#!/usr/bin/env python3
"""
Analyze workshop PR activity for leanprover-community/mathlib4.

Tracks PRs created, reviewed, and merged by workshop attendees during a
given date range.  Categorizes PRs by impact:
  - Created AND merged during the workshop
  - Created during the workshop (not yet merged / closed)
  - Pre-existing PRs reviewed by attendees during the workshop

Two modes:
  Discovery mode (no --attendees):
    Lists all contributors active during the date range so you can
    identify who attended the workshop.

  Report mode (--attendees):
    Shows categorized PR activity for the specified attendees, with
    merge status, cross-attendee collaboration, and summary statistics.

Usage:
    # Discovery: list all contributors
    python3 scripts/workshop_week_prs.py

    # Report: attendees from a file (one username per line)
    python3 scripts/workshop_week_prs.py --attendees attendees.txt

    # Report: attendees on the command line
    python3 scripts/workshop_week_prs.py --attendees "user1,user2,user3"

    # With explicit dates and output format
    python3 scripts/workshop_week_prs.py --attendees attendees.txt \\
        --start 2026-03-02 --end 2026-03-06 --format markdown

Uses the GitHub CLI (gh) if available, otherwise falls back to curl.
A GITHUB_TOKEN env var is recommended when using curl to avoid rate limits.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

REPO = "leanprover-community/mathlib4"
REPO_URL = f"https://github.com/{REPO}"
API_BASE = "https://api.github.com"

BOT_USERS = {
    "github-actions", "mathlib-bors", "dependabot", "mathlib-splicebot",
    "leanprover-community-mathlib4-bot", "leanprover-community-bot",
    "leanprover-radar",
}


def is_bot(username: str) -> bool:
    return username in BOT_USERS or username.endswith("[bot]")


def clean_title(title: str) -> str:
    return re.sub(r"^\[Merged by Bors\]\s*-\s*", "", title)


def is_bors_merged(title: str) -> bool:
    """Bors prepends '[Merged by Bors] - ' when it merges a PR.

    The GitHub ``merged_at`` field is **not** set because bors doesn't use
    GitHub's merge button, so we detect merges from the title instead.
    """
    return "[Merged by Bors]" in title


def parse_iso(s: str | None) -> datetime | None:
    if not s:
        return None
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def pr_number_from_url(url: str) -> int | None:
    m = re.search(r"/(?:issues|pulls)/(\d+)$", url)
    return int(m.group(1)) if m else None


# ---------------------------------------------------------------------------
# GitHub API helpers – prefer ``gh`` CLI, fall back to ``curl``
# ---------------------------------------------------------------------------

_HAS_GH: bool | None = None


def has_gh() -> bool:
    global _HAS_GH
    if _HAS_GH is None:
        _HAS_GH = shutil.which("gh") is not None
    return _HAS_GH


def _gh_api(endpoint: str) -> object:
    """Call the GitHub API via ``gh api``."""
    cmd = ["gh", "api", endpoint, "--paginate"]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    if r.returncode != 0:
        raise RuntimeError(f"gh api failed: {r.stderr.strip()}")
    # --paginate concatenates JSON arrays; parse the combined output
    text = r.stdout.strip()
    if not text:
        return []
    # gh --paginate can produce concatenated JSON arrays: [..][..]
    # Try to parse directly first, then fall back to joining them.
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        arrays = re.findall(r"\[.*?\]", text, re.DOTALL)
        combined: list = []
        for a in arrays:
            combined.extend(json.loads(a))
        return combined


def _curl_api(url: str, token: str | None = None) -> object:
    """Call the GitHub API via curl."""
    cmd = ["curl", "-s"]
    if token:
        cmd.extend(["-H", f"Authorization: token {token}"])
    cmd.extend(["-H", "Accept: application/vnd.github.v3+json", url])
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    if not r.stdout.strip():
        return None
    data = json.loads(r.stdout)
    if isinstance(data, dict) and "rate limit" in data.get("message", "").lower():
        return None
    return data


def api_get(endpoint: str, token: str | None = None) -> object:
    """Fetch a single API endpoint."""
    if has_gh():
        return _gh_api(endpoint)
    return _curl_api(f"{API_BASE}/{endpoint}", token)


def api_search_paginated(query: str, token: str | None = None) -> list:
    """Paginate through the GitHub search API."""
    if has_gh():
        items: list = []
        page = 1
        while True:
            endpoint = f"search/issues?q={query}+type:pr&per_page=100&page={page}"
            cmd = ["gh", "api", endpoint, "--jq", ".items"]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            if r.returncode != 0:
                print(f"  gh api error: {r.stderr.strip()}", file=sys.stderr)
                break
            batch = json.loads(r.stdout) if r.stdout.strip() else []
            if not batch:
                break
            items.extend(batch)
            print(f"  search page {page}: {len(batch)} items", file=sys.stderr)
            if len(batch) < 100:
                break
            page += 1
        return items

    # curl fallback
    all_items: list = []
    for page in range(1, 11):
        url = (
            f"{API_BASE}/search/issues"
            f"?q={query}&per_page=100&page={page}"
        )
        data = _curl_api(url, token)
        if data is None:
            print(f"  Rate limited on page {page}, waiting 60s…", file=sys.stderr)
            time.sleep(60)
            data = _curl_api(url, token)
            if data is None:
                break
        items = data.get("items", []) if isinstance(data, dict) else []
        all_items.extend(items)
        print(f"  search page {page}: {len(items)} items", file=sys.stderr)
        if len(items) < 100:
            break
        time.sleep(2)
    return all_items


def api_list_paginated(
    endpoint: str,
    params: dict,
    token: str | None = None,
    max_pages: int = 30,
) -> list:
    """Paginate through a GitHub list endpoint (e.g. issue comments)."""
    if has_gh():
        qs = "&".join(f"{k}={v}" for k, v in params.items())
        full = f"{endpoint}?{qs}&per_page=100"
        try:
            data = _gh_api(full)
            if isinstance(data, list):
                print(f"  {endpoint}: {len(data)} items (gh --paginate)", file=sys.stderr)
                return data
        except RuntimeError as exc:
            print(f"  gh error, falling back to curl: {exc}", file=sys.stderr)

    # curl fallback with manual pagination
    all_items: list = []
    for page in range(1, max_pages + 1):
        qs = "&".join(f"{k}={v}" for k, v in params.items())
        url = f"{API_BASE}/{endpoint}?{qs}&per_page=100&page={page}"
        data = _curl_api(url, token)
        if data is None:
            print(f"  Rate limited on page {page}, waiting 60s…", file=sys.stderr)
            time.sleep(60)
            data = _curl_api(url, token)
            if data is None:
                print(f"  Still rate limited. Stopping.", file=sys.stderr)
                break
        if not isinstance(data, list) or len(data) == 0:
            break
        all_items.extend(data)
        print(f"  {endpoint} page {page}: {len(data)} items", file=sys.stderr)
        if len(data) < 100:
            break
        time.sleep(1)
    return all_items


# ---------------------------------------------------------------------------
# Data fetching
# ---------------------------------------------------------------------------


def fetch_created_prs(start: str, end: str, token: str | None) -> list:
    """All PRs created in the date range."""
    print("Fetching PRs created in date range…", file=sys.stderr)
    query = f"repo:{REPO}+is:pr+created:{start}..{end}"
    prs = api_search_paginated(query, token)
    print(f"  Total: {len(prs)} PRs created", file=sys.stderr)
    return prs


def fetch_closed_prs(start: str, end: str, token: str | None) -> list:
    """All PRs closed (including merged) in the date range."""
    print("Fetching PRs closed in date range…", file=sys.stderr)
    query = f"repo:{REPO}+is:pr+closed:{start}..{end}"
    prs = api_search_paginated(query, token)
    print(f"  Total: {len(prs)} PRs closed", file=sys.stderr)
    return prs


def fetch_comments(start: str, token: str | None) -> list:
    """All issue/PR comments since *start*."""
    print("Fetching comments…", file=sys.stderr)
    comments = api_list_paginated(
        f"repos/{REPO}/issues/comments",
        {"sort": "created", "direction": "desc", "since": f"{start}T00:00:00Z"},
        token,
    )
    print(f"  Total: {len(comments)} comments", file=sys.stderr)
    return comments


def fetch_pr_detail(pr_num: int, token: str | None) -> dict | None:
    """Fetch full details for a single PR."""
    data = api_get(f"repos/{REPO}/pulls/{pr_num}", token)
    if isinstance(data, dict) and "title" in data:
        return data
    # gh --paginate may wrap single objects in a list
    if isinstance(data, list) and len(data) == 1 and "title" in data[0]:
        return data[0]
    return None


# ---------------------------------------------------------------------------
# Attendee loading
# ---------------------------------------------------------------------------


def load_attendees(value: str) -> list[str]:
    """Load attendees from a file or a comma-separated string."""
    path = Path(value)
    if path.exists():
        return [
            line.strip().lstrip("@")
            for line in path.read_text().splitlines()
            if line.strip() and not line.startswith("#")
        ]
    return [n.strip().lstrip("@") for n in value.split(",") if n.strip()]


# ---------------------------------------------------------------------------
# Discovery mode
# ---------------------------------------------------------------------------


def run_discovery(start: str, end: str, token: str | None) -> None:
    """List all contributors to help identify attendees."""
    created = fetch_created_prs(start, end, token)
    closed = fetch_closed_prs(start, end, token)

    merged = [pr for pr in closed if is_bors_merged(pr.get("title", ""))]
    created_only = [pr for pr in created if not is_bors_merged(pr.get("title", ""))]

    merged_by: dict[str, list] = defaultdict(list)
    for pr in merged:
        merged_by[pr["user"]["login"]].append(pr)

    created_by: dict[str, list] = defaultdict(list)
    for pr in created_only:
        created_by[pr["user"]["login"]].append(pr)

    humans = sorted(
        {a for a in set(merged_by) | set(created_by) if not is_bot(a)}
    )

    print(f"{'=' * 70}")
    print(f"ALL CONTRIBUTORS: {start} to {end}")
    print(f"Repository: {REPO}")
    print(f"{'=' * 70}")
    print()
    print("Re-run with --attendees to restrict output to workshop participants.")
    print()
    print(f"{'Username':<30} {'Merged':<10} {'Created':<10}")
    print(f"{'-' * 30} {'-' * 10} {'-' * 10}")
    for author in humans:
        nm = len(merged_by.get(author, []))
        nc = len(created_by.get(author, []))
        print(f"  @{author:<28} {nm:<10} {nc:<10}")
    print()
    print(f"Total: {len(merged)} PRs merged, {len(created_only)} PRs created, "
          f"{len(humans)} unique human contributors")


# ---------------------------------------------------------------------------
# Report mode
# ---------------------------------------------------------------------------


class PRInfo:
    """Collected data about a single PR."""

    __slots__ = (
        "number", "title", "author", "state", "created_at",
        "is_merged", "attendee_authors", "attendee_reviewers",
    )

    def __init__(self, number: int):
        self.number = number
        self.title = "(unknown)"
        self.author = "unknown"
        self.state = "unknown"
        self.created_at: datetime | None = None
        self.is_merged = False
        self.attendee_authors: set[str] = set()
        self.attendee_reviewers: set[str] = set()

    @property
    def url(self) -> str:
        return f"{REPO_URL}/pull/{self.number}"

    @property
    def is_cross_attendee(self) -> bool:
        """True when both author and a reviewer are attendees."""
        if self.attendee_authors and self.attendee_reviewers - self.attendee_authors:
            return True
        return len(self.attendee_reviewers - self.attendee_authors) >= 2

    def involvement_str(self) -> str:
        parts: list[str] = []
        for u in sorted(self.attendee_authors):
            parts.append(f"{u} (author)")
        for u in sorted(self.attendee_reviewers - self.attendee_authors):
            parts.append(f"{u} (reviewer)")
        return ", ".join(parts)

    def populate_from_api(self, raw: dict) -> None:
        self.title = clean_title(raw.get("title", self.title))
        self.author = raw.get("user", {}).get("login", self.author)
        self.state = raw.get("state", self.state)
        self.created_at = parse_iso(raw.get("created_at"))
        self.is_merged = is_bors_merged(raw.get("title", ""))


def run_report(
    attendees: list[str],
    start: str,
    end: str,
    token: str | None,
    fmt: str,
) -> None:
    attendee_set = set(attendees)
    start_dt = datetime.fromisoformat(f"{start}T00:00:00+00:00")
    end_dt = datetime.fromisoformat(f"{end}T23:59:59+00:00")

    print(
        f"Fetching activity for {len(attendee_set)} attendees "
        f"({start} to {end})…",
        file=sys.stderr,
    )

    # 1. All PRs created during the range
    created_prs = fetch_created_prs(start, end, token)

    # 2. All PRs closed during the range (to capture merges of older PRs)
    closed_prs = fetch_closed_prs(start, end, token)

    # 3. All comments during the range
    comments = fetch_comments(start, token)

    # ------------------------------------------------------------------
    # Build PR info from created + closed lists
    # ------------------------------------------------------------------
    prs: dict[int, PRInfo] = {}

    def ensure_pr(num: int) -> PRInfo:
        if num not in prs:
            prs[num] = PRInfo(num)
        return prs[num]

    for raw in created_prs:
        info = ensure_pr(raw["number"])
        info.populate_from_api(raw)

    for raw in closed_prs:
        info = ensure_pr(raw["number"])
        # Only overwrite if this gives us merge info we didn't have
        if is_bors_merged(raw.get("title", "")):
            info.populate_from_api(raw)
        elif info.title == "(unknown)":
            info.populate_from_api(raw)

    # ------------------------------------------------------------------
    # Track attendee authorship (PRs created during the range)
    # ------------------------------------------------------------------
    for raw in created_prs:
        author = raw["user"]["login"]
        if author in attendee_set:
            ensure_pr(raw["number"]).attendee_authors.add(author)

    # ------------------------------------------------------------------
    # Track attendee comments with precise timestamps
    # ------------------------------------------------------------------
    for c in comments:
        cdt = parse_iso(c.get("created_at"))
        if not cdt or cdt < start_dt or cdt > end_dt:
            continue
        user = c["user"]["login"]
        if is_bot(user) or user not in attendee_set:
            continue
        pr_num = pr_number_from_url(c.get("issue_url", ""))
        if pr_num is None:
            continue
        ensure_pr(pr_num).attendee_reviewers.add(user)

    # ------------------------------------------------------------------
    # Filter to PRs with attendee involvement
    # ------------------------------------------------------------------
    involved = {
        num: info for num, info in prs.items()
        if info.attendee_authors or info.attendee_reviewers
    }

    # Fetch details for PRs we only know via comments
    missing = [
        num for num, info in involved.items()
        if info.title == "(unknown)"
    ]
    if missing:
        print(
            f"Fetching details for {len(missing)} PRs found via comments…",
            file=sys.stderr,
        )
        for i, num in enumerate(sorted(missing)):
            raw = fetch_pr_detail(num, token)
            if raw:
                involved[num].populate_from_api(raw)
            if (i + 1) % 20 == 0:
                print(f"  {i + 1}/{len(missing)}", file=sys.stderr)
            time.sleep(0.5 if not has_gh() else 0.2)

    # ------------------------------------------------------------------
    # Categorize
    # ------------------------------------------------------------------
    def created_during(info: PRInfo) -> bool:
        return info.created_at is not None and start_dt <= info.created_at <= end_dt

    # A: Created by an attendee during the workshop
    cat_created_merged: list[PRInfo] = []
    cat_created_open: list[PRInfo] = []
    cat_created_closed: list[PRInfo] = []

    # B: Pre-existing PRs that attendees reviewed/merged during the workshop
    cat_pre_merged: list[PRInfo] = []
    cat_pre_open: list[PRInfo] = []

    for info in sorted(involved.values(), key=lambda i: i.number, reverse=True):
        if created_during(info) and info.author in attendee_set:
            if info.is_merged:
                cat_created_merged.append(info)
            elif info.state == "open":
                cat_created_open.append(info)
            else:
                cat_created_closed.append(info)
        elif info.attendee_reviewers or info.attendee_authors:
            # Pre-existing or created by non-attendee but reviewed by attendee
            if info.is_merged:
                cat_pre_merged.append(info)
            elif info.state == "open":
                cat_pre_open.append(info)
            # silently skip closed-unmerged pre-existing PRs (not interesting)

    # ------------------------------------------------------------------
    # Output
    # ------------------------------------------------------------------
    n_created = len(cat_created_merged) + len(cat_created_open) + len(cat_created_closed)
    n_pre = len(cat_pre_merged) + len(cat_pre_open)
    total_merged = len(cat_created_merged) + len(cat_pre_merged)
    n_collab = sum(1 for info in involved.values() if info.is_cross_attendee)

    if fmt == "csv":
        _output_csv(
            cat_created_merged, cat_created_open, cat_created_closed,
            cat_pre_merged, cat_pre_open,
        )
    else:
        _output_text(
            attendee_set, start, end,
            cat_created_merged, cat_created_open, cat_created_closed,
            cat_pre_merged, cat_pre_open,
            n_created, n_pre, total_merged, n_collab,
        )


def _pr_line(info: PRInfo, show_ext_author: bool = False) -> tuple[str, str]:
    """Return (main line, detail line) for a PR."""
    collab = "  [COLLAB]" if info.is_cross_attendee else ""
    ext = ""
    if show_ext_author and info.author not in info.attendee_authors:
        ext = f" (by {info.author})"
    line1 = f"  #{info.number}: {info.title}{ext}"
    line2 = f"      {info.involvement_str()}{collab}"
    return line1, line2


def _output_text(
    attendees, start, end,
    created_merged, created_open, created_closed,
    pre_merged, pre_open,
    n_created, n_pre, total_merged, n_collab,
) -> None:
    print(f"{'=' * 78}")
    print(f"WORKSHOP PR ACTIVITY: {start} to {end}")
    print(f"Repository: {REPO}")
    print(f"Attendees ({len(attendees)}): {', '.join(sorted(attendees))}")
    print(f"{'=' * 78}")

    print(f"\n## PRs CREATED by attendees during the workshop ({n_created})\n")

    print(f"### Merged ({len(created_merged)})\n")
    for info in created_merged:
        l1, l2 = _pr_line(info)
        print(l1)
        print(l2)

    print(f"\n### Still open ({len(created_open)})\n")
    for info in created_open:
        l1, l2 = _pr_line(info)
        print(l1)
        print(l2)

    if created_closed:
        print(f"\n### Closed without merge ({len(created_closed)})\n")
        for info in created_closed:
            l1, l2 = _pr_line(info)
            print(l1)
            print(l2)

    print(f"\n{'=' * 78}")
    print(f"\n## PRE-EXISTING PRs reviewed by attendees ({n_pre})\n")

    print(f"### Merged ({len(pre_merged)})\n")
    for info in pre_merged:
        l1, l2 = _pr_line(info, show_ext_author=True)
        print(l1)
        print(l2)

    if pre_open:
        print(f"\n### Still open ({len(pre_open)})\n")
        for info in pre_open:
            l1, l2 = _pr_line(info, show_ext_author=True)
            print(l1)
            print(l2)

    # Per-attendee summary
    print(f"\n{'=' * 78}")
    print("ACTIVITY PER ATTENDEE")
    print(f"{'=' * 78}")
    stats: dict[str, dict[str, int]] = defaultdict(lambda: {"authored": 0, "reviewed": 0})
    for info in (
        created_merged + created_open + created_closed + pre_merged + pre_open
    ):
        for u in info.attendee_authors:
            stats[u]["authored"] += 1
        for u in info.attendee_reviewers - info.attendee_authors:
            stats[u]["reviewed"] += 1

    for user in sorted(stats, key=lambda u: sum(stats[u].values()), reverse=True):
        s = stats[user]
        print(f"  @{user}: {s['authored']} authored, {s['reviewed']} reviewed")

    # Summary
    print(f"\n{'=' * 78}")
    print("SUMMARY")
    print(f"{'=' * 78}")
    print(f"PRs created by attendees during workshop:  {n_created}")
    print(f"  Merged:                                  {len(created_merged)}")
    print(f"  Still open:                              {len(created_open)}")
    if created_closed:
        print(f"  Closed (superseded):                     {len(created_closed)}")
    print()
    print(f"Pre-existing PRs with attendee review:     {n_pre}")
    print(f"  Merged:                                  {len(pre_merged)}")
    print(f"  Still open:                              {len(pre_open)}")
    print()
    print(f"TOTAL MERGED with workshop involvement:    {total_merged}")
    print(f"TOTAL still in pipeline:                   {len(created_open) + len(pre_open)}")
    print(f"Cross-attendee collaboration:              {n_collab} PRs")


def _output_csv(
    created_merged, created_open, created_closed,
    pre_merged, pre_open,
) -> None:
    print("category,pr,title,author,state,involvement,cross_attendee")
    for cat, label in [
        (created_merged, "created+merged"),
        (created_open, "created_open"),
        (created_closed, "created_closed"),
        (pre_merged, "pre_merged"),
        (pre_open, "pre_open"),
    ]:
        for info in cat:
            title = info.title.replace('"', '""')
            inv = info.involvement_str().replace('"', '""')
            collab = "yes" if info.is_cross_attendee else ""
            print(f'{label},{info.number},"{title}",{info.author},'
                  f'{info.state},"{inv}",{collab}')


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--attendees", "-a",
        metavar="FILE_OR_LIST",
        help=(
            "File with one GitHub username per line, or comma-separated list. "
            "If omitted, lists all contributors so you can identify attendees."
        ),
    )
    parser.add_argument("--start", default="2026-03-02", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", default="2026-03-06", help="End date (YYYY-MM-DD)")
    parser.add_argument(
        "--token",
        default=os.environ.get("GITHUB_TOKEN", ""),
        help="GitHub token for curl fallback (or set GITHUB_TOKEN env var)",
    )
    parser.add_argument(
        "--format", "-f",
        choices=["text", "csv", "markdown"],
        default="text",
        help="Output format (default: text)",
    )
    args = parser.parse_args()
    token = args.token or None

    if not has_gh() and not token:
        print(
            "Warning: neither 'gh' CLI nor GITHUB_TOKEN found. "
            "API rate limits will be very low (60 req/hr).",
            file=sys.stderr,
        )

    # "markdown" is an alias for "text" (the text output uses markdown-ish headers)
    fmt = "csv" if args.format == "csv" else "text"

    if args.attendees:
        attendees = load_attendees(args.attendees)
        if not attendees:
            print("Error: no attendees found.", file=sys.stderr)
            sys.exit(1)
        run_report(attendees, args.start, args.end, token, fmt)
    else:
        run_discovery(args.start, args.end, token)


if __name__ == "__main__":
    main()
