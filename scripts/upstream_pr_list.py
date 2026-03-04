#!/usr/bin/env python3

"""List PRs merged to leanprover-community/mathlib4 after a given date.

For each PR, outputs a JSON line with: number, title, author, created_at,
merged_at, and commenters (comment + review authors, excluding the PR author).

Modes:
  --git-only   Extract everything from git log (no API calls, fast).
  default      Use GitHub REST API for full data (author, commenters).
               Set GITHUB_TOKEN env var for higher rate limits (5000/hr vs 60/hr).
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
import urllib.request
import urllib.error

REPO_OWNER = "leanprover-community"
REPO_NAME = "mathlib4"
UPSTREAM_URL = f"https://github.com/{REPO_OWNER}/{REPO_NAME}.git"
DEFAULT_START_DATE = "2026-03-02T09:00:00Z"
API_BASE = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}"


# ---------------------------------------------------------------------------
# GitHub REST API helpers
# ---------------------------------------------------------------------------

def github_get(path: str, token: str | None) -> list | dict:
    """GET a GitHub API endpoint, handling pagination, rate limits, and retries."""
    headers = {"Accept": "application/vnd.github+json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"

    all_items: list = []
    url = f"{API_BASE}/{path}" if not path.startswith("http") else path
    sep = "&" if "?" in url else "?"
    if "per_page" not in url:
        url += f"{sep}per_page=100"

    while url:
        req = urllib.request.Request(url, headers=headers)
        retries = 0
        while True:
            try:
                with urllib.request.urlopen(req) as resp:
                    data = json.loads(resp.read().decode())
                    remaining = resp.headers.get("X-RateLimit-Remaining")
                    if remaining and int(remaining) < 5:
                        reset_time = int(
                            resp.headers.get("X-RateLimit-Reset", 0)
                        )
                        wait = max(0, reset_time - int(time.time())) + 1
                        print(
                            f"Rate limit nearly exhausted, waiting {wait}s...",
                            file=sys.stderr,
                        )
                        time.sleep(wait)

                    if isinstance(data, dict):
                        return data

                    all_items.extend(data)

                    url = None
                    link_header = resp.headers.get("Link", "")
                    for part in link_header.split(","):
                        if 'rel="next"' in part:
                            url = part.split("<")[1].split(">")[0]
                break  # success, exit retry loop
            except urllib.error.HTTPError as e:
                if e.code == 403 and "rate limit" in e.read().decode().lower():
                    reset_time = int(e.headers.get("X-RateLimit-Reset", 0))
                    wait = max(0, reset_time - int(time.time())) + 1
                    print(f"Rate limited, waiting {wait}s...", file=sys.stderr)
                    time.sleep(wait)
                    continue
                if e.code >= 500 and retries < 4:
                    retries += 1
                    wait = 2 ** retries
                    print(
                        f"Server error {e.code}, retrying in {wait}s "
                        f"({retries}/4)...",
                        file=sys.stderr,
                    )
                    time.sleep(wait)
                    continue
                raise

    return all_items


# ---------------------------------------------------------------------------
# Git log parsing
# ---------------------------------------------------------------------------

def _author_from_email(email: str) -> str:
    """Extract a GitHub username from a noreply email, or return the email."""
    # GitHub noreply format: "12345678+username@users.noreply.github.com"
    m = re.match(r"\d+\+(.+)@users\.noreply\.github\.com$", email)
    if m:
        return m.group(1)
    # Older format: "username@users.noreply.github.com"
    m = re.match(r"(.+)@users\.noreply\.github\.com$", email)
    if m:
        return m.group(1)
    return email


def _title_from_subject(subject: str) -> str:
    """Strip the trailing '(#NNN)' and optional '[Merged by Bors] - ' prefix."""
    title = re.sub(r"\s*\(#\d+\)$", "", subject)
    title = re.sub(r"^\[Merged by Bors\]\s*-\s*", "", title)
    return title


def get_merged_prs_from_git(start_date: str) -> list[dict]:
    """Get PR data from git log.

    Returns a list of dicts with: number, title, author, merged_at.
    The author is extracted from the commit email (best-effort GitHub username).
    """
    print("Fetching upstream master...", file=sys.stderr)
    subprocess.run(
        ["git", "fetch", UPSTREAM_URL, "master"],
        check=True,
        capture_output=True,
        text=True,
    )

    # %aI = author date ISO, %ae = author email, %s = subject
    result = subprocess.run(
        [
            "git", "log",
            f"--after={start_date}",
            "FETCH_HEAD",
            "--format=%aI\t%ae\t%s",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    prs: list[dict] = []
    for line in result.stdout.splitlines():
        m = re.search(r"\(#(\d+)\)$", line.strip())
        if not m:
            continue
        parts = line.split("\t", 2)
        if len(parts) != 3:
            continue
        date_str, email, subject = parts
        prs.append({
            "number": int(m.group(1)),
            "title": _title_from_subject(subject),
            "author": _author_from_email(email),
            "merged_at": date_str,
        })

    print(f"Found {len(prs)} merged PRs since {start_date}", file=sys.stderr)
    return prs


# ---------------------------------------------------------------------------
# API-based enrichment
# ---------------------------------------------------------------------------

def extract_commenters(
    pr_author: str,
    comments: list[dict],
    reviews: list[dict],
) -> list[str]:
    """Extract unique commenter logins from comments and reviews."""
    commenters: set[str] = set()

    for c in comments:
        user = c.get("user")
        if user and user.get("login"):
            commenters.add(user["login"])

    for r in reviews:
        user = r.get("user")
        if user and user.get("login"):
            commenters.add(user["login"])

    commenters.discard(pr_author)
    return sorted(commenters)


def fetch_pr_data(number: int, merge_time: str, token: str | None) -> dict:
    """Fetch full data for a single PR via the GitHub API."""
    pr = github_get(f"pulls/{number}", token)
    comments = github_get(f"issues/{number}/comments", token)
    reviews = github_get(f"pulls/{number}/reviews", token)

    author = pr.get("user", {})
    author_login = author.get("login", "ghost") if author else "ghost"
    merged_at = pr.get("merged_at") or merge_time

    return {
        "number": pr["number"],
        "title": pr["title"],
        "author": author_login,
        "created_at": pr["created_at"],
        "merged_at": merged_at,
        "commenters": extract_commenters(author_login, comments, reviews),
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="List PRs merged to mathlib4 after a given date."
    )
    parser.add_argument(
        "--since",
        default=DEFAULT_START_DATE,
        help=f"ISO 8601 datetime cutoff (default: {DEFAULT_START_DATE})",
    )
    parser.add_argument(
        "--git-only",
        action="store_true",
        help="Use only git log data (no API calls). "
        "Omits created_at and commenters, author is best-effort.",
    )
    args = parser.parse_args()

    git_prs = get_merged_prs_from_git(args.since)
    if not git_prs:
        print("No PRs found.", file=sys.stderr)
        return

    git_prs.sort(key=lambda p: p["merged_at"])

    if args.git_only:
        for pr in git_prs:
            print(json.dumps(pr))
        print(f"Done. Output {len(git_prs)} PRs (git-only).", file=sys.stderr)
        return

    # Full API mode
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print(
            "Warning: GITHUB_TOKEN not set, using anonymous API access "
            "(60 req/hr). Set GITHUB_TOKEN for 5000 req/hr.\n"
            "Use --git-only to skip API calls entirely.",
            file=sys.stderr,
        )

    merge_times = {pr["number"]: pr["merged_at"] for pr in git_prs}
    total = len(git_prs)
    print(f"Fetching details for {total} PRs (3 API calls each)...", file=sys.stderr)

    for i, pr in enumerate(git_prs, 1):
        number = pr["number"]
        print(f"  [{i}/{total}] PR #{number}...", file=sys.stderr)
        pr_data = fetch_pr_data(number, merge_times[number], token)
        print(json.dumps(pr_data))
        sys.stdout.flush()

    print(f"Done. Output {total} PRs.", file=sys.stderr)


if __name__ == "__main__":
    main()
