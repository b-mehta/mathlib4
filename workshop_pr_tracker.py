#!/usr/bin/env python3
"""
Track mathlib4 PRs involving workshop attendees.

Uses the GitHub REST API via curl to find PRs created or commented on
by workshop attendees during a given date range. Categorizes PRs into:
- Created AND merged during the workshop
- Created during the workshop (not yet merged)
- Merged during the workshop (created before)
- Reviewed during the workshop (pre-existing PRs)

Usage:
    python3 workshop_pr_tracker.py [--start YYYY-MM-DD] [--end YYYY-MM-DD] [--token GITHUB_TOKEN]

Defaults to March 2-6, 2026 (Bonn workshop week).
A GitHub token is strongly recommended to avoid rate limits (60 req/hr unauthenticated
vs 5000 req/hr authenticated). Create one at https://github.com/settings/tokens
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from collections import defaultdict
from datetime import datetime, timezone, timedelta

REPO = "leanprover-community/mathlib4"

WORKSHOP_ATTENDEES = {
    "riccardobrasca", "joelriou", "grunweg", "chrisflav", "EtienneC30",
    "mattrobball", "tb65536", "b-mehta", "kbuzzard", "smorel394",
    "RemyDegenne", "faenuccio", "kckennylau", "justus-springer",
    "Whysoserioushah", "erdOne", "smmercuri", "kebekus", "fpvandoorn",
    "MichaelStollBayreuth", "PatrickMassot", "mariainesdff", "robin-carlier",
    "jcommelin", "DavidLedvinka", "jjdishere",
}

BOT_USERS = {
    "github-actions", "mathlib-bors", "dependabot", "mathlib-splicebot",
    "leanprover-community-mathlib4-bot", "leanprover-community-bot",
    "leanprover-radar",
}


def github_api(endpoint, token=None, params=None):
    """Call the GitHub REST API. Returns parsed JSON."""
    url = f"https://api.github.com/{endpoint}"
    if params:
        qs = "&".join(f"{k}={v}" for k, v in params.items())
        url = f"{url}?{qs}"

    cmd = ["curl", "-s"]
    if token:
        cmd.extend(["-H", f"Authorization: token {token}"])
    cmd.extend(["-H", "Accept: application/vnd.github.v3+json", url])

    r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    if not r.stdout.strip():
        return None
    data = json.loads(r.stdout)

    if isinstance(data, dict) and "message" in data and "rate limit" in data.get("message", "").lower():
        return None
    return data


def github_api_paginated(endpoint, token=None, params=None, max_pages=20, stop_before=None):
    """Paginate through GitHub API results. stop_before is an ISO date string."""
    all_results = []
    base_params = dict(params or {})
    base_params["per_page"] = "100"

    for page in range(1, max_pages + 1):
        base_params["page"] = str(page)
        data = github_api(endpoint, token, base_params)

        if data is None:
            print(f"  Rate limited on page {page}, waiting 60s...", file=sys.stderr)
            time.sleep(60)
            data = github_api(endpoint, token, base_params)
            if data is None:
                print(f"  Still rate limited. Stopping pagination.", file=sys.stderr)
                break

        if not isinstance(data, list) or len(data) == 0:
            break

        all_results.extend(data)

        if stop_before:
            last_date = data[-1].get("created_at", "")
            if last_date < stop_before:
                break

        print(f"  Page {page}: {len(data)} items", file=sys.stderr)
        time.sleep(1)

    return all_results


def parse_date(s):
    if not s:
        return None
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def pr_number_from_url(url):
    m = re.search(r"/(?:issues|pulls)/(\d+)$", url)
    return int(m.group(1)) if m else None


def clean_title(t):
    return re.sub(r'^\[Merged by Bors\]\s*-\s*', '', t)


def fetch_pr_detail(pr_num, token=None):
    """Fetch full detail for a single PR (title, state, dates)."""
    data = github_api(f"repos/{REPO}/pulls/{pr_num}", token)
    if data and isinstance(data, dict) and "title" in data:
        return {
            "title": clean_title(data["title"]),
            "raw_title": data["title"],
            "author": data["user"]["login"],
            "state": data["state"],
            "created_at": data.get("created_at"),
            "closed_at": data.get("closed_at"),
        }
    return None


def main():
    parser = argparse.ArgumentParser(description="Track workshop PR activity")
    parser.add_argument("--start", default="2026-03-02", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", default="2026-03-06", help="End date (YYYY-MM-DD)")
    parser.add_argument("--token", default=os.environ.get("GITHUB_TOKEN", ""),
                        help="GitHub token (or set GITHUB_TOKEN env var)")
    parser.add_argument("--format", choices=["markdown", "csv"], default="markdown",
                        help="Output format")
    args = parser.parse_args()

    token = args.token or None
    start_dt = datetime.fromisoformat(f"{args.start}T00:00:00+00:00")
    end_dt = datetime.fromisoformat(f"{args.end}T23:59:59+00:00")
    stop_before = (start_dt - timedelta(days=1)).strftime("%Y-%m-%d")

    print(f"Fetching data for {args.start} to {args.end}...", file=sys.stderr)

    # 1. Fetch recently created PRs
    print("Fetching created PRs...", file=sys.stderr)
    created_prs = github_api_paginated(
        f"repos/{REPO}/pulls", token,
        params={"state": "all", "sort": "created", "direction": "desc"},
        stop_before=f"{stop_before}T00:00:00Z"
    )
    print(f"  Total: {len(created_prs)} PRs", file=sys.stderr)

    # 2. Fetch comments in date range
    print("Fetching comments...", file=sys.stderr)
    comments = github_api_paginated(
        f"repos/{REPO}/issues/comments", token,
        params={"sort": "created", "direction": "desc",
                "since": f"{args.start}T00:00:00Z"},
        stop_before=f"{args.start}T00:00:00Z"
    )
    print(f"  Total: {len(comments)} comments", file=sys.stderr)

    # 3. Build PR detail from list endpoint
    # In mathlib, bors closes PRs on merge and prepends "[Merged by Bors] - " to the title.
    # The GitHub API merged_at field is NOT set because bors doesn't use GitHub's merge button.
    # So we use: title starts with "[Merged by Bors]" + state=closed => merged.
    # The closed_at field gives the merge timestamp.
    pr_detail = {}
    for pr in created_prs:
        created_at = parse_date(pr["created_at"])
        closed_at = parse_date(pr.get("closed_at"))
        is_merged = "[Merged by Bors]" in pr["title"]
        pr_detail[pr["number"]] = {
            "title": clean_title(pr["title"]),
            "raw_title": pr["title"],
            "author": pr["user"]["login"],
            "state": pr["state"],
            "created_at": created_at,
            "closed_at": closed_at,
            "is_merged": is_merged,
            "created_during": created_at and start_dt <= created_at <= end_dt,
            "merged_during": is_merged and closed_at and start_dt <= closed_at <= end_dt,
        }

    # 4. Build activity maps
    people = defaultdict(lambda: {"authored": set(), "commented": set()})

    for pr in created_prs:
        created_at = parse_date(pr["created_at"])
        if not created_at or created_at < start_dt or created_at > end_dt:
            continue
        author = pr["user"]["login"]
        if author not in BOT_USERS and not author.endswith("[bot]"):
            people[author]["authored"].add(pr["number"])

    for comment in comments:
        created_at = parse_date(comment["created_at"])
        if not created_at or created_at < start_dt or created_at > end_dt:
            continue
        user = comment["user"]["login"]
        if user in BOT_USERS or user.endswith("[bot]"):
            continue
        pr_num = pr_number_from_url(comment.get("issue_url", ""))
        if pr_num is None:
            continue
        people[user]["commented"].add(pr_num)

    # 5. Collect workshop PRs
    workshop_prs = set()
    for user in WORKSHOP_ATTENDEES:
        if user in people:
            workshop_prs.update(people[user]["authored"])
            workshop_prs.update(people[user]["commented"])

    # 6. Fetch details for PRs only found via comments (not in the list endpoint)
    missing = sorted([n for n in workshop_prs if n not in pr_detail])
    if missing:
        print(f"Fetching details for {len(missing)} PRs found via comments...", file=sys.stderr)
        for i, pr_num in enumerate(missing):
            detail = fetch_pr_detail(pr_num, token)
            if detail:
                created_at = parse_date(detail["created_at"])
                closed_at = parse_date(detail.get("closed_at"))
                is_merged = "[Merged by Bors]" in detail["raw_title"]
                pr_detail[pr_num] = {
                    **detail,
                    "created_at": created_at,
                    "closed_at": closed_at,
                    "is_merged": is_merged,
                    "created_during": created_at and start_dt <= created_at <= end_dt,
                    "merged_during": is_merged and closed_at and start_dt <= closed_at <= end_dt,
                }
            else:
                pr_detail[pr_num] = {
                    "title": "(details unavailable)",
                    "author": "unknown",
                    "state": "unknown",
                    "is_merged": False,
                    "created_during": False,
                    "merged_during": False,
                }
            if (i + 1) % 10 == 0:
                print(f"  {i + 1}/{len(missing)} done", file=sys.stderr)
            time.sleep(0.5)

    # 7. Categorize and output
    def get_title(n):
        return pr_detail.get(n, {}).get("title", "(unknown)")

    def get_involvement(pr_num):
        involved = []
        for user in sorted(WORKSHOP_ATTENDEES):
            if user not in people:
                continue
            roles = []
            if pr_num in people[user]["authored"]:
                roles.append("author")
            if pr_num in people[user]["commented"]:
                roles.append("reviewer")
            if roles:
                involved.append(f"{user} ({', '.join(roles)})")
        return involved

    def categorize(n):
        d = pr_detail.get(n, {})
        created = d.get("created_during", False)
        merged = d.get("merged_during", False)
        if created and merged:
            return "created+merged"
        elif created:
            return "created"
        elif merged:
            return "merged"
        else:
            return "reviewed"

    categories = {
        "created+merged": [],
        "created": [],
        "merged": [],
        "reviewed": [],
    }
    for n in sorted(workshop_prs, reverse=True):
        categories[categorize(n)].append(n)

    REPO_URL = f"https://github.com/{REPO}/pull"

    if args.format == "markdown":
        print(f"# Workshop PR Activity: {args.start} to {args.end}\n")
        print(f"**{len(workshop_prs)} PRs** touched by **{len(WORKSHOP_ATTENDEES)} attendees**\n")

        section_headers = {
            "created+merged": "Created AND merged during the workshop",
            "created": "Created during the workshop (not yet merged)",
            "merged": "Merged during the workshop (created before)",
            "reviewed": "Reviewed during the workshop (pre-existing PRs)",
        }
        for cat_key in ["created+merged", "created", "merged", "reviewed"]:
            prs = categories[cat_key]
            if not prs:
                continue
            print(f"\n### {section_headers[cat_key]} ({len(prs)} PRs)\n")
            print("| # | Title | Workshop involvement |")
            print("|---|-------|---------------------|")
            for n in prs:
                title = get_title(n).replace("|", "\\|")
                link = f"[#{n}]({REPO_URL}/{n})"
                involved = ", ".join(get_involvement(n))
                print(f"| {link} | {title} | {involved} |")
    else:
        print("Category,PR,Title,Workshop Involvement")
        for cat_key in ["created+merged", "created", "merged", "reviewed"]:
            for n in categories[cat_key]:
                title = get_title(n).replace('"', '""')
                involved = "; ".join(get_involvement(n))
                print(f'{cat_key},{n},"{title}","{involved}"')

    # Summary to stderr
    print(f"\n---", file=sys.stderr)
    print(f"Summary:", file=sys.stderr)
    for cat_key, label in [("created+merged", "Created+merged"), ("created", "Created (open)"),
                            ("merged", "Merged (pre-existing)"), ("reviewed", "Reviewed")]:
        print(f"  {label}: {len(categories[cat_key])} PRs", file=sys.stderr)
    print(f"  Total: {len(workshop_prs)} PRs", file=sys.stderr)
    print(f"\nAttendee activity:", file=sys.stderr)
    attendee_data = []
    for user in WORKSHOP_ATTENDEES:
        a = len(people[user]["authored"]) if user in people else 0
        c = len(people[user]["commented"]) if user in people else 0
        if a + c > 0:
            attendee_data.append((user, a, c))
    attendee_data.sort(key=lambda x: x[1] + x[2], reverse=True)
    for user, a, c in attendee_data:
        print(f"  {user}: {a} authored, {c} reviewed", file=sys.stderr)


if __name__ == "__main__":
    main()
