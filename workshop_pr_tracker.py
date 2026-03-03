#!/usr/bin/env python3
"""
Track mathlib4 PRs involving workshop attendees.

Uses the GitHub REST API via curl to find PRs created or commented on
by workshop attendees during a given date range.

Usage:
    python3 workshop_pr_tracker.py [--start YYYY-MM-DD] [--end YYYY-MM-DD] [--token GITHUB_TOKEN]

Defaults to March 2-6, 2026 (Bonn workshop week).
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
    data = json.loads(r.stdout)

    # Check for rate limiting
    if isinstance(data, dict) and "message" in data and "rate limit" in data.get("message", "").lower():
        return None  # signal rate limit
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
            # Rate limited — wait and retry once
            print(f"  Rate limited on page {page}, waiting 60s...", file=sys.stderr)
            time.sleep(60)
            data = github_api(endpoint, token, base_params)
            if data is None:
                print(f"  Still rate limited. Stopping pagination.", file=sys.stderr)
                break

        if not isinstance(data, list) or len(data) == 0:
            break

        all_results.extend(data)

        # Check if we've gone past our date window
        if stop_before:
            last_date = data[-1].get("created_at", "")
            if last_date < stop_before:
                break

        print(f"  Page {page}: {len(data)} items", file=sys.stderr)
        time.sleep(1)  # be nice to API

    return all_results


def parse_date(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def pr_number_from_url(url):
    m = re.search(r"/(?:issues|pulls)/(\d+)$", url)
    return int(m.group(1)) if m else None


def fetch_pr_title(pr_num, token=None):
    """Fetch the title for a single PR."""
    data = github_api(f"repos/{REPO}/pulls/{pr_num}", token)
    if data and isinstance(data, dict) and "title" in data:
        return re.sub(r'^\[Merged by Bors\]\s*-\s*', '', data["title"])
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
    # For API queries, use the day before start as stop_before
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

    # 3. Build PR info from created PRs
    pr_info = {}
    for pr in created_prs:
        title = re.sub(r'^\[Merged by Bors\]\s*-\s*', '', pr["title"])
        pr_info[pr["number"]] = {"title": title, "author": pr["user"]["login"]}

    # 4. Build activity maps
    people = defaultdict(lambda: {"authored": set(), "commented": set()})

    for pr in created_prs:
        created_at = parse_date(pr["created_at"])
        if created_at < start_dt or created_at > end_dt:
            continue
        author = pr["user"]["login"]
        if author not in BOT_USERS and not author.endswith("[bot]"):
            people[author]["authored"].add(pr["number"])

    for comment in comments:
        created_at = parse_date(comment["created_at"])
        if created_at < start_dt or created_at > end_dt:
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

    # 6. Fetch missing titles
    missing = [n for n in sorted(workshop_prs) if n not in pr_info]
    if missing:
        print(f"Fetching titles for {len(missing)} PRs...", file=sys.stderr)
        for i, pr_num in enumerate(missing):
            title = fetch_pr_title(pr_num, token)
            if title:
                pr_info[pr_num] = {"title": title, "author": "unknown"}
            else:
                pr_info[pr_num] = {"title": "(title unavailable)", "author": "unknown"}
            if (i + 1) % 10 == 0:
                print(f"  {i + 1}/{len(missing)} done", file=sys.stderr)
            time.sleep(0.5)

    # 7. Output table
    def get_title(pr_num):
        return pr_info.get(pr_num, {}).get("title", "(unknown)")

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

    if args.format == "markdown":
        print(f"# Workshop PR Activity: {args.start} to {args.end}\n")
        print(f"**{len(workshop_prs)} PRs** involving **{len(WORKSHOP_ATTENDEES)} attendees**\n")
        print("| # | Title | Workshop involvement |")
        print("|---|-------|---------------------|")
        for pr_num in sorted(workshop_prs, reverse=True):
            title = get_title(pr_num).replace("|", "\\|")
            link = f"[#{pr_num}](https://github.com/{REPO}/pull/{pr_num})"
            involved = ", ".join(get_involvement(pr_num))
            print(f"| {link} | {title} | {involved} |")
    else:
        print("PR,Title,Workshop Involvement")
        for pr_num in sorted(workshop_prs, reverse=True):
            title = get_title(pr_num).replace('"', '""')
            involved = "; ".join(get_involvement(pr_num))
            print(f'{pr_num},"{title}","{involved}"')

    # Summary
    print(f"\n---", file=sys.stderr)
    print(f"Attendee summary:", file=sys.stderr)
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
