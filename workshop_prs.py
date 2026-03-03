#!/usr/bin/env python3
"""
Track PR activity on leanprover-community/mathlib4 during the maintainer workshop.
Workshop dates: March 2-6, 2026.

Usage:
    python3 workshop_prs.py [--start 2026-03-02] [--end 2026-03-06] [--cache]

Outputs a people summary and PR list showing who created and commented on PRs.
"""

import argparse
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import defaultdict
from datetime import datetime, timezone

REPO = "leanprover-community/mathlib4"
API_BASE = "https://api.github.com"
BOT_SUFFIXES = ["[bot]"]
BOT_USERS = {
    "github-actions",
    "mathlib-bors",
    "dependabot",
    "mathlib-splicebot",
    "leanprover-community-mathlib4-bot",
    "leanprover-community-bot",
    "leanprover-radar",
    "github-actions[bot]",
    "mathlib-bors[bot]",
    "dependabot[bot]",
    "mathlib-splicebot[bot]",
}
CACHE_DIR = "/tmp/workshop_prs_cache"


def is_bot(username: str) -> bool:
    """Check if a username belongs to a bot."""
    lower = username.lower()
    if lower in BOT_USERS:
        return True
    for suffix in BOT_SUFFIXES:
        if lower.endswith(suffix):
            return True
    return False


def api_request(url: str, params: dict | None = None) -> tuple:
    """Make a GitHub API request. Returns (data, link_header)."""
    if params:
        url = url + "?" + urllib.parse.urlencode(params)

    req = urllib.request.Request(url)
    req.add_header("User-Agent", "workshop-tracker")
    req.add_header("Accept", "application/vnd.github.v3+json")

    try:
        resp = urllib.request.urlopen(req)
        data = json.loads(resp.read())
        link_header = resp.getheader("Link", "")
        return data, link_header
    except urllib.error.HTTPError as e:
        if e.code == 403:
            body = e.read().decode()
            if "rate limit" in body.lower():
                print(f"  *** Rate limited. Waiting 60s...", file=sys.stderr)
                time.sleep(60)
                return api_request(url)  # retry once
            print(f"  *** HTTP 403: {body[:200]}", file=sys.stderr)
        elif e.code == 422:
            print(f"  *** HTTP 422: {e.read().decode()[:200]}", file=sys.stderr)
        else:
            print(f"  *** HTTP {e.code}: {e.read().decode()[:200]}", file=sys.stderr)
        raise


def parse_next_link(link_header: str) -> str | None:
    """Parse the 'next' URL from a GitHub Link header."""
    if not link_header:
        return None
    for part in link_header.split(","):
        if 'rel="next"' in part:
            match = re.search(r"<(.+?)>", part)
            if match:
                return match.group(1)
    return None


def paginate(url: str, params: dict | None = None, max_pages: int = 20) -> list:
    """Fetch all pages from a paginated GitHub API endpoint."""
    all_items = []
    page = 0

    if params is None:
        params = {}
    params.setdefault("per_page", "100")

    full_url = url + "?" + urllib.parse.urlencode(params)

    while full_url and page < max_pages:
        page += 1
        print(f"  Fetching page {page}: {full_url[:100]}...", file=sys.stderr)
        req = urllib.request.Request(full_url)
        req.add_header("User-Agent", "workshop-tracker")
        req.add_header("Accept", "application/vnd.github.v3+json")

        try:
            resp = urllib.request.urlopen(req)
        except urllib.error.HTTPError as e:
            if e.code == 403 and "rate limit" in e.read().decode().lower():
                print(f"  *** Rate limited on page {page}. Stopping pagination.", file=sys.stderr)
                break
            raise

        data = json.loads(resp.read())
        link_header = resp.getheader("Link", "")

        # Search API wraps results in {"items": [...]}
        if isinstance(data, dict) and "items" in data:
            all_items.extend(data["items"])
            print(f"    Got {len(data['items'])} items (total available: {data.get('total_count', '?')})", file=sys.stderr)
        elif isinstance(data, list):
            all_items.extend(data)
            print(f"    Got {len(data)} items", file=sys.stderr)
        else:
            all_items.append(data)

        full_url = parse_next_link(link_header)

    return all_items


def load_cache(name: str):
    """Load cached data if available."""
    path = os.path.join(CACHE_DIR, f"{name}.json")
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return None


def save_cache(name: str, data):
    """Save data to cache."""
    os.makedirs(CACHE_DIR, exist_ok=True)
    path = os.path.join(CACHE_DIR, f"{name}.json")
    with open(path, "w") as f:
        json.dump(data, f)


def parse_date(date_str: str) -> datetime:
    """Parse a GitHub API date string."""
    return datetime.fromisoformat(date_str.replace("Z", "+00:00"))


def pr_number_from_url(url: str) -> int | None:
    """Extract PR number from a GitHub API URL like .../issues/12345 or .../pulls/12345."""
    match = re.search(r"/(?:issues|pulls)/(\d+)$", url)
    if match:
        return int(match.group(1))
    return None


def main():
    parser = argparse.ArgumentParser(description="Track mathlib4 workshop PR activity")
    parser.add_argument("--start", default="2026-03-02", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", default="2026-03-06", help="End date (YYYY-MM-DD)")
    parser.add_argument("--cache", action="store_true", help="Use cached API responses")
    args = parser.parse_args()

    start_date = datetime.fromisoformat(args.start + "T00:00:00+00:00")
    # End date is inclusive, so we go to end of day
    end_date = datetime.fromisoformat(args.end + "T23:59:59+00:00")

    print(f"Tracking mathlib4 workshop activity: {args.start} to {args.end}", file=sys.stderr)
    print(f"Repository: {REPO}", file=sys.stderr)
    print(file=sys.stderr)

    # --- Step 1: Fetch PRs created in the date range ---
    print("=== Step 1: Fetching PRs created in date range ===", file=sys.stderr)
    created_prs_cache = load_cache("created_prs") if args.cache else None
    if created_prs_cache is not None:
        created_prs = created_prs_cache
        print(f"  Loaded {len(created_prs)} created PRs from cache", file=sys.stderr)
    else:
        query = f"repo:{REPO} is:pr created:{args.start}..{args.end}"
        created_prs = paginate(
            f"{API_BASE}/search/issues",
            {"q": query, "sort": "created", "order": "asc"},
            max_pages=5,
        )
        save_cache("created_prs", created_prs)
    print(f"  Found {len(created_prs)} PRs created in range", file=sys.stderr)

    # --- Step 2: Fetch all issue comments since start date ---
    print("\n=== Step 2: Fetching all issue comments since start date ===", file=sys.stderr)
    comments_cache = load_cache("comments") if args.cache else None
    if comments_cache is not None:
        all_comments = comments_cache
        print(f"  Loaded {len(all_comments)} comments from cache", file=sys.stderr)
    else:
        all_comments = paginate(
            f"{API_BASE}/repos/{REPO}/issues/comments",
            {"since": f"{args.start}T00:00:00Z", "sort": "created", "direction": "asc"},
            max_pages=50,
        )
        save_cache("comments", all_comments)
    print(f"  Fetched {len(all_comments)} total comments", file=sys.stderr)

    # --- Step 3: Process data ---
    print("\n=== Step 3: Processing data ===", file=sys.stderr)

    # Track PR info: pr_number -> {title, author, url, state, created_at}
    pr_info = {}
    for pr in created_prs:
        num = pr["number"]
        pr_info[num] = {
            "title": pr["title"],
            "author": pr["user"]["login"],
            "url": pr["html_url"],
            "state": pr.get("state", "unknown"),
            "created_at": pr.get("created_at", ""),
            "pull_request": pr.get("pull_request", {}),
        }

    # Track people -> activity
    people = defaultdict(lambda: {"authored": set(), "commented": set()})

    # Record PR authors
    for pr in created_prs:
        author = pr["user"]["login"]
        if not is_bot(author):
            people[author]["authored"].add(pr["number"])

    # Process comments
    comments_in_range = 0
    for comment in all_comments:
        created_at = parse_date(comment["created_at"])
        if created_at < start_date or created_at > end_date:
            continue

        user = comment["user"]["login"]
        if is_bot(user):
            continue

        pr_num = pr_number_from_url(comment.get("issue_url", ""))
        if pr_num is None:
            continue

        comments_in_range += 1
        people[user]["commented"].add(pr_num)

        # Record PR info if we don't have it yet (PR was created before the range)
        if pr_num not in pr_info:
            pr_info[pr_num] = {
                "title": f"(PR #{pr_num} - title not fetched)",
                "author": "unknown",
                "url": f"https://github.com/{REPO}/pull/{pr_num}",
                "state": "unknown",
                "created_at": "",
            }

    print(f"  Comments in date range (non-bot): {comments_in_range}", file=sys.stderr)
    print(f"  Unique people active: {len(people)}", file=sys.stderr)
    print(f"  Unique PRs touched: {len(pr_info)}", file=sys.stderr)

    # --- Step 4: Try to fetch titles for PRs we only know from comments ---
    untitled_prs = [num for num, info in pr_info.items() if info["title"].startswith("(PR #")]
    if untitled_prs:
        print(f"\n=== Step 4: Fetching titles for {len(untitled_prs)} PRs found via comments ===", file=sys.stderr)
        # Use search API to fetch in batches
        batch_size = 15  # keep search query reasonable
        for i in range(0, len(untitled_prs), batch_size):
            batch = untitled_prs[i:i+batch_size]
            # Build a search query with specific PR numbers
            number_query = " ".join(str(n) for n in batch)
            query = f"repo:{REPO} is:pr {number_query}"
            try:
                results = paginate(
                    f"{API_BASE}/search/issues",
                    {"q": query},
                    max_pages=2,
                )
                for pr in results:
                    num = pr["number"]
                    if num in pr_info and pr_info[num]["title"].startswith("(PR #"):
                        pr_info[num]["title"] = pr["title"]
                        pr_info[num]["author"] = pr["user"]["login"]
                        pr_info[num]["state"] = pr.get("state", "unknown")
                        pr_info[num]["created_at"] = pr.get("created_at", "")
                        # Also record author if not bot
                        author = pr["user"]["login"]
                        if not is_bot(author) and num in [n for person_data in people.values() for n in person_data["commented"]]:
                            pass  # Author is already tracked if they commented
                print(f"  Fetched {len(results)} PR details", file=sys.stderr)
            except Exception as e:
                print(f"  *** Failed to fetch PR batch: {e}", file=sys.stderr)
                break

    # --- Step 5: Output ---
    print("\n" + "=" * 80)
    print(f"MATHLIB4 WORKSHOP ACTIVITY: {args.start} to {args.end}")
    print("=" * 80)

    # People summary sorted by total activity
    print(f"\n{'=' * 80}")
    print("PEOPLE SUMMARY (sorted by activity)")
    print(f"{'=' * 80}")
    print(f"{'GitHub Username':<30} {'PRs Authored':<15} {'PRs Commented':<15} {'Total':<8}")
    print(f"{'-' * 30} {'-' * 15} {'-' * 15} {'-' * 8}")

    sorted_people = sorted(
        people.items(),
        key=lambda x: len(x[1]["authored"]) + len(x[1]["commented"]),
        reverse=True,
    )

    for username, activity in sorted_people:
        n_authored = len(activity["authored"])
        n_commented = len(activity["commented"])
        total = n_authored + n_commented
        print(f"{username:<30} {n_authored:<15} {n_commented:<15} {total:<8}")

    # PR list
    print(f"\n{'=' * 80}")
    print("ALL PRs WITH ACTIVITY DURING WORKSHOP")
    print(f"{'=' * 80}")

    # Collect all PR numbers with any workshop activity
    all_pr_nums = set()
    for person_data in people.values():
        all_pr_nums.update(person_data["authored"])
        all_pr_nums.update(person_data["commented"])

    # Sort by PR number descending (most recent first)
    for pr_num in sorted(all_pr_nums, reverse=True):
        info = pr_info.get(pr_num, {})
        title = info.get("title", "(unknown)")
        author = info.get("author", "unknown")
        url = info.get("url", f"https://github.com/{REPO}/pull/{pr_num}")

        # Who from the workshop touched this PR?
        involved = []
        for username, activity in people.items():
            roles = []
            if pr_num in activity["authored"]:
                roles.append("author")
            if pr_num in activity["commented"]:
                roles.append("commenter")
            if roles:
                involved.append(f"{username} ({', '.join(roles)})")

        print(f"\n#{pr_num}: {title}")
        print(f"  URL: {url}")
        print(f"  Author: {author}")
        print(f"  Workshop involvement: {'; '.join(involved)}")

    # Summary stats
    print(f"\n{'=' * 80}")
    print("SUMMARY")
    print(f"{'=' * 80}")
    print(f"Date range: {args.start} to {args.end}")
    print(f"Unique people active: {len(people)}")
    print(f"PRs created in range: {len(created_prs)}")
    print(f"Total PRs with activity: {len(all_pr_nums)}")
    print(f"Non-bot comments in range: {comments_in_range}")


if __name__ == "__main__":
    main()
