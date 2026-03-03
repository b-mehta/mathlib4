#!/usr/bin/env python3
"""
Analyze PRs created and merged during the workshop week (March 2-6, 2026).

This script fetches PRs from leanprover-community/mathlib4 that were created
or merged during the week of March 2-6, 2026, and lists the people involved.

Usage:
    python3 scripts/workshop_week_prs.py

Requires 'gh' (GitHub CLI) to be installed and authenticated.
"""

import json
import subprocess
import sys
from collections import defaultdict

REPO = "leanprover-community/mathlib4"
START_DATE = "2026-03-02"
END_DATE = "2026-03-06"


def gh_api(query: str) -> list:
    """Run a GitHub search query and return all results using pagination."""
    items = []
    page = 1
    while True:
        cmd = [
            "gh", "api",
            f"search/issues?q={query}+type:pr&per_page=100&page={page}",
            "--jq", ".items"
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if result.returncode != 0:
            print(f"Error calling GitHub API: {result.stderr}", file=sys.stderr)
            sys.exit(1)
        batch = json.loads(result.stdout)
        if not batch:
            break
        items.extend(batch)
        if len(batch) < 100:
            break
        page += 1
    return items


def get_prs_created() -> list:
    """Fetch PRs created during the workshop week."""
    query = f"repo:{REPO}+created:{START_DATE}..{END_DATE}"
    return gh_api(query)


def get_prs_closed() -> list:
    """Fetch PRs closed (including merged) during the workshop week."""
    query = f"repo:{REPO}+closed:{START_DATE}..{END_DATE}"
    return gh_api(query)


def is_bors_merged(pr: dict) -> bool:
    """Check if a PR was merged by Bors (indicated by title prefix)."""
    return "[Merged by Bors]" in pr.get("title", "")


def get_original_title(pr: dict) -> str:
    """Strip the Bors prefix from a merged PR title."""
    return pr["title"].replace("[Merged by Bors] - ", "")


def main():
    print("Fetching PR data from GitHub...")
    created_prs = get_prs_created()
    closed_prs = get_prs_closed()

    # Merged PRs are those closed during the week with the Bors prefix
    merged_prs = [pr for pr in closed_prs if is_bors_merged(pr)]

    # Filter out Bors merge PRs from the created list
    # (the original PRs are the ones without the Bors prefix)
    original_created = [pr for pr in created_prs if not is_bors_merged(pr)]

    print()
    print("=" * 80)
    print(f"WORKSHOP WEEK PR ANALYSIS: {START_DATE} to {END_DATE}")
    print(f"Repository: {REPO}")
    print("=" * 80)

    # --- Merged PRs ---
    print()
    print(f"MERGED PRs ({len(merged_prs)} total):")
    print("-" * 80)
    merged_by_author = defaultdict(list)
    for pr in sorted(merged_prs, key=lambda x: x["closed_at"]):
        author = pr["user"]["login"]
        title = get_original_title(pr)
        merged_by_author[author].append(pr)
        print(f"  #{pr['number']} [{pr['closed_at'][:10]}] @{author}: {title[:65]}")

    # --- Created PRs (originals only) ---
    print()
    print(f"CREATED PRs ({len(original_created)} total, excl. Bors merge PRs):")
    print("-" * 80)
    created_by_author = defaultdict(list)
    for pr in sorted(original_created, key=lambda x: x["created_at"]):
        author = pr["user"]["login"]
        created_by_author[author].append(pr)
        state = "open" if pr["state"] == "open" else "closed"
        print(f"  #{pr['number']} [{pr['created_at'][:10]}] @{author} ({state}): {pr['title'][:65]}")

    # --- Summary: Authors of merged PRs ---
    print()
    print("AUTHORS OF MERGED PRs (potential workshop attendees):")
    print("-" * 50)
    for author, prs in sorted(merged_by_author.items(), key=lambda x: -len(x[1])):
        if "[bot]" not in author:
            print(f"  @{author}: {len(prs)} PR(s) merged")

    # --- Summary: Authors of created PRs ---
    print()
    print("AUTHORS OF CREATED PRs (potential workshop attendees):")
    print("-" * 50)
    for author, prs in sorted(created_by_author.items(), key=lambda x: -len(x[1])):
        if "[bot]" not in author:
            print(f"  @{author}: {len(prs)} PR(s) created")

    # --- Combined unique authors ---
    all_authors = set(merged_by_author.keys()) | set(created_by_author.keys())
    all_authors.discard("mathlib-splicebot[bot]")
    bots = {a for a in all_authors if "[bot]" in a}
    human_authors = all_authors - bots

    print()
    print(f"ALL UNIQUE HUMAN AUTHORS ({len(human_authors)} people):")
    print("-" * 50)
    for author in sorted(human_authors):
        merged_count = len(merged_by_author.get(author, []))
        created_count = len(created_by_author.get(author, []))
        print(f"  @{author}: {merged_count} merged, {created_count} created")

    print()
    print(f"Total: {len(merged_prs)} PRs merged, {len(original_created)} PRs created")
    print(f"       {len(human_authors)} unique human contributors")


if __name__ == "__main__":
    main()
