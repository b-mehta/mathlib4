#!/usr/bin/env python3
"""
Analyze workshop activity during the week of March 2-6, 2026.

Tracks PRs created and commented on by workshop attendees in
leanprover-community/mathlib4.  Only PRs where at least one attendee was
involved (as author or commenter) are shown.

Usage:
    # List all contributors (to help identify attendees):
    python3 scripts/workshop_week_prs.py

    # Show only workshop attendees' activity (file, one username per line):
    python3 scripts/workshop_week_prs.py --attendees attendees.txt

    # Specify attendees directly on the command line:
    python3 scripts/workshop_week_prs.py --attendees "user1,user2,user3"

Requires 'gh' (GitHub CLI) to be installed and authenticated.
"""

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

REPO = "leanprover-community/mathlib4"
START_DATE = "2026-03-02"
END_DATE = "2026-03-06"


def gh_search(query: str) -> list:
    """Run a GitHub search query and return all results using pagination."""
    items = []
    page = 1
    while True:
        cmd = [
            "gh", "api",
            f"search/issues?q={query}+type:pr&per_page=100&page={page}",
            "--jq", ".items",
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


def get_all_prs_created() -> list:
    """Fetch all PRs created during the workshop week."""
    return gh_search(f"repo:{REPO}+created:{START_DATE}..{END_DATE}")


def get_all_prs_closed() -> list:
    """Fetch all PRs closed during the workshop week."""
    return gh_search(f"repo:{REPO}+closed:{START_DATE}..{END_DATE}")


def get_prs_by_author(username: str) -> list:
    """Fetch PRs created by a user during the workshop week."""
    return gh_search(f"repo:{REPO}+created:{START_DATE}..{END_DATE}+author:{username}")


def get_prs_commented_by(username: str) -> list:
    """Fetch PRs that a user commented on during the workshop week.

    Uses the 'commenter' qualifier combined with an 'updated' window.  A PR is
    included if the user ever commented on it AND the PR was last updated during
    the workshop week.  This is a GitHub API limitation: the API does not expose
    a per-comment date filter, so some results may include comments posted
    outside the exact date range (e.g. if the PR was updated for other reasons).
    """
    return gh_search(
        f"repo:{REPO}+updated:{START_DATE}..{END_DATE}+commenter:{username}"
    )


def is_bors_merged(pr: dict) -> bool:
    """Check if a PR was merged by Bors (indicated by title prefix)."""
    return "[Merged by Bors]" in pr.get("title", "")


def get_original_title(pr: dict) -> str:
    """Strip the Bors prefix from a merged PR title."""
    return pr["title"].replace("[Merged by Bors] - ", "")


def load_attendees(attendees_arg: str) -> list[str]:
    """Load attendees from a file path or a comma-separated string."""
    path = Path(attendees_arg)
    if path.exists():
        names = [
            line.strip().lstrip("@")
            for line in path.read_text().splitlines()
            if line.strip() and not line.startswith("#")
        ]
        return names
    return [name.strip().lstrip("@") for name in attendees_arg.split(",") if name.strip()]


def run_all_contributors_report() -> None:
    """List every contributor who created or merged a PR (no attendee filter)."""
    print("Fetching PR data from GitHub...")
    created_prs = get_all_prs_created()
    closed_prs = get_all_prs_closed()

    merged_prs = [pr for pr in closed_prs if is_bors_merged(pr)]
    original_created = [pr for pr in created_prs if not is_bors_merged(pr)]

    print()
    print("=" * 80)
    print(f"ALL CONTRIBUTORS DURING WORKSHOP WEEK: {START_DATE} to {END_DATE}")
    print(f"Repository: {REPO}")
    print("=" * 80)
    print()
    print("NOTE: Re-run with --attendees to restrict output to workshop participants.")
    print()

    merged_by_author: dict[str, list] = defaultdict(list)
    for pr in merged_prs:
        merged_by_author[pr["user"]["login"]].append(pr)

    created_by_author: dict[str, list] = defaultdict(list)
    for pr in original_created:
        created_by_author[pr["user"]["login"]].append(pr)

    all_authors = set(merged_by_author) | set(created_by_author)
    human_authors = {a for a in all_authors if "[bot]" not in a}

    print(f"ALL UNIQUE HUMAN AUTHORS ({len(human_authors)} people):")
    print("Confirm which are at the workshop, then re-run with --attendees.")
    print("-" * 60)
    for author in sorted(human_authors):
        n_merged = len(merged_by_author.get(author, []))
        n_created = len(created_by_author.get(author, []))
        print(f"  @{author}: {n_merged} merged, {n_created} created")

    print()
    print(f"Total: {len(merged_prs)} PRs merged, {len(original_created)} PRs created")
    print(f"       {len(human_authors)} unique human contributors")


def run_attendee_report(attendees: list[str]) -> None:
    """Show PRs where at least one workshop attendee was involved."""
    print(f"Fetching activity for {len(attendees)} workshop attendee(s)...")

    # pr_number -> {'pr': dict, 'creators': set[str], 'commenters': set[str]}
    involved: dict[int, dict] = {}

    attendee_created: dict[str, list] = {}
    attendee_commented: dict[str, list] = {}

    for username in attendees:
        print(f"  @{username}...", end=" ", flush=True)

        created = [
            pr for pr in get_prs_by_author(username) if not is_bors_merged(pr)
        ]
        commented_raw = get_prs_commented_by(username)
        created_nums = {pr["number"] for pr in created}
        # Only keep PRs not authored by this attendee for the "commented" bucket
        commented = [
            pr for pr in commented_raw
            if pr["number"] not in created_nums and not is_bors_merged(pr)
        ]

        print(f"{len(created)} created, {len(commented)} commented")

        attendee_created[username] = created
        attendee_commented[username] = commented

        for pr in created:
            num = pr["number"]
            if num not in involved:
                involved[num] = {"pr": pr, "creators": set(), "commenters": set()}
            involved[num]["creators"].add(username)

        for pr in commented:
            num = pr["number"]
            if num not in involved:
                involved[num] = {"pr": pr, "creators": set(), "commenters": set()}
            involved[num]["commenters"].add(username)

    print()
    print("=" * 80)
    print(f"WORKSHOP ACTIVITY: {START_DATE} to {END_DATE}")
    print(f"Repository: {REPO}")
    attendee_list = ", ".join("@" + a for a in sorted(attendees))
    print(f"Attendees ({len(attendees)}): {attendee_list}")
    print("=" * 80)

    sorted_entries = sorted(involved.values(), key=lambda e: e["pr"]["number"])

    print()
    print(f"PRs INVOLVING WORKSHOP ATTENDEES ({len(involved)} total):")
    print("-" * 80)
    for entry in sorted_entries:
        pr = entry["pr"]
        creators = entry["creators"]
        commenters = entry["commenters"]
        title = get_original_title(pr)
        date = pr["created_at"][:10]
        state = "open" if pr["state"] == "open" else "closed"
        pr_author = pr["user"]["login"]
        if creators:
            involvement = "created by " + ", ".join("@" + u for u in sorted(creators))
        else:
            involvement = "commented by " + ", ".join("@" + u for u in sorted(commenters))
        print(f"  #{pr['number']} [{date}] @{pr_author} ({state}): {title[:55]}")
        print(f"    ↳ attendee {involvement}")

    print()
    print("ACTIVITY PER ATTENDEE:")
    print("-" * 50)
    for username in sorted(attendees):
        n_created = len(attendee_created.get(username, []))
        n_commented = len(attendee_commented.get(username, []))
        print(f"  @{username}: {n_created} PR(s) created, {n_commented} PR(s) commented on")

    n_created_prs = sum(1 for e in sorted_entries if e["creators"])
    n_comment_only = len(involved) - n_created_prs
    print()
    print(f"Summary: {len(involved)} PRs with attendee involvement")
    print(f"  - {n_created_prs} created by an attendee")
    print(f"  - {n_comment_only} commented on (but not created) by an attendee")


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
    args = parser.parse_args()

    if args.attendees:
        attendees = load_attendees(args.attendees)
        if not attendees:
            print("Error: No attendees found in the provided value.", file=sys.stderr)
            sys.exit(1)
        run_attendee_report(attendees)
    else:
        run_all_contributors_report()


if __name__ == "__main__":
    main()
