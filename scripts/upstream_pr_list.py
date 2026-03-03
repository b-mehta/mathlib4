#!/usr/bin/env python3

"""List PRs merged to leanprover-community/mathlib4 after a given date.

For each PR, outputs a JSON line with: number, title, author, created_at,
merged_at, and commenters (comment + review authors, excluding the PR author).

Uses the GitHub REST API via urllib (no external dependencies).
Set GITHUB_TOKEN env var for higher rate limits (5000/hr vs 60/hr anonymous).
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


def github_get(path: str, token: str | None) -> list | dict:
    """GET a GitHub API endpoint, handling pagination and rate limits."""
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
        try:
            with urllib.request.urlopen(req) as resp:
                data = json.loads(resp.read().decode())
                remaining = resp.headers.get("X-RateLimit-Remaining")
                if remaining and int(remaining) < 5:
                    reset_time = int(resp.headers.get("X-RateLimit-Reset", 0))
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
        except urllib.error.HTTPError as e:
            if e.code == 403 and "rate limit" in e.read().decode().lower():
                reset_time = int(e.headers.get("X-RateLimit-Reset", 0))
                wait = max(0, reset_time - int(time.time())) + 1
                print(f"Rate limited, waiting {wait}s...", file=sys.stderr)
                time.sleep(wait)
                continue
            raise

    return all_items


def get_merged_prs_from_git(start_date: str) -> dict[int, str]:
    """Get PR numbers and their merge timestamps from git log.

    Returns a dict mapping PR number to the ISO 8601 commit date (which is
    the merge time, since mathlib uses merge commits via Bors).
    """
    print("Fetching upstream master...", file=sys.stderr)
    subprocess.run(
        ["git", "fetch", UPSTREAM_URL, "master"],
        check=True,
        capture_output=True,
        text=True,
    )

    # Use --format to get both the commit date and the subject line
    result = subprocess.run(
        [
            "git", "log",
            f"--after={start_date}",
            "FETCH_HEAD",
            "--format=%aI %s",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    pr_merge_times: dict[int, str] = {}
    for line in result.stdout.splitlines():
        # Format: "2026-03-02T10:15:00+00:00 feat: something (#12345)"
        m = re.search(r"\(#(\d+)\)$", line.strip())
        if m:
            pr_num = int(m.group(1))
            # The date is everything before the first space in the subject,
            # but since %aI is the first token, split on first space
            date_str = line.split(" ", 1)[0]
            pr_merge_times[pr_num] = date_str

    print(
        f"Found {len(pr_merge_times)} merged PRs since {start_date}",
        file=sys.stderr,
    )
    return pr_merge_times


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


def fetch_pr_data(
    number: int, merge_time: str, token: str | None
) -> dict:
    """Fetch all data for a single PR (details, comments, reviews)."""
    pr = github_get(f"pulls/{number}", token)
    comments = github_get(f"issues/{number}/comments", token)
    reviews = github_get(f"pulls/{number}/reviews", token)

    author = pr.get("user", {})
    author_login = author.get("login", "ghost") if author else "ghost"

    # Prefer GitHub's merged_at; fall back to git log commit date
    merged_at = pr.get("merged_at") or merge_time

    return {
        "number": pr["number"],
        "title": pr["title"],
        "author": author_login,
        "created_at": pr["created_at"],
        "merged_at": merged_at,
        "commenters": extract_commenters(author_login, comments, reviews),
    }


def main():
    parser = argparse.ArgumentParser(
        description="List PRs merged to mathlib4 after a given date."
    )
    parser.add_argument(
        "--since",
        default=DEFAULT_START_DATE,
        help=f"ISO 8601 datetime cutoff (default: {DEFAULT_START_DATE})",
    )
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print(
            "Warning: GITHUB_TOKEN not set, using anonymous API access (60 req/hr).",
            file=sys.stderr,
        )
        print(
            "Set GITHUB_TOKEN env var for 5000 req/hr.",
            file=sys.stderr,
        )

    pr_merge_times = get_merged_prs_from_git(args.since)
    if not pr_merge_times:
        print("No PRs found.", file=sys.stderr)
        return

    sorted_numbers = sorted(pr_merge_times)
    total = len(sorted_numbers)
    print(f"Fetching details for {total} PRs (3 API calls each)...", file=sys.stderr)

    for i, number in enumerate(sorted_numbers, 1):
        print(f"  [{i}/{total}] PR #{number}...", file=sys.stderr)
        pr_data = fetch_pr_data(number, pr_merge_times[number], token)
        print(json.dumps(pr_data))
        sys.stdout.flush()

    print(f"Done. Output {total} PRs.", file=sys.stderr)


if __name__ == "__main__":
    main()
