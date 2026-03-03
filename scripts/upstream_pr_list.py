#!/usr/bin/env python3

"""List PRs merged to leanprover-community/mathlib4 after a given date.

For each PR, outputs a JSON line with: number, title, author, created_at,
merged_at, and commenters (comment + review authors, excluding the PR author).

Requires the GitHub CLI (gh) to be installed and authenticated.
"""

import argparse
import json
import re
import shutil
import subprocess
import sys

REPO_OWNER = "leanprover-community"
REPO_NAME = "mathlib4"
UPSTREAM_URL = f"https://github.com/{REPO_OWNER}/{REPO_NAME}.git"
DEFAULT_START_DATE = "2026-03-02T09:00:00Z"
BATCH_SIZE = 30

PR_FIELDS = """
  number
  title
  author { login }
  createdAt
  mergedAt
  comments(first: 100) {
    nodes { author { login } }
    pageInfo { hasNextPage }
  }
  reviews(first: 100) {
    nodes { author { login } }
    pageInfo { hasNextPage }
  }
"""


def check_gh_installed():
    """Check if GitHub CLI (gh) is installed and accessible."""
    if not shutil.which("gh"):
        print("Error: GitHub CLI (gh) is not installed or not in PATH", file=sys.stderr)
        print("Install it from https://cli.github.com/", file=sys.stderr)
        sys.exit(1)


def get_merged_pr_numbers(start_date: str) -> set[int]:
    """Get PR numbers merged after start_date by inspecting git log."""
    print(f"Fetching upstream master...", file=sys.stderr)
    subprocess.run(
        ["git", "fetch", UPSTREAM_URL, "master"],
        check=True,
        capture_output=True,
        text=True,
    )

    result = subprocess.run(
        ["git", "log", f"--after={start_date}", "FETCH_HEAD", "--oneline"],
        check=True,
        capture_output=True,
        text=True,
    )

    pr_numbers: set[int] = set()
    for line in result.stdout.splitlines():
        m = re.search(r"\(#(\d+)\)$", line.strip())
        if m:
            pr_numbers.add(int(m.group(1)))

    print(f"Found {len(pr_numbers)} merged PRs since {start_date}", file=sys.stderr)
    return pr_numbers


def fetch_pr_details_batch(numbers: list[int]) -> list[dict]:
    """Fetch details for a batch of PRs using a single GraphQL query."""
    aliases = []
    for n in numbers:
        aliases.append(f'  pr{n}: pullRequest(number: {n}) {{{PR_FIELDS}}}')

    query = (
        "{\n"
        f'  repository(owner: "{REPO_OWNER}", name: "{REPO_NAME}") {{\n'
        + "\n".join(aliases)
        + "\n  }\n}"
    )

    result = subprocess.run(
        ["gh", "api", "graphql", "-f", f"query={query}"],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"GraphQL query failed: {result.stderr}", file=sys.stderr)
        sys.exit(1)

    data = json.loads(result.stdout)
    repo_data = data["data"]["repository"]

    prs = []
    for n in numbers:
        pr_data = repo_data.get(f"pr{n}")
        if pr_data:
            prs.append(pr_data)
    return prs


def fetch_all_pr_details(numbers: set[int]) -> list[dict]:
    """Fetch details for all PRs, batching into groups of BATCH_SIZE."""
    sorted_numbers = sorted(numbers)
    all_prs = []

    for i in range(0, len(sorted_numbers), BATCH_SIZE):
        batch = sorted_numbers[i : i + BATCH_SIZE]
        print(
            f"Fetching PR details batch {i // BATCH_SIZE + 1} "
            f"({len(batch)} PRs)...",
            file=sys.stderr,
        )
        all_prs.extend(fetch_pr_details_batch(batch))

    return all_prs


def extract_commenters(pr_data: dict) -> list[str]:
    """Extract unique commenter logins from comments and reviews."""
    commenters: set[str] = set()

    for comment in pr_data.get("comments", {}).get("nodes", []):
        if comment and comment.get("author") and comment["author"].get("login"):
            commenters.add(comment["author"]["login"])

    for review in pr_data.get("reviews", {}).get("nodes", []):
        if review and review.get("author") and review["author"].get("login"):
            commenters.add(review["author"]["login"])

    # Warn if comments or reviews were truncated
    comments_pi = pr_data.get("comments", {}).get("pageInfo", {})
    reviews_pi = pr_data.get("reviews", {}).get("pageInfo", {})
    if comments_pi.get("hasNextPage") or reviews_pi.get("hasNextPage"):
        pr_num = pr_data.get("number", "?")
        print(
            f"Warning: PR #{pr_num} has >100 comments/reviews, "
            f"commenter list may be incomplete",
            file=sys.stderr,
        )

    # Remove PR author from commenters
    author = pr_data.get("author")
    if author and author.get("login"):
        commenters.discard(author["login"])

    return sorted(commenters)


def format_pr(pr_data: dict) -> dict:
    """Format a PR into the output dict."""
    author = pr_data.get("author")
    author_login = author["login"] if author and author.get("login") else "ghost"

    return {
        "number": pr_data["number"],
        "title": pr_data["title"],
        "author": author_login,
        "created_at": pr_data["createdAt"],
        "merged_at": pr_data.get("mergedAt"),
        "commenters": extract_commenters(pr_data),
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

    check_gh_installed()

    pr_numbers = get_merged_pr_numbers(args.since)
    if not pr_numbers:
        print("No PRs found.", file=sys.stderr)
        return

    prs = fetch_all_pr_details(pr_numbers)
    prs.sort(key=lambda p: p["number"])

    for pr_data in prs:
        print(json.dumps(format_pr(pr_data)))

    print(f"Output {len(prs)} PRs.", file=sys.stderr)


if __name__ == "__main__":
    main()
