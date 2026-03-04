#!/usr/bin/env python3

"""List PRs merged to leanprover-community/mathlib4 after a given date.

For each PR, outputs a JSON line with: number, title, author, merged_at.
Author is best-effort (GitHub username from noreply email, or raw email).
"""

import argparse
import json
import re
import subprocess
import sys

UPSTREAM_URL = "https://github.com/leanprover-community/mathlib4.git"
DEFAULT_START_DATE = "2026-03-02T09:00:00Z"


def _author_from_email(email: str) -> str:
    """Extract a GitHub username from a noreply email, or return the email."""
    m = re.match(r"(?:\d+\+)?(.+)@users\.noreply\.github\.com$", email)
    return m.group(1) if m else email


def _title_from_subject(subject: str) -> str:
    """Strip the trailing '(#NNN)' and optional '[Merged by Bors] - ' prefix."""
    title = re.sub(r"\s*\(#\d+\)$", "", subject)
    return re.sub(r"^\[Merged by Bors\]\s*-\s*", "", title)


def main():
    parser = argparse.ArgumentParser(
        description="List PRs merged to mathlib4 after a given date."
    )
    parser.add_argument(
        "--since", default=DEFAULT_START_DATE,
        help=f"ISO 8601 datetime cutoff (default: {DEFAULT_START_DATE})",
    )
    args = parser.parse_args()

    print("Fetching upstream master...", file=sys.stderr)
    subprocess.run(
        ["git", "fetch", f"--shallow-since={args.since}", UPSTREAM_URL, "master"],
        check=True, capture_output=True, text=True,
    )

    result = subprocess.run(
        ["git", "log", f"--after={args.since}", "FETCH_HEAD", "--format=%aI\t%ae\t%s"],
        check=True, capture_output=True, text=True,
    )

    prs: list[dict] = []
    for line in result.stdout.splitlines():
        parts = line.split("\t", 2)
        if len(parts) != 3:
            continue
        date_str, email, subject = parts
        m = re.search(r"\(#(\d+)\)$", subject)
        if not m:
            continue
        prs.append({
            "number": int(m.group(1)),
            "title": _title_from_subject(subject),
            "author": _author_from_email(email),
            "merged_at": date_str,
        })

    prs.sort(key=lambda p: p["merged_at"])
    for pr in prs:
        print(json.dumps(pr))
    print(f"Done. Output {len(prs)} PRs.", file=sys.stderr)


if __name__ == "__main__":
    main()
