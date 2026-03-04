#!/usr/bin/env python3
"""List PRs merged to mathlib4 after a given date as JSON lines."""

import json
import re
import subprocess
import sys

UPSTREAM_URL = "https://github.com/leanprover-community/mathlib4.git"
SINCE = sys.argv[1] if len(sys.argv) > 1 else "2026-03-02T09:00:00Z"

print("Fetching upstream master...", file=sys.stderr)
subprocess.run(
    ["git", "fetch", f"--shallow-since={SINCE}", UPSTREAM_URL, "master"],
    check=True, capture_output=True, text=True,
)

result = subprocess.run(
    ["git", "log", "--reverse", f"--after={SINCE}", "FETCH_HEAD", "--format=%aI\t%ae\t%s"],
    check=True, capture_output=True, text=True,
)

count = 0
for line in result.stdout.splitlines():
    parts = line.split("\t", 2)
    if len(parts) != 3:
        continue
    date_str, email, subject = parts
    m = re.search(r"\(#(\d+)\)$", subject)
    if not m:
        continue
    # Extract GitHub username from noreply email if possible
    author = re.match(r"(?:\d+\+)?(.+)@users\.noreply\.github\.com$", email)
    # Strip trailing (#NNN) and [Merged by Bors] prefix from title
    title = re.sub(r"\s*\(#\d+\)$", "", subject)
    title = re.sub(r"^\[Merged by Bors\]\s*-\s*", "", title)
    print(json.dumps({
        "number": int(m.group(1)),
        "title": title,
        "author": author.group(1) if author else email,
        "merged_at": date_str,
    }))
    count += 1

print(f"Done. Output {count} PRs.", file=sys.stderr)
