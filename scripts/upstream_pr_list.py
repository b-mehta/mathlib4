#!/usr/bin/env python3
"""List PRs merged to mathlib4 after a given date as JSON lines."""

import json
import re
import subprocess
import sys
import time
import urllib.request
import urllib.error

REPO = "leanprover-community/mathlib4"
UPSTREAM_URL = f"https://github.com/{REPO}.git"
SINCE = sys.argv[1] if len(sys.argv) > 1 else "2026-03-02T09:00:00Z"

# Workshop attendees (GitHub usernames, case-insensitive matching)
ATTENDEES = {
    "joelriou",
    "chrisflav",
    "tb65536",
    "EtienneC30",
    "MichaelStollBayreuth",
    "justus-springer",
    "RemyDegenne",
    "kc_kennylau",
    "grunweg",
    "smorel394",
    "mariainesdff",
    "bhavikmehta8",
    "smmercuri",
    "kebekus",
    "DavidLedvinka",
    "Whysoserioushah",
    "erdOne",
    "vdoorn",
    "hrmacbeth",
}
_ATTENDEES_LOWER = {a.lower() for a in ATTENDEES}


def is_attendee(author: str) -> bool:
    return author.lower() in _ATTENDEES_LOWER


def gh_api_get(path: str) -> dict | None:
    """Try gh CLI first, fall back to unauthenticated curl."""
    try:
        r = subprocess.run(
            ["gh", "api", path, "--jq", ".user.login"],
            capture_output=True, text=True, timeout=10,
        )
        if r.returncode == 0 and r.stdout.strip():
            return r.stdout.strip()
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    # Fall back to unauthenticated REST
    url = f"https://api.github.com/{path}"
    req = urllib.request.Request(url, headers={"Accept": "application/vnd.github+json"})
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read())
            return data.get("user", {}).get("login")
    except (urllib.error.URLError, json.JSONDecodeError, KeyError):
        return None


def resolve_authors(prs: list[dict]) -> dict[str, str]:
    """Resolve emails -> GitHub usernames for PRs with unresolved authors.

    Groups by email so we only make one API call per unique email, not per PR.
    """
    # Collect one PR number per unresolved email
    email_to_pr: dict[str, int] = {}
    for pr in prs:
        author = pr["author"]
        if "@" in author and author not in email_to_pr:
            email_to_pr[author] = pr["number"]

    if not email_to_pr:
        return {}

    print(f"Resolving {len(email_to_pr)} author(s) via GitHub API...", file=sys.stderr)
    email_to_username: dict[str, str] = {}
    for email, pr_num in email_to_pr.items():
        login = gh_api_get(f"repos/{REPO}/pulls/{pr_num}")
        if login:
            email_to_username[email] = login
            print(f"  {email} -> @{login}", file=sys.stderr)
        else:
            print(f"  {email} -> (could not resolve)", file=sys.stderr)
        time.sleep(0.5)  # Be polite to the API

    return email_to_username


print("Fetching upstream master...", file=sys.stderr)
subprocess.run(
    ["git", "fetch", f"--shallow-since={SINCE}", UPSTREAM_URL, "master"],
    check=True, capture_output=True, text=True,
)

result = subprocess.run(
    ["git", "log", "--reverse", f"--after={SINCE}", "FETCH_HEAD", "--format=%aI\t%ae\t%s"],
    check=True, capture_output=True, text=True,
)

# First pass: extract PRs from git log
prs: list[dict] = []
for line in result.stdout.splitlines():
    parts = line.split("\t", 2)
    if len(parts) != 3:
        continue
    date_str, email, subject = parts
    m = re.search(r"\(#(\d+)\)$", subject)
    if not m:
        continue
    # Extract GitHub username from noreply email if possible
    author_m = re.match(r"(?:\d+\+)?(.+)@users\.noreply\.github\.com$", email)
    title = re.sub(r"\s*\(#\d+\)$", "", subject)
    title = re.sub(r"^\[Merged by Bors\]\s*-\s*", "", title)
    prs.append({
        "number": int(m.group(1)),
        "title": title,
        "author": author_m.group(1) if author_m else email,
        "merged_at": date_str,
    })

# Second pass: resolve unresolved authors via API
email_to_username = resolve_authors(prs)
for pr in prs:
    if pr["author"] in email_to_username:
        pr["author"] = email_to_username[pr["author"]]

# Classify PRs
attendee_prs = [pr for pr in prs if is_attendee(pr["author"])]
other_prs = [pr for pr in prs if not is_attendee(pr["author"])]

print(f"=== Workshop attendee PRs ({len(attendee_prs)}) ===")
for pr in attendee_prs:
    print(json.dumps(pr))

print(f"\n=== Non-attendee PRs ({len(other_prs)}) ===")
for pr in other_prs:
    print(json.dumps(pr))

print(f"\nDone. {len(attendee_prs)} attendee PRs, {len(other_prs)} non-attendee PRs, {len(prs)} total.", file=sys.stderr)
