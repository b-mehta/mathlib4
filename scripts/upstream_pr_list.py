#!/usr/bin/env python3
"""List PRs merged to mathlib4 after a given date, split by workshop attendee status."""

import json
import re
import subprocess
import sys
import time

REPO = "leanprover-community/mathlib4"
SINCE = sys.argv[1] if len(sys.argv) > 1 else "2026-03-02T09:00:00Z"

ATTENDEES = {s.lower() for s in [
    "joelriou", "chrisflav", "tb65536", "EtienneC30", "MichaelStollBayreuth",
    "justus-springer", "RemyDegenne", "kc_kennylau", "grunweg", "smorel394",
    "mariainesdff", "bhavikmehta8", "b-mehta", "smmercuri", "kebekus",
    "DavidLedvinka", "Whysoserioushah", "erdOne", "vdoorn", "hrmacbeth",
]}

NOREPLY_RE = re.compile(r"(?:\d+\+)?(.+)@users\.noreply\.github\.com$")
PR_NUM_RE = re.compile(r"\(#(\d+)\)$")


def resolve_email(email: str, pr_num: int) -> str | None:
    """Resolve a git email to a GitHub username via the API."""
    r = subprocess.run(
        ["gh", "api", f"repos/{REPO}/pulls/{pr_num}", "--jq", ".user.login"],
        capture_output=True, text=True, timeout=10,
    )
    return r.stdout.strip() or None if r.returncode == 0 else None


# Fetch and parse git log
print("Fetching upstream master...", file=sys.stderr)
subprocess.run(
    ["git", "fetch", f"--shallow-since={SINCE}",
     f"https://github.com/{REPO}.git", "master"],
    check=True, capture_output=True, text=True,
)
log = subprocess.run(
    ["git", "log", "--reverse", f"--after={SINCE}", "FETCH_HEAD",
     "--format=%aI\t%ae\t%s"],
    check=True, capture_output=True, text=True,
).stdout

# Extract PRs
prs: list[dict] = []
for line in log.splitlines():
    parts = line.split("\t", 2)
    if len(parts) != 3:
        continue
    date_str, email, subject = parts
    m = PR_NUM_RE.search(subject)
    if not m:
        continue
    noreply = NOREPLY_RE.match(email)
    title = PR_NUM_RE.sub("", subject).strip()
    title = re.sub(r"^\[Merged by Bors\]\s*-\s*", "", title)
    prs.append({
        "number": int(m.group(1)),
        "title": title,
        "author": noreply.group(1) if noreply else email,
        "merged_at": date_str,
    })

# Resolve raw emails to GitHub usernames (one API call per unique email)
emails = {pr["author"]: pr["number"] for pr in prs if "@" in pr["author"]}
resolved: dict[str, str] = {}
if emails:
    print(f"Resolving {len(emails)} author(s) via GitHub API...", file=sys.stderr)
for email, pr_num in emails.items():
    login = resolve_email(email, pr_num)
    print(f"  {email} -> {f'@{login}' if login else '(unknown)'}", file=sys.stderr)
    if login:
        resolved[email] = login
    time.sleep(0.5)
for pr in prs:
    pr["author"] = resolved.get(pr["author"], pr["author"])

# Output, split by attendee status
attendee = [pr for pr in prs if pr["author"].lower() in ATTENDEES]
other = [pr for pr in prs if pr["author"].lower() not in ATTENDEES]

print(f"=== Workshop attendee PRs ({len(attendee)}) ===")
for pr in attendee:
    print(json.dumps(pr))
print(f"\n=== Non-attendee PRs ({len(other)}) ===")
for pr in other:
    print(json.dumps(pr))

print(f"\nDone. {len(attendee)} attendee, {len(other)} non-attendee, {len(prs)} total.",
      file=sys.stderr)
