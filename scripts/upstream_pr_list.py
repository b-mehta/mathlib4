#!/usr/bin/env python3
"""List PRs merged to mathlib4 after a given date, split by workshop attendee status."""

import json, re, subprocess, sys, time

REPO = "leanprover-community/mathlib4"
SINCE = sys.argv[1] if len(sys.argv) > 1 else "2026-03-02T09:00:00Z"
ATTENDEES = {s.lower() for s in [
    "joelriou", "chrisflav", "tb65536", "EtienneC30", "MichaelStollBayreuth",
    "justus-springer", "RemyDegenne", "kc_kennylau", "grunweg", "smorel394",
    "mariainesdff", "bhavikmehta8", "b-mehta", "smmercuri", "kebekus",
    "DavidLedvinka", "Whysoserioushah", "erdOne", "vdoorn", "hrmacbeth",
]}

def run(*cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def gh_login(pr_num):
    r = run("gh", "api", f"repos/{REPO}/pulls/{pr_num}", "--jq", ".user.login", timeout=10)
    return r.stdout.strip() or None

# Fetch and parse git log
print("Fetching upstream master...", file=sys.stderr)
run("git", "fetch", f"--shallow-since={SINCE}", f"https://github.com/{REPO}.git", "master", check=True)
log = run("git", "log", "--reverse", f"--after={SINCE}", "FETCH_HEAD",
          "--format=%aI\t%ae\t%s", check=True).stdout

# Extract PRs
prs = []
for line in log.splitlines():
    parts = line.split("\t", 2)
    if len(parts) != 3:
        continue
    date, email, subject = parts
    m = re.search(r"\(#(\d+)\)$", subject)
    if not m:
        continue
    noreply = re.match(r"(?:\d+\+)?(.+)@users\.noreply\.github\.com$", email)
    prs.append({
        "number": int(m.group(1)),
        "title": re.sub(r"^\[Merged by Bors\]\s*-\s*", "", re.sub(r"\s*\(#\d+\)$", "", subject)),
        "author": noreply.group(1) if noreply else email,
        "merged_at": date,
    })

# Resolve raw emails to GitHub usernames
emails = {pr["author"]: pr["number"] for pr in prs if "@" in pr["author"]}
resolved = {}
for email, pr_num in emails.items():
    login = gh_login(pr_num)
    print(f"  {email} -> {f'@{login}' if login else '?'}", file=sys.stderr)
    if login:
        resolved[email] = login
    time.sleep(0.5)
for pr in prs:
    pr["author"] = resolved.get(pr["author"], pr["author"])

# Output split by attendee status
for label, pred in [("Workshop attendee", True), ("Non-attendee", False)]:
    group = [pr for pr in prs if (pr["author"].lower() in ATTENDEES) == pred]
    print(f"=== {label} PRs ({len(group)}) ===")
    for pr in group:
        print(json.dumps(pr))
    print()

print(f"Done. {len(prs)} total PRs.", file=sys.stderr)
