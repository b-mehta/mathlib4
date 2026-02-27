#!/bin/bash
# Session-start hook for mathlib4 — only runs in Claude Code web environments.
# Installs: gh, lean4-skills plugin, elan/lake, ripgrep, eza

[ "${CLAUDE_CODE_REMOTE:-}" = "true" ] || exit 0

log() { echo "[session-start] $*"; }

# --- gh (GitHub CLI) ---
if ! command -v gh &>/dev/null; then
  log "Installing gh..."
  curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg \
    | sudo tee /usr/share/keyrings/githubcli-archive-keyring.gpg >/dev/null
  echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" \
    | sudo tee /etc/apt/sources.list.d/github-cli.list >/dev/null
  sudo apt-get update -qq && sudo apt-get install -y -qq gh
fi

# --- lean4-skills plugin ---
PLUGIN_DIR="$HOME/.claude/plugins/cache/lean4-skills"
if [ ! -d "$PLUGIN_DIR" ]; then
  log "Installing lean4-skills plugin..."
  tmp="$(mktemp -d)"
  git clone --depth 1 https://github.com/cameronfreer/lean4-skills.git "$tmp/repo"
  mkdir -p "$PLUGIN_DIR"
  cp -r "$tmp/repo/." "$PLUGIN_DIR/"
  # Copy skills to personal skills directory as a fallback
  for d in "$tmp/repo/plugins/lean4/skills" "$tmp/repo/skills"; do
    [ -d "$d" ] && cp -r "$d/"* "$HOME/.claude/skills/" 2>/dev/null || true
  done
  rm -rf "$tmp"
fi

# --- elan + lake ---
if ! command -v elan &>/dev/null; then
  log "Installing elan..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
  echo "export PATH=\"\$HOME/.elan/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE"
fi

# Install the project's toolchain (gives us lake)
if [ -f lean-toolchain ] && command -v elan &>/dev/null; then
  elan toolchain install "$(cat lean-toolchain | tr -d '[:space:]')" 2>/dev/null || true
fi

# --- ripgrep & eza ---
if ! command -v rg &>/dev/null || ! command -v eza &>/dev/null; then
  log "Installing ripgrep and eza..."
  sudo apt-get update -qq && sudo apt-get install -y -qq ripgrep eza
fi

log "Done."
