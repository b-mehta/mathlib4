#!/bin/bash
set -uo pipefail
# NOTE: we intentionally do NOT set -e so that one step failing
# does not prevent subsequent steps from running.

# Only run in remote (Claude Code web) environments
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

###############################################################################
# Session-start hook for mathlib4 Claude Code web environment
#
# Installs:
#   1. GitHub CLI (gh)
#   2. lean4-skills Claude Code plugin (cameronfreer/lean4-skills)
#   3. elan + lake (Lean 4 toolchain manager and build system)
###############################################################################

# --------------------------------------------------------------------------- #
# 1. Install GitHub CLI (gh)
#    Uses conda-forge binary (works without apt repos being reachable).
#    Falls back to apt if conda is unavailable.
# --------------------------------------------------------------------------- #
if ! command -v gh &>/dev/null; then
  echo "[session-start] Installing GitHub CLI (gh)..."
  if command -v conda &>/dev/null; then
    conda install -y -c conda-forge gh 2>/dev/null
  else
    (
      curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg \
        | sudo dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg 2>/dev/null
      sudo chmod go+r /usr/share/keyrings/githubcli-archive-keyring.gpg
      echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" \
        | sudo tee /etc/apt/sources.list.d/github-cli.list >/dev/null
      sudo apt-get update -qq
      sudo apt-get install -y -qq gh
    )
  fi
  if command -v gh &>/dev/null; then
    echo "[session-start] gh installed: $(gh --version | head -1)"
  else
    echo "[session-start] WARNING: gh installation failed - will retry next session"
  fi
else
  echo "[session-start] gh already installed: $(gh --version | head -1)"
fi

# --------------------------------------------------------------------------- #
# 2. Install lean4-skills plugin (cameronfreer/lean4-skills)
#    Copies plugin files to ~/.claude/plugins/ and registers it.
# --------------------------------------------------------------------------- #
PLUGIN_CACHE_DIR="$HOME/.claude/plugins/cache/lean4-skills"
if [ ! -d "$PLUGIN_CACHE_DIR" ]; then
  echo "[session-start] Installing lean4-skills plugin..."
  TMPDIR_PLUGIN="$(mktemp -d)"
  git clone --depth 1 https://github.com/cameronfreer/lean4-skills.git "$TMPDIR_PLUGIN/lean4-skills"

  # Copy to the plugin cache location that Claude Code expects
  mkdir -p "$PLUGIN_CACHE_DIR"
  cp -r "$TMPDIR_PLUGIN/lean4-skills/." "$PLUGIN_CACHE_DIR/"

  # Also make the skills available as personal skills so they activate
  # regardless of plugin system state
  if [ -d "$TMPDIR_PLUGIN/lean4-skills/plugins/lean4/skills" ]; then
    cp -r "$TMPDIR_PLUGIN/lean4-skills/plugins/lean4/skills/"* "$HOME/.claude/skills/" 2>/dev/null || true
  fi
  if [ -d "$TMPDIR_PLUGIN/lean4-skills/skills" ]; then
    cp -r "$TMPDIR_PLUGIN/lean4-skills/skills/"* "$HOME/.claude/skills/" 2>/dev/null || true
  fi

  rm -rf "$TMPDIR_PLUGIN"
  echo "[session-start] lean4-skills plugin installed to $PLUGIN_CACHE_DIR"
else
  echo "[session-start] lean4-skills plugin already installed"
fi

# --------------------------------------------------------------------------- #
# 3. Install elan (Lean version manager) and lake (Lean build system)
#    elan manages Lean toolchains; lake ships bundled with each toolchain.
# --------------------------------------------------------------------------- #
if ! command -v elan &>/dev/null; then
  echo "[session-start] Installing elan (Lean toolchain manager)..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  # Make elan/lake available in this session
  export PATH="$HOME/.elan/bin:$PATH"
  echo "export PATH=\"\$HOME/.elan/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE"
  echo "[session-start] elan installed: $(elan --version)"
else
  echo "[session-start] elan already installed: $(elan --version)"
fi

# Install the toolchain specified by this project's lean-toolchain file
if [ -f lean-toolchain ] && command -v elan &>/dev/null; then
  TOOLCHAIN="$(cat lean-toolchain | tr -d '[:space:]')"
  if ! elan toolchain list | grep -q "$(echo "$TOOLCHAIN" | sed 's|.*/||')"; then
    echo "[session-start] Installing Lean toolchain: $TOOLCHAIN ..."
    elan toolchain install "$TOOLCHAIN"
  else
    echo "[session-start] Lean toolchain already installed: $TOOLCHAIN"
  fi
fi

if command -v lake &>/dev/null; then
  echo "[session-start] lake available: $(lake --version 2>/dev/null || echo 'version unknown')"
else
  echo "[session-start] Warning: lake not found in PATH after elan install"
fi

echo "[session-start] Environment setup complete."
