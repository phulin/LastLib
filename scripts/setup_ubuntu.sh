#!/usr/bin/env bash

# Provision LastLib and LastLib Swarm on a fresh Ubuntu 26.04 installation.
# Run this script as your normal user from any directory. It uses sudo only for
# Ubuntu packages; uv, Volta, elan, Lean, and Codex are installed for the current user.

set -Eeuo pipefail
IFS=$'\n\t'

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
readonly SCRIPT_DIR
REPO_ROOT="$(cd -- "${SCRIPT_DIR}/.." && pwd)"
readonly REPO_ROOT

log() {
  printf '\n==> %s\n' "$*"
}

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

if [[ ! -r /etc/os-release ]]; then
  die "cannot identify the operating system (/etc/os-release is missing)"
fi

# shellcheck disable=SC1091
source /etc/os-release
if [[ "${ID:-}" != "ubuntu" || "${VERSION_ID:-}" != "26.04" ]]; then
  die "this setup script requires Ubuntu 26.04 (found ${PRETTY_NAME:-unknown})"
fi

if [[ "${EUID}" -eq 0 ]]; then
  APT=(apt-get)
else
  command -v sudo >/dev/null 2>&1 || die "sudo is required to install Ubuntu packages"
  APT=(sudo apt-get)
fi

log "Installing Ubuntu packages"
"${APT[@]}" update
"${APT[@]}" install -y \
  build-essential \
  ca-certificates \
  curl \
  fish \
  fuse3 \
  fuse-overlayfs \
  git \
  htop \
  neovim \
  pkg-config \
  ripgrep \
  rsync \
  tmux

SETUP_TMP_DIR="$(mktemp -d)"
readonly SETUP_TMP_DIR
cleanup() {
  rm -rf -- "${SETUP_TMP_DIR}"
}
trap cleanup EXIT

download_installer() {
  local name="$1"
  local url="$2"
  local destination="${SETUP_TMP_DIR}/${name}.sh"

  curl --proto '=https' --tlsv1.2 --fail --silent --show-error --location \
    --output "${destination}" "${url}"
  sh "${destination}" "${@:3}"
}

export VOLTA_HOME="${HOME}/.volta"
export PATH="${HOME}/.local/bin:${HOME}/.elan/bin:${VOLTA_HOME}/bin:${PATH}"

if ! command -v uv >/dev/null 2>&1; then
  log "Installing uv"
  UV_NO_MODIFY_PATH=1 download_installer uv https://astral.sh/uv/install.sh
else
  log "uv is already installed"
fi

if ! command -v volta >/dev/null 2>&1; then
  log "Installing Volta"
  download_installer volta https://get.volta.sh
else
  log "Volta is already installed"
fi

if ! command -v elan >/dev/null 2>&1; then
  log "Installing elan"
  download_installer elan https://elan.lean-lang.org/elan-init.sh \
    -y --default-toolchain none
else
  log "elan is already installed"
fi

log "Persisting user-installed tools on the Fish PATH"
fish -c 'fish_add_path --universal "$HOME/.local/bin" "$HOME/.elan/bin" "$VOLTA_HOME/bin"'

log "Installing or updating Codex from OpenAI"
download_installer codex https://chatgpt.com/codex/install.sh < <(yes n)

log "Installing the pinned Python and project dependencies"
PYTHON_VERSION="$(tr -d '[:space:]' < "${REPO_ROOT}/.python-version")"
readonly PYTHON_VERSION
uv python install "${PYTHON_VERSION}"
uv sync --project "${REPO_ROOT}" --all-groups --locked

log "Installing the pinned Lean toolchain"
LEAN_TOOLCHAIN="$(tr -d '[:space:]' < "${REPO_ROOT}/lean/lean-toolchain")"
readonly LEAN_TOOLCHAIN
if elan toolchain list | sed 's/ (default)$//' | grep -Fxq -- "${LEAN_TOOLCHAIN}"; then
  log "Lean toolchain ${LEAN_TOOLCHAIN} is already installed"
else
  elan toolchain install "${LEAN_TOOLCHAIN}"
fi

log "Fetching pinned Lake dependencies"
if [[ ! -d "${REPO_ROOT}/lean/.lake/packages/mathlib" ]]; then
  (
    cd "${REPO_ROOT}/lean"
    lake update
  )
fi

log "Downloading the Mathlib build cache"
(
  cd "${REPO_ROOT}/lean"
  lake exe cache get
)

log "Checking the installed command-line tools"
volta --version
uv run --project "${REPO_ROOT}" lastlib-swarm --help >/dev/null
(
  cd "${REPO_ROOT}/lean"
  lake env lean --version
)
codex --version

if [[ ! -e /dev/fuse ]]; then
  printf '\nwarning: /dev/fuse is unavailable. LastLib Swarm will use its slower shared isolation mode.\n' >&2
fi

cat <<EOF

Setup complete.

Open a new Fish shell to use the persisted paths for user-installed tools.

Then authenticate Codex interactively once:
  codex

From ${REPO_ROOT}, a useful smoke test is:
  uv run lastlib-swarm plan books/
EOF
