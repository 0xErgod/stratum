#!/usr/bin/env bash
# Build the release stratum-kernel binary and register it as a Jupyter kernel.
#
# This writes a kernelspec whose argv[0] is the ABSOLUTE path to the freshly
# built binary, then installs it with `jupyter kernelspec install`. Re-run after
# rebuilding if the binary moves.
#
# Usage: ./install.sh [--user]     (default: --user; pass nothing for a system install)
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$here/../.." && pwd)"

echo ">> building release binary…"
cargo build --release --manifest-path "$repo_root/Cargo.toml" -p stratum-kernel

bin="$repo_root/target/release/stratum-kernel"
[[ "${OS:-}" == "Windows_NT" ]] && bin="$bin.exe"
if [[ ! -f "$bin" ]]; then
  echo "!! built binary not found at $bin" >&2
  exit 1
fi

# argv[0] must be a path the Jupyter launcher can exec. On Windows that launcher
# is native Python, which cannot run an MSYS/Cygwin `/z/...` path — convert to a
# forward-slash Windows path (e.g. Z:/…/stratum-kernel.exe) with `cygpath -m`,
# valid both in JSON and for the launcher.
argv0="$bin"
if [[ "${OS:-}" == "Windows_NT" ]] && command -v cygpath >/dev/null 2>&1; then
  argv0="$(cygpath -m "$bin")"
fi

staging="$(mktemp -d)/stratum"
mkdir -p "$staging"

# Rewrite argv[0] in the committed kernelspec (kernelspec/kernel.json) to the
# absolute binary path. Read/write as UTF-8 so a non-ASCII description does not
# trip Windows' default cp1252 codec.
python3 - "$here/kernelspec/kernel.json" "$argv0" "$staging/kernel.json" <<'PY'
import json, sys
src, binpath, dst = sys.argv[1:4]
with open(src, encoding="utf-8") as f:
    spec = json.load(f)
spec["argv"][0] = binpath
with open(dst, "w", encoding="utf-8") as f:
    json.dump(spec, f, indent=2)
print(">> kernelspec argv[0] ->", binpath)
PY

scope="${1:---user}"
echo ">> jupyter kernelspec install $scope --name stratum"
jupyter kernelspec install "$scope" --replace --name stratum "$staging"

echo ">> done. Open JupyterLab or a VS Code notebook and pick the 'Stratum' kernel."
