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
if [[ ! -x "$bin" && ! -f "$bin" ]]; then
  echo "!! built binary not found at $bin" >&2
  exit 1
fi

staging="$(mktemp -d)/stratum"
mkdir -p "$staging"

# Rewrite argv[0] in the kernelspec to the absolute binary path.
python3 - "$here/kernel.json" "$bin" "$staging/kernel.json" <<'PY'
import json, sys
src, binpath, dst = sys.argv[1:4]
spec = json.load(open(src))
spec["argv"][0] = binpath
json.dump(spec, open(dst, "w"), indent=2)
print(">> kernelspec argv[0] ->", binpath)
PY

scope="${1:---user}"
echo ">> jupyter kernelspec install $scope --name stratum"
jupyter kernelspec install "$scope" --replace --name stratum "$staging"

echo ">> done. Open JupyterLab and pick the 'Stratum' kernel."
