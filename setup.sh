#!/usr/bin/env bash
# Set up Lean 4, the Lean REPL, and the part of Mathlib this engine's targets need.
# Tested on Linux x86_64 (2 cores, 7 GB RAM): about 25 minutes, mostly compiling Mathlib.
#
#   ./setup.sh            build only the Mathlib modules the blueprint imports (~2,000 files)
#   FULL_MATHLIB=1 ./setup.sh   use the whole of Mathlib via its download cache (fast if reachable)
#
# Everything goes under $WORKDIR (default: ./lean-workspace).
set -euo pipefail

WORKDIR="${WORKDIR:-$PWD/lean-workspace}"
mkdir -p "$WORKDIR" && cd "$WORKDIR"
export PATH="$HOME/.elan/bin:$PATH"

# 1. elan (Lean version manager), from its GitHub release
if ! command -v elan >/dev/null; then
  case "$(uname -s)-$(uname -m)" in
    Linux-x86_64)  ASSET=elan-x86_64-unknown-linux-gnu.tar.gz ;;
    Linux-aarch64) ASSET=elan-aarch64-unknown-linux-gnu.tar.gz ;;
    Darwin-arm64)  ASSET=elan-aarch64-apple-darwin.tar.gz ;;
    Darwin-x86_64) ASSET=elan-x86_64-apple-darwin.tar.gz ;;
    *) echo "unsupported platform"; exit 1 ;;
  esac
  curl -sSfL -o elan.tar.gz "https://github.com/leanprover/elan/releases/latest/download/$ASSET"
  tar xzf elan.tar.gz && ./elan-init -y --default-toolchain none --no-modify-path
fi

# 2. The Lean version Mathlib master uses
TC=$(curl -sSfL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain)
echo "Mathlib uses $TC"
elan toolchain install "$TC" || {
  # fallback when release.lean-lang.org is unreachable: take the release from GitHub
  V=${TC#leanprover/lean4:}
  case "$(uname -s)" in Linux) OS=linux ;; Darwin) OS=darwin ;; esac
  [ "$(uname -m)" = "aarch64" ] || [ "$(uname -m)" = "arm64" ] && SUF="_aarch64" || SUF=""
  F="lean-${V#v}-${OS}${SUF}.tar.zst"
  curl -sSfL -o lean.tar.zst "https://github.com/leanprover/lean4/releases/download/$V/$F"
  if command -v zstd >/dev/null; then tar --zstd -xf lean.tar.zst
  else python3 -m pip install -q zstandard && python3 -c "
import zstandard, tarfile
with open('lean.tar.zst','rb') as f:
    tarfile.open(fileobj=zstandard.ZstdDecompressor().stream_reader(f), mode='r|').extractall('.')"; fi
  elan toolchain link lean-local "$WORKDIR/${F%.tar.zst}"
  TC=lean-local
}
elan default "$TC"

# 3. The Lean REPL
[ -d repl ] || git clone -q https://github.com/leanprover-community/repl
(cd repl && echo "$TC" > lean-toolchain && lake build)

# 4. A Mathlib project
mkdir -p ymproj && cd ymproj
echo "$TC" > lean-toolchain
cat > lakefile.toml <<'EOF'
name = "ymproj"
defaultTargets = ["Ymproj"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "master"

[[lean_lib]]
name = "Ymproj"
EOF
cat > Ymproj.lean <<'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.GCongr
EOF
lake update
if [ "${FULL_MATHLIB:-0}" = "1" ]; then
  echo "import Mathlib" > Ymproj.lean
  lake exe cache get
fi
lake build

echo
echo "Done. Run the engine with:"
echo "  python3 proof_engine.py --project $WORKDIR/ymproj --repl $WORKDIR/repl/.lake/build/bin/repl --proposer static"
