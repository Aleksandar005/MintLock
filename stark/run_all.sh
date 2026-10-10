#!/usr/bin/env bash
# Builds every STARK module and runs it. Each proof module proves a statement,
# verifies the proof with Winterfell's verifier, runs its negative (soundness)
# tests, and exits non-zero if any check fails. This script stops at the first
# failure. Expect a few minutes; disc_full_l64 alone takes about a minute.
set -euo pipefail
cd "$(dirname "$0")"

cargo build --release --bins

BINS=(
  # building blocks (August 13)
  stark-poc
  mulseg mulseg2 mulseg3 mulseg4
  mulseg5_logup mulseg6_chain mulseg6_integ
  mulseg_a mulseg_b mulseg_c mulseg_d1 mulseg_d2 mulseg_e1 mulseg_e2
  # assembled modules (August 14)
  round_full reduce_chain reduce_merged perm_bind
  disc_anchor disc_full disc_full_l64
)

for b in "${BINS[@]}"; do
  echo "==================== $b"
  "./target/release/$b"
done

# Off-chain prover: reads data/trajectory.txt, writes data/receipt.bin.
# It produces a proof but does not verify it (see README).
echo "==================== prover"
./target/release/prover

echo
echo "All ${#BINS[@]} proof modules passed; prover wrote data/receipt.bin."
