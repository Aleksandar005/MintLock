# MintLock

Time-lock encryption and sealed-bid auctions on Ethereum, built on class groups
of imaginary quadratic fields, with no trusted setup anywhere in the stack.

A bid is locked so that nobody can open it before a fixed amount of sequential
work (T squarings in the group) has been done. Whoever does the work publishes
the result together with a Wesolowski proof, and a smart contract checks the
proof on-chain. RSA-based designs need someone to generate the modulus, and that
person knew the group order at some point. In a class group the discriminant is
derived from a public seed, and the group order is not a secret anyone holds; it
is a number nobody has computed.

**Status:** research prototype. Not audited, not deployed, not for real funds.

## Repository layout

| path | contents |
|---|---|
| `python-demo/` | reference class-group arithmetic (`classgroup.py`), time-lock and Wesolowski prove/verify (`timelock.py`), CLI demo, tests, 2048-bit validation, measurement scripts |
| `solidity/src/` | contracts: 96-bit demo (`LibClassGroup`, `TimelockVault`, `SealedAuction`) and 1024-bit bignum stack (`LibBigInt`, `LibClassGroupBig`, `LibWesolowskiBig`, `SegmentedWesolowski`, `OptimisticWesolowski`) |
| `solidity/test/` | Foundry tests, differential tests against Python vectors, fuzzing, gas benchmarks |
| `solidity/patches/` | 2048-bit version of `LibWesolowskiBig` (kept out of `src/`, see its README) |
| `solidity/stark-verifier/` | parts of an on-chain STARK verifier (unfinished) |
| `stark/` | Rust prototype that arithmetizes class-group reduction as a STARK (Winterfell) |
| `auction.html` | browser front end for the sealed-bid auction demo |
| `docs/` | design notes, optimization history, status (in Serbian) |

## Measured results

All numbers below were reproduced on 2026-10-10 from this repository
(forge 1.5.1, solc 0.8.24, `via_ir`, optimizer 20000 runs).
`forge test` runs 90 tests in 18 suites, all passing.

**96-bit demo discriminant** (insecure, for logic and live demos only)

| what | gas | test |
|---|---|---|
| Wesolowski verify, two separate exponentiations | 4.62M | `TimelockVault.t.sol` `test_GasReport` |
| same, joint (Shamir) exponentiation | 2.81M | same |
| `openBid` in the auction (verify + on-chain decrypt) | 2.80M | `SealedAuction.t.sol` `test_GasOpenBid` |

**1024-bit discriminant**

| what | gas | test |
|---|---|---|
| one composition, NUCOMP vs. classical | 389k vs. 3.53M | `Nucomp.t.sol` |
| one full-size squaring (NUDUPL) | 367k | `VerifyShapedBench.t.sol` |
| half-width xgcd, Lehmer vs. classical | 409k vs. 9.16M | `LehmerBench.t.sol` |
| **full verification of a real proof** (T = 4096, 80-bit challenge) | **54.8M** | `WesolowskiE2E.t.sol` `test_RealProofVerifies` |
| shaped worst case (80 squarings + 74 compositions on full-size forms), NUCOMP | 102.2M | `VerifyNucompBench.t.sol` |
| same shape, old classical composition path | 237.3M | `VerifyShapedBench.t.sol` |
| segmented verification: start + 8 steps | 2.33M + at most 7.63M per step | `SegmentedWesolowski.t.sol` |
| optimistic verification: claim / finalize / challenge one segment | 0.63M / 9k / 7.31M | `OptimisticWesolowski.t.sol` |

Since the Fusaka upgrade (December 2025) a single Ethereum transaction is
capped at 16,777,216 gas (EIP-7825). A one-call 1024-bit verification does not
fit; the segmented and optimistic verifiers keep every transaction under the cap.

Earlier figures in `docs/` (489M, 228M) come from older code paths and
benchmarks; the table above reflects the current code.

**Python reference**

`test_classgroup.py` checks a known small class group (Cl(−23) has order 3),
the group laws on a random discriminant, and repeated squaring.
`validate_2048.py` passes at 1024 and 2048 bits: group laws, discriminant
invariance, NUCOMP equal to classical composition on 60 random pairs,
sequential squaring, and Wesolowski prove/verify with a forged result rejected.

## STARK prototype

The long-term way to make verification cheap without a trusted setup is to
prove the class-group arithmetic off-chain with a transparent STARK and verify
only the proof on-chain. `stark/` contains 22 Winterfell 0.8.3 proof modules,
each with negative (soundness) tests, plus an off-chain prover. They cover the
building blocks of one reduction round at 2048-bit width, the relation
`4ac − b² = |D|`, LogUp range checks, and chaining across rounds.

This is a prototype of components, not a working verifier: a correct
reduction of a real form is not yet proven end to end, composition and the
Wesolowski check are not arithmetized, and the Solidity verifier parts compile
but are not assembled into a full `verify()`. STARK verifier gas figures in
`docs/` are projections, not measurements. See `stark/README.md` for the
module-by-module account.

## Known limitations

- **Discriminant binding.** In `SegmentedWesolowski` and `OptimisticWesolowski`
  the stored commitment is `keccak256(u, pi, T)`. The discriminant `D` is passed
  in as an argument on each call and is not part of the commitment. This is an
  open issue.
- **Parameter sizes.** The 96-bit demo is insecure. The 1024-bit contracts and
  the 2048-bit Python validation are prototype sizes; the notes in `docs/` cite
  much larger discriminants (about 6656 bits) as a conservative target.
- **2048-bit on-chain.** The serializer patch in `solidity/patches/` has not
  been run through forge; existing fixtures are 1024-bit.
- **Not audited.**

## Running

```bash
# Python (3.8+, no dependencies)
cd python-demo
python3 test_classgroup.py
python3 demo.py run --seconds 30 -m "test message"
python3 validate_2048.py          # takes a few minutes

# Solidity (Foundry)
cd solidity
forge install foundry-rs/forge-std --no-git
# foundry.toml points solc at /usr/local/bin/solc; change it or remove that line
forge test -vv

# STARK prototype (Rust)
cd stark
./run_all.sh                      # builds and runs all proof modules
```

`solidity/README.md` and `python-demo/README.md` describe the live demos
(local chain with `anvil`, step-by-step lock and unlock).
