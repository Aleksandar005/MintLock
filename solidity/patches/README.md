# patches/

`LibWesolowskiBig-2048.sol` is the width-generic version of
`src/LibWesolowskiBig.sol`: forms are serialized to 256 bytes (`PAD_WORDS = 8`)
instead of 128, so 2048-bit discriminants fit. It pairs with
`python-demo/gen_wesolowski_fixture_2048.py`; byte equivalence with Python's
`abs(x).to_bytes(256, 'big')` was checked on 5000 random values (August 2026).

It is kept out of `src/` on purpose. Swapping it in changes the Fiat-Shamir
seed for every existing fixture, so `test/WesolowskiE2E.t.sol` and the tests
that go through `OptimisticWesolowski` / `SegmentedWesolowski` would need
regenerated 2048-bit fixtures before they pass again. This has not been run
with forge yet.
