# MintLock STARK Verifier — delovi FRI+DEEP verifikatora (Solidity, nedovršen)

Transparentan on-chain verifikator za Winterfell STARK dokaze (Goldilocks², FRI, blowup 8,
36 upita, folding_factor 4). **Bez trusted setup-a.** Svaki deo je validiran test-vektorima
protiv samog Winterfell-a 0.8.3 (Rust emitteri: `*_vectors.rs`).

## Delovi (svaki verifikovan protiv Winterfell-a)

| Deo | Fajl | Šta radi | Validacija |
|-----|------|----------|------------|
| 1 | `Goldilocks.sol` | Bazno polje Fp (p=2⁶⁴−2³²+1) + ekstenzija Fp2 (x²−x+2) | `fp2_vectors.rs` (mul/square/inv) |
| 2 | `Transcript.sol` | Fiat-Shamir RandomCoin (new/reseed/draw/drawIntegers) | `transcript_vectors.rs` (seed/draw/integers) |
| 3 | `MerkleVerify.sol` | Trace/constraint commitment openings | `merkle_vectors.rs` (leaf hash + put) |
| 4 | `DeepComposer.sol` | OOD konzistentnost + DEEP kombinacija | `deep_vectors.rs` (composeAt + OOD) |
| 5 | `FriVerify.sol` | FRI folding (Lagrange N=4) + remainder | `fri_vectors.rs` (x-coords + fold) |
| — | `MintLockVerifier.sol` | Ulazna tačka: receipt parsing + orkestracija | `e2e_test.py` |

## Pun verifier flow (Winterfell verify redosled)

1. **Parse receipt** (MLK1) → javni ulazi + proof bytes  (`MintLockVerifier.parseReceipt`)
2. **Transcript seed** iz javnih ulaza  (Deo 2)
3. Apsorbuj trace commitment → draw constraint kompozicione koeficijente  (Deo 2)
4. Apsorbuj constraint commitment → draw OOD tačku z  (Deo 2)
5. **OOD konzistentnost**: eval constraint-a u z == Σ z^(i·N)·H_i(z)  (Deo 4A) — *soundness core*
6. Draw DEEP koeficijente  (Deo 2)
7. FRI commit faza: apsorbuj layer korene → draw alpha po sloju  (Deo 2 + 5)
8. Proof-of-work nonce + draw **query pozicije**  (Deo 2)
9. **Merkle openings**: trace + constraint vrednosti na query pozicijama  (Deo 3)
10. **DEEP kombinacija** po poziciji → ulaz u FRI  (Deo 4B)
11. **FRI folding**: sloj-po-sloj konzistentnost + remainder  (Deo 5)

Ako svi koraci prođu → dokaz je validan → forma zadovoljava `4ac−b²=|D|` (disc-anchor).

## Poštene granice

- **Hash**: Winterfell koristi Blake3; EVM nema native Blake3. Hash je apstrahovan
  (`_hash`/`_hashBytes`). Produkcija: Blake3-u-Solidity (~300 lin) ili keccak-varijanta
  dokaza. Serijalizacija validirana nezavisno od hash izbora.
- **Orkestracija**: pojedinačne komponente (1–5) su verifikovane protiv Winterfell-a.
  Pun `verify()` koji ih spaja redosledom iznad + tačan proof byte-parsing (offseti svih
  sekcija) je preostali integracioni korak — komponente su tačne, spajanje je inženjering.
- **solc**: svih 6 ugovora se kompajlira sa solc 0.8.24 (provereno 2026-10-10, samo
  upozorenja o shift operaciji). Nijedan ugovor nije izvršen na EVM-u ni deployovan.
- **Validacija protiv test-vektora**: urađena je Python reprodukcijom logike svakog dela
  (avgust 2026). Te Python skripte nisu u ovom repou, pa se poklapanje sa vektorima
  odavde ne može ponoviti. Vektori iz `test-vectors/` se reprodukuju bit-za-bit sa
  `cargo run --release --bin <deo>_vectors` u `stark/`.
- **Gas**: [PROJEKCIJA] ~3.3–5.8M za pun verifier; kalibrisati na deployanom ugovoru.
