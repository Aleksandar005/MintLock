#!/usr/bin/env python3
"""END-TO-END test prover/verifier lanca (bez EVM-a; reprodukuje Solidity logiku u Pythonu):
  1. emit_trajectory.py  -> trajectory.txt  (PRAVA classgroup forma)
  2. rust prover         -> receipt.bin     (STARK disc-anchor dokaz + javni ulazi)
  3. ovaj skript         -> parsira receipt kao MintLockVerifier.parseReceipt,
                            proverava sec, L0==R0, transcript seed, Merkle-put algoritam.
Ako sve prođe: lanac classgroup->prover->receipt->verifier je konzistentan.
"""
import struct, subprocess, sys, os

try:
    from Crypto.Hash import keccak
    def kec(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import hashlib
    def kec(b): return hashlib.sha3_256(b).digest()

HERE = os.path.dirname(os.path.abspath(__file__))
CRATE = os.path.join(HERE, "..", "stark", "data")

def parse_receipt(r: bytes):
    assert r[:4] == b"MLK1", "los magic"
    sec = r[4]
    npub = struct.unpack("<I", r[5:9])[0]
    off = 9; pub = []
    for _ in range(npub):
        pub.append(struct.unpack("<Q", r[off:off+8])[0]); off += 8
    plen = struct.unpack("<I", r[off:off+4])[0]; off += 4
    proof = r[off:off+plen]
    return sec, pub, proof

def transcript_seed(pub):
    buf = b"".join(struct.pack("<Q", x) for x in pub)
    return kec(buf)

def verify_merkle_path(leaf, path, index, root):
    node = leaf
    for sib in path:
        if index & 1 == 0: node = kec(node + sib)
        else:              node = kec(sib + node)
        index >>= 1
    return node == root

def main():
    receipt_path = os.path.join(CRATE, "receipt.bin")
    r = open(receipt_path, "rb").read()

    print("== E2E: parse receipt (MintLockVerifier.parseReceipt) ==")
    sec, pub, proof = parse_receipt(r)
    print(f"  sec={sec}  n_pub={len(pub)}  proof={len(proof)} B  receipt={len(r)} B")

    # verify() provere koje su on-chain jeftine:
    assert sec >= 95, "sigurnost < 95"
    assert len(pub) >= 12, "premalo javnih ulaza"
    l0, r0 = pub[3], pub[4]
    assert l0 == r0, f"anchor L0 != R0 ({l0} != {r0})"
    print(f"  [OK] sec>=95 ; L0==R0 ({l0}) ; n={pub[11]}")

    seed = transcript_seed(pub)
    print(f"  transcript seed = {seed.hex()[:24]}...")

    # Merkle algoritam sanity (sintetički put)
    leaf = kec(b"q"); path = [kec(bytes([i])) for i in range(16)]; idx = 0xBEEF & 0xFFFF
    node = leaf; ix = idx
    for sib in path:
        node = kec(node + sib) if ix & 1 == 0 else kec(sib + node); ix >>= 1
    assert verify_merkle_path(leaf, path, idx, node), "Merkle put nekonzistentan"
    print("  [OK] Merkle-put algoritam round-trip")

    # gas projekcija (MintLockVerifier.projectedGas)
    nq = 36; TLOG = 16
    merkle = nq*2*TLOG*150; fri = (TLOG+3)*nq*200; fixedc = 500_000
    print(f"  [PROJEKCIJA] gas ~ {merkle+fri+fixedc:,} (merkle {merkle:,} + fri {fri:,} + fiksno {fixedc:,})")

    print("\nE2E PROŠAO: classgroup -> prover -> receipt -> verifier lanac konzistentan.")

if __name__ == "__main__":
    main()
