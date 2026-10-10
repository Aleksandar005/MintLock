#!/usr/bin/env python3
"""Generise PRAVI Wesolowski dokaz na 2048-bit D i emituje Solidity e2e fixture.
Serijalizacija mora biti bajt-za-bajt identicna LibWesolowskiBig._ser."""
import hashlib, sys
from classgroup import (discriminant_from_seed, prime_form, reduce_form,
                        compose, square, power, is_probable_prime)

T = 4096
PAD_BYTES = 256  # mora se poklapati sa LibWesolowskiBig.PAD_WORDS*32 (2048-bit)
D = discriminant_from_seed(b"petnica-2026", bits=2048)
u = reduce_form(power(prime_form(D), 0xC1A55, D))

def pad128(x):
    return abs(x).to_bytes(PAD_BYTES, 'big')  # sirina-genericki (2048-bit)

def ser(f):
    a, b, c = reduce_form(f)
    return pad128(a) + bytes([1 if b < 0 else 0]) + pad128(b) + pad128(c)

def small_prime_80(n):
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    return is_probable_prime(n, rounds=40)

def fiat_shamir_prime(u, w, T, D):
    seed = hashlib.sha256(ser(u) + ser(w) + T.to_bytes(32,'big') + pad128(D)).digest()
    counter = 0
    while True:
        cand = int.from_bytes(hashlib.sha256(seed + counter.to_bytes(32,'big')).digest(),'big') >> 176
        cand |= (1 << 79) | 1
        if small_prime_80(cand): return cand
        counter += 1

# w = u^(2^T) sekvencijalnim kvadriranjem; pi streaming algoritmom
w = u
for _ in range(T): w = reduce_form(square(w))
l = fiat_shamir_prime(u, w, T, D)
r = 1; pi = None
for _ in range(T):
    b = (2*r) // l; r = (2*r) % l
    if pi is not None: pi = reduce_form(square(pi))
    if b:
        pi = u if pi is None else reduce_form(compose(pi, u))
# sanity u Python-u pre emitovanja
lhs = reduce_form(compose(power(pi, l, D), power(u, pow(2, T, l), D)))
assert lhs == reduce_form(w), "python sanity failed"

def limbs(x):
    x = abs(x); out = []
    while x: out.append(x & ((1<<256)-1)); x >>= 256
    return out or [0]

def emit_int(name, v):
    L = limbs(v); neg = "true" if v < 0 else "false"
    lines = [f"        uint256[] memory L=new uint256[]({len(L)});"]
    for i, w_ in enumerate(L): lines.append(f"        L[{i}]={w_};")
    body = "\n".join(lines)
    return f"    function {name}() internal pure returns (B.Int memory z){{\n{body}\n        z.limbs=L; z.neg={neg};\n    }}\n"

def emit_form(pfx, f):
    a,b,c = reduce_form(f)
    s = emit_int(pfx+"_a", a) + emit_int(pfx+"_b", b) + emit_int(pfx+"_c", c)
    s += f"    function {pfx}() internal pure returns (CG.Form memory){{ return CG.Form({pfx}_a(),{pfx}_b(),{pfx}_c()); }}\n"
    return s

sol = f'''// SPDX-License-Identifier: MIT
// AUTO-GENERISANO: python3 gen_wesolowski_fixture.py (T={T}, seed petnica-2026)
pragma solidity ^0.8.24;
import {{Test, console2}} from "forge-std/Test.sol";
import {{LibBigInt as B}} from "../src/LibBigInt.sol";
import {{LibClassGroupBig as CG}} from "../src/LibClassGroupBig.sol";
import {{LibWesolowskiBig as W}} from "../src/LibWesolowskiBig.sol";

contract WesolowskiE2E is Test {{
    uint256 constant T_ = {T};
    uint256 constant L_EXPECTED = {l};
{emit_int("D_", D)}{emit_form("U_", u)}{emit_form("Wf_", w)}{emit_form("PI_", pi)}
    function test_PrimeMatchesPython() public pure {{
        require(W.fiatShamirPrime(U_(), Wf_(), T_, D_()) == L_EXPECTED, "l mismatch");
    }}
    function test_RealProofVerifies() public view {{
        uint256 g0 = gasleft();
        bool ok = W.verify(U_(), Wf_(), PI_(), T_, D_());
        console2.log("WESOLOWSKI e2e verify gas:", g0 - gasleft());
        require(ok, "real proof rejected");
    }}
    function test_TamperedProofFails() public pure {{
        require(!W.verify(U_(), Wf_(), U_(), T_, D_()), "accepted pi=u");
        require(!W.verify(U_(), U_(), PI_(), T_, D_()), "accepted w=u");
    }}
}}
'''
open('../solidity/patches/WesolowskiE2E-2048.t.sol','w').write(sol)
print(f"OK: T={T}, l={l}")
