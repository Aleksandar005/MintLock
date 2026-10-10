#!/usr/bin/env python3
"""Emituje PRAVU reduce trajektoriju klasno-grupne forme (2048-bit D) kao JSON,
koji Rust prover čita da izgradi STARK trag. Svaki rho korak: (a,b,c,k) pre koraka
i finalna redukovana forma. Limbovi su 16-bit (LE) za direktnu potrošnju u tragu.

Format:
{
  "D_bits": 2048,
  "D_abs_limbs": [...],          # |D| u 16-bit LE limbovima
  "L": <broj limba forme>,
  "start": {"a":[limbs],"b":[limbs],"b_sign":0/1,"c":[limbs]},
  "rounds": [ {"k": <int>, "a":[..],"b":[..],"b_sign":..,"c":[..]}, ... ],
  "final": {"a":[..],"b":[..],"b_sign":..,"c":[..]},
  "n_rounds": <int>
}
"""
import json, sys
from measure_reduce_depth import (discriminant_from_seed, prime_form,
                                  normalize, rho, disc, compose, power)

LB = 16
MASK = (1 << LB) - 1

def to_limbs(x, nlimbs=None):
    x = abs(int(x)); out = []
    while x:
        out.append(x & MASK); x >>= LB
    if nlimbs is not None:
        while len(out) < nlimbs: out.append(0)
        out = out[:nlimbs]
    if not out: out = [0]
    return out

def form_json(f, nlimbs):
    a, b, c = f
    return {
        "a": to_limbs(a, nlimbs),
        "b": to_limbs(b, nlimbs),
        "b_sign": 1 if b < 0 else 0,
        "c": to_limbs(c, nlimbs),
    }

def reduce_trajectory(f, D):
    """kao reduce_plain, ali beleži svaku formu + k pre svakog rho koraka."""
    traj = []
    f, k0 = normalize(f, D)
    traj.append((f, k0))
    a, b, c = f
    while a > c or (a == c and b < 0):
        pref = f
        f, k = rho(f, D)
        traj.append((f, k))
        a, b, c = f
    if (a == c or a == -b) and b < 0:
        f = (a, -b, c)
    return f, traj

def main():
    seed = sys.argv[1].encode() if len(sys.argv) > 1 else b"petnica-2026"
    exp = int(sys.argv[2], 0) if len(sys.argv) > 2 else 0xC1A55
    D = discriminant_from_seed(seed, bits=2048)
    # startna forma: sirova kompozicija prime_form-a (bez reduce) -> velika, netrivijalna,
    # disc == D. reduce_trajectory je zatim redukuje beležeći svaki korak.
    g = prime_form(D)
    ncomp = int(sys.argv[4], 0) if len(sys.argv) > 4 else 20
    f0 = g
    for _ in range(ncomp):
        f0 = compose(f0, g)
    # nlimbs: dovoljno za najveći limb-niz u trajektoriji
    fin, traj = reduce_trajectory(f0, D)
    all_forms = [f for (f, _) in traj] + [fin, f0]
    nlimbs = max(max(len(to_limbs(v)) for v in form) for form in all_forms)
    nlimbs = max(nlimbs, 64)  # bar 64 (1024-bit) za konzistentnost sa tragom

    out_lines = []
    out_lines.append(f"D_bits 2048")
    out_lines.append(f"L {nlimbs}")
    out_lines.append(f"n_rounds {len(traj)}")
    out_lines.append("D_abs " + ",".join(map(str, to_limbs(abs(disc(f0)), 128))))
    def emit_form(tag, f):
        a,b,c = f
        out_lines.append(f"{tag}_a " + ",".join(map(str, to_limbs(a, nlimbs))))
        out_lines.append(f"{tag}_bsign {1 if b<0 else 0}")
        out_lines.append(f"{tag}_b " + ",".join(map(str, to_limbs(b, nlimbs))))
        out_lines.append(f"{tag}_c " + ",".join(map(str, to_limbs(c, nlimbs))))
    emit_form("start", traj[0][0])
    for idx,(f,k) in enumerate(traj):
        out_lines.append(f"round {idx} k {int(k)}")
        emit_form(f"r{idx}", f)
    emit_form("final", fin)

    path = sys.argv[3] if len(sys.argv) > 3 else "trajectory.txt"
    with open(path, "w") as fp:
        fp.write("\n".join(out_lines) + "\n")
    print(f"emitovano: {len(traj)} rundi, L={nlimbs}, -> {path}", file=sys.stderr)

if __name__ == "__main__":
    main()
