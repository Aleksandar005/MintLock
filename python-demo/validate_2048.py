"""
Validacija klasno-grupne aritmetike na >=2048-bit diskriminanti.
Sve protiv referentnog compose() + zakoni grupe + pun Wesolowski protokol.
"""
import sys, time, secrets, random
sys.setrecursionlimit(200000)
import classgroup as cg
import timelock as tl

def disc(f):
    a, b, c = f
    return b*b - 4*a*c

def rand_elem(g, D, kbits=256):
    return cg.power(g, secrets.randbits(kbits) | 1, D)

def check(name, cond):
    print(f"  [{'ok' if cond else 'GRESKA'}] {name}")
    assert cond, name

def bench(fn, n):
    t0 = time.time()
    for _ in range(n):
        fn()
    return (time.time() - t0) / n * 1000.0  # ms/op

def suite(bits, seed=b"petnica-2048", n_pairs=60, n_bench=80):
    print(f"\n================  D = {bits}-bit  ================")
    t0 = time.time()
    D = cg.discriminant_from_seed(seed + str(bits).encode(), bits=bits)
    print(f"  D generisan za {time.time()-t0:.2f}s ; |D|={abs(D).bit_length()} bita ; D%4={D%4}")
    check("D je negativan, |D| ima tacan broj bitova", D < 0 and abs(D).bit_length() == bits)

    g = cg.prime_form(D)
    idf = cg.identity(D)
    check("disc(g) == D", disc(g) == D)
    check("disc(identity) == D", disc(idf) == D)
    a0 = abs(g[0]).bit_length()
    print(f"  koeficijent a redukovane forme ~ {a0} bita (ocekivano ~|D|/2)")

    # --- zakoni grupe ---
    x, y, z = rand_elem(g, D), rand_elem(g, D), rand_elem(g, D)
    check("disc ocuvana na slucajnim elementima", disc(x)==D and disc(y)==D and disc(z)==D)
    check("neutral: x*e == x", cg.compose(x, idf) == cg.reduce_form(x))
    check("inverz: x*x^-1 == e", cg.compose(x, cg.inverse(x)) == idf)
    check("komutativnost: x*y == y*x", cg.compose(x,y) == cg.compose(y,x))
    check("asocijativnost: (x*y)*z == x*(y*z)",
          cg.compose(cg.compose(x,y),z) == cg.compose(x,cg.compose(y,z)))

    # --- NUCOMP == compose (disciplina projekta) ---
    ok = 0
    for _ in range(n_pairs):
        f1, f2 = rand_elem(g, D), rand_elem(g, D)
        if f1 == f2:
            continue
        r_nucomp = cg.nucomp(f1, f2, D)
        r_compose = cg.compose(f1, f2)
        assert r_nucomp == r_compose, "NUCOMP != compose"
        assert disc(r_nucomp) == D, "NUCOMP disc drift"
        ok += 1
    check(f"NUCOMP == compose na {ok} slucajnih parova (+ disc ocuvana)", ok > 0)
    # nucomp(f,f) mora da padne na square
    check("nucomp(f,f) == square(f)", cg.nucomp(x, x, D) == cg.square(x))

    # --- VDF lanac (timelock jezgro) ---
    T = 300
    w_seq = tl.sequential_square(g, T, D, quiet=True)
    w_pow = cg.power(g, pow(2, T), D)
    check(f"sekvencijalno g^(2^{T}) == power(g, 2^{T})", w_seq == cg.reduce_form(w_pow))

    # --- pun Wesolowski protokol na ovoj sirini ---
    r = tl.random_exponent(256)
    u = cg.power(g, r, D)
    w = tl.sequential_square(u, T, D, quiet=True)
    pi = tl.prove(u, w, T, D, quiet=True)
    check("Wesolowski verify(validan) == True", tl.verify(u, w, T, pi, D) is True)
    w_bad = cg.compose(w, g)  # lazno w
    check("Wesolowski verify(lazno w) == False", tl.verify(u, w_bad, T, pi, D) is False)

    # --- propusnost ---
    f1, f2 = rand_elem(g, D), rand_elem(g, D)
    ms_sq   = bench(lambda: cg.square(f1), n_bench)
    ms_comp = bench(lambda: cg.compose(f1, f2), n_bench)
    ms_nuc  = bench(lambda: cg.nucomp(f1, f2, D), n_bench)
    print(f"  propusnost: square {ms_sq:.3f} ms/op | compose {ms_comp:.3f} ms/op | nucomp {ms_nuc:.3f} ms/op")
    return dict(bits=bits, sq=ms_sq, comp=ms_comp, nuc=ms_nuc, a_bits=a0)

r1024 = suite(1024)
r2048 = suite(2048)

print("\n================  RAST CENE 1024 -> 2048  ================")
for k, lbl in [("sq","kvadriranje"),("comp","kompozicija (klasicna)"),("nuc","NUCOMP")]:
    factor = r2048[k]/r1024[k]
    print(f"  {lbl:26s}: {r1024[k]:.3f} -> {r2048[k]:.3f} ms/op  (x{factor:.2f})")
print("\nSVE 2048-bit PROVERE PROSLE.")
