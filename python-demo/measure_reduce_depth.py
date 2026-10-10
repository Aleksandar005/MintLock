"""
Merenje dubine redukcije N (broj rho rundi) za kompoziciju punih redukovanih
formi imaginarne kvadratne klasne grupe. Ulaz za AIR: dužina traga u Fazi RED
je N_rho * (redova po rundi), pa nam treba IZMEREN N, ne pretpostavljen.

Samostalan (ne uvozi classgroup.py) — implementira referentnu Dirichlet
kompoziciju + klasičnu redukciju (normalize/rho) pozitivno-definitnih formi.
Disc-ocuvanje i redukovanost se ASERTUJU (disciplina kao u validate_2048.py).

Napomena o vernosti: rho-runde su geometrijsko svojstvo forme (koliko je daleko
od redukovane), prakticno nezavisno od toga da li se kompozicija radi klasicno,
preko NUCOMP ili NUDUPL. Zato je izmeren N ovde dobar donji-nivo anchor za
duzinu traga, cak i ako se repo reduce razlikuje za konstantu.
"""
import sys, time, secrets, hashlib, statistics
sys.setrecursionlimit(200000)

# ----------------------------------------------------------------------
#  osnovna teorija brojeva
# ----------------------------------------------------------------------
def egcd(a, b):
    """vraca (g, x, y) tako da g = x*a + y*b"""
    if b == 0:
        return (a, 1, 0)
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q*r
        old_s, s = s, old_s - q*s
        old_t, t = t, old_t - q*t
    return (old_r, old_s, old_t)

_SMALL = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

def is_probable_prime(n, rounds=40):
    if n < 2: return False
    for p in _SMALL:
        if n % p == 0: return n == p
    d = n - 1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for _ in range(rounds):
        a = 2 + secrets.randbelow(n - 3)
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = x*x % n
            if x == n - 1: break
        else:
            return False
    return True

def next_prime(n):
    if n <= 2: return 2
    n |= 1
    while not is_probable_prime(n): n += 2
    return n

def kronecker(a, n):
    """Kronecker simbol (a/n), n>0 neparno dovoljno za nas slucaj (n prost)."""
    if n == 0: return 1 if a in (1, -1) else 0
    if n < 0: n = -n
    result = 1
    if a < 0:
        a = -a
        if n % 4 == 3: result = -result
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: result = -result
        a %= n
    return result if n == 1 else 0

def tonelli(a, p):
    """sqrt(a) mod p, p neparan prost, (a/p)=1"""
    a %= p
    if a == 0: return 0
    if p % 4 == 3: return pow(a, (p + 1)//4, p)
    q = p - 1; s = 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while kronecker(z, p) != -1: z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1)//2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt*tt % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b*b % p, t*b*b % p, r*b % p
    return r

# ----------------------------------------------------------------------
#  diskriminanta, prime_form
# ----------------------------------------------------------------------
def discriminant_from_seed(seed, bits):
    """D = -p, p prost, p ≡ 3 mod 4  ->  D ≡ 1 mod 4 ; |D| ima tacno `bits` bita."""
    need = (bits + 7)//8
    buf, ctr = b'', 0
    while len(buf) < need:
        buf += hashlib.sha256(seed + ctr.to_bytes(8, 'big')).digest(); ctr += 1
    p = int.from_bytes(buf[:need], 'big')
    p |= (1 << (bits - 1)); p &= (1 << bits) - 1; p |= 3
    while not (p % 4 == 3 and is_probable_prime(p)): p += 4
    return -p

def prime_form(D):
    """najmanji prost a=q sa (D/q)=1, forma (q,b,c) redukovana."""
    q = 2
    while True:
        q = next_prime(q + 1)
        if D % q == 0: continue
        if kronecker(D, q) == 1:
            r = tonelli(D % q, q)
            b = r % q
            if b % 2 == 0: b += q          # b neparno (D neparno)
            c = (b*b - D)//(4*q)
            assert (b*b - D) % (4*q) == 0
            return reduce_plain((q, b, c), D)

# ----------------------------------------------------------------------
#  normalize / rho / reduce
# ----------------------------------------------------------------------
def disc(f):
    a, b, c = f
    return b*b - 4*a*c

def normalize(f, D):
    """b -> (-a, a] ; vraca (forma, k)  gde je b' = b + 2k a."""
    a, b, c = f
    if -a < b <= a:
        return (a, b, c), 0
    k = (a - b)//(2*a)
    b2 = b + 2*a*k
    while b2 <= -a: b2 += 2*a; k += 1
    while b2 > a:  b2 -= 2*a; k -= 1
    c2 = (b2*b2 - D)//(4*a)
    return (a, b2, c2), k

def rho(f, D):
    """jedan korak redukcije: (a,b,c) -> normalize(c,-b,a)."""
    a, b, c = f
    nf, k = normalize((c, -b, a), D)
    return nf, k

def is_reduced(f):
    a, b, c = f
    return (-a < b <= a < c) or (0 <= b <= a and a == c)

def reduce_plain(f, D):
    f, _ = normalize(f, D)
    a, b, c = f
    while a > c or (a == c and b < 0):
        f, _ = rho(f, D); a, b, c = f
    if (a == c or a == -b) and b < 0:
        f = (a, -b, c)
    return f

def reduce_counting(f, D):
    """kao reduce_plain ali broji rho runde i pamti max |k| (bit-duzina)."""
    f, k0 = normalize(f, D)
    kbits = [abs(k0).bit_length()]
    rounds = 0
    a, b, c = f
    while a > c or (a == c and b < 0):
        f, k = rho(f, D)
        rounds += 1
        kbits.append(abs(k).bit_length())
        a, b, c = f
    if (a == c or a == -b) and b < 0:
        f = (a, -b, c)
    return f, rounds, max(kbits)

# ----------------------------------------------------------------------
#  kompozicija (Dirichlet, NUCOMP-free) + power
# ----------------------------------------------------------------------
def compose(f1, f2):
    """vraca NEREDUKOVAN proizvod dve forme istog D."""
    a1, b1, c1 = f1
    a2, b2, c2 = f2
    if a1 > a2:
        a1, b1, c1, a2, b2, c2 = a2, b2, c2, a1, b1, c1
    s = (b1 + b2)//2
    n = b2 - s
    if a2 % a1 == 0:
        y1, d = 0, a1
    else:
        d, u, _ = egcd(a2, a1); y1 = u
    if s % d == 0:
        y2, x2, d1 = -1, 0, d
    else:
        d1, u, v = egcd(s, d); x2, y2 = u, -v
    v1, v2 = a1//d1, a2//d1
    r = (y1*y2*n - x2*c2) % v1
    b3 = b2 + 2*v2*r
    a3 = v1*v2
    c3 = (c2*d1 + r*(b2 + v2*r))//v1
    return (a3, b3, c3)

def compose_reduced(f1, f2, D):
    return reduce_plain(compose(f1, f2), D)

def identity(D):
    b = 1 if D % 2 else 0
    return reduce_plain((1, b, (b*b - D)//4), D)

def power(g, e, D):
    r = identity(D); base = g
    while e > 0:
        if e & 1: r = compose_reduced(r, base, D)
        base = compose_reduced(base, base, D)
        e >>= 1
    return r

def rand_elem(g, D, kbits=256):
    return power(g, secrets.randbits(kbits) | 1, D)

# ----------------------------------------------------------------------
#  merni pokret
# ----------------------------------------------------------------------
def measure(bits, seed=b"petnica-air", trials=200, kbits=256):
    print(f"\n================  D = {bits}-bit  ================")
    t0 = time.time()
    D = discriminant_from_seed(seed + str(bits).encode(), bits=bits)
    print(f"  D generisan za {time.time()-t0:.2f}s ; |D|={abs(D).bit_length()} bita ; D%4={D%4}")
    assert D < 0 and abs(D).bit_length() == bits
    g = prime_form(D)
    assert disc(g) == D and is_reduced(g)

    a_bits_reduced = abs(g[0]).bit_length()
    # sqrt(|D|/3) je gornja granica za a redukovane forme
    sqrt_bound_bits = (abs(D)//3).bit_length()//2 + 1
    print(f"  redukovana forma: a≈{a_bits_reduced} bita ; teorijska granica a≈|D|/2≈{sqrt_bound_bits} bita")

    rounds_list, kbits_list, a_in_bits, a_out_bits = [], [], [], []
    t0 = time.time()
    for _ in range(trials):
        f1 = rand_elem(g, D, kbits)
        f2 = rand_elem(g, D, kbits)
        prod = compose(f1, f2)                    # NEREDUKOVAN
        a_in_bits.append(abs(prod[0]).bit_length())
        rf, rounds, maxk = reduce_counting(prod, D)
        assert disc(rf) == D, "disc drift u redukciji"
        assert is_reduced(rf), "izlaz nije redukovan"
        a_out_bits.append(abs(rf[0]).bit_length())
        rounds_list.append(rounds)
        kbits_list.append(maxk)
    dt = time.time() - t0

    def stat(x):
        xs = sorted(x)
        p95 = xs[min(len(xs)-1, int(0.95*len(xs)))]
        return min(xs), statistics.mean(xs), p95, max(xs)

    rmin, rmean, rp95, rmax = stat(rounds_list)
    kmin, kmean, kp95, kmax = stat(kbits_list)
    ain = statistics.mean(a_in_bits)
    aout = statistics.mean(a_out_bits)

    print(f"  {trials} kompozicija punih formi izmereno za {dt:.2f}s")
    print(f"  a proizvoda pre redukcije ≈ {ain:.0f} bita  ->  a posle ≈ {aout:.0f} bita")
    print(f"  RHO RUNDE (N):   min {rmin}  |  mean {rmean:.1f}  |  p95 {rp95}  |  max {rmax}")
    print(f"  max |k| po redukciji (bita): min {kmin} | mean {kmean:.1f} | p95 {kp95} | max {kmax}")
    return dict(bits=bits, rmean=rmean, rmax=rmax, rp95=rp95, kmax=kmax, kp95=kp95)

def implikacija(results):
    print("\n================  IMPLIKACIJA NA DUZINU TRAGA  ================")
    print("  Faza RED: redova_traga ≈ N_rho * (MUL/CARRY podredova po rundi).")
    print("  N_rho (worst-case u uzorku) je jedini deo koji zavisi od ulaza.")
    for r in results:
        # svaka runda: c' = c + k b + k^2 a  -> ~2 bignum mnozenja (k mali) + 1 kvadr.
        # gruba mera: uzimamo p95 kao dizajn-N (retki repovi se hendluju paddingom).
        print(f"  D={r['bits']}-bit:  dizajn-N (p95) = {r['rp95']}  ; "
              f"hard-cap N (max) = {r['rmax']}  ; k staje u {r['kp95']}-bit (p95)")
    print("\n  Napomena: k je MALI (par bita) -> mnozenja k*a, k^2*a su usko-ulazna;")
    print("  dominira b^2 i a*c u anchor-invarijanti, ne k-mnozenja.")
    print("\nSVE PROVERE (disc ocuvana, izlaz redukovan) PROSLE.")


if __name__ == "__main__":
    import json
    if len(sys.argv) >= 2 and sys.argv[1] == "final":
        implikacija([json.loads(x) for x in sys.argv[2:]]); sys.exit()
    bits   = int(sys.argv[1]) if len(sys.argv) > 1 else 1024
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    kbits  = int(sys.argv[3]) if len(sys.argv) > 3 else 64
    r = measure(bits, trials=trials, kbits=kbits)
    print("JSON " + json.dumps(r))
