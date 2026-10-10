"""
Meri STVARAN broj limb-operacija po rho rundi, rekonstruisanjem b',c' preko
eksplicitne limb-schoolbook aritmetike sa brojacima. Ne pretpostavlja formule —
broji mnozenja i carry/add pozicije na pravoj trajektoriji redukcije.

Limb: 32-bit (Goldilocks-kompatibilno, proizvod 2 limba < 2^64 < p).
Koeficijent ~1024-bit -> L = ceil(1024/32) = 32 limba.
"""
import secrets, statistics
import measure_reduce_depth as m

LIMB = 32
MASK = (1 << LIMB) - 1

def to_limbs(x):
    x = abs(x); out = []
    while x: out.append(x & MASK); x >>= LIMB
    return out or [0]

class Counter:
    def __init__(self): self.mul = 0; self.carry = 0
    # 1-limb * bignum schoolbook (k je uvek <=1 limb na 32-bit)
    def small_mul(self, k, x_limbs):
        assert k <= MASK, "k nije 1 limb!"
        self.mul += len(x_limbs)          # L limb-mnozenja
        self.carry += len(x_limbs) + 1    # normalizacija produkta (L+1 pozicija)
    def add(self, n_positions):
        self.carry += n_positions         # add sa carry-propagacijom

def round_cost(a, b, c, k, D, ctr):
    """troskovi za b' = b + 2k a ; c' = c + k b + k^2 a (isti izraz kao AIR)."""
    A = to_limbs(a); B = to_limbs(b)
    kk = abs(k)
    two_k = 2*kk
    # 2k * a
    ctr.small_mul(two_k & MASK if two_k <= MASK else two_k, A) if two_k <= MASK else ctr.__dict__  # guard
    # (ako 2k predje 1 limb, tretiraj kao 2 limba)
    if two_k > MASK:
        ctr.mul += len(A)  # drugi limb
        ctr.carry += 1
    ctr.add(len(A) + 2)                    # b + 2ka
    # k * b
    ctr.small_mul(kk, B)
    # k^2
    ctr.mul += 1
    k2 = kk*kk
    # k^2 * a  (k^2 moze biti 1-2 limba)
    ctr.mul += len(A) * (1 if k2 <= MASK else 2)
    ctr.carry += len(A) + (1 if k2 <= MASK else 2)
    ctr.add(len(A) + 2)                    # c + kb
    ctr.add(len(A) + 2)                    # ... + k^2 a

def measure_round_cost(bits, trials=30):
    D = m.discriminant_from_seed(b"petnica-air" + str(bits).encode(), bits=bits)
    g = m.prime_form(D)
    per_round_mul, per_round_carry, L_seen = [], [], []
    for _ in range(trials):
        f1 = m.rand_elem(g, D, 64); f2 = m.rand_elem(g, D, 64)
        prod = m.compose(f1, f2)
        # ponovi redukciju rucno, belezeci k svake runde
        f, k0 = m.normalize(prod, D)
        a, b, c = f
        L_seen.append(len(to_limbs(a)))
        while a > c or (a == c and b < 0):
            ctr = Counter()
            (a2, b2, c2), k = m.rho((a, b, c), D)
            round_cost(a, b, c, k, D, ctr)
            per_round_mul.append(ctr.mul)
            per_round_carry.append(ctr.carry)
            a, b, c = a2, b2, c2
    return (statistics.mean(per_round_mul), max(per_round_mul),
            statistics.mean(per_round_carry), max(per_round_carry),
            statistics.mean(L_seen))

for bits in (1024, 2048):
    mul_mean, mul_max, car_mean, car_max, Lm = measure_round_cost(bits)
    cells_mean = mul_mean + car_mean
    print(f"D={bits}-bit  L={Lm:.0f} limba(32-bit)")
    print(f"  limb-MNOZENJA / rundi : mean {mul_mean:.1f}  max {mul_max}")
    print(f"  carry/add poz. / rundi: mean {car_mean:.1f}  max {car_max}")
    print(f"  ukupno limb-celija/rundi: ~{cells_mean:.0f}")
    print(f"  (analiticki ocekivano: 3L+1={3*Lm+1:.0f} mult, ~6L+6={6*Lm+6:.0f} carry)\n")
