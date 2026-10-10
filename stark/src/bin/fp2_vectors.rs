// Emituje test-vektore za Fp2 (Goldilocks²) iz Winterfell-a: mul, square, inv.
// Python (reprodukcija Solidity) proverava poklapanje.
use winterfell::math::{fields::f64::BaseElement, FieldElement, StarkField};
type F2 = winterfell::math::fields::QuadExtension<BaseElement>;
fn main() {
    let mut rng: u64 = 0x1234_5678_9abc_def0;
    let mut nx = || { rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; rng };
    for _ in 0..20 {
        let a0 = BaseElement::new(nx()); let a1 = BaseElement::new(nx());
        let b0 = BaseElement::new(nx()); let b1 = BaseElement::new(nx());
        let a = F2::new(a0, a1); let b = F2::new(b0, b1);
        let m = a * b; let s = a.square(); let iv = a.inv();
        let base = |e: F2| { let v = e.base_element(0); let w = e.base_element(1); (v.as_int(), w.as_int()) };
        let (a0i,a1i)=base(a); let (b0i,b1i)=base(b);
        let (m0,m1)=base(m); let (s0,s1)=base(s); let (i0,i1)=base(iv);
        println!("{},{},{},{},{},{},{},{},{},{}", a0i,a1i,b0i,b1i,m0,m1,s0,s1,i0,i1);
    }
}
