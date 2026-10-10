// Emituje FRI folding vektore (N=4) iz Winterfell polynom interpolate/eval, da validiramo
// Solidity FRI folding korak. Jedan sloj: 4 (x,y) tačke -> interpoliraj row poly -> eval u alpha.
use winterfell::math::{fields::f64::BaseElement, FieldElement, StarkField, polynom, get_power_series};
type F2 = winterfell::math::fields::QuadExtension<BaseElement>;
fn c2(e: F2)->(u64,u64){(e.base_element(0).as_int(),e.base_element(1).as_int())}
fn mkf2(a:u64,b:u64)->F2{F2::new(BaseElement::new(a),BaseElement::new(b))}
fn main(){
    let mut rng:u64=0xF71_0001;
    let mut nx=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;rng};
    const N:usize=4;
    // domen: generator g reda domain_size, offset
    let domain_size=64u64;
    let g = BaseElement::get_root_of_unity(6); // 2^6=64
    let offset = BaseElement::new(7);
    // folding_roots[i] = g^(domain_size/N * i)
    let froots: Vec<BaseElement> = (0..N).map(|i| g.exp_vartime((domain_size/(N as u64)*(i as u64)).into())).collect();
    // foldovana pozicija i -> xe = g^i * offset ; xs = xe * froots[k]
    let fpos = 5u64;
    let xe = g.exp_vartime(fpos.into()) * offset;
    let xs: Vec<F2> = froots.iter().map(|&r| F2::from(xe*r)).collect();
    // y vrednosti (layer_values za tu poziciju) — proizvoljne Fp2
    let ys: Vec<F2> = (0..N).map(|_| mkf2(nx(),nx())).collect();
    // interpoliraj row poly, eval u alpha
    let alpha = mkf2(nx(),nx());
    let poly = polynom::interpolate(&xs, &ys, false);
    let folded = polynom::eval(&poly, alpha);

    println!("G {}", g.as_int());
    println!("OFFSET {}", offset.as_int());
    println!("DOMAIN {}", domain_size);
    println!("FPOS {}", fpos);
    println!("ALPHA {},{}", c2(alpha).0, c2(alpha).1);
    for k in 0..N { println!("X{} {},{}", k, c2(xs[k]).0, c2(xs[k]).1); }
    for k in 0..N { println!("Y{} {},{}", k, c2(ys[k]).0, c2(ys[k]).1); }
    println!("FOLDED {},{}", c2(folded).0, c2(folded).1);
    let _ = get_power_series::<BaseElement>;
}
