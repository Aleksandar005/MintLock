// Emituje DEEP kompozicija test-vektore reprodukujući Winterfell DeepComposer formule
// (compose_trace_columns + compose_constraint_evaluations + combine) u Fp2, koristeći
// Winterfell QuadExtension aritmetiku. Solidity replika se validira protiv ovoga.
use winterfell::math::{fields::f64::BaseElement, FieldElement, StarkField};
type F2 = winterfell::math::fields::QuadExtension<BaseElement>;
fn c2(e: F2) -> (u64,u64){ (e.base_element(0).as_int(), e.base_element(1).as_int()) }
fn mkf2(a:u64,b:u64)->F2{ F2::new(BaseElement::new(a),BaseElement::new(b)) }
fn main(){
    let mut rng:u64=0xDEEF_0001;
    let mut nx=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;rng};
    // parametri
    let ncol_main=3usize; let ncol_con=2usize;
    let z = mkf2(nx(),nx());
    let g = BaseElement::new(7); // trace_domain_generator (proizvoljan za test)
    let zg = z * F2::from(g);
    // OOD trace frame: T_i(z) i T_i(zg)
    let tz: Vec<F2> = (0..ncol_main).map(|_| mkf2(nx(),nx())).collect();
    let tzg: Vec<F2> = (0..ncol_main).map(|_| mkf2(nx(),nx())).collect();
    // OOD constraint evals H_i(z)
    let hz: Vec<F2> = (0..ncol_con).map(|_| mkf2(nx(),nx())).collect();
    // DEEP koeficijenti
    let cc_trace: Vec<F2> = (0..ncol_main).map(|_| mkf2(nx(),nx())).collect();
    let cc_con: Vec<F2> = (0..ncol_con).map(|_| mkf2(nx(),nx())).collect();
    // query pozicije -> x koordinate (bazne, u Fp2 preko From)
    let xs: Vec<F2> = [3u64,11,29].iter().map(|&p| F2::from(BaseElement::new(p))).collect();
    // query vrednosti trace (bazne) i constraint (Fp2)
    let qtrace: Vec<Vec<u64>> = xs.iter().map(|_| (0..ncol_main).map(|_| nx()%BaseElement::MODULUS).collect()).collect();
    let qcon: Vec<Vec<F2>> = xs.iter().map(|_| (0..ncol_con).map(|_| mkf2(nx(),nx())).collect()).collect();

    // ---- emit ulaz ----
    println!("Z {},{}", c2(z).0, c2(z).1);
    println!("ZG {},{}", c2(zg).0, c2(zg).1);
    println!("G {}", g.as_int());
    for i in 0..ncol_main { println!("TZ{} {},{}", i, c2(tz[i]).0, c2(tz[i]).1); }
    for i in 0..ncol_main { println!("TZG{} {},{}", i, c2(tzg[i]).0, c2(tzg[i]).1); }
    for i in 0..ncol_con { println!("HZ{} {},{}", i, c2(hz[i]).0, c2(hz[i]).1); }
    for i in 0..ncol_main { println!("CCT{} {},{}", i, c2(cc_trace[i]).0, c2(cc_trace[i]).1); }
    for i in 0..ncol_con { println!("CCC{} {},{}", i, c2(cc_con[i]).0, c2(cc_con[i]).1); }
    for (j,x) in xs.iter().enumerate(){ println!("X{} {},{}", j, c2(*x).0, c2(*x).1); }
    for (j,row) in qtrace.iter().enumerate(){ println!("QT{} {}", j, row.iter().map(|v|v.to_string()).collect::<Vec<_>>().join(",")); }
    for (j,row) in qcon.iter().enumerate(){ println!("QC{} {}", j, row.iter().map(|v|{let (a,b)=c2(*v);format!("{}:{}",a,b)}).collect::<Vec<_>>().join(",")); }

    // ---- compute DEEP (Winterfell formule) ----
    for (j,&x) in xs.iter().enumerate() {
        // trace kompozicija
        let mut t1=F2::ZERO; let mut t2=F2::ZERO;
        for i in 0..ncol_main {
            let val = F2::from(BaseElement::new(qtrace[j][i]));
            t1 += (val - tz[i]) * cc_trace[i];
            t2 += (val - tzg[i]) * cc_trace[i];
        }
        let t1den = x - z; let t2den = x - zg;
        let tnum = t1*t2den + t2*t1den;
        let tden = t1den*t2den;
        let tcomp = tnum * tden.inv();
        // constraint kompozicija
        let mut cnum=F2::ZERO;
        for i in 0..ncol_con { cnum += (qcon[j][i] - hz[i]) * cc_con[i]; }
        let ccomp = cnum * (x - z).inv();
        let deep = tcomp + ccomp;
        println!("DEEP{} {},{}", j, c2(deep).0, c2(deep).1);
    }
}
