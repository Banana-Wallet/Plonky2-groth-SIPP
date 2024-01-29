use ark_bn254::{Config, Fq, Fq12, Fq2, Fr, G1Affine, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::One;
use ark_ff::{Fp, MontFp, QuadExtConfig};
use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, goldilocks_field::GoldilocksField},
    hash::hash_types::RichField,
    iop::witness::PartialWitness,
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::CircuitConfig,
        config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig},
    },
};
use plonky2_bn254::fields::debug_tools::print_ark_fq;
use plonky2_bn254::{
    curves::{
        g1curve_target::G1Target, g2curve_target::G2Target,
        map_to_g2::map_to_g2_without_cofactor_mul,
    },
    fields::{fq12_target::Fq12Target, fq2_target::Fq2Target, fq_target::FqTarget},
};
use plonky2_bn254_pairing::pairing::{pairing, pairing_circuit};
use sipp::{
    prover_native::{inner_product, sipp_prove_native},
    verifier_circuit::sipp_verifier_circuit,
    verifier_native::sipp_verify_native,
};
use std::ops::{Add, Mul};
use std::time::Instant;

pub struct VerificationKey {
    pub alpha1: G1Affine,
    pub beta2: G2Affine,
    pub gamma2: G2Affine,
    pub delta2: G2Affine,
    pub ic: Vec<G1Affine>,
}

pub struct Proof {
    pub a: G1Affine,
    pub b: G2Affine,
    pub c: G1Affine,
}

pub struct ProofTarget<F: RichField + Extendable<D>, const D: usize> {
    pub a: G1Target<F, D>,
    pub b: G2Target<F, D>,
    pub c: G1Target<F, D>,
}

pub struct VerificationKeyTarget<F: RichField + Extendable<D>, const D: usize> {
    pub alpha1: G1Target<F, D>,
    pub beta2: G2Target<F, D>,
    pub gamma2: G2Target<F, D>,
    pub delta2: G2Target<F, D>,
    pub ic: Vec<G1Target<F, D>>,
}

fn get_verification_key() -> VerificationKey {
    println!("start vk building");
    VerificationKey {
        alpha1: G1Affine::new(
            Fq::from(MontFp!(
                "6763126530687886999315782887200758703366235230289874831627658839515656330867"
            )),
            Fq::from(MontFp!(
                "12297948670392550312636836114470404429657568989657927437959695771502446445179"
            )),
        ),
        beta2: G2Affine::new(
            Fq2::new(
                MontFp!(
                    "15362786867599176251482538547160991918100063526460909721657878971551583339657"
                ),
                MontFp!(
                    "3804423004921008809819632629079723167970572551072432396497601916259815496626"
                ),
            ),
            Fq2::new(
                MontFp!(
                    "21885719103633717693283841528133243510750001708857084897139570082577218850374"
                ),
                MontFp!(
                    "2076817281717432063622727433912740683541778328445173073030513609350245776784"
                ),
            ),
        ),
        gamma2: G2Affine::new(
            Fq2::new(
                MontFp!(
                    "1505558511994093266228972967760414664043255115544025409518939393775943607863"
                ),
                MontFp!(
                    "21131173266568468249589649137903719095480044620502529067534622738225157042304"
                ),
            ),
            Fq2::new(
                MontFp!(
                    "4008759115482693545406793535591568078300615151288108694080317738431649117177"
                ),
                MontFp!(
                    "18835856718271757625037377080288624550370480296914695806777038708085497610013"
                ),
            ),
        ),
        delta2: G2Affine::new(
            Fq2::new(
                MontFp!(
                    "1497911744463986566314308077983046202449361313910668647770797503379177516252"
                ),
                MontFp!(
                    "10829154948357654897792444316512827659620136273388886760324770466776134105520"
                ),
            ),
            Fq2::new(
                MontFp!(
                    "10850392992008761830625471778404650447428083833210258292805429019728339148884"
                ),
                MontFp!(
                    "12593805385728178657844996215584371401133999503150901444097670307277076679963"
                ),
            ),
        ),
        ic: vec![
            G1Affine::new(
                Fq::from(MontFp!(
                    "20417302999686518463947604254824206482787540497747166602791183033521164889663"
                )),
                Fq::from(MontFp!(
                    "13070739245581256634078674103787887995405997871287223137308760941168103411852"
                )),
            ),
            G1Affine::new(
                Fq::from(MontFp!(
                    "7134628694475811382742267026042639323743922548568185680200196927023443639137"
                )),
                Fq::from(MontFp!(
                    "9624761392337090719715532152667200620426657721236517270124636244477804835035"
                )),
            ),
        ],
    }
}

fn main() {
    println!("start circuit building");
    let proof = Proof {
        a: G1Affine::new(
            Fq::from(MontFp!(
                "12887163950774589848429612384269252267879103641214292968732875014481055665029"
            )),
            Fq::from(MontFp!(
                "21622722808554299809135926587843590844306004439941801858752721909447067565676"
            )),
        ),
        b: G2Affine::new(
            Fq2::new(
                MontFp!(
                    "19252399014017622041717411504172796635144662505041726695471440307521907621323"
                ),
                MontFp!(
                    "11302764088468560462334032644947221757922107890363805071604206102241252698616"
                ),
            ),
            Fq2::new(
                MontFp!(
                    "226455389767104611295930017850538586277567900474601688185243021343711813551"
                ),
                MontFp!(
                    "18768786825809469978354139019891648686066930676359588724933329715343055477839"
                ),
            ),
        ),
        c: G1Affine::new(
            Fq::from(MontFp!(
                "16716067220884575876883941674457042090348240918922797664931133638121340220774"
            )),
            Fq::from(MontFp!(
                "19465170897811434280250972276398658394224541760713812318242639282725837098749"
            )),
        ),
    };

    let vk = get_verification_key();
    println!("end vk building");

  
    let (vk_ic_1_x, vk_ic_1_y) = vk.ic[1].xy().unwrap();
    let vk_ic_affine = G1Affine::new(*vk_ic_1_x, *vk_ic_1_y);

    let vk_x_val = vk.ic[0];
    let vk_ic_mul = vk_ic_affine.mul_bigint(&[20u64;1]).into_affine();

    // println!(" temp_affine {:?}", temp_affine);
    let vk_x_final = (vk_x_val + vk_ic_mul).into_affine();
    // println!(" vk_x_final {:?}", vk_x_val);

    let mut a = vec![
        proof.a,
        vk.alpha1,
        vk_x_final,
        proof.c,
    ];

    for _ in 0..31 {
        a.push(proof.a);
        a.push(vk.alpha1);
        a.push(vk_x_final);
        a.push(proof.c);
    };

    let mut b = vec![
        proof.b,
        vk.beta2,
        vk.gamma2,
        vk.delta2,
    ];

    for _ in 0..31 {
        b.push(proof.b);
        b.push(vk.beta2);
        b.push(vk.gamma2);
        b.push(vk.delta2);
    };

    println!("start native aggregation");
    let start_native_aggregation_time = Instant::now();

    let sipp_proof_native = sipp_prove_native(&a, &b);

    let end_native_aggregation_time = Instant::now();
    println!("end native aggregation");
    println!(
        "native aggregation time: {:?}",
        end_native_aggregation_time.duration_since(start_native_aggregation_time)
    );

    println!("SIPP proof native");

    let sipp_statement_native = sipp_verify_native(&a, &b, &sipp_proof_native).unwrap();

    println!("SIPP statement native");
    // assert!(pairing(sipp_statement.final_A, sipp_statement.final_B) == sipp_statement.final_Z);

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // ! start circuit building
    let testing_value = Fq::from(1u64);
    print_ark_fq(testing_value, "reached line 256".to_string());
    let num_inputs = 1;
    let vk_alpha1 = G1Target::empty(&mut builder);
    print_ark_fq(testing_value, "reached line 259".to_string());
    let vk_beta2 = G2Target::empty(&mut builder);
    print_ark_fq(testing_value, "reached line 261".to_string());
    let vk_gamma2 = G2Target::empty(&mut builder);
    print_ark_fq(testing_value, "reached line 263".to_string());
    let vk_delta2 = G2Target::empty(&mut builder);
    print_ark_fq(testing_value, "reached line 265".to_string());
    let vk_ic = (0..num_inputs + 1)
        .map(|_| G1Target::empty(&mut builder))
        .collect_vec();
    print_ark_fq(testing_value, "reached line 269".to_string());

    let input_target = (0..num_inputs)
        .map(|_| FqTarget::empty(&mut builder))
        .collect_vec();
    print_ark_fq(testing_value, "reached line 274".to_string());
    let proof_a = G1Target::empty(&mut builder);
    let proof_b = G2Target::empty(&mut builder);
    let proof_c = G1Target::empty(&mut builder);
    print_ark_fq(testing_value, "reached line 278".to_string());

    let vk_x = vk_ic[0].clone();
    print_ark_fq(testing_value, "reached line 281".to_string());

    for i in 0..num_inputs {
        // vk_x = vk_x.add(vk_ic[i+1].mul_bigint(&[input[i];1])).into_affine();
        let (x, y) = (vk_ic[i + 1].x.clone(), vk_ic[i + 1].y.clone());
    print_ark_fq(testing_value, "reached line 286".to_string());
        let (x_ic_mul_input) = x.mul(&mut builder, &input_target[i]);
    print_ark_fq(testing_value, "reached line 288".to_string());
        let (y_ic_mul_input) = y.mul(&mut builder, &input_target[i]);
    print_ark_fq(testing_value, "reached line 290".to_string());
        // let (x_ic_mul_input_plus_x) = x_ic_mul_input.add(&mut builder, &vk_ic[i].x);
        // let (y_ic_mul_input_plus_y) = y_ic_mul_input.add(&mut builder, &vk_ic[i].y);
        let temp_affine = G1Target::new(x_ic_mul_input, y_ic_mul_input);
    print_ark_fq(testing_value, "reached line 294".to_string());
        vk_x.add(&mut builder, &temp_affine);
    }

    let neg_a = proof_a.neg(&mut builder);
    // print_fq_target(&mut builder, &proof_b.x, "Pairing check #1".to_string());
    print_ark_fq(testing_value, "reached line 300".to_string());

    let mut a:  Vec<G1Target<F, D>> = vec![neg_a.clone(), vk_alpha1.clone(), vk_x.clone(), proof_c.clone()];
    for _ in 0..31 {
        a.push(neg_a.clone());
        a.push(vk_alpha1.clone());
        a.push(vk_x.clone());
        a.push(proof_c.clone());
    }
    print_ark_fq(testing_value, "reached line 309".to_string());

    let mut b: Vec<G2Target<F, D>> = vec![
        proof_b.clone(),
        vk_beta2.clone(),
        vk_gamma2.clone(),
        vk_delta2.clone(),
    ];


    for _ in 0..31 {
        b.push(proof_b.clone());
        b.push(vk_beta2.clone());
        b.push(vk_gamma2.clone());
        b.push(vk_delta2.clone());
    };
    print_ark_fq(testing_value, "reached line 325".to_string());

    let n: usize = 128;
    let log_n = n.trailing_zeros();
    let sipp_proof_circuit = (0..2 * log_n + 1)
    .map(|_| Fq12Target::empty(&mut builder))
    .collect_vec();
print_ark_fq(testing_value, "reached line 332".to_string());
    let sipp_statement = sipp_verifier_circuit::<F, C, D>(&mut builder, &a, &b, &sipp_proof_circuit);
    print_ark_fq(testing_value, "reached line 334".to_string());
    // final pairing. This also takes much time!
    let z = pairing_circuit::<F, C, D>(&mut builder, sipp_statement.final_A, sipp_statement.final_B);
    print_ark_fq(testing_value, "reached line 337".to_string());
    Fq12Target::connect(&mut builder, &z, &sipp_statement.final_Z);
    print_ark_fq(testing_value, "reached line 339".to_string());

    println!("Start building circuit");
    let start_building_circuit = Instant::now();
    let data = builder.build::<C>();
    let end_building_circuit = Instant::now();
    println!(
        "End building circuit. took {:?}",
        end_building_circuit.duration_since(start_building_circuit)
    );

    // ! aggregate using SIPP instead of making pairing checks
   
    let (vk_alpha_x, vk_alpha_y) = vk.alpha1.xy().unwrap();
    let (vk_beta2_x, vk_beta2_y) = vk.beta2.xy().unwrap();
    let (vk_gamma_x, vk_gamma_y) = vk.gamma2.xy().unwrap();
    let (vk_delta2_x, vk_delta2_y) = vk.delta2.xy().unwrap();
    // let vk_ic_0 = vk.ic.xy().unwrap();
    let (vk_ic_0_x, vk_ic_0_y) = vk.ic[0].xy().unwrap();
    let (vk_ic_1_x, vk_ic_1_y) = vk.ic[1].xy().unwrap();

    let (proof_a_x, proof_a_y) = proof.a.xy().unwrap();
    let (proof_b_x, proof_b_y) = proof.b.xy().unwrap();
    let (proof_c_x, proof_c_y) = proof.c.xy().unwrap();

    let mut pw = PartialWitness::<F>::new();
    vk_alpha1.x.set_witness(&mut pw, vk_alpha_x);
    vk_alpha1.y.set_witness(&mut pw, vk_alpha_y);

    vk_beta2.x.set_witness(&mut pw, vk_beta2_x);
    vk_beta2.y.set_witness(&mut pw, vk_beta2_y);

    vk_gamma2.x.set_witness(&mut pw, vk_gamma_x);
    vk_gamma2.y.set_witness(&mut pw, vk_gamma_y);

    vk_delta2.x.set_witness(&mut pw, vk_delta2_x);
    vk_delta2.y.set_witness(&mut pw, vk_delta2_y);

    vk_ic[0].x.set_witness(&mut pw, vk_ic_0_x);
    vk_ic[0].y.set_witness(&mut pw, vk_ic_0_y);
    vk_ic[1].x.set_witness(&mut pw, vk_ic_1_x);
    vk_ic[1].y.set_witness(&mut pw, vk_ic_1_y);

    // let vk_ic = (0..num_inputs).map(|_| G1Target::empty(&mut builder)).collect_vec();
    proof_a.x.set_witness(&mut pw, proof_a_x);
    proof_a.y.set_witness(&mut pw, proof_a_y);
    proof_b.x.set_witness(&mut pw, proof_b_x);
    proof_b.y.set_witness(&mut pw, proof_b_y);
    proof_c.x.set_witness(&mut pw, proof_c_x);
    proof_c.y.set_witness(&mut pw, proof_c_y);

    // num_inputs = 0;
    input_target[0].set_witness(&mut pw, &Fq::from(20u64));
    sipp_proof_circuit.iter()
    .zip_eq(sipp_proof_native.iter())
    .for_each(|(t, w)| {
        t.set_witness(&mut pw, w);
    });

    println!("start proving");
    let start_proving = Instant::now();

    let _proof = data.prove(pw).unwrap();
    let end_proving = Instant::now();
    println!("proof {:?}", _proof);
    println!(
        "end proving. took {:?}",
        end_proving.duration_since(start_proving)
    );    
    println!("end proving");
}
