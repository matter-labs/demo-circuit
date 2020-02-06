extern crate num_bigint;
use self::num_bigint::{BigUint,ToBigUint};
use std::str::FromStr;
use super::uint32::UInt32;
use super::multieq::MultiEq;
use super::boolean::Boolean;
use bellman::{ConstraintSystem, SynthesisError};
use bellman::pairing::Engine;
use circuit::Assignment;
use bellman::pairing::ff::{
    Field,
    SqrtField,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};
use bellman::{
    LinearCombination,
    Variable
};
use super::num::AllocatedNum;


fn raise_to_power<CS,E>(
    mut cs: CS,
    x: &AllocatedNum<E>,
    alpha: &E::Fr
) -> Result<AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E>,E:Engine
{
        assert_ne!(*alpha,E::Fr::zero());
        assert_ne!(*alpha,E::Fr::one());
        let alpha_bits_be = {
            let mut tmp = Vec::with_capacity(E::Fr::NUM_BITS as usize);
            let mut found_one = false;
            for b in BitIterator::new(alpha.into_repr()) {
                found_one |= b;
                if !found_one {
                    continue;
                }
                tmp.push(b);
            }
            tmp
        };
        let squares={//define square, square of square, etc variables
            let mut tmp:Vec<AllocatedNum<E>>=vec![x.clone()];
            //alpha is constant
            for i in 1..alpha_bits_be.len(){
                let sqr=tmp.last().unwrap().square(cs.namespace(|| format!("sqr{}",i)))?;
                tmp.push(sqr);
            }
            tmp
        };
        assert_eq!(squares.len(),alpha_bits_be.len());
        let res={
            let n=alpha_bits_be.len();
            let mut tmp=squares[n-1].clone();
            //alpha is constant
            for i in 1..n{
                if alpha_bits_be[i] {
                    tmp=squares[n-1-i].mul(cs.namespace(|| format!("mul_due_to_bit{}",i)),&tmp)?;
                }
            }
            tmp.clone()
        };
        Ok(res) 
}

fn fr_to_biguint<Fr: PrimeField>(fr: &Fr) -> BigUint {
    let mut buffer = Vec::<u8>::new();
    Fr::char()
        .write_be(&mut buffer)
        .expect("failed to write into Vec<u8>");
    buffer.clear();
    fr.into_repr()
        .write_be(&mut buffer)
        .expect("failed to write into Vec<u8>");
    let value = BigUint::from_bytes_be(&buffer);
    value
}

fn biguint_to_fr<F: PrimeField>(bigint: &BigUint) -> Option<F> {
    F::from_str(&bigint.to_str_radix(10))
}

fn get_alphas<F:PrimeField>() -> Result<(F,F), SynthesisError>{
    let zero=BigUint::from_str("0").unwrap();
    let one=BigUint::from_str("1").unwrap();
    let p_m_1={
        let mut p=F::char();
        p.sub_noborrow(&F::one().into_repr());
        let p=F::from_repr(p).unwrap();
        fr_to_biguint(&p)
    };
    let alpha={
        let mut erath=vec![BigUint::from_str("2").unwrap(),BigUint::from_str("3").unwrap()];
        let mut res=erath.last().unwrap().clone();
        while (&p_m_1 % &res)==zero{
            while {
                let mut prime=true;
                for pr in erath.iter(){
                    prime &= (&res % pr) != zero;
                }
                !prime
            } {
                res+=&one;
            }
            erath.push(res.clone());
        }
        res
    };
    let anti_alpha:BigUint=&p_m_1/&alpha;
    assert_eq!(((&alpha * &anti_alpha) % &p_m_1).clone(),one.clone() );
    let res_alpha=biguint_to_fr(&alpha).unwrap();
    let res_anti_alpha=biguint_to_fr(&anti_alpha).unwrap();
    Ok((res_alpha,res_anti_alpha))
}


#[cfg(test)]
mod test {
    use bellman::{ConstraintSystem};
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::{Field, PrimeField};
    use ::circuit::test::*;
    use ::circuit::num::AllocatedNum;
    use ::circuit::rescue::*;

    #[test]
    fn test_rising_to_power() {
        let values=vec![
            // x, a, x^a, constraints
            ("1","2","1",1),
            ("1","3","1",2),
            ("1","4","1",2),
            ("1","5","1",3),
            ("1","6","1",3),
            ("1","7","1",4),

            ("2","2","4",1),
            ("2","3","8",2),
            ("2","4","16",2),
            ("2","5","32",3),
            ("2","6","64",3),
            ("2","7","128",4),

            ("3","2","9",1),
            ("3","3","27",2),
            ("3","4","81",2),
            ("3","5","243",3),
            ("3","6","729",3),
            ("3","7","2187",4)
        ];
        for (x_s,a_s,y_s,n) in values{
            let mut cs = TestConstraintSystem::<Bn256>::new();
            let x = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str(&x_s[..]).unwrap()) ).unwrap();
            let a = Fr::from_str(&a_s[..]).unwrap();
            let y = raise_to_power(&mut cs,&x,&a).unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(),n);
            assert_eq!(y.get_value().unwrap(),Fr::from_str(&y_s[..]).unwrap());
        }
    }

    #[test]
    fn alpha_test(){
        let alphas=get_alphas::<Fr>().unwrap();
        assert_ne!(alphas.0,Fr::zero());
        assert_ne!(alphas.1,Fr::zero());
        assert_ne!(alphas.0,Fr::one());
        assert_ne!(alphas.1,Fr::one());
        assert_ne!(alphas.0,alphas.1);
        assert_eq!(alphas.0,Fr::from_str("5").unwrap());
        let values=vec!["2","3","4","5","6","7"];
        for x_s in values{
            let mut cs = TestConstraintSystem::<Bn256>::new();
            let x = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str(&x_s[..]).unwrap()) ).unwrap();
            {
                let y = raise_to_power(cs.namespace(|| "part1"),&x,&alphas.0).unwrap();
                let z = raise_to_power(cs.namespace(|| "part2"),&y,&alphas.1).unwrap();
                assert_eq!(x.get_value().unwrap(),z.get_value().unwrap());
            }
            {
                let y = raise_to_power(cs.namespace(|| "part3"),&x,&alphas.1).unwrap();
                let z = raise_to_power(cs.namespace(|| "part4"),&y,&alphas.0).unwrap();
                assert_eq!(x.get_value().unwrap(),z.get_value().unwrap());
            }
        }
    }

}
