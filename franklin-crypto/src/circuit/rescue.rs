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


pub fn generate_powers<CS,E>(
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
fn generate_roots<CS,E>(
    mut cs: CS,
    x: &AllocatedNum<E>,
    alphas: &(Option<E::Fr>,Option<E::Fr>)
) -> Result<AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E>,E:Engine
{
        //Calculate the root
        let result_var=AllocatedNum::alloc(cs.namespace(|| "found root"), ||{
            let zero=BigUint::from_str("0").unwrap();
            let one=BigUint::from_str("1").unwrap();
            let p={
                let mut p=E::Fr::char();
                p.sub_noborrow(&E::Fr::one().into_repr());
                let p=E::Fr::from_repr(p).unwrap();
                fr_to_biguint(&p)+&one
            };
            let k_inv=fr_to_biguint(&alphas.1.unwrap());
            let a=fr_to_biguint(&x.get_value().unwrap());
            let res=a.modpow(&k_inv,&p);
            Ok(biguint_to_fr(&res).unwrap())
        })?;

        {//Prove that the root is correct
            let alpha_bits_be = {
                let mut tmp = Vec::with_capacity(E::Fr::NUM_BITS as usize);
                let mut found_one = false;
                for b in BitIterator::new(alphas.0.unwrap().into_repr()) {
                    found_one |= b;
                    if !found_one {
                        continue;
                    }
                    tmp.push(b);
                }
                tmp
            };
            let squares={
                let mut tmp:Vec<AllocatedNum<E>>=vec![result_var.clone()];
                for i in 1..alpha_bits_be.len(){
                    let sqr=tmp.last().unwrap().square(cs.namespace(|| format!("root_result_sqr{}",i)))?;
                    tmp.push(sqr);
                }
                tmp
            };
            assert_eq!(squares.len(),alpha_bits_be.len());
            let n=alpha_bits_be.len();
            let mut tmp=squares[n-1].clone();
            let last_m={
                let mut res=0;
                for i in 1..n{
                    if alpha_bits_be[i] {
                        res=i;
                    }
                }
                res
            };
            for i in 1..last_m{
                if alpha_bits_be[i] {
                    tmp=squares[n-1-i].mul(cs.namespace(|| format!("mul_due_to_bit{}",i)),&tmp)?;
                }
            }
            cs.enforce(
                || "last multiplication has to yield the argument",
                |lc| lc + tmp.get_variable(),
                |lc| lc + squares[last_m].get_variable(),
                |lc| lc + x.get_variable()
            );
    
        };
        Ok(result_var) 
}


fn fr_to_biguint<Fr: PrimeField>(fr: &Fr) -> BigUint {
    let mut buffer = Vec::<u8>::new();
    fr.into_repr()
        .write_be(&mut buffer)
        .expect("failed to write into Vec<u8>");
    let value = BigUint::from_bytes_be(&buffer);
    value
}

fn biguint_to_fr<F: PrimeField>(bigint: &BigUint) -> Option<F> {
    F::from_str(&bigint.to_str_radix(10))
}

fn get_alphas<F:PrimeField>() -> (Option<F>,Option<F>){
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
            //if this prime number does not fulfill the condition gcd(alpha,p-1)=1
            //we obtain the next prime number and test it
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
    let anti_alpha=alpha.modpow(&(&p_m_1 - &one - &one), &p_m_1 );
    (biguint_to_fr(&alpha),biguint_to_fr(&anti_alpha))
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
    fn power_test() {
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
            let y = generate_powers(&mut cs,&x,&a).unwrap();

            let xx= fr_to_biguint(&x.get_value().unwrap());
            let yy= fr_to_biguint(&y.get_value().unwrap());
            let k=fr_to_biguint(&a);
            let p={
                let mut p=Fr::char();
                p.sub_noborrow(&Fr::one().into_repr());
                let p=Fr::from_repr(p).unwrap();
                let one=BigUint::from_str("1").unwrap();
                fr_to_biguint(&p)+&one
            };
            assert_eq!(xx.modpow(&k,&p),yy.clone());

            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(),n);
            assert_eq!(y.get_value().unwrap(),Fr::from_str(&y_s[..]).unwrap());
        }
    }

    #[test]
    fn root_test(){
        let alphas=get_alphas::<Fr>();
        assert_eq!(alphas.0.unwrap(),Fr::from_str("5").unwrap());
        let values=vec!["1","2","3","4","5","6","7","8","9"];
        for x_s in values{
            let mut cs = TestConstraintSystem::<Bn256>::new();
            let x = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str(&x_s[..]).unwrap()) ).unwrap();
            let y = generate_roots(&mut cs, &x, &alphas).unwrap();

            let xx= fr_to_biguint(&x.get_value().unwrap());
            let yy= fr_to_biguint(&y.get_value().unwrap());
            let k=fr_to_biguint(&alphas.0.unwrap());
            
            let p={
                let mut p=Fr::char();
                p.sub_noborrow(&Fr::one().into_repr());
                let p=Fr::from_repr(p).unwrap();
                let one=BigUint::from_str("1").unwrap();
                fr_to_biguint(&p)+&one
            };
            assert_eq!(yy.modpow(&k,&p),xx.clone());
            assert!(cs.is_satisfied());
        }
    }

}
