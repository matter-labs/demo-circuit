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
        let res={
            let mut tmp:Vec<AllocatedNum<E>>=vec![];
            //alpha is constant
            for (i,b) in alpha_bits_be.into_iter().rev().enumerate(){
                if b {
                    let prev=tmp.last();
                    let next=match prev{
                        Some(ref value) => {
                            squares[i].mul(cs.namespace(|| format!("mul_due_to_bit{}",i)),value)?
                        },
                        None => {
                            squares[i].clone()
                        }
                    };
                    tmp.push(next);
                }
            }
            tmp.last().unwrap().clone()
        };
        Ok(res) 
}

#[cfg(test)]
mod test {
    use bellman::{ConstraintSystem};
    use bellman::pairing::bls12_381::{Bls12, Fr};
    use bellman::pairing::ff::{Field, PrimeField};
    use ::circuit::test::*;
    use ::circuit::num::AllocatedNum;
    use ::circuit::rescue::*;

    #[test]
    fn test_rising_to_power() {
        let values=vec![
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
            let mut cs = TestConstraintSystem::<Bls12>::new();
            let x = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str(&x_s[..]).unwrap()) ).unwrap();
            let a = Fr::from_str(&a_s[..]).unwrap();
            let y = raise_to_power(&mut cs,&x,&a).unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(),n);
            assert_eq!(y.get_value().unwrap(),Fr::from_str(&y_s[..]).unwrap());
        }
    }

}
