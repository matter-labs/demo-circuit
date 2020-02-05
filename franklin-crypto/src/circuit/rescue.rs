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
        let mut res = x.clone();
        let mut counter=E::Fr::one();
        let mut c=1;
        loop{//this loop will repeat exactly alpha-1 times
            counter.add_assign(&E::Fr::one());
            c+=1;
            let val = res.mul(cs.namespace(|| format!("power{}",c)), x)?;
            res = val.clone();
            if counter==(*alpha) {
                break;
            }
        }
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
            ("2","2","4",1),
            ("2","3","8",2),
            ("2","4","16",3),
            ("2","5","32",4),
            ("2","6","64",5),
            ("2","7","128",6),
            ("3","2","9",1),
            ("3","3","27",2),
            ("3","4","81",3),
            ("3","5","243",4),
            ("3","6","729",5),
            ("3","7","2187",6)
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
