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
            let mut val=res.get_value().unwrap().clone();
            val.mul_assign(&x.get_value().unwrap());
            let val_=AllocatedNum::alloc(cs.namespace(|| format!("power{}",c)),|| Ok(val) )?;
            cs.enforce(
                || format!("define_power{}",c),
                |lc| lc + res.get_variable(),
                |lc| lc + x.get_variable(),
                |lc| lc + val_.get_variable()
            );
            res=val_;
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
            ("1","2","1"),
            ("1","3","1"),
            ("2","2","4"),
            ("2","3","8"),
            ("2","4","16"),
            ("2","5","32"),
            ("2","6","64"),
            ("2","7","128"),
            ("3","2","9"),
            ("3","3","27")
        ];
        for (x_s,a_s,y_s) in values{
            let mut cs = TestConstraintSystem::<Bls12>::new();
            let x = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str(&x_s[..]).unwrap()) ).unwrap();
            let a = Fr::from_str(&a_s[..]).unwrap();
            let y = raise_to_power(&mut cs,&x,&a).unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(y.get_value().unwrap(),Fr::from_str(&y_s[..]).unwrap());
        }
    }

}
