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

#[derive(Clone,Copy)]
struct AllocatedRepr<E:Engine> {
    variable: Variable,
    value: Option<E::Fr>
}


impl<E:Engine> AllocatedRepr<E>{
    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    pub fn alloc<CS>(
        cs: &mut CS,
        msg : &str,
        val: Option<E::Fr>,
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let var = cs.alloc(|| &msg[..], || { Ok(val.unwrap()) })?;
        Ok(AllocatedRepr {
            variable: var,
            value: val
        })
    }
    pub fn raise_to_power<CS>(
        mut cs: CS,
        name:&str,
        x: &Self,
        alpha: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let cs = &mut cs.namespace(|| &name[..]);
        if alpha.get_value().unwrap().is_zero() {
            Ok(Self::alloc(cs,"power result",Some(E::Fr::one()))?)
        }else{
            if alpha.get_value().unwrap() == E::Fr::one() {
                Ok(x.clone())
            }else{
                let mut res = x.clone();
                let mut counter=E::Fr::one();
                let mut c=1;
                loop{
                    counter.add_assign(&E::Fr::one());
                    c+=1;
                    let mut val=res.get_value().unwrap().clone();
                    val.mul_assign(&x.get_value().unwrap());
                    let val_=Self::alloc(cs,&format!("power{}",c)[..], Some(val))?;
                    cs.enforce(
                        || format!("define_power{}",c),
                        |lc| lc + res.variable,
                        |lc| lc + x.variable,
                        |lc| lc + val_.variable
            
                    );
                    res=val_;
                    if counter==alpha.get_value().unwrap() {
                        break;
                    }
                }
                Ok(res)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use bellman::{ConstraintSystem};
    use bellman::pairing::bls12_381::{Bls12, Fr};
    use bellman::pairing::ff::{Field, PrimeField};
    use ::circuit::test::*;
    use super::{
        AllocatedRepr
    };

    #[test]
    fn test_allocated_representation() {
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let values=vec![
            ("v0","0"),
            ("v1","1"),
            ("v2","2"),
            ("v3","3"),
            ("v4","4"),
            ("v5","5"),
            ("v6","6"),
            ("v7","7")
        ];
        for (name,x_s) in values{
            let x = AllocatedRepr::alloc(&mut cs, &name[..], Some(Fr::from_str(&x_s[..]).unwrap())).unwrap();
            assert_eq!(x.get_value().unwrap(), Fr::from_str(&x_s[..]).unwrap());
            assert_eq!(cs.get(&name[..]), Fr::from_str(&x_s[..]).unwrap());
            assert_eq!(cs.num_constraints(), 0);
        }
    }

    #[test]
    fn test_rising_to_power() {
        let values=vec![
            ("1","0","1"),
            ("1","1","1"),
            ("1","2","1"),
            ("1","3","1"),
            ("2","0","1"),
            ("2","1","2"),
            ("2","2","4"),
            ("2","3","8"),
            ("2","4","16"),
            ("2","5","32"),
            ("2","6","64"),
            ("2","7","128"),
            ("3","0","1"),
            ("3","1","3"),
            ("3","2","9"),
            ("3","3","27")
        ];
        for (x_s,a_s,y_s) in values{
            let mut cs = TestConstraintSystem::<Bls12>::new();
            let x = AllocatedRepr::alloc(&mut cs, "x", Some(Fr::from_str(&x_s[..]).unwrap())).unwrap();
            let a = AllocatedRepr::alloc(&mut cs, "a", Some(Fr::from_str(&a_s[..]).unwrap())).unwrap();
            let y = AllocatedRepr::raise_to_power(&mut cs,&format!("{}^{}",x_s,a_s)[..],&x,&a).unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(y.get_value().unwrap(),Fr::from_str(&y_s[..]).unwrap());
        }
    }
}
