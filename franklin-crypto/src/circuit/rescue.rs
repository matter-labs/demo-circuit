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

#[derive(Clone)]
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
        x: &Self,
        alpha: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let cs = &mut cs.namespace(|| "power");
        if alpha.get_value().unwrap().is_zero() {
            Ok(Self::alloc(cs,"power result",Some(E::Fr::one()))?)
        }else{
            let n_bits={
                let mut res=0;
                for (i,b) in BitIterator::new(alpha.get_value().unwrap().into_repr()).enumerate(){
                    if b.clone() {
                        res=i+1;
                    }
                }          
                res
            };
            let vars = { //Define all multipliers with powers 2^k needed to be defined to rise x to the power alpha
                let mut res:Vec<AllocatedRepr<E>>= vec![x.clone()];
                for i in 1..n_bits{
                    let cs = &mut cs.namespace(|| format!("Multiplier{}", i));
                    let v = &res[res.len()-1];
                    let mut sqr_=v.get_value().unwrap();
                    sqr_.mul_assign(&sqr_.clone());
                    let sqr_v=Self::alloc(cs,"multiplier", Some(sqr_))?;
                    cs.enforce( 
                        || "define multiplier",
                        |lc| lc + v.variable,
                        |lc| lc + v.variable,
                        |lc| lc + sqr_v.variable
                    );
                    res.push(sqr_v);
                };
                res
            };
            assert_eq!(vars.len(),n_bits);
            let multipliers={//Defining list of multipliers with powers 2^k needed to multiply
                let mut res=vec![];
                for (i,b) in BitIterator::new(alpha.get_value().unwrap().into_repr()).enumerate(){
                    if b.clone() {
                        res.push(&vars[i]); 
                    }
                }
                res
            };
            assert!(multipliers.len()>0);
            if multipliers.len()==1 {
                Ok(multipliers.last().unwrap().clone().clone())
            }else{
                let mut new_vars:Vec<AllocatedRepr<E>>=vec![];
                for i in 1..multipliers.len(){
                    let cs = &mut cs.namespace(|| format!("Multiply{}", i));
                    let prev_v = if i==1{ &multipliers[0] }else{ new_vars.last().unwrap() };
                    let mut v= prev_v.get_value().unwrap();
                    v.mul_assign(&multipliers[i].get_value().unwrap());
                    let next_v=Self::alloc(cs,format!("powerresult{}",i).as_str(), Some(v) )?;
                    cs.enforce(
                        || "define powerresult",
                        |lc| lc + prev_v.variable,
                        |lc| lc + multipliers[i].variable,
                        |lc| lc + next_v.variable
                    );
                    new_vars.push(next_v);
                }
                Ok(new_vars.last().unwrap().clone().clone())
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
            ("v3","1")
        ];
        for (name,x_s) in values{
            let x = AllocatedRepr::alloc(&mut cs, &name[..], Some(Fr::from_str(&x_s[..]).unwrap())).unwrap();
            assert!(x.get_value().unwrap() == Fr::from_str(&x_s[..]).unwrap());
            assert!(cs.get(&name[..]) == Fr::from_str(&x_s[..]).unwrap());
            assert_eq!(cs.num_constraints(), 0);
        }
    }

    #[test]
    fn test_rising_to_power() {
        let values=vec![
            ("1","0","1"),
            ("1","1","1"),
            ("1","2","1"),
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
            let y = AllocatedRepr::raise_to_power(&mut cs,&x,&a).unwrap();
            assert_eq!(y.get_value().unwrap(),Fr::from_str(&y_s[..]).unwrap());
            assert!(cs.is_satisfied());
        }
    }
}
