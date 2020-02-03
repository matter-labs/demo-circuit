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
        val: E::Fr,
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let var = cs.alloc(|| &msg[..], || { Ok(val) })?;
        Ok(AllocatedRepr {
            variable: var,
            value: Some(val)
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
            Ok(Self::alloc(cs,"power result",E::Fr::one()).unwrap())
        }else{
            let alpha_bits = {
                let mut res:Vec<bool>=BitIterator::new(alpha.get_value().unwrap().into_repr()).collect();
                while (res.len()>1)&&(!res[res.len()-1]) {
                    res.remove(res.len()-1);
                }
                res
            };
            let vars = { //Define all multipliers needed to rise x to the power alpha
                let res= vec![x];
                for i in 1..alpha_bits.len(){
                    let cs = &mut cs.namespace(|| format!("Multiplier{}", i));
                    let v = res[res.len()-1];
                    let mut sqr_=v.get_value().unwrap();
                    sqr_.mul_assign(&sqr_.clone());
                    let sqr_v=Self::alloc(cs,"multiplier", sqr_)?;
                    cs.enforce( 
                        || "define multiplier",
                        |lc| lc + v.variable,
                        |lc| lc + v.variable,
                        |lc| lc + sqr_v.variable
                    );
                };
                res
            };
            assert_eq!(vars.len(),alpha_bits.len());
            let mut multipliers= vec![];
            for (i,b) in alpha_bits.iter().enumerate(){
                if *b { multipliers.push(vars[i]); }
            }
            assert!(multipliers.len()>0);
            if multipliers.len()==1 {
                Ok(multipliers.last().unwrap().clone().clone())
            }else{
                let mut new_vars=vec![];
                for i in 1..multipliers.len(){
                    let cs = &mut cs.namespace(|| format!("Multiply{}", i));
                    let prev_v = if i==1{ multipliers[0] }else{ new_vars.last().unwrap() };
                    let mut v= prev_v.get_value().unwrap();
                    v.mul_assign(&multipliers[i].get_value().unwrap());
                    let next_v=Self::alloc(cs,format!("powerresult{}",i).as_str(), v )?;
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

