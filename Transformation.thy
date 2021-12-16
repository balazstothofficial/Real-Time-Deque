theory Transformation 
  imports States
begin

datatype 'a transformation =
   Left "'a Small.state" "'a Big.state"
 | Right "'a Big.state" "'a Small.state"

fun toListLeft :: "'a transformation \<Rightarrow> 'a list" where
  "toListLeft (Left small big)  = Small.toList small @ (rev (Big.toList big))"
| "toListLeft (Right big small) = Big.toList big @ (rev (Small.toList small))"

fun toListLeft' :: "'a transformation \<Rightarrow> 'a list" where
  "toListLeft' (Left (Small.state.Common (state.Idle _ small)) 
                     (Big.state.Common   (state.Idle _ big)))
     = Idle.toList small @ (rev (Idle.toList big))"
| "toListLeft' (Right (Big.state.Common   (state.Idle _ big)) 
                      (Small.state.Common (state.Idle _ small)))
     = Idle.toList big @ (rev (Idle.toList small))"
 
fun toListRight :: "'a transformation \<Rightarrow> 'a list" where
  "toListRight (Left small big)  = Big.toList big @ (rev (Small.toList small))"
| "toListRight (Right big small) = Small.toList small @ (rev (Big.toList big))"

fun tick :: "'a transformation \<Rightarrow> 'a transformation" where
  "tick (Left small big) = (case States.tick (big, small) of (big, small) \<Rightarrow> Left small big)"
| "tick (Right big small) = (case States.tick (big, small) of (big, small) \<Rightarrow> Right big small)"  

definition fourTicks where
  "fourTicks \<equiv> tick^^4"

definition sixTicks where
  "sixTicks \<equiv> tick^^6"

fun invariant :: "'a transformation \<Rightarrow> bool" where
  "invariant (Left small big)  \<longleftrightarrow> States.invariant (big, small)"
| "invariant (Right big small) \<longleftrightarrow> States.invariant (big, small)"

fun remainingSteps where
  "remainingSteps (Left small big) = States.remainingSteps (big, small)"
| "remainingSteps (Right big small) = States.remainingSteps (big, small)"

end