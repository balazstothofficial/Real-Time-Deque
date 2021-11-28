theory Transformation 
  imports Big Small
begin

fun tickStates :: "('a Big.state * 'a Small.state) \<Rightarrow> 'a Big.state * 'a Small.state" where
  "tickStates (Reverse currentB big auxB 0, Reverse1 currentS _ auxS) =
    (Big.tick (Reverse currentB big auxB 0), Reverse2 currentS auxS big [] 0)"
| "tickStates (left, right) = (Big.tick left, Small.tick right)"

datatype 'a transformation =
   Left "'a Small.state" "'a Big.state"
 | Right "'a Big.state" "'a Small.state"

fun toListLeft :: "'a transformation \<Rightarrow> 'a list" where
  "toListLeft (Left small big)  = Small.toList small  @ (rev (Big.toList big))"
| "toListLeft (Right big small) = Big.toList big @ (rev (Small.toList small))"

fun length :: "'a transformation \<Rightarrow> nat" where
  "length transformation = List.length (toListLeft transformation)"
 
fun toListRight :: "'a transformation \<Rightarrow> 'a list" where
  "toListRight (Left small big)  = Big.toList big @ (rev (Small.toList small))"
| "toListRight (Right big small) = Small.toList small @ (rev (Big.toList big))"

fun ticks :: "'a transformation \<Rightarrow> 'a transformation" where
  "ticks (Left small big) = (case tickStates (big, small) of (big, small) \<Rightarrow> Left small big)"
| "ticks (Right big small) = (case tickStates (big, small) of (big, small) \<Rightarrow> Right big small)"  

fun fourTicks where
  "fourTicks transformation = (ticks (ticks (ticks (ticks transformation))))"

fun sixTicks where
  "sixTicks transformation = ticks (ticks (fourTicks transformation))"

fun nTicks :: "nat \<Rightarrow> 'a transformation \<Rightarrow> 'a transformation" where
  "nTicks 0 transformation = transformation"
| "nTicks (Suc n) transformation = nTicks n (ticks transformation)"

fun remainingSteps :: "'a transformation \<Rightarrow> nat" where
  "remainingSteps (Left small big) = max (Small.remainingSteps small) (Big.remainingSteps big)"
| "remainingSteps (Right big small) = max (Small.remainingSteps small) (Big.remainingSteps big)"

fun invariant :: "'a transformation \<Rightarrow> bool" where
  "invariant (Left small big) = True"
| "invariant (Right big small) = True"

lemma fourTicks: "fourTicks t = nTicks 4 t"
  by (simp add: numeral_Bit0)

lemma sixTicks: "sixTicks t = nTicks 6 t"
  by (metis add_One_commute add_Suc eval_nat_numeral(3) fourTicks fourTicks.simps nTicks.simps(2) numeral_plus_numeral semiring_norm(3) semiring_norm(4) sixTicks.simps)

end