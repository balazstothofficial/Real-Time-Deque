theory Transformation 
  imports Big Small
begin

fun ticksHelper :: "('a Big.state * 'a Small.state) \<Rightarrow> 'a Big.state * 'a Small.state" where
  "ticksHelper (Reverse currentB big auxB 0, Reverse1 currentS _ auxS) =
    (Big.Common (normalize (Copy currentB auxB [] 0)), Reverse2 currentS auxS big [] 0)"
| "ticksHelper (left, right) = (Big.tick left, Small.tick right)"

datatype 'a transformation =
   Left "'a Small.state" "'a Big.state"
 | Right "'a Big.state" "'a Small.state"

fun toListLeft :: "'a transformation \<Rightarrow> 'a list" where
  "toListLeft (Left small big)  = Small.toList small  @ (rev (Big.toList big))"
| "toListLeft (Right big small) = Big.toList big @ (rev (Small.toList small))"
 
fun toListRight :: "'a transformation \<Rightarrow> 'a list" where
  "toListRight (Left small big)  = Big.toList big @ (rev (Small.toList small))"
| "toListRight (Right big small) = Small.toList small @ (rev (Big.toList big))"

fun ticks :: "'a transformation \<Rightarrow> 'a transformation" where
  "ticks (Left small big) = (case ticksHelper (big, small) of (big, small) \<Rightarrow> Left small big)"
| "ticks (Right big small) = (case ticksHelper (big, small) of (big, small) \<Rightarrow> Right big small)"  

fun fourTicks where
  "fourTicks transformation = (ticks (ticks (ticks (ticks transformation))))"

fun sixTicks where
  "sixTicks transformation = ticks (ticks (fourTicks transformation))"


end
