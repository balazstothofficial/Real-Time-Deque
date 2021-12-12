theory Transformation 
  imports States
begin

datatype 'a transformation =
   Left "'a Small.state" "'a Big.state"
 | Right "'a Big.state" "'a Small.state"

fun toListLeft :: "'a transformation \<Rightarrow> 'a list" where
  "toListLeft (Left small big)  = Small.toList small @ (rev (Big.toList big))"
| "toListLeft (Right big small) = Big.toList big @ (rev (Small.toList small))"
 
fun toListRight :: "'a transformation \<Rightarrow> 'a list" where
  "toListRight (Left small big)  = Big.toList big @ (rev (Small.toList small))"
| "toListRight (Right big small) = Small.toList small @ (rev (Big.toList big))"

fun tick :: "'a transformation \<Rightarrow> 'a transformation" where
  "tick (Left small big) = (case States.tick (big, small) of (big, small) \<Rightarrow> Left small big)"
| "tick (Right big small) = (case States.tick (big, small) of (big, small) \<Rightarrow> Right big small)"  

definition fourTicks where
  "fourTicks \<equiv> tick o tick o tick o tick"

definition sixTicks where
  "sixTicks \<equiv> tick o tick o tick o tick o tick o tick"

fun invariant :: "'a transformation \<Rightarrow> bool" where
  "invariant (Left small big)  \<longleftrightarrow> States.invariant (big, small)"
| "invariant (Right big small) \<longleftrightarrow> States.invariant (big, small)"

fun flip :: "('a * 'a) option \<Rightarrow> ('a * 'a) option" where
  "flip (Some (a, b)) = Some (b, a)"
| "flip None = None"

fun terminateTicks where
  "terminateTicks (Left small big) = flip (States.terminateTicks (big, small))"
| "terminateTicks (Right big small) = States.terminateTicks (big, small)"

(* Probably not needed: *)

fun minNewSize:: "'a transformation \<Rightarrow> (nat * nat)" where
  "minNewSize (Left small big)  = (Small.minNewSize small, Big.minNewSize big)"
| "minNewSize (Right big small) = (Small.minNewSize small, Big.minNewSize big)"

fun length :: "'a transformation \<Rightarrow> nat" where
  "length transformation = List.length (toListLeft transformation)"

end