theory Transformation 
  imports States
begin

datatype 'a transformation =
   Left "'a Small.state" "'a Big.state"
 | Right "'a Big.state" "'a Small.state"

fun toListLeft :: "'a transformation \<Rightarrow> 'a list" where
  "toListLeft (Left small big)  = States.toListSmallFirst (big, small)"
| "toListLeft (Right big small) = States.toListBigFirst (big, small)"
 
fun toListRight :: "'a transformation \<Rightarrow> 'a list" where
  "toListRight (Left small big)  = States.toListBigFirst (big, small)"
| "toListRight (Right big small) = States.toListSmallFirst (big, small)"

fun tick :: "'a transformation \<Rightarrow> 'a transformation" where
  "tick (Left small big) = (case States.tick (big, small) of (big, small) \<Rightarrow> Left small big)"
| "tick (Right big small) = (case States.tick (big, small) of (big, small) \<Rightarrow> Right big small)"  

abbreviation fourTicks where
  "fourTicks \<equiv> tick^^4"

abbreviation sixTicks where
  "sixTicks \<equiv> tick^^6"

fun invariant :: "'a transformation \<Rightarrow> bool" where
  "invariant (Left small big)  \<longleftrightarrow> States.invariant (big, small)"
| "invariant (Right big small) \<longleftrightarrow> States.invariant (big, small)"

fun isEmpty :: "'a transformation \<Rightarrow> bool" where
  "isEmpty (Left small big)  \<longleftrightarrow> States.isEmpty (big, small)"
| "isEmpty (Right big small) \<longleftrightarrow> States.isEmpty (big, small)"

fun remainingSteps where
  "remainingSteps (Left small big) = States.remainingSteps (big, small)"
| "remainingSteps (Right big small) = States.remainingSteps (big, small)"

fun inSizeWindow :: "'a transformation \<Rightarrow> bool" where
  "inSizeWindow (Left small big) = States.inSizeWindow (big, small)"
| "inSizeWindow (Right big small) = States.inSizeWindow (big, small)"

fun inSizeWindow' :: "'a transformation \<Rightarrow> nat \<Rightarrow> bool" where
  "inSizeWindow' (Left small big) steps = States.inSizeWindow' (big, small) steps"
| "inSizeWindow' (Right big small) steps = States.inSizeWindow' (big, small) steps"

end