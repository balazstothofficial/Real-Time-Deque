theory Big
  imports Common
begin

datatype 'a state = 
     Reverse "'a current" "'a stack" "'a list" nat
   | Common "'a Common.state"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Common common) = Common.toList common"
| "toList (Reverse (Current extra _ _ remained) big aux count) = (
   let reversed = revN count (Stack.toList big) aux in
    extra @ (revN remained reversed [])
  )"

fun toCurrentList :: "'a state \<Rightarrow> 'a list" where
  "toCurrentList (Common common) = Common.toCurrentList common"
| "toCurrentList (Reverse current _ _ _) = Current.toList current"

fun tick :: "'a state \<Rightarrow> 'a state" where
  "tick (Common state) = Common (Common.tick state)"
| "tick (Reverse current _ aux 0) = Common (normalize (Copy current aux [] 0))"
| "tick (Reverse current big aux count) = 
     Reverse current (Stack.pop big) ((first big)#aux) (count - 1)"

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Common state) = Common (Common.push x state)"
| "push x (Reverse current big aux count) = Reverse (put x current) big aux count"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Common state) = (let (x, state) = Common.pop state in (x, Common state))"
| "pop (Reverse current big aux count) = (top current, Reverse (bottom current) big aux count)"

fun isEmpty :: "'a state \<Rightarrow> bool" where
  "isEmpty (Common state) = Common.isEmpty state"
| "isEmpty (Reverse current _ _ _) = Current.isEmpty current"

fun invariant :: "'a state \<Rightarrow> bool" where
  "invariant (Common state) \<longleftrightarrow> Common.invariant state"
| "invariant (Reverse current big aux count) \<longleftrightarrow> (
   case current of Current extra added old remained \<Rightarrow>
      Current.invariant current
    \<and> List.length aux \<ge> remained - count
    \<and> remained \<ge> count
    \<and> count \<le> Stack.size big
    \<and> Stack.toList old = rev (take (Stack.size old) ((rev (Stack.toList big)) @ aux))
    \<and> take remained (Stack.toList old) = rev (take remained (revN count (Stack.toList big) aux))
)"

(* TODO: This should be prevented on a higher level? *) 
fun pop_invariant :: "'a state \<Rightarrow> bool" where
  "pop_invariant (Common state) = True"
| "pop_invariant (Reverse (Current _ _ _ remained) _ _ count) \<longleftrightarrow> remained > count"

(* Just for proof *)
fun remainingSteps :: "'a state \<Rightarrow> nat" where
  "remainingSteps (Common state) = Common.remainingSteps state"
| "remainingSteps (Reverse (Current _ _ _ remaining) _ _ count) = count + remaining + 1"

fun size :: "'a state \<Rightarrow> nat" where
  "size (Common state) = Common.size state"
| "size (Reverse current _ _ _) = Current.size current"

fun newSize :: "'a state \<Rightarrow> nat" where
  "newSize (Common state) = Common.newSize state"
| "newSize (Reverse current _ _ _) = Current.newSize current"

end