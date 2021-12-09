theory Big
  imports Common
begin

datatype 'a state = 
     Reverse "'a current" "'a stack" "'a list" nat
   | Common "'a Common.state"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Common common) = Common.toList common"
| "toList (Reverse current _ _ _) = Current.toList current"

fun tick :: "'a state \<Rightarrow> 'a state" where
  "tick (Common state) = Common (Common.tick state)"
| "tick (Reverse current _ auxB 0) = Common (normalize (Copy current auxB [] 0))"
| "tick (Reverse current big auxB count) = 
     Reverse current (Stack.pop big) ((first big)#auxB) (count - 1)"

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Common state) = Common (Common.push x state)"
| "push x (Reverse current big auxB count) = Reverse (put x current) big auxB count"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Common state) = (let (x, state) = Common.pop state in (x, Common state))"
| "pop (Reverse current big auxB count) = (top current, Reverse (bottom current) big auxB count)"

fun isEmpty :: "'a state \<Rightarrow> bool" where
  "isEmpty (Common state) = Common.isEmpty state"
| "isEmpty (Reverse current _ _ _) = Current.isEmpty current"

fun invariant :: "'a state \<Rightarrow> bool" where
  "invariant (Common state) \<longleftrightarrow> Common.invariant state"
| "invariant (Reverse current big auxB count) \<longleftrightarrow> (
   case current of Current _ _ old remained \<Rightarrow>
       Stack.toList old = drop ((List.length auxB + count) - remained) (rev auxB @ (take count (Stack.toList big)))
    \<and> Current.invariant current
    \<and> List.length auxB \<ge> remained - count
    \<and> remained \<ge> count
    \<and> count \<le> Stack.size big
)"

fun pop_invariant :: "'a state \<Rightarrow> bool" where
  "pop_invariant (Common state) = True"
| "pop_invariant (Reverse (Current _ _ _ remained) _ _ count) \<longleftrightarrow> remained > count"

(* Just for proof *)
fun length :: "'a state \<Rightarrow> nat" where
  "length big = List.length (toList big)"

fun remainingSteps :: "'a state \<Rightarrow> nat" where
  "remainingSteps (Common state) = Common.remainingSteps state"
| "remainingSteps (Reverse _ _ _ count) = count"

fun minNewSize :: "'a state \<Rightarrow> nat" where
  "minNewSize (Common state) = Common.minNewSize state"
| "minNewSize (Reverse (Current _ _ _ remained) _ _ _) = remained"


end