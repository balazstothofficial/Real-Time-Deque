theory Small
  imports Common
begin

datatype 'a state =
   Reverse1 "'a current" "'a stack" "'a list"
 | Reverse2 "'a current" "'a list" "'a stack" "'a list" nat
 | Common "'a Common.state"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Common common) = Common.toList common"
| "toList (Reverse1 current _ _ ) = Current.toList current"
| "toList (Reverse2 current _ _ _ _) = Current.toList current"

fun tick :: "'a state \<Rightarrow> 'a state" where
  "tick (Common state) = Common (Common.tick state)"
| "tick (Reverse1 current small auxS) = (
    if Stack.isEmpty small 
    then Reverse1 current small auxS 
    else Reverse1 current (Stack.pop small) ((first small)#auxS)
  )"
| "tick (Reverse2 current auxS big newS count) = (
    if Stack.isEmpty big
    then Common (normalize (Copy current auxS newS count))
    else Reverse2 current auxS (Stack.pop big) ((first big)#newS) (count + 1)
  )"

value "tick (Reverse2 (Current [] 0 (Stack [] [a\<^sub>1]) 1) [a\<^sub>1] (Stack [] []) [a\<^sub>2] 1)"

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Common state) = Common (Common.push x state)"
| "push x (Reverse1 current small auxS) = Reverse1 (put x current) small auxS"
| "push x (Reverse2 current auxS big newS count) = Reverse2 (put x current) auxS big newS count"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Common state) = (
    let (x, state) = Common.pop state 
    in (x, Common state)
  )"
| "pop (Reverse1 current small auxS) = 
    (top current, Reverse1 (bottom current) small auxS)"
| "pop (Reverse2 current auxS big newS count) = 
    (top current, Reverse2 (bottom current) auxS big newS count)"

(* Just for proof *)
fun length :: "'a state \<Rightarrow> nat" where
  "length small = List.length (toList small)"

fun isEmpty :: "'a state \<Rightarrow> bool" where
  "isEmpty (Common state) = Common.isEmpty state"
| "isEmpty (Reverse1 current _ _) = Current.isEmpty current"
| "isEmpty (Reverse2 current _ _ _ _) = Current.isEmpty current"

(* TODO: *)
fun invariant :: "'a state \<Rightarrow> bool" where
  "invariant (Common state) = Common.invariant state"
| "invariant (Reverse1 current small auxS) = (
   case current of Current _ _ old remained \<Rightarrow>
   let smallSize = Stack.size small in
      drop (remained - smallSize) (Stack.toList old) = drop (smallSize - remained) (Stack.toList small)
    \<and> Stack.toList old = drop ((List.length auxS + smallSize) - remained) (rev auxS @ Stack.toList small)
    \<and> Current.invariant current
  )"
| "invariant (Reverse2 current auxS big newS count) = (
   case current of Current _ _ old remained \<Rightarrow>
       Stack.toList old = drop (List.length auxS - remained) (rev auxS)
    \<and> remained > Stack.size old
    \<and> remained \<ge> count + Stack.size big
    \<and> remained \<le> List.length auxS + count + Stack.size big
    \<and> count + Stack.size big > Stack.size old
    \<and> count = List.length newS
    \<and> Current.invariant current
)"

(* 

fun invariant :: "'a state \<Rightarrow> bool" where
  "invariant (Common state) \<longleftrightarrow> Common.invariant state"
| "invariant (Reverse current big auxB count) \<longleftrightarrow> (
   case current of Current extra added old remained \<Rightarrow>
       Stack.toList old = drop ((List.length auxB + count) - remained) (rev auxB @ (take count (Stack.toList big)))
    \<and> Current.invariant current
    \<and> List.length auxB \<ge> remained - count
    \<and> remained \<ge> count
    \<and> count \<le> Stack.size big
)"

*)

fun pop_invariant :: "'a state \<Rightarrow> bool" where
  "pop_invariant (Common state) = True"
| "pop_invariant (Reverse1 current _ _) \<longleftrightarrow> True"
| "pop_invariant (Reverse2 (Current _ _ _ remained) _ _ _ count) \<longleftrightarrow> remained > count"

fun remainingSteps :: "'a state \<Rightarrow> nat" where
  "remainingSteps (Common state) = Common.remainingSteps state"
| "remainingSteps (Reverse1 _ small _) = Stack.size small"
| "remainingSteps (Reverse2 _ _ big _ _) = Stack.size big"

end