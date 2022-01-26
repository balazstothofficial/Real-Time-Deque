theory Small
  imports Common
begin

datatype 'a state =
   Reverse1 "'a current" "'a stack" "'a list"
 | Reverse2 "'a current" "'a list" "'a stack" "'a list" nat
 | Common "'a Common.state"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Common common) = Common.toList common"
| "toList (Reverse2 (Current extra _ _ remained) aux big new count) =
  extra @ revN (remained - (count + Stack.size big)) aux (rev (Stack.toList big) @ new)
"

fun toCurrentList :: "'a state \<Rightarrow> 'a list" where
  "toCurrentList (Common common) = Common.toCurrentList common"
| "toCurrentList (Reverse2 current _ _ _ _) = Current.toList current"
| "toCurrentList (Reverse1 current _ _) = Current.toList current"

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
 
(* Just for proof: *)
fun length :: "'a state \<Rightarrow> nat" where
  "length small = List.length (toList small)"

fun isEmpty :: "'a state \<Rightarrow> bool" where
  "isEmpty (Common state) = Common.isEmpty state"
| "isEmpty (Reverse1 current _ _) = Current.isEmpty current"
| "isEmpty (Reverse2 current _ _ _ _) = Current.isEmpty current"


fun invariant :: "'a state \<Rightarrow> bool" where
  "invariant (Common state) = Common.invariant state"
| "invariant (Reverse2 current auxS big newS count) = (
   case current of Current _ _ old remained \<Rightarrow>
      remained = count + Stack.size big + Stack.size old
    \<and> remained \<ge> Stack.size old
    \<and> count = List.length newS
    \<and> Current.invariant current
    \<and> List.length auxS \<ge> Stack.size old
    \<and> Stack.toList old = rev (take (Stack.size old) auxS)
  )"
| "invariant (Reverse1 current small auxS) = (
   case current of Current _ _ old remained \<Rightarrow>
      Current.invariant current
    \<and> remained \<ge> Stack.size old
    \<and> Stack.size small + List.length auxS \<ge> Stack.size old
    \<and> Stack.toList old = rev (take (Stack.size old) (rev (Stack.toList small) @ auxS))
  )"

fun size :: "'a state \<Rightarrow> nat" where
  "size (Common state) = Common.size state"
| "size (Reverse2 current _ _ _ _) = Current.size current"
| "size (Reverse1 current _ _) = Current.size current"

fun newSize :: "'a state \<Rightarrow> nat" where
  "newSize (Common state) = Common.newSize state"
| "newSize (Reverse2 current _ _ _ _) = Current.newSize current"
| "newSize (Reverse1 current _ _) = Current.newSize current"

end