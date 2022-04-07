theory Small
  imports Common
begin

datatype (plugins del: size) 'a state =
   Reverse1 "'a current" "'a stack" "'a list"
 | Reverse2 "'a current" "'a list" "'a stack" "'a list" nat
 | Common "'a Common.state"

fun list :: "'a state \<Rightarrow> 'a list" where
  "list (Common common) = Common.list common"
| "list (Reverse2 (Current extra _ _ remained) aux big new count) =
  extra @ reverseN (remained - (count + Stack.size big)) aux (rev (Stack.list big) @ new)"

fun list_current :: "'a state \<Rightarrow> 'a list" where
  "list_current (Common common) = Common.list_current common"
| "list_current (Reverse2 current _ _ _ _) = Current.list current"
| "list_current (Reverse1 current _ _) = Current.list current"

fun step :: "'a state \<Rightarrow> 'a state" where
  "step (Common state) = Common (Common.step state)"
| "step (Reverse1 current small auxS) = (
    if Stack.is_empty small 
    then Reverse1 current small auxS 
    else Reverse1 current (Stack.pop small) ((first small)#auxS)
  )"
| "step (Reverse2 current auxS big newS count) = (
    if Stack.is_empty big
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

instantiation state::(type) emptyable
begin

fun is_empty :: "'a state \<Rightarrow> bool" where
  "is_empty (Common state) = Common.is_empty state"
| "is_empty (Reverse1 current _ _) = Current.is_empty current"
| "is_empty (Reverse2 current _ _ _ _) = Current.is_empty current"

instance..
end

instantiation state::(type) invar
begin

fun invar :: "'a state \<Rightarrow> bool" where
  "invar (Common state) = Common.invar state"
| "invar (Reverse2 current auxS big newS count) = (
   case current of Current _ _ old remained \<Rightarrow>
      remained = count + Stack.size big + Stack.size old
    \<and> remained \<ge> Stack.size old
    \<and> count = List.length newS
    \<and> Current.invar current
    \<and> List.length auxS \<ge> Stack.size old
    \<and> Stack.list old = rev (take (Stack.size old) auxS)
  )"
| "invar (Reverse1 current small auxS) = (
   case current of Current _ _ old remained \<Rightarrow>
      Current.invar current
    \<and> remained \<ge> Stack.size old
    \<and> Stack.size small + List.length auxS \<ge> Stack.size old
    \<and> Stack.list old = rev (take (Stack.size old) (rev (Stack.list small) @ auxS))
  )"

instance..
end

instantiation state::(type) size
begin

fun size :: "'a state \<Rightarrow> nat" where
  "size (Common state) = Common.size state"
| "size (Reverse2 current _ _ _ _) = min (Current.size current) (Current.size_new current)"
| "size (Reverse1 current _ _) = min (Current.size current) (Current.size_new current)"

instance..
end


fun size_new :: "'a state \<Rightarrow> nat" where
  "size_new (Common state) = Common.size_new state"
| "size_new (Reverse2 current _ _ _ _) = Current.size_new current"
| "size_new (Reverse1 current _ _) = Current.size_new current"

(* Just for proof: (Still needed?)*)
fun length :: "'a state \<Rightarrow> nat" where
  "length small = List.length (list small)"

end