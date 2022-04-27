theory States 
  imports Big Small
begin

datatype direction = Left | Right

datatype 'a states = States direction "'a Big.state" "'a Small.state"

fun step :: "'a states \<Rightarrow> 'a states" where
  "step (States dir (Reverse currentB big auxB 0) (Reverse1 currentS _ auxS)) =
    States dir (Big.step (Reverse currentB big auxB 0)) (Reverse2 currentS auxS big [] 0)"
| "step (States dir left right) = States dir (Big.step left) (Small.step right)"

abbreviation four_steps where
  "four_steps \<equiv> step^^4"

abbreviation six_steps where
  "six_steps \<equiv> step^^6"

fun remaining_steps :: "'a states \<Rightarrow> nat" where
  "remaining_steps (States _ big small) = max 
    (Big.remaining_steps big) 
    (case small of 
       Small.Common common \<Rightarrow> Common.remaining_steps common
     | Reverse2 (Current _ _ _ remaining) _ big _ count \<Rightarrow> (remaining - (count + Stack.size big)) + Stack.size big + 1
     | Reverse1 (Current _ _ _ remaining) _ _ \<Rightarrow>
         case big of
           Reverse currentB big auxB count \<Rightarrow> Stack.size big + (remaining + count - Stack.size big) + 2
    )"

fun lists :: "'a states \<Rightarrow> 'a list * 'a list" where
  "lists (States _ (Reverse currentB big auxB count) (Reverse1 currentS small auxS)) = (
    Big.list (Reverse currentB big auxB count),
    Small.list (Reverse2 currentS (reverseN count (Stack.list small) auxS) ((Stack.pop ^^ count) big) [] 0)
  )"
| "lists (States _ big small) = (Big.list big, Small.list small)"

fun list_small_first :: "'a states \<Rightarrow> 'a list" where
  "list_small_first states = (let (big, small) = lists states in small @ (rev big))"

fun list_big_first :: "'a states \<Rightarrow> 'a list" where
  "list_big_first states = (let (big, small) = lists states in big @ (rev small))"

fun lists_current :: "'a states \<Rightarrow> 'a list * 'a list" where
  "lists_current (States _ big small) = (Big.list_current big, Small.list_current small)"

fun list_current_small_first :: "'a states \<Rightarrow> 'a list" where
  "list_current_small_first states = (let (big, small) = lists_current states in small @ (rev big))"

fun list_current_big_first :: "'a states \<Rightarrow> 'a list" where
  "list_current_big_first states = (let (big, small) = lists_current states in big @ (rev small))"

(* TODO: Steps inbetween probably not necessary *)
fun listL :: "'a states \<Rightarrow> 'a list" where
  "listL (States Left big small)  = list_small_first (States Left big small)"
| "listL (States Right big small) = list_big_first (States Right big small)"

instantiation states::(type) invar
begin

fun invar :: "'a states \<Rightarrow> bool" where
  "invar (States dir big small)  \<longleftrightarrow> (
     Big.invar big 
   \<and> Small.invar small
   \<and> list_small_first (States dir big small) = list_current_small_first (States dir big small)
   \<and> (case (big, small) of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow> 
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | (Reverse _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      ))"

instance..
end

fun size_ok' :: "'a states \<Rightarrow> nat \<Rightarrow> bool" where
  "size_ok' (States _ big small) steps \<longleftrightarrow> 
      Small.size_new small + steps + 2 \<le> 3 * Big.size_new big
    \<and> Big.size_new big + steps + 2 \<le> 3 * Small.size_new small
    \<and> steps + 1 \<le> 4 * Small.size small
    \<and> steps + 1 \<le> 4 * Big.size big
  "

fun size_ok :: "'a states \<Rightarrow> bool" where
  "size_ok states \<longleftrightarrow> size_ok' states (remaining_steps states)"

instantiation states::(type) emptyable
begin

fun is_empty :: "'a states \<Rightarrow> bool" where
  "is_empty (States _ big small) \<longleftrightarrow> Big.is_empty big \<or> Small.is_empty small"

instance..
end

end
