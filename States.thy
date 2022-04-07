theory States 
  imports Big Small
begin

type_synonym 'a states = "'a Big.state * 'a Small.state"

fun step :: "'a states \<Rightarrow> 'a states" where
  "step (Reverse currentB big auxB 0, Reverse1 currentS _ auxS) =
    (Big.step (Reverse currentB big auxB 0), Reverse2 currentS auxS big [] 0)"
| "step (left, right) = (Big.step left, Small.step right)"

fun remaining_steps :: "'a states \<Rightarrow> nat" where
  "remaining_steps (big, small) = max 
    (Big.remaining_steps big) 
    (case small of 
       Small.Common common \<Rightarrow> Common.remaining_steps common
     | Reverse2 (Current _ _ _ remaining) _ big _ count \<Rightarrow> (remaining - (count + Stack.size big)) + Stack.size big + 1
     | Reverse1 (Current _ _ _ remaining) _ _ \<Rightarrow>
         case big of
           Reverse currentB big auxB count \<Rightarrow> Stack.size big + (remaining + count - Stack.size big) + 2
    )"

fun lists :: "'a states \<Rightarrow> 'a list * 'a list" where
  "lists (Reverse currentB big auxB count, Reverse1 currentS small auxS) = (
    Big.list (Reverse currentB big auxB count),
    Small.list (Reverse2 currentS (reverseN count (Stack.list small) auxS) ((Stack.pop ^^ count) big) [] 0)
  )"
| "lists (big, small) = (Big.list big, Small.list small)"

fun list_small_first :: "'a states \<Rightarrow> 'a list" where
  "list_small_first states = (let (big, small) = lists states in small @ (rev big))"

fun list_big_first :: "'a states \<Rightarrow> 'a list" where
  "list_big_first states = (let (big, small) = lists states in big @ (rev small))"

fun lists_current :: "'a states \<Rightarrow> 'a list * 'a list" where
  "lists_current (big, small) = (Big.list_current big, Small.list_current small)"

fun list_current_small_first :: "'a states \<Rightarrow> 'a list" where
  "list_current_small_first states = (let (big, small) = lists_current states in small @ (rev big))"

fun list_current_big_first :: "'a states \<Rightarrow> 'a list" where
  "list_current_big_first states = (let (big, small) = lists_current states in big @ (rev small))"

fun invar :: "'a states \<Rightarrow> bool" where
  "invar states \<longleftrightarrow> (
    let (big, small) = states in
     Big.invar big 
   \<and> Small.invar small
   \<and> list_small_first states = list_current_small_first states
   \<and> (case states of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow> 
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | (Reverse _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      ))"

fun size_ok' :: "'a states \<Rightarrow> nat \<Rightarrow> bool" where
  "size_ok' (big, small) steps \<longleftrightarrow> 
      Small.size_new small + steps + 2 \<le> 3 * Big.size_new big
    \<and> Big.size_new big + steps + 2 \<le> 3 * Small.size_new small
    \<and> steps + 1 \<le> 4 * Small.size small
    \<and> steps + 1 \<le> 4 * Big.size big
  "

fun size_ok :: "'a states \<Rightarrow> bool" where
  "size_ok states \<longleftrightarrow> size_ok' states (remaining_steps states)"

fun is_empty :: "'a states \<Rightarrow> bool" where
  "is_empty (big, small) \<longleftrightarrow> Big.is_empty big \<or> Small.is_empty small"
                                                    
end
