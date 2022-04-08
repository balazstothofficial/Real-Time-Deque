theory Transforming 
  imports States
begin

datatype 'a states =
   Left "'a Small.state" "'a Big.state"
 | Right "'a Big.state" "'a Small.state"

fun listL :: "'a states \<Rightarrow> 'a list" where
  "listL (Left small big)  = States.list_small_first (big, small)"
| "listL (Right big small) = States.list_big_first (big, small)"

fun step :: "'a states \<Rightarrow> 'a states" where
  "step (Left small big) = (case States.step (big, small) of (big, small) \<Rightarrow> Left small big)"
| "step (Right big small) = (case States.step (big, small) of (big, small) \<Rightarrow> Right big small)"  

abbreviation four_steps where
  "four_steps \<equiv> step^^4"

abbreviation six_steps where
  "six_steps \<equiv> step^^6"

instantiation states::(type) invar
begin

fun invar :: "'a states \<Rightarrow> bool" where
  "invar (Left small big)  \<longleftrightarrow> States.invar (big, small)"
| "invar (Right big small) \<longleftrightarrow> States.invar (big, small)"

instance..
end

instantiation states::(type) emptyable
begin

fun is_empty :: "'a states \<Rightarrow> bool" where
  "is_empty (Left small big)  \<longleftrightarrow> States.is_empty (big, small)"
| "is_empty (Right big small) \<longleftrightarrow> States.is_empty (big, small)"

instance..
end

fun remaining_steps where
  "remaining_steps (Left small big) = States.remaining_steps (big, small)"
| "remaining_steps (Right big small) = States.remaining_steps (big, small)"

fun size_ok :: "'a states \<Rightarrow> bool" where
  "size_ok (Left small big) = States.size_ok (big, small)"
| "size_ok (Right big small) = States.size_ok (big, small)"

fun size_ok' :: "'a states \<Rightarrow> nat \<Rightarrow> bool" where
  "size_ok' (Left small big) steps = States.size_ok' (big, small) steps"
| "size_ok' (Right big small) steps = States.size_ok' (big, small) steps"

end