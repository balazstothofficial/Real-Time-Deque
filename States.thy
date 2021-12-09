theory States 
  imports Big Small
begin

type_synonym 'a states = "'a Big.state * 'a Small.state"

fun tick :: "'a states \<Rightarrow> 'a states" where
  "tick (Reverse currentB big auxB 0, Reverse1 currentS _ auxS) =
    (Big.tick (Reverse currentB big auxB 0), Reverse2 currentS auxS big [] 0)"
| "tick (left, right) = (Big.tick left, Small.tick right)"

fun invariant :: "'a states \<Rightarrow> bool" where
  "invariant (big, small) \<longleftrightarrow> 
    Big.invariant big 
  \<and> Small.invariant small
  \<and> (
    case (big, small) of 
      (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow>
           Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
    | _ \<Rightarrow> True
)"

end
