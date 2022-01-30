theory States 
  imports Big Small
begin

type_synonym 'a states = "'a Big.state * 'a Small.state"

fun tick :: "'a states \<Rightarrow> 'a states" where
  "tick (Reverse currentB big auxB 0, Reverse1 currentS _ auxS) =
    (Big.tick (Reverse currentB big auxB 0), Reverse2 currentS auxS big [] 0)"
| "tick (left, right) = (Big.tick left, Small.tick right)"

fun remainingSteps :: "'a states \<Rightarrow> nat" where
  "remainingSteps (big, small) = max 
    (Big.remainingSteps big) 
    (case small of 
       Small.Common common \<Rightarrow> Common.remainingSteps common
     | Reverse2 (Current _ _ _ remaining) _ big _ count \<Rightarrow> (remaining - (count + Stack.size big)) + Stack.size big + 1
     | Reverse1 (Current _ _ _ remaining) _ _ \<Rightarrow>
         case big of
           Reverse currentB big auxB count \<Rightarrow> Stack.size big + (remaining + count - Stack.size big) + 2
    )"

fun toList :: "'a states \<Rightarrow> 'a list * 'a list" where
  "toList (Reverse currentB big auxB count, Reverse1 currentS small auxS) = (
    Big.toList (Reverse currentB big auxB count),
    Small.toList (Reverse2 currentS (reverseN count (Stack.toList small) auxS) ((Stack.pop ^^ count) big) [] 0)
  )"
| "toList (big, small) = (Big.toList big, Small.toList small)"

fun toListSmallFirst :: "'a states \<Rightarrow> 'a list" where
  "toListSmallFirst states = (let (big, small) = toList states in small @ (rev big))"

fun toListBigFirst :: "'a states \<Rightarrow> 'a list" where
  "toListBigFirst states = (let (big, small) = toList states in big @ (rev small))"

fun toCurrentList :: "'a states \<Rightarrow> 'a list * 'a list" where
  "toCurrentList (big, small) = (Big.toCurrentList big, Small.toCurrentList small)"

fun toCurrentListSmallFirst :: "'a states \<Rightarrow> 'a list" where
  "toCurrentListSmallFirst states = (let (big, small) = toCurrentList states in small @ (rev big))"

fun toCurrentListBigFirst :: "'a states \<Rightarrow> 'a list" where
  "toCurrentListBigFirst states = (let (big, small) = toCurrentList states in big @ (rev small))"

fun invariant :: "'a states \<Rightarrow> bool" where
  "invariant states \<longleftrightarrow> (
    let (big, small) = states in
     Big.invariant big 
   \<and> Small.invariant small
   \<and> toListSmallFirst states = toCurrentListSmallFirst states
   \<and> (case states of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow> 
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | (Reverse _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      ))"

fun inSizeWindow' :: "'a states \<Rightarrow> nat \<Rightarrow> bool" where
  "inSizeWindow' (big, small) steps \<longleftrightarrow> 
      4 * Small.newSize small + steps \<le> 12 * Big.newSize big
    \<and> 4 * Big.newSize big + steps \<le> 12 * Small.newSize small
    \<and> steps \<le> 4 * Small.size small
    \<and> steps \<le> 4 * Big.size big
  "

fun inSizeWindow :: "'a states \<Rightarrow> bool" where
  "inSizeWindow states \<longleftrightarrow> inSizeWindow' states (remainingSteps states)"

fun isEmpty :: "'a states \<Rightarrow> bool" where
  "isEmpty (big, small) \<longleftrightarrow> Big.isEmpty big \<or> Small.isEmpty small"
                                                    
end
