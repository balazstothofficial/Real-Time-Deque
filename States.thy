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
  "toList (Big.state.Common (Idle _ bigIdle), Small.state.Common (Idle _ smallIdle)) = (Idle.toList bigIdle, Idle.toList smallIdle)"


fun endInvariant :: "'a states \<Rightarrow> bool" where
  "endInvariant states \<longleftrightarrow> (\<exists> bigCurrent smallCurrent bigIdle smallIdle.
      (tick ^^ remainingSteps states) states = (
         Big.state.Common   (Idle bigCurrent  bigIdle),
         Small.state.Common (Idle smallCurrent smallIdle)
        ) \<and>  Current.toList smallCurrent @ rev (Current.toList bigCurrent) 
             = Idle.toList smallIdle @ rev (Idle.toList bigIdle)
      )"

definition invariant :: "'a states \<Rightarrow> bool" where
  "invariant states \<longleftrightarrow> (
    let (big, small) = states in
      Big.invariant big 
   \<and>  Small.invariant small
   \<and> (
      case states of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow>
             Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | _ \<Rightarrow> True
    )
   \<and> endInvariant states
  )"

end
