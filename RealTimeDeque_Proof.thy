theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Transformation_Proof
begin

fun runningFold :: "('a deque \<Rightarrow> 'a deque) list \<Rightarrow> 'a deque \<Rightarrow> 'a deque list" where
  "runningFold [] _ = []"
| "runningFold (x#xs) deque = (
  let deque = x deque 
  in deque # runningFold xs deque
)"

value "runningFold 
  [
  enqueueLeft (0::int), 
  enqueueLeft 1, 
  enqueueLeft 2,
  enqueueLeft 3,
  enqueueLeft 4,
  enqueueLeft 5,
  enqueueLeft 6,
  enqueueLeft 7,
  enqueueLeft 8,
  enqueueLeft 9,
  enqueueLeft 10,
  enqueueLeft 11,
  enqueueLeft 12,
  enqueueLeft 13,
  enqueueLeft 14,
  enqueueLeft 15,
  enqueueLeft 16,
  enqueueLeft 17,
  enqueueLeft 18,
  enqueueLeft 19,
  enqueueLeft 20,
  enqueueLeft 21,
  enqueueLeft 22,
  enqueueLeft 23,
  enqueueLeft 24,
  enqueueLeft 25
  ] 
  Empty"

lemma testing: "
  invariant ( Transforming (
      Left 
      (Small.state.Common (state.Idle currentS (idle.Idle left leftLength)))
      (Big.state.Common   (state.Idle currentB (idle.Idle right rightLength))
      )
    )) \<Longrightarrow>
  listLeft (
    Transforming (
      Left 
      (Small.state.Common (state.Idle currentS (idle.Idle left leftLength)))
      (Big.state.Common   (state.Idle currentB (idle.Idle right rightLength))
      )
    )
  )
    = 
  listLeft (Idle (idle.Idle left leftLength) (idle.Idle right rightLength))"
  sorry


interpretation RealTimeDeque: Deque where
  empty        = empty        and
  enqueueLeft  = enqueueLeft  and
  enqueueRight = enqueueRight and
  firstLeft    = firstLeft    and
  firstRight   = firstRight   and
  dequeueLeft  = dequeueLeft  and
  dequeueRight = dequeueRight and
  isEmpty      = isEmpty      and
  listLeft     = listLeft     and
  listRight    = listRight    and
  invariant    = invariant
proof (standard, goal_cases)
  case 1
  then show ?case by (simp add: empty_def)
next
  case 2
  then show ?case by (simp add: empty_def)
next
  case (3 q x)
  then show ?case
  proof(induction x q rule: enqueueLeft.induct)
    case (1 x)
    then show ?case by auto
  next
    case (2 x y)
    then show ?case by auto
  next
    case (3 x y z)
    then show ?case by auto
  next
    case (4 x a b c)
    then show ?case by auto
  next
    case (5 x left right rightLength)
    then show ?case 
      apply(auto simp: Let_def  split: idle.splits prod.splits)
         apply (metis Idle.toList.simps Idle_Proof.push)
        apply(auto simp: sixTicks_def split: prod.splits)
      apply (metis Big.toList.simps(2) Current.toList.simps Idle.toList.simps Idle_Proof.push Small.toList.simps(2) append_Cons append_Nil tick_toListBig tick_toListSmall)
       apply (metis Idle.toList.simps Idle_Proof.push)
      by (metis Big.toList.simps(2) Current.toList.simps Idle.toList.simps Idle_Proof.push Small.toList.simps(2) append_Cons append_Nil tick_toListBig tick_toListSmall)
  next
    case (6 x left right)
  
    then have "listLeft
      (case fourTicks (transformation.Left (Small.push x left) right) of
            Left (Small.state.Common (state.Idle _ left))
                 (Big.state.Common (state.Idle _ right)) \<Rightarrow>
               Idle left right
            | _ \<Rightarrow> Transforming (fourTicks (transformation.Left (Small.push x left) right))) =
         x # Small.toList left @ rev (Big.toList right)"
      apply(auto)
      sorry

    then have "listLeft (enqueueLeft x (Transforming (transformation.Left left right))) 
          = x # Small.toList left @ rev (Big.toList right)"
      by(auto simp: Let_def)

    then show ?case
      by auto
  next
    case (7 x left right)
    then show ?case 
      sorry
  qed
next
  case (4 q x)
  then show ?case
    sorry
next
  case (5 q)
  then show ?case  sorry
next
  case (6 q)
  then show ?case sorry
next
  case (7 q)
  then show ?case sorry
next
  case (8 q)
  then show ?case sorry
next
  case (9 q)
  then show ?case 
    sorry
next
  case (10 q)
  then show ?case sorry
next
  case 11
  then show ?case 
    by (simp add: RealTimeDeque.empty_def)
next
  case (12 q x)
  then show ?case
  proof(induction x q rule: enqueueLeft.induct)
  case (1 x)
    then show ?case by auto
  next
    case (2 x y)
    then show ?case by auto
  next
    case (3 x y z)
    then show ?case by auto
  next
    case (4 x a b c)
    then show ?case by auto 
  next
    case (5 x left right rightLength)
    then show ?case 
      apply(auto )
      sorry
  next
    case (6 x left right)
    then show ?case
      apply(auto simp: Let_def split: transformation.splits state_splits)
      sorry
  next
    case (7 x left right)
    then show ?case sorry
  qed
next
  case (13 q x)
  then show ?case sorry
next
  case (14 q)
  then show ?case sorry
next
  case (15 q)
  then show ?case sorry
next 
  case (16 q)
  then show ?case
  proof(induction q)
    case Empty
    then show ?case by auto
  next
    case (One x)
    then show ?case by auto
  next
    case (Two x y)
    then show ?case by auto
  next
    case (Three x y z)
    then show ?case by auto
  next
    case (Idle left right)
    then show ?case by auto
  next
    case (Transforming transformation)
    then show ?case 
    proof(induction transformation)
      case (Left small big)
      then show ?case by auto
    next
      case (Right big small)
      then show ?case by auto
      qed
  qed
qed

end
