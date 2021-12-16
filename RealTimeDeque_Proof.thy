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
      apply (metis Big.toList.simps(2) Current.toList.simps Idle.toList.simps Idle_Proof.push Small.toList.simps(2) append_Cons append_Nil nTicks toListLeft.simps(2))
       apply (metis Idle.toList.simps Idle_Proof.push)
      by (metis Big.toList.simps(2) Current.toList.simps Idle.toList.simps Idle_Proof.push Small.toList.simps(2) append_Cons append_Nil nTicks toListLeft.simps(2))
  next
    case (6 x left right)

    then show ?case
      apply(auto simp: Let_def split: transformation.splits)
      subgoal for x11 x12
        apply(auto split: Small.state.splits Big.state.splits Common.state.splits)
        apply (metis Small.toList.simps(2) Small_Proof.push append_Cons fourTicks toListLeft.simps(1))
        apply (metis Small.toList.simps(3) Small_Proof.push append_Cons fourTicks toListLeft.simps(1))
        apply (metis Common.toList.simps(2) Small.toList.simps(1) Small_Proof.push append_Cons fourTicks toListLeft.simps(1))
        apply (metis Big.toList.simps(2) Common.toList.simps(1) Cons_eq_appendI Small.toList.simps(1) Small_Proof.push fourTicks toListLeft.simps(1))
         apply (metis Big.toList.simps(1) Common.toList.simps(1) Common.toList.simps(2) Small.toList.simps(1) Small_Proof.push append_Cons fourTicks toListLeft.simps(1))
        apply(auto simp: Let_def fourTicks_def invariant_def split: state_splits current.splits)
        sorry
      by (metis Small_Proof.push append_Cons fourTicks toListLeft.simps(1) toListLeft.simps(2))
  next
    case (7 x left right)

    then show ?case 
      apply(auto simp: Let_def split: transformation.splits)
      apply (metis Big_Proof.push Cons_eq_appendI fourTicks toListLeft.simps(1) toListLeft.simps(2))
      apply(auto split: state_splits current.splits)
      apply (metis Big.toList.simps(2) Big_Proof.push append_Cons fourTicks toListLeft.simps(2))
      apply (metis Big.toList.simps(1) Big_Proof.push Common.toList.simps(2) append_Cons fourTicks toListLeft.simps(2))
      apply (metis Big.toList.simps(1) Big_Proof.push Common.toList.simps(1) Small.toList.simps(2) append_Cons fourTicks toListLeft.simps(2))
      apply (metis Big.toList.simps(1) Big_Proof.push Common.toList.simps(1) Cons_eq_appendI Small.toList.simps(3) fourTicks toListLeft.simps(2))
      apply (metis Big.toList.simps(1) Big_Proof.push Common.toList.simps(1) Common.toList.simps(2) Cons_eq_appendI Small.toList.simps(1) fourTicks toListLeft.simps(2))
      apply(auto simp: Let_def invariant_def fourTicks_def split: state_splits current.splits)
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
      apply(auto simp: Let_def sixTicks_def split: idle.splits)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_push)
         apply (metis Idle.size.simps Idle_Proof.size_push le_Suc_eq)
      subgoal sorry
      apply (metis Idle.invariant.simps Idle_Proof.invariant_push)
      sorry
  next
    case (6 x left right)
    then show ?case
      apply(auto simp: Let_def split: transformation.split state_splits)
      apply (metis Transformation.invariant.simps(1) invariant_fourTicks invariant_pushSmall)+
      subgoal sorry
      subgoal sorry
      subgoal sorry
      by (metis Transformation.invariant.simps(1) Transformation.invariant.simps(2) invariant_fourTicks invariant_pushSmall)
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
