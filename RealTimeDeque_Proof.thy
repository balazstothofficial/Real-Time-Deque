theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Transformation_Proof 
begin

interpretation RealTimeDeque: Deque where
  empty    = empty    and
  enqueueLeft = enqueueLeft and
  enqueueRight = enqueueRight and
  firstLeft = firstLeft and
  firstRight = firstRight and
  dequeueLeft = dequeueLeft and
  dequeueRight = dequeueRight and
  isEmpty = isEmpty and
  listLeft = listLeft and
  listRight = listRight and
  invariant = invariant
proof (standard, goal_cases)
  case 1
  then show ?case by (simp add: empty_def)
next
  case 2
  then show ?case by (simp add: empty_def)
next
  case (3 q x)
  then show ?case
  proof(induction q arbitrary: x)
    case Empty
    then show ?case by auto
  next
    case (One x)
    then show ?case by auto
  next
    case (Two x1 x2a)
    then show ?case by auto
  next
    case (Three x1 x2a x3)
    then show ?case by auto
  next
    case (Idle left right)
    then show ?case
    proof(induction x "Idle left right" rule: enqueueLeft.induct)
      case (5 x left leftLength right rightLength)
      then show ?case 
        by (auto simp: push Let_def all_ticks split: prod.splits)
    qed
  next
    case (Transforming t x)
    then show ?case 
    proof(induction t arbitrary: x)
      case (Left left right)
      then show ?case 
        apply(auto simp: Let_def split: prod.splits state_splits)
        sorry
    next
      case (Right left right)
      then show ?case
         apply(auto simp: Let_def split: prod.splits state_splits)
        sorry
    qed
  qed
next
case (4 q x)
  then show ?case  sorry
next
  case (5 q)
  then show ?case sorry
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
  then show ?case sorry
next
  case (10 q)
  then show ?case sorry
next
  case 11
  then show ?case sorry
next
  case (12 q x)
  then show ?case sorry
next
  case (13 q x)
  then show ?case sorry
next
  case (14 q)
  then show ?case sorry
next
  case (15 q)
  then show ?case sorry
qed

end
