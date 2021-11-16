theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Transformation_Proof 
begin

(* TODO: Stricter invariant!
lemma please_1: "\<lbrakk>RealTimeDeque.invariant (Transforming (transformation.Left left right));
      ticksHelper (right, left) =  (Big.state.Common (state.Idle x21a (idle.Idle x1d x2d)), Small.state.Common (state.Idle x21 (idle.Idle x1c x2c)))\<rbrakk>
       \<Longrightarrow> Stack.toList x1c @ rev (Stack.toList x1d) = Small.toList left @ rev (Current.toList x21a)"
  apply(induction "Transforming (transformation.Left left right)" rule: RealTimeDeque.invariant.induct)
  apply(auto split: if_splits current.splits)
  sorry


lemma please: "\<lbrakk>RealTimeDeque.invariant (Transforming (transformation.Left left right));
        ticksHelper (x1b, x2b) = (Big.state.Common (state.Idle x21a (idle.Idle x1d x2d)), Small.state.Common (state.Idle x21 (idle.Idle x1c x2c)));
        ticksHelper (x1a, x2a) = (x1b, x2b); ticksHelper (x1, x2) = (x1a, x2a); ticksHelper (right, left) = (x1, x2)\<rbrakk>
       \<Longrightarrow> Stack.toList x1c @ rev (Stack.toList x1d) = Small.toList left @ rev (Current.toList x21a)"
  apply(induction "(right, left)" rule: ticksHelper.induct)
  apply(auto split: current.splits)
  sorry *)

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
        by (auto simp: Stack_Proof.push Let_def all_ticks ticks_helper split: prod.splits)
    qed
  next
    case (Transforming t x)
    then show ?case 
    proof(induction t arbitrary: x)
      case (Left left right)
      then show ?case 
        apply(auto simp: Let_def ticks_help ticks_help2 small_push
                  split: prod.splits Small.state.splits state_splits)
        sorry
    next
      case (Right left right)
      then show ?case
         apply(auto simp: Let_def ticks_help ticks_help2 split: prod.splits state_splits)
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
