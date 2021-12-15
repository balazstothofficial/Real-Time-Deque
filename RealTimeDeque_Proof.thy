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


lemma terminates: "States.invariant states \<Longrightarrow> isSomeAnd States.invariant (States.terminateTicks states)"
proof(induction states)
  case (Pair big small)
  then have tick: "States.invariant (States.tick (big, small))"
    using States_Proof.invariant_tick by blast

  then show ?case
  proof(induction "States.tick (big, small)")
    case (Pair a b)
    with Pair tick show ?case
      apply(induction a)
      apply auto
      sorry
  qed
qed

fun invariant' :: "'a deque \<Rightarrow> bool" where
  "invariant' Empty = True"
| "invariant' (One _) = True"
| "invariant' (Two _ _) = True"
| "invariant' (Three _ _ _) = True"
| "invariant' (Idle left right) = (
    Idle.invariant left \<and>
    Idle.invariant right \<and>
   (Idle.size left \<ge> 2 \<or> Idle.size right \<ge> 2)
  )"
| "invariant' (Transforming (Left left right)) = (\<forall>x.
    case fourTicks (Left (Small.push x left) right) of 
      (Left (Small.state.Common (state.Idle currentL (idle.Idle idleL _))) 
            (Big.state.Common   (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
       x # Small.toList left @ rev (Big.toList right) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True
  )"
| "invariant' (Transforming (Right left right)) = (\<forall>x.
    case fourTicks (Right (Big.push x left) right) of 
      (Right (Big.state.Common  (state.Idle currentL (idle.Idle idleL _))) 
            (Small.state.Common (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
        x # Big.toList left @ rev (Small.toList right) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True
)"


lemma please: "(
    case fourTicks (Left left right) of 
      (Left (Small.state.Common (state.Idle currentL (idle.Idle idleL _))) 
            (Big.state.Common   (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
        Small.toList left @ rev (Big.toList right) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True
  ) \<Longrightarrow>
    (\<forall>x.
    case fourTicks (Left (Small.push x left) right) of 
      (Left (Small.state.Common (state.Idle currentL (idle.Idle idleL _))) 
            (Big.state.Common   (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
       x # Small.toList left @ rev (Big.toList right) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True
  )"
  sorry

lemma someAnd:
  assumes "isSomeAnd predicate (terminateTicks transformation)"
  shows "\<exists>transformation'. terminateTicks transformation = Some transformation'"
  using assms apply(induction predicate "terminateTicks transformation" rule: isSomeAnd.induct)
  apply auto
  by metis

(*lemma someAnd_2:
  assumes "isSomeAnd predicate (terminateTicks transformation)"
  shows "\<exists>currentL currentR idleL idleR xa xb. terminateTicks transformation = Some (
       Left (Small.state.Common (state.Idle currentL (idle.Idle idleL xa)))
            (Big.state.Common   (state.Idle currentR (idle.Idle idleR xb)))
        )"
using assms proof(induction predicate "terminateTicks transformation" rule: isSomeAnd.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 predicate a)
  then show ?case
  proof(induction a arbitrary: predicate)
    case (Left x1 x2)
    then show ?case
      sorry
  next
    case (Right x1 x2)
    then show ?case sorry
  qed 
qed*)


lemma inv': "invariant deque \<Longrightarrow> invariant' deque"
proof(induction deque)
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
  case (Idle x1 x2a)
  then show ?case by auto
next
  case (Transforming tr)
  then show ?case
  proof(induction tr)
    case (Left small big)

    (*obtain currentL currentR idleL idleR xa xb where termi: "terminateTicks tr = Some (
          Left (Small.state.Common (state.Idle currentL (idle.Idle idleL xa)))
              (Big.state.Common   (state.Idle currentR (idle.Idle idleR xb)))
        )"
      sorry

    have sth: "Small.toList small @ rev (Big.toList big) = Stack.toList idleL @ rev (Stack.toList idleR)"
      sorry

    have "States.invariant (big, small) \<Longrightarrow> isSomeAnd States.invariant (States.terminateTicks (big, small))"
      sorry*)

    then have " case fourTicks (Left small big) of 
      (Left (Small.state.Common (state.Idle currentL (idle.Idle idleL _))) 
            (Big.state.Common   (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
        Small.toList small @ rev (Big.toList big) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True"
      apply(auto split: transformation.split Small.state.split Common.state.split idle.split Big.state.split)   
      sorry

    then show ?case 
      using please by auto
      (*
      apply auto
      subgoal for x
      proof(induction  "fourTicks (Left (Small.push x small) big)")
        case (Left small' big')
        then show ?case
        proof(induction small')
          case (Reverse1 x1 x2 x3a)
          then show ?case 
            by(auto split: transformation.splits)
        next
          case (Reverse2 x1 x2 x3a x4 x5)
          then show ?case
            by(auto split: transformation.splits)
        next
          case (Common smallCommon)
          then show ?case
          proof(induction smallCommon)
            case (Copy x1 x2 x3 x4)
            then show ?case
              by(auto split: transformation.splits)
          next
            case (Idle smallCurrent smallIdle)
            then show ?case
            proof(induction big')
              case (Reverse x1 x2a x3 x4)
              then show ?case 
                by(auto split: transformation.splits idle.splits)
            next
              case (Common bigCommon)
              then show ?case
              proof(induction bigCommon)
                case (Copy x1 x2 x3 x4)
                then show ?case 
                  by(auto split: transformation.splits idle.splits)
              next
                case (Idle bigCurrent bigIdle)
                then show ?case 
                proof(induction smallIdle)
                  case (Idle smallIdle smallIdleLength)
                  then show ?case 
                  proof(induction bigIdle)
                    case (Idle bigIdle bigIdleLength) 

                    let ?isSome = "
                isSomeAnd (\<lambda>t. toListLeft' t = Small.toList small @ rev (Big.toList big))
                  (case if States.invariant (big, small)
                        then case big of
                                   Big.state.Common (state.Idle _ _) \<Rightarrow>
                                        case small of 
                                                 Small.state.Common (state.Idle _ _) \<Rightarrow> Some (big, small) 
                                              | _ \<Rightarrow> States.terminateTicks (States.tick (big, small))
                                | _ \<Rightarrow> States.terminateTicks (States.tick (big, small))
                         else None of 
                              None \<Rightarrow> None 
                            | Some (big, small) \<Rightarrow> Some (transformation.Left small big))"
                    let ?pushedSmall = "Small.push x small"

                    have ?isSome 
                      using Left.prems by blast

                    then have "terminateTicks (Left ?pushedSmall big) = Some(
                              Left (Small.state.Common (state.Idle smallCurrent (idle.Idle smallIdle smallIdleLength))) 
                                   (Big.state.Common   (state.Idle bigCurrent (idle.Idle bigIdle bigIdleLength))))"
                      sorry
                      
                    with Idle have "x # Small.toList small @ rev (Big.toList big) = Stack.toList smallIdle @ rev (Stack.toList bigIdle)"
                      apply auto
                      sorry
  
                    with Idle show ?case
                      by(auto split: transformation.splits)
                  qed
              qed
            qed
          qed
        qed
      qed*)
        (*
          apply(auto simp:  split: transformation.split  Small.state.split Common.state.split idle.split Big.state.split)
          subgoal for x1a x2a x1aa x2aa x1b x2b x21 x1c x21a x1d x2c x2d
          proof -
            from local show ?thesis
              sorry
          qed
          .*)
      next
        case (Right x1 x2)
        then show ?case 
          sorry
          (*by(auto simp: case_prod_unfold fourTicks_def)*)
      qed
    
      
      (*apply(auto simp: fourTicks_def split: prod.split Big.state.split Small.state.split Common.state.split idle.split)
      sorry*)
      (*subgoal for x
        apply(induction x small rule: Small.push.induct; induction big)
        apply(auto split: transformation.split)
        subgoal for x1 x2a x3 x4 x state x11 x12
          apply(auto simp:  split: Small.state.split Common.state.split idle.split Big.state.split)
          sorry
        subgoal for x xa state x11 x12
          apply(auto split: Small.state.split Common.state.split idle.split Big.state.split)
          sorry
    
        sorry
      .*)
  (*next
    case (Right big small)
    then show ?case sorry
  qed *)
qed


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

    then have "invariant' (Transforming (transformation.Left left right))"
      using inv' by blast

    then show ?case
      apply(auto simp: Let_def split: transformation.splits state_splits)
            apply (metis Cons_eq_appendI Small.toList.simps(2) Small_Proof.push fourTicks toListLeft.simps(1))
           apply (metis Cons_eq_appendI Small.toList.simps(3) Small_Proof.push fourTicks toListLeft.simps(1))
      apply (metis Common.toList.simps(2) Cons_eq_appendI Small.toList.simps(1) Small_Proof.push fourTicks toListLeft.simps(1))
      apply (metis Big.toList.simps(2) Common.toList.simps(1) Cons_eq_appendI Small.toList.simps(1) Small_Proof.push fourTicks toListLeft.simps(1))
      apply (metis Big.toList.simps(1) Common.toList.simps(1) Common.toList.simps(2) Cons_eq_appendI Small.toList.simps(1) Small_Proof.push fourTicks toListLeft.simps(1))
       apply (metis Idle.toList.elims)
      by (metis Small_Proof.push append_Cons fourTicks toListLeft.simps(1) toListLeft.simps(2))
  next
    case (7 x left right)
     then have "invariant' (Transforming (transformation.Right left right))"
      using inv' by blast

    then show ?case 
      apply(auto simp: Let_def split: transformation.splits state_splits)
            apply (metis Big_Proof.push append_Cons fourTicks toListLeft.simps(1) toListLeft.simps(2))
           apply (metis Big.toList.simps(2) Big_Proof.push append_Cons fourTicks toListLeft.simps(2))
          apply (metis Big.toList.simps(1) Big_Proof.push Common.toList.simps(2) Cons_eq_appendI fourTicks toListLeft.simps(2))
      apply (metis Big.toList.simps(1) Big_Proof.push Common.toList.simps(1) Cons_eq_appendI Small.toList.simps(2) fourTicks toListLeft.simps(2))
      apply (metis Big.toList.simps(1) Big_Proof.push Common.toList.simps(1) Cons_eq_appendI Small.toList.simps(3) fourTicks toListLeft.simps(2))
      apply (metis Big.toList.simps(1) Big_Proof.push Common.toList.simps(1) Common.toList.simps(2) Cons_eq_appendI Small.toList.simps(1) fourTicks toListLeft.simps(2))
      by (metis Idle.toList.elims)
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
      apply(auto simp: Let_def split: idle.splits)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_push)
         apply (metis Idle.size.simps Idle_Proof.size_push le_Suc_eq)
      
      sorry
  next
    case (6 x left right)
    then show ?case
      apply(auto simp: Let_def split: transformation.split Small.state.split)
      subgoal for x12 x11a x12a x13
        apply(cases x12)
         apply auto
        sorry
      apply (smt (z3) Transformation.invariant.simps(1) invariant_fourTicks invariant_pushSmall isSomeAnd.simps(1) option.simps(4))
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
