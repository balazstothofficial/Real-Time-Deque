theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Idle_Proof Transformation_Proof
begin

fun t_invariant_1' :: "'a transformation \<Rightarrow> bool" where
  "t_invariant_1' (Left left right) = (
  \<exists>n currentL idleL nL currentR idleR nR. 
  nTicks n (Left left right) = 
    Left (Small.state.Common (state.Idle currentL (idle.Idle idleL nL))) 
         (Big.state.Common   (state.Idle currentR (idle.Idle idleR nR)))
  \<and> Small.toList left @ rev (Big.toList right) = Stack.toList idleL @ rev (Stack.toList idleR)
  \<and> Stack.toList idleL @ rev (Stack.toList idleR) = Current.toList currentL @ rev (Current.toList currentR)
  )"
| "t_invariant_1' (Right left right) = True"

fun t_invariant_1 :: "'a transformation \<Rightarrow> bool" where
  "t_invariant_1 (Left left right) = (
    case fourTicks (Left left right) of 
      (Left (Small.state.Common (state.Idle currentL (idle.Idle idleL _))) 
            (Big.state.Common   (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
      Small.toList left @ rev (Big.toList right) = Stack.toList idleL @ rev (Stack.toList idleR) \<and>
      Current.toList currentL @ rev (Current.toList currentR) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True
  )"
| "t_invariant_1 (Right left right) = True"

lemma "t_invariant_1' t \<Longrightarrow> t_invariant_1 t"
  apply(induction t)
   apply(auto split: prod.splits state_splits)
  sorry

fun t_invariant :: "'a transformation \<Rightarrow> bool" where
  "t_invariant (Left left right) = (\<forall>x.
    case fourTicks (Left (push x left) right) of 
      (Left (Small.state.Common (state.Idle currentL (idle.Idle idleL _))) 
            (Big.state.Common   (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
      x # Small.toList left @ rev (Big.toList right) = Stack.toList idleL @ rev (Stack.toList idleR) \<and>
      Current.toList currentL @ rev (Current.toList currentR) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True
  )"
| "t_invariant (Right left right) = True"

lemma "t_invariant_1' t = t_invariant_1' (ticks t)"
  apply(induction t)
   apply(auto split: prod.splits)
  sorry

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
  dequeueLeft,
  dequeueLeft,
  dequeueLeft,
  dequeueLeft,
  dequeueLeft
  ] 
  Empty"

fun invariant :: "'a deque \<Rightarrow> bool" where
  "invariant Empty = True"
| "invariant (One _) = True"
| "invariant (Two _ _) = True"
| "invariant (Three _ _ _) = True"
| "invariant (Idle (idle.Idle left leftLength) (idle.Idle right rightLength)) = (
   Stack.size left = leftLength \<and>
   Stack.size right = rightLength \<and>
   (leftLength \<ge> 2 \<or> rightLength \<ge> 2)
  )"
| "invariant (Transforming (Left left right)) = (\<forall>x.
    case fourTicks (Left (push x left) right) of 
      (Left (Small.state.Common (state.Idle currentL (idle.Idle idleL _))) 
            (Big.state.Common   (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
      x # Small.toList left @ rev (Big.toList right) = Stack.toList idleL @ rev (Stack.toList idleR) \<and>
      Current.toList currentL @ rev (Current.toList currentR) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True
  )"
| "invariant (Transforming (Right left right)) = (\<forall>x.
    case fourTicks (Right (Big.push x left) right) of 
      (Right (Big.state.Common   (state.Idle currentL (idle.Idle idleL _))) 
             (Small.state.Common (state.Idle currentR (idle.Idle idleR _)))) \<Rightarrow>
      x # Big.toList left @ rev (Small.toList right) = Stack.toList idleL @ rev (Stack.toList idleR) \<and>
      Current.toList currentL @ rev (Current.toList currentR) = Stack.toList idleL @ rev (Stack.toList idleR)
    | _ \<Rightarrow> True
  )"

(* TODO: Probably more strict needed! *)
fun isIdle :: "'a transformation \<Rightarrow> bool" where
  "isIdle (
    Left 
      (Small.state.Common (state.Idle currentL (idle.Idle idleL _))) 
      (Big.state.Common   (state.Idle currentR (idle.Idle idleR _)))
    ) = True"
| "isIdle (
    Right
      (Big.state.Common   (state.Idle currentL (idle.Idle idleL _))) 
      (Small.state.Common (state.Idle currentR (idle.Idle idleR _)))
    ) = True"
| "isIdle _ = False"

fun invariant_t :: "'a deque \<Rightarrow> bool" where
  "invariant_t Empty = True"
| "invariant_t (One _) = True"
| "invariant_t (Two _ _) = True"
| "invariant_t (Three _ _ _) = True"
| "invariant_t (Idle (idle.Idle left leftLength) (idle.Idle right rightLength)) = (
   Stack.size left = leftLength \<and>
   Stack.size right = rightLength \<and>
   (leftLength \<ge> 2 \<or> rightLength \<ge> 2)
  )"
| "invariant_t (Transforming transformation) = (
    let ticked = fourTicks transformation in
    let steps = remainingSteps transformation in
    let steps' = remainingSteps ticked in
    steps - steps' = 4 \<or> 
    (steps' = 0 \<and> isIdle ticked)
  )"
                     

lemma ticks_inv: "\<lbrakk>
  invariant_t (Transforming transformation)
\<rbrakk> \<Longrightarrow> invariant_t (Transforming (fourTicks transformation))"
  sorry

value "Left (Reverse1 (Current [] 0 (Stack [] []) 0) (Stack [] []) []) (Reverse (Current [] 0 (Stack [] []) 2) (Stack [a\<^sub>1] [a\<^sub>1]) [] 2)"

value "fourTicks ( (Left (Reverse1 (Current [] 0 (Stack [] []) 0) (Stack [] []) []) (Reverse (Current [] 0 (Stack [] []) 2) (Stack [a\<^sub>1] [a\<^sub>1]) [] 2)))"

value "invariant_t (Transforming (Left (Reverse1 (Current [] 0 (Stack [] []) 0) (Stack [] []) []) (Reverse (Current [] 0 (Stack [] []) 2) (Stack [0::nat] [1]) [] 2)))"

value "invariant_t (Transforming (ticks (Left (Reverse1 (Current [] 0 (Stack [] []) 0) (Stack [] []) []) (Reverse (Current [] 0 (Stack [] []) 2) (Stack [a\<^sub>1] [a\<^sub>1]) [] 2))))"


lemma ticksLength: "Transformation.length t = Transformation.length (ticks t)"
  by (simp add: ticks)

lemma sixTicks_inv: 
  assumes 
    "invariant (Transforming (Right left right))" 
  shows
   "invariant (Transforming (sixTicks (Right left right)))"
  sorry

lemma helper: " \<lbrakk>
  \<not> Suc (Stack.size left) \<le> 3 * Stack.size right;
  leftLength = Stack.size left; 
  rightLength = Stack.size right;
  2 \<le> Stack.size left
\<rbrakk> \<Longrightarrow> 3 * List.length (Stack.toList right) < Suc (List.length (Stack.toList (Stack.push x left)))"
  by (simp add: Stack_Proof.push size_listLength)

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
      case (5 x rightIdle rightLength)
      then show ?case 
        apply (auto simp: Idle_Proof.push Let_def all_ticks ticks_helper split: prod.splits idle.splits)
        (* TODO: *)
        apply (metis Idle.toList.simps Idle_Proof.push)
        by (metis Big.toList.simps(2) Current.toList.simps Idle.toList.simps Idle_Proof.push Small.toList.simps(2) append_Cons append_self_conv2 ticks_help ticks_help2)
    qed
  next
    case (Transforming t x)
    then show ?case 
    proof(induction t)
      case (Left left right)
      then show ?case 
        apply(auto simp: Let_def ticks_help ticks_help2 ticks_helpFUCK split: prod.splits state_splits)
        by fastforce
    next
      case (Right left right)
      then show ?case
        apply(auto simp: Let_def ticks_help ticks_help2 ticks_helpFUCK' split: prod.splits state_splits)
        by fastforce
    qed
  qed
next
case (4 q x)
  then show ?case
    sorry
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
    obtain left' leftLength where "idle.Idle left' leftLength = left"
      apply(induction left)
      by auto
    
    with 5 show ?case 
    proof(induction "3 * rightLength \<ge> (Suc leftLength)")
      case True
      then show ?case
        by(auto simp: Let_def size_push Stack_Proof.size_push split: prod.splits state_splits)
    next
      case False
      let ?newDeque = "enqueueLeft x (deque.Idle left  (idle.Idle right rightLength))"
      let ?pushedLeft = "Stack.push x left'"
      let ?leftStart = "Reverse (Current [] 0 ?pushedLeft (leftLength - rightLength - 1)) ?pushedLeft [] (leftLength - rightLength - 1)"
      let ?rightStart = "Reverse1 (Current [] 0 right (2 * rightLength + 1)) right []"
      let ?transformationStart = "Right ?leftStart ?rightStart"

      let ?newleftLength = "Big.length ?leftStart"
      let ?newRightLength = "Small.length ?rightStart"    

      from False.hyps False.prems have initialLength_same: "3 * ?newRightLength < Suc ?newleftLength"
        by(auto simp: helper)

      with False.prems False.hyps have "invariant (Transforming ?transformationStart)"
        sorry

      with False.prems sixTicks_inv have "invariant (Transforming (sixTicks ?transformationStart))"
        using sixTicks_inv
        by blast
      
      with False show ?case 
        apply(auto simp: Stack_Proof.size_push Let_def size_push split: prod.splits state_splits)
        sorry
    qed
    (*proof(induction left arbitrary: x)
      case (Stack left1 left2)
      then show ?case
      proof(induction right arbitrary: x)
        case (Stack right1 right2)
        let ?newDeque = "enqueueLeft  x (deque.Idle (idle.Idle (Stack left1 left2) leftLength) (idle.Idle (Stack right1 right2) rightLength))"

        have leftLength:  "leftLength = length left1 + length left2"
          using Stack.prems
          by auto
        have rightLength: "rightLength = length right1 + length right2"
          using Stack.prems
          by auto
     
        from Stack.prems show ?case
        proof(induction ?newDeque)
          case Empty
          then show ?case by auto
        next
          case (One a)
          then show ?case
            by(auto simp: Let_def)
        next
          case (Two a b)
          then show ?case
            by(auto simp: Let_def)
        next
          case (Three x1 x2a x3)
          then show ?case 
            by(auto simp: Let_def)
        next
          case (Idle newLeft newRight)
          then show ?case 
            by(auto simp: Let_def)
        next
          case (Transforming transformation)
          then show ?case
          proof(induction transformation)
            case (Left newLeft newRight)
            then show ?case
              by (auto simp: Let_def split: prod.splits)
          next
            case (Right newLeft newRight)
            with Right.prems show ?case
            proof(cases "fourTicks (Right (Big.push x newLeft) newRight)")
              case (Left leftInv rightInv)
              then show ?thesis
                by(auto simp: Let_def split: prod.splits)
            next
              case (Right leftInv rightInv)
              from Right.prems show ?thesis
              proof(induction "Suc (length left1 + length left2) \<le> 3 * length right1 + 3 * length right2")
                case True
                then show ?case by auto
              next
                case False

             
                from False.prems  have "invariant (Transforming (transformation.Right newLeft newRight))"
                  apply(auto simp: Let_def split: prod.splits state_splits)
                  sorry

            
                with False.prems show ?case
                  by auto
              qed       
              qed
             qed 
            qed
          qed
        qed   *)
  next
    case (6 x left right)
    then show ?case sorry
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
    case (Two x1 x2a)
    then show ?case by auto
  next
    case (Three x1 x2a x3)
    then show ?case by auto
  next
    case (Idle x1 x2a)
    then show ?case by auto
  next
    case (Transforming x)
    then show ?case 
    proof(induction x)
      case (Left x1 x2)
      then show ?case by auto
    next
      case (Right x1 x2)
      then show ?case by auto
      qed
  qed
qed

end
