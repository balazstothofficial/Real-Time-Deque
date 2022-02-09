theory RealTimeDeque_Enqueue
  imports Deque RealTimeDeque Transformation_Proof
begin

lemma helper: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> Stack.size right - (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left)) = 0"
proof -
  assume a1: "Idle.invariant left'"
  assume a2: "rightLength = Stack.size right"
  assume "idle.Idle left leftLength = Idle.push x left'"
  then have f3: "\<And>n. List.length (drop n (Stack.toList left)) = leftLength - n"
    using a1 by (metis (no_types) Idle.invariant.simps Idle_Proof.invariant_push length_drop Stack_Proof.size_listLength)
  moreover
  { assume "\<exists>n. rightLength + (rightLength + 1) - leftLength = rightLength + n"
    moreover
    { assume "\<exists>n. rightLength + (rightLength + 1) - (leftLength - (leftLength - (rightLength + 1))) = rightLength + n"
      then have "rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.toList left))) = 0"
        using f3 diff_is_0_eq nat_le_iff_add by presburger }
    ultimately have "leftLength \<le> rightLength + 1 \<longrightarrow> rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.toList left))) = 0"
      using diff_zero by fastforce }
  ultimately show ?thesis
    using a2
    by (metis (no_types, lifting) Nat.add_diff_assoc One_nat_def popN_drop add_Suc_right add_diff_cancel_left' diff_cancel2 diff_diff_cancel linear mult_2 plus_1_eq_Suc Stack_Proof.size_listLength)
qed

lemma list_enqueueLeft: "invariant deque \<Longrightarrow> listLeft (enqueueLeft x deque) = x # listLeft deque"
proof(induction x deque rule: enqueueLeft.induct)
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
  case (5 x left' right rightLength)
  then show ?case 
  proof(induction "Idle.push x left'")
    case (Idle left leftLength)
    then show ?case 
    proof(induction "3 * rightLength \<ge> leftLength")
      case True
      then show ?case
        apply(auto split: idle.splits)
        by (metis Idle.toList.simps Idle_Proof.push_toList)+
    next
      case False
      let ?transformation = "(Right 
          (Reverse (Current [] 0 left (leftLength - Suc (Stack.size right))) left [] (leftLength - Suc (Stack.size right)))
          (Reverse1 (Current [] 0 right (Suc (2 * Stack.size right))) right []))"

      from False have leftNotEmpty: "\<not> Stack.isEmpty left"
      proof(induction x left' rule: Idle.push.induct)
        case (1 x stack stackSize)
        then show ?case
          apply(induction x stack rule: Stack.push.induct)
          by auto
      qed

      from False have invariant: "Transformation.invariant ?transformation"
        apply(auto)
        apply(auto simp: reverseN_take popN_drop leftNotEmpty)
        apply (metis Idle.invariant.simps Idle_Proof.invariant_push diff_le_self)
        apply (simp add: Stack_Proof.size_listLength)+
        apply (smt (verit) popN_drop append_take_drop_id diff_is_0_eq helper leftNotEmpty length_rev rev_append rev_rev_ident Stack_Proof.size_listLength take_all_iff)
        by (metis Idle.invariant.simps Idle_Proof.invariant_push add_Suc_right diff_add_inverse)
     
      then have "toListLeft ?transformation = x # Idle.toList left' @ rev (Stack.toList right)"
        apply(auto simp: reverseN_take)
        by (metis (no_types, lifting) Idle.hyps Idle.toList.simps Idle_Proof.push_toList append_Cons append_assoc rev_append rev_swap)

      with invariant have 
         "toListLeft (sixTicks ?transformation) = x # Idle.toList left' @ rev (Stack.toList right)"
        by (auto simp: sixTicks)

      with False show ?case
        by(auto simp: Let_def split: idle.splits)
    qed
  qed
next
  case (6 x left right)
  let ?newLeft = "Small.push x left"
  let ?newTransfomation = "Left ?newLeft right"
  let ?tickedTransformation = "fourTicks ?newTransfomation"

  from 6 have invariant: "Transformation.invariant ?newTransfomation"
    by (meson RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) invariant_push_small)

  then have toList: "toListLeft ?newTransfomation = x # Small.toCurrentList left @ rev (Big.toCurrentList right)"
    by(auto simp: push_small push_toCurrentList)
                        
  from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
    using invariant_fourTicks by blast

  then have "toListLeft ?tickedTransformation = x # Small.toCurrentList left @ rev (Big.toCurrentList right)"
    using Transformation_Proof.fourTicks invariant toList by fastforce

  with 6 show ?case
    by(auto simp: Let_def split: transformation.splits state_splits)
next
  case (7 x left right)

  let ?newLeft = "Big.push x left"
  let ?newTransfomation = "Right ?newLeft right"
  let ?tickedTransformation = "fourTicks ?newTransfomation"

  from 7 have invariant: "Transformation.invariant ?newTransfomation"
    by (meson RealTimeDeque.invariant.simps Transformation.invariant.simps invariant_push_big)

  then have toListRight: "toListRight ?newTransfomation = Small.toCurrentList right @ rev (Big.toCurrentList (Big.push x left))"
    by auto

  with invariant have toListLeft: "toListLeft ?newTransfomation = x # Big.toCurrentList left @ rev (Small.toCurrentList right)"
    apply(auto simp: push_big split: prod.splits)
    by (metis Big_Proof.push_toCurrentList append_Cons rev_append rev_rev_ident)
  
  from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
    using invariant_fourTicks by blast

  then have "toListLeft ?tickedTransformation = x # Big.toCurrentList left @ rev (Small.toCurrentList right)"
    using Transformation_Proof.fourTicks invariant toListLeft by fastforce


  with 7 show ?case 
    apply(auto simp: Let_def split: transformation.split prod.split Big.state.split Common.state.split Small.state.split)
    by (metis rev_append rev_rev_ident)+
qed


lemma helper2: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> Suc (List.length (Stack.toList right) + Stack.size right) - leftLength = 0"
  by(auto simp: size_listLength)

lemma helper3: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> rev (
            take 
               (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
               (rev (
                      take (leftLength - Suc (Stack.size right)) (Stack.toList right))
                    )
               ) =
         Stack.toList right"
  by(auto simp: rev_take helper2 size_listLength[symmetric] helper)

lemma helper4: "\<lbrakk>
  \<not> leftLength \<le> 3 * Stack.size right; 
  idle.Idle left leftLength = Idle.push x left'; 
  Idle.invariant left'; rightLength = Stack.size right;
  \<not> Idle.isEmpty left'; 
  \<not> Stack.isEmpty right;
   \<not> Stack.isEmpty left
\<rbrakk> \<Longrightarrow> reverseN (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
          (reverseN (leftLength - Suc (Stack.size right)) (Stack.toList right) [])
          (rev (Stack.toList ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))) @
         rev (take (leftLength - Suc (Stack.size right)) (Stack.toList left)) =
         Stack.toList right @ rev (Stack.toList left)"
  by (metis (no_types, lifting) popN_drop append_Nil2 append_assoc append_take_drop_id helper3 rev_append reverseN_take)

lemma calculation_helper: "\<lbrakk>
          \<not> l \<le> 3 * r; 
          Suc l' = l;
          0 < l;
          0 < l';
          0 < r;
          l' \<le> 3 * r;
          l + l - Suc (Suc (r + r)) \<le> Suc (l + r)
       \<rbrakk> \<Longrightarrow> Suc (l + r - 4) \<le> 4 * r"
  by auto

lemma inSizeWindowStates_inSizeWindowLeft: "States.inSizeWindow ((States.tick ^^ n) (big, small)) \<Longrightarrow> inSizeWindow ((tick ^^ n) (Left small big))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma inSizeWindowStates_inSizeWindowRight: "States.inSizeWindow ((States.tick ^^ n) (big, small)) \<Longrightarrow> inSizeWindow ((tick ^^ n) (Right big small))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma tick_same_left: "case tick (Left small big) of Left _ _ \<Rightarrow> True | _ \<Rightarrow> False"
  by(auto split: prod.splits)

lemma tick_same_left_n: "case (tick ^^ n) (Left small big) of Left _ _ \<Rightarrow> True | _ \<Rightarrow> False"
proof(induction n arbitrary: small big)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (metis (no_types, lifting) Transformation.tick.simps(1) comp_def funpow_Suc_right prod.case_eq_if) 
qed

lemma tick_same_right: "case tick (Right big small) of Right _ _ \<Rightarrow> True | _ \<Rightarrow> False"
  by(auto split: prod.splits)

lemma tick_same_right_n: "case (tick ^^ n) (Right big small) of Right _ _ \<Rightarrow> True | _ \<Rightarrow> False"
proof(induction n arbitrary: small big)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (metis (no_types, lifting) Transformation.tick.simps(2) comp_def funpow_Suc_right prod.case_eq_if) 
qed

lemma remainingSteps_notIdle: "Transformation.invariant transformation \<Longrightarrow> remainingSteps transformation > 0 \<longleftrightarrow> (
    case transformation of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> False 
    | Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> False 
    | _ \<Rightarrow> True) "
  apply(induction transformation)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remainingSteps_left_idle: "Transformation.invariant (Left small big) \<Longrightarrow> remainingSteps (Left small big) = 0 \<longleftrightarrow> (
    case (Left small big) of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remainingSteps_right_idle: "Transformation.invariant (Right big small) \<Longrightarrow> remainingSteps (Right big small) = 0 \<longleftrightarrow> (
    case (Right big small) of 
      Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma invariant_enqueueLeft: "invariant deque \<Longrightarrow> invariant (enqueueLeft x deque)"
proof(induction x deque rule: enqueueLeft.induct)
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
  case (5 x left' right rightLength)
  then show ?case
  proof(induction "Idle.push x left'")
    case (Idle left leftLength)
    then show ?case
    proof(induction "3 * rightLength \<ge> leftLength")
      case True
      then show ?case
        apply(auto split: idle.splits)
           apply (metis Idle.invariant.simps Idle_Proof.invariant_push)
          apply (metis Idle.size.simps Idle_Proof.size_push Stack_Proof.size_isNotEmpty zero_less_Suc)
         apply (metis Idle.invariant.simps Idle_Proof.invariant_push)
        by (metis Idle.size.simps Idle_Proof.size_push diff_is_0_eq' le_diff_conv mult.commute mult_Suc zero_le_numeral)
    next
      case False

      
      let ?newLeftLength = "leftLength - (Stack.size right) - 1"
      let ?newRightLength = "Suc (2 * Stack.size right)"
      let ?transformation = "(Right 
          (Reverse (Current [] 0 left ?newLeftLength) left [] ?newLeftLength)
          (Reverse1 (Current [] 0 right ?newRightLength) right []))"

      from False have leftNotEmpty: "\<not> Stack.isEmpty left"
        proof(induction x left' rule: Idle.push.induct)
          case (1 x stack stackSize)
          then show ?case
            apply(induction x stack rule: Stack.push.induct)
            by auto
        qed

      from False  have leftLength: "leftLength = Stack.size left" 
        using Idle_Proof.invariant_push[of left' x]
        by(induction left') auto
         
      from False have oldSize: "Suc (Idle.size left') = leftLength"
        apply auto 
        by (metis Idle.size.simps Idle_Proof.size_push leftLength)    

      from False have remSteps: "6 < Transformation.remainingSteps ?transformation"
        apply(auto simp: max_def)
        by (smt (z3) add.commute add_2_eq_Suc' diff_add_inverse2 diff_is_0_eq le_less_Suc_eq length_greater_0_conv leftLength mult_Suc Stack_Proof.size_isNotEmpty not_le not_less_eq numeral_3_eq_3 numeral_Bit0 Stack_Proof.size_listLength oldSize)
        
      from False have invariant: "Transformation.invariant ?transformation"
        apply(auto simp: Stack_Proof.size_listLength popN_drop leftNotEmpty)
           apply (metis Idle.invariant.simps Idle_Proof.invariant_push diff_le_self Stack_Proof.size_listLength)
          apply (simp add: reverseN_take)
        apply (smt (verit, best) popN_drop Suc_leI diff_add_inverse diff_add_inverse2 diff_diff_left helper4 le_eq_less_or_eq leftNotEmpty length_drop mult_Suc numeral_3_eq_3 plus_1_eq_Suc reverseN_reverseN Stack_Proof.size_listLength oldSize)
        by (metis Idle.invariant.simps Idle_Proof.invariant_push add_Suc_right diff_add_inverse Stack_Proof.size_listLength)

      with remSteps have "5 < Transformation.remainingSteps (tick ?transformation)"
        using remainingStepsDecline_3[of ?transformation 5] by auto

      with invariant have "4 < Transformation.remainingSteps ((tick ^^ 2) ?transformation)"
        using invariant_nTicks invariant_tick remainingStepsDecline_4[of ?transformation 4 1]
        by (smt (z3) add.commute add_Suc_right funpow_0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remSteps remainingStepsDecline_4)

      with remSteps have remStepsEnd: "0 < Transformation.remainingSteps (sixTicks ?transformation)"
        using remainingStepsDecline_4[of ?transformation 5 5] 
        by (smt (z3) One_nat_def Suc_eq_plus1 add_Suc_right invariant numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remainingStepsDecline_4)

 
      from False leftNotEmpty have inSizeWindow: "inSizeWindow' ?transformation (remainingSteps ?transformation - 6)"
        apply(auto simp: max_def oldSize leftLength)
        subgoal
          proof(induction "Stack.size left + Stack.size right \<le> 4")
            case True
            then show ?case
              apply(auto)
              by (smt (z3) add_Suc_shift add_diff_cancel_right' add_leE diff_zero first_pop length_Cons less_Suc_eq_le mult.commute mult_2_right mult_Suc_right not_less_eq numeral_3_eq_3 numeral_Bit0 Stack_Proof.size_listLength)
          next
            case False
            then show ?case
              by auto
          qed
        using oldSize leftLength
              Stack_Proof.size_isNotEmpty[of left] 
              Stack_Proof.size_isNotEmpty[of right] 
              size_isNotEmpty[of left'] 
              calculation_helper
        by auto

      then have "inSizeWindow' (sixTicks ?transformation) (remainingSteps (sixTicks ?transformation))"
        using sizeWindow_steps invariant remSteps by blast

      then have sixTicks_inSizeWindow: "inSizeWindow (sixTicks ?transformation)"
        using sizeWindow'_sizeWindow
        using sixTicks_inSizeWindow inSizeWindow by blast

     from invariant have "Transformation.invariant (sixTicks ?transformation)"
       using invariant_sixTicks by blast

      with False sixTicks_inSizeWindow show ?case
        apply(auto simp: Let_def split: idle.splits)
        using remStepsEnd by simp
     qed
  qed
next
  case (6 x left right)
  let ?newLeft = "Small.push x left"
  let ?newTransfomation = "Left ?newLeft right"
  let ?tickedTransformation = "fourTicks ?newTransfomation"

  have start_sizeWindow: "inSizeWindow (Left left right)"
    using "6.prems" RealTimeDeque.invariant.simps(6) by blast

  from 6 have invariant: "Transformation.invariant ?newTransfomation"
    by (meson RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) invariant_push_small)

  then have invariant_fourTicks: "Transformation.invariant (fourTicks ?newTransfomation)"
    using invariant_fourTicks by blast

  with 6 show ?case
  proof(induction "remainingSteps (Left left right) > 4")
    case True
    then have states_inv: "States.invariant (right, left)" by auto
    from True have states_rem: "4 \<le> States.remainingSteps (right, left)" by auto
    from True have states_window: "States.inSizeWindow (right, left)" by auto
    
    from True have "remainingSteps ?newTransfomation > 4"
      by (metis Transformation.remainingSteps.simps(1) remainingSteps_pushSmall states_inv)

    then have remSteps: "remainingSteps ?tickedTransformation > 0"
      by (metis One_nat_def add_Suc_shift funpow_0 invariant numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remainingStepsDecline_4)

    from True have sizeWindow: "inSizeWindow ?tickedTransformation"
      using tick4_pushSmall_sizeWindow[of right left x] states_inv states_rem states_window inSizeWindowStates_inSizeWindowLeft by auto

    have "case ?tickedTransformation of
      Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using tick_same_left[of ?newLeft right] remainingSteps_notIdle[of ?tickedTransformation]
      apply(auto split: prod.splits transformation.splits Small.state.splits Big.state.splits Common.state.splits)
      using remSteps by auto

    then have "(case ?tickedTransformation of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?tickedTransformation) = Transforming ?tickedTransformation"
      by(auto split: transformation.splits Small.state.splits Common.state.splits Big.state.splits)

    with True  have "invariant (case ?tickedTransformation of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?tickedTransformation)"
      by (smt (z3) RealTimeDeque.invariant.simps(6) remSteps sizeWindow) 

    with True show ?case
      by(auto simp: Let_def)

  next
    case False
    then have "remainingSteps ?newTransfomation \<le> 4"
      by (metis RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) Transformation.remainingSteps.simps(1) leI remainingSteps_pushSmall)

    with False have remSteps: "remainingSteps ?tickedTransformation = 0"
      using invariant remainingStepsDecline_5[of ?newTransfomation 4]
      by auto

    obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Left tickedLeft tickedRight"
      using tick_same_left_n[of 4 ?newLeft right]
      by (simp add: case_prod_unfold numeral_Bit0)

    with remSteps have "case Left tickedLeft tickedRight of
      Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" using remainingSteps_left_idle[of ] tick_same_left
      using local.invariant_fourTicks by auto

    then obtain l idleLeft r idleRight where idle: "Left tickedLeft tickedRight = 
      Left (Small.state.Common (state.Idle l idleLeft)) (Big.state.Common (state.Idle r idleRight))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have transformation_invariant: "Transformation.invariant (Left tickedLeft tickedRight)"
      using False
      using \<open>fourTicks (transformation.Left (Small.push x left) right) = transformation.Left tickedLeft tickedRight\<close>
      by auto

    with ticked invariant_fourTicks have "Big.newSize right = Big.newSize tickedRight"
      using invariant tickN_left_newSizeBig by blast

    have leftSizes1: "Small.size ?newLeft = Suc (Small.size left)"
      by (meson "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) funpow_0 tickN_pushSmall_sizeSmall)

    with ticked invariant_fourTicks have leftSizes: "Small.newSize ?newLeft = Small.newSize tickedLeft"
      using invariant tickN_left_newSizeSmall by blast

    then have "0 < Small.newSize left"
      using "6.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_smallNewSize by blast

    then have "0 < Small.newSize ?newLeft"
      using \<open>Small.size (Small.push x left) = Suc (Small.size left)\<close> invariant Small_Proof.size_newSize by fastforce

    then have "0 < Small.newSize tickedLeft"
      by (simp add: \<open>Small.newSize (Small.push x left) = Small.newSize tickedLeft\<close>)

    then have "0 < Big.newSize right"
      using "6.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_bigNewSize by blast

    then have rightNotEmpty: "0 < Big.newSize tickedRight"
      by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)

    have leftSize: "Idle.size idleLeft = Small.newSize tickedLeft"
      using idle transformation_invariant by auto

    have rightSize: "Idle.size idleRight = Big.newSize tickedRight"
      using idle transformation_invariant by auto

    have wind2: "Small.newSize left \<le> 3 * Big.newSize right - 1"
      using start_sizeWindow
      by auto

    have "Suc (Small.newSize left) = Small.newSize ?newLeft"
      by (metis "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) funpow_0 tickN_pushSmall_newSizeSmall)

    with wind2 have "Small.newSize ?newLeft \<le> 3 * Big.newSize right"
      using \<open>0 < Big.newSize right\<close> by linarith

    then have "Small.newSize tickedLeft \<le> 3 * Big.newSize right"  
      by (simp add: leftSizes)

    then have T: "Small.newSize tickedLeft \<le> 3 * Big.newSize tickedRight"  
      using \<open>Big.newSize right = Big.newSize tickedRight\<close> by presburger

    have "Big.newSize right \<le> 3 * Small.newSize left"
      using start_sizeWindow leftSizes1
      by auto

    then have "Big.newSize right \<le> 3 * Small.newSize ?newLeft"
      using leftSizes1
      by (metis (no_types, hide_lams) "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) dual_order.trans funpow_0 le_add2 mult_le_mono2 plus_1_eq_Suc tickN_pushSmall_newSizeSmall)

    then have "Big.newSize right \<le> 3 * Small.newSize tickedLeft"
      by (simp add: leftSizes)

    then have "Big.newSize tickedRight \<le> 3 * Small.newSize tickedLeft"
      by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)
    
    with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
      apply auto
      apply (metis Common.newSize.simps(1) Idle.isEmpty.elims(2) Idle.size.simps Small.newSize.simps(1) \<open>0 < Small.newSize (Small.push x left)\<close> \<open>Small.newSize (Small.push x left) = Small.newSize tickedLeft\<close> list.size(3) Stack_Proof.size_listLength Stack_Proof.toList_isNotEmpty verit_comp_simplify1(1))
      using rightNotEmpty Idle_Proof.isNotEmpty by auto
     
     with False  have "invariant (case Left tickedLeft tickedRight of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming (Left tickedLeft tickedRight))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

     with False show ?case
       by (metis \<open>fourTicks (transformation.Left (Small.push x left) right) = transformation.Left tickedLeft tickedRight\<close> enqueueLeft.simps(6))
   qed
next
  case (7 x left right)
  let ?newLeft = "Big.push x left"
  let ?newTransfomation = "Right ?newLeft right"
  let ?tickedTransformation = "fourTicks ?newTransfomation"

  have start_sizeWindow: "inSizeWindow (Right left right)"
    using "7.prems" RealTimeDeque.invariant.simps(6) by blast

  from 7 have invariant: "Transformation.invariant ?newTransfomation"
    by (meson RealTimeDeque.invariant.simps(6) Transformation.invariant.simps invariant_push_big)

  then have invariant_fourTicks: "Transformation.invariant (fourTicks ?newTransfomation)"
    using invariant_fourTicks by blast

  with 7 show ?case
  proof(induction "remainingSteps (Right left right) > 4")
    case True
    then have states_inv: "States.invariant (left, right)" by auto
    from True have states_rem: "4 \<le> States.remainingSteps (left, right)" by auto
    from True have states_window: "States.inSizeWindow (left, right)" by auto
    
    from True have "remainingSteps ?newTransfomation > 4"
      by (metis Transformation.remainingSteps.simps(2) remainingSteps_pushBig states_inv)

    then have remSteps: "remainingSteps ?tickedTransformation > 0"
      by (metis One_nat_def add_Suc_shift funpow_0 invariant numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remainingStepsDecline_4)

    from True have sizeWindow: "inSizeWindow ?tickedTransformation"
      using tick4_pushBig_sizeWindow[of left right x] states_inv states_rem states_window inSizeWindowStates_inSizeWindowLeft
      using inSizeWindowStates_inSizeWindowRight by blast

    have "case ?tickedTransformation of
      Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using tick_same_right[of ?newLeft right] remainingSteps_notIdle[of ?tickedTransformation]
      apply(auto split: prod.splits transformation.splits Small.state.splits Big.state.splits Common.state.splits)
      using remSteps by auto

    then have "(case ?tickedTransformation of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?tickedTransformation) = Transforming ?tickedTransformation"
      by(auto split: transformation.splits Small.state.splits Common.state.splits Big.state.splits)

    with True  have "invariant (case ?tickedTransformation of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?tickedTransformation)"
      by (smt (z3) RealTimeDeque.invariant.simps(6) remSteps sizeWindow) 

    with True show ?case
      by(auto simp: Let_def)

  next
    case False
    then have "remainingSteps ?newTransfomation \<le> 4"
      by (metis RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(2) Transformation.remainingSteps.simps(2) leI remainingSteps_pushBig)

    with False have remSteps: "remainingSteps ?tickedTransformation = 0"
      using invariant remainingStepsDecline_5[of ?newTransfomation 4]
      by auto

    obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Right tickedLeft tickedRight"
      using tick_same_right_n[of 4 ?newLeft right]
      by (simp add: case_prod_unfold numeral_Bit0)

    with remSteps have "case Right tickedLeft tickedRight of
      Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" using remainingSteps_right_idle tick_same_right
      using local.invariant_fourTicks by auto

    then obtain l idleLeft r idleRight where idle: "Right tickedLeft tickedRight = 
      Right (Big.state.Common (state.Idle l idleLeft)) (Small.state.Common (state.Idle r idleRight))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have transformation_invariant: "Transformation.invariant (Right tickedLeft tickedRight)"
      using False
      using \<open>fourTicks (transformation.Right (Big.push x left) right) = transformation.Right tickedLeft tickedRight\<close>
      by auto

    with ticked invariant_fourTicks have "Small.newSize right = Small.newSize tickedRight"
      using invariant tickN_right_newSizeSmall by blast

    have leftSizes1: "Big.size ?newLeft = Suc (Big.size left)"
      using "7.prems" Big_Proof.size_push by fastforce

    with ticked invariant_fourTicks have leftSizes: "Big.newSize ?newLeft = Big.newSize tickedLeft" 
      using invariant tickN_right_newSizeBig by blast

    then have "0 < Big.newSize left"
     using "7.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_bigNewSize
     by fastforce

    then have "0 < Big.newSize ?newLeft"
      using \<open>Big.size (Big.push x left) = Suc (Big.size left)\<close> invariant Big_Proof.size_newSize by fastforce

    then have "0 < Big.newSize tickedLeft"
      by (simp add: \<open>Big.newSize (Big.push x left) = Big.newSize tickedLeft\<close>)

    then have "0 < Small.newSize right"
      using "7.prems" RealTimeDeque.invariant.simps Transformation.inSizeWindow.simps Transformation.invariant.simps sizeWindow_smallNewSize 
      by fastforce

    then have rightNotEmpty: "0 < Small.newSize tickedRight"
      by (simp add: \<open>Small.newSize right = Small.newSize tickedRight\<close>)

    have leftSize: "Idle.size idleLeft = Big.newSize tickedLeft"
      using idle transformation_invariant by auto

    have rightSize: "Idle.size idleRight = Small.newSize tickedRight"
      using idle transformation_invariant by auto

    have wind2: "Big.newSize left \<le> 3 * Small.newSize right - 1"
      using start_sizeWindow
      by auto

    have "Suc (Big.newSize left) = Big.newSize ?newLeft"
      using "7.prems" Big_Proof.newSize_push by fastforce

    with wind2 have "Big.newSize ?newLeft \<le> 3 * Small.newSize right"
      using \<open>0 < Small.newSize right\<close> by linarith

    then have "Big.newSize tickedLeft \<le> 3 * Small.newSize right"  
      by (simp add: leftSizes)

    then have T: "Big.newSize tickedLeft \<le> 3 * Small.newSize tickedRight"  
      using \<open>Small.newSize right = Small.newSize tickedRight\<close> by presburger

    have "Small.newSize right \<le> 3 * Big.newSize left"
      using start_sizeWindow leftSizes1
      by auto

    then have "Small.newSize right \<le> 3 * Big.newSize ?newLeft"
      using leftSizes1
      using \<open>Suc (Big.newSize left) = Big.newSize (Big.push x left)\<close> by linarith

    then have "Small.newSize right \<le> 3 * Big.newSize tickedLeft"
      by (simp add: leftSizes)

    then have "Small.newSize tickedRight \<le> 3 * Big.newSize tickedLeft"
      by (simp add: \<open>Small.newSize right = Small.newSize tickedRight\<close>)
    
    with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
      apply auto
      apply (metis Idle.isEmpty.elims(2) Idle.size.simps Stack_Proof.size_isEmpty Suc_neq_Zero \<open>Suc (Big.newSize left) = Big.newSize (Big.push x left)\<close> leftSize leftSizes)
      using rightNotEmpty Idle_Proof.isNotEmpty by auto
     
     with False  have "invariant (case Right tickedLeft tickedRight of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming (Right tickedLeft tickedRight))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

     with False show ?case
      by (metis enqueueLeft.simps(7) ticked)
  qed
qed

end

