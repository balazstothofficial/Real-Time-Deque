theory RealTimeDeque_Enqueue
  imports Deque RealTimeDeque Transformation_Proof
begin

lemma helper_1_4: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> Stack.size right - (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left)) = 0"
proof -
  assume a1: "Idle.invariant left'"
  assume a2: "rightLength = Stack.size right"
  assume "idle.Idle left leftLength = Idle.push x left'"
  then have f3: "\<And>n. List.length (drop n (Stack.toList left)) = leftLength - n"
    using a1 by (metis (no_types) Idle.invariant.simps Idle_Proof.invariant_push length_drop size_listLength)
  moreover
  { assume "\<exists>n. rightLength + (rightLength + 1) - leftLength = rightLength + n"
    moreover
    { assume "\<exists>n. rightLength + (rightLength + 1) - (leftLength - (leftLength - (rightLength + 1))) = rightLength + n"
      then have "rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.toList left))) = 0"
        using f3 diff_is_0_eq nat_le_iff_add by presburger }
    ultimately have "leftLength \<le> rightLength + 1 \<longrightarrow> rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.toList left))) = 0"
      using diff_zero by fastforce }
  ultimately show ?thesis
    using a2 helper_2
    by (metis (no_types, lifting) Nat.add_diff_assoc One_nat_def States_Proof.helper add_Suc_right add_diff_cancel_left' diff_cancel2 diff_diff_cancel linear mult_2 plus_1_eq_Suc size_listLength)
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
          apply(auto simp: reverseN_take helper leftNotEmpty)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_push diff_le_self)
          apply (simp add: size_listLength)+
          apply (smt (verit) States_Proof.helper append_take_drop_id diff_is_0_eq helper_1_4 leftNotEmpty length_rev rev_append rev_rev_ident size_listLength take_all_iff)
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
      by(auto simp: push_small currentList_push)
                          
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
      by (metis Big_Proof.currentList_push append_Cons rev_append rev_rev_ident)
    
    from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
      using invariant_fourTicks by blast

    then have "toListLeft ?tickedTransformation = x # Big.toCurrentList left @ rev (Small.toCurrentList right)"
      using Transformation_Proof.fourTicks invariant toListLeft by fastforce


    with 7 show ?case 
      apply(auto simp: Let_def split: transformation.split prod.split Big.state.split Common.state.split Small.state.split)
      by (metis rev_append rev_rev_ident)+
  qed

lemma test_2: "List.length (Stack.toList stack) = Stack.size stack"
  apply(induction stack)
  by auto

lemma helper_1_3: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> Suc (List.length (Stack.toList right) + Stack.size right) - leftLength = 0"
  by(auto simp: test_2)

lemma helper_1_2: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> rev (
            take 
               (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
               (rev (
                      take (leftLength - Suc (Stack.size right)) (Stack.toList right))
                    )
               ) =
         Stack.toList right"
  by(auto simp: rev_take helper_1_3 test_2 helper_1_4)

lemma anja: "0 < Stack.size left \<Longrightarrow> \<not>Stack.isEmpty left"
  apply(induction left rule: Stack.isEmpty.induct)
  by auto

lemma anja_2: "0 < Idle.size idle \<Longrightarrow> \<not>Idle.isEmpty idle"
  apply(induction idle rule: Idle.isEmpty.induct)
  by(auto simp: anja)

lemma anja_3: "\<not>Stack.isEmpty left \<Longrightarrow> 0 < Stack.size left"
  apply(induction left rule: Stack.isEmpty.induct)
  by auto

lemma anja_4: "\<not>Idle.isEmpty idle \<Longrightarrow> 0 < Idle.size idle "
  apply(induction idle rule: Idle.isEmpty.induct)
  by(auto simp: anja_3)

lemma maybe3: "\<lbrakk>
          \<not> l \<le> 3 * r; 
          Suc l' = l;
          0 < l;
          0 < l';
          0 < r;
          l' \<le> 3 * r;
          l + l - Suc (Suc (r + r)) \<le> Suc (l + r)
       \<rbrakk> \<Longrightarrow> Suc (l + r - 4) \<le> 4 * r"
  by auto

lemma maybe4: "\<lbrakk>
    \<not> l \<le> 3 * r; 
    0 < l;
    0 < l'; 
    0 < r; 
    l' \<le> 3 * r;
    l + l - Suc (Suc (r + r)) \<le> Suc (l + r);
    Suc l' = l
\<rbrakk> \<Longrightarrow> 0 < r"
  by auto

lemma maybe5: " \<lbrakk>
   \<not> l \<le> 3 * r; 
   0 < l;
   0 < l'; 
   0 < r; 
   l' \<le> 3 * r;
   l + l - Suc (Suc (r + r)) \<le> Suc (l + r);
   Suc l' = l
\<rbrakk> \<Longrightarrow> Suc 0 < l - Suc r"
  by auto

lemma helper_1: "\<lbrakk>
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
  by (metis (no_types, lifting) States_Proof.helper append_Nil2 append_assoc append_take_drop_id helper_1_2 rev_append reverseN_take)

lemma fixed_5: "States.inSizeWindow ((States.tick ^^ n) (big, small)) \<Longrightarrow> inSizeWindow ((tick ^^ n) (Left small big))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma fixed_6: "States.inSizeWindow ((States.tick ^^ n) (big, small)) \<Longrightarrow> inSizeWindow ((tick ^^ n) (Right big small))"
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


lemma remSteps_idle_5: "Transformation.invariant transformation \<Longrightarrow> remainingSteps transformation > 0 \<longleftrightarrow> (
    case transformation of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> False 
    | Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> False 
    | _ \<Rightarrow> True) "
  apply(induction transformation)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remSteps_idle_6: "Transformation.invariant (Left small big) \<Longrightarrow> remainingSteps (Left small big) = 0 \<longleftrightarrow> (
    case (Left small big) of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remSteps_idle_6': "Transformation.invariant (Right big small) \<Longrightarrow> remainingSteps (Right big small) = 0 \<longleftrightarrow> (
    case (Right big small) of 
      Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma geficke2:  "States.inSizeWindow ((States.tick ^^ n) (right, Small.push x left)) \<Longrightarrow>
     Transformation.inSizeWindow ((tick ^^ n) (transformation.Left (Small.push x left) right))"
  by (simp add: fixed_5)

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
          apply (metis Idle.size.simps Idle_Proof.size_push size_isNotEmpty zero_less_Suc)
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

      from False have "0 < leftLength"
        by auto

      from False have test: "leftLength = Stack.size left" 
        apply auto
        by (metis Idle.invariant.simps Idle_Proof.invariant_push)

      from False have suc: "Suc (Idle.size left') = leftLength"
        apply auto 
        by (metis Idle.size.simps Idle_Proof.size_push local.test)    

      from False have remSteps: "6 < Transformation.remainingSteps ?transformation"
        apply(auto simp: max_def)
        by (smt (z3) add.commute add_2_eq_Suc' diff_add_inverse2 diff_is_0_eq le_less_Suc_eq length_greater_0_conv local.test mult_Suc size_isNotEmpty not_le not_less_eq numeral_3_eq_3 numeral_Bit0 size_listLength suc)
        
      from False have invariant: "Transformation.invariant ?transformation"
        apply(auto simp: size_listLength helper leftNotEmpty)
           apply (metis Idle.invariant.simps Idle_Proof.invariant_push diff_le_self size_listLength)
          apply (simp add: reverseN_take)
        apply (smt (verit, best) States_Proof.helper Suc_leI diff_add_inverse diff_add_inverse2 diff_diff_left helper_1 le_eq_less_or_eq leftNotEmpty length_drop mult_Suc numeral_3_eq_3 plus_1_eq_Suc reverseN_reverseN size_listLength suc)
        by (metis Idle.invariant.simps Idle_Proof.invariant_push add_Suc_right diff_add_inverse size_listLength)

      with remSteps have "5 < Transformation.remainingSteps (tick ?transformation)"
        using remainingStepsDecline_3[of ?transformation 5] by auto

      with invariant have "4 < Transformation.remainingSteps ((tick ^^ 2) ?transformation)"
        using invariant_nTicks invariant_tick remainingStepsDecline_4[of ?transformation 4 1]
        by (smt (z3) add.commute add_Suc_right funpow_0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remSteps remainingStepsDecline_4)

      with remSteps have remStepsEnd: "0 < Transformation.remainingSteps (sixTicks ?transformation)"
        unfolding sixTicks_def using remainingStepsDecline_4[of ?transformation 5 5] 
        by (smt (z3) One_nat_def Suc_eq_plus1 add_Suc_right invariant numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remainingStepsDecline_4)

      from False leftNotEmpty have " Stack.size right \<le> 3 * Idle.size left'"
        by auto

      have dummy: "4 + 8 * Stack.size right \<le> 12 * (Stack.size left - Suc (Stack.size right)) \<longleftrightarrow>
            16 + 20 * Stack.size right \<le> 12 * Stack.size left"
        by auto

      have dummy_2: "\<lbrakk>
        \<not> Stack.size left \<le> 3 * Stack.size right; 
        idle.Idle left (Stack.size left) = Idle.push x left';
        \<not> Stack.isEmpty left; 
        Idle.invariant left';
        rightLength = Stack.size right; 
        \<not> Idle.isEmpty left'; 
        \<not> Stack.isEmpty right; 
        Idle.size left' \<le> 3 * Stack.size right;
        Stack.size left + Stack.size left - Suc (Suc (Stack.size right + Stack.size right)) \<le> Suc (Stack.size left + Stack.size right);
        leftLength = Stack.size left; 
        Suc (Idle.size left') = Stack.size left
     \<rbrakk> \<Longrightarrow> Suc (Stack.size left + Stack.size right - 4) \<le> 4 * Stack.size right"
        using anja_3[of left] anja_3[of right] anja_4[of left'] maybe3 by auto

      from False leftNotEmpty have inSizeWindow: "inSizeWindow' ?transformation (remainingSteps ?transformation - 6)"
        apply(auto simp: test max_def suc)
        subgoal using local.test suc 
        proof(induction "Stack.size left + Stack.size right \<le> 4")
          case True
          then show ?case
            apply(auto simp: dummy)
            by (smt (z3) add_Suc_shift add_diff_cancel_right' add_leE diff_zero first_pop length_Cons less_Suc_eq_le mult.commute mult_2_right mult_Suc_right not_less_eq numeral_3_eq_3 numeral_Bit0 size_listLength)
        next
          case False
          then show ?case
            by auto
        qed
        using local.test suc
              apply(auto simp: min_def) 
        subgoal using dummy_2 by auto
        subgoal using dummy_2 by auto
        subgoal using maybe4[of "Stack.size left" "Stack.size right" "Idle.size left'"] anja_3[of left] anja_3[of right] anja_4[of left']
          by auto
        using maybe5[of "Stack.size left" "Stack.size right" "Idle.size left'"] anja_3[of left] anja_3[of right] anja_4[of left']
        by auto

      then have "inSizeWindow' (sixTicks ?transformation) (remainingSteps (sixTicks ?transformation))"
        using sizeWindow_steps  invariant remSteps unfolding sixTicks_def by blast

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
      by (metis Transformation.remainingSteps.simps(1) same_d states_inv)

    then have remSteps: "remainingSteps ?tickedTransformation > 0"
      by (metis One_nat_def add_Suc_shift fourTicks_def funpow_0 invariant numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remainingStepsDecline_4)

    from True have sizeWindow: "inSizeWindow ?tickedTransformation"
      using same[of right left x] states_inv states_rem states_window geficke2 unfolding fourTicks_def by auto

    have "case ?tickedTransformation of
      Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using tick_same_left[of ?newLeft right] remSteps_idle_5[of ?tickedTransformation]
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
      by (metis RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) Transformation.remainingSteps.simps(1) leI same_d)

    with False have remSteps: "remainingSteps ?tickedTransformation = 0"
      unfolding fourTicks_def using invariant remainingStepsDecline_5[of ?newTransfomation 4]
      by auto

    obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Left tickedLeft tickedRight"
      unfolding fourTicks_def using tick_same_left_n[of 4 ?newLeft right]
      by (simp add: case_prod_unfold numeral_Bit0)

    with remSteps have "case Left tickedLeft tickedRight of
      Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" using remSteps_idle_6[of ] tick_same_left
      using local.invariant_fourTicks by auto

    then obtain l idleLeft r idleRight where idle: "Left tickedLeft tickedRight = 
      Left (Small.state.Common (state.Idle l idleLeft)) (Big.state.Common (state.Idle r idleRight))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have transformation_invariant: "Transformation.invariant (Left tickedLeft tickedRight)"
      using False
      using \<open>fourTicks (transformation.Left (Small.push x left) right) = transformation.Left tickedLeft tickedRight\<close>
      by auto

    with ticked invariant_fourTicks have "Big.newSize right = Big.newSize tickedRight"
      unfolding fourTicks_def 
      using invariant size_tick_n_6 by blast

    have leftSizes1: "Small.size ?newLeft = Suc (Small.size left)"
      by (meson "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) funpow_0 same_c)

    with ticked invariant_fourTicks have leftSizes: "Small.newSize ?newLeft = Small.newSize tickedLeft"
      unfolding fourTicks_def 
      using invariant size_tick_n_2 by blast

    then have "0 < Small.newSize left"
      using "6.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_smallNewSize by blast

    then have "0 < Small.newSize ?newLeft"
      using \<open>Small.size (Small.push x left) = Suc (Small.size left)\<close> invariant sizes_small by fastforce

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
      by (metis "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) funpow_0 same_c_2)

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
      by (metis (no_types, hide_lams) "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) dual_order.trans funpow_0 le_add2 mult_le_mono2 plus_1_eq_Suc same_c_2)

    then have "Big.newSize right \<le> 3 * Small.newSize tickedLeft"
      by (simp add: leftSizes)

    then have "Big.newSize tickedRight \<le> 3 * Small.newSize tickedLeft"
      by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)
    
    with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
      apply auto
      apply (metis Common.newSize.simps(1) Idle.isEmpty.elims(2) Idle.size.simps Small.newSize.simps(1) \<open>0 < Small.newSize (Small.push x left)\<close> \<open>Small.newSize (Small.push x left) = Small.newSize tickedLeft\<close> list.size(3) size_listLength toList_isNotEmpty verit_comp_simplify1(1))
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
      by (metis Transformation.remainingSteps.simps(2) same_d2 states_inv)

    then have remSteps: "remainingSteps ?tickedTransformation > 0"
      by (metis One_nat_def add_Suc_shift fourTicks_def funpow_0 invariant numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remainingStepsDecline_4)

    from True have sizeWindow: "inSizeWindow ?tickedTransformation"
      using same2[of left right x] states_inv states_rem states_window geficke2 unfolding fourTicks_def
      using fixed_6 by blast

    have "case ?tickedTransformation of
      Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using tick_same_right[of ?newLeft right] remSteps_idle_5[of ?tickedTransformation]
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
      by (metis RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(2) Transformation.remainingSteps.simps(2) leI same_d2)

    with False have remSteps: "remainingSteps ?tickedTransformation = 0"
      unfolding fourTicks_def using invariant remainingStepsDecline_5[of ?newTransfomation 4]
      by auto

    obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Right tickedLeft tickedRight"
      unfolding fourTicks_def using tick_same_right_n[of 4 ?newLeft right]
      by (simp add: case_prod_unfold numeral_Bit0)

    with remSteps have "case Right tickedLeft tickedRight of
      Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" using remSteps_idle_6' tick_same_right
      using local.invariant_fourTicks by auto

    then obtain l idleLeft r idleRight where idle: "Right tickedLeft tickedRight = 
      Right (Big.state.Common (state.Idle l idleLeft)) (Small.state.Common (state.Idle r idleRight))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have transformation_invariant: "Transformation.invariant (Right tickedLeft tickedRight)"
      using False
      using \<open>fourTicks (transformation.Right (Big.push x left) right) = transformation.Right tickedLeft tickedRight\<close>
      by auto

    with ticked invariant_fourTicks have "Small.newSize right = Small.newSize tickedRight"
      unfolding fourTicks_def 
      using invariant size_tick_n_4 by blast

    have leftSizes1: "Big.size ?newLeft = Suc (Big.size left)"
      using "7.prems" push_size_big by fastforce

    with ticked invariant_fourTicks have leftSizes: "Big.newSize ?newLeft = Big.newSize tickedLeft"
      unfolding fourTicks_def 
      using invariant size_tick_n_8 by blast

    then have "0 < Big.newSize left"
     using "7.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_bigNewSize
     by fastforce

    then have "0 < Big.newSize ?newLeft"
      using \<open>Big.size (Big.push x left) = Suc (Big.size left)\<close> invariant sizes_big by fastforce

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
      using "7.prems" push_newSize_big by fastforce

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

