theory RealTimeDeque_Enqueue
  imports Deque RealTimeDeque Transformation_Proof
begin

lemma helper: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invar left'; rightLength = Stack.size right;
     \<not> Idle.is_empty left'; \<not> Stack.is_empty right; \<not> Stack.is_empty left\<rbrakk>
    \<Longrightarrow> Stack.size right - (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left)) = 0"
proof -
  assume a1: "Idle.invar left'"
  assume a2: "rightLength = Stack.size right"
  assume "idle.Idle left leftLength = Idle.push x left'"
  then have f3: "\<And>n. List.length (drop n (Stack.list left)) = leftLength - n"
    using a1 by (metis (no_types) Idle.invar.simps Idle_Proof.invar_push length_drop Stack_Proof.size_list_length)
  moreover
  { assume "\<exists>n. rightLength + (rightLength + 1) - leftLength = rightLength + n"
    moreover
    { assume "\<exists>n. rightLength + (rightLength + 1) - (leftLength - (leftLength - (rightLength + 1))) = rightLength + n"
      then have "rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.list left))) = 0"
        using f3 diff_is_0_eq nat_le_iff_add by presburger }
    ultimately have "leftLength \<le> rightLength + 1 \<longrightarrow> rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.list left))) = 0"
      using diff_zero by fastforce }
  ultimately show ?thesis
    using a2
    by (metis (no_types, lifting) Nat.add_diff_assoc One_nat_def popN_drop add_Suc_right add_diff_cancel_left' diff_cancel2 diff_diff_cancel linear mult_2 plus_1_eq_Suc Stack_Proof.size_list_length)
qed

lemma list_enqL: "invar deque \<Longrightarrow> listL (enqL x deque) = x # listL deque"
proof(induction x deque rule: enqL.induct)
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
        by (metis Idle.list.simps Idle_Proof.push_list)+
    next
      case False
      let ?transformation = "(Right 
          (Reverse (Current [] 0 left (leftLength - Suc (Stack.size right))) left [] (leftLength - Suc (Stack.size right)))
          (Reverse1 (Current [] 0 right (Suc (2 * Stack.size right))) right []))"

      from False have left_not_empty: "\<not> Stack.is_empty left"
      proof(induction x left' rule: Idle.push.induct)
        case (1 x stack stackSize)
        then show ?case
          apply(induction x stack rule: Stack.push.induct)
          by auto
      qed

      from False have invar: "Transformation.invar ?transformation"
        apply(auto)
        apply(auto simp: reverseN_take popN_drop left_not_empty)
        apply (metis Idle.invar.simps Idle_Proof.invar_push diff_le_self)
        apply (simp add: Stack_Proof.size_list_length)+
        apply (smt (verit) popN_drop append_take_drop_id diff_is_0_eq helper left_not_empty length_rev rev_append rev_rev_ident Stack_Proof.size_list_length take_all_iff)
        by (metis Idle.invar.simps Idle_Proof.invar_push add_Suc_right diff_add_inverse)
     
      then have "Transformation.listL ?transformation = x # Idle.list left' @ rev (Stack.list right)"
        apply(auto simp: reverseN_take)
        by (metis (no_types, lifting) Idle.hyps Idle.list.simps Idle_Proof.push_list append_Cons append_assoc rev_append rev_swap)

      with invar have 
         "Transformation.listL (six_steps ?transformation) = x # Idle.list left' @ rev (Stack.list right)"
        by (auto simp: n_steps)

      with False show ?case
        by(auto simp: Let_def split: idle.splits)
    qed
  qed
next
  case (6 x left right)
  let ?newLeft = "Small.push x left"
  let ?newTransfomation = "Left ?newLeft right"
  let ?steppedTransformation = "four_steps ?newTransfomation"

  from 6 have invar: "Transformation.invar ?newTransfomation"
    by (meson invar.simps(6) Transformation.invar.simps(1) invar_push_small)

  then have list: "Transformation.listL ?newTransfomation = x # Small.list_current left @ rev (Big.list_current right)"
    by(auto simp: push_small push_list_current)
                        
  from invar have four_steps: "Transformation.invar ?steppedTransformation"
    using invar_n_steps by blast

  then have "Transformation.listL ?steppedTransformation = x # Small.list_current left @ rev (Big.list_current right)"
    using n_steps invar list by fastforce

  with 6 show ?case
    by(auto simp: Let_def split: transformation.splits state_splits)
next
  case (7 x left right)

  let ?newLeft = "Big.push x left"
  let ?newTransfomation = "Right ?newLeft right"
  let ?steppedTransformation = "four_steps ?newTransfomation"

  from 7 have invar: "Transformation.invar ?newTransfomation"
    by (meson RealTimeDeque.invar.simps Transformation.invar.simps invar_push_big)

  then have listR: "Transformation.listR ?newTransfomation = Small.list_current right @ rev (Big.list_current (Big.push x left))"
    by auto

  with invar have listL: "Transformation.listL ?newTransfomation = x # Big.list_current left @ rev (Small.list_current right)"
    apply(auto simp: push_big split: prod.splits)
    by (metis Big_Proof.push_list_current append_Cons rev_append rev_rev_ident)
  
  from invar have four_steps: "Transformation.invar ?steppedTransformation"
    using invar_n_steps by blast

  then have "Transformation.listL ?steppedTransformation = x # Big.list_current left @ rev (Small.list_current right)"
    using n_steps invar listL by fastforce

  with 7 show ?case 
    apply(auto simp: Let_def split: transformation.split prod.split Big.state.split Common.state.split Small.state.split)
    by (metis rev_append rev_rev_ident)+
qed


lemma helper2: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invar left'; rightLength = Stack.size right;
     \<not> Idle.is_empty left'; \<not> Stack.is_empty right; \<not> Stack.is_empty left\<rbrakk>
    \<Longrightarrow> Suc (List.length (Stack.list right) + Stack.size right) - leftLength = 0"
  by(auto simp: size_list_length)

lemma helper3: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invar left'; rightLength = Stack.size right;
     \<not> Idle.is_empty left'; \<not> Stack.is_empty right; \<not> Stack.is_empty left\<rbrakk>
    \<Longrightarrow> rev (
            take 
               (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
               (rev (
                      take (leftLength - Suc (Stack.size right)) (Stack.list right))
                    )
               ) =
         Stack.list right"
  by(auto simp: rev_take helper2 size_list_length[symmetric] helper)

lemma helper4: "\<lbrakk>
  \<not> leftLength \<le> 3 * Stack.size right; 
  idle.Idle left leftLength = Idle.push x left'; 
  Idle.invar left'; rightLength = Stack.size right;
  \<not> Idle.is_empty left'; 
  \<not> Stack.is_empty right;
  \<not> Stack.is_empty left
\<rbrakk> \<Longrightarrow> reverseN (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
          (reverseN (leftLength - Suc (Stack.size right)) (Stack.list right) [])
          (rev (Stack.list ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))) @
         rev (take (leftLength - Suc (Stack.size right)) (Stack.list left)) =
         Stack.list right @ rev (Stack.list left)"
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

lemma size_ok_states_left: "States.size_ok ((States.step ^^ n) (big, small)) \<Longrightarrow> size_ok ((step ^^ n) (Left small big))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma size_ok_states_right: "States.size_ok ((States.step ^^ n) (big, small)) \<Longrightarrow> size_ok ((step ^^ n) (Right big small))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma step_same_left: "case step (Left small big) of Left _ _ \<Rightarrow> True | _ \<Rightarrow> False"
  by(auto split: prod.splits)

lemma step_same_left_n: "case (step ^^ n) (Left small big) of Left _ _ \<Rightarrow> True | _ \<Rightarrow> False"
proof(induction n arbitrary: small big)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (metis (no_types, lifting) Transformation.step.simps(1) comp_def funpow_Suc_right prod.case_eq_if) 
qed

lemma step_same_right: "case step (Right big small) of Right _ _ \<Rightarrow> True | _ \<Rightarrow> False"
  by(auto split: prod.splits)

lemma step_same_right_n: "case (step ^^ n) (Right big small) of Right _ _ \<Rightarrow> True | _ \<Rightarrow> False"
proof(induction n arbitrary: small big)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (metis (no_types, lifting) Transformation.step.simps(2) comp_def funpow_Suc_right prod.case_eq_if) 
qed

lemma remaining_steps_not_idle: "Transformation.invar transformation \<Longrightarrow> remaining_steps transformation > 0 \<longleftrightarrow> (
    case transformation of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> False 
    | Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> False 
    | _ \<Rightarrow> True) "
  apply(induction transformation)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remaining_steps_left_idle: "Transformation.invar (Left small big) \<Longrightarrow> remaining_steps (Left small big) = 0 \<longleftrightarrow> (
    case (Left small big) of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remaining_steps_right_idle: "Transformation.invar (Right big small) \<Longrightarrow> remaining_steps (Right big small) = 0 \<longleftrightarrow> (
    case (Right big small) of 
      Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma invar_enqL: "invar deque \<Longrightarrow> invar (enqL x deque)"
proof(induction x deque rule: enqL.induct)
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
           apply (metis Idle.invar.simps Idle_Proof.invar_push)
          apply (metis Idle.size.simps Idle_Proof.size_push Stack_Proof.size_not_empty zero_less_Suc)
         apply (metis Idle.invar.simps Idle_Proof.invar_push)
        by (metis Idle.size.simps Idle_Proof.size_push diff_is_0_eq' le_diff_conv mult.commute mult_Suc zero_le_numeral)
    next
      case False

      
      let ?newLeftLength = "leftLength - (Stack.size right) - 1"
      let ?newRightLength = "Suc (2 * Stack.size right)"
      let ?transformation = "(Right 
          (Reverse (Current [] 0 left ?newLeftLength) left [] ?newLeftLength)
          (Reverse1 (Current [] 0 right ?newRightLength) right []))"

      from False have left_not_empty: "\<not> Stack.is_empty left"
        proof(induction x left' rule: Idle.push.induct)
          case (1 x stack stackSize)
          then show ?case
            apply(induction x stack rule: Stack.push.induct)
            by auto
        qed

      from False have leftLength: "leftLength = Stack.size left" 
        using Idle_Proof.invar_push[of left' x]
        by(induction left') auto
         
      from False have old_size: "Suc (Idle.size left') = leftLength"
        apply auto 
        by (metis Idle.size.simps Idle_Proof.size_push leftLength)    

      from False have remaining_steps: "6 < Transformation.remaining_steps ?transformation"
        apply(auto simp: max_def)
        by (smt (z3) add.commute add_2_eq_Suc' diff_add_inverse2 diff_is_0_eq le_less_Suc_eq length_greater_0_conv leftLength mult_Suc Stack_Proof.size_not_empty not_le not_less_eq numeral_3_eq_3 numeral_Bit0 Stack_Proof.size_list_length old_size)
        
      from False have invar: "Transformation.invar ?transformation"
        apply(auto simp: Stack_Proof.size_list_length popN_drop left_not_empty)
           apply (metis Idle.invar.simps Idle_Proof.invar_push diff_le_self Stack_Proof.size_list_length)
          apply (simp add: reverseN_take)
        apply (smt (verit, best) popN_drop Suc_leI diff_add_inverse diff_add_inverse2 diff_diff_left helper4 le_eq_less_or_eq left_not_empty length_drop mult_Suc numeral_3_eq_3 plus_1_eq_Suc reverseN_reverseN Stack_Proof.size_list_length old_size)
        by (metis Idle.invar.simps Idle_Proof.invar_push add_Suc_right diff_add_inverse Stack_Proof.size_list_length)

      with remaining_steps have "5 < Transformation.remaining_steps (step ?transformation)"
        using remaining_steps_decline_3[of ?transformation 5] by auto

      with invar have "4 < Transformation.remaining_steps ((step ^^ 2) ?transformation)"
        using invar_n_steps invar_step remaining_steps_decline_4[of ?transformation 4 1]
        by (smt (z3) add.commute add_Suc_right funpow_0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remaining_steps remaining_steps_decline_4)

      with remaining_steps have remaining_steps_end: "0 < Transformation.remaining_steps (six_steps ?transformation)"
        using remaining_steps_decline_4[of ?transformation 5 5] 
        by (smt (z3) One_nat_def Suc_eq_plus1 add_Suc_right invar numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remaining_steps_decline_4)

 
      from False left_not_empty have size_ok: "size_ok' ?transformation (remaining_steps ?transformation - 6)"
        apply(auto simp: max_def old_size leftLength)
        subgoal
          proof(induction "Stack.size left + Stack.size right \<le> 4")
            case True
            then show ?case
              apply(auto)
              by (smt (z3) add_Suc_shift add_diff_cancel_right' add_leE diff_zero first_pop length_Cons less_Suc_eq_le mult.commute mult_2_right mult_Suc_right not_less_eq numeral_3_eq_3 numeral_Bit0 Stack_Proof.size_list_length)
          next
            case False
            then show ?case
              by auto
          qed
        using old_size leftLength
              Stack_Proof.size_not_empty[of left] 
              Stack_Proof.size_not_empty[of right] 
              size_not_empty[of left'] 
              calculation_helper
        by auto

      then have "size_ok' (six_steps ?transformation) (remaining_steps (six_steps ?transformation))"
        using size_ok_steps invar remaining_steps by blast

      then have six_steps_size_ok: "size_ok (six_steps ?transformation)"
        using size_ok'_size_ok
        using n_steps_size_ok size_ok by blast

     from invar have "Transformation.invar (six_steps ?transformation)"
       using invar_n_steps by blast

      with False six_steps_size_ok show ?case
        apply(auto simp: Let_def split: idle.splits)
        using remaining_steps_end by simp
     qed
  qed
next
  case (6 x left right)
  let ?newLeft = "Small.push x left"
  let ?newTransfomation = "Left ?newLeft right"
  let ?steppedTransformation = "four_steps ?newTransfomation"

  have start_size_ok: "size_ok (Left left right)"
    using "6.prems" invar.simps(6) by blast

  from 6 have invar: "Transformation.invar ?newTransfomation"
    by (meson invar.simps(6) Transformation.invar.simps(1) invar_push_small)

  then have invar_four_steps: "Transformation.invar (four_steps ?newTransfomation)"
    using invar_n_steps by blast

  with 6 show ?case
  proof(induction "remaining_steps (Left left right) > 4")
    case True
    then have states_invar: "States.invar (right, left)" by auto
    from True have states_rem: "4 \<le> States.remaining_steps (right, left)" by auto
    from True have states_size_ok: "States.size_ok (right, left)" by auto
    
    from True have "remaining_steps ?newTransfomation > 4"
      by (metis Transformation.remaining_steps.simps(1) remaining_steps_push_small states_invar)

    then have remaining_steps: "remaining_steps ?steppedTransformation > 0"
      by (metis One_nat_def add_Suc_shift funpow_0 invar numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remaining_steps_decline_4)

    from True have size_ok: "size_ok ?steppedTransformation"
      using step_4_push_small_size_ok[of right left x] states_invar states_rem states_size_ok size_ok_states_left by auto

    have "case ?steppedTransformation of
      Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using step_same_left[of ?newLeft right] remaining_steps_not_idle[of ?steppedTransformation]
      apply(auto split: prod.splits transformation.splits Small.state.splits Big.state.splits Common.state.splits)
      using remaining_steps by auto

    then have "(case ?steppedTransformation of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?steppedTransformation) = Transforming ?steppedTransformation"
      by(auto split: transformation.splits Small.state.splits Common.state.splits Big.state.splits)

    with True  have "invar (case ?steppedTransformation of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?steppedTransformation)"
      by (smt (z3) invar.simps(6) remaining_steps size_ok) 

    with True show ?case
      by(auto simp: Let_def)

  next
    case False
    then have "remaining_steps ?newTransfomation \<le> 4"
      by (metis invar.simps(6) Transformation.invar.simps(1) Transformation.remaining_steps.simps(1) leI remaining_steps_push_small)

    with False have remaining_steps: "remaining_steps ?steppedTransformation = 0"
      using invar remaining_steps_decline_5[of ?newTransfomation 4]
      by auto

    obtain steppedL steppedR where stepped: "?steppedTransformation = Left steppedL steppedR"
      using step_same_left_n[of 4 ?newLeft right]
      by (simp add: case_prod_unfold numeral_Bit0)

    with remaining_steps have "case Left steppedL steppedR of
      Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" using remaining_steps_left_idle[of ] step_same_left
      using invar_four_steps by auto

    then obtain l idleL r idleR where idle: "Left steppedL steppedR = 
      Left (Small.state.Common (state.Idle l idleL)) (Big.state.Common (state.Idle r idleR))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have transformation_invar: "Transformation.invar (Left steppedL steppedR)"
      using False
      using \<open>four_steps (Left (Small.push x left) right) = Left steppedL steppedR\<close>
      by auto

    with stepped invar_four_steps have "Big.size_new right = Big.size_new steppedR"
      using invar step_n_left_size_new_big by blast

    have left_sizes_1: "Small.size ?newLeft = Suc (Small.size left)"
      by (meson "6.prems" invar.simps(6) Transformation.invar.simps(1) funpow_0 step_n_push_size_small)

    with stepped invar_four_steps have left_sizes: "Small.size_new ?newLeft = Small.size_new steppedL"
      using invar step_n_left_size_new_small by blast

    then have "0 < Small.size_new left"
      using "6.prems" invar.simps(6) size_ok.simps(1) Transformation.invar.simps(1) size_ok_size_new_small by blast

    then have "0 < Small.size_new ?newLeft"
      using \<open>Small.size (Small.push x left) = Suc (Small.size left)\<close> invar Small_Proof.size_size_new by fastforce

    then have "0 < Small.size_new steppedL"
      by (simp add: \<open>Small.size_new (Small.push x left) = Small.size_new steppedL\<close>)

    then have "0 < Big.size_new right"
      using "6.prems" invar.simps(6) size_ok.simps(1) Transformation.invar.simps(1) size_ok_size_new_big by blast

    then have right_not_empty: "0 < Big.size_new steppedR"
      by (simp add: \<open>Big.size_new right = Big.size_new steppedR\<close>)

    have left_size: "Idle.size idleL = Small.size_new steppedL"
      using idle transformation_invar by auto

    have right_size: "Idle.size idleR = Big.size_new steppedR"
      using idle transformation_invar by auto

    have wind2: "Small.size_new left \<le> 3 * Big.size_new right - 1"
      using start_size_ok
      by auto

    have "Suc (Small.size_new left) = Small.size_new ?newLeft"
      by (metis "6.prems" invar.simps(6) Transformation.invar.simps(1) funpow_0 step_n_push_size_new_small)

    with wind2 have "Small.size_new ?newLeft \<le> 3 * Big.size_new right"
      using \<open>0 < Big.size_new right\<close> by linarith

    then have "Small.size_new steppedL \<le> 3 * Big.size_new right"  
      by (simp add: left_sizes)

    then have T: "Small.size_new steppedL \<le> 3 * Big.size_new steppedR"  
      using \<open>Big.size_new right = Big.size_new steppedR\<close> by presburger

    have "Big.size_new right \<le> 3 * Small.size_new left"
      using start_size_ok left_sizes_1
      by auto

    then have "Big.size_new right \<le> 3 * Small.size_new ?newLeft"
      using left_sizes_1
      by (metis (no_types, opaque_lifting) "6.prems" invar.simps(6) Transformation.invar.simps(1) dual_order.trans funpow_0 le_add2 mult_le_mono2 plus_1_eq_Suc step_n_push_size_new_small)

    then have "Big.size_new right \<le> 3 * Small.size_new steppedL"
      by (simp add: left_sizes)

    then have "Big.size_new steppedR \<le> 3 * Small.size_new steppedL"
      by (simp add: \<open>Big.size_new right = Big.size_new steppedR\<close>)
    
    with idle transformation_invar T have "invar (Idle idleL idleR)"
      apply auto
      apply (metis Common.size_new.simps(1) Idle.is_empty.elims(2) Idle.size.simps Small.size_new.simps(1) \<open>0 < Small.size_new (Small.push x left)\<close> \<open>Small.size_new (Small.push x left) = Small.size_new steppedL\<close> list.size(3) Stack_Proof.size_list_length Stack_Proof.list_not_empty verit_comp_simplify1(1))
      using right_not_empty Idle_Proof.not_empty by auto
     
     with False have "invar(case Left steppedL steppedR of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming (Left steppedL steppedR))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

     with False show ?case
       by (metis \<open>four_steps (transformation.Left (Small.push x left) right) = transformation.Left steppedL steppedR\<close> enqL.simps(6))
   qed
next
  case (7 x left right)
  let ?newLeft = "Big.push x left"
  let ?newTransfomation = "Right ?newLeft right"
  let ?steppedTransformation = "four_steps ?newTransfomation"

  have start_size_ok: "size_ok (Right left right)"
    using "7.prems" invar.simps(6) by blast

  from 7 have invar: "Transformation.invar ?newTransfomation"
    by (meson invar.simps(6) Transformation.invar.simps invar_push_big)

  then have invar_four_steps: "Transformation.invar (four_steps ?newTransfomation)"
    using invar_n_steps by blast

  with 7 show ?case
  proof(induction "remaining_steps (Right left right) > 4")
    case True
    then have states_invar: "States.invar (left, right)" by auto
    from True have states_rem: "4 \<le> States.remaining_steps (left, right)" by auto
    from True have states_size_ok: "States.size_ok (left, right)" by auto
    
    from True have "remaining_steps ?newTransfomation > 4"
      by (metis remaining_steps.simps(2) remaining_steps_push_big states_invar)

    then have remaining_steps: "remaining_steps ?steppedTransformation > 0"
      by (metis One_nat_def add_Suc_shift funpow_0 invar numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remaining_steps_decline_4)

    from True have size_ok: "size_ok ?steppedTransformation"
      using step_4_push_big_size_ok[of left right x] states_invar states_rem states_size_ok size_ok_states_right
      by blast

    have "case ?steppedTransformation of
      Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using step_same_right[of ?newLeft right] remaining_steps_not_idle[of ?steppedTransformation]
      apply(auto split: prod.splits transformation.splits Small.state.splits Big.state.splits Common.state.splits)
      using remaining_steps by auto

    then have "(case ?steppedTransformation of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?steppedTransformation) = Transforming ?steppedTransformation"
      by(auto split: transformation.splits Small.state.splits Common.state.splits Big.state.splits)

    with True  have "invar (case ?steppedTransformation of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?steppedTransformation)"
      by (smt (z3) invar.simps(6) remaining_steps size_ok) 

    with True show ?case
      by(auto simp: Let_def)

  next
    case False
    then have "remaining_steps ?newTransfomation \<le> 4"
      by (metis invar.simps(6) Transformation.invar.simps(2) remaining_steps.simps(2) leI remaining_steps_push_big)

    with False have remaining_steps: "remaining_steps ?steppedTransformation = 0"
      using invar remaining_steps_decline_5[of ?newTransfomation 4]
      by auto

    obtain steppedL steppedR where stepped: "?steppedTransformation = Right steppedL steppedR"
      using step_same_right_n[of 4 ?newLeft right]
      by (simp add: case_prod_unfold numeral_Bit0)

    with remaining_steps have "case Right steppedL steppedR of
      Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" using remaining_steps_right_idle step_same_right
      using invar_four_steps by auto

    then obtain l idleL r idleR where idle: "Right steppedL steppedR = 
      Right (Big.state.Common (state.Idle l idleL)) (Small.state.Common (state.Idle r idleR))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have transformation_invar: "Transformation.invar (Right steppedL steppedR)"
      using False
      using \<open>four_steps (Right (Big.push x left) right) = Right steppedL steppedR\<close>
      by auto

    with stepped invar_four_steps have "Small.size_new right = Small.size_new steppedR"
      using invar step_n_right_size_new_small by blast

    have left_sizes_1: "Big.size ?newLeft = Suc (Big.size left)"
      using "7.prems" Big_Proof.size_push by fastforce

    with stepped invar_four_steps have left_sizes: "Big.size_new ?newLeft = Big.size_new steppedL" 
      using invar step_n_right_size_new_big by blast

    then have "0 < Big.size_new left"
     using "7.prems" invar.simps(6) size_ok.simps(1) Transformation.invar.simps(1) size_ok_size_new_big
     by fastforce

    then have "0 < Big.size_new ?newLeft"
      using \<open>Big.size (Big.push x left) = Suc (Big.size left)\<close> invar Big_Proof.size_size_new by fastforce

    then have "0 < Big.size_new steppedL"
      by (simp add: \<open>Big.size_new (Big.push x left) = Big.size_new steppedL\<close>)

    then have "0 < Small.size_new right"
      using "7.prems" invar.simps size_ok.simps Transformation.invar.simps size_ok_size_new_small
      by fastforce

    then have right_not_empty: "0 < Small.size_new steppedR"
      by (simp add: \<open>Small.size_new right = Small.size_new steppedR\<close>)

    have left_size: "Idle.size idleL = Big.size_new steppedL"
      using idle transformation_invar by auto

    have right_size: "Idle.size idleR = Small.size_new steppedR"
      using idle transformation_invar by auto

    have size_ok_2: "Big.size_new left \<le> 3 * Small.size_new right - 1"
      using start_size_ok
      by auto

    have "Suc (Big.size_new left) = Big.size_new ?newLeft"
      using "7.prems" Big_Proof.size_new_push by fastforce

    with size_ok_2 have "Big.size_new ?newLeft \<le> 3 * Small.size_new right"
      using \<open>0 < Small.size_new right\<close> by linarith

    then have "Big.size_new steppedL \<le> 3 * Small.size_new right"  
      by (simp add: left_sizes)

    then have T: "Big.size_new steppedL \<le> 3 * Small.size_new steppedR"  
      using \<open>Small.size_new right = Small.size_new steppedR\<close> by presburger

    have "Small.size_new right \<le> 3 * Big.size_new left"
      using start_size_ok left_sizes_1
      by auto

    then have "Small.size_new right \<le> 3 * Big.size_new ?newLeft"
      using left_sizes_1
      using \<open>Suc (Big.size_new left) = Big.size_new (Big.push x left)\<close> by linarith

    then have "Small.size_new right \<le> 3 * Big.size_new steppedL"
      by (simp add: left_sizes)

    then have "Small.size_new steppedR \<le> 3 * Big.size_new steppedL"
      by (simp add: \<open>Small.size_new right = Small.size_new steppedR\<close>)
    
    with idle transformation_invar T have "invar (Idle idleL idleR)"
      apply auto
      apply (metis Idle.is_empty.elims(2) Idle.size.simps Stack_Proof.size_empty Suc_neq_Zero \<open>Suc (Big.size_new left) = Big.size_new (Big.push x left)\<close> left_size left_sizes)
      using right_not_empty Idle_Proof.not_empty by auto
     
     with False  have "invar (case Right steppedL steppedR of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming (Right steppedL steppedR))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

     with False show ?case
      by (metis enqL.simps(7) stepped)
  qed
qed

end

