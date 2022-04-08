theory RealTimeDeque_Dequeue
  imports Deque RealTimeDeque Transforming_Proof
begin

lemma idle_pop_list: "\<lbrakk>Idle.pop left = (x, idle.Idle left' leftLength'); Idle.invar left\<rbrakk>
   \<Longrightarrow>  Stack.list left' = tl (Idle.list left)"
  apply(induction left rule: Idle.pop.induct)
  apply auto
  by (metis Stack.is_empty.elims(2) Stack.pop.simps(1) Stack_Proof.pop_list list_empty list.sel(2))

lemma list_deqL': "\<lbrakk>invar deque; listL deque \<noteq> []; deqL' deque = (x', deque')\<rbrakk>
   \<Longrightarrow> x' # listL deque' = listL deque"
proof(induction deque arbitrary: x' rule: deqL'.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 x y)
  then show ?case by auto
next
  case (3 x y z)
  then show ?case by auto
next
  case (4 left right rightLength)

  then obtain x left' leftLength' where "Idle.pop left = (x, (idle.Idle left' leftLength'))"
    using Idle.push.cases by blast

  with 4 show ?case
  proof(induction "3 * leftLength' \<ge> rightLength")
    case True
    then show ?case 
      apply auto
      by (metis Idle.list.simps Idle_Proof.pop_list)+
  next
    case False
    then show ?case
    proof(induction "leftLength' \<ge> 1")
      case True
      let ?states = "
       Left (Reverse1 (Current [] 0 left' (Suc (2 * leftLength'))) left' [])
            (Reverse (Current [] 0 right (Stack.size right - Suc leftLength')) right [] (Stack.size right - Suc leftLength'))"

      from True have invariant: "Transforming.invar ?states"
        apply(auto simp: Let_def Stack_Proof.size_list_length)
        apply (metis reverseN_reverseN reverseN_take append_Nil2)
        apply (metis Idle.invar.simps Idle_Proof.invar_pop eq_imp_le le_SucI mult_2 Stack_Proof.size_list_length trans_le_add2)
        apply(auto simp: reverseN_take)
        subgoal 
          apply(auto simp: popN_drop popN_size)
          by (smt (z3) Idle.invar.simps Idle_Proof.invar_pop add_Suc_right add_le_imp_le_diff append_take_drop_id le_refl length_rev mult_2 mult_Suc not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 rev_append rev_rev_ident Stack_Proof.size_list_length take_all_iff trans_le_add2)
        apply (metis Idle.invar.simps Idle_Proof.invar_pop Suc_diff_le diff_add_inverse le_add1 mult_2 Stack_Proof.size_list_length)
        apply (metis Idle.invar.simps Idle_Proof.invar_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 Stack_Proof.size_list_length trans_le_add2)
        apply (metis Idle.invar.simps Idle_Proof.invar_pop le_SucI le_add1 mult_2 Stack_Proof.size_list_length)
        apply (metis Idle.is_empty.elims(3) Idle.list.simps \<open>\<lbrakk>Suc 0 \<le> leftLength'; \<not> List.length (Stack.list right) \<le> 3 * leftLength'; Idle.pop left = (x', idle.Idle left' leftLength'); Idle.invar left; x = x'; deque' = Transforming (six_steps (states.Left (Reverse1 (Current [] 0 left' (Suc (2 * leftLength'))) left' []) (Reverse (Current [] 0 right (List.length (Stack.list right) - Suc leftLength')) right [] (List.length (Stack.list right) - Suc leftLength')))); rightLength = List.length (Stack.list right); \<not> Idle.is_empty left; \<not> Stack.is_empty right; Idle.size left \<le> 3 * List.length (Stack.list right); List.length (Stack.list right) \<le> 3 * Idle.size left; Idle.list left \<noteq> []\<rbrakk> \<Longrightarrow> rev (take (Suc (2 * leftLength') - List.length (Stack.list ((Stack.pop ^^ (List.length (Stack.list right) - Suc leftLength')) right))) (rev (take (List.length (Stack.list right) - Suc leftLength') (Stack.list left')))) @ rev (Stack.list ((Stack.pop ^^ (List.length (Stack.list right) - Suc leftLength')) right)) @ rev (take (List.length (Stack.list right) - Suc leftLength') (Stack.list right)) = Stack.list left' @ rev (Stack.list right)\<close> Stack_Proof.list_not_empty)
        apply (metis Idle.invar.simps Idle_Proof.invar_pop Suc_diff_le add_diff_cancel_right' le_add2 mult_2 Stack_Proof.size_list_length)
        by (metis Idle.invar.simps Idle_Proof.invar_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 Stack_Proof.size_list_length trans_le_add2)

      with True have "Transforming.listL ?states = tl (Idle.list left) @ rev (Stack.list right)"
        by(auto simp: idle_pop_list)

      with invariant have "Transforming.listL (six_steps ?states) = tl (Idle.list left) @ rev (Stack.list right)"
        by (auto simp: n_steps)

      with True show ?case 
        apply(auto simp: Let_def invar_n_steps step_list split: prod.splits)
        apply (metis Idle.list.simps Idle_Proof.pop_list idle_pop_list)
        by (metis Idle.list.simps Idle_Proof.pop_list idle_pop_list)

    next
      case False
      obtain right1 right2 where "right = Stack right1 right2"
        using Stack.list.cases by blast

      with False show ?case 
        apply(induction right1 right2 rule: small_deque.induct)
        apply(auto simp: Idle_Proof.invar_pop Idle_Proof.size_pop)
        apply (metis Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Suc_leI gr_zeroI length_0_conv pop_list_2 size_list_length)
        apply (metis (mono_tags, lifting) Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list le_zero_eq length_0_conv not_less_eq_eq Stack_Proof.size_list_length)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) not_less_eq_eq same_append_eq Stack_Proof.size_list_length tl_append2)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) not_less_eq_eq same_append_eq Stack_Proof.size_list_length tl_append2)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) not_less_eq_eq same_append_eq Stack_Proof.size_list_length tl_append2)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) not_less_eq_eq same_append_eq Stack_Proof.size_list_length tl_append2)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) not_less_eq_eq same_append_eq Stack_Proof.size_list_length tl_append2)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) not_less_eq_eq same_append_eq Stack_Proof.size_list_length tl_append2)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) not_less_eq_eq same_append_eq Stack_Proof.size_list_length tl_append2)
        using Idle_Proof.invar_pop Idle_Proof.size_pop by fastforce+
    qed
  qed    
    
next
  case (5 left right)

  then have start_invar: "Transforming.invar (Left left right)"
    by auto

  from 5 have left_invar: "Small.invar left"
    by auto

  from 5 have leftSize: "0 < Small.size left"
    by auto

  with 5(3) obtain left' where pop: "Small.pop left = (x', left')"
    by(auto simp: Let_def split: prod.splits states.splits Small.state.splits Common.state.splits Big.state.splits)

  let ?newTransfomation = "Left left' right"
  let ?steppedTransforming = "four_steps ?newTransfomation"

  have invar: "Transforming.invar ?newTransfomation"
    using pop start_invar leftSize invar_pop_small_left[of left right x' left']
    by auto

  have "x' # Small.list_current left' = Small.list_current left"
    using left_invar leftSize pop Small_Proof.pop_list_current[of left x' left'] by auto
    
  then have listL: "x' # Transforming.listL ?newTransfomation = Small.list_current left @ rev (Big.list_current right)"
    using invar leftSize Small_Proof.pop_list_current[of left x' left'] 5(1)
    by auto      

  from invar have n_steps: "Transforming.invar ?steppedTransforming"
    using invar_n_steps by blast

  then have 1: "x' # Transforming.listL ?steppedTransforming = Small.list_current left @ rev (Big.list_current right)"
    using Transforming_Proof.n_steps invar listL by metis

  then have 2: "listL (deqL (Transforming (Left left right))) = Transforming.listL ?steppedTransforming"
    apply(auto simp: Let_def split: prod.splits states.splits Small.state.splits)
       apply (simp add: local.pop)+
     apply(auto split: Common.state.splits Big.state.splits)
    by (simp add: local.pop)

  with 1 have 3: "x' # listL (deqL (Transforming (Left left right))) = Small.list_current left @ rev (Big.list_current right)"
    by auto

  with 5(1) have 4: "listL (Transforming (Left left right)) = Small.list_current left @ rev (Big.list_current right)"
    by auto

  from 3 4 have "x' # listL (deqL (Transforming (Left left right))) = listL (Transforming (Left left right))"
    by auto

  with 5 show ?case by auto
next
  case (6 left right)
  then have start_invar: "Transforming.invar (Right left right)"
    by auto

  from 6 have left_invar: "Big.invar left"
    by auto

  from 6 have leftSize: "0 < Big.size left"
    by auto

  with 6(3) obtain left' where pop: "Big.pop left = (x', left')"
    by(auto simp: Let_def split: prod.splits states.splits Small.state.splits Common.state.splits Big.state.splits)

  let ?newTransfomation = "Right left' right"
  let ?steppedTransforming = "four_steps ?newTransfomation"

  have invar: "Transforming.invar ?newTransfomation"
    using pop start_invar leftSize invar_pop_big_right[of left right x' left']
    by auto

  have "x' # Big.list_current left' = Big.list_current left"
    using left_invar leftSize pop Big_Proof.pop_list_current[of left x' left'] by auto
    
  then have listL: "x' # Transforming.listL ?newTransfomation = Big.list_current left @ rev (Small.list_current right)"
    using left_invar invar leftSize Big_Proof.pop_list_current[of left x' left'] 6(1)
    by (metis States.lists_current.simps Transforming.invar.simps(2) append_Cons invar_list_big_first old.prod.case list_current_big_first.simps Transforming.listL.simps(2))

  from invar have four_steps: "Transforming.invar ?steppedTransforming"
    using invar_n_steps by blast

  then have 1: "x' # Transforming.listL ?steppedTransforming = Big.list_current left @ rev (Small.list_current right)"
    using Transforming_Proof.n_steps invar listL
    by metis

  then have 2: "listL (deqL (Transforming (Right left right))) = Transforming.listL ?steppedTransforming"
    apply(auto simp: Let_def split: prod.splits states.splits Small.state.splits)
       apply (simp add: local.pop)+
    by(auto split: Common.state.splits Big.state.splits Small.state.splits)

  with 1 have 3: "x' # listL (deqL (Transforming (Right left right))) = Big.list_current left @ rev (Small.list_current right)"
    by auto

  with 6(1) have 4: "listL (Transforming (Right left right)) = Big.list_current left @ rev (Small.list_current right)"
    using invar_list_big_first by fastforce

  from 3 4 have "x' # listL (deqL (Transforming (Right left right))) = listL (Transforming (Right left right))"
    by auto

  with 6 show ?case by auto
next
  case 7
  then show ?case by auto
qed

lemma list_deqL:
    "\<lbrakk>invar deque; listL deque \<noteq> []\<rbrakk> \<Longrightarrow> listL (deqL deque) = tl (listL deque)"
  using list_deqL' apply(auto split: prod.splits)
  by (smt (z3) list.sel(3) list_deqL')

lemma list_firstL:
    "\<lbrakk>invar deque; listL deque \<noteq> []\<rbrakk> \<Longrightarrow> firstL deque = hd (listL deque)"
  using list_deqL' apply(auto split: prod.splits)
  by (smt (z3) list.sel(1) list_deqL')

lemma step_same_left: "case step (Left small big) of Left _ _ \<Rightarrow> True | _ \<Rightarrow> False"
  by(auto split: prod.splits)

lemma step_same_left_n: "case (step ^^ n) (Left small big) of Left _ _ \<Rightarrow> True | _ \<Rightarrow> False"
proof(induction n arbitrary: small big)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (metis (no_types, lifting) Transforming.step.simps(1) comp_def funpow_Suc_right prod.case_eq_if) 
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
    by (metis (no_types, lifting) Transforming.step.simps(2) comp_def funpow_Suc_right prod.case_eq_if) 
qed

lemma size_ok_states_left: "States.size_ok ((States.step ^^ n) (big, small))
   \<Longrightarrow> size_ok ((step ^^ n) (Left small big))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma size_ok_states_right: "States.size_ok ((States.step ^^ n) (big, small))
   \<Longrightarrow> size_ok ((step ^^ n) (Right big small))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma remaining_steps_not_idle: "Transforming.invar states \<Longrightarrow> remaining_steps states > 0 \<longleftrightarrow> (
    case states of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> False 
    | Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> False 
    | _ \<Rightarrow> True) "
  apply(induction states)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remaining_steps_left_idle: "Transforming.invar (Left small big) \<Longrightarrow> remaining_steps (Left small big) = 0 \<longleftrightarrow> (
    case (Left small big) of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remaining_steps_right_idle: "Transforming.invar (Right big small) \<Longrightarrow> remaining_steps (Right big small) = 0 \<longleftrightarrow> (
    case (Right big small) of 
      Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma invar_deqL:
    "\<lbrakk>invar deque; \<not> is_empty deque\<rbrakk> \<Longrightarrow> invar (deqL deque)"
proof(induction deque rule: deqL'.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 x y)
  then show ?case by auto
next
  case (3 x y z)
  then show ?case by auto
next
  case (4 left right rightLength)
  then show ?case
  proof(induction "Idle.pop left")
    case (Pair x left')
    then show ?case
    proof(induction left')
      case (Idle iLeft iLeftLength)
      then show ?case 
      proof(induction "Stack.size right \<le> 3 * iLeftLength")
        case True
        then show ?case 
          apply(auto split: prod.splits)
             apply (meson Idle.invar.simps Idle_Proof.invar_pop)
          apply (metis Idle.invar.simps Idle_Proof.invar_pop bot_nat_0.extremum length_0_conv mult_zero_right Stack_Proof.list_not_empty Stack_Proof.size_list_length verit_la_disequality)
           apply (metis Idle.size.simps Idle_Proof.size_pop Suc_leD)
          using Idle_Proof.invar_pop by fastforce
      next  
        case False
        then show ?case
        proof(induction "1 \<le> iLeftLength")
          case True
          let ?states = "states.Left (Reverse1 (Current [] 0 iLeft (Suc (2 * iLeftLength))) iLeft [])
            (Reverse (Current [] 0 right (Stack.size right - Suc iLeftLength)) right [] (Stack.size right - Suc iLeftLength))"

          from True have invar: "Transforming.invar ?states"
            apply(auto simp: reverseN_take Stack_Proof.size_list_length)
               apply (metis Idle.invar.simps Idle_Proof.invar_pop le_SucI le_add2 mult_2 Stack_Proof.size_list_length)
            subgoal apply(auto simp: popN_size popN_drop)
              by (smt (z3) Idle.invar.simps Idle_Proof.invar_pop add_Suc_right add_le_imp_le_diff append_take_drop_id le_refl length_rev mult_2 mult_Suc not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 rev_append rev_rev_ident Stack_Proof.size_list_length take_all_iff trans_le_add2)
            apply (metis Idle.invar.simps Idle_Proof.invar_pop Suc_diff_le diff_add_inverse diff_le_self mult_2 Stack_Proof.size_list_length)
            by (metis Idle.invar.simps Idle_Proof.invar_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 Stack_Proof.size_list_length trans_le_add2)

          then have invar_six: "Transforming.invar (six_steps ?states)"
            using invar_n_steps by blast

          from True have remaining_steps: "6 < Transforming.remaining_steps ?states"
            by(auto simp: max_def)

          with invar have "5 < Transforming.remaining_steps (step ?states)"
            using remaining_steps_decline_3[of ?states 5] by auto

          with invar have "4 < Transforming.remaining_steps ((step ^^ 2) ?states)"
            using invar_n_steps invar_step remaining_steps_decline_4[of ?states 4 1]
            by (smt (z3) add.commute add_Suc_right funpow_0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remaining_steps remaining_steps_decline_4)

          with remaining_steps have remaining_steps_end: "0 < Transforming.remaining_steps (six_steps ?states)"
            using remaining_steps_decline_4[of ?states 5 5] 
            by (smt (z3) One_nat_def Suc_eq_plus1 add_Suc_right invar numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remaining_steps_decline_4)
          
          from True have idleLength: "Stack.size iLeft = iLeftLength"
            apply auto
            by (metis Idle.invar.simps Idle_Proof.invar_pop)

          from True have size_ok': "size_ok' ?states (remaining_steps ?states - 6)"
            apply(auto simp: max_def idleLength)
            apply (smt (z3) Idle.invar.simps Idle.size.simps Idle_Proof.invar_pop Idle_Proof.size_pop Suc_eq_plus1 diff_add_inverse2 diff_commute diff_diff_left diff_is_0_eq mult.commute mult_2_right mult_Suc_right numeral_2_eq_2 numeral_3_eq_3)
            by (smt (z3) Idle.size.simps Idle_Proof.size_pop add_2_eq_Suc diff_Suc_diff_eq1 diff_add_inverse diff_commute diff_diff_left diff_is_0_eq le_add1 idleLength mult_2 mult_Suc mult_Suc_right numeral_2_eq_2 numeral_3_eq_3)
  
          then have size_ok: "size_ok (six_steps ?states)"
            using size_ok_steps invar remaining_steps size_ok'_size_ok by blast
  
          with True invar_six size_ok show ?case
            by(auto simp: Let_def remaining_steps_end split: prod.splits)
     
        next
          case False

          then  have 0: "iLeftLength = 0"
            by auto

          with False have "Idle.size left = 1"
            apply auto
            by (metis Idle.invar.simps Idle.size.simps Idle_Proof.invar_pop Idle_Proof.size_pop)

          with False have "rightLength < 4"
            by auto

          with False show ?case
            apply(auto split: prod.splits stack.splits)
            subgoal for x1 x2
              apply(induction x1 x2 rule: small_deque.induct)
              by auto
            done
        qed
      qed
    qed
  qed
next
  case (5 left right)
 
  obtain x newLeft where popped: "Small.pop left = (x, newLeft)"
    by fastforce

  let ?newTransfomation = "Left newLeft right"
  let ?steppedTransforming = "four_steps ?newTransfomation"

  have start_size_ok: "size_ok (Left left right)"
    using "5.prems" RealTimeDeque.invar.simps(6) by blast

  from 5 have invar: "Transforming.invar ?newTransfomation"
    by (meson RealTimeDeque.invar.simps(6) Transforming.size_ok.simps(1) invar_pop_small_left size_ok_size_small popped)

  then have invar_four_steps: "Transforming.invar (four_steps ?newTransfomation)"
    using invar_n_steps by blast

  have last_steps:  "False = (4 < remaining_steps (Left newLeft right)) \<Longrightarrow> 
    invar (deqL (Transforming (Left left right)))"
  proof -
    assume steps: "False = (4 < remaining_steps (Left newLeft right))"

    then have "remaining_steps ?newTransfomation \<le> 4"
        using not_less by blast

    with 5 have no_remaining_steps: "remaining_steps ?steppedTransforming = 0"
      using invar remaining_steps_decline_5[of ?newTransfomation 4]
      by auto

    from 5 have left_not_empty: "0 < Small.size left" 
      by auto

    from 5 have states_invar: "States.invar (right, left)" 
      by auto

    from 5 have states_size_ok: "States.size_ok (right, left)" 
      by auto

    obtain steppedL steppedR where stepped: "?steppedTransforming = Left steppedL steppedR"
      using step_same_left_n[of 4 newLeft right]
      by (simp add: case_prod_unfold numeral_Bit0)

    with no_remaining_steps have "case Left steppedL steppedR of
      Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" using remaining_steps_left_idle[of ] step_same_left
      using invar_four_steps by auto

    then obtain l idleL r idleR where idle: "Left steppedL steppedR = 
      Left (Small.state.Common (state.Idle l idleL)) (Big.state.Common (state.Idle r idleR))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have states_invar: "Transforming.invar (Left steppedL steppedR)"
      using 5 \<open>four_steps (Left newLeft right) = Left steppedL steppedR\<close>
      by (metis invar_four_steps)

    with stepped invar_four_steps 
    have size_new_right: "Big.size_new right = Big.size_new steppedR"
      using invar step_n_left_size_new_big by blast

    have size_new_left: "Suc (Small.size_new newLeft) = Small.size_new left"
      by (metis left_not_empty funpow_0 step_n_pop_size_new_small states_invar popped)

    with stepped invar_four_steps 
    have size_new_stepped_left: "Small.size_new newLeft = Small.size_new steppedL"
      using invar step_n_left_size_new_small by blast

    have previous_steps: "0 < remaining_steps (Left left right)"
      using "5.prems"(1) invar.simps(6) by blast 

    with start_size_ok size_ok_size_new_big states_size_ok
    have "1 < Small.size_new left"
      by auto

    then have "0 < Small.size_new newLeft"
      using size_new_left
      by linarith

    then have left_not_empty: "0 < Small.size_new steppedL" 
      using size_new_stepped_left by auto

    then have "0 < Big.size_new right"
      using "5.prems" RealTimeDeque.invar.simps(6) Transforming.size_ok.simps(1) Transforming.invar.simps(1) size_ok_size_new_big by blast

    then have right_not_empty: "0 < Big.size_new steppedR"
      by (simp add: size_new_right)

    have left_size: "Idle.size idleL = Small.size_new steppedL"
      using idle states_invar by auto

    have right_size: "Idle.size idleR = Big.size_new steppedR"
      using idle states_invar by auto

    have "Small.size_new left \<le> 3 * Big.size_new right" 
      using start_size_ok by auto
    
    with size_new_left have "Small.size_new newLeft \<le> 3 * Big.size_new right" 
      by auto

    then have stepped_size_ok: "Small.size_new steppedL \<le> 3 * Big.size_new steppedR"  
      using size_new_right size_new_stepped_left by presburger

    have not_empty_idleL: "0 < Idle.size idleL"
      using left_size left_not_empty by auto

    have "4 * Big.size_new right + (States.remaining_steps (right, left)) \<le> 12 * Small.size_new left - (3 * States.remaining_steps (right, left)) - 8"
      using start_size_ok by auto 

    then have "4 * Big.size_new right + 1 \<le> 12 * Small.size_new left - 3 - 8"
      using previous_steps by auto

    then have "Big.size_new right \<le> 3 * Small.size_new newLeft"
      using size_new_left by auto

    then have "Big.size_new right \<le> 3 * Small.size_new steppedL"
      by (simp add: size_new_stepped_left)

    then have "Big.size_new steppedR \<le> 3 * Small.size_new steppedL"
      by (simp add: \<open>Big.size_new right = Big.size_new steppedR\<close>)
    
    with idle states_invar stepped_size_ok
    have "invar (Idle idleL idleR)"
      using right_not_empty Idle_Proof.not_empty left_size left_not_empty apply auto
      using not_empty_idleL by blast
     
     with 5 have invar_stepped: "invar (case Left steppedL steppedR of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming (Left steppedL steppedR))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle states.inject(1) states.simps(5) by auto

     have "(case Left steppedL steppedR of
       Left (Small.state.Common (state.Idle _ left)) (Big.state.Common (state.Idle x_ right)) \<Rightarrow> deque.Idle left right
    | _ \<Rightarrow> Transforming (states.Left steppedL steppedR)) = Idle idleL idleR"
       by (simp add: idle)

     have "deqL (Transforming (Left left right)) = (case ?steppedTransforming of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?steppedTransforming)"
       by(auto simp: popped Let_def split: prod.splits states.splits Small.state.splits Common.state.splits Big.state.splits)

     with stepped have "deqL (Transforming (Left left right)) = (case Left steppedL steppedR of 
      Left 
        (Small.Common (Common.Idle _ left)) 
        (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming (Left steppedL steppedR))"
      by metis

     with 5 invar_stepped show ?case
        by auto
    qed

  with 5 show ?case
  proof(induction "remaining_steps (Left left right) > 4")
    case True
    then have states_invar: "States.invar (right, left)" by auto
    from True have states_rem: "4 \<le> States.remaining_steps (right, left)" by auto
    from True have states_window: "States.size_ok (right, left)" by auto
    from True have "0 < Small.size left" by auto


    from 5 show ?case 
    proof(induction "remaining_steps ?newTransfomation > 4")
      case True
      
      with True have "remaining_steps ?newTransfomation > 4"
        by auto

      then have remaining_steps: "remaining_steps ?steppedTransforming > 0"
        by (metis One_nat_def add_Suc_shift funpow_0 invar numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remaining_steps_decline_4)

      from True have size_ok: "size_ok ?steppedTransforming"
        using step_4_pop_small_size_ok[of right left x] states_invar states_rem states_window size_ok_states_left
        by (metis Transforming.remaining_steps.simps(1) \<open>0 < Small.size left\<close> size_ok_states_left less_imp_le_nat popped)

      have "case ?steppedTransforming of
        Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> False
      | _ \<Rightarrow> True"
        using step_same_left[of newLeft right] remaining_steps_not_idle[of ?steppedTransforming]
        apply(auto split: prod.splits states.splits Small.state.splits Big.state.splits Common.state.splits)
        using remaining_steps by auto

      then have "(case ?steppedTransforming of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?steppedTransforming) = Transforming ?steppedTransforming"
        by(auto split: states.splits Small.state.splits Common.state.splits Big.state.splits)

      with True  have "invar (case ?steppedTransforming of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?steppedTransforming)"
        by (smt (z3) RealTimeDeque.invar.simps(6) invar_four_steps remaining_steps size_ok)

      then have "invar
          (case 
                  (case four_steps (states.Left newLeft right) of
                        Left (Small.state.Common (state.Idle _ left')) (Big.state.Common (state.Idle _ right)) \<Rightarrow> (x, Idle left' right)
                      | _ \<Rightarrow> (x, Transforming ?steppedTransforming)) of
           (x, deque) \<Rightarrow> deque)"
        by(auto split: prod.splits states.splits Small.state.splits Big.state.splits Common.state.splits)

    with True show ?case
      apply(auto simp: Let_def split: prod.splits)
      using popped by fastforce
    
    next
      case False
      then show ?case 
        using last_steps by auto
    qed
    
  next
    case False

    then have "remaining_steps ?newTransfomation \<le> 4"
      by (metis (no_types, lifting) invar.simps(6) size_ok.simps(1) Transforming.invar.simps(1) remaining_steps.simps(1) dual_order.trans not_le_imp_less remaining_steps_pop_small size_ok_size_small popped)

    then show ?case
      using last_steps
      by auto
   qed
next
  case (6 left right)
  obtain x newLeft where popped: "Big.pop left = (x, newLeft)"
    by fastforce

  let ?newTransfomation = "Right newLeft right"
  let ?steppedTransforming = "four_steps ?newTransfomation"

  have start_size_ok: "size_ok (Right left right)"
    using "6.prems" invar.simps(6) by blast

  from 6 have invar: "Transforming.invar ?newTransfomation"
    by (meson invar.simps(6)size_ok.simps(2) invar_pop_big_right size_ok_size_big popped)

  then have invar_four_steps: "Transforming.invar (four_steps ?newTransfomation)"
    using invar_n_steps by blast

  have last_steps:  "False = (4 < Transforming.remaining_steps (Right newLeft right)) \<Longrightarrow> 
    invar (deqL (Transforming (Right left right)))"
  proof -
    assume steps: "False = (4 < Transforming.remaining_steps (Right newLeft right))"

    then have "remaining_steps ?newTransfomation \<le> 4"
        using not_less by blast

    with 6 have no_remaining_steps: "remaining_steps ?steppedTransforming = 0"
      using invar remaining_steps_decline_5[of ?newTransfomation 4]
      by auto

    from 6 have left_not_empty: "0 < Big.size left" 
      by auto

    from 6 have states_invar: "States.invar (left, right)" 
      by auto

    from 6 have states_size_ok: "States.size_ok (left, right)" 
      by auto

    obtain steppedL steppedR where stepped: "?steppedTransforming = Right steppedL steppedR"
      using step_same_left_n[of 4 right newLeft]
      by (simp add: case_prod_unfold numeral_Bit0)

    with no_remaining_steps have "case Right steppedL steppedR of
      Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" using remaining_steps_right_idle step_same_right
      using invar_four_steps by auto

    then obtain l idleL r idleR where idle: "Right steppedL steppedR = 
      Right (Big.state.Common (state.Idle l idleL)) (Small.state.Common (state.Idle r idleR))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have states_invar: "Transforming.invar (Right steppedL steppedR)"
      using 6 stepped 
      by (metis invar_four_steps)

    with stepped invar_four_steps 
    have size_new_right: "Small.size_new right = Small.size_new steppedR"
      using invar step_n_right_size_new_small
      by blast

    have size_new_left: "Suc (Big.size_new newLeft) = Big.size_new left"
      by (metis left_not_empty funpow_0 step_n_pop_size_new_big states_invar popped)

    with stepped invar_four_steps
    have size_new_steppedL: "Big.size_new newLeft = Big.size_new steppedL"
      using invar step_n_right_size_new_big by blast

    have previous_steps: "0 < remaining_steps (Right left right)"
      using "6.prems"(1) invar.simps(6) by blast 

    with start_size_ok size_ok_size_new_big states_size_ok
    have "1 < Big.size_new left"
      by auto

    then have "0 < Big.size_new newLeft"
      using size_new_left
      by linarith

    then have left_not_empty: "0 < Big.size_new steppedL" 
      using size_new_steppedL by auto

    then have "0 < Small.size_new right"
      using size_ok_size_new_small states_size_ok by blast

    then have right_not_empty: "0 < Small.size_new steppedR"
      by (simp add: size_new_right)

    have left_size: "Idle.size idleL = Big.size_new steppedL"
      using idle states_invar by auto

    have right_size: "Idle.size idleR = Small.size_new steppedR"
      using idle states_invar by auto

    have "Big.size_new left \<le> 3 * Small.size_new right" 
      using start_size_ok by auto
    
    with size_new_left have "Big.size_new newLeft \<le> 3 * Small.size_new right" 
      by auto

    then have stepped_size_ok: "Big.size_new steppedL \<le> 3 * Small.size_new steppedR"  
      using size_new_right size_new_steppedL by presburger

    have not_empty_idleL: "0 < Idle.size idleL"
      using left_size left_not_empty by auto

    have "4 * Small.size_new right + (States.remaining_steps (left, right)) \<le> 12 * Big.size_new left - (3 * States.remaining_steps (left, right)) - 8"
      using start_size_ok by auto 

    then have "4 * Small.size_new right + 1 \<le> 12 * Big.size_new left - 3 - 8"
      using previous_steps by auto

    then have "Small.size_new right \<le> 3 * Big.size_new newLeft"
      using size_new_left by auto

    then have "Small.size_new right \<le> 3 * Big.size_new steppedL"
      by (simp add: size_new_steppedL)

    then have "Small.size_new steppedR \<le> 3 * Big.size_new steppedL"
      by (simp add: size_new_right)
    
    with idle states_invar stepped_size_ok
    have "invar (Idle idleL idleR)"
      using right_not_empty Idle_Proof.not_empty left_size left_not_empty apply auto
      using not_empty_idleL by blast
     
     with 6 have invar_stepped: "invar (case Right steppedL steppedR of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming (Right steppedL steppedR))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle states.inject(1) states.simps(5) by auto

     have "(case Right steppedL steppedR of
       Right (Big.state.Common (state.Idle _ left)) (Small.state.Common (state.Idle x_ right)) \<Rightarrow> deque.Idle left right
    | _ \<Rightarrow> Transforming (Right steppedL steppedR)) = Idle idleL idleR"
       by (simp add: idle)

     have "deqL (Transforming (Right left right)) = (case ?steppedTransforming of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?steppedTransforming)"
       by(auto simp: popped Let_def split: prod.splits states.splits Small.state.splits Common.state.splits Big.state.splits)

     with stepped have "deqL (Transforming (Right left right)) = (case Right steppedL steppedR of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming (Right steppedL steppedR))"
      by metis

     with 6 invar_stepped show ?case
        by auto
    qed

  from 6 invar_four_steps show ?case
  proof(induction "remaining_steps (Right left right) > 4")
    case True
    then have states_invar: "States.invar (left, right)" by auto
    from True have states_size_ok: "States.size_ok (left, right)" by auto
    from True have "0 < Big.size left" by auto

    show ?case 
    proof(induction "remaining_steps ?newTransfomation > 4")
      case True
      with True have "remaining_steps ?newTransfomation > 4" 
        by auto

    then have remaining_steps: "remaining_steps ?steppedTransforming > 0"
      by (metis One_nat_def add_Suc_shift funpow_0 invar numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remaining_steps_decline_4)

    from True have size_ok: "size_ok ?steppedTransforming"
      using step_4_pop_big_size_ok[of left right x] states_invar states_size_ok size_ok_states_right
      by (metis Transforming.remaining_steps.simps(2) \<open>0 < Big.size left\<close> less_imp_le popped)

    have "case ?steppedTransforming of
      Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using step_same_right[of newLeft right] remaining_steps_not_idle[of ?steppedTransforming]
      apply(auto split: prod.splits states.splits Small.state.splits Big.state.splits Common.state.splits)
      using remaining_steps by auto

    then have "(case ?steppedTransforming of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?steppedTransforming) = Transforming ?steppedTransforming"
      by(auto split: states.splits Small.state.splits Common.state.splits Big.state.splits)

    with True  have "invar (case ?steppedTransforming of 
      Right 
        (Big.Common (Common.Idle _ left)) 
        (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
   | _ \<Rightarrow> Transforming ?steppedTransforming)"
      by (smt (z3) invar.simps invar_four_steps remaining_steps size_ok)

    then have "invar
        (case 
                (case four_steps (states.Right newLeft right) of
                      Right (Big.state.Common (state.Idle _ left')) (Small.state.Common (state.Idle _ right)) \<Rightarrow> (x, Idle left' right)
                    | _ \<Rightarrow> (x, Transforming ?steppedTransforming)) of
         (x, deque) \<Rightarrow> deque)"
      by(auto split: prod.splits states.splits  Big.state.splits Small.state.splits Common.state.splits)

    with True show ?case
      apply(auto simp: Let_def split: prod.splits)
      using popped by fastforce
    next
      case False
      then show ?case
      using last_steps by auto
    qed
  next
    case False
   
    then have "remaining_steps ?newTransfomation \<le> 4"
      by (metis (no_types, lifting) RealTimeDeque.invar.simps(6) Transforming.size_ok.simps Transforming.invar.simps remaining_steps.simps dual_order.trans not_le_imp_less remaining_steps_pop_big size_ok_size_big popped)

    then show ?case
      using last_steps by auto
   qed
next
  case 7
  then show ?case by auto
qed

end
