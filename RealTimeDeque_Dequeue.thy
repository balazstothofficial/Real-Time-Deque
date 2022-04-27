theory RealTimeDeque_Dequeue
  imports Deque RealTimeDeque States_Proof
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
       States Left
          (Reverse (Current [] 0 right (Stack.size right - Suc leftLength')) right [] (Stack.size right - Suc leftLength'))
          (Reverse1 (Current [] 0 left' (Suc (2 * leftLength'))) left' [])
            "

      from True have invariant: "States.invar ?states"
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
        apply (metis Idle_Proof.pop_list List.list.simps(3) \<open>\<lbrakk>Suc 0 \<le> leftLength'; \<not> List.length (Stack.list right) \<le> 3 * leftLength'; Idle.pop left = (x', idle.Idle left' leftLength'); Idle.invar left; x = x'; deque' = Transforming (six_steps (States direction.Left (Reverse (Current [] 0 right (List.length (Stack.list right) - Suc leftLength')) right [] (List.length (Stack.list right) - Suc leftLength')) (Reverse1 (Current [] 0 left' (Suc (2 * leftLength'))) left' []))); rightLength = List.length (Stack.list right); \<not> Idle.is_empty left; \<not> Stack.is_empty right; Idle.size left \<le> 3 * List.length (Stack.list right); List.length (Stack.list right) \<le> 3 * Idle.size left; Idle.list left \<noteq> []\<rbrakk> \<Longrightarrow> rev (take (Suc (2 * leftLength') - List.length (Stack.list ((Stack.pop ^^ (List.length (Stack.list right) - Suc leftLength')) right))) (rev (take (List.length (Stack.list right) - Suc leftLength') (Stack.list left')))) @ rev (Stack.list ((Stack.pop ^^ (List.length (Stack.list right) - Suc leftLength')) right)) @ rev (take (List.length (Stack.list right) - Suc leftLength') (Stack.list right)) = Stack.list left' @ rev (Stack.list right)\<close>)
          apply (metis Idle.invar.simps Idle_Proof.invar_pop Suc_diff_le add_diff_cancel_right' le_add2 mult_2 Stack_Proof.size_list_length)
        by (metis Idle.invar.simps Idle_Proof.invar_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 Stack_Proof.size_list_length trans_le_add2)

      with True have "States.listL ?states = tl (Idle.list left) @ rev (Stack.list right)"
        by(auto simp: idle_pop_list)

      with invariant have "States.listL (six_steps ?states) = tl (Idle.list left) @ rev (Stack.list right)"
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
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def le_zero_eq length_0_conv not_less_eq_eq Stack_Proof.size_list_length)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def le_zero_eq length_0_conv not_less_eq_eq Stack_Proof.size_list_length)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def le_zero_eq length_0_conv not_less_eq_eq Stack_Proof.size_list_length)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def le_zero_eq length_0_conv not_less_eq_eq Stack_Proof.size_list_length)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def le_zero_eq length_0_conv not_less_eq_eq Stack_Proof.size_list_length)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def le_zero_eq length_0_conv not_less_eq_eq Stack_Proof.size_list_length)
        apply (metis (mono_tags, lifting) False.hyps Idle.invar.simps Idle.list.simps Idle_Proof.invar_pop Idle_Proof.pop_list One_nat_def le_zero_eq length_0_conv not_less_eq_eq Stack_Proof.size_list_length)
        using Idle_Proof.invar_pop Idle_Proof.size_pop by fastforce+
    qed
  qed    
    
next
  case (5 big small)

  then have start_invar: "States.invar (States Left big small)"
    by auto

  from 5 have small_invar: "Small.invar small"
    by auto

  from 5 have smallSize: "0 < Small.size small"
    by auto

  with 5(3) obtain small' where pop: "Small.pop small = (x', small')"
    by(auto simp: Let_def split: prod.splits states.splits direction.splits Small.state.splits Common.state.splits Big.state.splits)

  let ?newStates = "States Left big small'"
  let ?steppedStates = "four_steps ?newStates"

  have invar: "States.invar ?newStates"
    using pop start_invar smallSize invar_pop_small_size
    by metis

  have "x' # Small.list_current small' = Small.list_current small"
    using small_invar smallSize pop Small_Proof.pop_list_current[of small x' small'] by auto
    
  then have listL: "x' # States.listL ?newStates = Small.list_current small @ rev (Big.list_current big)"
    using invar smallSize Small_Proof.pop_list_current[of small x' small'] 5(1)
    by auto      

  from invar have n_steps: "States.invar ?steppedStates"
    using invar_n_steps by blast

  then have 1: "x' # States.listL ?steppedStates = Small.list_current small @ rev (Big.list_current big)"
    using States_Proof.n_steps invar listL by metis

  then have 2: "listL (deqL (Transforming (States Left big small))) = States.listL ?steppedStates"
    apply(auto simp: Let_def split: prod.splits direction.splits states.splits Small.state.splits)
    apply (simp add: local.pop)+
    apply(auto split: Small.state.splits Common.state.splits Big.state.splits)
    by (simp add: local.pop)

  with 1 have 3: "x' # listL (deqL (Transforming (States Left big small))) = Small.list_current small @ rev (Big.list_current big)"
    by auto

  with 5(1) have 4: "listL (Transforming (States Left big small)) = Small.list_current small @ rev (Big.list_current big)"
    by auto

  from 3 4 have "x' # listL (deqL (Transforming (States Left big small))) = listL (Transforming (States Left big small))"
    by auto

  with 5 show ?case by auto
next
  case (6 big small)
  then have start_invar: "States.invar (States Right big small)"
    by auto

  from 6 have big_invar: "Big.invar big"
    by auto

  from 6 have bigSize: "0 < Big.size big"
    by auto

  with 6(3) obtain big' where pop: "Big.pop big = (x', big')"
    by(auto simp: Let_def split: prod.splits direction.splits states.splits Small.state.splits Common.state.splits Big.state.splits)

  let ?newStates = "States Right big' small"
  let ?steppedStates = "four_steps ?newStates"

  have invar: "States.invar ?newStates"
    using pop start_invar bigSize invar_pop_big_size
    by metis

  have "x' # Big.list_current big' = Big.list_current big"
    using big_invar bigSize pop Big_Proof.pop_list_current[of big x' big'] by auto
    
  then have listL: "x' # States.listL ?newStates = Big.list_current big @ rev (Small.list_current small)"
    using invar bigSize Big_Proof.pop_list_current[of big x' big'] 6(1)
    apply(auto split: prod.splits)
    by (metis append_Cons rev_append rev_rev_ident)
 
  from invar have four_steps: "States.invar ?steppedStates"
    using invar_n_steps by blast

  then have 1: "x' # States.listL ?steppedStates = Big.list_current big @ rev (Small.list_current small)"
    using States_Proof.n_steps invar listL
    by metis

  then have 2: "listL (deqL (Transforming (States Right big small))) = States.listL ?steppedStates"
    apply(auto simp: Let_def split: prod.splits states.splits Small.state.splits)
       apply (simp add: local.pop)+
    by(auto split: direction.splits Common.state.splits Big.state.splits Small.state.splits)

  with 1 have 3: "x' # listL (deqL (Transforming (States Right big small))) = Big.list_current big @ rev (Small.list_current small)"
    by auto

  with 6(1) have 4: "listL (Transforming (States Right big small)) = Big.list_current big @ rev (Small.list_current small)"
    using invar_list_big_first[of "States Right big small"] by fastforce

  from 3 4 have "x' # listL (deqL (Transforming (States Right big small))) = listL (Transforming (States Right big small))"
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

lemma remaining_steps_not_idle: "States.invar states \<Longrightarrow> remaining_steps states > 0 \<longleftrightarrow> (
    case states of 
      States _ (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> False 
    | _ \<Rightarrow> True) "
  apply(induction states)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remaining_steps_idle: "States.invar (States dir big small)
  \<Longrightarrow> remaining_steps (States dir big small) = 0 \<longleftrightarrow> (
    case (States dir big small) of 
       States _ (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> True 
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
          let ?states = "States Left 
              (Reverse (Current [] 0 right (Stack.size right - Suc iLeftLength)) right [] (Stack.size right - Suc iLeftLength))
              (Reverse1 (Current [] 0 iLeft (Suc (2 * iLeftLength))) iLeft [])
            "

          from True have invar: "States.invar ?states"
            apply(auto simp: reverseN_take Stack_Proof.size_list_length)
               apply (metis Idle.invar.simps Idle_Proof.invar_pop le_SucI le_add2 mult_2 Stack_Proof.size_list_length)
            subgoal apply(auto simp: popN_size popN_drop)
              by (smt (z3) Idle.invar.simps Idle_Proof.invar_pop add_Suc_right add_le_imp_le_diff append_take_drop_id le_refl length_rev mult_2 mult_Suc not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 rev_append rev_rev_ident Stack_Proof.size_list_length take_all_iff trans_le_add2)
            apply (metis Idle.invar.simps Idle_Proof.invar_pop Suc_diff_le diff_add_inverse diff_le_self mult_2 Stack_Proof.size_list_length)
            by (metis Idle.invar.simps Idle_Proof.invar_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 Stack_Proof.size_list_length trans_le_add2)

          then have invar_six: "States.invar (six_steps ?states)"
            using invar_n_steps by blast

          from True have remaining_steps: "6 < remaining_steps ?states"
            by(auto simp: max_def)

          with invar have "5 < remaining_steps (step ?states)"
            using remaining_steps_decline_3[of ?states 5] by auto

          with invar have "4 < remaining_steps ((step ^^ 2) ?states)"
            using invar_n_steps invar_step remaining_steps_decline_4[of ?states 4 1]
            by (smt (z3) add.commute add_Suc_right funpow_0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remaining_steps remaining_steps_decline_4)

          with remaining_steps have remaining_steps_end: "0 < remaining_steps (six_steps ?states)"
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
            using size_ok_steps invar remaining_steps size_ok.elims(3) by blast
  
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
  case (5 big small)
 
  obtain x newSmall where popped: "Small.pop small = (x, newSmall)"
    by fastforce

  let ?newStates = "States Left big newSmall"
  let ?steppedStates = "four_steps ?newStates"

  have start_size_ok: "size_ok (States Left big small)"
    using "5.prems" RealTimeDeque.invar.simps(6) by blast

  from 5 have invar: "States.invar ?newStates"
    by (meson RealTimeDeque.invar.simps(6) invar_pop_small_size popped size_ok_size_small)

  then have invar_four_steps: "States.invar (four_steps ?newStates)"
    using invar_n_steps by blast

  have last_steps:  "False = (4 < remaining_steps (States Left big newSmall)) \<Longrightarrow> 
    invar (deqL (Transforming (States Left big small)))"
  proof -
    assume steps: "False = (4 < remaining_steps (States Left big newSmall))"

    then have "remaining_steps ?newStates \<le> 4"
        using not_less by blast

    with 5 have no_remaining_steps: "remaining_steps ?steppedStates = 0"
      using invar remaining_steps_decline_5[of ?newStates 4]
      by auto

    from 5 have small_not_empty: "0 < Small.size small" 
      by auto

    from 5 have states_invar: "States.invar (States Left big small)" 
      by auto

    from 5 have states_size_ok: "States.size_ok (States Left big small)" 
      by auto

    obtain steppedSmall steppedBig where stepped: "?steppedStates = States Left steppedBig steppedSmall"
      by (metis(full_types)States.listL.cases step_n_same)

    with no_remaining_steps have "case States Left steppedBig steppedSmall of
      States Left (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False" 
      using remaining_steps_idle invar_four_steps by auto

    then obtain sI smallIdle bI bigIdle where idle: "States Left steppedBig steppedSmall = 
      States Left 
          (Big.state.Common (state.Idle bI bigIdle))
          (Small.state.Common (state.Idle sI smallIdle))
      "
      by(auto split: Small.state.splits Big.state.splits Common.state.splits)

    then have states_invar: "States.invar (States Left steppedBig steppedSmall)"
      using 5
      by (metis invar_four_steps stepped)
     

    with stepped invar_four_steps 
    have size_new_big: "Big.size_new big = Big.size_new steppedBig"
      using invar
      by (metis step_n_size_new_big)

    have size_new_small: "Suc (Small.size_new newSmall) = Small.size_new small"
      using small_not_empty states_invar popped 
      by (metis "5.prems"(1) RealTimeDeque.invar.simps(6) Small_Proof.size_new_pop States.invar.simps size_ok_size_new_small)

    with stepped invar_four_steps 
    have size_new_stepped_small: "Small.size_new newSmall = Small.size_new steppedSmall"
      using invar
      by (simp add: step_n_size_new_small)

    have previous_steps: "0 < remaining_steps (States Left big small)"
      using "5.prems"(1) invar.simps(6) by blast 

    with start_size_ok size_ok_size_new_big states_size_ok
    have "1 < Small.size_new small"
      by auto

    then have "0 < Small.size_new newSmall"
      using size_new_small
      by linarith

    then have small_not_empty: "0 < Small.size_new steppedSmall" 
      using size_new_stepped_small by auto

    then have "0 < Big.size_new big"
      using "5.prems" RealTimeDeque.invar.simps(6) States.size_ok.simps(1) States.invar.simps(1) size_ok_size_new_big by blast

    then have big_not_empty: "0 < Big.size_new steppedBig"
      by (simp add: size_new_big)

    have small_size: "Idle.size smallIdle = Small.size_new steppedSmall"
      using idle states_invar by auto

    have big_size: "Idle.size bigIdle = Big.size_new steppedBig"
      using idle states_invar by auto

    have "Small.size_new small \<le> 3 * Big.size_new big" 
      using start_size_ok by auto
    
    with size_new_small have "Small.size_new newSmall \<le> 3 * Big.size_new big" 
      by auto

    then have stepped_size_ok: "Small.size_new steppedSmall \<le> 3 * Big.size_new steppedBig"  
      using size_new_big size_new_stepped_small by presburger

    have not_empty_smallIdle: "0 < Idle.size smallIdle"
      using small_size small_not_empty by auto

    have "4 * Big.size_new big + (States.remaining_steps (States Left big small)) \<le> 12 * Small.size_new small - (3 * States.remaining_steps (States Left big small)) - 8"
      using start_size_ok by auto 

    then have "4 * Big.size_new big + 1 \<le> 12 * Small.size_new small - 3 - 8"
      using previous_steps by auto

    then have "Big.size_new big \<le> 3 * Small.size_new newSmall"
      using size_new_small by auto

    then have "Big.size_new big \<le> 3 * Small.size_new steppedSmall"
      by (simp add: size_new_stepped_small)

    then have "Big.size_new steppedBig \<le> 3 * Small.size_new steppedSmall"
      by (simp add: \<open>Big.size_new big = Big.size_new steppedBig\<close>)
    
    with idle states_invar stepped_size_ok
    have "invar (Idle smallIdle bigIdle)"
      using big_not_empty Idle_Proof.not_empty small_size small_not_empty apply auto
      using not_empty_smallIdle by blast
     
     with 5 have invar_stepped: "invar (case States Left steppedBig steppedSmall of 
      States Left 
           (Big.Common (Common.Idle _ big))
           (Small.Common (Common.Idle _ small)) 
          \<Rightarrow> Idle small big
   | _ \<Rightarrow> Transforming (States Left steppedBig steppedSmall))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle states.inject(1) states.simps(5) by auto

     have "(case States Left steppedBig steppedSmall of
       States Left 
      (Big.state.Common (state.Idle _ big))
      (Small.state.Common (state.Idle _ small)) 
         \<Rightarrow> deque.Idle small big
    | _ \<Rightarrow> Transforming (States Left steppedBig steppedSmall)) = Idle smallIdle bigIdle"
       by (simp add: idle)

     have "deqL (Transforming (States Left big small)) = (case ?steppedStates of 
      States Left 
         (Big.Common (Common.Idle _ big))
         (Small.Common (Common.Idle _ small)) 
        \<Rightarrow> Idle small big
   | _ \<Rightarrow> Transforming ?steppedStates)"
       by(auto simp: popped Let_def split: prod.splits states.splits direction.splits Big.state.splits Common.state.splits Small.state.splits)

     with stepped have "deqL (Transforming (States Left big small))
       = (case States Left steppedBig steppedSmall of 
      States Left 
        (Big.Common (Common.Idle _ big))
        (Small.Common (Common.Idle _ small)) 
        \<Rightarrow> Idle small big
   | _ \<Rightarrow> Transforming (States Left steppedBig steppedSmall))"
      by metis

     with 5 invar_stepped show ?case
        by auto
    qed

  with 5 show ?case
  proof(induction "remaining_steps (States Left big small) > 4")
    case True
    then have states_invar: "States.invar (States Left big small)" by auto
    from True have states_rem: "4 \<le> States.remaining_steps  (States Left big small)" by auto
    from True have states_window: "States.size_ok  (States Left big small)" by auto
    from True have "0 < Small.size small" by auto


    from 5 show ?case 
    proof(induction "remaining_steps ?newStates > 4")
      case True
      
      with True have "remaining_steps ?newStates > 4"
        by auto

      then have remaining_steps: "remaining_steps ?steppedStates > 0"
        by (metis One_nat_def add_Suc_shift funpow_0 invar numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remaining_steps_decline_4)

      from True have size_ok: "size_ok ?steppedStates"
        using step_4_pop_small_size_ok[of Left big small x] states_invar states_rem states_window 
        using \<open>0 < Small.size small\<close> order_less_imp_le popped by blast

      have "case ?steppedStates of
        States Left  (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
      | _ \<Rightarrow> True"
        apply(auto split: direction.splits prod.splits states.splits Small.state.splits Big.state.splits Common.state.splits)
        using remaining_steps by auto

      then have "(case ?steppedStates of 
        States Left 
          (Big.Common (Common.Idle _ big))
          (Small.Common (Common.Idle _ small)) 
           \<Rightarrow> Idle small big
     | _ \<Rightarrow> Transforming ?steppedStates) = Transforming ?steppedStates"
        by(auto split: direction.splits states.splits Small.state.splits Common.state.splits Big.state.splits)

      with True have "invar (case ?steppedStates of 
        States Left 
           (Big.Common (Common.Idle _ big))
          (Small.Common (Common.Idle _ small)) 
          \<Rightarrow> Idle small big
     | _ \<Rightarrow> Transforming ?steppedStates)"
        by (smt (z3) RealTimeDeque.invar.simps(6) invar_four_steps remaining_steps size_ok)

      then have "invar
          (case 
                  (case four_steps (States Left big newSmall) of
                        States Left 
                             (Big.state.Common (state.Idle _ big))
                              (Small.state.Common (state.Idle _ small')) 
                 \<Rightarrow> (x, Idle small' big)
                      | _ \<Rightarrow> (x, Transforming ?steppedStates)) of
           (x, deque) \<Rightarrow> deque)"
        by(auto split: prod.splits direction.splits states.splits Small.state.splits Big.state.splits Common.state.splits)

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

    then have "remaining_steps ?newStates \<le> 4"
      by (metis (no_types, lifting) invar.simps(6)  dual_order.trans not_le_imp_less remaining_steps_pop_small size_ok_size_small popped)

    then show ?case
      using last_steps
      by auto
   qed
next
  case (6 big small)
  obtain x newBig where popped: "Big.pop big = (x, newBig)"
    by fastforce

  let ?newStates = "States Right newBig small"
  let ?steppedStates = "four_steps ?newStates"

  have start_size_ok: "size_ok (States Right big small)"
    using "6.prems" invar.simps(6) by blast

  from 6 have invar: "States.invar ?newStates"
    by (meson invar.simps(6) invar_pop_big_size popped size_ok_size_big)

  then have invar_four_steps: "States.invar (four_steps ?newStates)"
    using invar_n_steps by blast

  have last_steps:  "False = (4 < remaining_steps (States Right newBig small)) \<Longrightarrow> 
    invar (deqL (Transforming (States Right big small)))"
  proof -
    assume steps: "False = (4 < remaining_steps (States Right newBig small))"

    then have "remaining_steps ?newStates \<le> 4"
        using not_less by blast

    with 6 have no_remaining_steps: "remaining_steps ?steppedStates = 0"
      using invar remaining_steps_decline_5[of ?newStates 4]
      by auto

    from 6 have big_not_empty: "0 < Big.size big" 
      by auto

    from 6 have states_invar: "States.invar (States Right big small)" 
      by auto

    from 6 have states_size_ok: "States.size_ok (States Right big small)" 
      by auto

    obtain steppedBig steppedSmall where stepped: "?steppedStates = States Right steppedBig steppedSmall"
      by (metis(full_types) States.listL.cases step_n_same)

    with no_remaining_steps have "case States Right steppedBig steppedSmall of
      States Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False"
      using invar_four_steps remaining_steps_idle by auto

    then obtain bI bigIdle sI smallIdle where idle: "States Right steppedBig steppedSmall = 
      States Right (Big.state.Common (state.Idle bI bigIdle)) (Small.state.Common (state.Idle sI smallIdle))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have states_invar: "States.invar (States Right steppedBig steppedSmall)"
      using 6 stepped 
      by (metis invar_four_steps)

    with stepped invar_four_steps 
    have size_new_small: "Small.size_new small = Small.size_new steppedSmall"
      by (metis step_n_size_new_small invar)

    have size_new_big: "Suc (Big.size_new newBig) = Big.size_new big"
      using big_not_empty funpow_0 step_n_pop_size_new_big states_invar popped
      by (metis "6.prems"(1) invar.simps(6))

    with stepped invar_four_steps
    have size_new_steppedL: "Big.size_new newBig = Big.size_new steppedBig"
      using invar
      by (simp add: step_n_size_new_big)

    have previous_steps: "0 < remaining_steps (States Right big small)"
      using "6.prems"(1) invar.simps(6) by blast 

    with start_size_ok size_ok_size_new_big states_size_ok
    have "1 < Big.size_new big"
      by auto

    then have "0 < Big.size_new newBig"
      using size_new_big
      by linarith

    then have big_not_empty: "0 < Big.size_new steppedBig" 
      using size_new_steppedL by auto

    then have "0 < Small.size_new small"
      using size_ok_size_new_small states_size_ok by blast

    then have small_not_empty: "0 < Small.size_new steppedSmall"
      by (simp add: size_new_small)

    have big_size: "Idle.size bigIdle = Big.size_new steppedBig"
      using idle states_invar by auto

    have small_size: "Idle.size smallIdle = Small.size_new steppedSmall"
      using idle states_invar by auto

    have "Big.size_new big \<le> 3 * Small.size_new small" 
      using start_size_ok by auto
    
    with size_new_big have "Big.size_new newBig \<le> 3 * Small.size_new small" 
      by auto

    then have stepped_size_ok: "Big.size_new steppedBig \<le> 3 * Small.size_new steppedSmall"  
      using size_new_small size_new_steppedL by presburger

    have not_empty_idleL: "0 < Idle.size bigIdle"
      using big_size big_not_empty by auto

    have "4 * Small.size_new small + (States.remaining_steps (States Right big small)) \<le> 12 * Big.size_new big - (3 * States.remaining_steps (States Right big small)) - 8"
      using start_size_ok by auto 

    then have "4 * Small.size_new small + 1 \<le> 12 * Big.size_new big - 3 - 8"
      using previous_steps by auto

    then have "Small.size_new small \<le> 3 * Big.size_new newBig"
      using size_new_big by auto

    then have "Small.size_new small \<le> 3 * Big.size_new steppedBig"
      by (simp add: size_new_steppedL)

    then have "Small.size_new steppedSmall \<le> 3 * Big.size_new steppedBig"
      by (simp add: size_new_small)
    
    with idle states_invar stepped_size_ok
    have "invar (Idle bigIdle smallIdle)"
      using small_not_empty Idle_Proof.not_empty big_size big_not_empty apply auto
      using not_empty_idleL by blast
     
     with 6 have invar_stepped: "invar (case States Right steppedBig steppedSmall of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming (States Right steppedBig steppedSmall))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle states.inject(1) states.simps(5) by auto

     have "(case States Right steppedBig steppedSmall of
       States Right (Big.state.Common (state.Idle _ big)) (Small.state.Common (state.Idle x_ small)) \<Rightarrow> deque.Idle big small
    | _ \<Rightarrow> Transforming (States Right steppedBig steppedSmall)) = Idle bigIdle smallIdle"
       by (simp add: idle)

     have "deqL (Transforming (States Right big small)) = (case ?steppedStates of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming ?steppedStates)"
       by(auto simp: popped Let_def split: prod.splits direction.splits states.splits Small.state.splits Common.state.splits Big.state.splits)

     with stepped have "deqL (Transforming (States Right big small)) = (case States Right steppedBig steppedSmall of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming (States Right steppedBig steppedSmall))"
      by metis

     with 6 invar_stepped show ?case
        by auto
    qed

  from 6 invar_four_steps show ?case
  proof(induction "remaining_steps (States Right big small) > 4")
    case True
    then have states_invar: "States.invar (States Right big small)" by auto
    from True have states_size_ok: "States.size_ok (States Right big small)" by auto
    from True have "0 < Big.size big" by auto

    show ?case 
    proof(induction "remaining_steps ?newStates > 4")
      case True
      with True have "remaining_steps ?newStates > 4" 
        by auto

    then have remaining_steps: "remaining_steps ?steppedStates > 0"
      by (metis One_nat_def add_Suc_shift funpow_0 invar numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remaining_steps_decline_4)

    from True have size_ok: "size_ok ?steppedStates"
      using step_4_pop_big_size_ok[of Right big small x] states_invar states_size_ok
      using \<open>0 < Big.size big\<close> order_le_less popped by blast

    have "case ?steppedStates of
      States Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using remaining_steps_not_idle[of ?steppedStates]
      apply(auto split: prod.splits direction.splits states.splits Small.state.splits Big.state.splits Common.state.splits)
      using remaining_steps by auto

    then have "(case ?steppedStates of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming ?steppedStates) = Transforming ?steppedStates"
      by(auto split: states.splits direction.splits Small.state.splits Common.state.splits Big.state.splits)

    with True have "invar (case ?steppedStates of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming ?steppedStates)"
      by (smt (z3) invar.simps invar_four_steps remaining_steps size_ok)

    then have "invar
        (case 
                (case four_steps (States Right newBig small) of
                      States Right (Big.state.Common (state.Idle _ big')) (Small.state.Common (state.Idle _ small)) \<Rightarrow> (x, Idle big' small)
                    | _ \<Rightarrow> (x, Transforming ?steppedStates)) of
         (x, deque) \<Rightarrow> deque)"
      by(auto split: prod.splits direction.splits states.splits  Big.state.splits Small.state.splits Common.state.splits)

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
   
    then have "remaining_steps ?newStates \<le> 4"
      by (metis (no_types, lifting) RealTimeDeque.invar.simps(6) dual_order.trans not_le_imp_less remaining_steps_pop_big size_ok_size_big popped)

    then show ?case
      using last_steps by auto
   qed
next
  case 7
  then show ?case by auto
qed

end
