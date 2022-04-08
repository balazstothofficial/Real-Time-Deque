theory Transforming_Proof
  imports  Transforming States_Proof
begin

lemma invar_step: "invar states \<Longrightarrow> invar (step states)"
proof(induction states rule: step.induct)
  case (1 small big)

  then have "States.invar (big, small)"
    by auto
  
  then have "States.invar (States.step (big, small))"
    using States_Proof.invar_step by blast

  then have "Transforming.invar (case States.step (big, small) of (big, small) \<Rightarrow> Left small big)"
    by(auto split: prod.split)

  then show ?case by auto
next
  case (2 big small)

  then have "States.invar (big, small)"
    by auto
  
  then have "States.invar (States.step (big, small))"
    using States_Proof.invar_step by blast

  then have "invar (case States.step (big, small) of (big, small) \<Rightarrow> Right big small)"
    by(auto split: prod.split)

  then show ?case by auto
qed

lemma step_listL: "invar states \<Longrightarrow> listL (step states) = listL states"
proof(induction states rule: step.induct)
  case (1 small big)

  then have "list_small_first (big, small) = Small.list_current small @ rev (Big.list_current big)"
    by auto

  then have "list_small_first (States.step (big, small)) = Small.list_current small @ rev (Big.list_current big)"
    using "1.prems" step_lists by force

  then have "listL (case States.step (big, small) of (big, small) \<Rightarrow> Left small big) =
         Small.list_current small @ rev (Big.list_current big)"
    by(auto split: prod.splits)

  with 1 show ?case 
    by auto
next
  case (2 big small)
  
  then have statesToList: "list_big_first (big, small) = Big.list_current big @ rev (Small.list_current small)"
    using invar_list_big_first by fastforce

  then have "list_big_first (States.step (big, small)) = Big.list_current big @ rev (Small.list_current small)"
    using "2.prems"step_lists by force

  then have "listL (case States.step (big, small) of (big, small) \<Rightarrow> Right big small) =
         Big.list_current big @ rev (Small.list_current small)"
   by(auto split: prod.splits)

  with 2 show ?case 
    using statesToList by fastforce
qed

lemma invar_pop_small_left: "invar (Left small big) \<Longrightarrow> 0 < Small.size small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invar (Left small' big)"
  by (meson Transforming.invar.simps(1) invar_pop_small_size)

lemma invar_pop_big_left: "invar (Left small big) \<Longrightarrow> 0 < Big.size big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invar (Left small big')"
  by (meson Transforming.invar.simps(1) invar_pop_big_size)

lemma invar_pop_small_right: "invar (Right big small) \<Longrightarrow> 0 < Small.size small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invar (Right big small')"
  by (meson Transforming.invar.simps invar_pop_small_size)

lemma invar_pop_big_right: "invar (Right big small) \<Longrightarrow> 0 < Big.size big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invar (Right big' small)"
  by (meson Transforming.invar.simps invar_pop_big_size)

lemma n_steps: "invar states \<Longrightarrow> listL ((step^^n) states) = listL states"
  apply(induction n arbitrary: states)
  by(auto simp: funpow_swap1 invar_step step_listL)

lemmas steps = step_lists Big_Proof.step_list Common_Proof.step_list step_list n_steps

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits

lemma invar_n_steps: "invar states \<Longrightarrow> invar ((step^^n) states)"
  apply(induction n arbitrary: states)
  by(auto simp: invar_step)

lemma step_size_ok: "invar states \<Longrightarrow> size_ok states \<Longrightarrow> size_ok (step states)"
  apply(induction states)
  apply (metis Transforming.size_ok.simps(1) Transforming.invar.simps(1) Transforming.step.simps(1) prod.case_eq_if prod.exhaust_sel step_size_ok)
  by (metis Transforming.size_ok.simps(2) Transforming.invar.simps(2) Transforming.step.simps(2) prod.case_eq_if prod.exhaust_sel step_size_ok)
 
lemma n_steps_size_ok: "invar states \<Longrightarrow> size_ok states \<Longrightarrow> size_ok ((step ^^ n) states)"
  apply(induction n)
   apply(auto simp: funpow_swap1 invar_n_steps step_size_ok)
  by (metis step_size_ok funpow_swap1 invar_n_steps)

lemma remaining_steps_decline_3: "invar states \<Longrightarrow> Suc n < remaining_steps states
   \<Longrightarrow> n < remaining_steps (step states)"
proof(induction states)
  case (Left small big)
  then show ?case using remaining_steps_decline_3[of "(big, small)" n] 
    by(auto split: prod.splits)
next
case (Right big small)
  then show ?case using remaining_steps_decline_3[of "(big, small)" n] 
    by(auto split: prod.splits)
qed

lemma remaining_steps_decline_4: "invar states \<Longrightarrow> Suc n < remaining_steps ((step ^^ m) states)
   \<Longrightarrow> n < remaining_steps ((step ^^ Suc m) states)"
  by(auto simp: remaining_steps_decline_3 invar_n_steps)

lemma remaining_steps_decline_5': "invar states \<Longrightarrow> remaining_steps states = 1
   \<Longrightarrow> remaining_steps (step states) = 0"
proof(induction states)
  case (Left small big)
  then show ?case using remaining_steps_decline_2[of "(big, small)"]
    by(auto split: prod.splits)
next
  case (Right big small)
  then show ?case using remaining_steps_decline_2[of "(big, small)"]
    by(auto split: prod.splits)
qed

lemma remaining_steps_states_remaining_steps_left: "States.remaining_steps ((States.step ^^ n) (big, small)) = remaining_steps ((step ^^ n) (Left small big))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case apply(auto split: prod.splits)
    by (metis Transforming.step.simps(1) case_prod_unfold funpow_swap1 prod.exhaust_sel) 
qed

lemma remaining_steps_states_remaining_steps_right: "States.remaining_steps ((States.step ^^ n) (big, small)) = remaining_steps ((step ^^ n) (Right big small))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case apply(auto split: prod.splits)
    by (metis Transforming.step.simps(2) case_prod_unfold funpow_swap1 prod.exhaust_sel) 
qed

lemma remaining_steps_decline_5: "invar states \<Longrightarrow> remaining_steps states \<le> n
  \<Longrightarrow> remaining_steps ((step ^^ n) states) = 0"
proof(induction states)
  case (Left small big)
  then show ?case using remaining_steps_decline_5[of "(big, small)" n]
    by(auto simp: remaining_steps_states_remaining_steps_left split: prod.splits)
next
  case (Right big small)
  then show ?case using remaining_steps_decline_5[of "(big, small)"]
    by(auto simp: remaining_steps_states_remaining_steps_right split: prod.splits)
qed


lemma remaining_steps_step_n: "invar states \<Longrightarrow>  n < remaining_steps states
   \<Longrightarrow> remaining_steps states - n = remaining_steps ((step ^^ n) states)"
proof(induction states)
  case (Left small big)
  then show ?case 
    using remaining_steps_step_n[of "(big, small)" n]
    by (metis Transforming.invar.simps(1) Transforming.remaining_steps.simps(1) remaining_steps_states_remaining_steps_left)
next
  case (Right big small)
  then show ?case
    by (metis Transforming.invar.simps(2) remaining_steps_step_n funpow_0 remaining_steps_states_remaining_steps_right)
qed

lemma step_size_ok': "invar states \<Longrightarrow>
    size_ok' states x \<Longrightarrow> 
    size_ok' (step states) x"
proof(induction states)
  case (Left small big)
  then show ?case
    by (smt (verit, best) States.size_ok'.elims(2) States.size_ok'.elims(3) Transforming.size_ok'.simps(1) Transforming.invar.simps(1) Transforming.step.simps(1) invar_step case_prodE2 case_prod_conv step_size_big step_size_new_small step_size_new_big step_size_small)
next
  case (Right big small)
  then show ?case 
    using step_size_ok'
    by (smt (verit, ccfv_threshold) Transforming.size_ok'.simps(2) Transforming.invar.simps(2) Transforming.step.simps(2) invar_step case_prodE2 case_prod_unfold fst_conv snd_conv step_size_ok')
qed

lemma step_n_size_ok': "invar states \<Longrightarrow>
    size_ok' states x \<Longrightarrow> 
    size_ok' ((step ^^ n) states) x"
proof(induction n arbitrary: states)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case using step_size_ok' 
    by (metis invar_step comp_eq_dest_lhs funpow_Suc_right) 
qed

lemma size_ok_steps: "invar states \<Longrightarrow>
     n < remaining_steps states \<Longrightarrow> 
    size_ok' states (remaining_steps states - n) \<Longrightarrow> 
    size_ok' ((step ^^ n) states) (remaining_steps ((step ^^ n) states))"
  by (simp add: remaining_steps_step_n step_n_size_ok')

lemma size_ok'_size_ok: "size_ok' states (remaining_steps states) = size_ok states"
  apply(induction states rule: size_ok.induct)
  by auto

lemma step_n_left_size_new_small: "invar (Left left right) \<Longrightarrow> (step ^^ n) (Left left right) = Left left' right'
   \<Longrightarrow> Small.size_new left = Small.size_new left'"
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) invar.simps(1) step.simps(1) invar_step case_prod_unfold funpow_swap1 prod.exhaust_sel step_size_new_small)
qed

lemma step_n_right_size_new_small: "invar (Right left right) \<Longrightarrow> (step ^^ n) (Right left right) = Right left' right'
   \<Longrightarrow> Small.size_new right = Small.size_new right'"
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) invar.simps(2) step.simps(2) invar_step case_prod_unfold funpow_swap1 prod.exhaust_sel step_size_new_small)
qed


lemma step_n_left_size_new_big: "invar (Left left right) \<Longrightarrow> (step ^^ n) (Left left right) = Left left' right'
   \<Longrightarrow> Big.size_new right = Big.size_new right'"
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) lists_current.simps step_lists_current step_lists Suc.prems(1) invar.simps(1) step.simps(1) case_prodE case_prod_conv funpow_swap1 invar_step_1 invar_step_3 step_size_new_small step_size_new_big)
qed

lemma step_n_right_size_new_big: "invar (Right left right) \<Longrightarrow> (step ^^ n) (Right left right) = Right left' right'
 \<Longrightarrow> Big.size_new left = Big.size_new left'"
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) invar.simps(2) step.simps(2) invar_step case_prodE funpow_swap1 invar_step_3 old.prod.case step_n_right_size_new_small step_size_new_big)
qed

end
