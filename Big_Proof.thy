theory Big_Proof
  imports Big Common_Proof
begin

(* TODO: *)
lemma step_list: "invar big \<Longrightarrow> list (step big) = list big"
  apply(induction big rule: step_state.induct)
    apply(auto simp: step_list split: current.splits)
  by (metis Suc_neq_Zero bot_nat_0.extremum_uniqueI list_empty first_pop list.size(3) reverseN.simps(3) Stack_Proof.size_list_length)

lemma step_list_current: "invar big \<Longrightarrow> list_current (step big) = list_current big"
  apply(induction big rule: step_state.induct)
  by(auto simp: step_list_current split: current.splits)

lemma push: "list (push x big) = x # list big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: push_list)
next
  case (2 x current big aux count)
  then show ?case
    apply(induction x current rule: Current.push.induct)
    by auto
qed

(* TODO: *)
lemma helper_size: "0 < size (Reverse current big aux count) \<Longrightarrow> invar (Reverse current big aux count) \<Longrightarrow> 
    first current = hd (list (Reverse current big aux count))"
proof(induction current rule: Current.pop.induct)
  case (1 added old remained)
  then show ?case 
    apply(auto simp: reverseN_take rev_take)
    by (smt (z3) Nat.diff_diff_right add.commute diff_is_0_eq drop_eq_Nil first_list hd_append hd_take le_add_diff length_rev minus_nat.diff_0 nat_le_linear Stack_Proof.size_not_empty take_eq_Nil)
   
next
  case (2 x xs added old remained)
  then show ?case by auto
qed

lemma helper_2_size: "0 < size (Reverse current big aux count) \<Longrightarrow> invar (Reverse current big aux count) \<Longrightarrow> 
    list (Reverse (drop_first current) big aux count) = tl (list (Reverse current big aux count))"
proof(induction current rule: Current.pop.induct)
  case (1 added old remained)
  then have "
         drop (Suc (length (Stack.list big) + length aux) - (length (Stack.list big) - count + remained)) (rev aux) =
         tl (drop (length (Stack.list big) + length aux - (length (Stack.list big) - count + remained)) (rev aux))"
    apply(auto simp: reverseN_drop)
    by (smt (verit, del_insts) Nat.add_diff_assoc Nat.diff_diff_right add.commute diff_diff_cancel diff_le_self drop_Suc le_diff_conv plus_1_eq_Suc Stack_Proof.size_list_length tl_drop)

  with 1  show ?case 
    apply(auto simp: reverseN_take rev_take tl_drop  Stack_Proof.size_list_length)
    by (smt (verit, best) Nat.add_diff_assoc One_nat_def add.commute append_self_conv2 diff_add_inverse2 diff_is_0_eq' drop_Suc drop_all le_add2 le_diff_conv length_drop length_rev list.size(3) not_less_eq_eq plus_1_eq_Suc tl_append2 tl_drop)
next
  case (2 x xs added old remained)
  then show ?case by auto
qed

lemma helper_3_size: "0 < size big \<Longrightarrow> invar big \<Longrightarrow> list big \<noteq> []"
  apply(induction big)
   apply(auto simp: list_size split: current.splits)
   apply (simp add: reverseN_take)
  apply (metis bot_nat_0.extremum_uniqueI diff_zero leD list.size(3) Stack_Proof.size_list_length)
  using list_size by blast

(* TODO: rename *)
lemma pop_size: "0 < size big \<Longrightarrow> invar big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> x # list big' = list big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case
    by(auto simp: pop_list split: prod.splits)
next
  case (2 x current big aux count)
  
  
  from 2 show ?case 
    using helper_size[of current big aux count] helper_2_size[of current big aux count] helper_3_size 
    by(auto simp: helper_3_size split: current.splits)
qed 

(* TODO: rename *)
lemma pop_2_size: "0 < size big \<Longrightarrow> invar big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> list big' = tl (list big)"
  using pop_size cons_tl[of x "list big'" "list big"] 
  by force

(* TODO: *)
lemma invar_step: "invar (big :: 'a state) \<Longrightarrow> invar (step big)" 
proof(induction big rule: step_state.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invar_step)
next
  case (2 current uu aux)
  then show ?case
    apply(auto simp: reverseN_take split: current.splits)
    by (metis length_rev length_take min.absorb2 Stack_Proof.size_list_length take_append take_take)
next
  case (3 current big aux count)
  then have a: "rev (Stack.list big) @ aux = rev (Stack.list (Stack.pop big)) @ Stack.first big # aux"
    apply(auto split: current.splits)
    by (metis Zero_not_Suc bot_nat_0.extremum_uniqueI first_pop list.size(3) rev.simps(2) Stack_Proof.size_list_length Stack_Proof.list_not_empty)

  from 3 have b: "reverseN (Suc count) (Stack.list big) aux = reverseN count (Stack.list (Stack.pop big)) (Stack.first big # aux)"
    apply(auto simp: reverseN_take split: current.splits)
    by (metis Stack_Proof.size_empty Zero_not_Suc bot_nat_0.extremum_uniqueI first_pop rev.simps(2) take_Suc_Cons)

  from 3 a b show ?case
    apply(auto split: current.splits)
    by (metis Suc_le_lessD length_append_singleton length_rev less_Suc_eq_le Stack_Proof.size_list_length)
qed

lemma invar_push: "invar big \<Longrightarrow> invar (push x big)"
  apply(induction x big rule: push.induct)
  by(auto simp: invar_push split: current.splits)

lemma invar_pop_2: "\<lbrakk>
  0 < size big; 
  invar big;
  pop big = (x, big')
\<rbrakk> \<Longrightarrow> invar big'"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: invar_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    have a: "Stack.list (Stack.pop old) = tl (Stack.list old)"
      apply(induction old rule: Stack.pop.induct)
      by auto


    from 1 have b: "
     tl (rev (take (size old - length (Stack.list big)) aux) @ rev (take (size old) (rev (Stack.list big)))) =
         rev (take (size (Stack.pop old) - length (Stack.list big)) aux) @ rev (take (size (Stack.pop old)) (rev (Stack.list big)))"
    proof(induction "size old < length (Stack.list big)")
      case True
      then show ?case 
        apply(auto simp: reverseN_take)
        by (smt (z3) One_nat_def Stack_Proof.size_empty Stack_Proof.size_pop Suc_diff_eq_diff_pred Suc_diff_le bot_nat_0.not_eq_extremum diff_is_0_eq drop_Suc length_rev less_imp_le nat_le_linear not_less_eq_eq rev_is_Nil_conv rev_take self_append_conv2 take_eq_Nil tl_drop)
    next
      case False


      from False show ?case
      proof(induction "size (Stack.pop old) < length (Stack.list big)")
        case True
        then show ?case
          apply auto
          by (smt (verit, best) Cons_nth_drop_Suc One_nat_def Stack_Proof.size_empty Stack_Proof.size_pop Suc_le_eq a add.commute add_leE diff_add_inverse2 first_pop gen_length_def le_add_diff_inverse2 le_eq_less_or_eq length_code length_rev list.inject not_le_imp_less plus_1_eq_Suc rev_is_Nil_conv rev_rev_ident rev_take self_append_conv2 take_all_iff take_eq_Nil)
      next
        case False
        then show ?case apply auto
          by (smt (z3) Stack_Proof.size_empty Stack_Proof.size_pop Suc_diff_le Suc_le_lessD Suc_pred bot_nat_0.not_eq_extremum diff_Suc_Suc diff_add_inverse2 diff_is_0_eq drop_Suc length_append length_rev list.size(3) nat_le_linear not_le_imp_less rev_take Stack_Proof.size_list_length take_all_iff tl_append2 tl_drop)
      qed
    qed
             
    from 1 show ?case  
      apply auto
         apply linarith+
      subgoal 
        by(auto simp: a b reverseN_take)
      apply(auto simp: a reverseN_take  take_tl)
      apply(auto simp: rev_take)
      proof(induction "drop (length aux - (remained - min (length (Stack.list big)) count)) (rev aux) = []")
        case True
        then show ?case apply auto 
          by (smt (z3) Suc_diff_le diff_diff_cancel diff_diff_left diff_is_0_eq diff_le_self drop_Suc min.commute min_def Stack_Proof.size_list_length tl_drop)
      next
        case False
        then show ?case apply auto
          by (metis Suc_diff_le drop_Suc le_diff_conv min.commute min_def Stack_Proof.size_list_length tl_drop)
      qed
  next
    case (2 x xs added old remained)
    then show ?case
      by auto
  qed
qed

lemma push_list_current: "list_current (push x big) = x # list_current big"
  apply(induction x big rule: push.induct)
  by(auto simp: push_list_current Current_Proof.push_list)

lemma pop_list_current: "invar big \<Longrightarrow> 0 < size big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> x # list_current big' = list_current big"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: pop_list_current split: prod.splits)
next
  case (2 current big aux count)
  
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case
      apply auto
      by (metis first_pop Stack_Proof.size_not_empty)
  next
    case (2 x xs added old remained)
    then show ?case
      by auto
  qed
qed

(* TODO: *)
lemma list_current_size: "\<lbrakk>0 < size big; list_current big = []; invar big\<rbrakk> \<Longrightarrow> False"
  apply(induction big)
    apply(auto  split: current.splits)
    apply (simp add: Stack_Proof.size_list_length)
  using list_current_size by blast

lemma step_size: "invar (big :: 'a state) \<Longrightarrow> size big = size (step big)"
  apply(induction big rule: step_state.induct)
  by(auto simp: step_size split: current.splits)

(* TODO: *)
lemma size_empty: "invar (big :: 'a state) \<Longrightarrow> size big = 0 \<Longrightarrow> is_empty big"
  apply(induction big)
   apply(auto simp: size_empty Current_Proof.size_empty split: current.splits)
   apply (metis Stack_Proof.size_empty add.commute add_diff_cancel_right' bot_nat_0.extremum min_def zero_diff)
  by (metis add_gr_0 length_greater_0_conv less_numeral_extra(3) min_less_iff_conj)

lemma remaining_steps_step: "\<lbrakk>invar (big :: 'a state); remaining_steps big > 0\<rbrakk>
   \<Longrightarrow> remaining_steps big = Suc (remaining_steps (step big))"
  apply(induction big rule: step_state.induct)
  by(auto simp: remaining_steps_step split: current.splits)

lemma remaining_steps_step_0: "\<lbrakk>invar (big :: 'a state); remaining_steps big = 0\<rbrakk> 
  \<Longrightarrow> remaining_steps (step big) = 0"
  apply(induction big)
  by(auto simp: remaining_steps_step_0 split: current.splits)

lemma remaining_steps_push: "invar big \<Longrightarrow> remaining_steps big = remaining_steps (push x big)"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: remaining_steps_push)
next
  case (2 x current big aux count)
  then show ?case
  proof(induction current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case 
      by auto
  qed
qed

lemma remaining_steps_pop: "\<lbrakk>invar big; 0 < size big; pop big = (x, big')\<rbrakk>
   \<Longrightarrow> remaining_steps big' \<le> remaining_steps big"
proof(induction big rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: remaining_steps_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma size_push: "invar big \<Longrightarrow> Suc (size big) = size (push x big)"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: size_push)
next
  case (2 x current small auxS)
  then show ?case 
    by(auto simp: size_push split: current.splits)
qed

lemma size_new_push: "invar big \<Longrightarrow> Suc (size_new big) = size_new (push x big)"
proof(induction x big rule: Big.push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: size_new_push)
next
  case (2 x current small auxS)
  then show ?case 
    by(auto simp: size_push split: current.splits)
qed

lemma size_pop: "\<lbrakk>invar big; 0 < size big; pop big = (x, big')\<rbrakk>
   \<Longrightarrow> Suc (size big') = size big"
proof(induction big rule: pop.induct)
  case (1 state)
  then show ?case by(auto simp: size_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case
    using Current_Proof.size_pop[of current] apply(induction current rule: Current.pop.induct)
    by auto
qed

lemma size_new_pop: "\<lbrakk>invar big; 0 < size_new big; pop big = (x, big')\<rbrakk>
    \<Longrightarrow> Suc (size_new big') = size_new big"
proof(induction big rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: size_new_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_size_new: "\<lbrakk>invar (big :: 'a state); 0 < size big\<rbrakk> \<Longrightarrow> 0 < size_new big"
  by(induction big)(auto simp: size_size_new)

end
