theory Big_Proof
  imports Big Common_Proof
begin

(* TODO: *)
lemma tick_toList: "invariant big \<Longrightarrow> toList (tick big) = toList big"
  apply(induction big rule: tick.induct)
    apply(auto simp: tick_toList split: current.splits)
  by (metis Suc_neq_Zero bot_nat_0.extremum_uniqueI toList_isEmpty first_pop list.size(3) reverseN.simps(3) size_listLength)

lemma tick_toCurrentList: "invariant big \<Longrightarrow> toCurrentList (tick big) = toCurrentList big"
  apply(induction big rule: tick.induct)
  by(auto simp: tick_toCurrentList split: current.splits)

lemma push: "toList (push x big) = x # toList big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: push_toList)
next
  case (2 x current big aux count)
  then show ?case
    apply(induction x current rule: put.induct)
    by auto
qed

lemma helper: "\<not>Current.isEmpty current \<Longrightarrow> invariant (Reverse current big aux count) \<Longrightarrow> 
    top current = hd (Big.toList (Reverse current big aux count))"
proof(induction current rule: get.induct)
  case (1 added old remained)
  then show ?case 
    apply(auto simp: reverseN_drop)
    by (metis Nat.diff_diff_right add.commute first_pop hd_take le_diff_conv length_drop length_rev length_take list.sel(1) min.absorb2 rev_take size_listLength take_append)
next
  case (2 x xs added old remained)
  then show ?case by auto
qed

lemma helper_2: "\<not>Current.isEmpty current \<Longrightarrow> invariant (Reverse current big aux count) \<Longrightarrow> 
    Big.toList (Reverse (bottom current) big aux count) = tl (Big.toList (Reverse current big aux count))"
proof(induction current rule: get.induct)
  case (1 added old remained)
  then have "
         drop (Suc (length (Stack.toList big) + length aux) - (length (Stack.toList big) - count + remained)) (rev aux) =
         tl (drop (length (Stack.toList big) + length aux - (length (Stack.toList big) - count + remained)) (rev aux))"
    apply(auto simp: reverseN_drop)
    by (simp add: Suc_diff_le drop_Suc size_listLength tl_drop)

  with 1  show ?case 
    apply(auto simp: reverseN_drop )
    by (smt (verit, ccfv_threshold) Suc_diff_le add.commute diff_add_inverse diff_diff_left diff_is_0_eq drop0 drop_Suc drop_all_iff le_Suc_eq le_add_diff_inverse length_rev not_less_eq_eq self_append_conv2 size_listLength tl_append2)
next
  case (2 x xs added old remained)
  then show ?case by auto
qed

lemma moveToCommon: "\<lbrakk>\<not> Common.isEmpty x; Common.invariant x; Common.toList x = []\<rbrakk> \<Longrightarrow> False"
  apply(induction x)
   apply(auto simp: take_Cons' split: current.splits)
  using toList_isNotEmpty apply blast
  by (metis Idle.isEmpty.elims(3) Idle.toList.simps toList_isNotEmpty)

lemma helper_3: "\<not>isEmpty big \<Longrightarrow> invariant big \<Longrightarrow> toList big \<noteq> []"
  apply(induction big)
   apply(auto simp: moveToCommon split: current.splits)
  apply (simp add: reverseN_take)
  using moveToCommon by blast

(* TODO: *)
lemma pop: "\<not>isEmpty big \<Longrightarrow> invariant big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> x # toList big' = toList big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case
    by(auto simp: list_pop split: prod.splits)
next
  case (2 x current big aux count)
  
  
  from 2 show ?case 
    using helper[of current big aux count] helper_2[of current big aux count] helper_3  
    apply(auto simp: helper_3 split: current.splits)
    by (smt (verit, best) "2.prems"(1) "2.prems"(2) Big.toList.simps(2) helper_3 list.exhaust_sel)
qed 

(* TODO: *)
lemma pop_2: "\<not>isEmpty big \<Longrightarrow> invariant big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> toList big' = tl (toList big)"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case
    by(auto simp: list_pop split: prod.splits)
next
  case (2 x current big aux count)
  
  
  from 2 show ?case 
    using helper[of current big aux count] helper_2[of current big aux count] helper_3  
    by(auto simp: helper_3 split: current.splits)
qed 

(* TODO: *)
lemma invariant_tick: "invariant big \<Longrightarrow> invariant (tick big)" 
proof(induction big rule: tick.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invariant_tick)
next
  case (2 current uu aux)
  then show ?case
    apply(auto simp: reverseN_take split: current.splits)
    by (metis length_rev length_take min.absorb2 size_listLength take_append take_take)
next
  case (3 current big aux count)
  then have a: "rev (Stack.toList big) @ aux = rev (Stack.toList (Stack.pop big)) @ first big # aux"
    apply(auto split: current.splits)
    by (metis Zero_not_Suc bot_nat_0.extremum_uniqueI first_pop list.size(3) rev.simps(2) size_listLength toList_isNotEmpty)

  from 3 have b: "reverseN (Suc count) (Stack.toList big) aux = reverseN count (Stack.toList (Stack.pop big)) (first big # aux)"
    apply(auto simp: reverseN_take split: current.splits)
    by (metis Stack_Proof.size_isEmpty Zero_not_Suc bot_nat_0.extremum_uniqueI first_pop rev.simps(2) take_Suc_Cons)

  from 3 a b show ?case
    apply(auto split: current.splits)
    by (metis Suc_le_lessD length_append_singleton length_rev less_Suc_eq_le size_listLength)
qed

lemma invariant_push: "invariant big \<Longrightarrow> invariant (push x big)"
  apply(induction x big rule: push.induct)
  by(auto simp: invariant_push split: current.splits)

(* TODO: *)
lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty big; 
  invariant big;
  pop big = (x, big')
\<rbrakk> \<Longrightarrow> invariant big'"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: invariant_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    have a: "Stack.toList (Stack.pop old) = tl (Stack.toList old)"
      apply(induction old rule: Stack.pop.induct)
      by auto


    from 1 have b: "
     tl (rev (take (Stack.size old - length (Stack.toList big)) aux) @ rev (take (Stack.size old) (rev (Stack.toList big)))) =
         rev (take (Stack.size (Stack.pop old) - length (Stack.toList big)) aux) @ rev (take (Stack.size (Stack.pop old)) (rev (Stack.toList big)))"
    proof(induction "Stack.size old < length (Stack.toList big)")
      case True
      then show ?case 
        apply(auto simp: reverseN_take)
        by (smt (z3) One_nat_def Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_diff_eq_diff_pred Suc_diff_le bot_nat_0.not_eq_extremum diff_is_0_eq drop_Suc length_rev less_imp_le nat_le_linear not_less_eq_eq rev_is_Nil_conv rev_take self_append_conv2 take_eq_Nil tl_drop)
    next
      case False
     
        

      from False show ?case
      proof(induction "Stack.size (Stack.pop old) < length (Stack.toList big)")
        case True
        then show ?case
          apply auto
          by (smt (z3) Suc_diff_Suc Suc_leI append_self_conv2 diff_is_0_eq' drop0 drop_Suc length_rev pop_listLength rev_is_Nil_conv rev_rev_ident rev_take size_listLength take_eq_Nil)
      next
        case False
        then show ?case apply auto
          by (smt (z3) Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_diff_le Suc_le_lessD Suc_pred bot_nat_0.not_eq_extremum diff_Suc_Suc diff_add_inverse2 diff_is_0_eq drop_Suc length_append length_rev list.size(3) nat_le_linear not_le_imp_less rev_take size_listLength take_all_iff tl_append2 tl_drop)
      qed
    qed
             
    from 1 show ?case  
      apply auto
         apply linarith+
      subgoal 
        by(auto simp: a b reverseN_take)
      apply(auto simp: reverseN_take)
      by (smt (verit, ccfv_SIG) Suc_diff_Suc Suc_diff_le Suc_pred a bot_nat_0.not_eq_extremum diff_Suc_Suc diff_is_0_eq drop_Suc le_eq_less_or_eq length_rev length_take list.size(3) min.absorb2 nat_le_linear rev_take size_listLength take_append take_tl tl_append2 tl_drop)
  next
    case (2 x xs added old remained)
    then show ?case
      by auto
  qed
qed

lemma invariant_pop_2: "\<lbrakk>
  0 < size big; 
  invariant big;
  pop big = (x, big')
\<rbrakk> \<Longrightarrow> invariant big'"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: invariant_pop_2 split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    have a: "Stack.toList (Stack.pop old) = tl (Stack.toList old)"
      apply(induction old rule: Stack.pop.induct)
      by auto


    from 1 have b: "
     tl (rev (take (Stack.size old - length (Stack.toList big)) aux) @ rev (take (Stack.size old) (rev (Stack.toList big)))) =
         rev (take (Stack.size (Stack.pop old) - length (Stack.toList big)) aux) @ rev (take (Stack.size (Stack.pop old)) (rev (Stack.toList big)))"
    proof(induction "Stack.size old < length (Stack.toList big)")
      case True
      then show ?case 
        apply(auto simp: reverseN_take)
        by (smt (z3) One_nat_def Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_diff_eq_diff_pred Suc_diff_le bot_nat_0.not_eq_extremum diff_is_0_eq drop_Suc length_rev less_imp_le nat_le_linear not_less_eq_eq rev_is_Nil_conv rev_take self_append_conv2 take_eq_Nil tl_drop)
    next
      case False
     
        

      from False show ?case
      proof(induction "Stack.size (Stack.pop old) < length (Stack.toList big)")
        case True
        then show ?case
          apply auto
          by (smt (verit, best) Cons_nth_drop_Suc One_nat_def Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_le_eq a add.commute add_leE diff_add_inverse2 first_pop gen_length_def le_add_diff_inverse2 le_eq_less_or_eq length_code length_rev list.inject not_le_imp_less plus_1_eq_Suc rev_is_Nil_conv rev_rev_ident rev_take self_append_conv2 take_all_iff take_eq_Nil)
      next
        case False
        then show ?case apply auto
          by (smt (z3) Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_diff_le Suc_le_lessD Suc_pred bot_nat_0.not_eq_extremum diff_Suc_Suc diff_add_inverse2 diff_is_0_eq drop_Suc length_append length_rev list.size(3) nat_le_linear not_le_imp_less rev_take size_listLength take_all_iff tl_append2 tl_drop)
      qed
    qed
             
    from 1 show ?case  
      apply auto
         apply linarith+
      subgoal apply auto sorry
      subgoal 
        by(auto simp: a b reverseN_take)
      apply(auto simp: reverseN_take)
      by (smt (verit, ccfv_SIG) Suc_diff_Suc Suc_diff_le Suc_pred a bot_nat_0.not_eq_extremum diff_Suc_Suc diff_is_0_eq drop_Suc le_eq_less_or_eq length_rev length_take list.size(3) min.absorb2 nat_le_linear rev_take size_listLength take_append take_tl tl_append2 tl_drop)
  next
    case (2 x xs added old remained)
    then show ?case
      by auto
  qed
qed

lemma currentList_push: "toCurrentList (push x big) = x # toCurrentList big"
  apply(induction x big rule: push.induct)
  by(auto simp: currentList_push put_toList)

lemma currentList_pop: "\<not>isEmpty big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> toCurrentList big' = tl (toCurrentList big)"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: currentList_pop split: prod.splits)
next
  case (2 current big aux count)
  
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
      by(auto simp: Stack_Proof.pop_toList)
  next
    case (2 x xs added old remained)
    then show ?case
      by auto
  qed
qed

lemma some_empty: "\<lbrakk>isEmpty (tick big); \<not> isEmpty big; invariant big\<rbrakk> \<Longrightarrow> False"
  apply(induction big rule: tick.induct)
    apply(auto split: current.splits if_splits)
  using some_empty by blast

lemma currentList_empty: "\<lbrakk>\<not> isEmpty big; toCurrentList big = []; invariant big\<rbrakk> \<Longrightarrow> False"
  apply(induction big)
  using currentList_empty 
  by(auto simp:  Stack_Proof.size_isEmpty split: current.splits)

(* TODO: *)
lemma currentList_empty_2: "\<lbrakk>0 < size big; toCurrentList big = []; invariant big\<rbrakk> \<Longrightarrow> False"
  apply(induction big)
    apply(auto  split: current.splits)
    apply (simp add: size_listLength)
  using currentList_empty_2 by blast

lemma tick_size: "invariant big \<Longrightarrow> size big = size (tick big)"
  apply(induction big rule: tick.induct)
  by(auto simp: tick_size split: current.splits)

lemma tick_not_empty: "invariant big \<Longrightarrow> \<not>isEmpty big \<Longrightarrow> \<not>isEmpty (tick big)"
  apply(induction big rule: tick.induct)
  by(auto simp: tick_not_empty split: current.splits)

(* TODO: *)
lemma size_isEmpty: "invariant big \<Longrightarrow> size big = 0 \<Longrightarrow> isEmpty big"
  apply(induction big)
   apply(auto simp: size_isEmpty Current_Proof.size_isEmpty split: current.splits)
   apply (metis Stack_Proof.size_isEmpty add.commute add_diff_cancel_right' bot_nat_0.extremum min_def zero_diff)
  by (metis add_gr_0 length_greater_0_conv less_numeral_extra(3) min_less_iff_conj)

end
