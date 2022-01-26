theory Small_Proof 
  imports Common_Proof Small
begin

lemma tick_toCurrentList: "invariant small \<Longrightarrow> toCurrentList (tick small) = toCurrentList small"
  apply(induction small rule: tick.induct)
  by(auto simp: tick_toCurrentList split: current.splits)

lemma tick_toList: "invariant small \<Longrightarrow> toList (tick small) = toList small"
proof(induction small rule: toList.induct)
  case (1 common)
  then show ?case by(auto simp: tick_toList)
next
  case (2 extra uu uv remained aux big new count)
  then show ?case 
    apply(auto simp: revN_take)
    using empty apply blast
        apply (simp add: not_empty_2 size_listLength)
    using not_empty apply blast
      apply (metis Stack_Proof.size_pop Suc_pred add_diff_cancel_left' first_pop rev.simps(2))
     apply (metis Nat.add_0_right add.commute append_Nil2 empty length_0_conv length_rev not_empty not_gr_zero)
    by (metis diff_add_inverse first_pop length_Cons rev.simps(2) size_listLength)
next
  case (3 v va vb)
  (* HOW?! *)

  have "Small.toList (Reverse1 v (Stack.pop va) (first va # vb)) = Small.toList (Reverse1 v va vb)"
    sorry

  show ?case 
    apply(auto split: current.splits) 
    sorry
qed

lemma invariant_tick: "invariant small \<Longrightarrow> invariant (tick small)" 
proof(induction small rule: tick.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invariant_tick)
next
  case (2 current small aux)
  then show ?case
    apply(auto simp: Stack_Proof.pop size_listLength split: current.splits)
    sorry
next
  case (3 current auxS big newS count)
  then show ?case
    apply(auto simp: split: current.splits) 
          apply (metis length_0_conv not_empty_2 size_listLength)
    using not_empty apply blast
        apply (meson add_decreasing le_less_linear not_empty)
    using not_empty apply blast
      apply(auto simp: revN_take)
      apply (metis Nat.add_0_right add.commute empty le_refl list.size(3) size_listLength take_all)
     apply (simp add: Stack_Proof.size_pop)
    by (metis first_pop length_Cons size_listLength)
qed

lemma invariant_push: "invariant small \<Longrightarrow> invariant (push x small)"
  apply(induction x small rule: push.induct)
  by(auto simp: invariant_push split: current.splits)

lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty small; 
  invariant small;
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> invariant small'"
proof(induction small arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: invariant_pop split: prod.splits)
next
  case (2 current small aux)
  then show ?case 
    apply(induction current rule: get.induct)
     apply(auto simp: Stack_Proof.size_pop)
    using diff_le_mono apply blast
     apply (meson less_Suc_eq_le less_imp_diff_less)
    sorry
next
  case (3 current auxS big newS count)
  then show ?case 
     apply(induction current rule: get.induct)
     apply(auto simp: Stack_Proof.size_pop)
    apply (metis length_greater_0_conv less_eq_Suc_le not_empty_2 ordered_cancel_comm_monoid_diff_class.diff_add_assoc size_listLength)
    using diff_le_mono le_add2 apply blast
            apply (meson diff_le_self le_trans)
    sorry
    (*apply (metis Suc_leI length_greater_0_conv not_empty_2 ordered_cancel_comm_monoid_diff_class.diff_add_assoc size_listLength)
   by auto *)
qed

lemma invariant_pop_2_helper: "\<lbrakk>
  0 < Stack.size old; 
  Stack.size old \<le> Stack.size small + List.length auxS;
  Stack.toList old = 
    rev (take (Stack.size old - List.length (Stack.toList small)) auxS) @ 
    rev (take (Stack.size old) (rev (Stack.toList small)))
\<rbrakk> \<Longrightarrow> Stack.toList (Stack.pop old) =
        rev (take (Stack.size (Stack.pop old) - List.length (Stack.toList small)) auxS) @
        rev (take (Stack.size (Stack.pop old)) (rev (Stack.toList small)))"
proof(induction "Stack.size old \<le> Stack.size small")
  case True
  then show ?case 
    apply auto
    by (smt (z3) Stack_Proof.pop Stack_Proof.size_pop Suc_diff_le Suc_pred diff_Suc_Suc diff_is_0_eq' drop_Suc length_rev nat_le_linear not_empty not_less_eq_eq rev.simps(1) rev_take self_append_conv2 size_listLength take_eq_Nil tl_drop)
next
  case False
  then show ?case
    apply auto
    by (smt (verit) False(2) Stack_Proof.pop Stack_Proof.size_pop Suc_diff_le Suc_pred diff_Suc_Suc diff_diff_left diff_is_0_eq drop_Suc le_add_diff_inverse length_0_conv length_rev less_Suc_eq_le less_imp_diff_less not_empty not_less_eq_eq rev_take size_listLength take_eq_Nil tl_append2 tl_drop)
qed

lemma invariant_pop_2: "\<lbrakk>
  0 < Small.size small; 
  invariant small;
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> invariant small'"
proof(induction small arbitrary: x rule: pop.induct)
case (1 state)
  then show ?case by(auto simp: invariant_pop_2 split: prod.splits)
next
  case (2 current small auxS)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto)
        apply (simp add: Stack_Proof.size_pop not_empty)
       apply (simp add: Stack_Proof.size_pop not_empty)
      by (simp add: invariant_pop_2_helper)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case (3 current auxS big newS count)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply auto 
         apply (simp add: Stack_Proof.size_pop not_empty)+
      by (simp add: Stack_Proof.pop Suc_diff_le drop_Suc not_empty rev_take tl_drop)
  next
    case (2 x xs added old remained)
    then show ?case by auto 
  qed
qed

lemma push: "toList (push x small) = x # toList small"
proof(induction x small rule: push.induct)
  case (1 x state)
  then show ?case 
    apply auto
    using Common_Proof.push by fastforce
next
  case (2 x current small auxS)
  then show ?case 
  proof(induction x current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case apply auto
      (* undefined! *)
      sorry
  qed
next
  case (3 x current auxS big newS count)
  then show ?case 
  proof(induction x current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case by auto
  qed
qed


lemma pop: "\<not>isEmpty small \<Longrightarrow> invariant small \<Longrightarrow> pop small = (x, small') \<Longrightarrow> x # toList small' = toList small"
  sorry

lemma currentList_push: "toCurrentList (push x small) = x # toCurrentList small"
  apply(induction x small rule: push.induct)
  by(auto simp: currentList_push put)

lemma currentList_pop: "\<not> isEmpty small \<Longrightarrow> pop small = (x, small') \<Longrightarrow> toCurrentList small' = tl (toCurrentList small)"
  apply(induction small arbitrary: x rule: pop.induct)
    apply(auto simp: currentList_pop put split: prod.splits)
   apply (metis get list.sel(3))
  by (metis get list.sel(3))

lemma currentList_pop_2: "invariant small \<Longrightarrow> 0 < size small \<Longrightarrow> pop small = (x, small') \<Longrightarrow> toCurrentList small' = tl (toCurrentList small)"
  apply(induction small arbitrary: x rule: pop.induct)
    apply(auto simp: Common_Proof.currentList_pop_2 put get_2 split: prod.splits current.splits)
  subgoal sorry (* just times out *)
  apply (smt (z3) Current.invariant.simps Current.size.simps Current.toList.simps Suc_diff_Suc Suc_pred \<open>\<And>x4 x3 x2 x1a x1 smalla auxS. \<lbrakk>get (Current x1a (List.length x1a) x3 x4) = (x1, x2); small' = Reverse1 x2 smalla auxS; Stack.size x3 \<le> x4; Stack.size x3 \<le> Stack.size smalla + List.length auxS; Stack.toList x3 = rev (take (Stack.size x3 - List.length (Stack.toList smalla)) auxS) @ rev (take (Stack.size x3) (rev (Stack.toList smalla))); x1a \<noteq> []\<rbrakk> \<Longrightarrow> Current.toList x2 = tl x1a @ rev (take (Stack.size x3 - List.length (Stack.toList smalla)) auxS) @ rev (take (Stack.size x3) (rev (Stack.toList smalla)))\<close> diff_add_inverse get_2 less_imp_add_positive list.sel(3) list.size(3) tl_append2)
   apply (metis Current.toList.simps Pair_inject get.simps(2) list.exhaust_sel)
  by (metis Current.isEmpty.simps Current.toList.simps add_is_0 empty_size get list.sel(3) not_empty)

lemma currentList_empty: "\<lbrakk>\<not> isEmpty small; toCurrentList small = []; invariant small\<rbrakk> \<Longrightarrow> False"
  apply(induction small)
  using currentList_empty by(auto simp: not_empty_2 split: current.splits)

lemma currentList_empty_2: "\<lbrakk>0 < size small; toCurrentList small = []; invariant small\<rbrakk> \<Longrightarrow> False"
  apply(induction small)
    apply(auto  split: current.splits)
   apply (simp add: size_listLength)
  using currentList_empty_2 by blast

lemma tick_size: "invariant small \<Longrightarrow> size small = size (tick small)"
  apply(induction small rule: tick.induct)
  by(auto simp: tick_size split: current.splits)

lemma tick_not_empty: "invariant small \<Longrightarrow> \<not>isEmpty small \<Longrightarrow> \<not>isEmpty (tick small)"
  apply(induction small rule: tick.induct)
  apply(auto simp: tick_not_empty split: current.splits)
  using not_empty_2 apply blast
  using Stack.isEmpty.elims(2) by blast
  
lemma push_not_empty: "\<lbrakk>\<not> isEmpty small; isEmpty (push x small)\<rbrakk> \<Longrightarrow> False"
  apply(induction x small rule: push.induct)
    apply(auto simp: push_not_empty put_not_empty)
  apply (meson Common_Proof.push_not_empty)
  by (meson put_not_empty)+

lemma size_empty: "invariant small \<Longrightarrow> size small = 0 \<Longrightarrow> isEmpty small"
  apply(induction small)
  by(auto simp: size_empty Current_Proof.size_empty empty_size split: current.splits)

end