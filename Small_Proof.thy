theory Small_Proof 
  imports Common_Proof Small
begin

lemma tick_toCurrentList: "invariant small \<Longrightarrow> toCurrentList (tick small) = toCurrentList small"
  apply(induction small rule: tick.induct)
  by(auto simp: tick_toCurrentList split: current.splits)

lemma invariant_tick: "invariant small \<Longrightarrow> invariant (tick small)" 
proof(induction small rule: tick.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invariant_tick)
next
  case (2 current uu aux)
  then show ?case
    by(auto simp: Stack_Proof.pop size_listLength split: current.splits)
next
  case (3 current big aux v)
  then show ?case
    apply (auto simp: Stack_Proof.size_pop not_empty not_empty_2 size_listLength split: current.splits)
    using not_empty_2 apply blast
     apply (metis add_cancel_left_left empty length_0_conv)
    by (metis first_pop length_Cons)
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
    by(auto simp: Stack_Proof.size_pop)
next
  case (3 current auxS big newS count)
  then show ?case 
     apply(induction current rule: get.induct)
     apply(auto simp: Stack_Proof.size_pop)
    apply (metis length_greater_0_conv less_eq_Suc_le not_empty_2 ordered_cancel_comm_monoid_diff_class.diff_add_assoc size_listLength)
    by auto
qed

lemma currentList_push: "toCurrentList (push x small) = x # toCurrentList small"
  apply(induction x small rule: push.induct)
  by(auto simp: currentList_push put)

end