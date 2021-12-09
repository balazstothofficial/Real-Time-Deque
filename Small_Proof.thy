theory Small_Proof 
  imports Common_Proof Small
begin

lemma tick: "toList (tick state) = toList state"
  apply(induction state)
  by(auto simp: tick split: current.splits)

lemma push: "x # toList small = toList (push x small)"
  apply(induction x small rule: push.induct)
  by(auto simp: push put)

lemma pop: "\<lbrakk>\<not> isEmpty small; pop small = (x, small')\<rbrakk> \<Longrightarrow> x # toList small' = toList small"
  apply(induction small arbitrary: x rule: pop.induct)
  by(auto simp: get Common_Proof.pop split: prod.splits current.splits if_splits)

lemma invariant_tick: "invariant state \<Longrightarrow> invariant (tick state)"
proof(induction state rule: tick.induct)
  case (1 state)
  then show ?case 
    by (simp add: invariant_tick)
next
  case (2 current small auxS)
  then show ?case 
    apply(auto simp: Let_def split: current.splits)
    (* TODO: *)
     apply (metis add_Suc_right first_pop length_Cons size_listLength)
    by (metis helper_x)
next
  case (3 current auxS big newS count)
  then show ?case 
    (* TODO: *)
    apply(auto simp: not_empty size_pop split: current.splits)
       apply (metis length_0_conv not_empty_2 size_listLength)
    apply (smt (verit, best) Nat.diff_diff_right add_cancel_left_left add_diff_cancel_right' append_Nil2 diff_le_self empty le_add2 length_drop length_rev list.size(3) size_listLength take_all take_eq_Nil)
      apply (metis length_drop length_rev less_add_same_cancel2 less_imp_diff_less not_empty not_less size_listLength)
     apply (simp add: Stack_Proof.size_pop not_empty)
    by (metis Nat.add_0_right helper_x)
qed

lemma invariant_push: "invariant small \<Longrightarrow> invariant (push x small)"
proof(induction x small rule: push.induct)
  case (1 x state)
then show ?case by(auto simp: invariant_push)
next
  case (2 x current small auxS)
  then show ?case by(auto split: current.splits)
next
  case (3 x current auxS big newS count)
  then show ?case by(auto split: current.splits)
qed
 
lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty small; 
  invariant small; 
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> invariant small'"
(* TODO: *)
proof(induction small arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invariant_pop split: prod.splits)
next
  case (2 current small auxS)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: Let_def)
      apply (smt (verit, ccfv_threshold) Cons_nth_drop_Suc append_Nil diff_Suc_Suc diff_diff_cancel diff_is_0_eq drop_all drop_all_iff first_pop gen_length_def le_add2 le_eq_less_or_eq length_Cons length_append length_code length_drop length_rev list.sel(3) minus_nat.diff_0 nat_le_linear not_less_eq_eq size_listLength tl_append2) 
      apply (metis Stack_Proof.size_pop diff_le_mono)
      by (simp add:  Stack_Proof.size_pop)
  next
    case (2 x xs added old remained)
    then show ?case by(auto simp: Let_def)
  qed
next
  case (3 current auxS big newS count)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply auto
      apply (metis Stack_Proof.pop Suc_diff_le diff_Suc_Suc drop_Suc first_pop length_Cons size_listLength tl_drop)
       apply (metis Nat.diff_add_assoc Suc_leI length_greater_0_conv not_empty_2 size_listLength Stack_Proof.size_pop)
       apply (metis diff_le_mono le_add2 Stack_Proof.size_pop)
      by (simp add: Stack_Proof.size_pop)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

end