theory Common_Proof
  imports Common Current_Proof
begin

lemma tick: "toList (tick common) = toList common"
  apply(induction common)
  by(auto split: current.splits)

lemma tick_2: "Common.tick common = common' \<Longrightarrow> Common.toList common = Common.toList common'"
  by(auto simp: tick)

lemma pop: "\<lbrakk>\<not> isEmpty common; pop common = (x, common')\<rbrakk> \<Longrightarrow> x # toList common' = toList common"
  apply(induction common arbitrary: x rule: pop.induct)
   apply(auto simp: get  split: prod.splits current.splits if_splits)
  using get by fastforce+

lemma push: "toList (push x common) = x # toList common"
  apply(induction x common rule: push.induct)
  by(auto simp: put)

lemma take_hd: "xs \<noteq> [] \<Longrightarrow> take (Suc 0) xs = [hd xs]"
  apply(induction xs)
  by auto
 
lemma invariant_tick: "invariant common \<Longrightarrow> invariant (tick common)" 
proof(induction "common" rule: invariant.induct)
  case (1 current idle)
  then show ?case
    by auto
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current)
    case (Current extra added old remained)
    then show ?case
    proof(induction aux)
      case Nil
      then show ?case
        by auto
    next
      case (Cons a as)
      then show ?case
        apply auto
        (* TODO: *)
        by (smt (verit, del_insts) Nat.add_diff_assoc add.commute add_Suc diff_is_0_eq' drop_Cons' le_add1 le_add_diff_inverse2 length_Cons length_append length_drop length_rev nat_less_le not_le size_listLength)
    qed
  qed
qed
  
lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
  apply(induction x common rule: push.induct)
  by(auto split: stack.splits current.splits)

lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty common; 
  invariant common;
   pop common = (x, common')
\<rbrakk> \<Longrightarrow> invariant common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current stack stackSize)
  then show ?case 
  proof(induction current)
    case (Current extra added old remained)
    then show ?case
    proof(induction "Current extra added old remained" rule: get.induct)
      case 1
      then show ?case 
      proof(induction stack arbitrary: x rule: Stack.pop.induct)
        case (1 x left right)
        then show ?case by auto
      next
        case (2 x right)
        then show ?case
        proof(induction old arbitrary: x rule: Stack.pop.induct)
          case (1 x' left' right')
          then show ?case 
            apply auto
            (* TODO: *)
            by (smt (z3) Cons_nth_drop_Suc add.commute add_diff_cancel_right' diff_commute diff_less_Suc drop_Suc_Cons drop_append length_Cons length_append list.inject)
        next
          case (2 x' right')
          then show ?case 
            apply auto 
            (* TODO: *)
            by (metis Cons_nth_drop_Suc diff_less_Suc drop_Suc_Cons length_Cons list.sel(3))
        next
          case 3
          then show ?case by auto
        qed
      next
        case 3
        then show ?case by auto
      qed
    next
      case (2 x xs)
      then show ?case
        by(auto split: stack.splits)
    qed
  qed
next
  case (2 current aux new moved)
  then show ?case 
  (* TODO: *)
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
    proof(induction "Stack.size old < length new")
      case True
      then show ?case 
        apply auto
        apply (smt (z3) Cons_nth_drop_Suc Suc_diff_le Suc_pred diff_Suc_Suc diff_diff_cancel diff_is_0_eq' drop0 first_pop length_greater_0_conv less_imp_le list.inject not_empty_2 not_le size_listLength size_pop)
        apply (smt (verit) Cons_nth_drop_Suc Suc_diff_le Suc_n_not_le_n add_diff_cancel_right' append_self_conv2 diff_Suc_Suc diff_is_0_eq diff_le_mono2 drop_all first_pop le_eq_less_or_eq length_rev linear list.inject minus_nat.diff_0 not_empty_2 size_pop)
        by (meson diff_le_self le_trans)
    next
      case False
      then show ?case
      proof(induction "Stack.size (Stack.pop old) < length new")
        case True
        then show ?case 
          apply auto
          apply (smt (z3) append_Nil diff_add_inverse diff_diff_cancel drop0 drop_Suc_Cons drop_all first_pop le_less_Suc_eq le_refl length_Cons length_rev nat_less_le nat_neq_iff size_listLength size_pop zero_less_diff) 
          apply (metis Suc_diff_le append_Nil diff_add_inverse2 diff_self_eq_0 drop0 drop_Suc_Cons drop_all_iff first_pop le_refl length_Cons length_rev nat_neq_iff not_less_eq size_listLength)
          using diff_le_self le_trans by blast
      next
        case False
        then show ?case 
          apply auto
          apply (smt (verit, ccfv_threshold) Stack_Proof.pop Suc_le_lessD Suc_pred add_diff_inverse_nat append_eq_append_conv append_take_drop_id diff_add_inverse2 drop_all_iff length_append length_drop length_greater_0_conv size_listLength size_pop tl_append2)
          apply (smt (z3) Cons_nth_drop_Suc Suc_le_lessD diff_add_inverse2 diff_is_0_eq diff_zero drop_all_iff first_pop le_eq_less_or_eq length_Cons length_append length_drop length_rev list.sel(3) nat_neq_iff size_listLength tl_append2)
          by presburger
      qed
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed
  
end