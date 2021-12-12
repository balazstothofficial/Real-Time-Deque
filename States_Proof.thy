theory States_Proof
  imports States Big_Proof Small_Proof
begin

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits
lemmas invariant_ticks = Big_Proof.invariant_tick Common_Proof.invariant_tick Small_Proof.invariant_tick

lemma tick_toListSmall: "\<lbrakk>
 tick (big, small) = (big', small')
\<rbrakk> \<Longrightarrow> Small.toList small = Small.toList small'"
  apply(induction "(big, small)" rule: tick.induct)
  by(auto simp: Common_Proof.tick Small_Proof.tick split: current.splits)

lemma tick_toListBig: "\<lbrakk>
 tick (big, small) = (big', small')
\<rbrakk> \<Longrightarrow> Big.toList big = Big.toList big'"
  apply(induction "(big, small)" rule: tick.induct)
  by(auto simp: Common_Proof.tick Big_Proof.tick split: current.splits)

corollary tick_toList:  "\<lbrakk>
 tick (big, small) = (big', small')
\<rbrakk> \<Longrightarrow> Big.toList big = Big.toList big' \<and> Small.toList small = Small.toList small'"
  by(simp add: tick_toListBig tick_toListSmall)

lemma invariant_tick: "invariant states \<Longrightarrow> invariant (tick states)"
proof(induction states rule: tick.induct)
(* TODO: *)
case (1 currentB big auxB currentS uu auxS)
  then show ?case 
    apply(auto split: current.splits)
      apply (metis length_0_conv size_listLength)
     apply (metis le_refl size_listLength take_all)
    by (metis length_0_conv size_listLength)
next
  case ("2_1" v va vb vd right)
  then show ?case 
    apply(auto simp: invariant_ticks split: current.splits)
      apply (metis Stack_Proof.pop Zero_not_Suc bot_nat_0.extremum_uniqueI empty first list.size(3) size_listLength take_Suc)
    apply (metis One_nat_def Stack_Proof.size_pop Suc_diff_eq_diff_pred diff_is_0_eq less_le_trans not_empty zero_less_Suc)
    apply(auto simp: Let_def split: state_splits current.splits)
    apply (metis One_nat_def Stack_Proof.size_pop diff_Suc_eq_diff_pred less_le_trans not_empty zero_less_Suc)
      apply (metis le_SucE not_empty zero_less_Suc)
    apply (metis One_nat_def Stack_Proof.size_pop bot_nat_0.extremum_uniqueI diff_Suc_eq_diff_pred nat.discI not_empty not_le)
    by (metis Suc_n_not_le_n add_le_mono helper_x not_less_eq_eq)
next
  case ("2_2" v right)
  then show ?case 
    by(auto simp: invariant_ticks split: Small.state.splits current.splits)
next
  case ("2_3" left v va vb vc vd)
  then show ?case
    apply(auto simp: invariant_ticks split: state_splits current.splits) 
    apply (metis (full_types) length_0_conv not_empty_2 size_listLength)+
    using not_empty apply blast
    apply (metis diff_diff_left diff_zero empty le_refl list.size(3) size_listLength take_all)
    apply (meson not_empty)
    apply (meson add_decreasing not_empty not_le_imp_less)
    apply (metis Stack_Proof.size_pop Suc_pred)
    apply (metis first_pop length_Cons size_listLength)
    apply (meson not_empty)
    apply (metis diff_diff_add empty list.size(3) minus_nat.diff_0 order_refl size_listLength take_all_iff)
    apply (meson not_empty)
    apply (meson add_decreasing not_empty not_le_imp_less)
    apply (metis Stack_Proof.size_pop Suc_pred)
    apply (metis first_pop length_Cons size_listLength)
    apply (metis length_0_conv not_empty_2 size_listLength)
    using not_empty apply blast
    apply (metis Nat.add_0_right add.commute le_refl neq0_conv not_empty size_listLength take_all)
    using not_empty apply blast
    apply (meson add_decreasing not_empty not_le_imp_less)
    apply (simp add: Stack_Proof.size_pop)
    by (metis first_pop length_Cons size_listLength)
next
  case ("2_4" left v)
  then show ?case
    by(auto simp: invariant_ticks split: state_splits)
qed

lemma invariant_pushSmall: "invariant (big, small) \<Longrightarrow> invariant (big, Small.push x small)"
proof(induction x small rule: Small.push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: Common_Proof.invariant_push split: state_splits)
next
  case (2 x current small auxS)
  then show ?case 
    by(auto split: state_splits current.splits)
next
  case (3 x current auxS big newS count)
  then show ?case
    by(auto split: state_splits current.splits)
qed

lemma invariant_pushBig: "invariant (big, small) \<Longrightarrow> invariant (Big.push x big, small)"
proof(induction x big rule: Big.push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: Common_Proof.invariant_push)
next
  case (2 x current big auxB count)
  then show ?case
    by(auto split: current.splits)
qed

(* TODO: Pops not yet fully proven! *)

lemma helper: "\<lbrakk>
  Stack.toList old = drop (List.length auxS + Stack.size small - Stack.size old) (rev auxS) @ drop (Stack.size small - Stack.size old) (Stack.toList small);
  added = 0;
  Stack.size old \<le> remained; 
  Stack.size old \<le> Stack.size small + List.length auxS;
  big = Reverse (Current x1 (List.length x1) x3 x4) x12 x13 x14; \<not> Stack.isEmpty old; 
  Stack.size x12 - x14 = remained - Stack.size old;
  Stack.size small \<le> x14; 
  Stack.toList x3 = drop (List.length x13 + x14 - x4) (rev x13) @ take x14 (Stack.toList x12);
  x4 - x14 \<le> List.length x13; 
  x14 \<le> x4; 
  x14 \<le> Stack.size x12
\<rbrakk> \<Longrightarrow> Stack.toList (Stack.pop old) =
            drop (List.length auxS + Stack.size small - (Stack.size old - Suc 0)) (rev auxS) @
            drop (Stack.size small - (Stack.size old - Suc 0)) (Stack.toList small)"
proof(induction "Stack.size small < (Stack.size old - Suc 0)")
  case True
  then show ?case
    apply auto
    by (metis Stack_Proof.pop Suc_diff_le add.commute diff_le_self drop_Suc not_less self_append_conv2 size_listLength tl_append2 tl_drop)
next
  case False
  then show ?case
  proof(induction "List.length auxS")
    case 0
    then show ?case 
      apply auto
      by (metis False.prems(6) One_nat_def Stack_Proof.pop Suc_diff_eq_diff_pred Suc_diff_le add.left_neutral add_diff_cancel_left' bot_nat_0.extremum_uniqueI drop_Suc drop_all eq_iff not_empty_2 not_le size_listLength tl_drop trans_le_add2)
  next
    case (Suc x)
    then show ?case 
    sorry
  qed
qed

lemma helper_2: " \<lbrakk>
  \<not> Stack.isEmpty old; 
  Common.invariant x2;
 Stack.toList old =
 drop (List.length auxS + Stack.size small - Stack.size old) (rev auxS) @ drop (Stack.size small - Stack.size old) (Stack.toList small);
 added = 0; Stack.size old \<le> remained; Stack.size old \<le> Stack.size small + List.length auxS; big = Big.state.Common x2; x = first old;
 small' = Reverse1 (Current [] 0 (Stack.pop old) (remained - Suc 0)) small auxS\<rbrakk>
    \<Longrightarrow> Stack.toList (Stack.pop old) =
         drop (List.length auxS + Stack.size small - (Stack.size old - Suc 0)) (rev auxS) @
         drop (Stack.size small - (Stack.size old - Suc 0)) (Stack.toList small)"
proof(induction "Stack.size small < (Stack.size old - Suc 0)")
  case True
  then show ?case 
    apply auto
    by (metis Stack_Proof.pop Suc_diff_le add.commute append_self_conv2 diff_le_self drop_Suc leD size_listLength tl_append2 tl_drop)
next
  case False
  then show ?case 
    apply auto 
    sorry
qed

lemma invariant_popSmall: "\<lbrakk>
  invariant (big, small);
  \<not> Small.isEmpty small;
  Small.pop small = (x, small')
\<rbrakk> \<Longrightarrow> invariant (big, small')"
proof(induction small rule: Small.pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: Common_Proof.invariant_pop split: state_splits current.splits prod.splits)
next
  case (2 current small auxS)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: helper_2 helper Let_def Stack_Proof.size_pop split: state_splits current.splits) 
      by (metis Suc_pred length_0_conv neq0_conv not_empty_2 size_listLength)
  next
    case (2 x xs added old remained)
    then show ?case by(auto simp: Let_def split: state_splits)
  qed
next
  case (3 current auxS big newS count)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: Stack_Proof.size_pop split: state_splits current.splits)
      apply (metis One_nat_def Stack_Proof.pop Suc_diff_eq_diff_pred Suc_diff_le drop_Suc length_greater_0_conv not_empty_2 size_listLength tl_drop)
      apply (metis Nat.add_diff_assoc Suc_pred diff_is_0_eq length_greater_0_conv nat_le_linear not_empty_2 size_listLength)
      apply (metis One_nat_def Stack_Proof.pop Suc_diff_eq_diff_pred Suc_diff_le drop_Suc length_greater_0_conv not_empty_2 size_listLength tl_drop)
      by (metis Nat.diff_add_assoc Suc_leI gr0I not_empty_2 rev_is_Nil_conv rev_take take_eq_Nil)
  next
    case (2 x xs added old remained)
    then show ?case by(auto split: state_splits)
  qed
qed

lemma invariant_popBig: "\<lbrakk>
  invariant (big, small);
  \<not> Big.isEmpty big;
  Big.pop big = (x, big')
\<rbrakk> \<Longrightarrow> invariant (big', small)"
proof(induction big arbitrary: x small rule: Big.pop.induct)
case (1 state)
  then show ?case
    by(auto simp: Common_Proof.invariant_pop split: prod.splits)
next
  case (2 current big auxB count)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: Let_def split: current.splits state_splits)
         sorry
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma terminates: "States.invariant states \<Longrightarrow> States.terminateTicks states \<noteq> None"
  apply(induction states rule: States.terminateTicks.induct)
  by (simp) (metis States.terminateTicks.simps States_Proof.invariant_tick)+

end
