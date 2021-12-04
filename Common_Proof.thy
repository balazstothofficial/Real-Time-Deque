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
        by (metis length_Cons length_take size_listLength)
     qed
  qed
qed

value "tick ( Copy (Current [] 0 (Stack [] [a\<^sub>1]) 1) [a\<^sub>2, a\<^sub>1] [] 0)"
  
lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
  apply(induction x common rule: push.induct)
  by(auto split: stack.splits current.splits)

lemma helper_x: " \<not> Stack.isEmpty stack \<Longrightarrow> Suc (Stack.size (Stack.pop stack) + x) = Stack.size stack + x"
  apply(induction stack rule: Stack.pop.induct)
  by auto

lemma helper_x2: "\<lbrakk>
  \<not> length new < Stack.size (Stack.pop old);
  \<not> length new < Stack.size old;
  \<not> Stack.isEmpty old;
  Stack.toList old = take (Stack.size old) (drop (length aux + length new - remained) (rev aux)) @ take (Stack.size old + length new - remained) new;
  x = first old;
  common' = Copy (Current [] 0 (Stack.pop old) (remained - Suc 0)) aux new (length new); 
  length new < remained; 
  moved = length new;
  remained \<le> length aux + length new; added = 0;
  \<not> remained - Suc 0 \<le> length new
\<rbrakk> \<Longrightarrow> Stack.toList (Stack.pop old) =
         take (Stack.size (Stack.pop old)) (drop (Suc (length aux + length new) - remained) (rev aux)) @
         take (Stack.size old + length new - remained) new"
  apply(induction old rule: Stack.pop.induct)
    apply auto
  apply (smt (z3) Nat.diff_diff_right Suc_diff_le diff_diff_cancel diff_is_0_eq drop_Suc drop_all_iff leD le_diff_conv length_rev less_or_eq_imp_le list.sel(3) old.nat.distinct(2) take_eq_Nil take_tl tl_append2 tl_drop)
  (* TODO: *)
  sorry

(* TODO: *)
lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty common; 
  invariant common;
  pop common = (x, common')
\<rbrakk> \<Longrightarrow> invariant common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current stack stackSize)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
      apply(auto split: stack.splits current.splits prod.splits)
      apply (metis Stack.pop.simps(2) Stack.toList.simps Stack_Proof.pop append.left_neutral first_pop length_Cons size_listLength stack.inject take_tl)
      using Stack.isEmpty.simps(1) Stack.pop.elims apply blast
      using size_pop by fastforce
  next
    case (2 x xs added old remained)
    then show ?case by(auto split: stack.splits current.splits prod.splits)
  qed
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
    proof(induction "length new < Stack.size old")
      case True
      then show ?case 
        apply(auto simp: size_pop)
        apply (smt (z3) One_nat_def Suc_diff_Suc append_eq_conv_conj append_self_conv2 append_take_drop_id diff_Suc_eq_diff_pred diff_diff_cancel diff_is_0_eq' drop_Suc_Cons drop_rev first_pop le_diff_conv length_drop length_rev less_imp_le less_imp_le_nat ordered_cancel_comm_monoid_diff_class.diff_diff_right size_listLength take0 take_all)
        apply (smt (z3) Cons_nth_drop_Suc Nat.diff_diff_right Stack_Proof.pop Suc_diff_Suc Suc_diff_le diff_less diff_zero drop_all_iff length_greater_0_conv length_rev less_add_same_cancel2 less_le_trans less_or_eq_imp_le list.sel(3) list.size(3) not_le take_eq_Nil take_tl tl_append2 zero_less_diff)
        by (meson diff_le_self order_trans)
    next
      case False
      then show ?case
       proof(induction "length new < Stack.size (Stack.pop old)")
         case True
         then show ?case 
           by(auto simp: size_pop)
       next
         case False
         then show ?case  
           apply(auto simp: helper_x)
           apply (smt (verit, ccfv_SIG) Cons_nth_drop_Suc Stack_Proof.pop Suc_leI Suc_pred append_self_conv2 diff_diff_cancel drop_all_iff leD le_eq_less_or_eq length_drop length_greater_0_conv length_rev less_le_trans list.sel(3) nat_le_linear not_empty_2 ordered_cancel_comm_monoid_diff_class.diff_diff_right size_listLength size_pop take_all tl_append2)
           by(auto simp: helper_x2)
       qed
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed   
qed


end