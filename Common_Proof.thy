theory Common_Proof
  imports Common Idle_Proof Current_Proof
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
  
lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
  apply(induction x common rule: push.induct)
  by(auto split: stack.splits current.splits)

lemma helper_x: " \<not> Stack.isEmpty stack \<Longrightarrow> Suc (Stack.size (Stack.pop stack) + x) = Stack.size stack + x"
  apply(induction stack rule: Stack.pop.induct)
  by auto

lemma helper_y: " \<lbrakk>
  \<not> Stack.isEmpty old;
  Stack.toList old = take (Stack.size old) (drop (length aux + length new - remained) (rev aux)) @ take (Stack.size old + length new - remained) new;
  x = first old;
  common' = Copy (Current [] 0 (Stack.pop old) (remained - Suc 0)) aux new (length new); 
  length new < remained; moved = length new;
  remained \<le> length aux + length new;
  added = 0;
  \<not> remained - Suc 0 \<le> length new
\<rbrakk> \<Longrightarrow> Stack.toList (Stack.pop old) =
         take (Stack.size (Stack.pop old)) (drop (Suc (length aux + length new) - remained) (rev aux)) @
         take (Suc (Stack.size (Stack.pop old) + length new) - remained) new"
proof(induction "Stack.size (Stack.pop old)")
  case 0
  then show ?case apply auto
    by (metis length_0_conv size_listLength)
next
  case (Suc xa)
  then show ?case apply auto
    by (smt (z3) Nat.diff_diff_right Stack_Proof.pop Suc_diff_le diff_diff_cancel diff_is_0_eq drop_Suc drop_all_iff first_pop helper_x leD le_diff_conv length_Cons length_rev less_or_eq_imp_le size_listLength take_eq_Nil take_tl tl_append2 tl_drop zero_less_Suc)
qed

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
      using Stack.isEmpty.simps(1) Stack.pop.elims 
       apply blast
      using Stack_Proof.size_pop by fastforce
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
    proof(induction "length new < Stack.size (Stack.pop old)")
      case True
      then show ?case 
        apply auto
        apply (smt (verit) Nat.add_0_right Nat.diff_diff_right Stack_Proof.pop Stack_Proof.size_pop Suc_diff_Suc Suc_diff_diff Suc_diff_le Suc_leI add_Suc_right append.right_neutral append_Nil2 append_take_drop_id bot_nat_0.extremum diff_Suc_Suc diff_add_inverse diff_diff_cancel diff_diff_left diff_is_0_eq' first_pop le0 le_diff_conv length_Cons length_append length_drop length_rev less_or_eq_imp_le list.size(3) list.size(3) nat.inject nat_less_le nat_neq_iff not_le old.nat.inject size_listLength)
        apply(simp add: helper_y)
        by (meson diff_le_self le_trans)
    next
      case False
      then show ?case 
        apply auto
        apply (smt (verit, best) Cons_nth_drop_Suc Stack_Proof.pop Stack_Proof.size_pop Suc_pred add_diff_cancel_right' append_Nil2 append_eq_append_conv2 diff_diff_cancel diff_diff_left diff_is_0_eq' le_diff_conv length_0_conv length_drop length_rev less_imp_le list.sel(3) not_le ordered_cancel_comm_monoid_diff_class.diff_diff_right same_append_eq size_listLength take_all take_eq_Nil tl_append2 zero_less_diff)
        apply(simp add: helper_y)
        using diff_le_self dual_order.trans by blast
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed   
qed

lemma invariant_ticks: "invariant common \<Longrightarrow> invariant ((tick^^n) common)"
  apply(induction n)
  by(auto simp: invariant_tick)

lemma remainingSteps: "remainingSteps state > 0 \<Longrightarrow> remainingSteps state = Suc (remainingSteps (tick state))"
  apply(induction state rule: remainingSteps.induct)
  by auto

lemma tickN: "invariant state
   \<Longrightarrow> \<exists>current idle. (tick^^ remainingSteps state) state = Idle current idle"
proof(induction "remainingSteps state" arbitrary: state)
case 0
  then show ?case
    apply(induction state)
    by(auto split: current.splits)
next
  case (Suc x)
  obtain state' where state': "state' = tick state"
    by auto
  
  then have "invariant state'"
    by(auto simp: Suc.prems invariant_tick)
  
  have x: "(tick^^ x) state' = (tick^^ Suc x) state"
    by(auto simp: state' funpow_swap1)
  
  then have "remainingSteps state' = x"
    by (metis Suc.hyps(2) nat.inject remainingSteps state' zero_less_Suc)

  then have "\<exists>current idle. (tick^^ x) state' = Idle current idle"
    using Suc.hyps(1) \<open>Common.invariant state'\<close> by blast

  then show ?case
    by (simp add: Suc.hyps(2) x)
qed

end