theory Common_Proof
  imports Common Idle_Proof Current_Proof
begin

lemma take_hd: "xs \<noteq> [] \<Longrightarrow> take (Suc 0) xs = [hd xs]"
  apply(induction xs)
  by auto

lemma helping_1_1: "\<lbrakk>a \<le> Suc b; b < a\<rbrakk> \<Longrightarrow> a - b = 1"
  by auto

lemma helping_1: "\<lbrakk>
  Stack.toList x3b = take (Stack.size x3b) (drop (length x2 + length x3 - x4) (rev x2)) @ take (Stack.size x3b + length x3 - x4) x3;
  x4 \<le> length x2 + length x3; 
  x4 \<le> Suc (length x3); 
  length x3 < x4
\<rbrakk> \<Longrightarrow> take (x4 - length x3) x2 = [hd x2]"
  apply(auto simp: helping_1_1)
  apply(induction x2)
  by auto

lemma helping_2: "\<lbrakk>
  Stack.toList x3b = take (Stack.size x3b) (drop (length x2 + length x3 - x4) (rev x2)) @ take (Stack.size x3b + length x3 - x4) x3;
  x4 \<le> length x2 + length x3; 
  \<not> x4 \<le> Suc (length x3)
\<rbrakk> \<Longrightarrow> rev (take (x4 - Suc (length x3)) (tl x2)) @ [hd x2] = rev (take (x4 - length x3) x2)"
  (* TODO:* *)
  by (metis Suc_diff_Suc le_SucI length_greater_0_conv less_add_same_cancel2 less_le_trans not_le_imp_less rev.simps(2) take_Suc)

lemma tick: "invariant common \<Longrightarrow> toList (tick common) = toList common"
  apply(induction common)
  by(auto simp: take_hd helping_1 helping_2  split: current.splits)

lemma tick_2: "invariant common \<Longrightarrow> tick common = common' \<Longrightarrow> toList common = toList common'" 
  by(auto simp: tick)

lemma helper_pop_1: "\<lbrakk>remained > length new; remained - Suc 0 \<le> length new\<rbrakk> \<Longrightarrow> remained - length new = 1"
  by auto

lemma helper_pop_2: "\<lbrakk>
  \<not> remained \<le> length new; \<not> Stack.isEmpty old;
  Stack.toList old =
  take (Stack.size old) (drop (length aux + length new - remained) (rev aux)) @ take (Stack.size old + length new - remained) new;
  x = first old;
  common' = Copy (Current [] 0 (Stack.pop old) (remained - Suc 0)) aux new (length new); moved = length new;
  remained \<le> length aux + length new; added = 0;
  \<not> remained - Suc 0 \<le> length new
\<rbrakk> \<Longrightarrow> first old # drop (Suc (length aux + length new) - remained) (rev aux) = 
      drop (length aux + length new - remained) (rev aux)"
  apply(induction old rule: Stack.pop.induct)
    apply(auto simp: )
  apply (smt (verit, ccfv_threshold) Cons_nth_drop_Suc Nat.diff_diff_right Suc_diff_le add_Suc append_Cons append_Nil2 diff_diff_cancel diff_is_0_eq hd_take length_drop length_rev list.sel(1) nat_le_linear not_le take_all_iff take_eq_Nil zero_less_Suc)
  by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc Nat.diff_diff_right Nil_is_append_conv Stack.toList.simps Suc_diff_le add_Suc append_Cons append_Nil2 diff_diff_cancel diff_is_0_eq drop_all_iff empty first hd_take le_diff_conv length_drop length_rev list.sel(1) nat_le_linear not_le self_append_conv2 take_all_iff take_eq_Nil zero_less_Suc)


lemma pop: "\<lbrakk>invariant common; \<not> isEmpty common; pop common = (x, common')\<rbrakk>
   \<Longrightarrow> x # toList common' = toList common"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 idle)
  then show ?case 
    by(auto simp: Idle_Proof.pop split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
    proof(induction "moved \<ge> remained")
      case True
      then show ?case by auto
    next
      case False
      then show ?case
        apply(auto simp: rev_take helper_pop_2 helper_pop_1)
        by (smt (verit, best) Suc_pred add.commute add_diff_cancel_right' append.right_neutral append_eq_Cons_conv append_eq_conv_conj cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel diff_is_0_eq' dual_order.trans first hd_take helping_1 le_0_eq le_add1 le_add2 le_diff_conv le_diff_iff le_less_Suc_eq length_drop length_greater_0_conv length_rev lessI linear list.size(3) not_empty_2 not_le_imp_less not_less_eq_eq ordered_cancel_comm_monoid_diff_class.diff_diff_right rev.simps(1) rev.simps(2) rev_take size_listLength take_Nil take_all take_all_iff take_eq_Nil take_hd)
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed


lemma push: "toList (push x common) = x # toList common"
proof(induction x common rule: push.induct)
  case (1 x stack stackSize)
  then show ?case by(auto simp: Stack_Proof.push)
next
  case (2 x current aux new moved)
  then show ?case 
    apply(induction x current rule: put.induct)
    by auto
qed


lemma invariant_tick: "invariant common \<Longrightarrow> invariant (tick common)" 
proof(induction "common" rule: invariant.induct)
  case (1 idle)
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
        by auto
     qed
  qed
qed

  
lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
  apply(induction x common rule: push.induct)
  by(auto simp: Stack_Proof.size_push split: stack.splits current.splits)

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
  case (1 idle)
  then show ?case 
    by(auto simp: invariant_pop split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
    proof(induction old rule: Stack.pop.induct)
      case (1 x left right)
      then show ?case
        apply auto
        apply (smt (verit, del_insts) Stack.isEmpty.simps(2) Stack.pop.simps(1) Stack.size.simps Stack.toList.simps append_Cons helper_y length_Cons length_append)
        by (meson diff_le_self order_trans)
    next
      case (2 x right)
      then show ?case 
        apply auto
        apply (smt (verit) Stack.isEmpty.elims(2) Stack.pop.simps(2) Stack.size.simps Stack.toList.simps add.commute append_Nil gen_length_def helper_x helper_y length_code list.discI list.size(3))
        by (meson diff_le_self dual_order.trans)
    next
      case 3
      then show ?case by auto
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
   \<Longrightarrow> \<exists> idle. (tick^^ remainingSteps state) state = Idle idle"
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

  then have "\<exists> idle. (tick^^ x) state' = Idle idle"
    using Suc.hyps(1) \<open>Common.invariant state'\<close> by blast

  then show ?case
    by (simp add: Suc.hyps(2) x)
qed

end