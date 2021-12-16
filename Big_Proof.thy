theory Big_Proof
  imports Big Common_Proof
begin

(*lemma helper: "Big.toList (Big.tick (Reverse x1 x2a x3 x4)) = Current.toList x1"
  apply(induction x4)
  by(auto split: current.splits)*)

value "toList ( (Reverse (Current [] 0 (Stack [a\<^sub>1] [a\<^sub>2]) 2) (Stack [] []) [a\<^sub>2, a\<^sub>1] 0))"

lemma tick: "invariant state \<Longrightarrow> toList (tick state) = toList state"
proof(induction state rule: tick.induct)
  case (1 state)
  then show ?case by(auto simp: tick)
next
  case (2 current uu aux)
  then show ?case by(auto split: current.splits)
next
  case (3 current big aux v)
  then show ?case
    apply(auto split: current.splits)
    sorry
qed
    

lemma invariant_tick: "invariant state \<Longrightarrow> invariant (tick state)"
proof(induction state rule: tick.induct)
  case (1 state)
  then show ?case 
    by (simp add: invariant_tick)
next
  case (2 current big auxB)
  then show ?case by(auto simp: size_listLength split: current.splits)
next
  case (3 current big auxB count)
  then show ?case 
    apply(auto split: current.splits)
    (* TODO: *)
     apply (metis Stack_Proof.pop Zero_not_Suc bot_nat_0.extremum_uniqueI empty first list.size(3) size_listLength take_Suc)
    by (metis (no_types, lifting) One_nat_def Stack_Proof.size_pop Suc_diff_eq_diff_pred Zero_not_Suc bot_nat_0.extremum_uniqueI diff_is_0_eq empty length_greater_0_conv list.size(3) size_listLength)
qed

lemma pop: "\<lbrakk>\<not> isEmpty big; pop big = (x, big')\<rbrakk> \<Longrightarrow> x # toList big' = toList big"
  apply(induction big arbitrary: x rule: pop.induct)
  by(auto simp: get Common_Proof.pop split: prod.splits current.splits if_splits)

lemma push: "toList (push x big) = x # toList big"
  apply(induction x big rule: push.induct)
  by(auto simp: put Common_Proof.push)

lemma invariant_push: "invariant big \<Longrightarrow> invariant (push x big)"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case by(auto simp: invariant_push)
next
  case (2 x current big auxB count)
  then show ?case by(auto split: current.splits)
qed

lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty big; invariant big;
  pop_invariant big;
  pop big = (x, big')
\<rbrakk> \<Longrightarrow> invariant big'"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: Common_Proof.invariant_pop split: prod.splits)
next
  case (2 current big auxB count)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply auto 
      (* TODO: *)
      apply (smt (verit, best) Cons_nth_drop_Suc Stack_Proof.pop Suc_diff_le diff_diff_cancel diff_is_0_eq drop_all_iff le_diff_conv le_eq_less_or_eq length_rev list.sel(3) nat_neq_iff ordered_cancel_comm_monoid_diff_class.diff_diff_right tl_append2)
      by linarith+
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma remainingSteps: "remainingSteps state > 0
   \<Longrightarrow> remainingSteps state = Suc (remainingSteps (tick state))"
proof(induction state rule: tick.induct)
  case (1 state)
  then show ?case
    by(auto simp: remainingSteps)
next
  case (2 current uu auxB)
  then show ?case 
    by(auto split: current.splits)
next
  case (3 current big auxB count)
  then show ?case
    apply(induction count)
     apply auto
     apply (metis Big.remainingSteps.simps(2) Current.toList.cases add_Suc)
    by (metis Big.remainingSteps.simps(2) Current.toList.cases add_Suc)
qed

lemma tickN: "invariant state
   \<Longrightarrow> \<exists>current idle. (tick^^ remainingSteps state) state = Common (Idle current idle)"
proof(induction "remainingSteps state" arbitrary: state)
  case 0
  then show ?case
    apply(induction state)
    apply(auto split: current.splits)
    using tickN by fastforce
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

  then have "\<exists>current idle. (tick^^ x) state' = Common (Idle current idle)"
    using Suc.hyps(1) \<open>invariant state'\<close> by blast

  then show ?case
    by (simp add: Suc.hyps(2) x)
qed


end
