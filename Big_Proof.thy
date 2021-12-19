theory Big_Proof
  imports Big Common_Proof
begin

lemma tick_toList: "invariant big \<Longrightarrow> toList (tick big) = toList big"
  apply(induction big rule: tick.induct)
    apply(auto simp: tick_toList split: current.splits)
  by (metis Suc_neq_Zero bot_nat_0.extremum_uniqueI empty first_pop list.size(3) revN.simps(3) size_listLength)

lemma tick_toCurrentList: "invariant big \<Longrightarrow> toCurrentList (tick big) = toCurrentList big"
  apply(induction big rule: tick.induct)
  by(auto simp: tick_toCurrentList split: current.splits)

lemma push: "toList (push x big) = x # toList big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: push)
next
  case (2 x current big aux count)
  then show ?case
    apply(induction x current rule: put.induct)
    by auto
qed

(* TODO: lemma pop: "pop big = (x, big') \<Longrightarrow> x # toList big' = toList big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case apply(auto split: prod.splits)
    sorry
next
  case (2 x current big aux count)
  then show ?case sorry
qed *)

lemma invariant_tick: "invariant big \<Longrightarrow> invariant (tick big)" 
proof(induction big rule: tick.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invariant_tick)
next
  case (2 current uu aux)
  then show ?case
    by(auto split: current.splits)
next
  case (3 current big aux v)
  then show ?case
    by (auto simp: Stack_Proof.size_pop not_empty split: current.splits)
qed

lemma invariant_push: "invariant big \<Longrightarrow> invariant (push x big)"
  apply(induction x big rule: push.induct)
  by(auto simp: invariant_push split: current.splits)

lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty big; 
  invariant big;
  pop_invariant big;
  pop big = (x, big')
\<rbrakk> \<Longrightarrow> invariant big'"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: invariant_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
    apply(induction current rule: get.induct)
    by auto
qed

lemma currentList_push: "toCurrentList (push x big) = x # toCurrentList big"
  apply(induction x big rule: push.induct)
  by(auto simp: currentList_push put)

lemma some_empty: "\<lbrakk>isEmpty (tick big); \<not> isEmpty big; invariant big\<rbrakk> \<Longrightarrow> False"
  apply(induction big rule: tick.induct)
    apply(auto split: current.splits if_splits)
  using some_empty apply blast
  using Current.isEmpty.simps(1) Stack.isEmpty.elims(2) by blast

end
