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

lemma pop: "\<not>isEmpty big \<Longrightarrow> invariant big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> x # toList big' = toList big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case
    by(auto simp: list_pop split: prod.splits)
next
  case (2 x current big aux count)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)

    then have "first old # rev (take (remained - Suc (length (Stack.toList big))) aux) = rev (take (remained - length (Stack.toList big)) aux)"
      apply(auto simp: min_def split: if_splits)
      sorry

    with 1 have t: " first old #
         rev (take (remained - Suc (min (length (Stack.toList big)) count)) aux) = rev (take (remained - min (length (Stack.toList big)) count) aux)"
      apply(auto simp: min_def split: if_splits)
      sorry

    from 1 show ?case
      apply(auto simp: t revN_take)
      by (smt (z3) Suc_pred append_Cons diff_is_0_eq le_Suc_eq length_rev length_take not_Cons_self2 not_less_eq_eq rev_rev_ident t take_all_iff)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed 

lemma invariant_tick: "invariant big \<Longrightarrow> invariant (tick big)" 
proof(induction big rule: tick.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invariant_tick)
next
  case (2 current uu aux)
  then show ?case
    apply(auto simp: revN_take split: current.splits)
    by (metis length_rev length_take min.absorb2 size_listLength take_append take_take)
next
  case (3 current big aux v)
  then show ?case
    apply (auto simp: revN_take Stack_Proof.size_pop not_empty split: current.splits)
    subgoal 
     
      sorry
    sorry
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
     apply auto
       apply linarith+
    sorry
qed

lemma currentList_push: "toCurrentList (push x big) = x # toCurrentList big"
  apply(induction x big rule: push.induct)
  by(auto simp: currentList_push put)

lemma currentList_pop: "\<not>isEmpty big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> toCurrentList big' = tl (toCurrentList big)"
  apply(induction big arbitrary: x rule: pop.induct)
   apply(auto split: prod.splits)
   apply (meson currentList_pop)
  by (metis get list.sel(3))

lemma some_empty: "\<lbrakk>isEmpty (tick big); \<not> isEmpty big; invariant big\<rbrakk> \<Longrightarrow> False"
  apply(induction big rule: tick.induct)
    apply(auto split: current.splits if_splits)
  using some_empty by blast

lemma currentList_empty: "\<lbrakk>\<not> isEmpty big; toCurrentList big = []; invariant big\<rbrakk> \<Longrightarrow> False"
  apply(induction big)
  using currentList_empty by(auto simp: not_empty_2 split: current.splits)

lemma tick_size: "invariant big \<Longrightarrow> size big = size (tick big)"
  apply(induction big rule: tick.induct)
  by(auto simp: tick_size split: current.splits)

lemma tick_not_empty: "invariant big \<Longrightarrow> \<not>isEmpty big \<Longrightarrow> \<not>isEmpty (tick big)"
  apply(induction big rule: tick.induct)
  by(auto simp: tick_not_empty split: current.splits)

end
