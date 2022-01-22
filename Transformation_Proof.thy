theory Transformation_Proof
  imports  Transformation States_Proof
begin

lemma invariant_tick: "invariant transformation \<Longrightarrow> invariant (tick transformation)"
proof(induction transformation rule: tick.induct)
  case (1 small big)

  then have "States.invariant (big, small)"
    by auto
  
  then have "States.invariant (States.tick (big, small))"
    using States_Proof.invariant_tick by blast

  then have "Transformation.invariant (case States.tick (big, small) of (big, small) \<Rightarrow> Left small big)"
    by(auto split: prod.split)

  then show ?case by auto
next
  case (2 big small)

  then have "States.invariant (big, small)"
    by auto
  
  then have "States.invariant (States.tick (big, small))"
    using States_Proof.invariant_tick by blast

  then have "Transformation.invariant (case States.tick (big, small) of (big, small) \<Rightarrow> Right big small)"
    by(auto split: prod.split)

  then show ?case by auto
qed

lemma tick_toList: "invariant transformation \<Longrightarrow> toListLeft (tick transformation) = toListLeft transformation"
proof(induction transformation rule: tick.induct)
  case (1 small big)

  then have "States.toListSmallFirst (big, small) = Small.toCurrentList small @ rev (Big.toCurrentList big)"
    by auto

  then have "States.toListSmallFirst (States.tick (big, small)) = Small.toCurrentList small @ rev (Big.toCurrentList big)"
    using "1.prems" States_Proof.tick_toList by force

  then have "toListLeft (case States.tick (big, small) of (big, small) \<Rightarrow> transformation.Left small big) =
         Small.toCurrentList small @ rev (Big.toCurrentList big)"
    by(auto split: prod.splits)

  with 1 show ?case 
    by auto
next
  case (2 big small)
  
  then have statesToList: "States.toListBigFirst (big, small) = Big.toCurrentList big @ rev (Small.toCurrentList small)"
    using invariant_listBigFirst by fastforce

  then have "States.toListBigFirst (States.tick (big, small)) = Big.toCurrentList big @ rev (Small.toCurrentList small)"
    using "2.prems" States_Proof.tick_toList by force

  then have "toListLeft (case States.tick (big, small) of (big, small) \<Rightarrow> Right big small) =
         Big.toCurrentList big @ rev (Small.toCurrentList small)"
   by(auto split: prod.splits)

  with 2 show ?case 
    using statesToList by fastforce
qed

lemma invariant_pop_small: "invariant (Left small big) \<Longrightarrow> \<not>Small.isEmpty small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invariant (Left small' big)"
  by (meson Transformation.invariant.simps(1) invariant_pop_small)

lemma nTicks: "invariant transformation \<Longrightarrow> toListLeft ((tick^^n) transformation) = toListLeft transformation"
  apply(induction n arbitrary: transformation)
  by(auto simp: funpow_swap1 tick_toList invariant_tick)

lemma fourTicks: "invariant transformation \<Longrightarrow> toListLeft (fourTicks transformation) = toListLeft transformation"
  by(auto simp: fourTicks_def nTicks)

lemma sixTicks: "invariant transformation \<Longrightarrow> toListLeft (sixTicks transformation) = toListLeft transformation"
  by(auto simp: sixTicks_def nTicks)

lemmas ticks = States_Proof.tick_toList Big_Proof.tick_toList Common_Proof.tick_toList tick_toList nTicks sixTicks fourTicks

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits

lemma invariant_nTicks: "invariant transformation \<Longrightarrow> invariant ((tick^^n) transformation)"
  apply(induction n arbitrary: transformation)
  by(auto simp: invariant_tick)

lemma invariant_fourTicks: "invariant transformation \<Longrightarrow> invariant (fourTicks transformation)"
  by(auto simp: invariant_nTicks fourTicks_def)

lemma invariant_sixTicks: "invariant transformation \<Longrightarrow> invariant (sixTicks transformation)"
  by(auto simp: invariant_nTicks sixTicks_def)

(*lemma tick_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (tick transformation)"
  apply(induction transformation)
  apply (metis Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) prod.case_eq_if prod.exhaust_sel tick_inSizeWindow)
  by (metis Transformation.inSizeWindow.simps(2) Transformation.invariant.simps(2) Transformation.tick.simps(2) prod.case_eq_if prod.exhaust_sel tick_inSizeWindow)

lemma nTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow ((tick ^^ n) transformation)"
  apply(induction n)
   apply(auto simp: funpow_swap1 invariant_nTicks tick_inSizeWindow)
  by (metis Transformation_Proof.tick_inSizeWindow funpow_swap1 invariant_nTicks)

lemma fourTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (fourTicks transformation)"
  by(auto simp: nTicks_inSizeWindow fourTicks_def)

lemma sixTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (sixTicks transformation)"
  by(auto simp: nTicks_inSizeWindow sixTicks_def)*)
end
