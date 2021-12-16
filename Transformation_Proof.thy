theory Transformation_Proof
  imports  Transformation States_Proof
begin

lemma tick: "toListLeft (tick transformation) = toListLeft transformation"
  apply(induction transformation rule: toListLeft.induct)
  by(auto simp: tick_toListBig tick_toListSmall split: prod.splits)

lemma nTicks: "toListLeft ((tick^^n) transformation) = toListLeft transformation"
  apply(induction n arbitrary: transformation)
  by(auto simp: tick)

lemma fourTicks: "toListLeft (fourTicks transformation) = toListLeft transformation"
  by(auto simp: fourTicks_def nTicks)

lemma sixTicks: "toListLeft (sixTicks transformation) = toListLeft transformation"
  by(auto simp: sixTicks_def nTicks)

lemmas ticks = Small_Proof.tick Big_Proof.tick Common_Proof.tick tick nTicks sixTicks fourTicks

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits

lemma invariant_tick: "invariant transformation \<Longrightarrow> invariant (tick transformation)"
  apply(induction transformation rule: tick.induct)
  by (simp add: States_Proof.invariant_tick case_prod_unfold)+

lemma invariant_nTicks: "invariant transformation \<Longrightarrow> invariant ((tick^^n) transformation)"
  apply(induction n arbitrary: transformation)
  by(auto simp: invariant_tick)

lemma invariant_fourTicks: "invariant transformation \<Longrightarrow> invariant (fourTicks transformation)"
  by(auto simp: invariant_nTicks fourTicks_def)

lemma invariant_sixTicks: "invariant transformation \<Longrightarrow> invariant (sixTicks transformation)"
  by(auto simp: invariant_nTicks sixTicks_def)

end
