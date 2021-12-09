theory Transformation_Proof
  imports  Transformation States_Proof
begin

lemma tick: "toListLeft (tick transformation) = toListLeft transformation"
  apply(induction transformation rule: toListLeft.induct)
  by(auto simp: tick_toListBig tick_toListSmall split: prod.splits)

lemma fourTicks: "toListLeft (fourTicks transformation) = toListLeft transformation"
  by(auto simp: fourTicks_def tick)

lemma sixTicks: "toListLeft (sixTicks transformation) = toListLeft transformation"
  by(auto simp: sixTicks_def tick)

lemmas ticks = Small_Proof.tick Big_Proof.tick Common_Proof.tick tick sixTicks fourTicks

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits

lemma invariant_tick: "invariant transformation \<Longrightarrow> invariant (tick transformation)"
  apply(induction transformation rule: tick.induct)
  by (simp add: States_Proof.invariant_tick case_prod_unfold)+

lemma invariant_fourTicks: "invariant transformation \<Longrightarrow> invariant (fourTicks transformation)"
  apply(induction transformation rule: tick.induct)
  by (auto simp: fourTicks_def invariant_tick case_prod_unfold States_Proof.invariant_tick)

lemma invariant_sixTicks: "invariant transformation \<Longrightarrow> invariant (sixTicks transformation)"
  apply(induction transformation rule: tick.induct)
  by (auto simp: sixTicks_def invariant_tick case_prod_unfold States_Proof.invariant_tick)

end
