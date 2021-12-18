theory Transformation_Proof
  imports  Transformation States_Proof
begin

(* TODO: important! *)
lemma invariant_tick: "invariant transformation \<Longrightarrow> invariant (tick transformation)"
  apply(induction transformation rule: tick.induct)
   apply (auto simp: States_Proof.invariant_tick  split: prod.splits) 
  sorry

lemma tick_toList: "invariant transformation \<Longrightarrow> toListLeft (tick transformation) = toListLeft transformation"
 (* TODO: To be done with States equivalents *)
  sorry

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

end
