theory Small_Proof 
  imports Common_Proof Small
begin

lemma tick: "toList (tick state) = toList state"
  apply(induction state)
  by(auto simp: tick split: current.splits)

lemma push: "x # toList small = toList (push x small)"
  apply(induction x small rule: push.induct)
  by(auto simp: push put)

lemma pop: "\<lbrakk>\<not> isEmpty small; pop small = (x, small')\<rbrakk> \<Longrightarrow> x # toList small' = toList small"
  apply(induction small arbitrary: x rule: pop.induct)
  by(auto simp: get Common_Proof.pop split: prod.splits current.splits if_splits)

lemma invariant_tick: "invariant state \<Longrightarrow> invariant (tick state)"
  quickcheck
  sorry



value "tick ( Reverse2 (Current [] 0 (Stack [] [a\<^sub>1]) 2) [a\<^sub>1] (Stack [] []) [a\<^sub>1, a\<^sub>2] 2)"

lemma invariant_push: "invariant small \<Longrightarrow> invariant (push x small)"
  sorry

lemma invariant_pop: "\<lbrakk>\<not> isEmpty small; invariant small; pop_invariant small; pop small = (x, small')\<rbrakk>
   \<Longrightarrow> invariant small'"
  sorry

end