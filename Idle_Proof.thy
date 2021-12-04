theory Idle_Proof
  imports Idle Stack_Proof
begin

lemma push: "toList (push x idle) = x # toList idle"
  apply(induction idle arbitrary: x)
  by(auto simp: Stack_Proof.push)

lemma size_push: "size (push x idle) = Suc (size idle)"
  apply(induction idle arbitrary: x)
  by(auto simp: Stack_Proof.size_push)

lemma pop: "\<lbrakk>\<not> isEmpty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> x # toList idle' = toList idle"
  apply(induction idle arbitrary: x)
  by(auto simp: pop first_pop first not_empty_2)

lemma size_pop: "\<lbrakk>\<not> isEmpty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> Suc (size idle')  = size idle"
  apply(induction idle arbitrary: x)
  apply(auto simp: Stack_Proof.size_pop)
  by (simp add: not_empty_2 size_listLength)

lemma invariant_push: "invariant idle \<Longrightarrow> invariant (push x idle)"
  apply(induction x idle rule: push.induct)
  by(auto simp: Stack_Proof.size_push)

lemma invariant_pop: "\<lbrakk>\<not> isEmpty idle; invariant idle; pop idle = (x, idle')\<rbrakk>
   \<Longrightarrow> invariant idle'"
  apply(induction idle arbitrary: x rule: pop.induct)
  by(auto simp: Stack_Proof.size_pop)

end
