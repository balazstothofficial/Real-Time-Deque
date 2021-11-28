theory Idle_Proof
  imports Idle Stack_Proof
begin

lemma push: "toList (push x idle) = x # toList idle"
  apply(induction idle arbitrary: x)
  by(auto simp: Stack_Proof.push)

lemma size_push: "size (push x idle) = Suc (size idle)"
  apply(induction idle arbitrary: x)
  by(auto simp: Stack_Proof.size_push)



end
