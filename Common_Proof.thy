theory Common_Proof
  imports Common Current_Proof
begin

lemma tick: "toList (tick common) = toList common"
  apply(induction common)
  by(auto split: current.splits)

lemma push:  "toList (push x common) = x # toList common"
  apply(induction common arbitrary: x)
  apply(auto simp: put)
  (* TODO: *)
  by (metis Common.push.simps(1) Common.toList.simps(1) idle.exhaust put)
  
end