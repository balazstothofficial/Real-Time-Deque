theory Small_Proof 
  imports Common_Proof Small
begin

lemma tick: "toList (tick state) = toList state"
  apply(induction state)
  by(auto simp: tick split: current.splits)

end