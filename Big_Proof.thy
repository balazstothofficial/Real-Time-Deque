theory Big_Proof
  imports Big Common_Proof
begin

lemma tick: "toList (tick state) = toList state"
  apply(induction state)
  by(auto simp: tick)

end
