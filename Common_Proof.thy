theory Common_Proof
  imports Common
begin

lemma tick: "toList (tick common) = toList common"
  apply(induction common)
  by(auto split: current.splits)

end