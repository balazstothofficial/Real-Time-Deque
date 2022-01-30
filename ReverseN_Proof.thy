theory ReverseN_Proof
  imports ReverseN
begin

lemma reverseN_take: "reverseN n xs acc = rev (take n xs) @ acc"
  apply(induction n xs acc rule: reverseN.induct)
  by auto

lemma reverseN_drop: "reverseN n xs acc = drop (length xs - n) (rev xs) @ acc"
  apply(induction n xs acc rule: reverseN.induct)
  by auto

lemma reverseN_reverseN: "reverseN n (reverseN n xs []) [] = take n xs"
  by(auto simp: reverseN_take)

end
