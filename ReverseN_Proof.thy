theory ReverseN_Proof
  imports ReverseN
begin

lemma reverseN_take: "reverseN n xs acc = rev (take n xs) @ acc"
  by(induction n xs acc rule: reverseN.induct) auto

lemma reverseN_drop: "reverseN n xs acc = drop (length xs - n) (rev xs) @ acc"
  by(induction n xs acc rule: reverseN.induct) auto

lemma reverseN_reverseN: "reverseN n (reverseN n xs []) [] = take n xs"
  by(auto simp: reverseN_take)

lemma reverseN_step: "xs \<noteq> [] \<Longrightarrow> reverseN n (tl xs) (hd xs # acc) = reverseN (Suc n) xs acc"
  by(induction "Suc n" xs acc rule: reverseN.induct) auto

lemma reverseN_finish: "reverseN n [] acc = acc"
  by (simp add: reverseN_take)

lemma reverse1_tl: "xs \<noteq> [] \<Longrightarrow> acc = tl (reverseN (Suc 0) xs acc)"
  by(induction "Suc 0" xs acc rule: reverseN.induct) auto

lemma reverseN_tl: "n < length xs \<Longrightarrow> reverseN n xs acc = tl (reverseN (Suc n) xs acc)"
  by(induction n xs acc rule: reverseN.induct)(auto simp: reverse1_tl)

lemma reverseN_tl_hd: "0 < n \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> reverseN n xs ys = reverseN (n - (Suc 0)) (tl xs) (hd xs #ys)"
  by (simp add: reverseN_step)

lemma reverseN_nth: "n < length xs \<Longrightarrow> x = xs ! n \<Longrightarrow> x # reverseN n xs ys = reverseN (Suc n) xs ys"
  by(induction n xs ys rule: reverseN.induct) (auto simp: reverseN_tl_hd hd_conv_nth)

end
