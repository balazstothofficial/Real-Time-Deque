theory Util 
  imports Main
begin

lemma take_last_length: "\<lbrakk>take (Suc 0) (rev xs) = [last xs]\<rbrakk> \<Longrightarrow> Suc 0 \<le> length xs"
  apply(induction xs)
  by auto

lemma take_last: "xs \<noteq> [] \<Longrightarrow> take 1 (rev xs) = [last xs]"
  apply(induction xs)
  by(auto simp: take_last_length)

lemma take_hd: "xs \<noteq> [] \<Longrightarrow> take (Suc 0) xs = [hd xs]"
  apply(induction xs)
  by auto

lemma cons_tl: "x # xs = ys \<Longrightarrow> xs = tl ys"
  by auto

end
