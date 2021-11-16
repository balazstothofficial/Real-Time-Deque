theory Common_Proof
  imports Common Current_Proof
begin

lemma tick: "toList (tick common) = toList common"
  apply(induction common)
  by(auto split: current.splits)

lemma tick_2: "Common.tick common = common' \<Longrightarrow> Common.toList common = Common.toList common'"
  by(auto simp: tick)

lemma pop: "\<lbrakk>\<not> isEmpty common; pop common = (x, common')\<rbrakk> \<Longrightarrow> x # toList common' = toList common"
  apply(induction common arbitrary: x rule: pop.induct)
  by(auto simp: get  split: prod.splits)

lemma push: "toList (push x common) = x # toList common"
  apply(induction x common rule: push.induct)
  by(auto simp: put)
  
end