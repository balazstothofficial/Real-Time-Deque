theory Current_Proof
  imports Current Stack_Proof
begin

lemma put: "toList (put x current) = x # Current.toList current"
  apply(induction x current rule: put.induct)
  by auto

lemma get: "\<lbrakk>\<not> isEmpty current; get current = (x, current')\<rbrakk>
  \<Longrightarrow> x # Current.toList current' = Current.toList current"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: first_pop)

lemma bottom: "\<not> isEmpty current \<Longrightarrow> Current.toList (bottom current) = tl (Current.toList current)"
  apply(induction current rule: get.induct)
  by(auto simp: pop)

lemma invariant_put: "invariant current \<Longrightarrow> invariant (put x current)"
  apply(induction x current rule: put.induct)
  by auto

lemma invariant_get: "\<lbrakk>\<not> isEmpty current; invariant current; get current = (x, current')\<rbrakk>
   \<Longrightarrow> invariant current'"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: size_pop)

lemma invariant_bottom: "\<lbrakk>\<not> isEmpty current; invariant current\<rbrakk>
   \<Longrightarrow> invariant (bottom current)"
  apply(induction current rule: get.induct)
  by(auto simp: size_pop)

end