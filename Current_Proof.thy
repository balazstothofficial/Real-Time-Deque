theory Current_Proof
  imports Current Stack_Proof
begin

lemma put: "toList (put x current) = x # Current.toList current"
  apply(induction x current rule: put.induct)
  by auto

lemma get: "\<lbrakk>\<not> isEmpty current; get current = (x, current')\<rbrakk>
  \<Longrightarrow> x # Current.toList current' = Current.toList current"
  apply(induction current arbitrary: x rule: get.induct)
   apply auto
  by(auto simp: first_pop)

lemma get_2: "\<lbrakk>invariant current; 0 < size current; get current = (x, current')\<rbrakk>
  \<Longrightarrow> x # Current.toList current' = Current.toList current"
  apply(induction current arbitrary: x rule: get.induct)
   apply auto
  using first_pop not_empty by blast

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

lemma invariant_get_2: "\<lbrakk>0 < size current; invariant current; get current = (x, current')\<rbrakk>
   \<Longrightarrow> invariant current'"
  apply(induction current arbitrary: x rule: get.induct)
  by auto

lemma invariant_bottom: "\<lbrakk>\<not> isEmpty current; invariant current\<rbrakk>
   \<Longrightarrow> invariant (bottom current)"
  apply(induction current rule: get.induct)
  by(auto simp: size_pop)

lemma put_not_empty: "\<lbrakk>\<not> isEmpty current; isEmpty (put x current)\<rbrakk> \<Longrightarrow> False"
  apply(induction x current rule: put.induct)
  by auto

(* not optimal with only one direction *)
lemma size_empty: "invariant current \<Longrightarrow> size current = 0 \<Longrightarrow> isEmpty current"
  apply(induction current)
  by(auto simp: empty_size)

end