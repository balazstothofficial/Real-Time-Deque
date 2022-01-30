theory Current_Proof
  imports Current Stack_Proof
begin

lemma put_toList: "toList (put x current) = x # Current.toList current"
  apply(induction x current rule: put.induct)
  by auto

lemma get_toList: "\<lbrakk>\<not> isEmpty current; get current = (x, current')\<rbrakk>
  \<Longrightarrow> x # Current.toList current' = Current.toList current"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: first_pop)

lemma get_toList_size: "\<lbrakk>invariant current; 0 < size current; get current = (x, current')\<rbrakk>
  \<Longrightarrow> x # Current.toList current' = Current.toList current"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: first_pop size_isNotEmpty)

lemma bottom_toList: "\<not> isEmpty current \<Longrightarrow> toList (bottom current) = tl (toList current)"
  apply(induction current rule: get.induct)
  by(auto simp: pop_toList)

lemma invariant_put: "invariant current \<Longrightarrow> invariant (put x current)"
  apply(induction x current rule: put.induct)
  by auto

lemma invariant_get: "\<lbrakk>\<not> isEmpty current; invariant current; get current = (x, current')\<rbrakk>
   \<Longrightarrow> invariant current'"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: size_pop)

lemma invariant_get_size: "\<lbrakk>0 < size current; invariant current; get current = (x, current')\<rbrakk>
   \<Longrightarrow> invariant current'"
  apply(induction current arbitrary: x rule: get.induct)
  by auto

lemma invariant_bottom: "\<lbrakk>\<not> isEmpty current; invariant current\<rbrakk>
   \<Longrightarrow> invariant (bottom current)"
  apply(induction current rule: get.induct)
  by(auto simp: size_pop)

lemma put_isNotEmpty: "\<lbrakk>\<not> isEmpty current; isEmpty (put x current)\<rbrakk> \<Longrightarrow> False"
  apply(induction x current rule: put.induct)
  by auto

(* TODO: not optimal with only one direction (Is it really needed?) *)
lemma size_isEmpty: "invariant current \<Longrightarrow> size current = 0 \<Longrightarrow> isEmpty current"
  apply(induction current)
  by(auto simp: size_isEmpty)

lemma put_size: "Current.invariant current 
  \<Longrightarrow> Current.newSize (put x current) = Suc (Current.newSize current)"
  apply(induction x current rule: put.induct)
  by auto

end