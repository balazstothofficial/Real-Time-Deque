theory Current_Proof
  imports Current Stack_Proof
begin

lemma put_toList: "toList (put x current) = x # Current.toList current"
  by(induction x current rule: put.induct) auto

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

lemma bottom_toList_size: "\<lbrakk>invariant current; 0 < size current\<rbrakk>
   \<Longrightarrow> toList (bottom current) = tl (toList current)"
  apply(induction current rule: get.induct)
  by(auto simp: size_isNotEmpty pop_toList)

lemma invariant_put: "invariant current \<Longrightarrow> invariant (put x current)"
  by(induction x current rule: put.induct) auto

lemma invariant_get: "\<lbrakk>\<not> isEmpty current; invariant current; get current = (x, current')\<rbrakk>
   \<Longrightarrow> invariant current'"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: size_pop)

lemma invariant_size_get: "\<lbrakk>0 < size current; invariant current; get current = (x, current')\<rbrakk>
   \<Longrightarrow> invariant current'"
  by(induction current arbitrary: x rule: get.induct) auto

lemma invariant_bottom: "\<lbrakk>\<not> isEmpty current; invariant current\<rbrakk>
   \<Longrightarrow> invariant (bottom current)"
  by(induction current rule: get.induct) auto

lemma put_isNotEmpty: "\<lbrakk>\<not> isEmpty current; isEmpty (put x current)\<rbrakk> \<Longrightarrow> False"
  by(induction x current rule: put.induct) auto

(* TODO: not optimal with only one direction (Is it really needed?) *)
lemma size_isEmpty: "invariant current \<Longrightarrow> size current = 0 \<Longrightarrow> isEmpty current"
  apply(induction current)
  by(auto simp: size_isEmpty)

lemma newSize_isEmpty: "invariant current \<Longrightarrow> newSize current = 0 \<Longrightarrow> isEmpty current"
  apply(induction current)
  by(auto simp: size_isEmpty)

lemma toList_isNotEmpty: "\<lbrakk>toList current = []; \<not>isEmpty current\<rbrakk> \<Longrightarrow> False"
  apply(induction current)
  by(auto simp: toList_isEmpty)   

lemma toList_size: "\<lbrakk>invariant current; toList current = []; 0 < size current\<rbrakk> \<Longrightarrow> False"
  apply(induction current)
  by(auto simp: Stack_Proof.size_listLength)

lemma newSize_put: "invariant current \<Longrightarrow> newSize (put x current) = Suc (newSize current)"
  by(induction x current rule: put.induct) auto

lemma size_put: "invariant current \<Longrightarrow> size (put x current) = Suc (size current)"
  by(induction x current rule: put.induct) auto

lemma newSize_get: "\<lbrakk>0 < newSize current; invariant current \<rbrakk>
  \<Longrightarrow> newSize current = Suc (newSize (bottom current))"
  by(induction current rule: get.induct) auto

lemma size_get: "\<lbrakk>0 < size current; invariant current \<rbrakk>
  \<Longrightarrow> size current = Suc (size (bottom current))"
  apply(induction current rule: get.induct) 
  by(auto simp: size_pop size_isNotEmpty)

end