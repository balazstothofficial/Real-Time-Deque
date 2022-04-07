theory Current_Proof
  imports Current Stack_Proof
begin

lemma put_list: "list (put x current) = x # Current.list current"
  by(induction x current rule: put.induct) auto

lemma get_list: "\<lbrakk>\<not> is_empty current; get current = (x, current')\<rbrakk>
  \<Longrightarrow> x # list current' = list current"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: first_pop)

lemma get_list_size: "\<lbrakk>invar current; 0 < size current; get current = (x, current')\<rbrakk>
  \<Longrightarrow> x # list current' = list current"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: first_pop size_not_empty)

lemma bottom_list: "\<not> is_empty current \<Longrightarrow> list (bottom current) = tl (list current)"
  apply(induction current rule: get.induct)
  by(auto simp: pop_list)

lemma bottom_list_size: "\<lbrakk>invar current; 0 < size current\<rbrakk>
  \<Longrightarrow> list (bottom current) = tl (list current)"
  apply(induction current rule: get.induct)
  by(auto simp: size_not_empty pop_list)

lemma invar_put: "invar current \<Longrightarrow> invar (put x current)"
  by(induction x current rule: put.induct) auto

lemma invar_get: "\<lbrakk>\<not> is_empty current; invar current; get current = (x, current')\<rbrakk>
   \<Longrightarrow> invar current'"
  apply(induction current arbitrary: x rule: get.induct)
  by(auto simp: size_pop)

lemma invar_size_get: "\<lbrakk>0 < size current; invar current; get current = (x, current')\<rbrakk>
   \<Longrightarrow> invar current'"
  by(induction current arbitrary: x rule: get.induct) auto

lemma invar_bottom: "\<lbrakk>\<not> is_empty current; invar current\<rbrakk> \<Longrightarrow> invar (bottom current)"
  by(induction current rule: get.induct) auto

lemma put_not_empty: "\<lbrakk>\<not> is_empty current; is_empty (put x current)\<rbrakk> \<Longrightarrow> False"
  by(induction x current rule: put.induct) auto

(* TODO: not optimal with only one direction (Is it really needed?) *)
lemma size_empty: "invar current \<Longrightarrow> size current = 0 \<Longrightarrow> is_empty current"
  apply(induction current)
  by(auto simp: size_empty)

lemma size_new_empty: "invar current \<Longrightarrow> size_new current = 0 \<Longrightarrow> is_empty current"
  apply(induction current)
  by(auto simp: size_empty)

lemma list_not_empty: "\<lbrakk>list current = []; \<not>is_empty current\<rbrakk> \<Longrightarrow> False"
  apply(induction current)
  by(auto simp: list_empty)   

lemma list_size: "\<lbrakk>invar current; list current = []; 0 < size current\<rbrakk> \<Longrightarrow> False"
  apply(induction current)
  by(auto simp: size_list_length)

lemma size_new_put: "invar current \<Longrightarrow> size_new (put x current) = Suc (size_new current)"
  by(induction x current rule: put.induct) auto

lemma size_put: "invariant current \<Longrightarrow> size (put x current) = Suc (size current)"
  by(induction x current rule: put.induct) auto

lemma size_new_get: "\<lbrakk>0 < size_new current; invar current \<rbrakk>
  \<Longrightarrow> size_new current = Suc (size_new (bottom current))"
  by(induction current rule: get.induct) auto

lemma size_get: "\<lbrakk>0 < size current; invar current \<rbrakk> \<Longrightarrow> size current = Suc (size (bottom current))"
  apply(induction current rule: get.induct) 
  by(auto simp: size_pop size_not_empty)

end