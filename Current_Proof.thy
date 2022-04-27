theory Current_Proof
  imports Current Stack_Proof
begin

lemma push_list: "list (push x current) = x # Current.list current"
  by(induction x current rule: push.induct) auto

lemma pop_list: "\<lbrakk>\<not> is_empty current; pop current = (x, current')\<rbrakk>
  \<Longrightarrow> x # list current' = list current"
  apply(induction current arbitrary: x rule: pop.induct)
  by(auto simp: first_pop)

lemma pop_list_size: "\<lbrakk>invar current; 0 < size current; pop current = (x, current')\<rbrakk>
  \<Longrightarrow> x # list current' = list current"
  apply(induction current arbitrary: x rule: pop.induct)
  by(auto simp: first_pop size_not_empty)

lemma drop_first_list: "\<not> is_empty current \<Longrightarrow> list (drop_first current) = tl (list current)"
  apply(induction current rule: pop.induct)
  by(auto simp: Stack_Proof.pop_list)

lemma drop_first_list_size: "\<lbrakk>invar current; 0 < size current\<rbrakk>
  \<Longrightarrow> list (drop_first current) = tl (list current)"
  apply(induction current rule: pop.induct)
  by(auto simp: size_not_empty Stack_Proof.pop_list)

lemma invar_push: "invar current \<Longrightarrow> invar (push x current)"
  by(induction x current rule: push.induct) auto

lemma invar_pop: "\<lbrakk>\<not> is_empty current; invar current; pop current = (x, current')\<rbrakk>
   \<Longrightarrow> invar current'"
  apply(induction current arbitrary: x rule: pop.induct)
  by(auto simp: size_pop)

lemma invar_size_pop: "\<lbrakk>0 < size current; invar current; pop current = (x, current')\<rbrakk>
   \<Longrightarrow> invar current'"
  by(induction current arbitrary: x rule: pop.induct) auto

lemma invar_drop_first: "\<lbrakk>\<not> is_empty current; invar current\<rbrakk> \<Longrightarrow> invar (drop_first current)"
  by(induction current rule: pop.induct) auto

lemma push_not_empty: "\<lbrakk>\<not> is_empty current; is_empty (push x current)\<rbrakk> \<Longrightarrow> False"
  by(induction x current rule: push.induct) auto

(* TODO: not optimal with only one direction (Is it really needed?) *)
lemma size_empty: "invar (current :: 'a current) \<Longrightarrow> size current = 0 \<Longrightarrow> is_empty current"
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

lemma size_new_push: "invar current \<Longrightarrow> size_new (push x current) = Suc (size_new current)"
  by(induction x current rule: push.induct) auto

lemma size_push: "invariant current \<Longrightarrow> size (push x current) = Suc (size current)"
  by(induction x current rule: push.induct) auto

lemma size_new_pop: "\<lbrakk>0 < size_new current; invar current \<rbrakk>
  \<Longrightarrow> size_new current = Suc (size_new (drop_first current))"
  by(induction current rule: pop.induct) auto

lemma size_pop: "\<lbrakk>0 < size current; invar current \<rbrakk> \<Longrightarrow> size current = Suc (size (drop_first current))"
  apply(induction current rule: pop.induct) 
  by(auto simp: size_pop size_not_empty)

end