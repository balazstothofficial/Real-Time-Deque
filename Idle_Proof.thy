theory Idle_Proof
  imports Idle Stack_Proof
begin

lemma push_list: "list (push x idle) = x # list idle"
  apply(induction idle arbitrary: x)
  by(auto simp: push_list)

lemma pop_list: "\<lbrakk>\<not> is_empty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> x # list idle' = list idle"
  apply(induction idle arbitrary: x)
  by(auto simp: pop_list first_pop first_list list_not_empty)

lemma pop_list_2: "\<lbrakk>0 < size idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> x # list idle' = list idle"
  apply(induction idle arbitrary: x)
  by(auto simp: first_pop size_not_empty)

lemma size_push: "size (push x idle) = Suc (size idle)"
  apply(induction idle arbitrary: x)
  by(auto simp: size_push)

lemma size_pop: "\<lbrakk>\<not>is_empty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> Suc (size idle')  = size idle"
  apply(induction idle arbitrary: x)
  by(auto simp: size_list_length pop_list_length)

lemma invar_push: "invar idle \<Longrightarrow> invar (push x idle)"
  apply(induction x idle rule: push.induct)
  by(auto simp: Stack_Proof.size_push)

lemma invar_pop: "\<lbrakk>\<not> is_empty idle; invar idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> invar idle'"
  apply(induction idle arbitrary: x rule: pop.induct)
  by(auto simp: Stack_Proof.size_pop)

lemma not_empty: "\<lbrakk>is_empty idle; 0 < size idle\<rbrakk> \<Longrightarrow> False" 
  apply(induction idle)
  by (simp add: size_not_empty) 

lemma size_empty: "is_empty idle \<longleftrightarrow> size idle = 0"
  apply(induction idle)
  by(auto simp: size_empty)

lemma size_not_empty: "\<not>is_empty idle \<longleftrightarrow> 0 < size idle"
  apply(induction idle)
  by(auto simp: size_not_empty)

end
