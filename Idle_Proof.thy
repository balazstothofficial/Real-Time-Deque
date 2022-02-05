theory Idle_Proof
  imports Idle Stack_Proof
begin

lemma push_toList: "toList (push x idle) = x # toList idle"
  apply(induction idle arbitrary: x)
  by(auto simp: push_toList)

lemma pop_toList: "\<lbrakk>\<not> isEmpty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> x # toList idle' = toList idle"
  apply(induction idle arbitrary: x)
  by(auto simp: pop_toList first_pop first_toList toList_isNotEmpty)

lemma pop_toList_2: "\<lbrakk>0 < size idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> x # toList idle' = toList idle"
  apply(induction idle arbitrary: x)
  by(auto simp: first_pop size_isNotEmpty)

lemma size_push: "size (push x idle) = Suc (size idle)"
  apply(induction idle arbitrary: x)
  by(auto simp: size_push)

lemma size_pop: "\<lbrakk>\<not> isEmpty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> Suc (size idle')  = size idle"
  apply(induction idle arbitrary: x)
  by(auto simp: Stack_Proof.size_listLength pop_listLength)

lemma invariant_push: "invariant idle \<Longrightarrow> invariant (push x idle)"
  apply(induction x idle rule: push.induct)
  by(auto simp: Stack_Proof.size_push)

lemma invariant_pop: "\<lbrakk>\<not> isEmpty idle; invariant idle; pop idle = (x, idle')\<rbrakk>
   \<Longrightarrow> invariant idle'"
  apply(induction idle arbitrary: x rule: pop.induct)
  by(auto simp: Stack_Proof.size_pop)

lemma isNotEmpty: "\<lbrakk>isEmpty idle; 0 < size idle\<rbrakk> \<Longrightarrow> False" 
  apply(induction idle)
  by (simp add: size_isNotEmpty) 

lemma size_isEmpty: "isEmpty idle \<longleftrightarrow> size idle = 0"
  apply(induction idle)
  by(auto simp: size_isEmpty)

lemma size_isNotEmpty: "\<not>isEmpty idle \<longleftrightarrow> 0 < size idle"
  apply(induction idle)
  by(auto simp: size_isNotEmpty)

end
