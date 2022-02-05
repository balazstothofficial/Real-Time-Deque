theory Stack_Proof
  imports Stack Util
begin

lemma push_toList: "toList (push x stack) = x # toList stack"
  by(induction stack) auto

lemma pop_toList: "\<not> isEmpty stack \<Longrightarrow> toList (pop stack) = tl (toList stack)"
  by(induction stack rule: pop.induct) auto

lemma first_toList: "\<not> isEmpty stack \<Longrightarrow> first stack = hd (toList stack)"
  by(induction stack rule: first.induct) auto

lemma toList_isEmpty: "toList stack = [] \<longleftrightarrow> isEmpty stack"
  by(induction stack rule: isEmpty.induct) auto

lemma toList_isNotEmpty: "toList stack  \<noteq> [] \<longleftrightarrow> \<not> isEmpty stack"
  by(induction stack rule: isEmpty.induct) auto

lemma size_push: "size (push x stack) = Suc (size stack)"
  by(induction stack arbitrary: x) auto

lemma size_pop: "\<not> isEmpty stack \<Longrightarrow> size (pop stack) = size stack - Suc 0"
  by(induction stack rule: pop.induct) auto

lemma size_isEmpty: "size stack = 0 \<longleftrightarrow> isEmpty stack"
  by(induction stack rule: isEmpty.induct) auto

lemma size_isNotEmpty: "size stack > 0 \<longleftrightarrow> \<not> isEmpty stack"
  by(induction stack rule: isEmpty.induct) auto

lemma size_listLength: "Stack.size stack = List.length (Stack.toList stack)"
  by(induction stack) auto

lemma first_pop: "\<not> isEmpty stack \<Longrightarrow> first stack # Stack.toList (pop stack) = Stack.toList stack"
  by(induction stack rule: pop.induct) auto

lemma push_isNotEmpty: "\<lbrakk>\<not> isEmpty stack; isEmpty (push x stack)\<rbrakk> \<Longrightarrow> False"
  by(induction x stack rule: push.induct) auto

lemma pop_listLength: "\<not> Stack.isEmpty stack
   \<Longrightarrow> Suc (length (toList (pop stack))) = length (toList stack)"
  by(induction stack rule: pop.induct) auto

lemma first_take: "\<not>Stack.isEmpty stack \<Longrightarrow> [first stack] = take 1 (Stack.toList stack)"
  by (simp add: first_toList take_hd toList_isEmpty)

lemma first_take_pop: "\<lbrakk>\<not>Stack.isEmpty stack; 0 < x\<rbrakk>
   \<Longrightarrow> first stack # take (x - Suc 0) (toList (pop stack)) = take x (toList stack)"
  apply(induction stack rule: pop.induct)
  by(auto simp: take_Cons')

lemma popN_drop: "Stack.toList ((Stack.pop ^^ n) stack) = drop n (Stack.toList stack)" 
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto)
    by (metis drop_Suc isEmpty.elims(2) list.sel(2) pop.simps(1) pop_toList tl_drop toList_isEmpty)
qed

lemma popN_size: "Stack.size ((Stack.pop ^^ n) stack) = (Stack.size stack) - n"
  apply(induction n)
   apply auto
  by (metis (no_types, hide_lams) One_nat_def Stack.isEmpty.elims(2) Stack.pop.simps(1) Stack.toList.simps Stack_Proof.size_pop append_Nil diff_Suc_eq_diff_pred diff_commute diff_is_0_eq le_Suc_eq list.size(3) Stack_Proof.size_listLength)


end