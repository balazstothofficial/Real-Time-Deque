theory Stack_Proof
  imports Stack Util
begin

lemma push_toList: "toList (push x stack) = x # toList stack"
  apply(induction stack arbitrary: x)
  by auto

lemma pop_toList: "\<not> isEmpty stack \<Longrightarrow> toList (pop stack) = tl (toList stack)"
proof(induction stack)
  case (Stack left right)
  then show ?case 
    apply(induction left; induction right)
    by auto
qed

lemma first_toList: "\<not> isEmpty stack \<Longrightarrow> first stack = hd (toList stack)"
proof(induction stack)
  case (Stack left right)
  then show ?case
    apply(induction left; induction right)
    by auto
qed

lemma toList_isEmpty: "toList stack = [] \<longleftrightarrow> isEmpty stack"
proof(induction stack rule: toList.induct)
  case (1 left right)
  then show ?case
    apply(induction left; induction right)
    by auto
qed

lemma toList_isNotEmpty: "toList stack  \<noteq> [] \<longleftrightarrow> \<not> isEmpty stack"
proof(induction stack rule: toList.induct)
  case (1 left right)
  then show ?case
    apply(induction left; induction right)
    by auto
qed

lemma size_push: "size (push x stack) = Suc (size stack)"
  apply(induction stack arbitrary: x)
  by auto

lemma size_pop: "\<not> isEmpty stack \<Longrightarrow> size (pop stack) = size stack - Suc 0"
proof(induction stack)
  case (Stack left right)
  then show ?case 
    apply(induction left; induction right)
    by auto
qed

lemma size_isEmpty: "size stack = 0 \<longleftrightarrow> isEmpty stack"
  apply(induction stack rule: isEmpty.induct)
  by auto

lemma size_isNotEmpty: "size stack > 0 \<longleftrightarrow> \<not> isEmpty stack"
proof(induction stack)
  case (Stack left right)
  then show ?case
    apply(induction left; induction right)
    by auto
qed

lemma size_listLength: "Stack.size stack = List.length (Stack.toList stack)"
  apply(induction stack)
  by auto

lemma first_pop: "\<not> isEmpty stack \<Longrightarrow> first stack # Stack.toList (pop stack) = Stack.toList stack"
  apply(induction stack rule: pop.induct)
  by auto

lemma push_isNotEmpty: "\<lbrakk>\<not> isEmpty stack; isEmpty (push x stack)\<rbrakk> \<Longrightarrow> False"
  apply(induction x stack rule: push.induct)
  by auto

lemma pop_listLength: "\<not> Stack.isEmpty stack
   \<Longrightarrow> Suc (length (toList (pop stack))) = length (toList stack)"
  apply(induction stack rule: pop.induct)
  by auto

lemma first_take: "\<not>Stack.isEmpty stack \<Longrightarrow> [first stack] = take 1 (Stack.toList stack)"
  by (simp add: first_toList take_hd toList_isEmpty)

lemma first_take_pop: "\<lbrakk>\<not>Stack.isEmpty stack; 0 < x\<rbrakk>
   \<Longrightarrow> first stack # take (x - Suc 0) (toList (pop stack)) = take x (toList stack)"
  apply(induction stack rule: pop.induct)
  by(auto simp: take_Cons')

end