theory Stack_Proof
  imports Stack
begin

lemma push: "toList (push x stack) = x # toList stack"
  apply(induction stack arbitrary: x)
  by auto

lemma pop: "\<not> isEmpty stack \<Longrightarrow> toList (pop stack) = tl (toList stack)"
proof(induction stack)
  case (Stack left right)
  then show ?case 
    apply(induction left; induction right)
    by auto
qed

lemma not_empty: "size stack > 0 \<Longrightarrow> \<not> isEmpty stack"
proof(induction stack)
  case (Stack left right)
  then show ?case
    apply(induction left; induction right)
    by auto
qed

lemma not_empty_2: "\<not> Stack.isEmpty stack \<Longrightarrow> Stack.toList stack  \<noteq> []"
  apply (induction stack)
  by auto

lemma size_push: "size (push x stack) = Suc (size stack)"
  apply(induction stack arbitrary: x)
  by auto

lemma first: "\<not> isEmpty stack \<Longrightarrow> first stack = hd (toList stack)"
proof(induction stack)
  case (Stack left right)
  then show ?case
    apply(induction left; induction right)
    by auto
qed

lemma empty: "toList stack \<noteq> [] \<Longrightarrow> \<not>isEmpty stack"
proof(induction stack)
  case (Stack left right)
  then show ?case
    apply(induction left; induction right)
    by auto
qed

end