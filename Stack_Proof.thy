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

lemma not_empty_2: "\<not> isEmpty stack \<Longrightarrow> toList stack  \<noteq> []"
  apply (induction stack)
  by auto

lemma size_push: "size (push x stack) = Suc (size stack)"
  apply(induction stack arbitrary: x)
  by auto

lemma size_pop: "\<not> isEmpty stack \<Longrightarrow> size (pop stack) = size stack - Suc 0"
proof(induction stack)
  case (Stack left right)
  then show ?case 
  proof(induction left)
    case Nil
    then show ?case 
    proof(induction right)
      case Nil
      then show ?case by auto
    next
      case (Cons a right)
      then show ?case by auto
    qed
    next
    case (Cons a left)
    then show ?case by auto
  qed
qed

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

lemma first_pop: "\<not> isEmpty stack \<Longrightarrow> first stack # Stack.toList (pop stack) = Stack.toList stack"
  apply(induction stack rule: pop.induct)
  by auto

lemma size_listLength: "Stack.size stack = List.length (Stack.toList stack)"
  apply(induction stack)
  by auto

end