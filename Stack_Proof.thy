theory Stack_Proof
  imports Stack Util
begin

lemma push_list: "list (push x stack) = x # list stack"
  by(induction stack) auto

lemma pop_list: "\<not> is_empty stack \<Longrightarrow> list (pop stack) = tl (list stack)"
  by(induction stack rule: pop.induct) auto

lemma first_list: "\<not> is_empty stack \<Longrightarrow> first stack = hd (list stack)"
  by(induction stack rule: first.induct) auto

lemma list_empty: "list stack = [] \<longleftrightarrow> is_empty stack"
  by(induction stack rule: is_empty_stack.induct) auto

lemma list_not_empty: "list stack  \<noteq> [] \<longleftrightarrow> \<not> is_empty stack"
  by(induction stack rule: is_empty_stack.induct) auto

lemma size_push: "size (push x stack) = Suc (size stack)"
  by(induction stack arbitrary: x) auto

lemma size_pop: "size (pop stack) = size stack - Suc 0"
  by(induction stack rule: pop.induct) auto

lemma size_empty: "size (stack :: 'a stack) = 0 \<longleftrightarrow> is_empty stack"
  by(induction stack rule: is_empty_stack.induct) auto

lemma size_not_empty: "size (stack :: 'a stack) > 0 \<longleftrightarrow> \<not> is_empty stack"
  by(induction stack rule: is_empty_stack.induct) auto

lemma size_list_length: "size stack = List.length (list stack)"
  by(induction stack) auto

lemma first_pop: "\<not> is_empty stack \<Longrightarrow> first stack # list (pop stack) = list stack"
  by(induction stack rule: pop.induct) auto

lemma push_not_empty: "\<lbrakk>\<not> is_empty stack; is_empty (push x stack)\<rbrakk> \<Longrightarrow> False"
  by(induction x stack rule: push.induct) auto

lemma pop_list_length: "\<not> is_empty stack \<Longrightarrow> Suc (length (list (pop stack))) = length (list stack)"
  by(induction stack rule: pop.induct) auto

lemma first_take: "\<not>is_empty stack \<Longrightarrow> [first stack] = take 1 (Stack.list stack)"
  by (simp add: first_list take_hd list_empty)

lemma first_take_pop: "\<lbrakk>\<not>is_empty stack; 0 < x\<rbrakk>
   \<Longrightarrow> first stack # take (x - Suc 0) (list (pop stack)) = take x (list stack)"
  by(induction stack rule: pop.induct) (auto simp: take_Cons')

lemma pop_drop: "list (pop stack) = drop 1 (list stack)" 
  by(induction stack rule: pop.induct) auto

lemma popN_drop: "list ((pop ^^ n) stack) = drop n (list stack)" 
  by(induction n) (auto simp: pop_drop)

lemma popN_size: "size ((pop ^^ n) stack) = (size stack) - n"
 by(induction n)(auto simp: size_pop)

end