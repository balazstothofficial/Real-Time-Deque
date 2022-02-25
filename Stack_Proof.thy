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

lemma size_pop: "size (pop stack) = size stack - Suc 0"
  by(induction stack rule: pop.induct) auto

lemma size_isEmpty: "size stack = 0 \<longleftrightarrow> isEmpty stack"
  by(induction stack rule: isEmpty.induct) auto

lemma size_isNotEmpty: "size stack > 0 \<longleftrightarrow> \<not> isEmpty stack"
  by(induction stack rule: isEmpty.induct) auto

lemma size_listLength: "Stack.size stack = List.length (Stack.toList stack)"
  by(induction stack) auto

lemma first_pop: "\<not> isEmpty stack \<Longrightarrow> first stack # toList (pop stack) = toList stack"
  by(induction stack rule: pop.induct) auto

lemma push_isNotEmpty: "\<lbrakk>\<not> isEmpty stack; isEmpty (push x stack)\<rbrakk> \<Longrightarrow> False"
  by(induction x stack rule: push.induct) auto

lemma pop_listLength: "\<not> isEmpty stack
   \<Longrightarrow> Suc (length (toList (pop stack))) = length (toList stack)"
  by(induction stack rule: pop.induct) auto

lemma first_take: "\<not>isEmpty stack \<Longrightarrow> [first stack] = take 1 (Stack.toList stack)"
  by (simp add: first_toList take_hd toList_isEmpty)

lemma first_take_pop: "\<lbrakk>\<not>isEmpty stack; 0 < x\<rbrakk>
   \<Longrightarrow> first stack # take (x - Suc 0) (toList (pop stack)) = take x (toList stack)"
  by(induction stack rule: pop.induct) (auto simp: take_Cons')

lemma pop_drop: "toList (pop stack) = drop 1 (toList stack)" 
  by(induction stack rule: pop.induct) auto

lemma popN_drop: "toList ((pop ^^ n) stack) = drop n (toList stack)" 
  by(induction n) (auto simp: pop_drop)

lemma popN_size: "size ((pop ^^ n) stack) = (size stack) - n"
 by(induction n)(auto simp: size_pop)

end