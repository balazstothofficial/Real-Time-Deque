theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Transformation_Proof RealTimeDeque_Enqueue RealTimeDeque_Dequeue
begin
  
lemma swap: "invar q \<Longrightarrow> listR (swap q) = listL q"
  apply(induction q rule: swap.induct)
  by auto

lemma swap': "invar q \<Longrightarrow> listL (swap q) = listR q"
  apply(induction q rule: swap.induct)
  by auto

lemma invar_swap: "invar q \<Longrightarrow> invar (swap q)"
  apply(induction q rule: swap.induct)
  by auto

lemma size_list_stack: "Stack.list stack = [] \<Longrightarrow> Suc x \<le> 4 * Stack.size stack \<Longrightarrow> False"
  apply(induction stack rule: Stack.list.induct)
  by auto

lemma size_list_idle: "Idle.list idle = [] \<Longrightarrow> Suc x \<le> 4 * Idle.size idle \<Longrightarrow> False"
  apply(induction idle arbitrary: x rule: Idle.list.induct)
  using size_list_stack by auto

lemma size_list_common: "Common.invar common \<Longrightarrow> Suc x \<le> 4 * Common.size common \<Longrightarrow> Common.list common = [] \<Longrightarrow> False"
proof(induction common arbitrary: x)
  case (Copy x1 x2 x3 x4)
  then show ?case 
  proof(induction x1)
    case (Current x1a x2a x3a x4a)
    then have a: "Stack.list x3a = []"
      by auto

    from Current have b: "Suc x \<le> 4 * Stack.size x3a"
      by auto

    from a b size_list_stack show ?case 
      by auto
  qed
next
  case (Idle x1 x2)
  then have a: "0 < Idle.size x2"
    by auto

  from Idle have  b: "Suc x \<le> 4 * Idle.size x2"
    by auto

  from Idle have c: "Idle.list x2 = []"
    by auto

  from b c show ?case
    using size_list_idle by auto 
qed

lemma listL_is_empty: "invar deque \<Longrightarrow> is_empty deque = (listL deque = [])"
proof(induction deque)
  case Empty
  then show ?case by auto
next
  case (One x)
  then show ?case by auto
next
  case (Two x1 x2a)
  then show ?case by auto
next
  case (Three x1 x2a x3)
  then show ?case by auto
next
  case (Idle x1 x2a)
  then show ?case 
    apply auto
    by (metis Idle_Proof.pop_list list.discI surj_pair)
next
  case (Transforming x)
  then show ?case 
    apply(induction x)
    apply auto
    using Small_Proof.list_current_size apply force
    apply(auto simp: max_def split: prod.splits Big.state.splits Small.state.splits if_splits)
    subgoal 
      by(simp add: Nat.diff_diff_right diff_is_0_eq' list.size(3) min.absorb1 minus_nat.diff_0 mult_is_0 not_numeral_le_zero numeral_2_eq_2 Stack_Proof.size_list_length split: current.splits)
    subgoal by(auto split!: current.splits)
    subgoal by(auto split: current.splits)
    subgoal by(auto split: current.splits)
    using size_list_common by auto
qed

lemma listL_rev_listR: "listL deque = rev (listR deque)"
proof(induction deque)
  case Empty
  then show ?case by auto
next
  case (One x)
  then show ?case by auto
next
  case (Two x y)
  then show ?case by auto
next
  case (Three x y z)
  then show ?case by auto
next
  case (Idle left right)
  then show ?case by auto
next
  case (Transforming transformation)
  then show ?case 
  proof(induction transformation)
    case (Left small big)
    then show ?case 
      by(auto split: prod.splits)
  next
    case (Right big small)
    then show ?case 
      by(auto split: prod.splits)
  qed
qed
  

interpretation RealTimeDeque: Deque where
  empty    = empty    and
  enqL     = enqL     and
  enqR     = enqR     and
  firstL   = firstL   and
  firstR   = firstR   and
  deqL     = deqL     and
  deqR     = deqR     and
  is_empty = is_empty and
  listL    = listL    and
  listR    = listR    and
  invar    = invar
proof (standard, goal_cases)
  case 1
  then show ?case by (simp add: empty_def)
next
  case 2
  then show ?case by (simp add: empty_def)
next
  case (3 q x)
  then show ?case
    by(simp add: list_enqL)
next
  case (4 q x)

  then have invar_swap: "invar (swap q)"
    by (simp add: invar_swap)

  then have "listL (enqL x (swap q)) = x # listL (swap q)"
    by (simp add: list_enqL)

  then have "listL (enqL x (swap q)) = x # listR q"
    by(auto simp: 4 swap')

  then show ?case
    using 4 
    by (simp add: swap invar_enqL invar_swap)
next
  case (5 q)
  then show ?case
    using list_deqL by simp
next
  case (6 q)
  then have invar_swap: "invar (swap q)"
    by (simp add: invar_swap)

  then have "listL (deqL (swap q)) = tl (listL (swap q))"
    using 6 list_deqL swap' by fastforce


  then have "listL (deqL (swap q)) = tl (listR q)"
    by (simp add: 6 swap')

  then have "listR (swap (deqL (swap q))) = tl (listR q)"
    by (metis "6"(1) "6"(2) is_empty.elims(2) swap invar_deqL invar_swap listL.simps(1) swap')

  then show ?case     
    by(auto split: prod.splits)
next
  case (7 q)
  then show ?case
    using list_firstL by simp
next
  case (8 q)

  then have swap_invar: "invar (swap q)"
    by (simp add: invar_swap)

  from 8 have "listR q = listL (swap q)"
    by (simp add: swap')

  from 8 have "firstR q = firstL (swap q)"
    by(auto split: prod.splits)

  from 8 have "listL (swap q) \<noteq> []"
    using \<open>listR q = listL (swap q)\<close> by auto

  then have "firstL (swap q) = hd (listL (swap q))"
    using swap_invar list_firstL by auto
  
  then show ?case 
    using \<open>firstR q = firstL (swap q)\<close> \<open>listR q = listL (swap q)\<close> by presburger
next
  case (9 q)
  then show ?case using listL_is_empty by auto
next
  case (10 q)
  then show ?case
    by (simp add: listL_is_empty listL_rev_listR)
next
  case 11
  then show ?case 
    by (simp add: empty_def)
next
  case (12 q x)
  then show ?case by(simp add: invar_enqL)
next
  case (13 q x)
  then have swap: "enqR x q = swap (enqL x (swap q))"
    by simp

  from 13 have "invar (swap (enqL x (swap q)))"
    by (simp add: invar_enqL invar_swap)

  with swap show ?case 
    by simp
next
  case (14 q)
  then show ?case
    using invar_deqL by auto
next
  case (15 q)
  then have swap: "deqR q = swap (deqL (swap q))"
    by(auto split: prod.splits)

  from 15 have "invar (swap (deqL (swap q)))"
    by (metis invar_deqL invar_swap listL_is_empty listL_rev_listR rev.simps(1) swap')

  with swap show ?case
    by auto
next 
  case (16 q)
  then show ?case using listL_rev_listR by auto
qed

end
