theory RealTimeDeque_Proof
  imports Deque RealTimeDeque States_Proof RealTimeDeque_Enqueue RealTimeDeque_Dequeue
begin

lemma list_rev: "as @ rev bs = cs @ rev ds \<Longrightarrow> bs @ rev as  = ds @ rev cs"
  by (metis rev_append rev_rev_ident)

lemma swap_lists_left: "invar (States Left big small) \<Longrightarrow> 
    States.listL (States Left big small) = rev (States.listL (States Right big small))"
  by(auto split: prod.splits Big.state.splits Small.state.splits)

lemma swap_lists_right: "invar (States Right big small) \<Longrightarrow> 
    States.listL (States Right big small) = rev (States.listL (States Left big small))"
  by(auto split: prod.splits Big.state.splits Small.state.splits)

lemma swap_list: "invar q \<Longrightarrow> listR (swap q) = listL q"
  apply(induction q)
  apply auto
  subgoal for states
    apply(induction states)
    using swap_lists_left swap_lists_right 
    by (metis (full_types)RealTimeDeque.listL.simps(6) direction.exhaust swap.simps(6) swap.simps(7))
  done

lemma swap_list': "invar q \<Longrightarrow> listL (swap q) = listR q"
  using swap_list rev_swap
  by blast

lemma lists_same: "lists (States Left big small) = lists (States Right big small)"
  apply(induction "States Left big small" rule: lists.induct)
  by auto

lemma invar_swap: "invar q \<Longrightarrow> invar (swap q)"
  apply(induction q rule: swap.induct)
  by(auto simp: lists_same split: prod.splits)

lemma size_list_stack: "Stack.list stack = [] \<Longrightarrow> Suc x \<le> 4 * size stack \<Longrightarrow> False"
  apply(induction stack rule: Stack.list.induct)
  by auto

lemma size_list_idle: "Idle.list idle = [] \<Longrightarrow> Suc x \<le> 4 * size idle \<Longrightarrow> False"
  apply(induction idle arbitrary: x rule: Idle.list.induct)
  using size_list_stack by auto

lemma size_list_common: "invar common \<Longrightarrow> Suc x \<le> 4 * size common \<Longrightarrow> Common.list common = [] \<Longrightarrow> False"
proof(induction common arbitrary: x)
  case (Copy x1 x2 x3 x4)
  then show ?case 
  proof(induction x1)
    case (Current x1a x2a x3a x4a)
    then have a: "Stack.list x3a = []"
      by auto

    from Current have b: "Suc x \<le> 4 * size x3a"
      by auto

    from a b size_list_stack show ?case 
      by auto
  qed
next
  case (Idle x1 x2)
  then have a: "0 < size x2"
    by auto

  from Idle have  b: "Suc x \<le> 4 * size x2"
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
  case (Transforming states)

   have "is_empty (Transforming states) \<longleftrightarrow> listL (Transforming states) = []"
   proof
     assume "is_empty (Transforming states)"
     then show "listL (Transforming states) = []"
       by auto
   next
     assume "listL (Transforming states) = []"
     with Transforming show "is_empty (Transforming states)"
       apply auto
     proof(induction states)
       case (States dir big small)
       then show ?case
         apply(induction dir)
         apply(auto split: prod.splits)
         using Big_Proof.list_current_size by force+
     qed
   qed

   then show ?case.
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
  invar    = invar
proof (standard, goal_cases)
  case 1
  then show ?case by (simp add: empty_def)
next
  case (2 q x)
  then show ?case
    by(simp add: list_enqL)
next
  case (3 q x)

  then have invar_swap: "invar (swap q)"
    by (simp add: invar_swap)

  then have "listL (enqL x (swap q)) = x # listL (swap q)"
    by (simp add: list_enqL)

  then have "listL (enqL x (swap q)) = x # listR q"
    by(auto simp: 3 swap_list')

  then show ?case
    using 3
    by (simp add: swap_list invar_enqL invar_swap)
next
  case (4 q)
  then show ?case
    using list_deqL by simp
next
  case (5 q)
  then have invar_swap: "invar (swap q)"
    by (simp add: invar_swap)

  then have "listL (deqL (swap q)) = tl (listL (swap q))"
    using 5 list_deqL swap_list' by fastforce


  then have "listL (deqL (swap q)) = tl (listR q)"
    by (simp add: 5 swap_list')

  then have "listR (swap (deqL (swap q))) = tl (listR q)"
    by (metis "5"(1) "5"(2) invar_deqL listL_is_empty invar_swap swap_list swap_list')

  then show ?case     
    by(auto split: prod.splits)
next
  case (6 q)
  then show ?case
    using list_firstL by simp
next
  case (7 q)

  then have swap_invar: "invar (swap q)"
    by (simp add: invar_swap)

  from 7 have "listR q = listL (swap q)"
    by (simp add: swap_list')

  from 7 have "firstR q = firstL (swap q)"
    by(auto split: prod.splits)

  from 7 have "listL (swap q) \<noteq> []"
    using \<open>listR q = listL (swap q)\<close> by auto

  then have "firstL (swap q) = hd (listL (swap q))"
    using swap_invar list_firstL by auto
  
  then show ?case 
    using \<open>firstR q = firstL (swap q)\<close> \<open>listR q = listL (swap q)\<close> by presburger
next
  case (8 q)
  then show ?case using listL_is_empty by auto
next
  case (9)
  then show ?case
    by (simp add: empty_def)
next
  case (10 q x)
  then show ?case by(simp add: invar_enqL)
next
  case (11 q x)
  then have swap: "enqR x q = swap (enqL x (swap q))"
    by simp

  from 11 have "invar (swap (enqL x (swap q)))"
    by (simp add: invar_enqL invar_swap)

  with swap show ?case 
    by simp
next
  case (12 q)
  then show ?case
    using invar_deqL by auto
next
  case (13 q)
  then have swap: "deqR q = swap (deqL (swap q))"
    by(auto split: prod.splits)

  from 13 have "invar (swap (deqL (swap q)))"
    by (metis invar_deqL invar_swap listL_is_empty rev.simps(1) swap_list)

  with swap show ?case
    by auto
qed

end
