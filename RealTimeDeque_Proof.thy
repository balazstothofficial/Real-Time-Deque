theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Transformation_Proof RealTimeDeque_Enqueue RealTimeDeque_Dequeue
begin

lemma helper_1_1: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> rev (take (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
               (rev (take (leftLength - Suc (Stack.size right)) (Stack.toList right)))) @
         rev (drop (leftLength - Suc (Stack.size right)) (Stack.toList left)) @
         rev (take (leftLength - Suc (Stack.size right)) (Stack.toList left)) =
         Stack.toList right @ rev (Stack.toList left)"
  by (metis append_take_drop_id helper_1_2 rev_append)
  
lemma popN_drop: "\<lbrakk>
  \<not> leftLength \<le> 3 * Stack.size right; 
  idle.Idle left leftLength = Idle.push x left'; 
  Idle.invariant left'; 
  rightLength = Stack.size right;
  \<not> Idle.isEmpty left'; 
  \<not> Stack.isEmpty right
\<rbrakk> \<Longrightarrow> reverseN 
        (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
        (reverseN (leftLength - Suc (Stack.size right)) (Stack.toList right) [])
        (rev (Stack.toList ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left)))
      @ rev (reverseN (leftLength - Suc (Stack.size right)) (reverseN (leftLength - Suc (Stack.size right)) (Stack.toList left) []) []) =
         Stack.toList right @ rev (Stack.toList left)"
  apply(simp add: reverseN_reverseN helper_1)
  by (smt (verit, ccfv_SIG) Idle.size.simps Idle_Proof.size_push toList_isEmpty helper_1 length_greater_0_conv less_Suc_eq_0_disj Stack_Proof.size_listLength)

lemma swap: "invariant q \<Longrightarrow> listRight (swap q) = listLeft q"
  apply(induction q rule: swap.induct)
  by auto

lemma swap': "invariant q \<Longrightarrow> listLeft (swap q) = listRight q"
  apply(induction q rule: swap.induct)
  by auto

lemma swap_1: "invariant q \<Longrightarrow> invariant (swap q)"
  apply(induction q rule: swap.induct)
  by auto

lemma swap_2: "invariant (swap q) \<Longrightarrow> listLeft (enqueueLeft x (swap q)) = x # listLeft (swap q)"
  by(auto simp: list_enqueueLeft)

lemma swap_2': "swap (enqueueLeft x (swap q)) = enqueueRight x q"
  by auto

lemma swap_3:
  assumes
    "invariant q" 
  shows
    "listLeft (enqueueLeft x (swap q)) = listRight (enqueueRight x q)"
proof-
  have "listLeft (enqueueLeft x (swap q)) = x # listLeft (swap q)"
    by(auto simp: assms swap_2 swap_1)

  then have 1: "listLeft (enqueueLeft x (swap q)) = x # listRight q"
    by(auto simp: assms swap')

  have "invariant (enqueueLeft x (swap q))"
    by (simp add: assms invariant_enqueueLeft swap_1)

  with 1 have "listRight (swap (enqueueLeft x (swap q))) = x # listRight q"
    by (simp add: swap)

  then have "listRight (enqueueRight x q) = x # listRight q"
    by simp

  with 1 show ?thesis
    by simp
qed

lemma maybe2: "\<lbrakk>
  \<not> Suc l \<le> 3 * r; 
  l > 0;
  r > 0;
  l \<le> 3 * r;
  r \<le> 3 * l;
  Suc l + Suc l - Suc (Suc (r + r)) \<le> Suc (Suc l + r)
\<rbrakk> \<Longrightarrow> 10 + (9 * r + Suc l) \<le> 12 * (Suc l - Suc r)"
  by auto

lemma fixed: "States.inSizeWindow (big, small) \<Longrightarrow> inSizeWindow (Left small big)"
  by auto

lemma fixed_2: "States.inSizeWindow (big, small) \<Longrightarrow> inSizeWindow (Right big small)"
  by auto

lemma fixed_3: "States.inSizeWindow (States.tick (big, small)) \<Longrightarrow> inSizeWindow (tick (Left small big))"
  by(auto split: prod.splits)

lemma fixed_4: "States.inSizeWindow (States.tick (big, small)) \<Longrightarrow> inSizeWindow (tick (Right big small))"
  by(auto split: prod.splits)





lemma geficke: "States.inSizeWindow ((States.tick) (right, Small.push x left)) \<Longrightarrow>
        Transformation.inSizeWindow (tick (transformation.Left (Small.push x left) right))"
   by (smt (z3) Transformation.inSizeWindow.simps(1) Transformation.tick.simps(1) case_prod_unfold prod.exhaust_sel)



lemma geficke3:  "Small.pop small =(x, small') \<Longrightarrow> States.inSizeWindow ((States.tick ^^ n) (right, small')) \<Longrightarrow>
     Transformation.inSizeWindow ((tick ^^ n) (transformation.Left small' right))"
  by (simp add: fixed_5)

lemma remSteps_idle_1: "States.invariant states \<Longrightarrow> States.remainingSteps states = 0 \<Longrightarrow> (
    case states of (Big.Common (Common.Idle _ _), Small.Common (Common.Idle _ _)) \<Rightarrow> True 
                | _ \<Rightarrow> False) "
  apply(induction states)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remSteps_idle_2: "States.invariant states \<Longrightarrow> (
    case states of (Big.Common (Common.Idle _ _), Small.Common (Common.Idle _ _)) \<Rightarrow> True 
                | _ \<Rightarrow> False) \<Longrightarrow> States.remainingSteps states = 0"
  apply(induction states)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remSteps_idle_3: "States.invariant states \<Longrightarrow> States.remainingSteps states = 0 \<longleftrightarrow> (
    case states of (Big.Common (Common.Idle _ _), Small.Common (Common.Idle _ _)) \<Rightarrow> True 
                | _ \<Rightarrow> False) "
  apply(induction states)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remSteps_idle_4: "States.invariant states \<Longrightarrow> States.remainingSteps states > 0 \<longleftrightarrow> (
    case states of (Big.Common (Common.Idle _ _), Small.Common (Common.Idle _ _)) \<Rightarrow> False 
                | _ \<Rightarrow> True) "
  apply(induction states)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma finallly_1: "Stack.toList stack = [] \<Longrightarrow> Suc x \<le> 4 * Stack.size stack \<Longrightarrow> False"
  apply(induction stack rule: Stack.toList.induct)
  by auto

lemma finallly_2: "Idle.toList idle = [] \<Longrightarrow> Suc x \<le> 4 * Idle.size idle \<Longrightarrow> False"
  apply(induction idle arbitrary: x rule: Idle.toList.induct)
  using finallly_1 by auto

lemma finallly: "Common.invariant common \<Longrightarrow> Suc x \<le> 4 * Common.size common \<Longrightarrow> Common.toList common = [] \<Longrightarrow> False"
proof(induction common arbitrary: x)
  case (Copy x1 x2 x3 x4)
  then show ?case 
  proof(induction x1)
    case (Current x1a x2a x3a x4a)
    then have a: "Stack.toList x3a = []"
      by auto

    from Current have b: "Suc x \<le> 4 * Stack.size x3a"
      by auto

    from a b finallly_1 show ?case 
      by auto
  qed
next
  case (Idle x1 x2)
  then have a: "0 < Idle.size x2"
    by auto

  from Idle have  b: "Suc x \<le> 4 * Idle.size x2"
    by auto

  from Idle have c: "Idle.toList x2 = []"
    by auto

  from b c show ?case
    using finallly_2 by auto 
qed

lemma isEmpty_listLeft: "invariant deque \<Longrightarrow> isEmpty deque = (listLeft deque = [])"
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
    by (metis Idle_Proof.pop_toList list.discI surj_pair)
next
  case (Transforming x)
  then show ?case 
    apply(induction x)
    apply auto
    using Small_Proof.toCurrentList_size apply force
    apply(auto simp: max_def split: prod.splits Big.state.splits Small.state.splits if_splits)
    subgoal 
      by (simp add: Nat.diff_diff_right diff_is_0_eq' list.size(3) min.absorb1 minus_nat.diff_0 mult_is_0 not_numeral_le_zero numeral_2_eq_2 Stack_Proof.size_listLength split: current.splits)
    subgoal by(auto split!: current.splits)
    subgoal by(auto split: current.splits)
    subgoal by(auto split: current.splits)
    using finallly by auto
qed

lemma listLeft_rev_listRight: "listLeft deque = rev (listRight deque)"
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
    then show ?case by(auto split: prod.splits)
  next
    case (Right big small)
    then show ?case 
      by(auto split: prod.splits)
  qed
qed
  

interpretation RealTimeDeque: Deque where
  empty        = empty        and
  enqueueLeft  = enqueueLeft  and
  enqueueRight = enqueueRight and
  firstLeft    = firstLeft    and
  firstRight   = firstRight   and
  dequeueLeft  = dequeueLeft  and
  dequeueRight = dequeueRight and
  isEmpty      = isEmpty      and
  listLeft     = listLeft     and
  listRight    = listRight    and
  invariant    = invariant
proof (standard, goal_cases)
  case 1
  then show ?case by (simp add: empty_def)
next
  case 2
  then show ?case by (simp add: empty_def)
next
  case (3 q x)
  then show ?case
    by(simp add: list_enqueueLeft)
next
  case (4 q x)

  then have invariant_swap: "invariant (swap q)"
    by (simp add: swap_1)

  then have "listLeft (enqueueLeft x (swap q)) = x # listLeft (swap q)"
    by (simp add: list_enqueueLeft)

  then have "listLeft (enqueueLeft x (swap q)) = x # listRight q"
    by(auto simp: 4 swap')

  then show ?case
    using 4 swap_3 by fastforce
next
  case (5 q)
  then show ?case
    using list_dequeueLeft by simp
next
  case (6 q)
  then have invariant_swap: "invariant (swap q)"
    by (simp add: swap_1)

  then have "listLeft (dequeueLeft (swap q)) = tl (listLeft (swap q))"
    using 6 list_dequeueLeft swap' by fastforce


  then have "listLeft (dequeueLeft (swap q)) = tl (listRight q)"
    by (simp add: 6 swap')

  then have "listRight (swap (dequeueLeft (swap q))) = tl (listRight q)"
    by (metis "6"(1) "6"(2) RealTimeDeque.isEmpty.elims(2) RealTimeDeque_Proof.swap invariant_dequeueLeft invariant_swap listLeft.simps(1) swap')

  then show ?case     
    by(auto split: prod.splits)
next
  case (7 q)
  then show ?case
    using list_firstLeft by simp
next
  case (8 q)

  then have swap_invariant: "invariant (swap q)"
    by (simp add: swap_1)

  from 8 have "listRight q = listLeft (swap q)"
    by (simp add: swap')

  from 8 have "firstRight q = firstLeft (swap q)"
    by(auto split: prod.splits)

  from 8 have "listLeft (swap q) \<noteq> []"
    using \<open>listRight q = listLeft (swap q)\<close> by auto

  then have "firstLeft (swap q) = hd (listLeft (swap q))"
    using swap_invariant list_firstLeft by auto
  
  then show ?case 
    using \<open>firstRight q = firstLeft (swap q)\<close> \<open>listRight q = listLeft (swap q)\<close> by presburger
next
  case (9 q)
  then show ?case using isEmpty_listLeft by auto
next
  case (10 q)
  then show ?case
    by (simp add: isEmpty_listLeft listLeft_rev_listRight)
next
  case 11
  then show ?case 
    by (simp add: RealTimeDeque.empty_def)
next
  case (12 q x)
  then show ?case by(simp add: invariant_enqueueLeft)
next
  case (13 q x)
  then have swap: "enqueueRight x q = swap (enqueueLeft x (swap q))"
    by simp

  from 13 have "invariant (swap (enqueueLeft x (swap q)))"
    by (simp add: invariant_enqueueLeft swap_1)

  with swap show ?case 
    by simp
next
  case (14 q)
  then show ?case
    using invariant_dequeueLeft by auto
next
  case (15 q)
  then have swap: "dequeueRight q = swap (dequeueLeft (swap q))"
    by(auto split: prod.splits)

  from 15 have "invariant ( swap (dequeueLeft (swap q)))"
    by (metis RealTimeDeque.isEmpty.elims(2) RealTimeDeque_Proof.swap invariant_dequeueLeft isEmpty_listLeft listRight.simps(1) swap_1)

  with swap show ?case
    by auto
next 
  case (16 q)
  then show ?case using listLeft_rev_listRight by auto
qed

end
