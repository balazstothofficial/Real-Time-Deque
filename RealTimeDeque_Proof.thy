theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Transformation_Proof
begin

fun runningFold :: "('a deque \<Rightarrow> 'a deque) list \<Rightarrow> 'a deque \<Rightarrow> 'a deque list" where
  "runningFold [] _ = []"
| "runningFold (x#xs) deque = (
  let deque = x deque 
  in deque # runningFold xs deque
)"

value "runningFold 
  [
  enqueueLeft (0::int), 
  enqueueLeft 1, 
  enqueueLeft 2,
  enqueueLeft 3,
  enqueueLeft 4,
  enqueueLeft 5,
  enqueueLeft 6,
  enqueueLeft 7,
  enqueueLeft 8,
  enqueueLeft 9,
  enqueueLeft 10,
  enqueueLeft 11,
  enqueueLeft 12,
  enqueueLeft 13,
  enqueueLeft 14,
  enqueueLeft 15,
  enqueueLeft 16,
  enqueueLeft 17,
  enqueueLeft 18,
  enqueueLeft 19,
  enqueueLeft 20,
  enqueueLeft 21,
  enqueueLeft 22,
  enqueueLeft 23,
  enqueueLeft 24,
  enqueueLeft 25,
  dequeueRight,
   dequeueRight,
   dequeueRight,
   dequeueRight,
   dequeueRight,
   dequeueRight,
   dequeueRight,
   dequeueLeft,
   dequeueLeft,
   dequeueLeft,
    dequeueLeft
 
  ] 
  Empty"

(* TODO: Clean up! *)
lemma revN_take: "revN n xs acc = rev (take n xs) @ acc"
  apply(induction n xs acc rule: revN.induct)
  by auto

lemma revN_revN: "(revN n (revN n xs []) []) = take n xs"
  by(auto simp: revN_take)

lemma pop_drop: "Stack.toList ((Stack.pop ^^ n) stack) = drop n (Stack.toList stack)"
proof(induction n arbitrary: stack)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  then show ?case 
  proof(induction stack rule: Stack.pop.induct)
    case 1
    then show ?case 
      by(auto simp: funpow_swap1)
  next
    case (2 x left right)
    then show ?case 
      by(auto simp: funpow_swap1)
  next
    case (3 x right)
    then show ?case  
      by(auto simp: funpow_swap1)
  qed
qed

lemma test: "rev (drop n xs) @
             rev (take n xs) = rev xs"
  by (metis append_take_drop_id rev_append)

lemma test_2: "List.length (Stack.toList stack) = Stack.size stack"
  apply(induction stack)
  by auto

lemma helper_1_4: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> Stack.size right - (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left)) = 0"
proof -
  assume a1: "Idle.invariant left'"
  assume a2: "rightLength = Stack.size right"
  assume "idle.Idle left leftLength = Idle.push x left'"
  then have f3: "\<And>n. List.length (drop n (Stack.toList left)) = leftLength - n"
    using a1 by (metis (no_types) Idle.invariant.simps Idle_Proof.invariant_push length_drop size_listLength)
  moreover
  { assume "\<exists>n. rightLength + (rightLength + 1) - leftLength = rightLength + n"
    moreover
    { assume "\<exists>n. rightLength + (rightLength + 1) - (leftLength - (leftLength - (rightLength + 1))) = rightLength + n"
      then have "rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.toList left))) = 0"
        using f3 diff_is_0_eq nat_le_iff_add by presburger }
    ultimately have "leftLength \<le> rightLength + 1 \<longrightarrow> rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.toList left))) = 0"
      using diff_zero by fastforce }
  ultimately show ?thesis
    using a2 by (smt (z3) Nat.add_diff_assoc Nat.diff_diff_right Suc_1 Suc_eq_plus1_left add.commute add_Suc_right add_diff_cancel_right' cancel_comm_monoid_add_class.diff_cancel mult_2 nat_le_linear pop_drop size_listLength)
qed


lemma helper_1_3: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> Suc (List.length (Stack.toList right) + Stack.size right) - leftLength = 0"
  by(auto simp: test_2)

lemma helper_1_2: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> rev (
            take 
               (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
               (rev (
                      take (leftLength - Suc (Stack.size right)) (Stack.toList right))
                    )
               ) =
         Stack.toList right"
  by(auto simp: rev_take helper_1_3 test_2 helper_1_4)

lemma helper_1_1: "\<lbrakk>\<not> leftLength \<le> 3 * Stack.size right; idle.Idle left leftLength = Idle.push x left'; Idle.invariant left'; rightLength = Stack.size right;
     \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; \<not> Stack.isEmpty left\<rbrakk>
    \<Longrightarrow> rev (take (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
               (rev (take (leftLength - Suc (Stack.size right)) (Stack.toList right)))) @
         rev (drop (leftLength - Suc (Stack.size right)) (Stack.toList left)) @
         rev (take (leftLength - Suc (Stack.size right)) (Stack.toList left)) =
         Stack.toList right @ rev (Stack.toList left)"
  by(auto simp: test helper_1_2)

lemma helper_1: "\<lbrakk>
  \<not> leftLength \<le> 3 * Stack.size right; 
  idle.Idle left leftLength = Idle.push x left'; 
  Idle.invariant left'; rightLength = Stack.size right;
  \<not> Idle.isEmpty left'; 
  \<not> Stack.isEmpty right;
   \<not> Stack.isEmpty left
\<rbrakk> \<Longrightarrow> revN (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
          (revN (leftLength - Suc (Stack.size right)) (Stack.toList right) [])
          (rev (Stack.toList ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))) @
         rev (take (leftLength - Suc (Stack.size right)) (Stack.toList left)) =
         Stack.toList right @ rev (Stack.toList left)"
  by(auto simp: revN_take pop_drop helper_1_1)

lemma helper: "\<lbrakk>
  \<not> leftLength \<le> 3 * Stack.size right; 
  idle.Idle left leftLength = Idle.push x left'; 
  Idle.invariant left'; 
  rightLength = Stack.size right;
  \<not> Idle.isEmpty left'; 
  \<not> Stack.isEmpty right
\<rbrakk> \<Longrightarrow> revN 
        (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
        (revN (leftLength - Suc (Stack.size right)) (Stack.toList right) [])
        (rev (Stack.toList ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left)))
      @ rev (revN (leftLength - Suc (Stack.size right)) (revN (leftLength - Suc (Stack.size right)) (Stack.toList left) []) []) =
         Stack.toList right @ rev (Stack.toList left)"
  apply(simp add: revN_revN helper_1)
  by (smt (verit, ccfv_SIG) Idle.size.simps Idle_Proof.size_push empty helper_1 length_greater_0_conv less_Suc_eq_0_disj size_listLength)

lemma list_enqueueLeft: "invariant deque \<Longrightarrow> listLeft (enqueueLeft x deque) = x # listLeft deque"
  proof(induction x deque rule: enqueueLeft.induct)
    case (1 x)
    then show ?case by auto
  next
    case (2 x y)
    then show ?case by auto
  next
    case (3 x y z)
    then show ?case by auto
  next
    case (4 x a b c)
    then show ?case by auto
  next
    case (5 x left' right rightLength)
    then show ?case 
    proof(induction "Idle.push x left'")
      case (Idle left leftLength)
      then show ?case 
      proof(induction "3 * rightLength \<ge> leftLength")
        case True
        then show ?case
          apply(auto split: idle.splits)
          by (metis Idle.toList.simps Idle_Proof.push)+
      next
        case False
        let ?transformation = "(Right 
            (Reverse (Current [] 0 left (leftLength - Suc (Stack.size right))) left [] (leftLength - Suc (Stack.size right)))
            (Reverse1 (Current [] 0 right (Suc (2 * Stack.size right))) right []))"

        from False have leftNotEmpty: "\<not> Stack.isEmpty left"
        proof(induction x left' rule: Idle.push.induct)
          case (1 x stack stackSize)
          then show ?case
            apply(induction x stack rule: Stack.push.induct)
            by auto
        qed

        from False have invariant: "Transformation.invariant ?transformation"
          apply(auto)
          apply(auto simp: revN_take helper leftNotEmpty)
              apply (metis Idle.invariant.simps Idle_Proof.invariant_push diff_le_self)
             apply (simp add: size_listLength)+
          subgoal (* Just times out *) sorry
          by (metis Idle.invariant.simps Idle_Proof.invariant_push add_Suc_right diff_add_inverse)
       
        then have "toListLeft ?transformation = x # Idle.toList left' @ rev (Stack.toList right)"
          apply(auto simp: revN_take)
          by (metis (no_types, lifting) Idle.hyps Idle.toList.simps Idle_Proof.push append_Cons append_assoc rev_append rev_swap)

        with invariant have 
           "toListLeft (sixTicks ?transformation) = x # Idle.toList left' @ rev (Stack.toList right)"
          by (auto simp: sixTicks)

        with False show ?case
          by(auto simp: Let_def invariant_sixTicks tick_toList split: idle.splits)
      qed
    qed
  next
    case (6 x left right)
    let ?newLeft = "Small.push x left"
    let ?newTransfomation = "Left ?newLeft right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    from 6 have invariant: "Transformation.invariant ?newTransfomation"
      by (meson RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) invariant_push_small)

    then have toList: "toListLeft ?newTransfomation = x # Small.toCurrentList left @ rev (Big.toCurrentList right)"
      by(auto simp: push_small currentList_push)
                          
    from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
      using invariant_fourTicks by blast

    then have "toListLeft ?tickedTransformation = x # Small.toCurrentList left @ rev (Big.toCurrentList right)"
      using Transformation_Proof.fourTicks invariant toList by fastforce

    with 6 show ?case
      by(auto simp: Let_def split: transformation.splits state_splits)
  next
    case (7 x left right)

    let ?newLeft = "Big.push x left"
    let ?newTransfomation = "Right ?newLeft right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    from 7 have invariant: "Transformation.invariant ?newTransfomation"
      by (meson RealTimeDeque.invariant.simps Transformation.invariant.simps invariant_push_big)

    then have toListRight: "toListRight ?newTransfomation = Small.toCurrentList right @ rev (Big.toCurrentList (Big.push x left))"
      by auto

    with invariant have toListLeft: "toListLeft ?newTransfomation = x # Big.toCurrentList left @ rev (Small.toCurrentList right)"
      apply(auto simp: push_big split: prod.splits)
      by (metis Big_Proof.currentList_push append_Cons rev_append rev_rev_ident)
    
    from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
      using invariant_fourTicks by blast

    then have "toListLeft ?tickedTransformation = x # Big.toCurrentList left @ rev (Small.toCurrentList right)"
      using Transformation_Proof.fourTicks invariant toListLeft by fastforce


    with 7 show ?case 
      apply(auto simp: Let_def split: transformation.split prod.split Big.state.split Common.state.split Small.state.split)
      by (metis rev_append rev_rev_ident)+
  qed

lemma swap: "invariant q \<Longrightarrow> listRight (swap q) = listLeft q"
  apply(induction q rule: swap.induct)
  by auto

lemma swap_1: "invariant q \<Longrightarrow> invariant (swap q)"
  apply(induction q rule: swap.induct)
  by auto

lemma swap_2: "invariant (swap q) \<Longrightarrow> listLeft (enqueueLeft x (swap q)) = x # listLeft (swap q)"
  by(auto simp: list_enqueueLeft)

lemma maybe: "\<lbrakk>Idle.pop left = (x, idle.Idle left' leftLength'); Idle.invariant left\<rbrakk> \<Longrightarrow>  Stack.toList left' = tl (Idle.toList left)"
  apply(induction left rule: Idle.pop.induct)
  apply auto
  by (metis Stack.isEmpty.elims(2) Stack.pop.simps(1) Stack_Proof.pop empty list.sel(2))

(*lemma maybe_2_1: "\<lbrakk>\<not> Common.isEmpty common; Common.pop common = (x, common')\<rbrakk> \<Longrightarrow> Common.toList common = x # Common.toList common'"
proof(induction common rule: Common.pop.induct)
  case (1 current idle)
  then show ?case
  proof(induction idle rule: Idle.pop.induct)
    case (1 stack stackSize)
    then show ?case
      apply(induction current rule: get.induct)
       apply auto
       apply(induction stack rule: Stack.pop.induct)
         apply auto
      apply(induction stack rule: Stack.pop.induct)
      by auto
  qed
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)

    then show ?case 
    proof(induction  "remained - Suc 0 \<le> moved")
      case True
    

      with True show ?case 
        apply auto
        sorry
    next
      case False
      then show ?case 
        apply auto
        sorry
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed
   *)

(*lemma maybe_2: "\<lbrakk>
  left = Small.state.Common x3;
  Common.pop x3 = (x, state);
   Common.invariant x2a;
   Common.invariant x3;
  Common.toList x3 @ rev (Common.toList x2a) = Common.toCurrentList x3 @ rev (Common.toCurrentList x2a);
  \<not> Common.isEmpty x2a;
  \<not> Common.isEmpty x3; 
  Common.toCurrentList x3 \<noteq> []
\<rbrakk>  \<Longrightarrow> Common.toList state @ rev (Common.toList x2a) = Common.toCurrentList state @ rev (Common.toCurrentList x2a)"
proof(induction x3 rule: Common.pop.induct)
  case (1 current idle)
  then show ?case 
    apply(auto split: prod.splits)
    by (metis Idle_Proof.pop append_Cons get list.sel(3))
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
    proof(induction old rule: Stack.pop.induct)
      case 1
      then show ?case by auto
    next
      case (2 x left right)
      then show ?case 
        apply auto
        apply (smt (verit, best) Suc_diff_Suc diff_Suc_1 diff_self_eq_0 diff_zero leD le_less_Suc_eq length_Cons less_add_same_cancel2 less_le_trans less_nat_zero_code list.sel(3) list.size(3) neq0_conv revN.elims revN.simps(1) tl_append2)
        apply(induction "(remained - Suc (List.length new))" aux new rule: revN.induct)
          apply auto
        sorry
    next
      case (3 x right)
      then show ?case 
        apply auto
        sorry
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed*)
 

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

  have "listLeft (enqueueLeft x (swap q)) = x # listRight q"
    sorry

  then have "listRight (swap (enqueueLeft x (swap q))) = x # listRight q"
    using invariant_swap
    sorry

  then show ?case
    by auto
next
  case (5 q)
  then show ?case
  proof(induction q rule: dequeueLeft'.induct)
    case (1 x)
    then show ?case by auto
  next
    case (2 x y)
    then show ?case by auto
  next
    case (3 x y z)
    then show ?case by auto
  next
    case (4 left right rightLength)

    then obtain x left' leftLength' where "Idle.pop left = (x, (idle.Idle left' leftLength'))"
      using Idle.push.cases by blast
  
    with 4 show ?case
    proof(induction "3 * leftLength' \<ge> rightLength")
      case True
      then show ?case 
        apply auto
        apply (metis Idle.toList.simps Idle_Proof.pop list.sel(3))
        by (metis Idle.toList.simps Idle_Proof.pop list.distinct(1) list.sel(3) tl_append2)
    next
      case False
      then show ?case
      proof(induction "leftLength' \<ge> 1")
        case True
        let ?transformation = "
         Left (Reverse1 (Current [] 0 left' (Suc (2 * leftLength'))) left' [])
              (Reverse (Current [] 0 right (Stack.size right - Suc leftLength')) right [] (Stack.size right - Suc leftLength'))"

        from True have invariant: "Transformation.invariant ?transformation"
          apply(auto simp: size_listLength)
          apply (metis RealTimeDeque_Proof.revN_revN RealTimeDeque_Proof.revN_take append_Nil2)
                  apply (metis Idle.invariant.simps Idle_Proof.invariant_pop eq_imp_le le_SucI mult_2 size_listLength trans_le_add2)
                 apply(auto simp: revN_take)
          subgoal sorry (* Just timed out *)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_diff_le diff_add_inverse le_add1 mult_2 size_listLength)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 size_listLength trans_le_add2)
             apply (metis Idle.invariant.simps Idle_Proof.invariant_pop le_SucI le_add1 mult_2 size_listLength)
          apply (metis Idle_Proof.pop \<open>\<lbrakk>Suc 0 \<le> leftLength'; \<not> List.length (Stack.toList right) \<le> 3 * leftLength'; Idle.pop left = (x, idle.Idle left' leftLength'); Idle.invariant left; rightLength = List.length (Stack.toList right); \<not> Idle.isEmpty left; \<not> Stack.isEmpty right; Idle.size left \<le> 3 * List.length (Stack.toList right); List.length (Stack.toList right) \<le> 3 * Idle.size left; Idle.toList left \<noteq> []\<rbrakk> \<Longrightarrow> rev (take (Suc (2 * leftLength') - List.length (Stack.toList ((Stack.pop ^^ (List.length (Stack.toList right) - Suc leftLength')) right))) (rev (take (List.length (Stack.toList right) - Suc leftLength') (Stack.toList left')))) @ rev (Stack.toList ((Stack.pop ^^ (List.length (Stack.toList right) - Suc leftLength')) right)) @ rev (take (List.length (Stack.toList right) - Suc leftLength') (Stack.toList right)) = Stack.toList left' @ rev (Stack.toList right)\<close> list.distinct(1))
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_diff_le add_diff_cancel_right' le_add2 mult_2 size_listLength)
          by (metis Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 size_listLength trans_le_add2)

        with True have "toListLeft ?transformation = tl (Idle.toList left) @ rev (Stack.toList right)"
          by(auto simp: maybe)

        with invariant have "toListLeft (sixTicks ?transformation) = tl (Idle.toList left) @ rev (Stack.toList right)"
          by (auto simp: sixTicks)

        with True show ?case apply(auto simp: Let_def invariant_sixTicks tick_toList split: prod.splits)
          by (metis Idle_Proof.pop list.discI tl_append2)

      next
        case False
        obtain right1 right2 where "right = Stack right1 right2"
          using Stack.toList.cases by blast

        with False show ?case 
          apply(induction right1 right2 rule: toSmallDeque.induct)
          apply auto
          apply (metis (mono_tags, lifting) Cons_eq_append_conv Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop le_zero_eq length_0_conv list.sel(3) not_less_eq_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) Cons_eq_append_conv Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop le_zero_eq length_0_conv list.sel(3) not_less_eq_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop apply fastforce
          using Idle_Proof.invariant_pop Idle_Proof.size_pop by fastforce
      qed
    qed    
      
  next
    case (5 left right)
    then show ?case 
    proof(induction "Small.pop left")
      case (Pair x left')
      let ?newTransfomation = "Left left' right"
      let ?tickedTransformation = "fourTicks ?newTransfomation"
  
      from Pair have invariant: "Transformation.invariant ?newTransfomation"
        by (metis RealTimeDeque.invariant.simps(6) States.isEmpty.simps Transformation.isEmpty.simps(1) Transformation_Proof.invariant_pop_small)
     
      then have toList: "toListLeft ?newTransfomation = tl (Small.toCurrentList left) @ rev (Big.toCurrentList right)"
        apply(auto)
        by (metis Pair.hyps Pair.prems(1) RealTimeDeque.invariant.simps(6) Small_Proof.currentList_pop States.isEmpty.simps Transformation.isEmpty.simps(1))

      from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
        using invariant_fourTicks by blast

      then have "toListLeft ?tickedTransformation = tl (Small.toCurrentList left) @ rev (Big.toCurrentList right)"
        using Transformation_Proof.fourTicks invariant toList by fastforce


      with Pair show ?case 
        apply(auto simp: Let_def split: prod.split transformation.split Small.state.split Common.state.split Big.state.split)
              apply (metis Small_Proof.currentList_empty tl_append2)
        using Small_Proof.currentList_empty apply fastforce
            apply (metis Small_Proof.currentList_empty tl_append2)
        using Small_Proof.currentList_empty by fastforce+
    qed
  next
    case (6 left right)
    then show ?case 
      sorry
  next
    case 7
    then show ?case by auto
  qed
next
  case (6 q)
  then show ?case sorry
next
  case (7 q)
  then show ?case
  proof(induction q)
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
    then show ?case sorry
  next
    case (Transforming x)
    then show ?case sorry
  qed
next
  case (8 q)
  then show ?case
    sorry
next
  case (9 q)
  then show ?case
  proof(induction q)
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
      by (metis Idle_Proof.pop list.discI surj_pair)
  next
    case (Transforming x)
    then show ?case 
      apply(induction x)
       apply(auto split: )
      using Big_Proof.currentList_empty apply blast
      by (smt (z3) Nil_is_append_conv Small_Proof.currentList_empty case_prod_conv old.prod.exhaust rev.simps(1) rev_rev_ident)
  qed
next
  case (10 q)
  then show ?case sorry
next
  case 11
  then show ?case 
    by (simp add: RealTimeDeque.empty_def)
next
  case (12 q x)
  then show ?case
  proof(induction x q rule: enqueueLeft.induct)
  case (1 x)
    then show ?case by auto
  next
    case (2 x y)
    then show ?case by auto
  next
    case (3 x y z)
    then show ?case by auto
  next
    case (4 x a b c)
    then show ?case by auto 
  next
    case (5 x left' right rightLength)
    then show ?case
    proof(induction "Idle.push x left'")
      case (Idle left leftLength)
      then show ?case
      proof(induction "3 * rightLength \<ge> leftLength")
        case True
        then show ?case
          apply(auto split: idle.splits)
             apply (metis Idle.invariant.simps Idle_Proof.invariant_push)
            apply (metis Idle.size.simps Idle_Proof.size_push not_empty zero_less_Suc)
           apply (metis Idle.invariant.simps Idle_Proof.invariant_push)
          by (metis Idle.size.simps Idle_Proof.size_push diff_is_0_eq' le_diff_conv mult.commute mult_Suc zero_le_numeral)
      next
        case False
        let ?transformation = "(Right 
            (Reverse (Current [] 0 left (leftLength - Suc (Stack.size right))) left [] (leftLength - Suc (Stack.size right)))
            (Reverse1 (Current [] 0 right (Suc (2 * Stack.size right))) right []))"

        from False have leftNotEmpty: "\<not> Stack.isEmpty left"
          proof(induction x left' rule: Idle.push.induct)
            case (1 x stack stackSize)
            then show ?case
              apply(induction x stack rule: Stack.push.induct)
              by auto
          qed

        from False have inSizeWindow: "inSizeWindow ?transformation"
          apply auto
          sorry

        from False have invariant: "Transformation.invariant ?transformation"
          apply(auto simp: helper leftNotEmpty)
              apply (metis Idle.invariant.simps Idle_Proof.invariant_push diff_le_self)
          sorry
          (*    apply (metis Idle.invariant.simps Idle_Proof.invariant_push Suc_diff_le add_diff_cancel_left' le_add1)
          by (metis Idle.invariant.simps Idle_Proof.invariant_push diff_diff_cancel diff_is_0_eq' funpow_0 helper_1_3 helper_1_4 leftNotEmpty length_greater_0_conv less_numeral_extra(3) mult_2 nat_le_linear not_empty_2 size_listLength)
          *)
    
        with inSizeWindow have sixTicks_inSizeWindow: "inSizeWindow (sixTicks ?transformation)"
          using sixTicks_inSizeWindow by blast

       from invariant have "Transformation.invariant (sixTicks ?transformation)"
          using invariant_sixTicks by blast

        with False sixTicks_inSizeWindow show ?case
          by(auto simp: Let_def split: idle.splits)
       qed
    qed
  next
    case (6 x left right)
    let ?newLeft = "Small.push x left"
    let ?newTransfomation = "Left ?newLeft right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    from 6 have invariant: "Transformation.invariant ?newTransfomation"
      by (meson RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) invariant_push_small)

    then have invariant_fourTicks: "Transformation.invariant (fourTicks ?newTransfomation)"
      using invariant_fourTicks by blast

    from 6 invariant have "inSizeWindow ?newTransfomation"
    proof(induction x left rule: Small.push.induct)
      case (1 x state)
      then show ?case
      proof(induction x state rule: Common.push.induct)
        case (1 x current stack stackSize)
        then show ?case
          apply(induction x current rule: put.induct)
          sorry
      next
        case (2 x current aux new moved)
        then show ?case 
        proof(induction x current rule: put.induct)
          case (1 element extra added old remained)
          then show ?case 
            apply(auto simp: revN_take  split: state_splits)
            subgoal for x2
              apply(induction x2 rule: Common.remainingSteps.induct)
               apply auto
              sorry
            sorry
        qed
      qed
    next
      case (2 x current small auxS)
      then show ?case sorry
    next
      case (3 x current auxS big newS count)
      then show ?case
       proof(induction x current rule: put.induct)
         case (1 element extra added old remained)

         have "\<not> Current.isEmpty (Current extra (List.length extra) old (List.length newS + Stack.size big + Stack.size old)) \<Longrightarrow> \<not>Stack.isEmpty old"
           apply(induction "(Current extra (List.length extra) old (List.length newS + Stack.size big + Stack.size old))" rule: Current.isEmpty.induct)
           by auto

         with 1 have 3: "5 + (5 * Stack.size old + (4 * List.length extra + (4 * List.length newS + 5 * Stack.size big))) <  11 * Stack.size big + (11 * Stack.size old + (12 * List.length extra + 12 * List.length newS))" 
           by auto

         with 1 show ?case 
           apply(auto simp: max_def split: state_splits)
           subgoal for common
           proof(induction "\<not> Stack.isEmpty old")
             case True
             then have "4 * Common.newSize common <  11 * Stack.size big + (11 * Stack.size old + (12 * List.length extra + 12 * List.length newS))"
               by auto


             with True have " 5 + (5 * Stack.size old + (4 * List.length extra + (4 * List.length newS + 5 * Stack.size big))) < Suc (4 * Common.newSize common)"
               apply auto
               sorry

             with True show ?case
               using 3 apply auto
               sorry
           next
             case False
             then show ?case
               by auto
           qed
           sorry
       qed
    qed

    then have "inSizeWindow (fourTicks ?newTransfomation)"
      using fourTicks_inSizeWindow invariant by blast
    
    with 6 invariant_fourTicks show ?case
      by(auto simp: Let_def split: transformation.split Big.state.split Small.state.split Common.state.split)

  next
    case (7 x left right)
    let ?newLeft = "Big.push x left"
    let ?newTransfomation = "Right ?newLeft right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    from 7 have invariant: "Transformation.invariant ?newTransfomation"
      by (meson RealTimeDeque.invariant.simps Transformation.invariant.simps invariant_push_big)

    then have "Transformation.invariant (fourTicks ?newTransfomation)"
      using invariant_fourTicks by blast
    
    from 7 invariant have "inSizeWindow ?newTransfomation"
      apply auto
      sorry

    then have "inSizeWindow (fourTicks ?newTransfomation)"
      using fourTicks_inSizeWindow invariant by blast
    
    with 7 invariant_fourTicks show ?case
      apply(auto simp: Let_def)
      apply(cases "fourTicks (transformation.Right (Big.push x left) right)")
       apply auto
      sorry
  qed
next
  case (13 q x)
  then show ?case sorry
next
  case (14 q)
  then show ?case
  proof(induction q rule: dequeueLeft'.induct)
    case (1 x)
    then show ?case by auto
  next
    case (2 x y)
    then show ?case by auto
  next
    case (3 x y z)
    then show ?case by auto
  next
    case (4 left right rightLength)
    then show ?case
    proof(induction "Idle.pop left")
      case (Pair x left')
      then show ?case
      proof(induction left')
        case (Idle iLeft iLeftLength)
        then show ?case 
        proof(induction "Stack.size right \<le> 3 * iLeftLength")
          case True
          then show ?case 
            apply(auto split: prod.splits)
               apply (meson Idle.invariant.simps Idle_Proof.invariant_pop)
            apply (metis Idle.invariant.simps Idle_Proof.invariant_pop bot_nat_0.extremum bot_nat_0.not_eq_extremum length_0_conv mult_zero_right not_empty not_empty_2 size_listLength verit_la_disequality)
             apply (metis Idle.size.simps Idle_Proof.size_pop Suc_leD)
            using Idle_Proof.invariant_pop by fastforce
        next
          case False
          then show ?case
          proof(induction "1 \<le> iLeftLength")
            case True
            then show ?case
              apply(auto split: prod.splits)
              sorry
          next
            case False

            then have st: "iLeftLength \<le> 3 *Stack.size right"
              by auto

            from False  have 0: "iLeftLength = 0"
              by auto

            with False have "Idle.size left = 1"
              apply auto
              by (metis Idle.invariant.simps Idle.size.simps Idle_Proof.invariant_pop Idle_Proof.size_pop)

            with False have "rightLength < 4"
              by auto

            with False show ?case
              apply(auto split: prod.splits stack.splits)
              subgoal for x1 x2
                apply(induction x1 x2 rule: toSmallDeque.induct)
                by auto
              done
          qed
        qed
      qed
    qed
  next
    case (5 left right)
    then show ?case
      apply(auto)
      sorry
  next
    case (6 left right)
    then show ?case sorry
  next
    case 7
    then show ?case sorry
  qed
next
  case (15 q)
  then show ?case sorry
next 
  case (16 q)
  then show ?case
  proof(induction q)
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
        apply(auto split: prod.splits)
        by (metis rev_append rev_rev_ident)
      qed
  qed
qed

end
