theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Transformation_Proof
begin


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
  by (smt (verit, ccfv_SIG) Idle.size.simps Idle_Proof.size_push toList_isEmpty helper_1 length_greater_0_conv less_Suc_eq_0_disj size_listLength)

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

          apply (smt (z3) Idle.invariant.simps Idle.size.simps Idle_Proof.invariant_push Idle_Proof.size_push Nat.add_diff_assoc One_nat_def Suc_eq_plus1_left Suc_leI Suc_n_not_le_n add_Suc_right add_diff_cancel_left' add_diff_cancel_right' append.assoc diff_Suc_eq_diff_pred le_eq_less_or_eq length_drop length_greater_0_conv length_rev mult_2 mult_Suc not_le_imp_less numeral_3_eq_3 pop_drop rev_rev_ident self_append_conv2 size_listLength test)        
          by (metis Idle.invariant.simps Idle_Proof.invariant_push add_Suc_right diff_add_inverse)
       
        then have "toListLeft ?transformation = x # Idle.toList left' @ rev (Stack.toList right)"
          apply(auto simp: revN_take)
          by (metis (no_types, lifting) Idle.hyps Idle.toList.simps Idle_Proof.push append_Cons append_assoc rev_append rev_swap)

        with invariant have 
           "toListLeft (sixTicks ?transformation) = x # Idle.toList left' @ rev (Stack.toList right)"
          by (auto simp: sixTicks)

        with False show ?case
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
  by (metis Stack.isEmpty.elims(2) Stack.pop.simps(1) Stack_Proof.pop_toList toList_isEmpty list.sel(2))

lemma maybe2: "\<lbrakk>
  \<not> Suc l \<le> 3 * r; 
  l > 0;
  r > 0;
  l \<le> 3 * r;
  r \<le> 3 * l;
  Suc l + Suc l - Suc (Suc (r + r)) \<le> Suc (Suc l + r)
\<rbrakk> \<Longrightarrow> 10 + (9 * r + Suc l) \<le> 12 * (Suc l - Suc r)"
  by auto

lemma geficke: "States.inSizeWindow ((States.tick) (right, Small.push x left)) \<Longrightarrow>
        Transformation.inSizeWindow (tick (transformation.Left (Small.push x left) right))"
   by (smt (z3) Transformation.inSizeWindow.simps(1) Transformation.tick.simps(1) case_prod_unfold prod.exhaust_sel)

lemma geficke2:  "States.inSizeWindow ((States.tick ^^ n) (right, Small.push x left)) \<Longrightarrow>
     Transformation.inSizeWindow ((tick ^^ n) (transformation.Left (Small.push x left) right))"
  apply(induction n arbitrary: right x left)
   using geficke  apply(auto split: prod.splits)
 
   sorry

lemma geficke3:  "Small.pop small =(x, small') \<Longrightarrow> States.inSizeWindow ((States.tick ^^ n) (right, small')) \<Longrightarrow>
     Transformation.inSizeWindow ((tick ^^ n) (transformation.Left small' right))"
  sorry

(*lemma why: "\<lbrakk>
  \<not> leftLength \<le> 3 * Stack.size right; 
  idle.Idle left leftLength = Idle.push x left'; 
  Idle.invariant left'; 
  rightLength = Stack.size right;
  \<not> Idle.isEmpty left'; 
  \<not> Stack.isEmpty right; 
  Idle.size left' \<le> 3 * Stack.size right;
 Stack.size right \<le> 3 * Idle.size left'
\<rbrakk> \<Longrightarrow> False"
proof(induction x left' rule: Idle.push.induct)
  case (1 x stack stackSize)
  then show ?case apply auto
    sorry
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
          subgoal 
            by (smt (verit, ccfv_SIG) Idle.invariant.simps Idle_Proof.invariant_pop add_diff_cancel_left' diff_Suc_Suc le_add_diff_inverse2 le_cases3 le_diff_conv length_drop length_rev mult_2 mult_Suc not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 pop_drop rev_rev_ident size_listLength take_all_iff test trans_le_add2)
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
          apply (metis (mono_tags, lifting) Cons_eq_append_conv Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop le_zero_eq length_0_conv list.sel(3) not_less_eq_eq size_listLength)
          apply (metis (mono_tags, lifting) Cons_eq_append_conv Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop le_zero_eq length_0_conv list.sel(3) not_less_eq_eq size_listLength)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          using Idle_Proof.invariant_pop Idle_Proof.size_pop by fastforce+
      qed
    qed    
      
  next
    case (5 left right)
    then show ?case 
    proof(induction "Small.pop left")
      case (Pair x left')
      let ?newTransfomation = "Left left' right"
      let ?tickedTransformation = "fourTicks ?newTransfomation"

      from Pair have size: "0 < Small.size left"
        by auto

      with Pair invariant_pop_small_2[of left right x left'] have invariant: "Transformation.invariant ?newTransfomation"
        by auto
     
      then have toList: "toListLeft ?newTransfomation = tl (Small.toCurrentList left) @ rev (Big.toCurrentList right)"
        apply(auto)
        using size Small_Proof.currentList_pop_2[of left x left']
        using Pair.hyps Pair.prems(1) by auto

      from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
        using invariant_fourTicks by blast

      then have 1: "toListLeft ?tickedTransformation = tl (Small.toCurrentList left) @ rev (Big.toCurrentList right)"
        using Transformation_Proof.fourTicks invariant toList by fastforce

      then have 2: "listLeft (dequeueLeft (Transforming (Left left right))) = toListLeft ?tickedTransformation"
        apply(auto simp: Let_def split: prod.splits transformation.splits Small.state.splits)
        using Pair.hyps apply fastforce+
         apply(auto split: Common.state.splits Big.state.splits)
        using Pair.hyps by fastforce+
                             
      with Pair show ?case 
        apply(auto simp: 1 Let_def split: prod.split transformation.split Small.state.split Common.state.split Big.state.split)
        by (metis Small_Proof.currentList_empty_2 size tl_append2)
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
      apply auto
      using Small_Proof.currentList_empty_2 apply force
      apply(auto simp: max_def split: prod.splits Big.state.splits Small.state.splits if_splits)
      subgoal apply(auto simp: revN_take split: current.splits) 
        by (metis bot_nat_0.extremum list.size(3) mult_is_0 not_less_eq_eq size_listLength)
      subgoal apply(auto simp:  split: current.splits)
        by (simp add: size_listLength) 
      subgoal by(auto split: current.splits)
      subgoal by(auto split: current.splits)
      apply (meson Common_Proof.currentList_empty_2 less_le_trans nat_0_less_mult_iff)
      by (metis Common_Proof.currentList_empty_2 Nat.add_0_right le_add2 le_antisym mult_0_right neq0_conv)
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
            apply (metis Idle.size.simps Idle_Proof.size_push size_isNotEmpty zero_less_Suc)
           apply (metis Idle.invariant.simps Idle_Proof.invariant_push)
          by (metis Idle.size.simps Idle_Proof.size_push diff_is_0_eq' le_diff_conv mult.commute mult_Suc zero_le_numeral)
      next
        case False
        let ?newLeftLength = "leftLength - (Stack.size right) - 1"
        let ?newRightLength = "Suc (2 * Stack.size right)"
        let ?transformation = "(Right 
            (Reverse (Current [] 0 left ?newLeftLength) left [] ?newLeftLength)
            (Reverse1 (Current [] 0 right ?newRightLength) right []))"

        from False have leftNotEmpty: "\<not> Stack.isEmpty left"
          proof(induction x left' rule: Idle.push.induct)
            case (1 x stack stackSize)
            then show ?case
              apply(induction x stack rule: Stack.push.induct)
              by auto
          qed


          from False have "0 < leftLength"
            by auto

        from False have notEmpty: "\<not>Transformation.isEmpty ?transformation"
          apply(auto simp:)
          using leftNotEmpty apply fastforce
          by (metis Idle.invariant.simps Idle_Proof.invariant_push diff_is_0_eq funpow_0 helper_1_3 helper_1_4 leftNotEmpty length_greater_0_conv mult_2 size_isNotEmpty not_le size_listLength)

        from False have test: "leftLength = Stack.size left" 
          apply auto
          by (metis Idle.invariant.simps Idle_Proof.invariant_push)

        from False have suc: "Suc (Idle.size left') = leftLength"
          apply auto 
          by (metis Idle.size.simps Idle_Proof.size_push local.test)    

        from False have remSteps: "6 < Transformation.remainingSteps ?transformation"
          apply(auto simp: max_def)
          by (smt (z3) add.commute add_2_eq_Suc' diff_add_inverse2 diff_is_0_eq le_less_Suc_eq length_greater_0_conv local.test mult_Suc size_isNotEmpty not_le not_less_eq numeral_3_eq_3 numeral_Bit0 size_listLength suc)
          
        
        from False have invariant: "Transformation.invariant ?transformation"
          apply(auto simp: size_listLength helper leftNotEmpty)
             apply (metis Idle.invariant.simps Idle_Proof.invariant_push diff_le_self size_listLength)
            apply (simp add: RealTimeDeque_Proof.revN_take)
          apply (metis RealTimeDeque_Proof.revN_revN helper_1 leftNotEmpty size_listLength)
          by (metis Idle.invariant.simps Idle_Proof.invariant_push add_Suc_right diff_add_inverse size_listLength)

        with remSteps have "5 < Transformation.remainingSteps (tick ?transformation)"
          using remainingStepsDecline_3[of ?transformation 5] by auto

        with invariant have "4 < Transformation.remainingSteps ((tick ^^ 2) ?transformation)"
          using invariant_nTicks invariant_tick remainingStepsDecline_4[of ?transformation 4 1]
          by (smt (z3) add.commute add_Suc_right funpow_0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remSteps remainingStepsDecline_4)

        with remSteps have remStepsEnd: "0 < Transformation.remainingSteps (sixTicks ?transformation)"
          unfolding sixTicks_def using remainingStepsDecline_4[of ?transformation 5 5] 
          by (smt (z3) One_nat_def Suc_eq_plus1 add_Suc_right invariant numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remainingStepsDecline_4)

        from False leftNotEmpty have " Stack.size right \<le> 3 * Idle.size left'"
          by auto

        have dummy: "4 + 8 * Stack.size right \<le> 12 * (Stack.size left - Suc (Stack.size right)) \<longleftrightarrow>
              16 + 20 * Stack.size right \<le> 12 * Stack.size left"
          by auto

        from False leftNotEmpty have inSizeWindow: "inSizeWindow' ?transformation (remainingSteps ?transformation - 6)"
          apply(auto simp: test max_def suc)
          subgoal using local.test suc 
          proof(induction "Stack.size left + Stack.size right \<le> 4")
            case True
            then show ?case
              apply(auto simp: dummy)
              by (smt (z3) add_Suc_shift add_diff_cancel_right' add_leE diff_zero first_pop length_Cons less_Suc_eq_le mult.commute mult_2_right mult_Suc_right not_less_eq numeral_3_eq_3 numeral_Bit0 size_listLength)
          next
            case False
            then show ?case
              by auto
          qed
          using local.test suc by linarith+

        then have "inSizeWindow' (sixTicks ?transformation) (remainingSteps (sixTicks ?transformation))"
          using sizeWindow_steps  invariant remSteps unfolding sixTicks_def by blast

        then have sixTicks_inSizeWindow: "inSizeWindow (sixTicks ?transformation)"
          using sizeWindow'_sizeWindow
          using sixTicks_inSizeWindow inSizeWindow by blast

        from notEmpty invariant have sixTicks_notEmpty: "\<not>Transformation.isEmpty (sixTicks ?transformation)"
         using sixTicks_not_empty by blast

       from invariant have "Transformation.invariant (sixTicks ?transformation)"
         using invariant_sixTicks by blast

        with False sixTicks_inSizeWindow sixTicks_notEmpty show ?case
          apply(auto simp: Let_def split: idle.splits)
          using remStepsEnd by simp
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

    
    with 6 invariant_fourTicks show ?case
    proof(induction "remainingSteps (Left left right) \<ge> 4")
      case True
      then have states_inv: "States.invariant (right, left)" by auto
      from True have states_rem: "4 \<le> States.remainingSteps (right, left)" by auto
      from True have states_window: "States.inSizeWindow (right, left)" by auto
      


      with True have "inSizeWindow ?tickedTransformation"
        using same[of right left x] states_inv states_rem states_window geficke2 unfolding fourTicks_def by auto

      with True show ?case
        apply(auto simp: Let_def split: transformation.splits)
        sorry
    next
      case False
      then show ?case sorry
    qed

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
            apply (metis Idle.invariant.simps Idle_Proof.invariant_pop bot_nat_0.extremum bot_nat_0.not_eq_extremum length_0_conv mult_zero_right toList_isNotEmpty size_isNotEmpty size_listLength verit_la_disequality)
             apply (metis Idle.size.simps Idle_Proof.size_pop Suc_leD)
            using Idle_Proof.invariant_pop by fastforce
        next
          case False
          then show ?case
          proof(induction "1 \<le> iLeftLength")
            case True
            let ?transformation = "transformation.Left (Reverse1 (Current [] 0 iLeft (Suc (2 * iLeftLength))) iLeft [])
              (Reverse (Current [] 0 right (Stack.size right - Suc iLeftLength)) right [] (Stack.size right - Suc iLeftLength))"

            from True have invariant: "Transformation.invariant ?transformation"
              apply(auto simp: revN_take size_listLength)
                 apply (metis Idle.invariant.simps Idle_Proof.invariant_pop le_SucI le_add2 mult_2 size_listLength)
              subgoal sorry (* just times out *)
              apply (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_diff_le diff_add_inverse diff_le_self mult_2 size_listLength)
              by (metis Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 size_listLength trans_le_add2)

            then have invariant_six: "Transformation.invariant (sixTicks ?transformation)"
              using invariant_sixTicks by blast

          

          from True have remSteps: "6 < Transformation.remainingSteps ?transformation"
            by(auto simp: max_def)

         with invariant have "5 < Transformation.remainingSteps (tick ?transformation)"
          using remainingStepsDecline_3[of ?transformation 5] by auto

        with invariant have "4 < Transformation.remainingSteps ((tick ^^ 2) ?transformation)"
          using invariant_nTicks invariant_tick remainingStepsDecline_4[of ?transformation 4 1]
          by (smt (z3) add.commute add_Suc_right funpow_0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remSteps remainingStepsDecline_4)

        with remSteps have remStepsEnd: "0 < Transformation.remainingSteps (sixTicks ?transformation)"
          unfolding sixTicks_def using remainingStepsDecline_4[of ?transformation 5 5] 
          by (smt (z3) One_nat_def Suc_eq_plus1 add_Suc_right invariant numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remainingStepsDecline_4)
            from True have test: "Stack.size iLeft = iLeftLength"
              apply auto
              by (metis Idle.invariant.simps Idle_Proof.invariant_pop)

            from True have inSizeWindow: "inSizeWindow' ?transformation (remainingSteps ?transformation - 6)"
              apply(auto simp: max_def test)
              apply (smt (z3) Idle.invariant.simps Idle.size.simps Idle_Proof.invariant_pop Idle_Proof.size_pop Suc_eq_plus1 diff_add_inverse2 diff_commute diff_diff_left diff_is_0_eq mult.commute mult_2_right mult_Suc_right numeral_2_eq_2 numeral_3_eq_3)
              by (smt (z3) Idle.size.simps Idle_Proof.size_pop add_2_eq_Suc diff_Suc_diff_eq1 diff_add_inverse diff_commute diff_diff_left diff_is_0_eq le_add1 local.test mult_2 mult_Suc mult_Suc_right numeral_2_eq_2 numeral_3_eq_3)

            then have sizeWindow: "inSizeWindow (sixTicks ?transformation)"
              using sizeWindow_steps invariant remSteps sizeWindow'_sizeWindow unfolding sixTicks_def by blast

            from True have "\<not> Transformation.isEmpty ?transformation"
              apply auto
              by (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_le_lessD size_isNotEmpty)

            then have "\<not> Transformation.isEmpty (sixTicks ?transformation)"
              using invariant sixTicks_not_empty by blast
        
            with True invariant_six sizeWindow show ?case
              by(auto simp: Let_def remStepsEnd split: prod.splits)
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
    obtain x newLeft where t: "Small.pop left = (x, newLeft)"
      by fastforce

    let ?newTransfomation = "Left newLeft right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    from 5 t have invariant: "Transformation.invariant ?newTransfomation"
      by (metis RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.remainingSteps.simps(1) Transformation_Proof.invariant_pop_small_2 sizeWindow_smallSize)

    then have invariant_fourTicks: "Transformation.invariant (fourTicks ?newTransfomation)"
      using invariant_fourTicks by blast

    from 5 show ?case
    proof(induction "remainingSteps (Left left right) > 4")
      case True
      then have inv: "States.invariant (right, left)"
        by auto
      from True have steps: "4 \<le> States.remainingSteps (right, left)" 
        by auto
       from True have window: "States.inSizeWindow (right, left)" 
        by auto

      from True inv steps t window have newWindow: "inSizeWindow (fourTicks ?newTransfomation)" 
        using same_2[of right left x newLeft] geficke3[of left x newLeft 4 right] unfolding fourTicks_def by auto


      with invariant_fourTicks show ?case 
        apply(auto simp: Let_def split: prod.splits transformation.splits)
        subgoal sorry
                  apply (simp add: t)
        using t apply auto
        sorry
    next
      case False
      then show ?case 
        sorry
    qed
  next
    case (6 left right)
    then show ?case sorry
  next
    case 7
    then show ?case by auto
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
