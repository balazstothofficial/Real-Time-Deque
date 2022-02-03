theory RealTimeDeque_Proof
  imports Deque RealTimeDeque Transformation_Proof
begin


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
    using a2 helper_2
    by (metis (no_types, lifting) Nat.add_diff_assoc One_nat_def States_Proof.helper add_Suc_right add_diff_cancel_left' diff_cancel2 diff_diff_cancel linear mult_2 plus_1_eq_Suc size_listLength)
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
  by (metis append_take_drop_id helper_1_2 rev_append)
  

lemma helper_1: "\<lbrakk>
  \<not> leftLength \<le> 3 * Stack.size right; 
  idle.Idle left leftLength = Idle.push x left'; 
  Idle.invariant left'; rightLength = Stack.size right;
  \<not> Idle.isEmpty left'; 
  \<not> Stack.isEmpty right;
   \<not> Stack.isEmpty left
\<rbrakk> \<Longrightarrow> reverseN (Suc (2 * Stack.size right) - Stack.size ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))
          (reverseN (leftLength - Suc (Stack.size right)) (Stack.toList right) [])
          (rev (Stack.toList ((Stack.pop ^^ (leftLength - Suc (Stack.size right))) left))) @
         rev (take (leftLength - Suc (Stack.size right)) (Stack.toList left)) =
         Stack.toList right @ rev (Stack.toList left)"
  by (metis (no_types, lifting) States_Proof.helper append_Nil2 append_assoc append_take_drop_id helper_1_2 rev_append reverseN_take)
 
lemma helper: "\<lbrakk>
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
          by (metis Idle.toList.simps Idle_Proof.push_toList)+
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
          apply(auto simp: reverseN_take helper leftNotEmpty)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_push diff_le_self)
          apply (simp add: size_listLength)+
          apply (smt (verit) States_Proof.helper append_take_drop_id diff_is_0_eq helper_1_4 leftNotEmpty length_rev rev_append rev_rev_ident size_listLength take_all_iff)
          by (metis Idle.invariant.simps Idle_Proof.invariant_push add_Suc_right diff_add_inverse)
       
        then have "toListLeft ?transformation = x # Idle.toList left' @ rev (Stack.toList right)"
          apply(auto simp: reverseN_take)
          by (metis (no_types, lifting) Idle.hyps Idle.toList.simps Idle_Proof.push_toList append_Cons append_assoc rev_append rev_swap)

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
    sorry

  with 1 have "listRight (swap (enqueueLeft x (swap q))) = x # listRight q"
    by (simp add: swap)

  then have "listRight (enqueueRight x q) = x # listRight q"
    by simp

  with 1 show ?thesis
    by simp
qed


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

lemma fixed: "States.inSizeWindow (big, small) \<Longrightarrow> inSizeWindow (Left small big)"
  by auto

lemma fixed_2: "States.inSizeWindow (big, small) \<Longrightarrow> inSizeWindow (Right big small)"
  by auto

lemma fixed_3: "States.inSizeWindow (States.tick (big, small)) \<Longrightarrow> inSizeWindow (tick (Left small big))"
  by(auto split: prod.splits)

lemma fixed_4: "States.inSizeWindow (States.tick (big, small)) \<Longrightarrow> inSizeWindow (tick (Right big small))"
  by(auto split: prod.splits)

lemma fixed_5: "States.inSizeWindow ((States.tick ^^ n) (big, small)) \<Longrightarrow> inSizeWindow ((tick ^^ n) (Left small big))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma fixed_6: "States.inSizeWindow ((States.tick ^^ n) (big, small)) \<Longrightarrow> inSizeWindow ((tick ^^ n) (Right big small))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (simp add: case_prod_unfold funpow_swap1)
qed

lemma geficke: "States.inSizeWindow ((States.tick) (right, Small.push x left)) \<Longrightarrow>
        Transformation.inSizeWindow (tick (transformation.Left (Small.push x left) right))"
   by (smt (z3) Transformation.inSizeWindow.simps(1) Transformation.tick.simps(1) case_prod_unfold prod.exhaust_sel)

lemma geficke2:  "States.inSizeWindow ((States.tick ^^ n) (right, Small.push x left)) \<Longrightarrow>
     Transformation.inSizeWindow ((tick ^^ n) (transformation.Left (Small.push x left) right))"
  by (simp add: fixed_5)

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

lemma remSteps_idle_5: "Transformation.invariant transformation \<Longrightarrow> remainingSteps transformation > 0 \<longleftrightarrow> (
    case transformation of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> False 
    | Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> False 
    | _ \<Rightarrow> True) "
  apply(induction transformation)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remSteps_idle_6: "Transformation.invariant (Left small big) \<Longrightarrow> remainingSteps (Left small big) = 0 \<longleftrightarrow> (
    case (Left small big) of 
      Left (Small.Common (Common.Idle _ _)) (Big.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remSteps_idle_6': "Transformation.invariant (Right big small) \<Longrightarrow> remainingSteps (Right big small) = 0 \<longleftrightarrow> (
    case (Right big small) of 
      Right (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma tick_same_left: "case tick (Left small big) of Left _ _ \<Rightarrow> True | _ \<Rightarrow> False"
  by(auto split: prod.splits)

lemma tick_same_left_n: "case (tick ^^ n) (Left small big) of Left _ _ \<Rightarrow> True | _ \<Rightarrow> False"
proof(induction n arbitrary: small big)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (metis (no_types, lifting) Transformation.tick.simps(1) comp_def funpow_Suc_right prod.case_eq_if) 
qed


lemma tick_same_right: "case tick (Right big small) of Right _ _ \<Rightarrow> True | _ \<Rightarrow> False"
  by(auto split: prod.splits)

lemma tick_same_right_n: "case (tick ^^ n) (Right big small) of Right _ _ \<Rightarrow> True | _ \<Rightarrow> False"
proof(induction n arbitrary: small big)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    by (metis (no_types, lifting) Transformation.tick.simps(2) comp_def funpow_Suc_right prod.case_eq_if) 
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
    sorry
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
        apply (metis Idle.toList.simps Idle_Proof.pop_toList list.sel(3))
        by (metis Idle.toList.simps Idle_Proof.pop_toList list.distinct(1) list.sel(3) tl_append2)
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
          apply (metis reverseN_reverseN reverseN_take append_Nil2)
                  apply (metis Idle.invariant.simps Idle_Proof.invariant_pop eq_imp_le le_SucI mult_2 size_listLength trans_le_add2)
                 apply(auto simp: reverseN_take)
          subgoal apply(auto simp: States_Proof.helper States_Proof.helper_2)
            by (smt (z3) Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff append_take_drop_id le_refl length_rev mult_2 mult_Suc not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 rev_append rev_rev_ident size_listLength take_all_iff trans_le_add2)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_diff_le diff_add_inverse le_add1 mult_2 size_listLength)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 size_listLength trans_le_add2)
             apply (metis Idle.invariant.simps Idle_Proof.invariant_pop le_SucI le_add1 mult_2 size_listLength)
          apply (metis Idle_Proof.pop_toList \<open>\<lbrakk>Suc 0 \<le> leftLength'; \<not> List.length (Stack.toList right) \<le> 3 * leftLength'; Idle.pop left = (x, idle.Idle left' leftLength'); Idle.invariant left; rightLength = List.length (Stack.toList right); \<not> Idle.isEmpty left; \<not> Stack.isEmpty right; Idle.size left \<le> 3 * List.length (Stack.toList right); List.length (Stack.toList right) \<le> 3 * Idle.size left; Idle.toList left \<noteq> []\<rbrakk> \<Longrightarrow> rev (take (Suc (2 * leftLength') - List.length (Stack.toList ((Stack.pop ^^ (List.length (Stack.toList right) - Suc leftLength')) right))) (rev (take (List.length (Stack.toList right) - Suc leftLength') (Stack.toList left')))) @ rev (Stack.toList ((Stack.pop ^^ (List.length (Stack.toList right) - Suc leftLength')) right)) @ rev (take (List.length (Stack.toList right) - Suc leftLength') (Stack.toList right)) = Stack.toList left' @ rev (Stack.toList right)\<close> list.distinct(1))
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_diff_le add_diff_cancel_right' le_add2 mult_2 size_listLength)
          by (metis Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 size_listLength trans_le_add2)

        with True have "toListLeft ?transformation = tl (Idle.toList left) @ rev (Stack.toList right)"
          by(auto simp: maybe)

        with invariant have "toListLeft (sixTicks ?transformation) = tl (Idle.toList left) @ rev (Stack.toList right)"
          by (auto simp: sixTicks)

        with True show ?case apply(auto simp: Let_def invariant_sixTicks tick_toList split: prod.splits)
          by (metis Idle_Proof.pop_toList list.discI tl_append2)

      next
        case False
        obtain right1 right2 where "right = Stack right1 right2"
          using Stack.toList.cases by blast

        with False show ?case 
          apply(induction right1 right2 rule: toSmallDeque.induct)
          apply auto
          apply (metis (mono_tags, lifting) Cons_eq_append_conv Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList le_zero_eq length_0_conv list.sel(3) not_less_eq_eq size_listLength)
          apply (metis (mono_tags, lifting) Cons_eq_append_conv Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList le_zero_eq length_0_conv list.sel(3) not_less_eq_eq size_listLength)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq size_listLength tl_append2)
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

      with Pair invariant_pop_small_left_2 have invariant: "Transformation.invariant ?newTransfomation"
        by (metis RealTimeDeque.invariant.simps(6))
     
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
     proof(induction "Big.pop left")
       case (Pair x left')
       let ?newTransfomation = "Right left' right"
       let ?tickedTransformation = "fourTicks ?newTransfomation"

       from Pair have size: "0 < Big.size left"
          by auto

        with Pair invariant_pop_big_right_2 have invariant: "Transformation.invariant ?newTransfomation"
          by (metis RealTimeDeque.invariant.simps(6))

        then have toList: "toListLeft ?newTransfomation = tl (Big.toCurrentList left) @ rev (Small.toCurrentList right)"
          apply(auto)
          using size Big_Proof.currentList_pop_2[of left x left']
          by (smt (z3) Pair.hyps Pair.prems(1) RealTimeDeque.invariant.simps(6) States.invariant.elims(2) States.toCurrentList.simps Transformation.invariant.simps(2) invariant_pop_big_size_2_1 old.prod.case toCurrentListBigFirst.simps toListBigFirst.simps)

      from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
        using invariant_fourTicks by blast

      then have 1: "toListLeft ?tickedTransformation = tl (Big.toCurrentList left) @ rev (Small.toCurrentList right)"
        using Transformation_Proof.fourTicks invariant toList by fastforce

       then have 2: "listLeft (dequeueLeft (Transforming (Right left right))) = toListLeft ?tickedTransformation"
        apply(auto simp: Let_def split: prod.splits transformation.splits Small.state.splits)
        using Pair.hyps apply fastforce+
        apply(auto split: Common.state.splits  Small.state.splits Big.state.splits prod.splits)
        using Pair.hyps by auto
                             
      with Pair show ?case 
        apply(auto simp: 1 Let_def split: prod.split transformation.split Small.state.split Common.state.split Big.state.split)
        by (metis Big_Proof.currentList_empty_2 rev_append rev_rev_ident size tl_append2)+
     qed
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
      by (metis Idle_Proof.pop_toList list.discI surj_pair)
  next
    case (Transforming x)
    then show ?case 
      apply(induction x)
      apply auto
      using Small_Proof.currentList_empty_2 apply force
      apply(auto simp: max_def split: prod.splits Big.state.splits Small.state.splits if_splits)
      subgoal 
        by (simp add: Nat.diff_diff_right diff_is_0_eq' list.size(3) min.absorb1 minus_nat.diff_0 mult_is_0 not_numeral_le_zero numeral_2_eq_2 size_listLength split: current.splits)
      subgoal by(auto split!: current.splits)
      subgoal by(auto split: current.splits)
      subgoal by(auto split: current.splits)
      apply (metis Common_Proof.currentList_empty_2 Suc_le_lessD less_nat_zero_code mult.commute mult_0 neq0_conv)
      by (metis Common_Proof.currentList_empty_2 Suc_le_lessD less_nat_zero_code mult.commute mult_0 neq0_conv)
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
            apply (simp add: reverseN_take)
          apply (metis reverseN_reverseN helper_1 leftNotEmpty size_listLength)
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

        have dummy_2: "\<lbrakk>
          \<not> Stack.size left \<le> 3 * Stack.size right;
          idle.Idle left (Stack.size left) = Idle.push x left';
          \<not> Stack.isEmpty left;
          Idle.invariant left';
          rightLength = Stack.size right;
          \<not> Idle.isEmpty left';
          \<not> Stack.isEmpty right; 
          Idle.size left' \<le> 3 * Stack.size right;
          Stack.size left + Stack.size left - Suc (Suc (Stack.size right + Stack.size right)) \<le> Suc (Stack.size left + Stack.size right);
          leftLength = Stack.size left; 
          Suc (Idle.size left') = Stack.size left
        \<rbrakk> \<Longrightarrow> Suc (Stack.size left + Stack.size right - 4) \<le> 4 * Stack.size right"
          by (smt (verit, best) Suc_diff_le add.commute add_Suc add_Suc_shift diff_is_0_eq le_add2 le_antisym le_diff_conv mult_Suc not_le not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 plus_1_eq_Suc size_isNotEmpty)

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
          using local.test suc
             apply(auto simp: min_def) 
          subgoal using dummy_2 by auto
          using \<open>\<lbrakk>\<not> Stack.size left \<le> 3 * Stack.size right; idle.Idle left (Stack.size left) = Idle.push x left'; \<not> Stack.isEmpty left; Idle.invariant left'; rightLength = Stack.size right; \<not> Idle.isEmpty left'; \<not> Stack.isEmpty right; Idle.size left' \<le> 3 * Stack.size right; Stack.size left + Stack.size left - Suc (Suc (Stack.size right + Stack.size right)) \<le> Suc (Stack.size left + Stack.size right); leftLength = Stack.size left; Suc (Idle.size left') = Stack.size left\<rbrakk> \<Longrightarrow> Suc (Stack.size left + Stack.size right - 4) \<le> 4 * Stack.size right\<close> by linarith
        

        then have "inSizeWindow' (sixTicks ?transformation) (remainingSteps (sixTicks ?transformation))"
          using sizeWindow_steps  invariant remSteps unfolding sixTicks_def by blast

        then have sixTicks_inSizeWindow: "inSizeWindow (sixTicks ?transformation)"
          using sizeWindow'_sizeWindow
          using sixTicks_inSizeWindow inSizeWindow by blast

       from invariant have "Transformation.invariant (sixTicks ?transformation)"
         using invariant_sixTicks by blast

        with False sixTicks_inSizeWindow show ?case
          apply(auto simp: Let_def split: idle.splits)
          using remStepsEnd by simp
       qed
    qed
  next
    case (6 x left right)
    let ?newLeft = "Small.push x left"
    let ?newTransfomation = "Left ?newLeft right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    have start_sizeWindow: "inSizeWindow (Left left right)"
      using "6.prems" RealTimeDeque.invariant.simps(6) by blast

    from 6 have invariant: "Transformation.invariant ?newTransfomation"
      by (meson RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) invariant_push_small)

    then have invariant_fourTicks: "Transformation.invariant (fourTicks ?newTransfomation)"
      using invariant_fourTicks by blast

    with 6 show ?case
    proof(induction "remainingSteps (Left left right) > 4")
      case True
      then have states_inv: "States.invariant (right, left)" by auto
      from True have states_rem: "4 \<le> States.remainingSteps (right, left)" by auto
      from True have states_window: "States.inSizeWindow (right, left)" by auto
      
      from True have "remainingSteps ?newTransfomation > 4"
        by (metis Transformation.remainingSteps.simps(1) same_d states_inv)

      then have remSteps: "remainingSteps ?tickedTransformation > 0"
        by (metis One_nat_def add_Suc_shift fourTicks_def funpow_0 invariant numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remainingStepsDecline_4)

      from True have sizeWindow: "inSizeWindow ?tickedTransformation"
        using same[of right left x] states_inv states_rem states_window geficke2 unfolding fourTicks_def by auto

      have "case ?tickedTransformation of
        Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> False
      | _ \<Rightarrow> True"
        using tick_same_left[of ?newLeft right] remSteps_idle_5[of ?tickedTransformation]
        apply(auto split: prod.splits transformation.splits Small.state.splits Big.state.splits Common.state.splits)
        using remSteps by auto

      then have "(case ?tickedTransformation of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?tickedTransformation) = Transforming ?tickedTransformation"
        by(auto split: transformation.splits Small.state.splits Common.state.splits Big.state.splits)

      with True  have "invariant (case ?tickedTransformation of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?tickedTransformation)"
        by (smt (z3) RealTimeDeque.invariant.simps(6) remSteps sizeWindow) 

      with True show ?case
        by(auto simp: Let_def)

    next
      case False
      then have "remainingSteps ?newTransfomation \<le> 4"
        by (metis RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) Transformation.remainingSteps.simps(1) leI same_d)

      with False have remSteps: "remainingSteps ?tickedTransformation = 0"
        unfolding fourTicks_def using invariant remainingStepsDecline_5[of ?newTransfomation 4]
        by auto

      obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Left tickedLeft tickedRight"
        unfolding fourTicks_def using tick_same_left_n[of 4 ?newLeft right]
        by (simp add: case_prod_unfold numeral_Bit0)

      with remSteps have "case Left tickedLeft tickedRight of
        Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> True
      | _ \<Rightarrow> False" using remSteps_idle_6[of ] tick_same_left
        using local.invariant_fourTicks by auto

      then obtain l idleLeft r idleRight where idle: "Left tickedLeft tickedRight = 
        Left (Small.state.Common (state.Idle l idleLeft)) (Big.state.Common (state.Idle r idleRight))"
        by(auto split: Small.state.splits Common.state.splits Big.state.splits)

      then have transformation_invariant: "Transformation.invariant (Left tickedLeft tickedRight)"
        using False
        using \<open>fourTicks (transformation.Left (Small.push x left) right) = transformation.Left tickedLeft tickedRight\<close>
        by auto

      with ticked invariant_fourTicks have "Big.newSize right = Big.newSize tickedRight"
        unfolding fourTicks_def 
        using invariant size_tick_n_6 by blast

      have leftSizes1: "Small.size ?newLeft = Suc (Small.size left)"
        by (meson "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) funpow_0 same_c)

      with ticked invariant_fourTicks have leftSizes: "Small.newSize ?newLeft = Small.newSize tickedLeft"
        unfolding fourTicks_def 
        using invariant size_tick_n_2 by blast

      then have "0 < Small.newSize left"
        using "6.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_smallNewSize by blast

      then have "0 < Small.newSize ?newLeft"
        using \<open>Small.size (Small.push x left) = Suc (Small.size left)\<close> invariant sizes_small by fastforce

      then have "0 < Small.newSize tickedLeft"
        by (simp add: \<open>Small.newSize (Small.push x left) = Small.newSize tickedLeft\<close>)

      then have "0 < Big.newSize right"
        using "6.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_bigNewSize by blast

      then have rightNotEmpty: "0 < Big.newSize tickedRight"
        by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)

      have leftSize: "Idle.size idleLeft = Small.newSize tickedLeft"
        using idle transformation_invariant by auto

      have rightSize: "Idle.size idleRight = Big.newSize tickedRight"
        using idle transformation_invariant by auto

      have wind2: "Small.newSize left \<le> 3 * Big.newSize right - 1"
        using start_sizeWindow
        by auto

      have "Suc (Small.newSize left) = Small.newSize ?newLeft"
        by (metis "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) funpow_0 same_c_2)

      with wind2 have "Small.newSize ?newLeft \<le> 3 * Big.newSize right"
        using \<open>0 < Big.newSize right\<close> by linarith

      then have "Small.newSize tickedLeft \<le> 3 * Big.newSize right"  
        by (simp add: leftSizes)

      then have T: "Small.newSize tickedLeft \<le> 3 * Big.newSize tickedRight"  
        using \<open>Big.newSize right = Big.newSize tickedRight\<close> by presburger

      have "Big.newSize right \<le> 3 * Small.newSize left"
        using start_sizeWindow leftSizes1
        by auto

      then have "Big.newSize right \<le> 3 * Small.newSize ?newLeft"
        using leftSizes1
        by (metis (no_types, hide_lams) "6.prems" RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(1) dual_order.trans funpow_0 le_add2 mult_le_mono2 plus_1_eq_Suc same_c_2)

      then have "Big.newSize right \<le> 3 * Small.newSize tickedLeft"
        by (simp add: leftSizes)

      then have "Big.newSize tickedRight \<le> 3 * Small.newSize tickedLeft"
        by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)
      
      with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
        apply auto
        apply (metis Common.newSize.simps(1) Idle.isEmpty.elims(2) Idle.size.simps Small.newSize.simps(1) \<open>0 < Small.newSize (Small.push x left)\<close> \<open>Small.newSize (Small.push x left) = Small.newSize tickedLeft\<close> list.size(3) size_listLength toList_isNotEmpty verit_comp_simplify1(1))
        using rightNotEmpty Idle_Proof.isNotEmpty by auto
       
       with False  have "invariant (case Left tickedLeft tickedRight of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Left tickedLeft tickedRight))"
         using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

       with False show ?case
         by (metis \<open>fourTicks (transformation.Left (Small.push x left) right) = transformation.Left tickedLeft tickedRight\<close> enqueueLeft.simps(6))
     qed
  next
    case (7 x left right)
    let ?newLeft = "Big.push x left"
    let ?newTransfomation = "Right ?newLeft right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    have start_sizeWindow: "inSizeWindow (Right left right)"
      using "7.prems" RealTimeDeque.invariant.simps(6) by blast

    from 7 have invariant: "Transformation.invariant ?newTransfomation"
      by (meson RealTimeDeque.invariant.simps(6) Transformation.invariant.simps invariant_push_big)

    then have invariant_fourTicks: "Transformation.invariant (fourTicks ?newTransfomation)"
      using invariant_fourTicks by blast

    with 7 show ?case
    proof(induction "remainingSteps (Right left right) > 4")
      case True
      then have states_inv: "States.invariant (left, right)" by auto
      from True have states_rem: "4 \<le> States.remainingSteps (left, right)" by auto
      from True have states_window: "States.inSizeWindow (left, right)" by auto
      
      from True have "remainingSteps ?newTransfomation > 4"
        by (metis Transformation.remainingSteps.simps(2) same_d2 states_inv)

      then have remSteps: "remainingSteps ?tickedTransformation > 0"
        by (metis One_nat_def add_Suc_shift fourTicks_def funpow_0 invariant numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remainingStepsDecline_4)

      from True have sizeWindow: "inSizeWindow ?tickedTransformation"
        using same2[of left right x] states_inv states_rem states_window geficke2 unfolding fourTicks_def
        using fixed_6 by blast

      have "case ?tickedTransformation of
        Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
      | _ \<Rightarrow> True"
        using tick_same_right[of ?newLeft right] remSteps_idle_5[of ?tickedTransformation]
        apply(auto split: prod.splits transformation.splits Small.state.splits Big.state.splits Common.state.splits)
        using remSteps by auto

      then have "(case ?tickedTransformation of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?tickedTransformation) = Transforming ?tickedTransformation"
        by(auto split: transformation.splits Small.state.splits Common.state.splits Big.state.splits)

      with True  have "invariant (case ?tickedTransformation of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?tickedTransformation)"
        by (smt (z3) RealTimeDeque.invariant.simps(6) remSteps sizeWindow) 

      with True show ?case
        by(auto simp: Let_def)

    next
      case False
      then have "remainingSteps ?newTransfomation \<le> 4"
        by (metis RealTimeDeque.invariant.simps(6) Transformation.invariant.simps(2) Transformation.remainingSteps.simps(2) leI same_d2)

      with False have remSteps: "remainingSteps ?tickedTransformation = 0"
        unfolding fourTicks_def using invariant remainingStepsDecline_5[of ?newTransfomation 4]
        by auto

      obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Right tickedLeft tickedRight"
        unfolding fourTicks_def using tick_same_right_n[of 4 ?newLeft right]
        by (simp add: case_prod_unfold numeral_Bit0)

      with remSteps have "case Right tickedLeft tickedRight of
        Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
      | _ \<Rightarrow> False" using remSteps_idle_6' tick_same_right
        using local.invariant_fourTicks by auto

      then obtain l idleLeft r idleRight where idle: "Right tickedLeft tickedRight = 
        Right (Big.state.Common (state.Idle l idleLeft)) (Small.state.Common (state.Idle r idleRight))"
        by(auto split: Small.state.splits Common.state.splits Big.state.splits)

      then have transformation_invariant: "Transformation.invariant (Right tickedLeft tickedRight)"
        using False
        using \<open>fourTicks (transformation.Right (Big.push x left) right) = transformation.Right tickedLeft tickedRight\<close>
        by auto

      with ticked invariant_fourTicks have "Small.newSize right = Small.newSize tickedRight"
        unfolding fourTicks_def 
        using invariant size_tick_n_4 by blast

      have leftSizes1: "Big.size ?newLeft = Suc (Big.size left)"
        using "7.prems" push_size_big by fastforce

      with ticked invariant_fourTicks have leftSizes: "Big.newSize ?newLeft = Big.newSize tickedLeft"
        unfolding fourTicks_def 
        using invariant size_tick_n_8 by blast

      then have "0 < Big.newSize left"
       using "7.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_bigNewSize
       by fastforce

      then have "0 < Big.newSize ?newLeft"
        using \<open>Big.size (Big.push x left) = Suc (Big.size left)\<close> invariant sizes_big by fastforce

      then have "0 < Big.newSize tickedLeft"
        by (simp add: \<open>Big.newSize (Big.push x left) = Big.newSize tickedLeft\<close>)

      then have "0 < Small.newSize right"
        using "7.prems" RealTimeDeque.invariant.simps Transformation.inSizeWindow.simps Transformation.invariant.simps sizeWindow_smallNewSize 
        by fastforce

      then have rightNotEmpty: "0 < Small.newSize tickedRight"
        by (simp add: \<open>Small.newSize right = Small.newSize tickedRight\<close>)

      have leftSize: "Idle.size idleLeft = Big.newSize tickedLeft"
        using idle transformation_invariant by auto

      have rightSize: "Idle.size idleRight = Small.newSize tickedRight"
        using idle transformation_invariant by auto

      have wind2: "Big.newSize left \<le> 3 * Small.newSize right - 1"
        using start_sizeWindow
        by auto

      have "Suc (Big.newSize left) = Big.newSize ?newLeft"
        using "7.prems" push_newSize_big by fastforce

      with wind2 have "Big.newSize ?newLeft \<le> 3 * Small.newSize right"
        using \<open>0 < Small.newSize right\<close> by linarith

      then have "Big.newSize tickedLeft \<le> 3 * Small.newSize right"  
        by (simp add: leftSizes)

      then have T: "Big.newSize tickedLeft \<le> 3 * Small.newSize tickedRight"  
        using \<open>Small.newSize right = Small.newSize tickedRight\<close> by presburger

      have "Small.newSize right \<le> 3 * Big.newSize left"
        using start_sizeWindow leftSizes1
        by auto

      then have "Small.newSize right \<le> 3 * Big.newSize ?newLeft"
        using leftSizes1
        using \<open>Suc (Big.newSize left) = Big.newSize (Big.push x left)\<close> by linarith

      then have "Small.newSize right \<le> 3 * Big.newSize tickedLeft"
        by (simp add: leftSizes)

      then have "Small.newSize tickedRight \<le> 3 * Big.newSize tickedLeft"
        by (simp add: \<open>Small.newSize right = Small.newSize tickedRight\<close>)
      
      with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
        apply auto
        apply (metis Idle.isEmpty.elims(2) Idle.size.simps Stack_Proof.size_isEmpty Suc_neq_Zero \<open>Suc (Big.newSize left) = Big.newSize (Big.push x left)\<close> leftSize leftSizes)
        using rightNotEmpty Idle_Proof.isNotEmpty by auto
       
       with False  have "invariant (case Right tickedLeft tickedRight of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Right tickedLeft tickedRight))"
         using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

       with False show ?case
        by (metis enqueueLeft.simps(7) ticked)
    qed
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
              apply(auto simp: reverseN_take size_listLength)
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
      by (metis RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.remainingSteps.simps(1) Transformation_Proof.invariant_pop_small_left_2 sizeWindow_smallSize)

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
        unfolding fourTicks_def 
        using same2[of right left] geficke3[of left x newLeft 4 right] unfolding fourTicks_def by auto


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
