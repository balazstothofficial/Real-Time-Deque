theory RealTimeDeque_Dequeue
  imports Deque RealTimeDeque Transformation_Proof
begin

lemma maybe: "\<lbrakk>Idle.pop left = (x, idle.Idle left' leftLength'); Idle.invariant left\<rbrakk> \<Longrightarrow>  Stack.toList left' = tl (Idle.toList left)"
  apply(induction left rule: Idle.pop.induct)
  apply auto
  by (metis Stack.isEmpty.elims(2) Stack.pop.simps(1) Stack_Proof.pop_toList toList_isEmpty list.sel(2))

lemma list_dequeueLeft':
    "\<lbrakk>invariant deque; listLeft deque \<noteq> []; dequeueLeft' deque = (x', deque')\<rbrakk> \<Longrightarrow> x' # listLeft deque' = listLeft deque"
  proof(induction deque arbitrary: x' rule: dequeueLeft'.induct)
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
          apply(auto simp: Let_def Stack_Proof.size_listLength)
          apply (metis reverseN_reverseN reverseN_take append_Nil2)
                  apply (metis Idle.invariant.simps Idle_Proof.invariant_pop eq_imp_le le_SucI mult_2 Stack_Proof.size_listLength trans_le_add2)
                 apply(auto simp: reverseN_take)
          subgoal apply(auto simp: popN_drop popN_size)
            by (smt (z3) Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff append_take_drop_id le_refl length_rev mult_2 mult_Suc not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 rev_append rev_rev_ident Stack_Proof.size_listLength take_all_iff trans_le_add2)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_diff_le diff_add_inverse le_add1 mult_2 Stack_Proof.size_listLength)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 Stack_Proof.size_listLength trans_le_add2)
             apply (metis Idle.invariant.simps Idle_Proof.invariant_pop le_SucI le_add1 mult_2 Stack_Proof.size_listLength)
          apply (metis Idle.isEmpty.elims(3) Idle.toList.simps \<open>\<lbrakk>Suc 0 \<le> leftLength'; \<not> List.length (Stack.toList right) \<le> 3 * leftLength'; Idle.pop left = (x', idle.Idle left' leftLength'); Idle.invariant left; x = x'; deque' = Transforming (sixTicks (transformation.Left (Reverse1 (Current [] 0 left' (Suc (2 * leftLength'))) left' []) (Reverse (Current [] 0 right (List.length (Stack.toList right) - Suc leftLength')) right [] (List.length (Stack.toList right) - Suc leftLength')))); rightLength = List.length (Stack.toList right); \<not> Idle.isEmpty left; \<not> Stack.isEmpty right; Idle.size left \<le> 3 * List.length (Stack.toList right); List.length (Stack.toList right) \<le> 3 * Idle.size left; Idle.toList left \<noteq> []\<rbrakk> \<Longrightarrow> rev (take (Suc (2 * leftLength') - List.length (Stack.toList ((Stack.pop ^^ (List.length (Stack.toList right) - Suc leftLength')) right))) (rev (take (List.length (Stack.toList right) - Suc leftLength') (Stack.toList left')))) @ rev (Stack.toList ((Stack.pop ^^ (List.length (Stack.toList right) - Suc leftLength')) right)) @ rev (take (List.length (Stack.toList right) - Suc leftLength') (Stack.toList right)) = Stack.toList left' @ rev (Stack.toList right)\<close> Stack_Proof.toList_isNotEmpty)
          apply (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_diff_le add_diff_cancel_right' le_add2 mult_2 Stack_Proof.size_listLength)
          by (metis Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 Stack_Proof.size_listLength trans_le_add2)

        with True have "toListLeft ?transformation = tl (Idle.toList left) @ rev (Stack.toList right)"
          by(auto simp: maybe)

        with invariant have "toListLeft (sixTicks ?transformation) = tl (Idle.toList left) @ rev (Stack.toList right)"
          by (auto simp: sixTicks)

        with True show ?case apply(auto simp: Let_def invariant_sixTicks tick_toList split: prod.splits)
           apply (metis Idle.toList.simps Idle_Proof.pop_toList maybe)
          by (metis Idle.toList.simps Idle_Proof.pop_toList maybe)

      next
        case False
        obtain right1 right2 where "right = Stack right1 right2"
          using Stack.toList.cases by blast

        with False show ?case 
          apply(induction right1 right2 rule: toSmallDeque.induct)
          apply auto
          apply (metis (mono_tags, lifting) Cons_eq_append_conv Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList le_zero_eq length_0_conv list.sel(3) not_less_eq_eq Stack_Proof.size_listLength)
          apply (metis (mono_tags, lifting) Cons_eq_append_conv Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList le_zero_eq length_0_conv list.sel(3) not_less_eq_eq Stack_Proof.size_listLength)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq Stack_Proof.size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq Stack_Proof.size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq Stack_Proof.size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq Stack_Proof.size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq Stack_Proof.size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq Stack_Proof.size_listLength tl_append2)
          apply (metis (mono_tags, lifting) False.hyps Idle.invariant.simps Idle.toList.simps Idle_Proof.invariant_pop Idle_Proof.pop_toList One_nat_def append_Nil2 append_eq_append_conv2 le_zero_eq length_0_conv list.distinct(1) list.sel(3) not_less_eq_eq same_append_eq Stack_Proof.size_listLength tl_append2)
          using Idle_Proof.invariant_pop Idle_Proof.size_pop by fastforce+
      qed
    qed    
      
  next
    case (5 left right)

    then have start_invariant: "Transformation.invariant (Left left right)"
      by auto

    from 5 have left_invariant: "Small.invariant left"
      by auto
  
    from 5 have leftSize: "0 < Small.size left"
      by auto

    with 5(3) obtain left' where pop: "Small.pop left = (x', left')"
      by(auto simp: Let_def split: prod.splits transformation.splits Small.state.splits Common.state.splits Big.state.splits)

    let ?newTransfomation = "Left left' right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    have invariant: "Transformation.invariant ?newTransfomation"
      using pop  start_invariant leftSize invariant_pop_small_left[of left right x' left']
      by auto

    have "x' # Small.toCurrentList left' = Small.toCurrentList left"
      using left_invariant leftSize pop Small_Proof.pop_toCurrentList[of left x' left'] by auto
      
    then have toList: "x' # toListLeft ?newTransfomation = Small.toCurrentList left @ rev (Big.toCurrentList right)"
      using invariant leftSize Small_Proof.pop_toCurrentList[of left x' left'] 5(1)
      by auto      

    from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
      using invariant_fourTicks by blast

    then have 1: "x' # toListLeft ?tickedTransformation = Small.toCurrentList left @ rev (Big.toCurrentList right)"
      using Transformation_Proof.fourTicks invariant toList by fastforce

    then have 2: "listLeft (dequeueLeft (Transforming (Left left right))) = toListLeft ?tickedTransformation"
      apply(auto simp: Let_def split: prod.splits transformation.splits Small.state.splits)
         apply (simp add: local.pop)+
       apply(auto split: Common.state.splits Big.state.splits)
      by (simp add: local.pop)

    with 1 have 3: "x' # listLeft (dequeueLeft (Transforming (Left left right))) = Small.toCurrentList left @ rev (Big.toCurrentList right)"
      by auto

    with 5(1) have 4: "listLeft (Transforming (Left left right)) = Small.toCurrentList left @ rev (Big.toCurrentList right)"
      by auto

    from 3 4 have "x' # listLeft (dequeueLeft (Transforming (Left left right))) = listLeft (Transforming (Left left right))"
      by auto

    with 5 show ?case by auto
  next
    case (6 left right)
    then have start_invariant: "Transformation.invariant (Right left right)"
      by auto

    from 6 have left_invariant: "Big.invariant left"
      by auto
  
    from 6 have leftSize: "0 < Big.size left"
      by auto

    with 6(3) obtain left' where pop: "Big.pop left = (x', left')"
      by(auto simp: Let_def split: prod.splits transformation.splits Small.state.splits Common.state.splits Big.state.splits)

    let ?newTransfomation = "Right left' right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    have invariant: "Transformation.invariant ?newTransfomation"
      using pop start_invariant leftSize invariant_pop_big_right[of left right x' left']
      by auto

    have "x' # Big.toCurrentList left' = Big.toCurrentList left"
      using left_invariant leftSize pop Big_Proof.pop_toCurrentList[of left x' left'] by auto
      
    then have toList: "x' # toListLeft ?newTransfomation = Big.toCurrentList left @ rev (Small.toCurrentList right)"
      using left_invariant invariant leftSize Big_Proof.pop_toCurrentList[of left x' left'] 6(1)
      by (metis States.toCurrentList.simps Transformation.invariant.simps(2) append_Cons invariant_listBigFirst old.prod.case toCurrentListBigFirst.simps toListLeft.simps(2))

    from invariant have fourTicks: "Transformation.invariant ?tickedTransformation"
      using invariant_fourTicks by blast

    then have 1: "x' # toListLeft ?tickedTransformation = Big.toCurrentList left @ rev (Small.toCurrentList right)"
      using Transformation_Proof.fourTicks invariant toList by fastforce

    then have 2: "listLeft (dequeueLeft (Transforming (Right left right))) = toListLeft ?tickedTransformation"
      apply(auto simp: Let_def split: prod.splits transformation.splits Small.state.splits)
         apply (simp add: local.pop)+
      by(auto split: Common.state.splits Big.state.splits Small.state.splits)

    with 1 have 3: "x' # listLeft (dequeueLeft (Transforming (Right left right))) = Big.toCurrentList left @ rev (Small.toCurrentList right)"
      by auto

    with 6(1) have 4: "listLeft (Transforming (Right left right)) = Big.toCurrentList left @ rev (Small.toCurrentList right)"
      using invariant_listBigFirst by fastforce

    from 3 4 have "x' # listLeft (dequeueLeft (Transforming (Right left right))) = listLeft (Transforming (Right left right))"
      by auto

    with 6 show ?case by auto
  next
    case 7
    then show ?case by auto
  qed

lemma list_dequeueLeft:
    "\<lbrakk>invariant deque; listLeft deque \<noteq> []\<rbrakk> \<Longrightarrow> listLeft (dequeueLeft deque) = tl (listLeft deque)"
  using list_dequeueLeft' apply(auto split: prod.splits)
  by (smt (z3) list.sel(3) list_dequeueLeft')

lemma list_firstLeft:
    "\<lbrakk>invariant deque; listLeft deque \<noteq> []\<rbrakk> \<Longrightarrow> firstLeft deque = hd (listLeft deque)"
  using list_dequeueLeft' apply(auto split: prod.splits)
  by (smt (z3) list.sel(1) list_dequeueLeft')

lemma maybe2: "\<lbrakk>
  \<not> Suc l \<le> 3 * r; 
  l > 0;
  r > 0;
  l \<le> 3 * r;
  r \<le> 3 * l;
  Suc l + Suc l - Suc (Suc (r + r)) \<le> Suc (Suc l + r)
\<rbrakk> \<Longrightarrow> 10 + (9 * r + Suc l) \<le> 12 * (Suc l - Suc r)"
  by auto

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

lemma geficke2:  "States.inSizeWindow ((States.tick ^^ n) (right, Small.push x left)) \<Longrightarrow>
     Transformation.inSizeWindow ((tick ^^ n) (transformation.Left (Small.push x left) right))"
  by (simp add: fixed_5)

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

lemma invariant_dequeueLeft:
    "\<lbrakk>invariant deque; \<not> isEmpty deque\<rbrakk> \<Longrightarrow> invariant (dequeueLeft deque)"
  proof(induction deque rule: dequeueLeft'.induct)
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
            apply (metis Idle.invariant.simps Idle_Proof.invariant_pop bot_nat_0.extremum bot_nat_0.not_eq_extremum length_0_conv mult_zero_right Stack_Proof.toList_isNotEmpty size_isNotEmpty Stack_Proof.size_listLength verit_la_disequality)
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
              apply(auto simp: reverseN_take Stack_Proof.size_listLength)
                 apply (metis Idle.invariant.simps Idle_Proof.invariant_pop le_SucI le_add2 mult_2 Stack_Proof.size_listLength)
              subgoal apply(auto simp: popN_size popN_drop)
                by (smt (z3) Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff append_take_drop_id le_refl length_rev mult_2 mult_Suc not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3 rev_append rev_rev_ident Stack_Proof.size_listLength take_all_iff trans_le_add2)
              apply (metis Idle.invariant.simps Idle_Proof.invariant_pop Suc_diff_le diff_add_inverse diff_le_self mult_2 Stack_Proof.size_listLength)
              by (metis Idle.invariant.simps Idle_Proof.invariant_pop add_Suc_right add_le_imp_le_diff less_Suc_eq_le mult_2 mult_Suc not_le_imp_less numeral_2_eq_2 numeral_3_eq_3 Stack_Proof.size_listLength trans_le_add2)

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
          using remainingStepsDecline_4[of ?transformation 5 5] 
          by (smt (z3) One_nat_def Suc_eq_plus1 add_Suc_right invariant numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remainingStepsDecline_4)
            from True have test: "Stack.size iLeft = iLeftLength"
              apply auto
              by (metis Idle.invariant.simps Idle_Proof.invariant_pop)

            from True have inSizeWindow: "inSizeWindow' ?transformation (remainingSteps ?transformation - 6)"
              apply(auto simp: max_def test)
              apply (smt (z3) Idle.invariant.simps Idle.size.simps Idle_Proof.invariant_pop Idle_Proof.size_pop Suc_eq_plus1 diff_add_inverse2 diff_commute diff_diff_left diff_is_0_eq mult.commute mult_2_right mult_Suc_right numeral_2_eq_2 numeral_3_eq_3)
              by (smt (z3) Idle.size.simps Idle_Proof.size_pop add_2_eq_Suc diff_Suc_diff_eq1 diff_add_inverse diff_commute diff_diff_left diff_is_0_eq le_add1 local.test mult_2 mult_Suc mult_Suc_right numeral_2_eq_2 numeral_3_eq_3)

            then have sizeWindow: "inSizeWindow (sixTicks ?transformation)"
              using sizeWindow_steps invariant remSteps sizeWindow'_sizeWindow by blast
        
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

    have start_sizeWindow: "inSizeWindow (Left left right)"
      using "5.prems" RealTimeDeque.invariant.simps(6) by blast

    from 5 have invariant: "Transformation.invariant ?newTransfomation"
      by (meson RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) invariant_pop_small_left sizeWindow_smallSize t)

    then have invariant_fourTicks: "Transformation.invariant (fourTicks ?newTransfomation)"
      using invariant_fourTicks by blast

    with 5 show ?case
    proof(induction "remainingSteps (Left left right) > 4")
      case True
      then have states_inv: "States.invariant (right, left)" by auto
      from True have states_rem: "4 \<le> States.remainingSteps (right, left)" by auto
      from True have states_window: "States.inSizeWindow (right, left)" by auto
      from True have "0 < Small.size left" by auto

      show ?case 
      proof(induction "remainingSteps ?newTransfomation > 4")
        case True
        with True have "remainingSteps ?newTransfomation > 4" 
          by auto

      then have remSteps: "remainingSteps ?tickedTransformation > 0"
        by (metis One_nat_def add_Suc_shift funpow_0 invariant numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remainingStepsDecline_4)

      from True have sizeWindow: "inSizeWindow ?tickedTransformation"
        using tick4_popSmall_sizeWindow[of right left x] states_inv states_rem states_window geficke2
        by (metis Transformation.remainingSteps.simps(1) \<open>0 < Small.size left\<close> fixed_5 less_imp_le_nat t)

      have "case ?tickedTransformation of
        Left (Small.state.Common (state.Idle _ _)) (Big.state.Common (state.Idle _ _)) \<Rightarrow> False
      | _ \<Rightarrow> True"
        using tick_same_left[of newLeft right] remSteps_idle_5[of ?tickedTransformation]
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
        by (smt (z3) RealTimeDeque.invariant.simps(6) local.invariant_fourTicks remSteps sizeWindow)

      then have "RealTimeDeque.invariant
          (case 
                  (case fourTicks (transformation.Left newLeft right) of
                        Left (Small.state.Common (state.Idle _ left')) (Big.state.Common (state.Idle _ right)) \<Rightarrow> (x, Idle left' right)
                      | _ \<Rightarrow> (x, Transforming ?tickedTransformation)) of
           (x, deque) \<Rightarrow> deque)"
        by(auto split: prod.splits transformation.splits Small.state.splits Big.state.splits Common.state.splits)

      with True show ?case
        apply(auto simp: Let_def split: prod.splits)
        using t by fastforce
      next
        case False
        then have "remainingSteps ?newTransfomation \<le> 4"
        by (metis (no_types, lifting) RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) Transformation.remainingSteps.simps(1) dual_order.trans not_le_imp_less remainingSteps_popSmall sizeWindow_smallSize t)

      with False have remSteps: "remainingSteps ?tickedTransformation = 0"
        using invariant remainingStepsDecline_5[of ?newTransfomation 4]
        by auto

      obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Left tickedLeft tickedRight"
        using tick_same_left_n[of 4 newLeft right]
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
        using \<open>fourTicks (transformation.Left newLeft right) = transformation.Left tickedLeft tickedRight\<close>
        by (metis local.invariant_fourTicks)

      with ticked invariant_fourTicks have "Big.newSize right = Big.newSize tickedRight"
        using invariant tickN_left_newSizeBig by blast

      have leftSizes1: "Suc (Small.newSize newLeft) = Small.newSize left"
        by (metis \<open>0 < Small.size left\<close> funpow_0 tickN_popSmall_newSizeSmall states_inv t)

      with ticked invariant_fourTicks have leftSizes: "Small.newSize newLeft = Small.newSize tickedLeft"
        using invariant tickN_left_newSizeSmall by blast

      have a: "0 < Big.newSize right"
        using sizeWindow_bigNewSize states_window by blast

      have b: "0 < remainingSteps (Left left right)"
        using states_rem by fastforce

      from start_sizeWindow a b have "1 < Small.newSize left"
        by auto

      then have "0 < Small.newSize newLeft" using leftSizes1
        by linarith

      then have leftNotEmpty: "0 < Small.newSize tickedLeft" using leftSizes by auto

      then have "0 < Big.newSize right"
        using "5.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_bigNewSize by blast

      then have rightNotEmpty: "0 < Big.newSize tickedRight"
        by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)

      have leftSize: "Idle.size idleLeft = Small.newSize tickedLeft"
        using idle transformation_invariant by auto

      have rightSize: "Idle.size idleRight = Big.newSize tickedRight"
        using idle transformation_invariant by auto


      have "Small.newSize left \<le> 3 * Big.newSize right" 
        using start_sizeWindow by auto
      

      with leftSizes1 have "Small.newSize newLeft \<le> 3 * Big.newSize right" 
        by auto

      then have T: "Small.newSize tickedLeft \<le> 3 * Big.newSize tickedRight"  
        using \<open>Big.newSize right = Big.newSize tickedRight\<close> leftSizes by presburger

      have idleLeftNotEmpty: "0 < Idle.size idleLeft"
        using leftSize leftNotEmpty by auto

      have minSteps: "0 < States.remainingSteps (right, left)"
        using states_rem by linarith

      have "4 * Big.newSize right + (States.remainingSteps (right, left)) \<le> 12 * Small.newSize left - (3 * States.remainingSteps (right, left)) - 8"
        using start_sizeWindow by auto 

      then have "4 * Big.newSize right + 1 \<le> 12 * Small.newSize left - 3 - 8"
        using minSteps by auto

      then have "4 * Big.newSize right \<le> 12 * Small.newSize left - 12"
        by auto

      then have "Big.newSize right \<le> 3 * Small.newSize left - 3"
        by auto
      
      then have "Big.newSize right \<le> 3 * Small.newSize newLeft"
        using leftSizes1 by auto

      then have "Big.newSize right \<le> 3 * Small.newSize tickedLeft"
        by (simp add: leftSizes)

      then have "Big.newSize tickedRight \<le> 3 * Small.newSize tickedLeft"
        by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)
      
      with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
        apply auto
        using rightNotEmpty Idle_Proof.isNotEmpty apply auto
        using idleLeftNotEmpty by auto
       
       with False  have ticked_invar: "invariant (case Left tickedLeft tickedRight of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Left tickedLeft tickedRight))"
         using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

       have "(case Left tickedLeft tickedRight of
         Left (Small.state.Common (state.Idle _ left)) (Big.state.Common (state.Idle x_ right)) \<Rightarrow> deque.Idle left right
      | _ \<Rightarrow> Transforming (transformation.Left tickedLeft tickedRight)) = Idle idleLeft idleRight"
         by (simp add: idle)

       have "dequeueLeft (Transforming (transformation.Left left right)) = (case ?tickedTransformation of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?tickedTransformation)"
         by(auto simp: t Let_def split: prod.splits transformation.splits Small.state.splits Common.state.splits Big.state.splits)

       with ticked have "dequeueLeft (Transforming (transformation.Left left right)) = (case Left tickedLeft tickedRight of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Left tickedLeft tickedRight))"
        by metis

       with False ticked_invar show ?case
          by auto
      qed
      
    next
      case False
      then have "remainingSteps ?newTransfomation \<le> 4"
        by (metis (no_types, lifting) RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) Transformation.remainingSteps.simps(1) dual_order.trans not_le_imp_less remainingSteps_popSmall sizeWindow_smallSize t)

      with False have remSteps: "remainingSteps ?tickedTransformation = 0"
        using invariant remainingStepsDecline_5[of ?newTransfomation 4]
        by auto

      obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Left tickedLeft tickedRight"
        using tick_same_left_n[of 4 newLeft right]
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
        using \<open>fourTicks (transformation.Left newLeft right) = transformation.Left tickedLeft tickedRight\<close>
        by auto

      with ticked invariant_fourTicks have "Big.newSize right = Big.newSize tickedRight"
        using invariant tickN_left_newSizeBig by blast

      have leftSizes1: "Suc (Small.newSize newLeft) = Small.newSize left"
        by (metis (no_types, lifting) False(2) RealTimeDeque.invariant.simps(6) States.invariant.elims(2) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) case_prodD Small_Proof.newSize_pop sizeWindow_smallNewSize t)

      with ticked invariant_fourTicks have leftSizes: "Small.newSize newLeft = Small.newSize tickedLeft"
        using invariant tickN_left_newSizeSmall by blast

      have a: "0 < Big.newSize right"
        using Transformation.inSizeWindow.simps(1) sizeWindow_bigNewSize start_sizeWindow by blast

      have b: "0 < remainingSteps (Left left right)"
        using False.prems(1) RealTimeDeque.invariant.simps(6) by blast

      from start_sizeWindow a b have "1 < Small.newSize left"
        by auto

      then have "0 < Small.newSize newLeft" using leftSizes1
        by linarith

      then have leftNotEmpty: "0 < Small.newSize tickedLeft" using leftSizes by auto

      then have "0 < Big.newSize right"
        using "5.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_bigNewSize by blast

      then have rightNotEmpty: "0 < Big.newSize tickedRight"
        by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)

      have leftSize: "Idle.size idleLeft = Small.newSize tickedLeft"
        using idle transformation_invariant by auto

      have rightSize: "Idle.size idleRight = Big.newSize tickedRight"
        using idle transformation_invariant by auto


      have "Small.newSize left \<le> 3 * Big.newSize right" 
        using start_sizeWindow by auto
      

      with leftSizes1 have "Small.newSize newLeft \<le> 3 * Big.newSize right" 
        by auto

      then have T: "Small.newSize tickedLeft \<le> 3 * Big.newSize tickedRight"  
        using \<open>Big.newSize right = Big.newSize tickedRight\<close> leftSizes by presburger

      have idleLeftNotEmpty: "0 < Idle.size idleLeft"
        using leftSize leftNotEmpty by auto

      have minSteps: "0 < States.remainingSteps (right, left)"
        using False by auto 

      have "4 * Big.newSize right + (States.remainingSteps (right, left)) \<le> 12 * Small.newSize left - (3 * States.remainingSteps (right, left)) - 8"
        using start_sizeWindow by auto 

      then have "4 * Big.newSize right + 1 \<le> 12 * Small.newSize left - 3 - 8"
        using minSteps by auto

      then have "4 * Big.newSize right \<le> 12 * Small.newSize left - 12"
        by auto

      then have "Big.newSize right \<le> 3 * Small.newSize left - 3"
        by auto
      
      then have "Big.newSize right \<le> 3 * Small.newSize newLeft"
        using leftSizes1 by auto

      then have "Big.newSize right \<le> 3 * Small.newSize tickedLeft"
        by (simp add: leftSizes)

      then have "Big.newSize tickedRight \<le> 3 * Small.newSize tickedLeft"
        by (simp add: \<open>Big.newSize right = Big.newSize tickedRight\<close>)
      
      with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
        apply auto
        using rightNotEmpty Idle_Proof.isNotEmpty apply auto
        using idleLeftNotEmpty by auto
       
       with False  have ticked_invar: "invariant (case Left tickedLeft tickedRight of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Left tickedLeft tickedRight))"
         using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

       have "(case Left tickedLeft tickedRight of
         Left (Small.state.Common (state.Idle _ left)) (Big.state.Common (state.Idle x_ right)) \<Rightarrow> deque.Idle left right
      | _ \<Rightarrow> Transforming (transformation.Left tickedLeft tickedRight)) = Idle idleLeft idleRight"
         by (simp add: idle)

       have "dequeueLeft (Transforming (transformation.Left left right)) = (case ?tickedTransformation of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?tickedTransformation)"
         by(auto simp: t Let_def split: prod.splits transformation.splits Small.state.splits Common.state.splits Big.state.splits)

       with ticked have "dequeueLeft (Transforming (transformation.Left left right)) = (case Left tickedLeft tickedRight of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Left tickedLeft tickedRight))"
        by metis

       with False ticked_invar show ?case
          by auto
     qed
  next
    case (6 left right)
    obtain x newLeft where t: "Big.pop left = (x, newLeft)"
      by fastforce

    let ?newTransfomation = "Right newLeft right"
    let ?tickedTransformation = "fourTicks ?newTransfomation"

    have start_sizeWindow: "inSizeWindow (Right left right)"
      using "6.prems" RealTimeDeque.invariant.simps(6) by blast

    from 6 have invariant: "Transformation.invariant ?newTransfomation"
      by (meson RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(2) invariant_pop_big_right sizeWindow_bigSize t)

    then have invariant_fourTicks: "Transformation.invariant (fourTicks ?newTransfomation)"
      using invariant_fourTicks by blast

    with 6 show ?case
    proof(induction "remainingSteps (Right left right) > 4")
      case True
      then have states_inv: "States.invariant (left, right)" by auto
      from True have states_rem: "4 \<le> States.remainingSteps (left, right)" by auto
      from True have states_window: "States.inSizeWindow (left, right)" by auto
      from True have "0 < Big.size left" by auto

      show ?case 
      proof(induction "remainingSteps ?newTransfomation > 4")
        case True
        with True have "remainingSteps ?newTransfomation > 4" 
          by auto

      then have remSteps: "remainingSteps ?tickedTransformation > 0"
        by (metis One_nat_def add_Suc_shift funpow_0 invariant numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remainingStepsDecline_4)

      from True have sizeWindow: "inSizeWindow ?tickedTransformation"
        using tick4_popBig_sizeWindow[of left right x] states_inv states_rem states_window geficke2
        by (metis Transformation.remainingSteps.simps(2) \<open>0 < Big.size left\<close> fixed_6 less_imp_le t)

      have "case ?tickedTransformation of
        Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
      | _ \<Rightarrow> True"
        using tick_same_right[of newLeft right] remSteps_idle_5[of ?tickedTransformation]
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
        by (smt (z3) RealTimeDeque.invariant.simps local.invariant_fourTicks remSteps sizeWindow)

      then have "RealTimeDeque.invariant
          (case 
                  (case fourTicks (transformation.Right newLeft right) of
                        Right (Big.state.Common (state.Idle _ left')) (Small.state.Common (state.Idle _ right)) \<Rightarrow> (x, Idle left' right)
                      | _ \<Rightarrow> (x, Transforming ?tickedTransformation)) of
           (x, deque) \<Rightarrow> deque)"
        by(auto split: prod.splits transformation.splits  Big.state.splits Small.state.splits Common.state.splits)

      with True show ?case
        apply(auto simp: Let_def split: prod.splits)
        using t by fastforce
      next
        case False
        then have "remainingSteps ?newTransfomation \<le> 4"
        by (metis (no_types, lifting) RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) Transformation.remainingSteps.simps(1) dual_order.trans not_le_imp_less remainingSteps_popSmall sizeWindow_smallSize t)

      with False have remSteps: "remainingSteps ?tickedTransformation = 0"
        using invariant remainingStepsDecline_5[of ?newTransfomation 4]
        by auto

      obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Right tickedLeft tickedRight"
        using tick_same_right_n[of 4 newLeft right]
        by (simp add: case_prod_unfold numeral_Bit0)

      with remSteps have "case Right tickedLeft tickedRight of
        Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
      | _ \<Rightarrow> False" using remSteps_idle_6'[of ] tick_same_right
        using local.invariant_fourTicks by auto

      then obtain l idleLeft r idleRight where idle: "Right tickedLeft tickedRight = 
        Right (Big.state.Common (state.Idle l idleLeft)) (Small.state.Common (state.Idle r idleRight))"
        by(auto split: Small.state.splits Common.state.splits Big.state.splits)

      then have transformation_invariant: "Transformation.invariant (Right tickedLeft tickedRight)"
        using False
        using \<open>fourTicks (transformation.Right newLeft right) = transformation.Right tickedLeft tickedRight\<close>
        by (metis local.invariant_fourTicks)

      with ticked invariant_fourTicks have "Small.newSize right = Small.newSize tickedRight"
        using invariant tickN_right_newSizeSmall by blast

      have leftSizes1: "Suc (Big.newSize newLeft) = Big.newSize left"
        by (metis \<open>0 < Big.size left\<close> funpow_0 tickN_popBig_newSizeBig states_inv t)

      with ticked invariant_fourTicks have leftSizes: "Big.newSize newLeft = Big.newSize tickedLeft"
        using invariant tickN_right_newSizeBig by blast

      have a: "0 < Small.newSize right"
        using sizeWindow_smallNewSize states_window by blast

      have b: "0 < remainingSteps (Right left right)"
        using states_rem by force

      from start_sizeWindow a b have "1 < Big.newSize left"
        by auto

      then have "0 < Big.newSize newLeft" using leftSizes1
        by linarith

      then have leftNotEmpty: "0 < Big.newSize tickedLeft" using leftSizes by auto

      then have "0 < Small.newSize right"
        using "6.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) sizeWindow_smallNewSize 
        using states_window by blast

      then have rightNotEmpty: "0 < Small.newSize tickedRight"
        by (simp add: \<open>Small.newSize right = Small.newSize tickedRight\<close>)

      have leftSize: "Idle.size idleLeft = Big.newSize tickedLeft"
        using idle transformation_invariant by auto

      have rightSize: "Idle.size idleRight = Small.newSize tickedRight"
        using idle transformation_invariant by auto


      have "Big.newSize left \<le> 3 * Small.newSize right" 
        using start_sizeWindow by auto
      

      with leftSizes1 have "Big.newSize newLeft \<le> 3 * Small.newSize right" 
        by auto

      then have T: "Big.newSize tickedLeft \<le> 3 * Small.newSize tickedRight"  
        using \<open>Small.newSize right = Small.newSize tickedRight\<close> leftSizes by presburger

      have idleLeftNotEmpty: "0 < Idle.size idleLeft"
        using leftSize leftNotEmpty by auto

      have minSteps: "0 < States.remainingSteps (left, right)"
        using states_rem by linarith

      have "4 * Small.newSize right + (States.remainingSteps (left, right)) \<le> 12 * Big.newSize left - (3 * States.remainingSteps (left, right)) - 8"
        using start_sizeWindow by auto 

      then have "4 * Small.newSize right + 1 \<le> 12 * Big.newSize left - 3 - 8"
        using minSteps by auto

      then have "4 * Small.newSize right \<le> 12 * Big.newSize left - 12"
        by auto

      then have "Small.newSize right \<le> 3 * Big.newSize left - 3"
        by auto
      
      then have "Small.newSize right \<le> 3 * Big.newSize newLeft"
        using leftSizes1 by auto

      then have "Small.newSize right \<le> 3 * Big.newSize tickedLeft"
        by (simp add: leftSizes)

      then have "Small.newSize tickedRight \<le> 3 * Big.newSize tickedLeft"
        by (simp add: \<open>Small.newSize right = Small.newSize tickedRight\<close>)
      
      with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
        apply auto
        using rightNotEmpty Idle_Proof.isNotEmpty apply auto
        using idleLeftNotEmpty by auto
       
       with False  have ticked_invar: "invariant (case Right tickedLeft tickedRight of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Right tickedLeft tickedRight))"
         using idle by force

       have "(case Right tickedLeft tickedRight of
         Right (Big.state.Common (state.Idle _ left)) (Small.state.Common (state.Idle x_ right)) \<Rightarrow> deque.Idle left right
      | _ \<Rightarrow> Transforming (transformation.Right tickedLeft tickedRight)) = Idle idleLeft idleRight"
         by (simp add: idle)

       have "dequeueLeft (Transforming (transformation.Right left right)) = (case ?tickedTransformation of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?tickedTransformation)"
         by(auto simp: t Let_def split: prod.splits transformation.splits Small.state.splits Common.state.splits Big.state.splits)

       with ticked have "dequeueLeft (Transforming (transformation.Right left right)) = (case Right tickedLeft tickedRight of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Right tickedLeft tickedRight))"
        by metis

      with False ticked_invar show ?case
         by (metis \<open>(case transformation.Right tickedLeft tickedRight of transformation.Left state1 state2 \<Rightarrow> Transforming (transformation.Right tickedLeft tickedRight) | transformation.Right (Reverse current stack list enat) state2 \<Rightarrow> Transforming (transformation.Right tickedLeft tickedRight) | transformation.Right (Big.state.Common (Copy current list1 list2 enat)) state2 \<Rightarrow> Transforming (transformation.Right tickedLeft tickedRight) | transformation.Right (Big.state.Common (state.Idle xa left)) (Small.state.Common (Copy currenta list1 list2 enat)) \<Rightarrow> Transforming (transformation.Right tickedLeft tickedRight) | transformation.Right (Big.state.Common (state.Idle xa left)) (Small.state.Common (state.Idle x_ right)) \<Rightarrow> deque.Idle left right | transformation.Right (Big.state.Common (state.Idle xa left)) _ \<Rightarrow> Transforming (transformation.Right tickedLeft tickedRight)) = deque.Idle idleLeft idleRight\<close> \<open>RealTimeDeque.invariant (deque.Idle idleLeft idleRight)\<close>) 
      qed
      
    next
      case False
      then have "remainingSteps ?newTransfomation \<le> 4"
        by (metis (no_types, lifting) RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps Transformation.invariant.simps Transformation.remainingSteps.simps dual_order.trans not_le_imp_less remainingSteps_popBig sizeWindow_bigSize t)

      with False have remSteps: "remainingSteps ?tickedTransformation = 0"
        using invariant remainingStepsDecline_5[of ?newTransfomation 4]
        by auto

      obtain tickedLeft tickedRight where ticked: "?tickedTransformation = Right tickedLeft tickedRight"
        using tick_same_right_n[of 4 newLeft right]
        by (simp add: case_prod_unfold numeral_Bit0)

      with remSteps have "case Right tickedLeft tickedRight of
        Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
      | _ \<Rightarrow> False" using remSteps_idle_6'[of ] tick_same_right
        using local.invariant_fourTicks by auto

      then obtain l idleLeft r idleRight where idle: "Right tickedLeft tickedRight = 
        Right (Big.state.Common (state.Idle l idleLeft)) (Small.state.Common (state.Idle r idleRight))"
        by(auto split: Small.state.splits Common.state.splits Big.state.splits)

      then have transformation_invariant: "Transformation.invariant (Right tickedLeft tickedRight)"
        using False
        using \<open>fourTicks (transformation.Right newLeft right) = transformation.Right tickedLeft tickedRight\<close>
        by auto

      with ticked invariant_fourTicks have "Small.newSize right = Small.newSize tickedRight" 
        using invariant tickN_right_newSizeSmall by blast

      have leftSizes1: "Suc (Big.newSize newLeft) = Big.newSize left"
        by (metis (no_types, lifting) False(2) RealTimeDeque.invariant.simps(6) States.invariant.elims(2) Transformation.inSizeWindow.simps Transformation.invariant.simps case_prodD Big_Proof.newSize_pop sizeWindow_bigNewSize t)

      with ticked invariant_fourTicks have leftSizes: "Big.newSize newLeft = Big.newSize tickedLeft"
        using invariant tickN_right_newSizeBig by blast

      have a: "0 < Small.newSize right"
        using Transformation.inSizeWindow.simps(2) sizeWindow_smallNewSize start_sizeWindow by blast

      have b: "0 < remainingSteps (Right left right)"
        using False.prems(1) RealTimeDeque.invariant.simps(6) by blast

      from start_sizeWindow a b have "1 < Big.newSize left"
        by auto

      then have "0 < Big.newSize newLeft" using leftSizes1
        by linarith

      then have leftNotEmpty: "0 < Big.newSize tickedLeft" using leftSizes by auto

      then have "0 < Small.newSize right"
        using "6.prems" RealTimeDeque.invariant.simps(6) Transformation.inSizeWindow.simps Transformation.invariant.simps sizeWindow_smallNewSize by blast

      then have rightNotEmpty: "0 < Small.newSize tickedRight"
        by (simp add: \<open>Small.newSize right = Small.newSize tickedRight\<close>)

      have leftSize: "Idle.size idleLeft = Big.newSize tickedLeft"
        using idle transformation_invariant by auto

      have rightSize: "Idle.size idleRight = Small.newSize tickedRight"
        using idle transformation_invariant by auto

      have "Big.newSize left \<le> 3 * Small.newSize right" 
        using start_sizeWindow by auto

      with leftSizes1 have "Big.newSize newLeft \<le> 3 * Small.newSize right" 
        by auto

      then have T: "Big.newSize tickedLeft \<le> 3 * Small.newSize tickedRight"  
        using \<open>Small.newSize right = Small.newSize tickedRight\<close> leftSizes by presburger

      have idleLeftNotEmpty: "0 < Idle.size idleLeft"
        using leftSize leftNotEmpty by auto

      have minSteps: "0 < States.remainingSteps (left, right)"
        using False by auto 

      have "4 * Small.newSize right + (States.remainingSteps (left, right)) \<le> 12 * Big.newSize left - (3 * States.remainingSteps (left, right)) - 8"
        using start_sizeWindow by auto 

      then have "4 * Small.newSize right + 1 \<le> 12 * Big.newSize left - 3 - 8"
        using minSteps by auto

      then have "4 * Small.newSize right \<le> 12 * Big.newSize left - 12"
        by auto

      then have "Small.newSize right \<le> 3 * Big.newSize left - 3"
        by auto
      
      then have "Small.newSize right \<le> 3 * Big.newSize newLeft"
        using leftSizes1 by auto

      then have "Small.newSize right \<le> 3 * Big.newSize tickedLeft"
        by (simp add: leftSizes)

      then have "Small.newSize tickedRight \<le> 3 * Big.newSize tickedLeft"
        by (simp add: \<open>Small.newSize right = Small.newSize tickedRight\<close>)
      
      with idle transformation_invariant T have "invariant (Idle idleLeft idleRight)"
        apply auto
        using rightNotEmpty Idle_Proof.isNotEmpty apply auto
        using idleLeftNotEmpty by auto
       
       with False  have ticked_invar: "invariant (case Right tickedLeft tickedRight of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Right tickedLeft tickedRight))"
         using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle transformation.inject(1) transformation.simps(5) by auto

       have "(case Right tickedLeft tickedRight of
         Right (Big.state.Common (state.Idle _ left)) (Small.state.Common (state.Idle x_ right)) \<Rightarrow> deque.Idle left right
      | _ \<Rightarrow> Transforming (transformation.Right tickedLeft tickedRight)) = Idle idleLeft idleRight"
         by (simp add: idle)

       have "dequeueLeft (Transforming (transformation.Right left right)) = (case ?tickedTransformation of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming ?tickedTransformation)"
         by(auto simp: t Let_def split: prod.splits transformation.splits Small.state.splits Common.state.splits Big.state.splits)

       with ticked have "dequeueLeft (Transforming (transformation.Right left right)) = (case Right tickedLeft tickedRight of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming (Right tickedLeft tickedRight))"
        by metis

       with False ticked_invar show ?case
          by auto
     qed
  next
    case 7
    then show ?case by auto
  qed

end
