theory RealTimeDeque_Enqueue
  imports Deque RealTimeDeque States_Proof
begin

lemma helper: "\<lbrakk>\<not> leftLength \<le> 3 * size right; idle.Idle left leftLength = Idle.push x left'; invar left'; rightLength = size right;
     \<not> is_empty left'; \<not> is_empty right; \<not> is_empty left\<rbrakk>
    \<Longrightarrow> size right - (Suc (2 * size right) - size ((Stack.pop ^^ (leftLength - Suc (size right))) left)) = 0"
proof -
  assume a1: "invar left'"
  assume a2: "rightLength = size right"
  assume "idle.Idle left leftLength = Idle.push x left'"
  then have f3: "\<And>n. List.length (drop n (Stack.list left)) = leftLength - n"
    using a1 by (metis (no_types) invar_idle.simps Idle_Proof.invar_push length_drop Stack_Proof.size_list_length)
  moreover
  { assume "\<exists>n. rightLength + (rightLength + 1) - leftLength = rightLength + n"
    moreover
    { assume "\<exists>n. rightLength + (rightLength + 1) - (leftLength - (leftLength - (rightLength + 1))) = rightLength + n"
      then have "rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.list left))) = 0"
        using f3 diff_is_0_eq nat_le_iff_add by presburger }
    ultimately have "leftLength \<le> rightLength + 1 \<longrightarrow> rightLength - (rightLength + (rightLength + 1) - List.length (drop (leftLength - (rightLength + 1)) (Stack.list left))) = 0"
      using diff_zero by fastforce }
  ultimately show ?thesis
    using a2
    by (metis (no_types, lifting) Nat.add_diff_assoc One_nat_def popN_drop add_Suc_right add_diff_cancel_left' diff_cancel2 diff_diff_cancel linear mult_2 plus_1_eq_Suc Stack_Proof.size_list_length)
qed

lemma list_enqL: "invar deque \<Longrightarrow> listL (enqL x deque) = x # listL deque"
proof(induction x deque rule: enqL.induct)
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
        by (metis Idle.list.simps Idle_Proof.push_list)+
    next
      case False
      let ?states = "States Right 
          (Reverse (Current [] 0 left (leftLength - Suc (size right))) left [] (leftLength - Suc (size right)))
          (Reverse1 (Current [] 0 right (Suc (2 * size right))) right [])"

      from False have left_not_empty: "\<not> is_empty left"
      proof(induction x left' rule: Idle.push.induct)
        case (1 x stack stackSize)
        then show ?case
          apply(induction x stack rule: Stack.push.induct)
          by auto
      qed

      from False have invar: "invar ?states"
        apply(auto)
        apply(auto simp: reverseN_take popN_drop left_not_empty)
        apply (metis invar_idle.simps Idle_Proof.invar_push diff_le_self)
        apply (simp add: Stack_Proof.size_list_length)+
        apply (smt (verit) popN_drop append_take_drop_id diff_is_0_eq helper left_not_empty length_rev rev_append rev_rev_ident Stack_Proof.size_list_length take_all_iff)
        by (metis invar_idle.simps Idle_Proof.invar_push add_Suc_right diff_add_inverse)
     
      then have "States.listL ?states = x # Idle.list left' @ rev (Stack.list right)"
        apply(auto simp: reverseN_take)
        by (metis (no_types, lifting) Idle.hyps Idle.list.simps Idle_Proof.push_list append_Cons append_assoc rev_append rev_swap)

      with invar have 
         "States.listL (six_steps ?states) = x # Idle.list left' @ rev (Stack.list right)"
        by (auto simp: n_steps)

      with False show ?case
        by(auto simp: Let_def split: idle.splits)
    qed
  qed
next
  case (6 x big small)
  let ?newSmall = "Small.push x small"
  let ?newStates = "States Left big ?newSmall"
  let ?steppedStates = "four_steps ?newStates"

  from 6 have invar: "invar ?newStates"
    by (meson invar_deque.simps(6) invar_states.simps(1) invar_push_small)

  then have list: "States.listL ?newStates = x # Small.list_current small @ rev (Big.list_current big)"
    by(auto simp: push_small push_list_current)
                        
  from invar have four_steps: "invar ?steppedStates"
    using invar_n_steps by blast

  then have "States.listL ?steppedStates = x # Small.list_current small @ rev (Big.list_current big)"
    using n_steps invar list by fastforce

  with 6 show ?case
    by(auto simp: Let_def split: states.split direction.split Big.state.split Common.state.split Small.state.split)
next
  case (7 x big small)

  let ?newBig = "Big.push x big"
  let ?newStates = "States Right ?newBig small"
  let ?steppedStates = "four_steps ?newStates"

  from 7 have invar: "invar ?newStates"
    by (meson invar_deque.simps invar_states.simps invar_push_big)

  then have "States.listL ?newStates = list_big_first (States Right (Big.push x big) small)"
    by auto

  with invar have listL: "States.listL ?newStates = x # Big.list_current big @ rev (Small.list_current small)"
    apply(auto simp: push_big split: prod.splits)
    by (metis Big_Proof.push_list_current append_Cons rev_append rev_rev_ident)
  
  from invar have four_steps: "invar ?steppedStates"
    using invar_n_steps by blast

  then have "States.listL ?steppedStates = x # Big.list_current big @ rev (Small.list_current small)"
    using n_steps invar listL by fastforce

  with 7 show ?case 
    apply(auto simp: Let_def split: states.split direction.split prod.split Big.state.split Common.state.split Small.state.split)
    by (metis rev_append rev_rev_ident)+
qed


lemma helper2: "\<lbrakk>\<not> leftLength \<le> 3 * size right; idle.Idle left leftLength = Idle.push x left'; invar left'; rightLength = size right;
     \<not> is_empty left'; \<not> is_empty right; \<not> is_empty left\<rbrakk>
    \<Longrightarrow> Suc (List.length (Stack.list right) + size right) - leftLength = 0"
  by(auto simp: size_list_length)

lemma helper3: "\<lbrakk>\<not> leftLength \<le> 3 * size right; idle.Idle left leftLength = Idle.push x left'; invar left'; rightLength = size right;
     \<not> is_empty left'; \<not> is_empty right; \<not> is_empty left\<rbrakk>
    \<Longrightarrow> rev (
            take 
               (Suc (2 * size right) - size ((Stack.pop ^^ (leftLength - Suc (size right))) left))
               (rev (
                      take (leftLength - Suc (size right)) (Stack.list right))
                    )
               ) =
         Stack.list right"
  by(auto simp: rev_take helper2 size_list_length[symmetric] helper)

lemma helper4: "\<lbrakk>
  \<not> leftLength \<le> 3 * size right; 
  idle.Idle left leftLength = Idle.push x left'; 
  invar left'; rightLength = size right;
  \<not> is_empty left'; 
  \<not> is_empty right;
  \<not> is_empty left
\<rbrakk> \<Longrightarrow> reverseN (Suc (2 * size right) - size ((Stack.pop ^^ (leftLength - Suc (size right))) left))
          (reverseN (leftLength - Suc (size right)) (Stack.list right) [])
          (rev (Stack.list ((Stack.pop ^^ (leftLength - Suc (size right))) left))) @
         rev (take (leftLength - Suc (size right)) (Stack.list left)) =
         Stack.list right @ rev (Stack.list left)"
  by (metis (no_types, lifting) popN_drop append_Nil2 append_assoc append_take_drop_id helper3 rev_append reverseN_take)

lemma calculation_helper: "\<lbrakk>
          \<not> l \<le> 3 * r; 
          Suc l' = l;
          0 < l;
          0 < l';
          0 < r;
          l' \<le> 3 * r;
          l + l - Suc (Suc (r + r)) \<le> Suc (l + r)
       \<rbrakk> \<Longrightarrow> Suc (l + r - 4) \<le> 4 * r"
  by auto

lemma remaining_steps_not_idle: "invar states \<Longrightarrow> remaining_steps states > 0 \<longleftrightarrow> (
    case states of 
      States _ (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))  \<Rightarrow> False 
    | _ \<Rightarrow> True) "
  apply(induction states)
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma remaining_steps_idle: "invar (States dir small big) \<Longrightarrow> remaining_steps (States dir small big) = 0 \<longleftrightarrow> (
    case (States dir small big) of 
      States dir (Big.Common (Common.Idle _ _)) (Small.Common (Common.Idle _ _))   \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(auto split: Big.state.splits Small.state.splits Common.state.splits current.splits)

lemma invar_enqL: "invar deque \<Longrightarrow> invar (enqL x deque)"
proof(induction x deque rule: enqL.induct)
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
           apply (metis invar_idle.simps Idle_Proof.invar_push)
          apply (metis size_idle.simps Idle_Proof.size_push Stack_Proof.size_not_empty zero_less_Suc)
         apply (metis invar_idle.simps Idle_Proof.invar_push)
        by (metis size_idle.simps Idle_Proof.size_push diff_is_0_eq' le_diff_conv mult.commute mult_Suc zero_le_numeral)
    next
      case False

      
      let ?newLeftLength = "leftLength - (size right) - 1"
      let ?newRightLength = "Suc (2 * size right)"
      let ?states = "States Right 
          (Reverse (Current [] 0 left ?newLeftLength) left [] ?newLeftLength)
          (Reverse1 (Current [] 0 right ?newRightLength) right [])"

      from False have left_not_empty: "\<not> is_empty left"
        proof(induction x left' rule: Idle.push.induct)
          case (1 x stack stackSize)
          then show ?case
            apply(induction x stack rule: Stack.push.induct)
            by auto
        qed

      from False have leftLength: "leftLength = size left" 
        using Idle_Proof.invar_push[of left' x]
        by(induction left') auto
         
      from False have old_size: "Suc (size left') = leftLength"
        apply auto 
        by (metis size_idle.simps Idle_Proof.size_push leftLength)    

      from False have remaining_steps: "6 < States.remaining_steps ?states"
        apply(auto simp: max_def)
        by (smt (z3) add.commute add_2_eq_Suc' diff_add_inverse2 diff_is_0_eq le_less_Suc_eq length_greater_0_conv leftLength mult_Suc Stack_Proof.size_not_empty not_le not_less_eq numeral_3_eq_3 numeral_Bit0 Stack_Proof.size_list_length old_size)
        
      from False have invar: "invar ?states"
        apply(auto simp: Stack_Proof.size_list_length popN_drop left_not_empty)
           apply (metis invar_idle.simps Idle_Proof.invar_push diff_le_self Stack_Proof.size_list_length)
          apply (simp add: reverseN_take)
        apply (smt (verit, best) popN_drop Suc_leI diff_add_inverse diff_add_inverse2 diff_diff_left helper4 le_eq_less_or_eq left_not_empty length_drop mult_Suc numeral_3_eq_3 plus_1_eq_Suc reverseN_reverseN Stack_Proof.size_list_length old_size)
        by (metis invar_idle.simps Idle_Proof.invar_push add_Suc_right diff_add_inverse Stack_Proof.size_list_length)

      with remaining_steps have "5 < States.remaining_steps (step ?states)"
        using remaining_steps_decline_3[of ?states 5] by auto

      with invar have "4 < States.remaining_steps ((step ^^ 2) ?states)"
        using invar_n_steps invar_step remaining_steps_decline_4[of ?states 4 1]
        by (smt (z3) add.commute add_Suc_right funpow_0 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remaining_steps remaining_steps_decline_4)

      with remaining_steps have remaining_steps_end: "0 < States.remaining_steps (six_steps ?states)"
        using remaining_steps_decline_4[of ?states 5 5] 
        by (smt (z3) One_nat_def Suc_eq_plus1 add_Suc_right invar numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 remaining_steps_decline_4)

 
      from False left_not_empty have size_ok: "size_ok' ?states (remaining_steps ?states - 6)"
        apply(auto simp: max_def old_size leftLength)
        subgoal
          proof(induction "size left + size right \<le> 4")
            case True
            then show ?case
              apply(auto)
              by (smt (z3) add_Suc_shift add_diff_cancel_right' add_leE diff_zero first_pop length_Cons less_Suc_eq_le mult.commute mult_2_right mult_Suc_right not_less_eq numeral_3_eq_3 numeral_Bit0 Stack_Proof.size_list_length)
          next
            case False
            then show ?case
              by auto
          qed
        using old_size leftLength
              Stack_Proof.size_not_empty[of left] 
              Stack_Proof.size_not_empty[of right] 
              size_not_empty[of left'] 
              calculation_helper
        by auto

      then have "size_ok' (six_steps ?states) (remaining_steps (six_steps ?states))"
        using size_ok_steps invar remaining_steps by blast

      then have six_steps_size_ok: "size_ok (six_steps ?states)"
        by (meson size_ok.elims(3))

     from invar have "invar (six_steps ?states)"
       using invar_n_steps by blast

      with False six_steps_size_ok show ?case
        apply(auto simp: Let_def split: idle.splits)
        using remaining_steps_end by simp
     qed
  qed
next
  case (6 x big small)
  let ?newSmall = "Small.push x small"
  let ?newStates = "States Left big ?newSmall"
  let ?steppedStates = "four_steps ?newStates"

  have start_size_ok: "size_ok (States Left big small)"
    using "6.prems" invar_deque.simps(6) by blast

  from 6 have invar: "invar ?newStates"
    by (meson invar_deque.simps(6) invar_states.simps(1) invar_push_small)

  then have invar_four_steps: "invar (four_steps ?newStates)"
    using invar_n_steps by blast

  with 6 show ?case
  proof(induction "remaining_steps (States Left big small) > 4")
    case True
    then have states_invar: "invar (States Left big small)" by auto
    from True have states_rem: "4 \<le> States.remaining_steps (States Left big small)" by auto
    from True have states_size_ok: "States.size_ok (States Left big small)" by auto
    
    from True have "remaining_steps ?newStates > 4"
      by (metis remaining_steps_push_small states_invar)

    then have remaining_steps: "remaining_steps ?steppedStates > 0"
      by (metis One_nat_def add_Suc_shift funpow_0 invar numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remaining_steps_decline_4)

    from True have size_ok: "size_ok ?steppedStates"
      using step_4_push_small_size_ok[of Left big small x] states_invar states_rem states_size_ok 
      by auto

    have "case ?steppedStates of
      States Left (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using step_same[of Left big ?newSmall] remaining_steps_not_idle[of ?steppedStates]
      apply(auto split: direction.splits prod.splits states.splits Small.state.splits Big.state.splits Common.state.splits)
      using remaining_steps by auto

    then have "(case ?steppedStates of 
      States Left 
        (Big.Common (Common.Idle _ big))
        (Small.Common (Common.Idle _ small)) 
         \<Rightarrow> Idle small big
   | _ \<Rightarrow> Transforming ?steppedStates) = Transforming ?steppedStates"
      by(auto split: states.splits direction.splits  Small.state.splits Common.state.splits Big.state.splits)

    with True  have "invar (case ?steppedStates of 
      States Left 
        (Big.Common (Common.Idle _ big))
        (Small.Common (Common.Idle _ small)) 
         \<Rightarrow> Idle small big
   | _ \<Rightarrow> Transforming ?steppedStates)"
      by (smt (z3) invar_deque.simps(6) remaining_steps size_ok) 

    with True show ?case
      by(auto simp: Let_def)

  next
    case False
    then have "remaining_steps ?newStates \<le> 4"
      by (metis invar_deque.simps(6) leI remaining_steps_push_small)

    with False have remaining_steps: "remaining_steps ?steppedStates = 0"
      using invar remaining_steps_decline_5[of ?newStates 4]
      by auto

    obtain steppedSmall steppedBig where stepped: "?steppedStates = States Left steppedBig steppedSmall"
      by (metis(full_types) States.listL.cases step_n_same)

    with remaining_steps have "case States Left steppedBig steppedSmall of
      States Left (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _))  \<Rightarrow> True
    | _ \<Rightarrow> False"   
      using False.prems(2) remaining_steps_idle by fastforce

    then obtain sI smallIdle bI bigIdle where idle: "States Left steppedBig steppedSmall = 
     States Left (Big.state.Common (state.Idle bI bigIdle)) (Small.state.Common (state.Idle sI smallIdle)) "
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have states_invar: "invar (States Left steppedBig steppedSmall)"
      using False
      by (metis stepped)

    with stepped invar_four_steps have "Big.size_new big = Big.size_new steppedBig"
      using invar
      by (metis step_n_size_new_big)

    have small_sizes_1: "size ?newSmall = Suc (size small)"
      by (meson "6.prems" invar_deque.simps(6) invar_states.simps(1) funpow_0 step_n_push_size_small)

    with stepped invar_four_steps have small_sizes: "Small.size_new ?newSmall = Small.size_new steppedSmall"
      using invar
      by (metis step_n_size_new_small)

    then have "0 < Small.size_new small"
      using "6.prems" invar_deque.simps(6) size_ok.simps(1) invar_states.simps(1) size_ok_size_new_small by blast

    then have "0 < Small.size_new ?newSmall"
      using \<open>size (Small.push x small) = Suc (size small)\<close> invar Small_Proof.size_size_new by fastforce

    then have "0 < Small.size_new steppedSmall"
      by (simp add: \<open>Small.size_new (Small.push x small) = Small.size_new steppedSmall\<close>)

    then have "0 < Big.size_new big"
      using "6.prems" invar_deque.simps(6) size_ok.simps(1) invar_states.simps(1) size_ok_size_new_big by blast

    then have big_not_empty: "0 < Big.size_new steppedBig"
      by (simp add: \<open>Big.size_new big = Big.size_new steppedBig\<close>)

    have small_size: "size smallIdle = Small.size_new steppedSmall"
      using idle states_invar by auto

    have big_size: "size bigIdle = Big.size_new steppedBig"
      using idle states_invar by auto

    have wind2: "Small.size_new small \<le> 3 * Big.size_new big - 1"
      using start_size_ok
      by auto

    have "Suc (Small.size_new small) = Small.size_new ?newSmall"
      by (metis "6.prems" invar_deque.simps(6) funpow_0 step_n_push_size_new_small)

    with wind2 have "Small.size_new ?newSmall \<le> 3 * Big.size_new big"
      using \<open>0 < Big.size_new big\<close> by linarith

    then have "Small.size_new steppedSmall \<le> 3 * Big.size_new big"  
      by (simp add: small_sizes)

    then have T: "Small.size_new steppedSmall \<le> 3 * Big.size_new steppedBig"  
      using \<open>Big.size_new big = Big.size_new steppedBig\<close> by presburger

    have "Big.size_new big \<le> 3 * Small.size_new small"
      using start_size_ok small_sizes_1
      by auto

    then have "Big.size_new big \<le> 3 * Small.size_new ?newSmall"
      using small_sizes_1
      by (metis (no_types, opaque_lifting) "6.prems" invar_deque.simps(6) dual_order.trans funpow_0 le_add2 mult_le_mono2 plus_1_eq_Suc step_n_push_size_new_small)

    then have "Big.size_new big \<le> 3 * Small.size_new steppedSmall"
      by (simp add: small_sizes)

    then have "Big.size_new steppedBig \<le> 3 * Small.size_new steppedSmall"
      by (simp add: \<open>Big.size_new big = Big.size_new steppedBig\<close>)
    
    with idle states_invar T have "invar (Idle smallIdle bigIdle)"
      apply auto
      apply (metis Common.size_new.simps(1) is_empty_idle.elims(2) size_idle.simps Small.size_new.simps(1) \<open>0 < Small.size_new (Small.push x small)\<close> \<open>Small.size_new (Small.push x small) = Small.size_new steppedSmall\<close> list.size(3) Stack_Proof.size_list_length Stack_Proof.list_not_empty verit_comp_simplify1(1))
      using big_not_empty Idle_Proof.not_empty by auto
     
     with False have "invar(case States Left steppedBig steppedSmall of 
      States Left 
        (Big.Common (Common.Idle _ big))
        (Small.Common (Common.Idle _ small)) 
         \<Rightarrow> Idle small big
   | _ \<Rightarrow> Transforming (States Left steppedBig steppedSmall))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle states.inject(1) states.simps(5) by auto

     with False show ?case
       by (metis \<open>four_steps (States  Left  big (Small.push x small)) = States Left steppedBig steppedSmall\<close> enqL.simps(6))
   qed
next
  case (7 x big small)
  let ?newBig = "Big.push x big"
  let ?newStates = "States Right ?newBig small"
  let ?steppedStates = "four_steps ?newStates"

  have start_size_ok: "size_ok (States Right big small)"
    using "7.prems" invar_deque.simps(6) by blast

  from 7 have invar: "invar ?newStates"
    by (meson invar_deque.simps(6) invar_states.simps invar_push_big)

  then have invar_four_steps: "invar (four_steps ?newStates)"
    using invar_n_steps by blast

  with 7 show ?case
  proof(induction "remaining_steps (States Right big small) > 4")
    case True
    then have states_invar: "invar (States Right big small)" by auto
    from True have states_rem: "4 \<le> States.remaining_steps (States Right big small)" by auto
    from True have states_size_ok: "States.size_ok (States Right big small)" by auto
    
    from True have "remaining_steps ?newStates > 4"
      by (metis remaining_steps_push_big states_invar)

    then have remaining_steps: "remaining_steps ?steppedStates > 0"
      by (metis One_nat_def add_Suc_shift funpow_0 invar numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc remaining_steps_decline_4)

    from True have size_ok: "size_ok ?steppedStates"
      using step_4_push_big_size_ok[of Right big small x] states_invar states_rem states_size_ok 
      by blast

    have "case ?steppedStates of
      States Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> False
    | _ \<Rightarrow> True"
      using step_same[of Right ?newBig small] remaining_steps_not_idle[of ?steppedStates]
      apply(auto split: prod.splits direction.splits states.splits Small.state.splits Big.state.splits Common.state.splits)
      using remaining_steps by auto

    then have "(case ?steppedStates of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming ?steppedStates) = Transforming ?steppedStates"
      by(auto split: states.splits direction.splits Small.state.splits Common.state.splits Big.state.splits)

    with True  have "invar (case ?steppedStates of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming ?steppedStates)"
      by (smt (z3) invar_deque.simps(6) remaining_steps size_ok) 

    with True show ?case
      by(auto simp: Let_def)

  next
    case False
    then have "remaining_steps ?newStates \<le> 4"
      by (metis invar_deque.simps(6) leI remaining_steps_push_big)

    with False have remaining_steps: "remaining_steps ?steppedStates = 0"
      using invar remaining_steps_decline_5[of ?newStates 4]
      by auto

    obtain steppedBig steppedSmall where stepped: "?steppedStates = States Right steppedBig steppedSmall"
      by (metis(full_types) States.listL.cases step_n_same)

    with remaining_steps have "case States Right steppedBig steppedSmall of
      States Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False"
      using invar_four_steps remaining_steps_idle by auto

    then obtain bI bigIdle sI smallIdle where idle: "States Right steppedBig steppedSmall = 
      States Right (Big.state.Common (state.Idle bI bigIdle)) (Small.state.Common (state.Idle sI smallIdle))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have states_invar: "invar (States Right steppedBig steppedSmall)"
      by (metis False(3) stepped)
      
    with stepped invar_four_steps have "Small.size_new small = Small.size_new steppedSmall"
      by (metis invar step_n_size_new_small)

    have big_sizes_1: "size ?newBig = Suc (size big)"
      using "7.prems" Big_Proof.size_push by fastforce

    with stepped invar_four_steps have big_sizes: "Big.size_new ?newBig = Big.size_new steppedBig"
      by (metis invar step_n_size_new_big)

    then have "0 < Big.size_new big"
     using "7.prems" invar_deque.simps(6) size_ok.simps(1) size_ok_size_new_big
     by fastforce

    then have "0 < Big.size_new ?newBig"
      using \<open>size (Big.push x big) = Suc (size big)\<close> invar Big_Proof.size_size_new by fastforce

    then have "0 < Big.size_new steppedBig"
      by (simp add: \<open>Big.size_new (Big.push x big) = Big.size_new steppedBig\<close>)

    then have "0 < Small.size_new small"
      using "7.prems" invar_deque.simps size_ok.simps size_ok_size_new_small
      by fastforce

    then have small_not_empty: "0 < Small.size_new steppedSmall"
      by (simp add: \<open>Small.size_new small = Small.size_new steppedSmall\<close>)

    have big_size: "size bigIdle = Big.size_new steppedBig"
      using idle states_invar by auto

    have small_size: "size smallIdle = Small.size_new steppedSmall"
      using idle states_invar by auto

    have size_ok_2: "Big.size_new big \<le> 3 * Small.size_new small - 1"
      using start_size_ok
      by auto

    have "Suc (Big.size_new big) = Big.size_new ?newBig"
      using "7.prems" Big_Proof.size_new_push by fastforce

    with size_ok_2 have "Big.size_new ?newBig \<le> 3 * Small.size_new small"
      using \<open>0 < Small.size_new small\<close> by linarith

    then have "Big.size_new steppedBig \<le> 3 * Small.size_new small"  
      by (simp add: big_sizes)

    then have T: "Big.size_new steppedBig \<le> 3 * Small.size_new steppedSmall"  
      using \<open>Small.size_new small = Small.size_new steppedSmall\<close> by presburger

    have "Small.size_new small \<le> 3 * Big.size_new big"
      using start_size_ok big_sizes_1
      by auto

    then have "Small.size_new small \<le> 3 * Big.size_new ?newBig"
      using big_sizes_1
      using \<open>Suc (Big.size_new big) = Big.size_new (Big.push x big)\<close> by linarith

    then have "Small.size_new small \<le> 3 * Big.size_new steppedBig"
      by (simp add: big_sizes)

    then have "Small.size_new steppedSmall \<le> 3 * Big.size_new steppedBig"
      by (simp add: \<open>Small.size_new small = Small.size_new steppedSmall\<close>)
    
    with idle states_invar T have "invar (Idle bigIdle smallIdle)"
      apply auto
      apply (metis is_empty_idle.elims(2) size_idle.simps Stack_Proof.size_empty Suc_neq_Zero \<open>Suc (Big.size_new big) = Big.size_new (Big.push x big)\<close> big_size big_sizes)
      using small_not_empty Idle_Proof.not_empty by auto
     
     with False  have "invar (case States Right steppedBig steppedSmall of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming (States Right steppedBig steppedSmall))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle states.inject(1) states.simps(5) by auto

     with False show ?case
      by (metis enqL.simps(7) stepped)
  qed
qed

end

