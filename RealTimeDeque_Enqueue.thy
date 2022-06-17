theory RealTimeDeque_Enqueue
  imports Deque RealTimeDeque States_Proof
begin

lemma list_enqL: "invar deque \<Longrightarrow> listL (enqL x deque) = x # listL deque"
proof(induction x deque rule: enqL.induct)
  case (5 x left right length_right)

  obtain left' length_left' where pushed [simp]: 
      "Idle.push x left = idle.Idle left' length_left'"
    using is_empty_idle.cases by blast

  then have invar_left': "invar (idle.Idle left' length_left')"
    using Idle_Proof.invar_push[of left x] 5 by auto

  show ?case
  proof(cases "length_left' \<le> 3 * length_right")
    case True
    then show ?thesis 
      using Idle_Proof.push_list[of x left]
      by(auto simp: Let_def)
  next
    case False
    let ?length_left = "length_left' - length_right - 1"
    let ?length_right = "2 * length_right + 1"
    let ?big = "Reverse  (Current [] 0 left' ?length_left) left' [] ?length_left"
    let ?small = "Reverse1 (Current [] 0 right ?length_right) right []"
    let ?states = "States Right ?big ?small"
    let ?states_stepped = "six_steps ?states"

    from False 5 invar_left' have invar: "invar ?states"
      by(auto simp: reverseN_take rev_drop rev_take)

    then have "States.listL ?states = x # Idle.list left @ rev (Stack.list right)"
      using Idle_Proof.push_list[of x left]
      by(auto simp: reverseN_take)

    then have "States.listL ?states_stepped = x # Idle.list left @ rev (Stack.list right)"
      by (metis invar step_n_listL)

    with False show ?thesis 
      by(auto simp: Let_def)
  qed
next
  case (6 x big small)
  let ?small = "Small.push x small"
  let ?states = "States Left big ?small"
  let ?states_stepped = "four_steps ?states"

  obtain big_stepped small_stepped where stepped:
      "?states_stepped = States Left big_stepped small_stepped"
    by (metis remaining_steps_states.cases step_n_same)

  from 6 have "invar ?states"
    using invar_push_small[of Left big small x]
    by auto
                        
  then have 
      "States.listL ?states_stepped = x # Small.list_current small @ rev (Big.list_current big)"
    using step_n_listL by fastforce

  with 6 show ?case
    by(cases big_stepped; cases small_stepped)
      (auto simp: Let_def stepped split!: Common.state.split)
next
  case (7 x big small)

  let ?big = "Big.push x big"
  let ?states = "States Right ?big small"
  let ?states_stepped = "four_steps ?states"

  obtain big_stepped small_stepped where stepped:
      "?states_stepped = States Right big_stepped small_stepped"
    by (metis remaining_steps_states.cases step_n_same)

   from 7 have list_invar:
    "list_current_small_first (States Right big small) = list_small_first (States Right big small)"
    by auto

  from 7 have invar: "invar ?states"
    using invar_push_big[of Right big small x]
    by auto
                        
  then have
      "States.listL ?states = x # Big.list_current big @ rev (Small.list_current small)"
    using app_rev[of _ _ _ "x # Big.list_current big"]
    by(auto split: prod.split)

  then have "
      States.listL ?states_stepped = x # Big.list_current big @ rev (Small.list_current small)"
    by (metis invar step_n_listL)

  with list_invar show ?case
    using app_rev[of "Small.list_current small" "Big.list_current big"]
    by(cases big_stepped; cases small_stepped)   
      (auto simp: Let_def stepped split!: prod.split Common.state.split)
qed auto

lemma invar_enqL: "invar deque \<Longrightarrow> invar (enqL x deque)"
proof(induction x deque rule: enqL.induct)
  case (5 x left right length_right)
  obtain left' length_left' where pushed [simp]: 
      "Idle.push x left = idle.Idle left' length_left'"
    using is_empty_idle.cases by blast

  then have invar_left': "invar (idle.Idle left' length_left')"
    using Idle_Proof.invar_push[of left x] 5 by auto 

  have [simp]: "size left' = Suc (size left)"
    using Idle_Proof.size_push[of x left] 
    by auto 

  show ?case
  proof(cases "length_left' \<le> 3 * length_right")
    case True
    with 5 show ?thesis 
      using invar_left' Idle_Proof.size_push[of x left] Stack_Proof.size_not_empty[of left']
      by auto
  next
    case False
    let ?length_left = "length_left' - length_right - 1"
    let ?length_right = "Suc (2 * length_right)"
    let ?states = "States Right 
          (Reverse (Current [] 0 left' ?length_left) left' [] ?length_left)
          (Reverse1 (Current [] 0 right ?length_right) right [])"
    let ?states_stepped = "six_steps ?states"

    from invar_left' 5 False have invar: "invar ?states" 
      by(auto simp: reverseN_take rev_drop rev_take)

    then have invar_stepped: "invar ?states_stepped"
      using invar_step_n by blast 

    from False invar_left' 5 have remaining_steps: "6 < remaining_steps ?states" 
      using Stack_Proof.size_not_empty[of right]
      by auto

    then have remaining_steps_stepped: "0 < remaining_steps ?states_stepped" 
      using invar remaining_steps_n_steps_sub
      by (metis zero_less_diff)

    from False invar_left' 5 have "size_ok' ?states (remaining_steps ?states - 6)"
      using Stack_Proof.size_not_empty[of right] 
            size_not_empty
      by auto

    then have size_ok_stepped: "size_ok ?states_stepped" 
      using size_ok_steps[of ?states 6] remaining_steps invar
      by blast
   
    from False show ?thesis 
      using invar_stepped remaining_steps_stepped size_ok_stepped
      by(auto simp: Let_def)
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
    using invar_step_n by blast

  with 6 show ?case
  proof(induction "remaining_steps (States Left big small) > 4")
    case True
    then have states_invar: "invar (States Left big small)" by auto
    from True have states_rem: "4 \<le> remaining_steps (States Left big small)" by auto
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
      using step_same[of Left big ?newSmall]
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
      using invar remaining_steps_decline_n_steps[of ?newStates 4]
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

    with stepped invar_four_steps have "size_new big = size_new steppedBig"
      using invar
      by (metis step_n_size_new_big)

    have small_sizes_1: "size ?newSmall = Suc (size small)"
      by (meson "6.prems" invar_deque.simps(6) invar_states.simps(1) funpow_0 step_n_push_size_small)

    with stepped invar_four_steps have small_sizes: "size_new ?newSmall = size_new steppedSmall"
      using invar
      by (metis step_n_size_new_small)

    then have "0 < size_new small"
      using "6.prems" invar_deque.simps(6) invar_states.simps(1) size_ok_size_new_small by blast

    then have "0 < size_new ?newSmall"
      using \<open>size (Small.push x small) = Suc (size small)\<close> invar Small_Proof.size_size_new sorry (* by fastforce *)

    then have "0 < size_new steppedSmall"
      by (simp add: \<open>size_new (Small.push x small) = size_new steppedSmall\<close>)

    then have "0 < size_new big"
      using "6.prems" invar_deque.simps(6) invar_states.simps(1) size_ok_size_new_big by blast

    then have big_not_empty: "0 < size_new steppedBig"
      by (simp add: \<open>size_new big = size_new steppedBig\<close>)

    have small_size: "size smallIdle = size_new steppedSmall"
      using idle states_invar by auto

    have big_size: "size bigIdle = size_new steppedBig"
      using idle states_invar by auto

    have wind2: "size_new small \<le> 3 * size_new big - 1"
      using start_size_ok
      by auto

    have "Suc (size_new small) = size_new ?newSmall"
      by (metis "6.prems" invar_deque.simps(6) funpow_0 step_n_push_size_new_small)

    with wind2 have "size_new ?newSmall \<le> 3 * size_new big"
      using \<open>0 < size_new big\<close> by linarith

    then have "size_new steppedSmall \<le> 3 * size_new big"  
      by (simp add: small_sizes)

    then have T: "size_new steppedSmall \<le> 3 * size_new steppedBig"  
      using \<open>size_new big = size_new steppedBig\<close> by presburger

    have "size_new big \<le> 3 * size_new small"
      using start_size_ok small_sizes_1
      by auto

    then have "size_new big \<le> 3 * size_new ?newSmall"
      using small_sizes_1
      by (metis (no_types, opaque_lifting) "6.prems" invar_deque.simps(6) dual_order.trans funpow_0 le_add2 mult_le_mono2 plus_1_eq_Suc step_n_push_size_new_small)

    then have "size_new big \<le> 3 * size_new steppedSmall"
      by (simp add: small_sizes)

    then have "size_new steppedBig \<le> 3 * size_new steppedSmall"
      by (simp add: \<open>size_new big = size_new steppedBig\<close>)
    
    with idle states_invar T have "invar (Idle smallIdle bigIdle)"
      apply auto
      apply (metis Common.size_new_state.simps(1) is_empty_idle.elims(2) size_idle.simps size_new_state.simps(1) \<open>0 < size_new (Small.push x small)\<close> \<open>size_new (Small.push x small) = size_new steppedSmall\<close> list.size(3) Stack_Proof.size_list_length Stack_Proof.list_not_empty verit_comp_simplify1(1))
      using big_not_empty sorry
     
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
    using invar_step_n by blast

  with 7 show ?case
  proof(induction "remaining_steps (States Right big small) > 4")
    case True
    then have states_invar: "invar (States Right big small)" by auto
    from True have states_rem: "4 \<le> remaining_steps (States Right big small)" by auto
    from True have states_size_ok: "size_ok (States Right big small)" by auto
    
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
      using step_same[of Right ?newBig small] 
      sorry
      (* apply(auto split: prod.splits direction.splits states.splits Small.state.splits Big.state.splits Common.state.splits)
      using remaining_steps by auto *)

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
      using invar remaining_steps_decline_n_steps[of ?newStates 4]
      by auto

    obtain steppedBig steppedSmall where stepped: "?steppedStates = States Right steppedBig steppedSmall"
      by (metis(full_types) States.listL.cases step_n_same)

    with remaining_steps have "case States Right steppedBig steppedSmall of
      States Right (Big.state.Common (state.Idle _ _)) (Small.state.Common (state.Idle _ _)) \<Rightarrow> True
    | _ \<Rightarrow> False"
      using invar_four_steps remaining_steps_idle sorry

    then obtain bI bigIdle sI smallIdle where idle: "States Right steppedBig steppedSmall = 
      States Right (Big.state.Common (state.Idle bI bigIdle)) (Small.state.Common (state.Idle sI smallIdle))"
      by(auto split: Small.state.splits Common.state.splits Big.state.splits)

    then have states_invar: "invar (States Right steppedBig steppedSmall)"
      by (metis False(3) stepped)
      
    with stepped invar_four_steps have "size_new small = size_new steppedSmall"
      by (metis invar step_n_size_new_small)

    have big_sizes_1: "size ?newBig = Suc (size big)"
      using "7.prems" Big_Proof.size_push by fastforce

    with stepped invar_four_steps have big_sizes: "size_new ?newBig = size_new steppedBig"
      by (metis invar step_n_size_new_big)

    then have "0 < size_new big"
     using "7.prems" invar_deque.simps(6) size_ok_size_new_big
     by fastforce

    then have "0 < size_new ?newBig"
      using \<open>size (Big.push x big) = Suc (size big)\<close> invar Big_Proof.size_size_new sorry (* by fastforce *)

    then have "0 < size_new steppedBig"
      by (simp add: \<open>size_new (Big.push x big) = size_new steppedBig\<close>)

    then have "0 < size_new small"
      using "7.prems" invar_deque.simps size_ok_size_new_small
      by fastforce

    then have small_not_empty: "0 < size_new steppedSmall"
      by (simp add: \<open>size_new small = size_new steppedSmall\<close>)

    have big_size: "size bigIdle = size_new steppedBig"
      using idle states_invar by auto

    have small_size: "size smallIdle = size_new steppedSmall"
      using idle states_invar by auto

    have size_ok_2: "size_new big \<le> 3 * size_new small - 1"
      using start_size_ok
      by auto

    have "Suc (size_new big) = size_new ?newBig"
      using "7.prems" Big_Proof.size_new_push by fastforce

    with size_ok_2 have "size_new ?newBig \<le> 3 * size_new small"
      using \<open>0 < size_new small\<close> by linarith

    then have "size_new steppedBig \<le> 3 * size_new small"  
      by (simp add: big_sizes)

    then have T: "size_new steppedBig \<le> 3 * size_new steppedSmall"  
      using \<open>size_new small = size_new steppedSmall\<close> by presburger

    have "size_new small \<le> 3 * size_new big"
      using start_size_ok big_sizes_1
      by auto

    then have "size_new small \<le> 3 * size_new ?newBig"
      using big_sizes_1
      using \<open>Suc (size_new big) = size_new (Big.push x big)\<close> by linarith

    then have "size_new small \<le> 3 * size_new steppedBig"
      by (simp add: big_sizes)

    then have "size_new steppedSmall \<le> 3 * size_new steppedBig"
      by (simp add: \<open>size_new small = size_new steppedSmall\<close>)
    
    with idle states_invar T have "invar (Idle bigIdle smallIdle)"
      apply auto
      apply (metis is_empty_idle.elims(2) size_idle.simps Stack_Proof.size_empty Suc_neq_Zero \<open>Suc (size_new big) = size_new (Big.push x big)\<close> big_size big_sizes)
      using small_not_empty sorry
     
     with False  have "invar (case States Right steppedBig steppedSmall of 
      States Right 
        (Big.Common (Common.Idle _ big)) 
        (Small.Common (Common.Idle _ small)) \<Rightarrow> Idle big small
   | _ \<Rightarrow> Transforming (States Right steppedBig steppedSmall))"
       using Big.state.simps(6) Common.state.simps(6) Small.state.simps(12) idle states.inject(1) states.simps(5) by auto

     with False show ?case
      by (metis enqL.simps(7) stepped)
  qed
qed auto

end

