theory States_Proof
  imports States Big_Proof Small_Proof HOL.Real Complex_Main
begin

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits
lemmas invariant_ticks = Big_Proof.invariant_tick Common_Proof.invariant_tick Small_Proof.invariant_tick

lemma invariant_listBigFirst: "invariant states \<Longrightarrow> toListBigFirst states = toCurrentListBigFirst states"
  apply(auto split: prod.splits)
  by (metis rev_append rev_rev_ident)

lemma tick_toList: "invariant states \<Longrightarrow> toList (tick states) = toList states"
proof(induction states)
  case (Pair big small)
  then show ?case
 proof(induction small)
    case (Reverse1 currentS small auxS)

 
    from Reverse1 show ?case 
    proof(induction big)
      case (Reverse currentB big aux count)

      then have "Big.invariant (Reverse currentB big aux count)"
        by auto
      then have big: "Big.toList (Big.tick (Reverse currentB big aux count)) = Big.toList (Reverse currentB big aux count)"
        by(simp add: Big_Proof.tick_toList)

      from Reverse have "Small.invariant (Reverse1 currentS small auxS)"
        by auto

      from Reverse show ?case
      proof(induction "(Reverse currentB big aux count, Reverse1 currentS small auxS)" rule: States.tick.induct)
        case 1
        then show ?case 
          by (auto split: current.splits)
      next
        case ("2_1" n)
        then show ?case
        proof(induction "States.tick (Reverse currentB big aux count, Reverse1 currentS small auxS)" rule: toList.induct)
          case (1 currentB' big' auxB' count' currentS' small' auxS')
          then show ?case 
            apply(auto split: current.splits)

            using big apply(auto)
            apply (metis empty funpow_swap1 revN.elims revN.simps(2))
            by (metis first_pop funpow_swap1 revN.simps(3))
        next
          case ("2_1" v small)
          then show ?case by auto
        next
          case ("2_2" big v va vb vc vd)
          then show ?case by auto
        next
          case ("2_3" big v)
          then show ?case by auto
        qed
      qed
    next
      case (Common x)
      then show ?case by auto
    qed
  next
    case (Reverse2 x1 x2 x3a x4 x5)
    then show ?case 
      apply(auto simp: Big_Proof.tick_toList Common_Proof.tick_toList split: current.splits)
      using empty apply blast
      apply (metis first_pop rev.simps(2))
      apply (meson not_empty)
      apply (metis add.left_neutral empty neq0_conv not_empty rev.simps(1) self_append_conv2)
      apply (smt (z3) Stack_Proof.size_pop Suc_pred append_assoc diff_add_inverse first_pop rev.simps(2) rev_append rev_rev_ident rev_singleton_conv)
      by (metis (no_types, hide_lams) add.commute add_diff_cancel_right' append.left_neutral append_Cons append_assoc first_pop length_Cons rev.simps(2) size_listLength)
   next
    case (Common x)
    then show ?case
      by(auto simp: Big_Proof.tick_toList Common_Proof.tick_toList)
  qed
qed
  
lemma tick_toCurrentList: "invariant states \<Longrightarrow> toCurrentList (tick states) = toCurrentList states"
proof(induction states rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case 
    by(auto split: current.splits)
next
  case ("2_1" v va vb vd right)
  then show ?case
    by(auto simp: Common_Proof.tick_toCurrentList split: current.splits prod.splits Small.state.splits)
next
  case ("2_2" v right)
  then show ?case 
    by(auto simp: Common_Proof.tick_toCurrentList  split: Small.state.splits current.splits)
next
  case ("2_3" left v va vb vc vd)
  then show ?case
    by(auto simp: Big_Proof.tick_toCurrentList split: current.splits)
next
  case ("2_4" left v)
  then show ?case
    by(auto simp: Big_Proof.tick_toCurrentList Common_Proof.tick_toCurrentList)
qed

lemma push_big: "toList (big, small) = (big', small') \<Longrightarrow> toList (Big.push x big, small) = (x # big', small')"
proof(induction "(Big.push x big, small)" rule: toList.induct)
  case (1 currentB big' auxB count currentS small auxS)
  then show ?case
  proof(induction x big rule: Big.push.induct)
    case (1 x state)
    then show ?case 
      by auto
  next
    case (2 x current big aux count)
    then show ?case 
      apply(induction x current rule: put.induct)
      by auto
  qed
next
  case ("2_1" v)
  then show ?case 
  proof(induction x big rule: Big.push.induct)
    case (1 x state)
    then show ?case 
      by(auto simp: Common_Proof.push)
  next
    case (2 x current big aux count)
    then show ?case 
      by auto
  qed
next
  case ("2_2" v va vb vc vd)
  then show ?case 
    by(auto simp: Big_Proof.push)
next
  case ("2_3" v)
  then show ?case by(auto simp: Big_Proof.push)
qed

lemma push_small: "
   invariant (big, small) \<Longrightarrow>
   toList (big, small) = (big', small') \<Longrightarrow> 
   toList (big, Small.push x small) = (big', x # small')"
proof(induction "(big, Small.push x small)" rule: toList.induct)
case (1 currentB big auxB count currentS small auxS)
  then show ?case
    by(auto split: current.splits Small.state.splits)
next
  case ("2_1" v)
  then show ?case
  proof(induction x small rule: Small.push.induct)
    case (1 x state)
    then show ?case
      by(auto simp: Common_Proof.push)
  next
    case (2 x current small auxS)
    then show ?case 
      apply(induction x current rule: put.induct)
      by auto
  next
    case (3 x current auxS big newS count)
    then show ?case 
      apply(induction x current rule: put.induct)
      by auto
  qed
next
  case ("2_2" v va vb vc vd)
  then show ?case 
  proof(induction x small rule: Small.push.induct)
    case (1 x state)
    then show ?case 
      by auto
  next
    case (2 x current small auxS)
    then show ?case 
      by auto
  next
    case (3 x current auxS big newS count)
    then show ?case 
      apply(induction x current rule: put.induct)
      by auto
  qed
next
  case ("2_3" v)
  then show ?case
  proof(induction x small rule: Small.push.induct)
    case (1 x state)
    then show ?case 
      by(auto simp: Common_Proof.push)
  next
    case (2 x current small auxS)
    then show ?case 
      by auto
  next
    case (3 x current auxS big newS count)
    then show ?case
      by auto
  qed
qed


(*
(* TODO: pop_invariant here? Or prove this on a higher level? *)
lemma pop_big: "\<lbrakk>
  invariant (big, small);
  Big.pop big = (x, poppedBig);
  toList (poppedBig, small) = (poppedBig', small');
  toList (big, small) = (big', small'')
\<rbrakk> \<Longrightarrow> (x # poppedBig', small') = (big', small'')"
proof(induction "(poppedBig, small)" arbitrary: x rule: toList.induct)
  case (1 currentB big' auxB count currentS small auxS)
  then show ?case
  proof(induction big arbitrary: x rule: Big.pop.induct)
    case (1 state)
    then show ?case 
      by auto
  next
    case (2 current big aux count)
    then show ?case
      apply(induction current arbitrary: x rule: get.induct)
       apply(auto split: current.splits)
      sorry
  qed
next
  case ("2_1" v)
  then show ?case sorry
next
  case ("2_2" v va vb vc vd)
  then show ?case sorry
next
  case ("2_3" v)
  then show ?case 
  proof(induction big arbitrary: x rule: Big.pop.induct)
    case (1 state)
    then show ?case 
    proof(induction state rule: Common.pop.induct)
      case (1 current idle)
      
      then show ?case
        apply(induction current rule: get.induct)
        by(auto simp: Idle_Proof.pop split: prod.splits) 
    next
      case (2 current aux new moved)
      then show ?case 
      proof(induction current rule: get.induct)
        case (1 added old remained)
        then show ?case 
          apply auto
          sorry
      next
        case (2 x xs added old remained)
        then show ?case by auto
      qed
    qed
  next
    case (2 current big aux count)
    then show ?case 
    proof(induction current rule: get.induct)
      case (1 added old remained)
      then show ?case 
        apply(induction count "Stack.toList big" aux rule: revN.induct)
        apply auto 
        sorry
    next
      case (2 x xs added old remained)
      then show ?case by auto 
    qed 
  qed
qed*)

(*
lemma pop_small: "\<lbrakk>
  invariant (big, small);
  Small.pop small = (x, poppedSmall);
  toList (big, poppedSmall) = (big', poppedSmall');
  toList (big, small) = (big'', small')
\<rbrakk> \<Longrightarrow> (big', poppedSmall') = (big'', small')"
proof(induction poppedSmall)
  case (Reverse1 x1 x2 x3a)
  then show ?case sorry
next
  case (Reverse2 x1 x2 x3a x4 x5)
  then show ?case sorry
next
  case (Common common)
  then show ?case 
    apply(induction common rule: Common.pop.induct)
     apply(auto split: state_splits prod.splits)
    sorry
qed*)

lemma invariant_pop_big: "invariant (big, small) \<Longrightarrow> pop_invariant big \<Longrightarrow> \<not>Big.isEmpty big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invariant (big', small)"
proof(induction big arbitrary: small x rule: Big.pop.induct)
  case (1 state)
  then show ?case
    apply(auto simp: revN_take split: prod.splits Small.state.splits current.splits)
    apply (meson Common_Proof.invariant_pop)
    sorry
next
  case (2 current big aux count)
  then show ?case apply auto
    sorry
qed

lemma invariant_pop_small: "invariant (big, small) \<Longrightarrow> \<not>Small.isEmpty small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invariant (big, small')"
proof(induction small arbitrary: big x rule: Small.pop.induct)
  case (1 state)
  then show ?case 
    apply auto
      apply (meson "1.prems"(2) "1.prems"(3) Small.invariant.simps(1) Small_Proof.invariant_pop)
    sorry
next
  case (2 current small auxS)
  then show ?case sorry
next
  case (3 current auxS big newS count)
  then show ?case sorry
qed

lemma invariant_push_big: "invariant (big, small) \<Longrightarrow> invariant (Big.push x big, small)"
proof(induction x big arbitrary: small rule: Big.push.induct)
  case (1 x state)
  then show ?case
  proof(induction x state rule: Common.push.induct)
    case (1 x current stack stackSize)
    then show ?case 
    proof(induction x current rule: put.induct)
      case (1 element extra added old remained)
      then show ?case 
        apply(induction element stack rule: Stack.push.induct)
        by auto
    qed
  next
    case (2 x current aux new moved)
    then show ?case 
      apply(induction x current rule: put.induct)
      by auto
  qed
next
  case (2 x current big aux count)
  then show ?case
  proof(induction x current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case
      by(auto split: prod.splits Small.state.splits)
  qed
qed

lemma invariant_push_small: "invariant (big, small) \<Longrightarrow> invariant (big, Small.push x small)"
proof(induction x small arbitrary: big rule: Small.push.induct)
  case (1 x state)
  then show ?case 
  proof(induction x state rule: Common.push.induct)
    case (1 x current stack stackSize)
    then show ?case 
    proof(induction x current rule: put.induct)
      case (1 element extra added old remained)
      then show ?case 
        apply(induction element stack rule: Stack.push.induct)
        by(auto split: state_splits)
    qed
  next
    case (2 x current aux new moved)
    then show ?case 
      proof(induction x current rule: put.induct)
        case (1 element extra added old remained)
        then show ?case 
          by(auto split: state_splits)
      qed
  qed
next
  case (2 x current small auxS)
  then show ?case
   proof(induction x current rule: put.induct)
     case (1 element extra added old remained)
     then show ?case 
       by(auto split: state_splits)
   qed
next
  case (3 x current auxS big newS count)
  then show ?case 
  proof(induction x current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case
      by(auto split: state_splits)
  qed
qed

(* TODO: *)
lemma invariant_tick: "invariant states \<Longrightarrow> invariant (tick states)"
proof(induction states rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case 
    apply(auto simp: revN_take split: current.splits)
      apply (metis length_0_conv minus_nat.diff_0 rev_is_Nil_conv self_append_conv size_listLength take_eq_Nil)
    apply (metis (no_types, hide_lams) length_rev length_take min.absorb2 nat_le_linear size_listLength take_all take_append)
    by (metis length_0_conv minus_nat.diff_0 rev_is_Nil_conv self_append_conv size_listLength take_eq_Nil)
next
  case ("2_1" v va vb vd right)
  then show ?case 
    apply(auto split: current.splits)
         apply (simp add: Stack_Proof.size_pop not_empty)
    (*apply(auto simp: Stack_Proof.size_pop not_empty split: current.splits prod.splits Small.state.splits)*)
    sorry
    (*apply (smt (verit, best) Zero_not_Suc bot_nat_0.extremum_uniqueI empty first_pop funpow_swap1 list.size(3) revN.elims revN.simps(2) revN.simps(3) size_listLength)
     apply (metis le_SucE not_empty zero_less_Suc)
    by (metis Zero_not_Suc bot_nat_0.extremum_uniqueI empty first_pop funpow_swap1 list.size(3) revN.simps(3) size_listLength)*)
next
  case ("2_2" v right)
  then show ?case
    apply(auto simp: Common_Proof.invariant_tick Small_Proof.invariant_tick split:)
    apply (metis "2_2.prems" Big.tick.simps(1) Big.toList.simps(1) Common_Proof.tick_toCurrentList Pair_inject Small_Proof.tick_toCurrentList States.tick.simps(3) States.toList.simps(2) States_Proof.tick_toList)
    by(auto simp:  split: Small.state.splits current.splits if_splits)
next
  case ("2_3" left v va vb vc vd)
  then show ?case
    apply(auto simp: Big_Proof.invariant_tick Small_Proof.invariant_tick split: current.split state_splits)
    apply (simp add: Common_Proof.tick_toCurrentList Common_Proof.tick_toList size_listLength)
    sorry
    (*apply (metis Common_Proof.tick_toCurrentList Common_Proof.tick_toList Nat.add_0_right add.commute append.left_neutral empty list.size(3) rev.simps(1) size_listLength)
    using not_empty apply blast
    using Common_Proof.some_empty apply blast
    apply (metis Stack_Proof.size_pop Suc_pred)
        apply (metis first_pop length_Cons size_listLength)
    apply (smt (z3) Common_Proof.tick_toCurrentList Common_Proof.tick_toList Stack_Proof.size_pop Suc_pred add_diff_cancel_left' append_assoc first_pop rev.simps(2) rev_append rev_rev_ident rev_singleton_conv)
    apply (metis Common_Proof.tick_toCurrentList Common_Proof.tick_toList append.left_neutral append_Cons append_assoc diff_add_inverse first_pop length_Cons rev.simps(2) size_listLength)
    using Common_Proof.some_empty apply blast
    using Common_Proof.some_empty by blast*)
next
  case ("2_4" left v)
  then show ?case 
    apply(auto simp: Big_Proof.invariant_tick Common_Proof.invariant_tick)
    apply (simp add: Big_Proof.tick_toCurrentList Big_Proof.tick_toList Common_Proof.tick_toCurrentList tick_toList_2)
    by(simp split: Big.state.splits)
qed

lemma tick_newSize_big: "invariant (big, small) \<Longrightarrow> tick (big, small) = (big', small') \<Longrightarrow> Big.newSize big = Big.newSize big'"
  apply(induction "(big, small)" rule: tick.induct)
  by(auto simp: Big_Proof.tick_newSize split: current.splits)

lemma tick_newSize_small: "invariant (big, small) \<Longrightarrow> tick (big, small) = (big', small') \<Longrightarrow> Small.newSize small = Small.newSize small'"
  apply(induction "(big, small)" rule: tick.induct)
  by(auto simp: Small_Proof.tick_newSize split: current.splits)

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

lemma remainingStepsDecline: "invariant states \<Longrightarrow> remainingSteps states \<ge> remainingSteps (tick states)"
  sorry

lemma remainingStepsDecline_2: "invariant states \<Longrightarrow> remainingSteps states > 0 \<Longrightarrow>  remainingSteps states = Suc (remainingSteps (tick states))"
  sorry

lemma tick_remainingSteps: "remainingSteps states \<ge> n \<Longrightarrow> invariant states \<Longrightarrow> remainingSteps states = remainingSteps ((tick^^n) states) + n" 
proof(induction n arbitrary: states)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    using remainingStepsDecline_2[of states] invariant_tick[of states]
    by (smt (verit, ccfv_SIG) Suc_le_mono add_Suc_right funpow_simps_right(2) le_zero_eq neq0_conv o_apply zero_less_Suc)
qed


lemma tick_inSizeWindow: "invariant states \<Longrightarrow> inSizeWindow states \<Longrightarrow> inSizeWindow (tick states)"
  using hello remainingStepsDecline
  by (smt (verit, best) add.commute diff_add_inverse inSizeWindow'.elims(1) inSizeWindow.elims(1) le_diff_conv le_trans tick_newSize_big tick_newSize_small)

lemma tick_not_empty: "invariant states \<Longrightarrow> \<not>isEmpty states \<Longrightarrow> \<not>isEmpty (tick states)"
proof(induction states) 
  case (Pair big small)
  then show ?case
  proof(induction "Big.isEmpty big")
    case True
    then show ?thesis sorry
  next
    case False
    then have "\<not>Big.isEmpty (Big.tick big)"
      using Big_Proof.tick_not_empty by auto
    with False show ?thesis 
      apply(auto split: prod.splits Big.state.splits Small.state.splits current.splits)
      subgoal apply(auto simp: revN_take)
        sorry
      using not_empty_2 apply blast
      using Common_Proof.some_empty by blast
  qed
qed

lemma same: "invariant (big, small) \<Longrightarrow> remainingSteps (big, small) \<ge> 4 \<Longrightarrow> inSizeWindow (big, small) \<Longrightarrow> inSizeWindow ((tick ^^ 4) (big, Small.push x small))"
proof(induction x small arbitrary: big rule: Small.push.induct)
  case (1 x state)
  
  with 1 show ?case 
    apply(auto simp: max_def split: Big.state.splits prod.splits if_splits)
    sorry
next
  case (2 x current small auxS)
then show ?case sorry
next
  case (3 x current auxS big newS count)
  then show ?case apply auto sorry
qed

lemma same_2: "invariant (big, small) \<Longrightarrow> remainingSteps (big, small) \<ge> 4 \<Longrightarrow> inSizeWindow (big, small) \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> inSizeWindow ((tick ^^ 4) (big, small'))"
  apply auto
  sorry



end
