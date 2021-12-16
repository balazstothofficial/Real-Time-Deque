theory States_Proof
  imports States Big_Proof Small_Proof HOL.Real Complex_Main
begin

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits
lemmas invariant_ticks = Big_Proof.invariant_tick Common_Proof.invariant_tick Small_Proof.invariant_tick

lemma tick_toListSmall: "\<lbrakk>
 tick (big, small) = (big', small')
\<rbrakk> \<Longrightarrow> Small.toList small = Small.toList small'"
  apply(induction "(big, small)" rule: tick.induct)
  by(auto simp: Common_Proof.tick Small_Proof.tick split: current.splits)

lemma tick_toListBig: "\<lbrakk>
 tick (big, small) = (big', small')
\<rbrakk> \<Longrightarrow> Big.toList big = Big.toList big'"
  apply(induction "(big, small)" rule: tick.induct)
  by(auto simp: Common_Proof.tick Big_Proof.tick split: current.splits)

corollary tick_toList:  "\<lbrakk>
 tick (big, small) = (big', small')
\<rbrakk> \<Longrightarrow> Big.toList big = Big.toList big' \<and> Small.toList small = Small.toList small'"
  by(simp add: tick_toListBig tick_toListSmall)

lemma remainingSteps: "\<lbrakk>remainingSteps states > 0; invariant states\<rbrakk>
   \<Longrightarrow> Suc (remainingSteps (tick states)) = remainingSteps states"
proof(induction states rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case
    by(auto split: current.splits)
next
  case ("2_1" v va vb vd right)
  then show ?case
    apply(auto simp: invariant_def Let_def split: Big.state.splits Small.state.splits current.splits)
    apply(auto simp:  max_def)
    apply(induction va rule: Stack.pop.induct)
    apply auto
    apply(induction va rule: Stack.pop.induct)
    apply auto
    subgoal for bigCurrent smallCurrent bigIdle smallIdle x1 x3 x4 x22a x23a x24a x1b x3b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for bigCurrent smallCurrent bigIdle smallIdle x1 x3 x4 x22a x23a x24a x1b x3b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for bigCurrent smallCurrent bigIdle smallIdle x1 x3 x4 x22a x23a x24a x1b x3b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for bigCurrent smallCurrent bigIdle smallIdle x1 x3 x4 x22a x23a x24a x1b x3b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for bigCurrent smallCurrent bigIdle smallIdle x1 x3 x4 x22a x23a x24a x1b x3b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    apply(auto simp: Common_Proof.remainingSteps)
    subgoal for x3 x1 x3a x4
      apply(induction x3 rule: Common.tick.induct)
      by(auto split: current.splits if_splits)
    subgoal for x3 x1 x3a x4
      apply(induction x3 rule: Common.tick.induct)
      by(auto split: current.splits if_splits)
    done
next
  case ("2_2" v right)
  then show ?case
    apply(auto simp: invariant_def split: Small.state.splits current.splits)
    apply(induction v rule: Common.tick.induct)
    apply(auto split: current.splits)
         apply(auto simp: max_def)
                        apply (simp add: not_empty_2 size_listLength)      
                      apply (simp add: not_empty_2 size_listLength)
    using not_empty apply blast
    using not_empty apply blast
    using not_empty apply blast
                  apply (simp split: if_splits )
                  apply (metis Common_Proof.remainingSteps add.commute less_or_eq_imp_le neq0_conv not_less_eq_eq)
    apply (metis Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN add.commute bot_nat_0.extremum funpow_0 le_eq_less_or_eq not_less_eq_eq)
                apply (metis Common_Proof.remainingSteps bot_nat_0.extremum neq0_conv)
               apply (metis Stack_Proof.size_pop Suc_pred add_Suc_right diff_add_inverse)
    apply (metis Common_Proof.remainingSteps Stack_Proof.size_pop Suc_pred add_Suc_right diff_add_inverse less_or_eq_imp_le neq0_conv not_less_eq_eq)
    apply (metis Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN Stack_Proof.size_pop Suc_le_mono Suc_pred add_Suc_right diff_add_inverse funpow_0 gr0I less_Suc_eq_le zero_less_Suc)
            apply (metis Common_Proof.remainingSteps bot_nat_0.extremum neq0_conv)
           apply (metis Nat.add_0_right add.commute diff_add_inverse2 helper_x)
    apply (smt (z3) Common_Proof.remainingSteps Nitpick.size_list_simp(2) Stack_Proof.pop Suc_leI add_Suc_right add_diff_cancel_left' le_imp_less_Suc less_le_trans linear not_empty_2 size_listLength zero_less_Suc)
    apply (smt (z3) Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN Suc_diff_eq_diff_pred add_Suc_right diff_Suc_1 diff_add_inverse diff_is_0_eq first_pop funpow_0 gr0I length_Cons less_Suc_eq_le size_listLength zero_less_Suc)
        apply (metis Common_Proof.remainingSteps less_or_eq_imp_le neq0_conv)
        apply (metis Common_Proof.remainingSteps)
        apply (metis Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN eq_iff funpow_0 less_or_eq_imp_le neq0_conv not_less_eq_eq)
        apply (metis Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN funpow_0 nat_less_le neq0_conv not_less_eq)
    by (metis Common_Proof.remainingSteps less_or_eq_imp_le neq0_conv)
next
  case ("2_3" left v va vb vc vd)
  then show ?case
    apply(auto simp: invariant_def split: current.splits Big.state.splits)
    apply (metis Big.remainingSteps.simps(2) Big_Proof.remainingSteps One_nat_def add_diff_cancel_right' diff_Suc_1 lessI trans_less_add2)
    apply (metis length_0_conv not_empty_2 size_listLength)
    apply (meson not_empty)
    apply (metis Big.remainingSteps.simps(2) Big_Proof.remainingSteps Suc_eq_plus1_left add.commute diff_Suc_1 zero_less_Suc)
    apply (metis Big.remainingSteps.simps(2) Big_Proof.remainingSteps Suc_eq_plus1_left add.commute diff_add_inverse helper_x zero_less_Suc)
    apply (metis Big.remainingSteps.simps(2) Big_Proof.remainingSteps Suc_eq_plus1_left add.commute diff_add_inverse2 helper_x zero_less_Suc)
    apply (metis Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN funpow_0 max.commute max_0R max_def not_less_eq_eq)
    apply (metis length_0_conv not_empty_2 size_listLength)
    using not_empty apply blast
    apply (metis (no_types, lifting) Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN funpow_0 max_Suc_Suc max_def max_nat.neutr_eq_iff neq0_conv)
    apply (smt (z3) Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN Stack_Proof.size_pop Suc_pred add.commute add_Suc_right diff_add_inverse funpow_0 max_Suc_Suc max_def max_nat.neutr_eq_iff neq0_conv)
    by (smt (z3) Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN Suc_eq_plus1_left add.commute diff_add_inverse2 funpow_0 helper_x max_Suc_Suc max_def max_nat.neutr_eq_iff neq0_conv)
next
  case ("2_4" left v)
  then show ?case
    apply(auto simp: invariant_def split: Big.state.splits current.splits)
     apply (metis Big.remainingSteps.simps(2) Big_Proof.remainingSteps Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN Suc_eq_plus1_left add.commute funpow_0 gr0I max_Suc_Suc max_def max_nat.neutr_eq_iff zero_less_Suc)
    by (smt (z3) Common.tick.simps(1) Common_Proof.remainingSteps Common_Proof.tickN funpow_0 gr0I less_max_iff_disj max_Suc_Suc max_def)
qed


lemma helper: "
  (case states of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow>
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | _ \<Rightarrow> True) 
  \<Longrightarrow>  (case tick (states) of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow>
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | _ \<Rightarrow> True)"
  sorry

lemma endInvariant: "endInvariant states \<Longrightarrow> endInvariant (tick states)"
proof(induction states rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case sorry
next
  case ("2_1" v va vb vd right)
  then show ?case sorry
next
  case ("2_2" v right)
  then show ?case sorry
next
  case ("2_3" left v va vb vc vd)
  then show ?case sorry
next
  case ("2_4" big smallCommon)
  then show ?case 
  proof(induction "Big.remainingSteps big < Common.remainingSteps smallCommon")
    case True
    then show ?case 
    proof(induction "Common.remainingSteps smallCommon")
      case 0
      then show ?case
        by auto
    next
      case (Suc x)
      then show ?case
      proof(induction smallCommon rule: Common.tick.induct)
        case (1 current idle)
        then show ?case
          by auto
      next
        case (2 current aux new moved)
        then show ?case 
        proof(induction big rule: Big.tick.induct)
          case (1 state)
          then show ?case 
          proof(induction state rule: Common.tick.induct)
            case (1 current idle)
            then show ?case apply(auto simp: max_def split: current.splits)
              sorry 
          next
            case (2 current aux new moved)
            then show ?case 
              sorry
          qed
        next
          case (2 current uu auxB)
          then show ?case sorry
        next
          case (3 current big auxB v)
          then show ?case sorry
        qed
      qed
    qed
  next
    case False
    then show ?case
      sorry
  qed
qed


(*proof(induction "remainingSteps states" arbitrary: states)
  case 0

  then show ?case 
    by auto
next
  case (Suc x)
  then show ?case
  proof(induction states rule: tick.induct)
    case (1 currentB big auxB currentS uu auxS)
    then show ?case sorry
  next
    case ("2_1" v va vb vd right)
    then show ?case sorry
  next
    case ("2_2" v right)
    then show ?case sorry
  next
    case ("2_3" left v va vb vc vd)
    then show ?case sorry
  next
    case ("2_4" big smallCommon)
    then show ?case 
    proof(induction big)
      case (Reverse x1 x2a x3 x4)
      then show ?case sorry
    next
      case (Common bigCommon)
      then show ?case 
        apply(induction "Common.remainingSteps smallCommon < Common.remainingSteps bigCommon")
           apply auto
        sorry
    qed
  qed
qed *)

lemma invariant_tick: "invariant states \<Longrightarrow> invariant (tick states)"
proof(induction states)
  case (Pair big small)

  obtain big' small' where ticked: "tick (big, small) = (big', small')"
    using prod.exhaust_sel by blast

  from Pair have invariants: "Big.invariant big"  "Small.invariant small"
    by(auto simp: invariant_def)

  with ticked have "Big.tick big = big'"
    apply(induction "(big, small)" rule: tick.induct)
    by(auto)

  with ticked invariants have bigInvariant: "Big.invariant big'"
    by(auto simp: Big_Proof.invariant_tick)

  from ticked invariants have smallInvariant: "Small.invariant small'"
    apply(induction "(big, small)" rule: tick.induct)
    apply(auto simp: Small_Proof.invariant_tick Common_Proof.invariant_tick)
    apply(auto simp: Let_def split: current.splits if_splits)
    sorry

  from Pair ticked helper have middle: "case big' of
            Reverse x big xa count \<Rightarrow> case small' of Reverse1 (Current xb xc old remained) small xd \<Rightarrow> Stack.size big - count = remained - Stack.size old \<and> Stack.size small \<le> count | _ \<Rightarrow> True
            | Big.state.Common state \<Rightarrow> case small' of Reverse1 xa xb xc \<Rightarrow> False | _ \<Rightarrow> True"
    apply(auto simp: invariant_def)
    by fastforce
      
   from Pair show ?case
     unfolding invariant_def
     apply(auto simp: middle endInvariant  bigInvariant smallInvariant ticked)
     using endInvariant ticked by fastforce
qed

lemma tickN: "invariant states
   \<Longrightarrow> \<exists> bigCurrent bigIdle smallCurrent smallIdle.
    (tick^^ remainingSteps states) states = (
        Big.state.Common   (Idle bigCurrent  bigIdle),
        Small.state.Common (Idle smallCurrent smallIdle)
      )"
proof(induction "remainingSteps states" arbitrary: states)
  case 0
  then show ?case 
    apply(induction states)
    by(auto simp: invariant_def split: Small.state.splits current.splits Big.state.splits)
next
  case (Suc x)
  obtain states' where state': "states' = tick states"
    by auto
  
  then have "invariant states'"
    by(auto simp: Suc.prems invariant_tick)
  
  have x: "(tick^^ x) states' = (tick^^ Suc x) states"
    by(auto simp: state' funpow_swap1)
  
  then have "remainingSteps states' = x"
    by (metis States_Proof.remainingSteps Suc.hyps(2) Suc.prems diff_Suc_1 state' zero_less_Suc)

  then have "\<exists> bigCurrent bigIdle smallCurrent smallIdle.
    (tick^^ x) states' = (
        Big.state.Common   (Idle bigCurrent  bigIdle),
        Small.state.Common (Idle smallCurrent smallIdle)
      )"
    using Suc.hyps(1) \<open>invariant states'\<close> by blast

  then show ?case
    by (simp add: Suc.hyps(2) x)
 
qed

lemma invariant_pushSmall: "invariant (big, small) \<Longrightarrow> invariant (big, Small.push x small)"
proof(induction x small rule: Small.push.induct)
  case (1 x state)
  then show ?case 
    apply(auto simp: invariant_def Common_Proof.invariant_push split: state_splits current.splits)
    sorry
next
  case (2 x current small auxS)
  then show ?case 
    apply(auto simp: invariant_def split: state_splits current.splits)
    sorry
next
  case (3 x current auxS big newS count)
  then show ?case
    apply(auto simp: invariant_def split: state_splits current.splits)
    sorry
qed

lemma invariant_pushBig: "invariant (big, small) \<Longrightarrow> invariant (Big.push x big, small)"
proof(induction x big rule: Big.push.induct)
  case (1 x state)
  then show ?case 
    apply(auto simp: invariant_def Common_Proof.invariant_push)
    sorry
next
  case (2 x current big auxB count)
  then show ?case
    apply(auto simp: invariant_def  split: current.splits)
    sorry
qed

(* TODO: Pops not yet fully proven! *)

lemma invariant_popSmall: "\<lbrakk>
  invariant (big, small);
  \<not> Small.isEmpty small;
  Small.pop small = (x, small')
\<rbrakk> \<Longrightarrow> invariant (big, small')"
proof(induction small rule: Small.pop.induct)
  case (1 state)
  then show ?case
    apply(auto simp: invariant_def  Common_Proof.invariant_pop split: state_splits current.splits prod.splits)
    sorry
next
  case (2 current small auxS)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: invariant_def Let_def split: state_splits current.splits)
      subgoal for x12 x13 x14 x1 x3 x4
        apply(induction old rule: Stack.pop.induct)
          apply auto
          sorry
        apply (metis Stack_Proof.size_pop diff_le_mono)
       apply (metis Stack_Proof.size_pop less_Suc_eq_le less_imp_diff_less)
         apply (metis Nat.add_0_right helper_x)
        sorry
  next
    case (2 x xs added old remained)
    then show ?case 
      apply(auto simp: invariant_def Let_def split: state_splits)
      sorry
  qed
next
  case (3 current auxS big newS count)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: invariant_def Stack_Proof.size_pop split: state_splits current.splits)
      apply (metis One_nat_def Stack_Proof.pop Suc_diff_eq_diff_pred Suc_diff_le drop_Suc length_greater_0_conv not_empty_2 size_listLength tl_drop)
      apply (metis Nat.add_diff_assoc Suc_pred diff_is_0_eq length_greater_0_conv nat_le_linear not_empty_2 size_listLength)
      sorry
  next
    case (2 x xs added old remained)
    then show ?case apply(auto simp: invariant_def split: state_splits)
      sorry
  qed
qed

lemma invariant_popBig: "\<lbrakk>
  invariant (big, small);
  \<not> Big.isEmpty big;
  Big.pop big = (x, big')
\<rbrakk> \<Longrightarrow> invariant (big', small)"
proof(induction big arbitrary: x small rule: Big.pop.induct)
case (1 state)
  then show ?case
    apply(auto simp: invariant_def Common_Proof.invariant_pop split: prod.splits)
    sorry
next
  case (2 current big auxB count)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: Let_def split: current.splits state_splits)
         sorry
  next
    case (2 x xs added old remained)
    then show ?case 
      apply(auto simp: invariant_def)
      sorry
  qed
qed

(*

lemma listLeft': "\<lbrakk>
  invariant (
    Big.state.Common   (Idle bigCurrent  bigIdle),
    Small.state.Common (Idle smallCurrent smallIdle)
  )
  \<rbrakk> \<Longrightarrow> Current.toList smallCurrent @ rev (Current.toList bigCurrent) 
     = Idle.toList smallIdle @ rev (Idle.toList bigIdle)"
  apply(auto simp: invariant_def split: Big.state.splits Small.state.splits current.splits idle.splits stack.splits)
         apply (meson Small.invariant.cases)
  sorry

lemma listLeft: "\<lbrakk>
  invariant states;
  (tick^^ remainingSteps states) states = (
    Big.state.Common   (Idle bigCurrent  bigIdle),
    Small.state.Common (Idle smallCurrent smallIdle)
  )
  \<rbrakk> \<Longrightarrow> Current.toList smallCurrent @ rev (Current.toList bigCurrent) 
     = Idle.toList smallIdle @ rev (Idle.toList bigIdle)"
proof(induction "remainingSteps states" arbitrary: states)
  case 0
  then show ?case 
    apply(induction states)
    apply(auto simp: test invariant_def split: idle.splits stack.splits current.splits)
    
    sorry
next
  case (Suc x)
  then show ?case sorry
qed*)

end
