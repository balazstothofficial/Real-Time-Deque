theory States_Proof
  imports States Big_Proof Small_Proof HOL.Real Complex_Main
begin

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits
lemmas invar_steps = Big_Proof.invar_step Common_Proof.invar_step Small_Proof.invar_step

lemma invar_list_big_first: "invar states \<Longrightarrow> list_big_first states = list_current_big_first states"
  apply(auto split: prod.splits)
  by (metis rev_append rev_rev_ident)

lemma step_lists: "invar states \<Longrightarrow> lists (step states) = lists states"
proof(induction states rule: lists.induct)
  case (1 currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction "(Reverse currentB big auxB count, Reverse1 currentS small auxS)" rule: step.induct)
    case 1
    then show ?case 
    proof(induction currentB)
      case (Current extra added old remained)
      then show ?case by auto
    qed
  next
    case ("2_1" count')
    then show ?case 
      using Big_Proof.step_list[of "Reverse currentB big auxB count"]
      apply auto
      apply (metis (no_types, lifting) funpow_swap1 less_eq_nat.simps(1) list.size(3) reverseN_take take_all list_empty)
      by (metis (no_types, lifting) first_pop funpow_swap1 reverseN.simps(3))
  qed
next
  case ("2_1" common small)
  then show ?case 
    using Small_Proof.step_list_reverse2[of small]
    by(auto simp: Common_Proof.step_list split: Small.state.splits)
next
  case ("2_2" big current auxS big newS count)
  then show ?case 
    using 
      Small_Proof.step_list_reverse2[of "Reverse2 current auxS big newS count"]
      Big_Proof.step_list
    by auto
next
  case ("2_3" big common)
  then show ?case 
    by(auto simp: Big_Proof.step_list Common_Proof.step_list)
qed
  
lemma step_lists_current: "invar states \<Longrightarrow> lists_current (step states) = lists_current states"
proof(induction states rule: step.induct)
  case (1 currentB big auxB currentS small auxS)
  then show ?case 
    by(auto split: current.splits)
next
  case ("2_1" current big auxB count small)
  then show ?case
    by(auto simp: Common_Proof.step_list_current split: current.splits prod.splits Small.state.splits)
next
  case ("2_2" common small)
  then show ?case 
    by(auto simp: Common_Proof.step_list_current  split: Small.state.splits current.splits)
next
  case ("2_3" big current auxS big new count)
  then show ?case
    by(auto simp: Big_Proof.step_list_current split: current.splits)
next
  case ("2_4" big common)
  then show ?case
    by(auto simp: Big_Proof.step_list_current Common_Proof.step_list_current)
qed

lemma push_big: "lists (big, small) = (big', small')
   \<Longrightarrow> lists (Big.push x big, small) = (x # big', small')"
proof(induction "(Big.push x big, small)" rule: lists.induct)
  case (1 currentB big' auxB count currentS small auxS)
  then show ?case
  proof(induction x big rule: Big.push.induct)
    case (1 x state)
    then show ?case 
      by auto
  next
    case (2 x current big aux count)
    then show ?case 
      apply(induction x current rule: Current.push.induct)
      by auto
  qed
next
  case ("2_1" v)
  then show ?case 
  proof(induction x big rule: Big.push.induct)
    case (1 x state)
    then show ?case 
      by(auto simp: Common_Proof.push_list)
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
   invar (big, small) \<Longrightarrow>
   lists (big, small) = (big', small') \<Longrightarrow> 
   lists (big, Small.push x small) = (big', x # small')"
proof(induction "(big, Small.push x small)" rule: lists.induct)
case (1 currentB big auxB count currentS small auxS)
  then show ?case
    by(auto split: current.splits Small.state.splits)
next
  case ("2_1" v)
  then show ?case
  proof(induction x small rule: Small.push.induct)
    case (1 x state)
    then show ?case
      by(auto simp: Common_Proof.push_list)
  next
    case (2 x current small auxS)
    then show ?case 
      apply(induction x current rule: Current.push.induct)
      by auto
  next
    case (3 x current auxS big newS count)
    then show ?case 
      apply(induction x current rule: Current.push.induct)
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
      apply(induction x current rule: Current.push.induct)
      by auto
  qed
next
  case ("2_3" v)
  then show ?case
  proof(induction x small rule: Small.push.induct)
    case (1 x state)
    then show ?case 
      by(auto simp: Common_Proof.push_list)
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


lemma smart: "list_small_first (big, small) = list_current_small_first (big, small) \<longleftrightarrow>
              list_big_first (big, small) = list_current_big_first (big, small)"
  apply(auto split: prod.splits)
  by (metis rev_append rev_rev_ident)+


lemma invar_pop_big_size_1: "\<lbrakk>
  invar (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow>  Big.invar big'  \<and> Small.invar small"
  by(auto simp: Big_Proof.invar_pop_2)

lemma invar_pop_big_size_2_1_1: "\<lbrakk>
  invar (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> tl (list_big_first (big, small)) = list_big_first (big', small)"
proof(induction "(big, small)" rule: lists.induct)
  case (1 currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction currentB rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case
    proof(induction  "(Reverse2 currentS (drop (List.length (Stack.list small) - count) (rev (Stack.list small)) @ auxS) ((Stack.pop ^^ count) big) [] 0)" rule: Small.list.induct)
      case (2 extra uu uv remained')
      then show ?case   
      apply(auto simp: reverseN_take)
      proof(induction "rev (take (remained - min (List.length (Stack.list big)) count) auxB) = []")
        case True
        then show ?case apply auto 
           apply (smt (z3) Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc length_rev length_take min.absorb2 neq0_conv rev_is_Nil_conv rev_take Stack_Proof.size_not_empty Stack_Proof.size_list_length take_eq_Nil tl_append2 tl_drop Stack_Proof.list_not_empty) 
          by (smt (z3) Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc length_rev length_take min.absorb2 neq0_conv rev_take Stack_Proof.size_not_empty Stack_Proof.size_list_length take_eq_Nil tl_append2 tl_drop Stack_Proof.list_not_empty)
      next
        case False
        then show ?case apply auto 
           apply (smt (verit, best) False.prems(4) Suc_diff_eq_diff_pred Suc_diff_le diff_add_inverse diff_is_0_eq drop_Suc length_rev length_take min.absorb2 not_less_eq_eq plus_1_eq_Suc rev_take same_append_eq self_append_conv Stack_Proof.size_list_length take_eq_Nil tl_drop zero_less_Suc)
          by (smt (z3) Suc_diff_Suc Suc_diff_le diff_Suc_Suc drop_Suc min.absorb2 not_le_imp_less rev_take Stack_Proof.size_list_length tl_drop)
      qed
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case ("2_1" v)
  then show ?case 
    by(auto simp: pop_list split: prod.splits)
next
  case ("2_2" v va vb vc vd)
  then show ?case 
    apply(auto simp: pop_2_size)
    using helper_3_size tl_append2 by blast
next
  case ("2_3" v)
  then show ?case 
    apply(auto simp: pop_2_size)
    using helper_3_size tl_append2 by blast
qed

lemma invar_pop_big_size_2_1_2: "\<lbrakk>
  invar (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> tl (list_current_big_first (big, small)) = list_current_big_first (big', small)"
  apply(auto split: prod.splits)
  using Big_Proof.list_current_size Big_Proof.pop_list_current
  by (metis list.sel(3) tl_append2)

lemma invar_pop_big_size_2_1: "\<lbrakk>
  invar (big, small);
   0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> list_big_first (big', small) = list_current_big_first (big', small)"
  by (metis invar_list_big_first invar_pop_big_size_2_1_1 invar_pop_big_size_2_1_2)

lemma invar_pop_big_size_2: "\<lbrakk>
  invar (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> list_small_first (big', small) = list_current_small_first (big', small)"
  by (meson invar_pop_big_size_2_1 smart)


lemma invar_pop_big_size_3: "\<lbrakk>
  invar (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> (case (big', small) of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow> 
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | (Reverse _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      )"
  apply(auto split: Big.state.splits Small.state.splits)
   apply (smt (z3) Big.state.distinct(1) case_prod_conv old.prod.exhaust prod.inject)
  by (metis (no_types, lifting) Big.state.distinct(1) case_prod_conv old.prod.exhaust prod.inject)


lemma invar_pop_big_size: "\<lbrakk>
  invar (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> invar (big', small)"
  using invar_pop_big_size_1[of big small x big']  
        invar_pop_big_size_2[of big small x big']
        invar_pop_big_size_3[of big small x big']
  by auto

lemma invar_pop_small_size_1: "\<lbrakk>
  invar (big, small);
  0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow>  Big.invar big  \<and> Small.invar small'"
  by(auto simp: Small_Proof.invar_pop_2)

lemma invar_pop_small_size_2_1: "\<lbrakk>
  invar (big, small);
   0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> tl (list_small_first (big, small)) = list_small_first (big, small')"
proof(induction "(big, small)" rule: lists.induct)
  case (1 currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction currentS rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: popN_drop popN_size reverseN_drop rev_drop)
      by (smt (z3) Small_Proof.invar_pop_2_helper Stack_Proof.pop_list Stack_Proof.size_pop Suc_diff_le Suc_pred append_assoc diff_Suc_Suc diff_add_inverse diff_commute diff_diff_cancel diff_is_0_eq' diff_zero drop0 length_rev rev_drop rev_rev_ident rev_take Stack_Proof.size_not_empty Stack_Proof.size_list_length tl_append2 Stack_Proof.list_not_empty)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case ("2_1" v)
  then show ?case 
  proof(induction small)
    case (Reverse1 x1 x2 x3a)
    then show ?case by auto
  next
    case (Reverse2 x1 x2 x3a x4 x5)
    then show ?case 
    proof(induction x1 rule: Current.pop.induct)
      case (1 added old remained)
      then show ?case 
        apply(auto simp: reverseN_take)
        by (smt (z3) Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc length_greater_0_conv less_le_trans neq0_conv rev_is_Nil_conv rev_take take_eq_Nil tl_append2 tl_drop)+
    next
      case (2 x xs added old remained)
      then show ?case by auto
    qed
  next
    case (Common common)
    then show ?case
    proof(induction common rule: Common.pop.induct)
      case (1 current idle)
      then show ?case 
      proof(induction current rule: Current.pop.induct)
        case (1 added old remained)
       
  
        from 1 show ?case 
         proof(induction idle rule: Idle.pop.induct)
           case (1 stack stackSize)
           then show ?case 
             apply auto
             by (metis Stack_Proof.pop_list Stack_Proof.size_not_empty tl_append2 Stack_Proof.list_not_empty)
         qed
      next
        case (2 x xs added old remained)
        then show ?case apply(auto split: prod.splits)
          by (metis (no_types, lifting) Zero_not_Suc length_Cons list.sel(3) list.size(3) pop_list_2 tl_append2 zero_less_Suc) 
      qed
    next
      case (2 current aux new moved)
      then show ?case 
      proof(induction current rule: Current.pop.induct)
        case (1 added old remained)
        then show ?case 
          apply(auto simp: reverseN_drop)
          apply (smt (verit, ccfv_threshold) Suc_diff_Suc append_take_drop_id diff_Suc_1 diff_add_inverse2 diff_commute diff_diff_cancel diff_is_0_eq drop_eq_Nil length_rev less_le_trans list.sel(3) not_le same_append_eq self_append_conv2 take_all_iff take_hd_drop tl_append2)
          by (metis (no_types, lifting) Nat.diff_diff_right Suc_diff_le drop_Suc drop_eq_Nil leD le_add_diff_inverse le_diff_conv length_rev less_add_same_cancel2 less_imp_le_nat tl_append2 tl_drop zero_less_diff)
      next
        case (2 x xs added old remained)
        then show ?case by auto
      qed
    qed
  qed
next
  case ("2_2" current auxS big newS count)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: reverseN_drop) 
      by (simp_all add: Suc_diff_le drop_Suc rev_take tl_drop)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case ("2_3" common)
  then show ?case 
  proof(induction common rule: Common.pop.induct)
    case (1 current idle)
    then show ?case 
    proof(induction idle rule: Idle.pop.induct)
      case (1 stack stackSize)
      then show ?case 
      proof(induction current rule: Current.pop.induct)
        case (1 added old remained)
        then show ?case 
          apply(auto split: Big.state.splits)
          by (metis Stack_Proof.pop_list Stack_Proof.size_not_empty tl_append2 Stack_Proof.list_not_empty)
      next
        case (2 x xs added old remained)
        then show ?case 
          apply(auto split: Big.state.splits)
          by (metis Stack_Proof.pop_list list.sel(3) Stack_Proof.size_not_empty tl_append2 Stack_Proof.list_not_empty zero_less_Suc)
      qed
    qed
  next
    case (2 current aux new moved)
    then show ?case 
    proof(induction current rule: Current.pop.induct)
      case (1 added old remained)
      then show ?case 
        apply(auto simp: reverseN_take split: Big.state.splits)
        apply (smt (z3) One_nat_def diff_commute diff_is_0_eq leD le_diff_conv length_0_conv length_rev length_take length_tl min.absorb2 self_append_conv2 tl_append2)
        by (smt (verit, best) Nat.diff_diff_right Suc_diff_le diff_Suc_Suc diff_add_inverse diff_add_inverse2 diff_diff_left diff_is_0_eq drop_Suc leD length_greater_0_conv less_add_same_cancel2 less_imp_Suc_add less_le_trans less_or_eq_imp_le rev_is_Nil_conv rev_take take_eq_Nil tl_append2 tl_drop)
    next
      case (2 x xs added old remained)
      then show ?case by auto
    qed
  qed
qed

lemma invar_pop_small_size_2_2: "\<lbrakk>
  invar (big, small);
  0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> tl (list_current_small_first (big, small)) = list_current_small_first (big, small')"
  apply(auto simp: pop_list_current  split: prod.splits)
  using Small_Proof.list_current_size tl_append2
  by (metis (no_types, lifting) Small_Proof.pop_list_current list.sel(3))

lemma invar_pop_small_size_2: "\<lbrakk>
  invar (big, small);
  0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> list_small_first (big, small') = list_current_small_first (big, small')"
  using invar_pop_small_size_2_1 invar_pop_small_size_2_2 by fastforce

lemma invar_pop_small_size_3: "\<lbrakk>
  invar (big, small);
  0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> (case (big, small') of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow> 
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | (Reverse _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      )"
proof(induction small rule: Small.pop.induct)
  case (1 common)
  then show ?case
    by(auto split: Big.state.splits Small.state.splits prod.splits)
next
  case (2 current small auxS)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      by(auto simp: Stack_Proof.size_pop Stack_Proof.size_not_empty split: Big.state.splits)
  next
    case (2 x xs added old remained)
    then show ?case 
      by(auto split: Big.state.splits)
  qed
next
  case (3 current auxS big newS count)
  then show ?case 
    by(auto split: Big.state.splits)
qed
  
lemma invar_pop_small_size: "\<lbrakk>
  invar (big, small);
   0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
   \<Longrightarrow> invar (big, small')"
  using invar_pop_small_size_1[of big small x small']  
        invar_pop_small_size_2[of big small x small']
        invar_pop_small_size_3[of big small x small']
  by fastforce  

lemma invar_push_big: "invar (big, small) \<Longrightarrow> invar (Big.push x big, small)"
proof(induction x big arbitrary: small rule: Big.push.induct)
  case (1 x state)
  then show ?case
  proof(induction x state rule: Common.push.induct)
    case (1 x current stack stackSize)
    then show ?case 
    proof(induction x current rule: Current.push.induct)
      case (1 x extra added old remained)
      then show ?case 
        apply(induction x stack rule: Stack.push.induct)
        by auto
    qed
  next
    case (2 x current aux new moved)
    then show ?case 
      apply(induction x current rule: Current.push.induct)
      by auto
  qed
next
  case (2 x current big aux count)
  then show ?case
  proof(induction x current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case
      by(auto split: prod.splits Small.state.splits)
  qed
qed

lemma invar_push_small: "invar (big, small) \<Longrightarrow> invar (big, Small.push x small)"
proof(induction x small arbitrary: big rule: Small.push.induct)
  case (1 x state)
  then show ?case 
  proof(induction x state rule: Common.push.induct)
    case (1 x current stack stackSize)
    then show ?case 
    proof(induction x current rule: Current.push.induct)
      case (1 x extra added old remained)
      then show ?case 
        apply(induction x stack rule: Stack.push.induct)
        by(auto split: state_splits)
    qed
  next
    case (2 x current aux new moved)
    then show ?case 
      proof(induction x current rule: Current.push.induct)
        case (1 x extra added old remained)
        then show ?case 
          by(auto split: state_splits)
      qed
  qed
next
  case (2 x current small auxS)
  then show ?case
   proof(induction x current rule: Current.push.induct)
     case (1 x extra added old remained)
     then show ?case 
       by(auto split: state_splits)
   qed
next
  case (3 x current auxS big newS count)
  then show ?case 
  proof(induction x current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case
      by(auto split: state_splits)
  qed
qed

lemma invar_step_1: "invar states \<Longrightarrow> step states = (big, small) \<Longrightarrow> Big.invar big \<and> Small.invar small"
proof(induction states rule: step.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case apply(auto simp: reverseN_drop split: current.splits if_splits)
    apply (metis Stack_Proof.size_empty append.right_neutral cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel le_cases list.size(3) rev.simps(1) take_Nil Stack_Proof.list_not_empty)
    apply (smt (z3) Nil_is_rev_conv Stack_Proof.size_empty append_self_conv2 diff_diff_cancel length_drop length_rev length_take rev_append rev_take Stack_Proof.size_list_length take_all take_append take_eq_Nil take_take list_not_empty)
    by (metis Stack_Proof.size_empty append.right_neutral list.size(3) minus_nat.diff_0 rev.simps(1) take_Nil Stack_Proof.list_not_empty)
next
  case ("2_1" v va vb vd right)
  then show ?case using Big_Proof.invar_step  Small_Proof.invar_step
    by (metis (no_types, lifting) Pair_inject States.invar.elims(2) States.step.simps(2) case_prodD)
next
  case ("2_2" v right)
  then show ?case by(auto simp: Common_Proof.invar_step Small_Proof.invar_step)
next
  case ("2_3" left v va vb vc vd)
  then show ?case using Common_Proof.invar_step Big_Proof.invar_step  Small_Proof.invar_step
    by (smt (z3) States.invar.elims(2) States.step.simps(4) case_prod_conv)
next
  case ("2_4" left v)
  then show ?case by(auto simp: Common_Proof.invar_step Big_Proof.invar_step)
qed

lemma invar_step_2: "invar states \<Longrightarrow> list_small_first (step states) = list_current_small_first (step states)"
  using step_lists_current step_lists by fastforce

lemma invar_step_3: "invar states \<Longrightarrow>(case step states of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow> 
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | (Reverse _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      )"
proof(induction states rule: step.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by auto
next
  case ("2_1" v va vb vd right)
  then show ?case 
    apply(auto split: Big.state.splits Small.state.splits current.splits) 
    apply (metis One_nat_def Stack_Proof.size_pop diff_diff_left plus_1_eq_Suc)
    apply (metis Stack_Proof.size_empty gr_implies_not0 not_less)
    apply (metis One_nat_def Stack_Proof.size_pop diff_Suc_eq_diff_pred)
    by (metis not_less_eq_eq pop_list_length Stack_Proof.size_list_length)
next
  case ("2_2" v right)
  then show ?case by(auto split: Big.state.splits Small.state.splits) 
next
  case ("2_3" left v va vb vc vd)
  then show ?case by(auto split: Big.state.splits) 
next
  case ("2_4" left v)
  then show ?case by(auto split: Big.state.splits) 
qed

(* TODO: *)
lemma invar_step: "invar states \<Longrightarrow> invar (step states)"
  using invar_step_1 invar_step_2 invar_step_3
  by (smt (z3) States.invar.elims(3) case_prodI2)

lemma size_ok'_Suc: "size_ok' states (Suc steps) \<Longrightarrow> size_ok' states steps"
  apply(induction states steps rule: size_ok'.induct)
  by auto

lemma size_ok'_decline: "size_ok' states x \<Longrightarrow> x \<ge> y \<Longrightarrow> size_ok' states y"
  apply(induction states x rule: size_ok'.induct)
  by auto

lemma remaining_steps_0: "invar states \<Longrightarrow> remaining_steps states = 0 \<Longrightarrow> remaining_steps (step states) = 0"
  apply(induction states rule: step.induct)
  by(auto simp: remaining_steps_step_0 Common_Proof.remaining_steps_step_0 split: current.splits Small.state.splits)

lemma remaining_steps_0': "invar states \<Longrightarrow> remaining_steps states = 0 \<Longrightarrow> remaining_steps ((step ^^ n) states) = 0"
proof(induction n arbitrary: states)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (metis States_Proof.invar_step funpow_simps_right(2) o_apply remaining_steps_0)
qed

lemma remaining_steps_decline_2: "invar states \<Longrightarrow> remaining_steps states > 0 \<Longrightarrow> remaining_steps states = Suc (remaining_steps (step states))"
proof(induction states rule: step.induct)
case (1 currentB big auxB currentS uu auxS)
  then show ?case 
    by(auto simp: max_def split: Big.state.splits Small.state.splits current.splits)
next
case ("2_1" v va vb vd right)
  then show ?case 
  proof(induction right)
    case (Reverse1 x1 x2 x3a)
    then show ?case 
      apply(auto split: current.splits)
      subgoal 
        apply(auto simp: max_def)
        apply (metis One_nat_def Stack_Proof.size_pop diff_Suc_eq_diff_pred diff_le_self le_add_diff_inverse le_diff_conv)
        apply(auto simp: reverseN_drop)
        by (smt (verit, del_insts) One_nat_def Stack_Proof.size_empty Stack_Proof.size_pop Suc_le_lessD diff_Suc_diff_eq1 diff_add_inverse2 diff_diff_left diff_is_0_eq le_add2 le_add_diff_inverse not_add_less1 plus_1_eq_Suc)
      done
  next
    case (Reverse2 x1 x2 x3a x4 x5)
    then show ?case by auto
  next
    case (Common x)
    then show ?case by auto
  qed
next
  case ("2_2" v right)
  then show ?case  
    apply(auto split: Big.state.splits Small.state.splits current.splits)
    using Common_Proof.remaining_steps_step_0 Common_Proof.remaining_steps_step apply fastforce
    using Stack_Proof.size_empty apply blast
    using Stack_Proof.size_not_empty apply blast 
    using Common_Proof.remaining_steps_step_0 Common_Proof.remaining_steps_step apply fastforce
    apply (metis (no_types, opaque_lifting) add.commute add_Suc_right diff_add_inverse2 max_0L max_Suc_Suc neq0_conv pop_list_length Common_Proof.remaining_steps_step_0 Common_Proof.remaining_steps_step Stack_Proof.size_list_length)
    apply (smt (z3) Common_Proof.remaining_steps_step Common_Proof.remaining_steps_step_0 add_Suc_right diff_add_inverse max_Suc_Suc max_def max_nat.neutr_eq_iff neq0_conv pop_list_length size_list_length)
    by (metis (no_types, opaque_lifting) max.commute max_0L max_Suc_Suc neq0_conv Common_Proof.remaining_steps_step_0 Common_Proof.remaining_steps_step)
next
  case ("2_3" left v va vb vc vd)
  then show ?case 
    apply(auto split: Big.state.splits Small.state.splits current.splits) 
    using Common_Proof.remaining_steps_step_0 Common_Proof.remaining_steps_step apply fastforce
    using Stack_Proof.size_empty apply blast
    using Stack_Proof.size_not_empty apply blast 
    using Common_Proof.remaining_steps_step_0 Common_Proof.remaining_steps_step apply fastforce
    apply (smt (z3) Common_Proof.remaining_steps_step Common_Proof.remaining_steps_step_0 Stack_Proof.size_pop Suc_pred add.commute add_Suc_right diff_add_inverse le_add1 le_add_same_cancel1 max_Suc_Suc max_def neq0_conv plus_1_eq_Suc)
    by (smt (z3) Common_Proof.remaining_steps_step Common_Proof.remaining_steps_step_0 Stack_Proof.size_not_empty Stack_Proof.size_pop Suc_pred add.commute add_Suc_right add_diff_cancel_right' max.commute max_0R max_Suc_Suc neq0_conv)
next
  case ("2_4" left v)
  then show ?case 
    apply(auto simp: max_def Big_Proof.remaining_steps_step Common_Proof.remaining_steps_step split: if_splits) 
    using remaining_steps_step_0 Big_Proof.remaining_steps_step apply fastforce
    by (metis Suc_leI le_imp_less_Suc not_le Common_Proof.remaining_steps_step_0 Common_Proof.remaining_steps_step zero_less_iff_neq_zero)
qed

lemma remaining_steps_decline: "invar states \<Longrightarrow> remaining_steps states \<ge> remaining_steps (step states)"
  by (metis gr_implies_not_zero le_imp_less_Suc less_not_refl3 linear neqE remaining_steps_decline_2 remaining_steps_0)

lemma remaining_steps_decline_3: "invar states \<Longrightarrow> Suc n < remaining_steps states \<Longrightarrow> n < remaining_steps (step states)"
  apply(induction n)
   apply (metis Suc_lessD gr_zeroI less_not_refl3 remaining_steps_decline_2)
  by (metis Suc_lessD Suc_lessE Suc_lessI dual_order.strict_implies_not_eq remaining_steps_decline_2 zero_less_Suc)

lemma remaining_steps_decline_5: "invar states \<Longrightarrow> remaining_steps states \<le> n \<Longrightarrow> remaining_steps ((step ^^ n) states) = 0"
proof(induction "remaining_steps states = 0")
  case True
  then show ?case 
    using remaining_steps_0'
    by auto
next
  case False
  then have  "0 < remaining_steps states" by auto

  with False show ?case
  proof(induction n arbitrary: states)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then show ?case
      using remaining_steps_decline_2[of states]
      by (metis (no_types, opaque_lifting) States_Proof.invar_step \<open>0 < States.remaining_steps states\<close> funpow_simps_right(2) neq0_conv not_less_eq_eq o_apply remaining_steps_0')
  qed
qed

lemma step_remaining_steps: "remaining_steps states \<ge> n \<Longrightarrow> invar states \<Longrightarrow> remaining_steps states = remaining_steps ((step^^n) states) + n" 
proof(induction n arbitrary: states)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    using remaining_steps_decline_2[of states] invar_step[of states]
    by (smt (verit, ccfv_SIG) Suc_le_mono add_Suc_right funpow_simps_right(2) le_zero_eq neq0_conv o_apply zero_less_Suc)
qed

lemma step_size_new_small: "invar (big, small)
  \<Longrightarrow> step (big, small) = (big', small')  
  \<Longrightarrow> Small.size_new small = Small.size_new small'"
proof(induction "(big, small)" rule: step.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by auto
next
  case ("2_1" v va vb vd)
  then show ?case by(auto split: Small.state.splits current.splits)
next
  case ("2_2" v)
  then show ?case by(auto simp: step_size_new split: Small.state.splits current.splits)
next
  case ("2_3" v va vb vc vd)
  then show ?case by(auto split: current.splits)
next
  case ("2_4" v)
  then show ?case by(auto simp: step_size_new)
qed

lemma step_size_new_big: "invar (big, small)
  \<Longrightarrow> step (big, small) = (big', small')  
  \<Longrightarrow> Big.size_new big = Big.size_new big'"
proof(induction "(big, small)" rule: step.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by(auto split: current.splits)
next
  case ("2_1" v va vb vd)
  then show ?case by(auto split: Small.state.splits current.splits)
next
  case ("2_2" v)
  then show ?case by(auto simp: step_size_new split: Small.state.splits current.splits)
next
  case ("2_3" v va vb vc vd)
  then show ?case by(auto simp: step_size_new split: current.splits split: Big.state.splits)
next
  case ("2_4" v)
  then show ?case by(auto simp: step_size_new split: Big.state.splits)
qed

lemma step_size_small: "invar (big, small)
  \<Longrightarrow> step (big, small) = (big', small')  
  \<Longrightarrow> Small.size small = Small.size small'"
proof(induction "(big, small)" rule: step.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by auto
next
  case ("2_1" v va vb vd)
  then show ?case by(auto split: Small.state.splits current.splits)
next
  case ("2_2" v)
  then show ?case by(auto simp: Common_Proof.step_size split: Small.state.splits current.splits)
next
  case ("2_3" v va vb vc vd)
  then show ?case by(auto split: current.splits)
next
  case ("2_4" v)
  then show ?case by(auto simp: Common_Proof.step_size)
qed

lemma step_size_big: "invar (big, small)
  \<Longrightarrow> step (big, small) = (big', small')  
  \<Longrightarrow> Big.size big = Big.size big'"
proof(induction "(big, small)" rule: step.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by(auto split: current.splits)
next
  case ("2_1" v va vb vd)
  then show ?case by(auto split: Small.state.splits current.splits)
next
  case ("2_2" v)
  then show ?case by(auto simp: Common_Proof.step_size split: Small.state.splits current.splits)
next
  case ("2_3" v va vb vc vd)
  then show ?case by(auto simp: Common_Proof.step_size split: current.splits Big.state.splits)
next
  case ("2_4" v)
  then show ?case by(auto simp: Common_Proof.step_size split: Big.state.splits)
qed

lemma step_size_ok_1: "invar (big, small) \<Longrightarrow> step (big, small) = (big', small')
  \<Longrightarrow> Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small
  \<Longrightarrow> Big.size_new big' + remaining_steps (big', small') + 2 \<le> 3 * Small.size_new small'"
  using remaining_steps_decline step_size_new_small step_size_new_big
  by fastforce

lemma step_size_ok_2: "invar (big, small) \<Longrightarrow> step (big, small) = (big', small')
  \<Longrightarrow> Small.size_new small + remaining_steps (big, small) + 2 \<le> 3 * Big.size_new big
  \<Longrightarrow> Small.size_new small' + remaining_steps (big', small') + 2 \<le> 3 * Big.size_new big'"
  using remaining_steps_decline step_size_new_small step_size_new_big
  by fastforce

lemma step_size_ok_3: "invar (big, small) \<Longrightarrow> step (big, small) = (big', small')
  \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Small.size small
  \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Small.size small'"
using remaining_steps_decline step_size_small
  by fastforce

lemma step_size_ok_4: "invar (big, small) \<Longrightarrow> step (big, small) = (big', small')
  \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Big.size big
  \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Big.size big'"
using remaining_steps_decline step_size_big
  by fastforce

lemma step_size_ok: "invar states \<Longrightarrow> size_ok states \<Longrightarrow> size_ok (step states)"
  using step_size_ok_1 step_size_ok_2 step_size_ok_3 step_size_ok_4
  by (smt (z3) size_ok'.elims(1) size_ok.elims(1))

lemma remaining_steps_4: "invar states \<Longrightarrow> remaining_steps states = steps \<Longrightarrow> steps \<ge> 4 
  \<Longrightarrow> remaining_steps ((step ^^ 4) states) = steps - 4"
  by (metis diff_add_inverse2 step_remaining_steps)

lemma step_push_size_new_small: "invar (big, small) 
          \<Longrightarrow> step (big, Small.push x small) = (big', small')
          \<Longrightarrow> Small.size_new small' = Suc (Small.size_new small)"
  using 
    invar_push_small[of big small x]
    step_size_new_small[of big "Small.push x small" big' small']
    size_new_push[of small x]
  by simp

lemma step_push_size_small: "invar (big, small) 
          \<Longrightarrow> step (big, Small.push x small) = (big', small')
          \<Longrightarrow> Small.size small' = Suc (Small.size small)"
  using 
    invar_push_small[of big small x]
    step_size_small[of big "Small.push x small" big' small']
    size_push[of small x]
  by simp

lemma step_push_size_new_big: "invar (big, small) 
          \<Longrightarrow> step (Big.push x big, small) = (big', small')
          \<Longrightarrow> Big.size_new big' = Suc (Big.size_new big)"
  using 
    invar_push_big[of big small x] 
    step_size_new_big[of "Big.push x big" small big' small']
    Big_Proof.size_new_push[of big x]
  by auto

lemma step_pop_size_big: "invar (big, small) 
          \<Longrightarrow> 0 < Big.size big 
          \<Longrightarrow> Big.pop big = (x, bigP) 
          \<Longrightarrow> step (bigP, small) = (big', small')
          \<Longrightarrow> Big.size big = Suc (Big.size big')"
  using 
    invar_pop_big_size[of big small x bigP] 
    step_size_big[of bigP small big' small']  
    Big_Proof.size_pop[of big]
  by auto

lemma step_pop_size_new_big: "invar (big, small) 
          \<Longrightarrow> 0 < Big.size big 
          \<Longrightarrow> Big.pop big = (x, bigP) 
          \<Longrightarrow> step (bigP, small) = (big', small')
          \<Longrightarrow> Big.size_new big = Suc (Big.size_new big')"
  using 
    invar_pop_big_size[of big small x bigP] 
    Big_Proof.size_size_new[of big]
    step_size_new_big[of bigP small big' small']  
    Big_Proof.size_new_pop[of big]
  by auto

lemma step_push_size_big: "invar (big, small) 
          \<Longrightarrow> step (Big.push x big, small) = (big', small')
          \<Longrightarrow> Big.size big' = Suc (Big.size big)"
  using 
    invar_push_big[of big small x]
    Big_Proof.size_push[of big]
    step_size_big[of "Big.push x big" small big' small']
  by auto

lemma step_n_size_small: "invar (big, small) 
          \<Longrightarrow> (step ^^ n) (big, small) = (big', small')
          \<Longrightarrow> Small.size small' =  Small.size small"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have invar1: "invar (step (big, small))"
    using invar_step 
    by blast

  then obtain big1 small1 where step: "step (big, small) = (big1, small1)"
    by auto

  with step_size_small invar1 have "Small.size small = Small.size small1"
    by (metis Suc.prems(1))


  then have n_steps: "(step ^^ n) (big1, small1) = (big', small')"
    using Suc 
    by (metis \<open>States.step (big, small) = (big1, small1)\<close> funpow_simps_right(2) o_apply)

  have invar2: "invar (big1, small1)" using step invar1 by auto

  from Suc n_steps invar2 have "Small.size small' = Small.size small1"
    by auto


  with Suc show ?case
    using \<open>Small.size small = Small.size small1\<close> by presburger
qed

lemma step_n_size_big: "invar (big, small) 
          \<Longrightarrow> (step ^^ n) (big, small) = (big', small')
          \<Longrightarrow> Big.size big' = Big.size big"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have invar1: "invar (step (big, small))"
    using invar_step 
    by blast

  then obtain big1 small1 where step: "step (big, small) = (big1, small1)"
    by auto

  with invar1 have "Big.size big = Big.size big1"
    by (metis Suc.prems(1) step_size_big)


  then have n_steps: "(step ^^ n) (big1, small1) = (big', small')"
    using Suc 
    by (metis \<open>States.step (big, small) = (big1, small1)\<close> funpow_simps_right(2) o_apply)

  have invar2: "invar (big1, small1)" using step invar1 by auto

  from Suc n_steps invar2 have "Big.size big' = Big.size big1"
    by auto


  with Suc show ?case
    using \<open>Big.size big = Big.size big1\<close> by presburger
qed

lemma step_n_size_new_small: "invar (big, small) 
          \<Longrightarrow> (step ^^ n) (big, small) = (big', small')
          \<Longrightarrow> Small.size_new small' =  Small.size_new small"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have invar1: "invar (step (big, small))"
    using invar_step 
    by blast

  then obtain big1 small1 where step: "step (big, small) = (big1, small1)"
    by auto

  with step_size_new_small invar1 have "Small.size_new small = Small.size_new small1"
    by (metis Suc.prems(1))

  then have n_steps: "(step ^^ n) (big1, small1) = (big', small')"
    using Suc 
    by (metis \<open>States.step (big, small) = (big1, small1)\<close> funpow_simps_right(2) o_apply)

  have invar2: "invar (big1, small1)" using step invar1 by auto

  from Suc n_steps invar2 have "Small.size_new small' = Small.size_new small1"
    by auto


  with Suc show ?case
    using \<open>Small.size_new small = Small.size_new small1\<close> by presburger
qed

lemma step_n_size_new_big: "invar (big, small) 
          \<Longrightarrow> (step ^^ n) (big, small) = (big', small')
          \<Longrightarrow> Big.size_new big' =  Big.size_new big"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have invar1: "invar (step (big, small))"
    using invar_step 
    by blast

  then obtain big1 small1 where step: "step (big, small) = (big1, small1)"
    by auto

  with step_size_new_big invar1 have "Big.size_new big = Big.size_new big1"
    by (metis Suc.prems(1))


  then have n_steps: "(step ^^ n) (big1, small1) = (big', small')"
    using Suc 
    by (metis \<open>States.step (big, small) = (big1, small1)\<close> funpow_simps_right(2) o_apply)

  have invar2: "invar (big1, small1)" using step invar1 by auto

  from Suc n_steps invar2 have "Big.size_new big' = Big.size_new big1"
    by auto

  with Suc show ?case
    using \<open>Big.size_new big = Big.size_new big1\<close> by presburger
qed

lemma step_n_push_size_small: "invar (big, small) 
          \<Longrightarrow> (step ^^ n) (big, Small.push x small) = (big', small')
          \<Longrightarrow> Small.size small' = Suc (Small.size small)"
  by (metis invar_push_small old.prod.exhaust step_push_size_small step_n_size_small step_size_small)

lemma step_n_push_size_new_small: "invar (big, small) 
          \<Longrightarrow> (step ^^ n) (big, Small.push x small) = (big', small')
          \<Longrightarrow> Small.size_new small' = Suc (Small.size_new small)"
  by (metis invar_push_small old.prod.exhaust step_push_size_new_small step_n_size_new_small step_size_new_small)

lemma step_n_push_size_big: "invar (big, small) 
          \<Longrightarrow> (step ^^ n) (Big.push x big, small) = (big', small')
          \<Longrightarrow> Big.size big' = Suc (Big.size big)"
  by (metis invar_push_big old.prod.exhaust step_push_size_big step_n_size_big step_size_big)

lemma step_n_push_size_new_big: "invar (big, small) 
          \<Longrightarrow> (step ^^ n) (Big.push x big, small) = (big', small')
          \<Longrightarrow> Big.size_new big' = Suc (Big.size_new big)"
  by (metis invar_push_big old.prod.exhaust step_push_size_new_big step_n_size_new_big step_size_new_big)

lemma step_n_pop_size_small: "invar (big, small) 
          \<Longrightarrow> 0 < Small.size small 
          \<Longrightarrow> Small.pop small = (x, smallP) 
          \<Longrightarrow> (step ^^ n) (big, smallP) = (big', small')
          \<Longrightarrow> Small.size small = Suc (Small.size small')"
  using invar_pop_small_size size_pop step_n_size_small by fastforce

lemma step_n_pop_size_new_small: "invar (big, small) 
          \<Longrightarrow> 0 < Small.size small 
          \<Longrightarrow> Small.pop small = (x, smallP) 
          \<Longrightarrow> (step ^^ n) (big, smallP) = (big', small')
          \<Longrightarrow> Small.size_new small = Suc (Small.size_new small')"
  using invar_pop_small_size size_new_pop step_n_size_new_small size_size_new by fastforce

lemma step_n_pop_size_big: "invar (big, small) 
          \<Longrightarrow> 0 < Big.size big 
          \<Longrightarrow> Big.pop big = (x, bigP) 
          \<Longrightarrow> (step ^^ n) (bigP, small) = (big', small')
          \<Longrightarrow> Big.size big = Suc (Big.size big')"
  using invar_pop_big_size Big_Proof.size_pop step_n_size_big by fastforce

lemma step_n_pop_size_new_big: "invar (big, small) 
          \<Longrightarrow> 0 < Big.size big 
          \<Longrightarrow> Big.pop big = (x, bigP) 
          \<Longrightarrow> (step ^^ n) (bigP, small) = (big', small')
          \<Longrightarrow> Big.size_new big = Suc (Big.size_new big')"
  by (metis (no_types, opaque_lifting) States.remaining_steps.cases invar_pop_big_size step_pop_size_new_big step_size_new_big step_n_size_new_big)

lemma remaining_steps_push_small: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) = remaining_steps (big, Small.push x small)"
proof(induction x small rule: Small.push.induct)
  case (1 x state)
  then show ?case 
    apply(auto simp: max_def Common_Proof.remaining_steps_push)
    by (metis Common_Proof.remaining_steps_push)+
next
  case (2 x current small auxS)
  then show ?case 
  proof(induction x current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case by auto
  qed
next
  case (3 x current auxS big newS count)
  then show ?case
  proof(induction x current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case by auto
  qed
qed    

lemma remaining_steps_pop_small: "
          invar (big, small)
     \<Longrightarrow> 0 < Small.size small 
     \<Longrightarrow> Small.pop small = (x, smallP) 
     \<Longrightarrow> remaining_steps (big, small) \<ge> remaining_steps (big, smallP)"
proof(induction small rule: Small.pop.induct)
  case (1 state)
  then show ?case apply(auto simp: max_def Common_Proof.remaining_steps_pop split: prod.splits)
    using Common_Proof.remaining_steps_pop by fastforce 
next
  case (2 current small auxS)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      by(auto split: Big.state.splits) 
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case (3 current auxS big newS count)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma remaining_steps_pop_big: "
      invar (big, small)
       \<Longrightarrow> 0 < Big.size big 
       \<Longrightarrow> Big.pop big = (x, bigP) 
       \<Longrightarrow> remaining_steps (big, small) \<ge> remaining_steps (bigP, small)"
proof(induction big rule: Big.pop.induct)
  case (1 state)
  then show ?case 
  proof(induction state rule: Common.pop.induct)
    case (1 current idle)
    then show ?case 
    proof(induction idle rule: Idle.pop.induct)
      case (1 stack stackSize)
      then show ?case 
      proof(induction current rule: Current.pop.induct)
        case (1 added old remained)
        then show ?case by(auto split: Small.state.splits)
      next
        case (2 x xs added old remained)
        then show ?case by(auto split: Small.state.splits)
      qed
    qed
  next
    case (2 current aux new moved)
    then show ?case 
    proof(induction current rule: Current.pop.induct)
      case (1 added old remained)
      then show ?case by(auto split: Small.state.splits)
    next
      case (2 x xs added old remained)
      then show ?case by(auto split: Small.state.splits)
    qed
  qed
next
  case (2 current big aux count)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case by(auto split: Small.state.splits current.splits)
  next
    case (2 x xs added old remained)
    then show ?case by(auto split: Small.state.splits current.splits)
  qed
qed

lemma remaining_steps_push_big: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) = remaining_steps (Big.push x big, small)"
proof(induction x big rule: Big.push.induct)
  case (1 x state)
  then show ?case 
    apply(auto simp: max_def Common_Proof.remaining_steps_push split: Small.state.splits)
    using Common_Proof.remaining_steps_push by fastforce+
next
  case (2 x current big aux count)
  then show ?case
  proof(induction current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case 
      apply(auto split: Small.state.splits)
      by (metis Big.state.simps(5))
  qed
qed

lemma step_4_remaining_steps_pop_small: "invar (big, small)
      \<Longrightarrow> 0 < Small.size small 
      \<Longrightarrow> Small.pop small = (x, smallP) 
       \<Longrightarrow> remaining_steps (big, smallP) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, smallP)) = (big', small')
       \<Longrightarrow> remaining_steps (big', small') \<le> remaining_steps (big, small) - 4"
  by (metis diff_le_mono invar_pop_small_size remaining_steps_4 remaining_steps_pop_small)

lemma step_4_remaining_steps_push_big: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow> remaining_steps (big', small') = remaining_steps (big, small) - 4"
  by (metis invar_push_big remaining_steps_4 remaining_steps_push_big)

lemma step_4_remaining_steps_push_small: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow> remaining_steps (big', small') = remaining_steps (big, small) - 4"
  by (metis invar_push_small remaining_steps_4 remaining_steps_push_small)

lemma step_4_remaining_steps_pop_big: "invar (big, small)
       \<Longrightarrow> 0 < Big.size big 
       \<Longrightarrow> Big.pop big = (x, bigP) 
       \<Longrightarrow> remaining_steps (bigP, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (bigP, small)) = (big', small')
       \<Longrightarrow> remaining_steps (big', small') \<le> remaining_steps (big, small) - 4"
  by (metis add_le_imp_le_diff invar_pop_big_size remaining_steps_pop_big step_remaining_steps)

lemma step_4_pop_small_size_ok': "
            0 < Small.size small 
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> (remaining_steps (big, small) - 4) + 1 \<le> 4 * (Small.size small - 1)"
  by linarith

lemma step_4_pop_small_size_ok_1: "invar (big, small)
       \<Longrightarrow> 0 < Small.size small 
       \<Longrightarrow> Small.pop small = (x, smallP)
       \<Longrightarrow> remaining_steps (big, smallP) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, smallP)) = (big', small')
       \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Small.size small'"
  using step_4_pop_small_size_ok' remaining_steps_4 step_n_pop_size_small remaining_steps_pop_small
  by (smt (verit, ccfv_SIG) Suc_diff_1 Suc_inject add_le_cancel_right order_trans step_4_remaining_steps_pop_small)

lemma step_4_pop_big_size_ok_1: "invar (big, small)
       \<Longrightarrow> 0 < Big.size big 
       \<Longrightarrow> Big.pop big = (x, bigP) 
       \<Longrightarrow> remaining_steps (bigP, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (bigP, small)) = (big', small')
       \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Small.size small'"
  by (metis (no_types, lifting) add_leD1 add_mono_thms_linordered_semiring(3) invar_pop_big_size order.trans step_n_size_small remaining_steps_pop_big step_remaining_steps)

lemma step_4_pop_small_size_ok_2: "invar (big, small)
       \<Longrightarrow> 0 < Small.size small 
       \<Longrightarrow> Small.pop small = (x, smallP)
       \<Longrightarrow> remaining_steps (big, smallP) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, smallP)) = (big', small')
       \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Big.size big
       \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Big.size big'"
  by (smt (z3) add.commute add_leE invar_pop_small_size le_add_diff_inverse2 nat_add_left_cancel_le remaining_steps_4 step_n_size_big remaining_steps_pop_small)

lemma step_4_pop_big_size_ok_2: 
  assumes
    "invar (big, small)"
    "0 < Big.size big"
    "Big.pop big = (x, bigP)"
    "remaining_steps (bigP, small) \<ge> 4"
    "((step ^^ 4) (bigP, small)) = (big', small')"
    "remaining_steps (big, small) + 1 \<le> 4 * Big.size big"
  shows
    "remaining_steps (big', small') + 1 \<le> 4 * Big.size big'"
proof -
  from assms have "remaining_steps (bigP, small) + 1 \<le> 4 * Big.size big"
    by (meson add_le_cancel_right order.trans remaining_steps_pop_big)

  with assms show ?thesis
    by (smt (z3) Suc_diff_le Suc_eq_plus1 add_mult_distrib2 diff_diff_add diff_is_0_eq invar_pop_big_size mult_numeral_1_right numerals(1) plus_1_eq_Suc remaining_steps_4 step_n_pop_size_big)
qed

lemma step_4_pop_small_size_ok_3: "invar (big, small)
       \<Longrightarrow> 0 < Small.size small 
       \<Longrightarrow> Small.pop small = (x, smallP)
       \<Longrightarrow> remaining_steps (big, smallP) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, smallP)) = (big', small')
       \<Longrightarrow>  Small.size_new small + remaining_steps (big, small) + 2 \<le> 3 * Big.size_new big
       \<Longrightarrow>  Small.size_new small' + remaining_steps (big', small') + 2 \<le> 3 * Big.size_new big'"
  by (smt (verit, best) add_le_mono diff_Suc_1 diff_le_self dual_order.eq_iff invar_pop_small_size nat_less_le order.trans remaining_steps_4 step_n_size_new_big step_n_pop_size_new_small remaining_steps_pop_small)

lemma step_4_pop_big_size_ok_3': "
            0 < Big.size big 
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow>  Small.size_new small + remaining_steps (big, small) + 2 \<le> 3 * Big.size_new big
       \<Longrightarrow> Small.size_new small + (remaining_steps (big, small) - 4) + 2 \<le> 3 * (Big.size_new big - 1)"
  by linarith

lemma step_4_pop_big_size_ok_3: 
    assumes
      "invar (big, small)"
      "0 < Big.size big" 
      "Big.pop big = (x, bigP) "
      "remaining_steps (bigP, small) \<ge> 4"
      "((step ^^ 4) (bigP, small)) = (big', small')"
      "Small.size_new small + remaining_steps (big, small) + 2 \<le> 3 * Big.size_new big"
    shows
      "Small.size_new small' + remaining_steps (big', small') + 2 \<le> 3 * Big.size_new big'"
proof-
  from assms have "Small.size_new small + (remaining_steps (big, small) - 4) + 2 \<le> 3 * (Big.size_new big - 1)"
    by (meson dual_order.trans remaining_steps_pop_big step_4_pop_big_size_ok_3')

  then have  "Small.size_new small + remaining_steps (big', small') + 2 \<le> 3 * (Big.size_new big - 1)"
    by (smt (verit, ccfv_SIG) add_le_mono assms(1) assms(2) assms(3) assms(4) assms(5) dual_order.trans le_antisym less_or_eq_imp_le nat_less_le step_4_remaining_steps_pop_big)

  with assms show ?thesis 
    by (metis diff_Suc_1 invar_pop_big_size step_n_size_new_small step_n_pop_size_new_big)
qed

lemma step_4_pop_small_size_ok_4': "
            0 < Small.size small 
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small
       \<Longrightarrow> Big.size_new big + (remaining_steps (big, small) - 4) + 2 \<le> 3 * (Small.size_new small - 1)"
  by linarith

lemma step_4_pop_small_size_ok_4:
    assumes
      "invar (big, small)"
      "0 < Small.size small"
      "Small.pop small = (x, smallP)"
      "remaining_steps (big, smallP) \<ge> 4"
      "((step ^^ 4) (big, smallP)) = (big', small')"
      "Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small"
    shows
       "Big.size_new big' + remaining_steps (big', small') + 2 \<le> 3 * Small.size_new small'"
proof-
  from assms step_4_pop_small_size_ok_4' have  "Big.size_new big + (remaining_steps (big, small) - 4) + 2 \<le> 3 * (Small.size_new small - 1)"
    by (smt (verit, best) add_leE le_add_diff_inverse remaining_steps_pop_small)

  with assms have "Big.size_new big + remaining_steps (big', small') + 2 \<le> 3 * (Small.size_new small - 1)"
    by (meson add_le_mono le_refl order_trans step_4_remaining_steps_pop_small)

  with assms show ?thesis 
    by (metis diff_Suc_1 invar_pop_small_size step_n_size_new_big step_n_pop_size_new_small)
qed

lemma step_4_pop_big_size_ok_4': "
           0 < Big.size big 
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow>  Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small
       \<Longrightarrow>  (Big.size_new big - 1) + (remaining_steps (big, small) - 4) + 2 \<le> 3 * Small.size_new small"
  by linarith

lemma step_4_pop_big_size_ok_4: 
  assumes
    "invar (big, small)"
    "0 < Big.size big "
    "Big.pop big = (x, bigP)"
    "remaining_steps (bigP, small) \<ge> 4"
    "((step ^^ 4) (bigP, small)) = (big', small')"
    "Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small"
  shows
    "Big.size_new big' + remaining_steps (big', small') + 2 \<le> 3 * Small.size_new small'"
proof -
  from assms step_4_pop_big_size_ok_4' 
  have "(Big.size_new big - 1) + (remaining_steps (big, small) - 4) + 2 \<le> 3 * Small.size_new small"
    by linarith

  with assms have  "(Big.size_new big - 1) + remaining_steps (big', small') + 2 \<le> 3 * Small.size_new small"
    by (meson add_le_mono dual_order.eq_iff order_trans step_4_remaining_steps_pop_big)

  with assms show ?thesis 
    by (metis diff_Suc_1 invar_pop_big_size step_n_size_new_small step_n_pop_size_new_big)
qed

lemma step_4_push_small_size_ok_1: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Small.size small'"
  by (smt (z3) add.commute add_leD1 add_le_mono le_add1 le_add_diff_inverse2 mult_Suc_right nat_1_add_1 numeral_Bit0 step_n_push_size_small step_4_remaining_steps_push_small)

lemma step_4_push_big_size_ok_1: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Small.size small'"
  by (metis (full_types) Suc_diff_le add.commute invar_push_big less_Suc_eq_le less_imp_diff_less plus_1_eq_Suc step_n_size_small step_4_remaining_steps_push_big)

lemma step_4_push_small_size_ok_2: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Big.size big
       \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Big.size big'"
  by (metis (full_types) Suc_diff_le add.commute invar_push_small less_Suc_eq_le less_imp_diff_less plus_1_eq_Suc step_n_size_big step_4_remaining_steps_push_small)

lemma step_4_push_big_size_ok_2: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow> remaining_steps (big, small) + 1 \<le> 4 * Big.size big
       \<Longrightarrow> remaining_steps (big', small') + 1 \<le> 4 * Big.size big'"
  by (smt (z3) Suc_diff_le Suc_eq_plus1 less_Suc_eq_le less_imp_diff_less mult.commute mult_Suc step_n_push_size_big step_4_remaining_steps_push_big trans_le_add2)

lemma step_4_push_small_size_ok_3': "
            remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> Small.size_new small + remaining_steps (big, small) + 2 \<le> 3 * Big.size_new big
       \<Longrightarrow> (Suc (Small.size_new small)) + (remaining_steps (big, small) - 4) + 2 \<le> 3 * Big.size_new big"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma step_4_push_small_size_ok_3: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow>  Small.size_new small + remaining_steps (big, small) + 2 \<le> 3 * Big.size_new big
       \<Longrightarrow>  Small.size_new small' + remaining_steps (big', small') + 2 \<le> 3 * Big.size_new big'"
  using step_n_size_new_big step_n_push_size_new_small step_4_remaining_steps_push_small
  by (metis invar_push_small step_4_push_small_size_ok_3')

lemma step_4_push_big_size_ok_3': "
            remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> Small.size_new small + remaining_steps (big, small) + 2 \<le> 3 * Big.size_new big
       \<Longrightarrow> Small.size_new small + (remaining_steps (big, small) - 4) + 2 \<le> 3 * (Suc (Big.size_new big))"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma step_4_push_big_size_ok_3: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow>  Small.size_new small + remaining_steps (big, small) + 2 \<le> 3 * Big.size_new big
       \<Longrightarrow>  Small.size_new small' + remaining_steps (big', small') + 2 \<le> 3 * Big.size_new big'"
  by (metis invar_push_big step_n_size_new_small step_n_push_size_new_big step_4_remaining_steps_push_big step_4_push_big_size_ok_3')

lemma step_4_push_small_size_ok_4': "
            remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small
       \<Longrightarrow> Big.size_new big + (remaining_steps (big, small) - 4) + 2 \<le> 3 * (Suc (Small.size_new small))"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma step_4_push_small_size_ok_4: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow>  Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small
       \<Longrightarrow>  Big.size_new big' + remaining_steps (big', small') + 2 \<le> 3 * Small.size_new small'"
  by (metis invar_push_small step_n_size_new_big step_n_push_size_new_small step_4_remaining_steps_push_small step_4_push_small_size_ok_4')

lemma step_4_push_big_size_ok_4': "
            remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small
       \<Longrightarrow> (Suc (Big.size_new big)) + (remaining_steps (big, small) - 4) + 2 \<le> 3 * Small.size_new small"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma step_4_push_big_size_ok_4: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> ((step ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow>  Big.size_new big + remaining_steps (big, small) + 2 \<le> 3 * Small.size_new small
       \<Longrightarrow>  Big.size_new big' + remaining_steps (big', small') + 2 \<le> 3 * Small.size_new small'"
  by (metis invar_push_big step_n_size_new_small step_n_push_size_new_big step_4_remaining_steps_push_big step_4_push_big_size_ok_4')

lemma step_4_push_small_size_ok: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> size_ok (big, small)
       \<Longrightarrow> size_ok ((step ^^ 4) (big, Small.push x small))"
  using step_4_push_small_size_ok_1 step_4_push_small_size_ok_2 step_4_push_small_size_ok_3 step_4_push_small_size_ok_4 
  by (smt (verit) size_ok'.elims(3) size_ok'.simps size_ok.elims(2) size_ok.elims(3))

lemma step_4_push_big_size_ok: "invar (big, small)
       \<Longrightarrow> remaining_steps (big, small) \<ge> 4
       \<Longrightarrow> size_ok (big, small)
       \<Longrightarrow> size_ok ((step ^^ 4) (Big.push x big, small))"
  using step_4_push_big_size_ok_1 step_4_push_big_size_ok_2 step_4_push_big_size_ok_3 step_4_push_big_size_ok_4
  by (smt (verit) size_ok'.elims(3) size_ok'.simps size_ok.elims(2) size_ok.elims(3))

lemma step_4_pop_small_size_ok: "invar (big, small)
       \<Longrightarrow> 0 < Small.size small 
       \<Longrightarrow> Small.pop small = (x, smallP)
       \<Longrightarrow> remaining_steps (big, smallP) \<ge> 4
       \<Longrightarrow> size_ok (big, small)
       \<Longrightarrow> size_ok ((step ^^ 4) (big, smallP))"
  using step_4_pop_small_size_ok_1 step_4_pop_small_size_ok_2 step_4_pop_small_size_ok_3 step_4_pop_small_size_ok_4 
  by (smt (verit) size_ok'.elims(3) size_ok'.simps size_ok.elims(2) size_ok.elims(3))

lemma step_4_pop_big_size_ok: "invar (big, small)
       \<Longrightarrow> 0 < Big.size big 
       \<Longrightarrow> Big.pop big = (x, bigP) 
       \<Longrightarrow> remaining_steps (bigP, small) \<ge> 4
       \<Longrightarrow> size_ok (big, small)
       \<Longrightarrow> size_ok ((step ^^ 4) (bigP, small))"
  using step_4_pop_big_size_ok_1 step_4_pop_big_size_ok_2 step_4_pop_big_size_ok_3 step_4_pop_big_size_ok_4
  by (smt (verit) size_ok'.elims(3) size_ok'.simps size_ok.elims(2) size_ok.elims(3))

lemma size_ok_size_small: "size_ok (big, small) \<Longrightarrow> 0 < Small.size small"
  apply(induction small arbitrary: big)
  by auto

lemma size_ok_size_big: "size_ok (big, small) \<Longrightarrow> 0 < Big.size big"
  apply(induction big arbitrary: small)
  by auto

lemma size_ok_size_new_small: "size_ok (big, small) \<Longrightarrow> 0 < Small.size_new small"
  apply(induction small arbitrary: big)
  by auto

lemma size_ok_size_new_big: "size_ok (big, small) \<Longrightarrow> 0 < Big.size_new big"
  apply(induction big arbitrary: small)
  by auto

lemma remaining_steps_step_n: "invar states \<Longrightarrow>  n < remaining_steps states 
    \<Longrightarrow>  remaining_steps states - n = remaining_steps ((step ^^ n) states)"
  by (metis diff_add_inverse2 less_or_eq_imp_le step_remaining_steps)

lemma step_size_ok': "invar states \<Longrightarrow>
    size_ok' states x \<Longrightarrow> 
    size_ok' (step states) x"
proof(induction states x rule: size_ok'.induct)
  case (1 big small steps)
  then show ?case 
    using step_size_new_big[of big small] step_size_new_small[of big small] step_size_big[of big small] step_size_small[of big small]
    apply(auto split: )
  proof -
    assume a1: "\<And>big' small'. States.step (big, small) = (big', small') \<Longrightarrow> Big.size_new big = Big.size_new big'"
    assume a2: "\<And>big' small'. States.step (big, small) = (big', small') \<Longrightarrow> Small.size_new small = Small.size_new small'"
    assume a3: "\<And>big' small'. States.step (big, small) = (big', small') \<Longrightarrow> Big.size big = Big.size big'"
    assume a4: "\<And>big' small'. States.step (big, small) = (big', small') \<Longrightarrow> Small.size small = Small.size small'"
    assume a5: "Suc (Suc (Small.size_new small + steps)) \<le> 3 * Big.size_new big"
    assume a6: "Suc (Suc (Big.size_new big + steps)) \<le> 3 * Small.size_new small"
    assume a7: "Suc steps \<le> 4 * Small.size small"
    assume a8: "Suc steps \<le> 4 * Big.size big"
  
      have "\<forall>p n. (\<exists>s sa. (\<not> n + 1 \<le> 4 * Big.size (s::'a Big.state) \<or> \<not> n + 1 \<le> 4 * Small.size sa \<or> \<not> Big.size_new s + n + 2 \<le> 3 * Small.size_new sa \<or> \<not> Small.size_new sa + n + 2 \<le> 3 * Big.size_new s) \<and> (s, sa) = p) \<or> size_ok' p n"
        by simp
      then show ?thesis
        using a8 a7 a6 a5 a4 a3 a2 a1 by (smt (z3) Suc_1 Suc_eq_plus1 add_Suc_shift)
    qed
qed

  
end
