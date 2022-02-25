theory States_Proof
  imports States Big_Proof Small_Proof HOL.Real Complex_Main
begin

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits
lemmas invariant_ticks = Big_Proof.invariant_tick Common_Proof.invariant_tick Small_Proof.invariant_tick

lemma invariant_listBigFirst: "invariant states \<Longrightarrow> toListBigFirst states = toCurrentListBigFirst states"
  apply(auto split: prod.splits)
  by (metis rev_append rev_rev_ident)

lemma tick_toList: "invariant states \<Longrightarrow> toList (tick states) = toList states"
proof(induction states rule: toList.induct)
  case (1 currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction "(Reverse currentB big auxB count, Reverse1 currentS small auxS)" rule: States.tick.induct)
    case 1
    then show ?case 
    proof(induction currentB)
      case (Current extra added old remained)
      then show ?case by auto
    qed
  next
    case ("2_1" count')
    then show ?case 
      using Big_Proof.tick_toList[of "Reverse currentB big auxB count"]
      apply auto
      apply (metis (no_types, lifting) funpow_swap1 less_eq_nat.simps(1) list.size(3) reverseN_take take_all toList_isEmpty)
      by (metis (no_types, lifting) first_pop funpow_swap1 reverseN.simps(3))
  qed
next
  case ("2_1" common small)
  then show ?case 
    using Small_Proof.tick_toList_reverse2[of small]
    by(auto simp: Common_Proof.tick_toList split: Small.state.splits)
next
  case ("2_2" big current auxS big newS count)
  then show ?case 
    using 
      Small_Proof.tick_toList_reverse2[of "Reverse2 current auxS big newS count"]
      Big_Proof.tick_toList
    by auto
next
  case ("2_3" big common)
  then show ?case 
    by(auto simp: Big_Proof.tick_toList Common_Proof.tick_toList)
qed
  
lemma tick_toCurrentList: "invariant states \<Longrightarrow> toCurrentList (tick states) = toCurrentList states"
proof(induction states rule: tick.induct)
  case (1 currentB big auxB currentS small auxS)
  then show ?case 
    by(auto split: current.splits)
next
  case ("2_1" current big auxB count small)
  then show ?case
    by(auto simp: Common_Proof.tick_toCurrentList split: current.splits prod.splits Small.state.splits)
next
  case ("2_2" common small)
  then show ?case 
    by(auto simp: Common_Proof.tick_toCurrentList  split: Small.state.splits current.splits)
next
  case ("2_3" big current auxS big new count)
  then show ?case
    by(auto simp: Big_Proof.tick_toCurrentList split: current.splits)
next
  case ("2_4" big common)
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
      by(auto simp: Common_Proof.push_toList)
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
      by(auto simp: Common_Proof.push_toList)
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
      by(auto simp: Common_Proof.push_toList)
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


lemma smart: "toListSmallFirst (big, small) = toCurrentListSmallFirst (big, small) \<longleftrightarrow>
              toListBigFirst (big, small) = toCurrentListBigFirst (big, small)"
  apply(auto split: prod.splits)
  by (metis rev_append rev_rev_ident)+


lemma invariant_pop_big_size_1: "\<lbrakk>
  invariant (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow>  Big.invariant big'  \<and> Small.invariant small"
  by(auto simp: Big_Proof.invariant_pop_2)

lemma invariant_pop_big_size_2_1_1: "\<lbrakk>
  invariant (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> tl (toListBigFirst (big, small)) = toListBigFirst (big', small)"
proof(induction "(big, small)" rule: toList.induct)
  case (1 currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction currentB rule: get.induct)
    case (1 added old remained)
    then show ?case
    proof(induction  "(Reverse2 currentS (drop (List.length (Stack.toList small) - count) (rev (Stack.toList small)) @ auxS) ((Stack.pop ^^ count) big) [] 0)" rule: Small.toList.induct)
      case (2 extra uu uv remained')
      then show ?case   
        apply(auto simp: reverseN_take)
      proof(induction "rev (take (remained - min (List.length (Stack.toList big)) count) auxB) = []")
        case True
        then show ?case apply auto 
           apply (smt (z3) Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc length_rev length_take min.absorb2 neq0_conv rev_is_Nil_conv rev_take Stack_Proof.size_isNotEmpty Stack_Proof.size_listLength take_eq_Nil tl_append2 tl_drop Stack_Proof.toList_isNotEmpty) 
          by (smt (z3) Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc length_rev length_take min.absorb2 neq0_conv rev_take Stack_Proof.size_isNotEmpty Stack_Proof.size_listLength take_eq_Nil tl_append2 tl_drop Stack_Proof.toList_isNotEmpty)
      next
        case False
        then show ?case apply auto 
           apply (smt (verit, best) False.prems(4) Suc_diff_eq_diff_pred Suc_diff_le diff_add_inverse diff_is_0_eq drop_Suc length_rev length_take min.absorb2 not_less_eq_eq plus_1_eq_Suc rev_take same_append_eq self_append_conv Stack_Proof.size_listLength take_eq_Nil tl_drop zero_less_Suc)
          by (smt (z3) Suc_diff_Suc Suc_diff_le diff_Suc_Suc drop_Suc min.absorb2 not_le_imp_less rev_take Stack_Proof.size_listLength tl_drop)
      qed
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case ("2_1" v)
  then show ?case 
    by(auto simp: toList_pop split: prod.splits)
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

lemma invariant_pop_big_size_2_1_2: "\<lbrakk>
  invariant (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> tl (toCurrentListBigFirst (big, small)) = toCurrentListBigFirst (big', small)"
  apply(auto simp: pop_toCurrentList split: prod.splits)
  using Big_Proof.toCurrentList_size Big_Proof.pop_toCurrentList
  by (metis list.sel(3) tl_append2)

lemma invariant_pop_big_size_2_1: "\<lbrakk>
  invariant (big, small);
   0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> toListBigFirst (big', small) = toCurrentListBigFirst (big', small)"
  by (metis invariant_listBigFirst invariant_pop_big_size_2_1_1 invariant_pop_big_size_2_1_2)

lemma invariant_pop_big_size_2: "\<lbrakk>
  invariant (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> toListSmallFirst (big', small) = toCurrentListSmallFirst (big', small)"
  by (meson invariant_pop_big_size_2_1 smart)


lemma invariant_pop_big_size_3: "\<lbrakk>
  invariant (big, small);
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


lemma invariant_pop_big_size: "\<lbrakk>
  invariant (big, small);
  0 < Big.size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> invariant (big', small)"
  using invariant_pop_big_size_1[of big small x big']  
        invariant_pop_big_size_2[of big small x big']
        invariant_pop_big_size_3[of big small x big']
  by auto

lemma invariant_pop_small_size_1: "\<lbrakk>
  invariant (big, small);
  0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow>  Big.invariant big  \<and> Small.invariant small'"
  by(auto simp: Small_Proof.invariant_pop_2)

lemma invariant_pop_small_size_2_1: "\<lbrakk>
  invariant (big, small);
   0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> tl (toListSmallFirst (big, small)) = toListSmallFirst (big, small')"
proof(induction "(big, small)" rule: toList.induct)
  case (1 currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction currentS rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: popN_drop popN_size reverseN_drop rev_drop)
      by (smt (z3) Small_Proof.invariant_pop_2_helper Stack_Proof.pop_toList Stack_Proof.size_pop Suc_diff_le Suc_pred append_assoc diff_Suc_Suc diff_add_inverse diff_commute diff_diff_cancel diff_is_0_eq' diff_zero drop0 length_rev rev_drop rev_rev_ident rev_take Stack_Proof.size_isNotEmpty Stack_Proof.size_listLength tl_append2 Stack_Proof.toList_isNotEmpty)
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
    proof(induction x1 rule: get.induct)
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
      proof(induction current rule: get.induct)
        case (1 added old remained)
       
  
        from 1 show ?case 
         proof(induction idle rule: Idle.pop.induct)
           case (1 stack stackSize)
           then show ?case 
             apply auto
             by (metis Stack_Proof.pop_toList Stack_Proof.size_isNotEmpty tl_append2 Stack_Proof.toList_isNotEmpty)
         qed
      next
        case (2 x xs added old remained)
        then show ?case apply(auto split: prod.splits)
          by (metis (no_types, lifting) Zero_not_Suc length_Cons list.sel(3) list.size(3) pop_toList_2 tl_append2 zero_less_Suc) 
      qed
    next
      case (2 current aux new moved)
      then show ?case 
      proof(induction current rule: get.induct)
        case (1 added old remained)
        then show ?case 
          apply(auto simp: reverseN_drop)
          apply (smt (verit, ccfv_threshold) Suc_diff_Suc append_take_drop_id diff_Suc_1 diff_add_inverse2 diff_commute diff_diff_cancel diff_is_0_eq drop_all_iff length_rev less_le_trans list.sel(3) not_le same_append_eq self_append_conv2 take_all_iff take_hd_drop tl_append2)
          by (metis (no_types, lifting) Nat.diff_diff_right Suc_diff_le drop_Suc drop_all_iff leD le_add_diff_inverse le_diff_conv length_rev less_add_same_cancel2 less_imp_le_nat tl_append2 tl_drop zero_less_diff)
      next
        case (2 x xs added old remained)
        then show ?case by auto
      qed
    qed
  qed
next
  case ("2_2" current auxS big newS count)
  then show ?case 
  proof(induction current rule: get.induct)
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
      proof(induction current rule: get.induct)
        case (1 added old remained)
        then show ?case 
          apply(auto split: Big.state.splits)
          by (metis Stack_Proof.pop_toList Stack_Proof.size_isNotEmpty tl_append2 Stack_Proof.toList_isNotEmpty)
      next
        case (2 x xs added old remained)
        then show ?case 
          apply(auto split: Big.state.splits)
          by (metis Stack_Proof.pop_toList list.sel(3) Stack_Proof.size_isNotEmpty tl_append2 Stack_Proof.toList_isNotEmpty zero_less_Suc)
      qed
    qed
  next
    case (2 current aux new moved)
    then show ?case 
    proof(induction current rule: get.induct)
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

lemma invariant_pop_small_size_2_2: "\<lbrakk>
  invariant (big, small);
  0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> tl (toCurrentListSmallFirst (big, small)) = toCurrentListSmallFirst (big, small')"
  apply(auto simp: pop_toCurrentList  split: prod.splits)
  using Small_Proof.toCurrentList_size tl_append2
  by (metis (no_types, lifting) Small_Proof.pop_toCurrentList list.sel(3))

lemma invariant_pop_small_size_2: "\<lbrakk>
  invariant (big, small);
  0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> toListSmallFirst (big, small') = toCurrentListSmallFirst (big, small')"
  using invariant_pop_small_size_2_1 invariant_pop_small_size_2_2 by fastforce

lemma invariant_pop_small_size_3: "\<lbrakk>
  invariant (big, small);
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
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      by(auto simp: Stack_Proof.size_pop Stack_Proof.size_isNotEmpty split: Big.state.splits)
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
  
lemma invariant_pop_small_size: "\<lbrakk>
  invariant (big, small);
   0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
   \<Longrightarrow> invariant (big, small')"
  using invariant_pop_small_size_1[of big small x small']  
        invariant_pop_small_size_2[of big small x small']
        invariant_pop_small_size_3[of big small x small']
  by fastforce  

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

lemma invariant_tick_1: "invariant states \<Longrightarrow> tick states = (big, small) \<Longrightarrow> Big.invariant big \<and> Small.invariant small"
proof(induction states rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case apply(auto simp: reverseN_drop split: current.splits if_splits)
    apply (metis Stack_Proof.size_isEmpty append.right_neutral cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel le_cases list.size(3) rev.simps(1) take_Nil Stack_Proof.toList_isNotEmpty)
    apply (smt (z3) Nil_is_rev_conv Stack_Proof.size_isEmpty append_self_conv2 diff_diff_cancel length_drop length_rev length_take rev_append rev_take Stack_Proof.size_listLength take_all take_append take_eq_Nil take_take toList_isNotEmpty)
    by (metis Stack_Proof.size_isEmpty append.right_neutral list.size(3) minus_nat.diff_0 rev.simps(1) take_Nil Stack_Proof.toList_isNotEmpty)
next
  case ("2_1" v va vb vd right)
  then show ?case using Big_Proof.invariant_tick  Small_Proof.invariant_tick
    by (metis (no_types, lifting) Pair_inject States.invariant.elims(2) States.tick.simps(2) case_prodD)
next
  case ("2_2" v right)
  then show ?case by(auto simp: Common_Proof.invariant_tick Small_Proof.invariant_tick)
next
  case ("2_3" left v va vb vc vd)
  then show ?case using Common_Proof.invariant_tick Big_Proof.invariant_tick  Small_Proof.invariant_tick
    by (smt (z3) States.invariant.elims(2) States.tick.simps(4) case_prod_conv)
next
  case ("2_4" left v)
  then show ?case by(auto simp: Common_Proof.invariant_tick Big_Proof.invariant_tick)
qed

lemma invariant_tick_2: "invariant states \<Longrightarrow> toListSmallFirst (tick states) = toCurrentListSmallFirst (tick states)"
  using States_Proof.tick_toCurrentList States_Proof.tick_toList by fastforce

lemma invariant_tick_3: "invariant states \<Longrightarrow>(case tick states of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow> 
          Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | (Reverse _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      )"
proof(induction states rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by auto
next
  case ("2_1" v va vb vd right)
  then show ?case 
    apply(auto split: Big.state.splits Small.state.splits current.splits) 
    apply (metis One_nat_def Stack_Proof.size_pop Suc_le_lessD add_less_same_cancel1 diff_diff_left list.size(3) not_add_less1 plus_1_eq_Suc Stack_Proof.size_listLength toList_isEmpty)
    apply (metis Stack_Proof.size_isEmpty gr_implies_not0 not_less)
    apply (metis One_nat_def Stack_Proof.size_pop diff_Suc_eq_diff_pred less_le_trans Stack_Proof.size_isNotEmpty)
    by (metis not_less_eq_eq pop_listLength Stack_Proof.size_listLength)
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
lemma invariant_tick: "invariant states \<Longrightarrow> invariant (tick states)"
  using invariant_tick_1 invariant_tick_2 invariant_tick_3
  by (smt (z3) States.invariant.elims(3) case_prodI2)

lemma inSizeWindow'_Suc: "inSizeWindow' states (Suc steps) \<Longrightarrow> inSizeWindow' states steps"
  apply(induction states steps rule: inSizeWindow'.induct)
  by auto

lemma inSizeWindow'_decline: "inSizeWindow' states x \<Longrightarrow> x \<ge> y \<Longrightarrow> inSizeWindow' states y"
  apply(induction states x rule: inSizeWindow'.induct)
  by auto

lemma remainingSteps0: "invariant states \<Longrightarrow> remainingSteps states = 0 \<Longrightarrow> remainingSteps (tick states) = 0"
  apply(induction states rule: tick.induct)
  by(auto simp: remainingSteps_tick_0 Common_Proof.remainingSteps_tick_0 split: current.splits Small.state.splits)

lemma remainingSteps0': "invariant states \<Longrightarrow> remainingSteps states = 0 \<Longrightarrow> remainingSteps ((tick ^^ n) states) = 0"
proof(induction n arbitrary: states)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (metis States_Proof.invariant_tick funpow_simps_right(2) o_apply remainingSteps0)
qed

lemma remainingStepsDecline_2: "invariant states \<Longrightarrow> remainingSteps states > 0 \<Longrightarrow> remainingSteps states = Suc (remainingSteps (tick states))"
proof(induction states rule: tick.induct)
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
         apply (metis One_nat_def Stack_Proof.size_pop diff_Suc_eq_diff_pred diff_le_self le_add_diff_inverse le_diff_conv less_le_trans Stack_Proof.size_isNotEmpty zero_less_Suc)
        apply(auto simp: reverseN_drop)
        by (smt (verit, del_insts) One_nat_def Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_le_lessD diff_Suc_diff_eq1 diff_add_inverse2 diff_diff_left diff_is_0_eq le_add2 le_add_diff_inverse not_add_less1 plus_1_eq_Suc)
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
    using Common_Proof.remainingSteps_tick_0 Common_Proof.remainingSteps_tick apply fastforce
    using Stack_Proof.size_isEmpty apply blast
    using Stack_Proof.size_isNotEmpty apply blast 
    using Common_Proof.remainingSteps_tick_0 Common_Proof.remainingSteps_tick apply fastforce
    apply (metis (no_types, hide_lams) add.commute add_Suc_right diff_add_inverse2 max_0L max_Suc_Suc neq0_conv pop_listLength Common_Proof.remainingSteps_tick_0 Common_Proof.remainingSteps_tick Stack_Proof.size_listLength)
    apply (smt (z3) Common_Proof.remainingSteps_tick Common_Proof.remainingSteps_tick_0 add_Suc_right diff_add_inverse max_Suc_Suc max_def max_nat.neutr_eq_iff neq0_conv pop_listLength size_listLength)
    by (metis (no_types, hide_lams) max.commute max_0L max_Suc_Suc neq0_conv Common_Proof.remainingSteps_tick_0 Common_Proof.remainingSteps_tick)
next
  case ("2_3" left v va vb vc vd)
  then show ?case 
    apply(auto split: Big.state.splits Small.state.splits current.splits) 
    using Common_Proof.remainingSteps_tick_0 Common_Proof.remainingSteps_tick apply fastforce
    using Stack_Proof.size_isEmpty apply blast
    using Stack_Proof.size_isNotEmpty apply blast 
    using Common_Proof.remainingSteps_tick_0 Common_Proof.remainingSteps_tick apply fastforce
    apply (smt (z3) Common_Proof.remainingSteps_tick Common_Proof.remainingSteps_tick_0 Stack_Proof.size_pop Suc_pred add.commute add_Suc_right diff_add_inverse le_add1 le_add_same_cancel1 max_Suc_Suc max_def neq0_conv plus_1_eq_Suc)
    by (smt (z3) Common_Proof.remainingSteps_tick Common_Proof.remainingSteps_tick_0 Stack_Proof.size_isNotEmpty Stack_Proof.size_pop Suc_pred add.commute add_Suc_right add_diff_cancel_right' max.commute max_0R max_Suc_Suc neq0_conv)
next
  case ("2_4" left v)
  then show ?case 
    apply(auto simp: max_def Big_Proof.remainingSteps_tick Common_Proof.remainingSteps_tick split: if_splits) 
    using remainingSteps_tick_0 Big_Proof.remainingSteps_tick apply fastforce
    by (metis Suc_leI le_imp_less_Suc not_le Common_Proof.remainingSteps_tick_0 Common_Proof.remainingSteps_tick zero_less_iff_neq_zero)
qed

lemma remainingStepsDecline: "invariant states \<Longrightarrow> remainingSteps states \<ge> remainingSteps (tick states)"
  by (metis gr_implies_not_zero le_imp_less_Suc less_not_refl3 linear neqE remainingStepsDecline_2 remainingSteps0)

lemma remainingStepsDecline_3: "invariant states \<Longrightarrow> Suc n < remainingSteps states \<Longrightarrow> n < remainingSteps (tick states)"
  apply(induction n)
   apply (metis Suc_lessD gr_zeroI less_not_refl3 remainingStepsDecline_2)
  by (metis Suc_lessD Suc_lessE Suc_lessI dual_order.strict_implies_not_eq remainingStepsDecline_2 zero_less_Suc)

lemma remainingStepsDecline_5: "invariant states \<Longrightarrow> remainingSteps states \<le> n \<Longrightarrow> remainingSteps ((tick ^^ n) states) = 0"
proof(induction "remainingSteps states = 0")
  case True
  then show ?case 
    using remainingSteps0'
    by auto
next
  case False
  then have  "0 < remainingSteps states" by auto

  with False show ?case
  proof(induction n arbitrary: states)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then show ?case
      using remainingStepsDecline_2[of states]
      by (metis (no_types, hide_lams) States_Proof.invariant_tick \<open>0 < States.remainingSteps states\<close> funpow_simps_right(2) neq0_conv not_less_eq_eq o_apply remainingSteps0')
  qed
qed

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

lemma tick_newSizeSmall: "invariant (big, small)
  \<Longrightarrow> tick (big, small) = (big', small')  
  \<Longrightarrow> Small.newSize small = Small.newSize small'"
proof(induction "(big, small)" rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by auto
next
  case ("2_1" v va vb vd)
  then show ?case by(auto split: Small.state.splits current.splits)
next
  case ("2_2" v)
  then show ?case by(auto simp: tick_newSize split: Small.state.splits current.splits)
next
  case ("2_3" v va vb vc vd)
  then show ?case by(auto split: current.splits)
next
  case ("2_4" v)
  then show ?case by(auto simp: tick_newSize)
qed

lemma tick_newSizeBig: "invariant (big, small)
  \<Longrightarrow> tick (big, small) = (big', small')  
  \<Longrightarrow> Big.newSize big = Big.newSize big'"
proof(induction "(big, small)" rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by(auto split: current.splits)
next
  case ("2_1" v va vb vd)
  then show ?case by(auto split: Small.state.splits current.splits)
next
  case ("2_2" v)
  then show ?case by(auto simp: tick_newSize split: Small.state.splits current.splits)
next
  case ("2_3" v va vb vc vd)
  then show ?case by(auto simp: tick_newSize split: current.splits split: Big.state.splits)
next
  case ("2_4" v)
  then show ?case by(auto simp: tick_newSize split: Big.state.splits)
qed

lemma tick_sizeSmall: "invariant (big, small)
  \<Longrightarrow> tick (big, small) = (big', small')  
  \<Longrightarrow> Small.size small = Small.size small'"
proof(induction "(big, small)" rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by auto
next
  case ("2_1" v va vb vd)
  then show ?case by(auto split: Small.state.splits current.splits)
next
  case ("2_2" v)
  then show ?case by(auto simp: Common_Proof.tick_size split: Small.state.splits current.splits)
next
  case ("2_3" v va vb vc vd)
  then show ?case by(auto split: current.splits)
next
  case ("2_4" v)
  then show ?case by(auto simp: Common_Proof.tick_size)
qed

lemma tick_sizeBig: "invariant (big, small)
  \<Longrightarrow> tick (big, small) = (big', small')  
  \<Longrightarrow> Big.size big = Big.size big'"
proof(induction "(big, small)" rule: tick.induct)
  case (1 currentB big auxB currentS uu auxS)
  then show ?case by(auto split: current.splits)
next
  case ("2_1" v va vb vd)
  then show ?case by(auto split: Small.state.splits current.splits)
next
  case ("2_2" v)
  then show ?case by(auto simp: Common_Proof.tick_size split: Small.state.splits current.splits)
next
  case ("2_3" v va vb vc vd)
  then show ?case by(auto simp: Common_Proof.tick_size split: current.splits Big.state.splits)
next
  case ("2_4" v)
  then show ?case by(auto simp: Common_Proof.tick_size split: Big.state.splits)
qed

lemma tick_inSizeWindow_1: "invariant (big, small) \<Longrightarrow> tick (big, small) = (big', small')
  \<Longrightarrow> Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small
  \<Longrightarrow> Big.newSize big' + remainingSteps (big', small') + 2 \<le> 3 * Small.newSize small'"
  using remainingStepsDecline tick_newSizeSmall tick_newSizeBig
  by fastforce

lemma tick_inSizeWindow_2: "invariant (big, small) \<Longrightarrow> tick (big, small) = (big', small')
  \<Longrightarrow> Small.newSize small + remainingSteps (big, small) + 2 \<le> 3 * Big.newSize big
  \<Longrightarrow> Small.newSize small' + remainingSteps (big', small') + 2 \<le> 3 * Big.newSize big'"
  using remainingStepsDecline tick_newSizeSmall tick_newSizeBig
  by fastforce

lemma tick_inSizeWindow_3: "invariant (big, small) \<Longrightarrow> tick (big, small) = (big', small')
  \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Small.size small
  \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Small.size small'"
using remainingStepsDecline tick_sizeSmall
  by fastforce

lemma tick_inSizeWindow_4: "invariant (big, small) \<Longrightarrow> tick (big, small) = (big', small')
  \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Big.size big
  \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Big.size big'"
using remainingStepsDecline tick_sizeBig
  by fastforce

lemma tick_inSizeWindow: "invariant states \<Longrightarrow> inSizeWindow states \<Longrightarrow> inSizeWindow (tick states)"
  using tick_inSizeWindow_1 tick_inSizeWindow_2 tick_inSizeWindow_3 tick_inSizeWindow_4
  by (smt (z3) inSizeWindow'.elims(1) inSizeWindow.elims(1))

lemma remSteps_4: "invariant states \<Longrightarrow> remainingSteps states = steps \<Longrightarrow> steps \<ge> 4 \<Longrightarrow> remainingSteps ((tick ^^ 4) states) = steps - 4"
  by (metis diff_add_inverse2 tick_remainingSteps)

lemma tick_pushSmall_newSizeSmall: "invariant (big, small) 
          \<Longrightarrow> tick (big, Small.push x small) = (big', small')
          \<Longrightarrow> Small.newSize small' = Suc (Small.newSize small)"
  using 
    invariant_push_small[of big small x]
    tick_newSizeSmall[of big "Small.push x small" big' small']
    newSize_push[of small x]
  by simp

lemma tick_pushSmall_sizeSmall: "invariant (big, small) 
          \<Longrightarrow> tick (big, Small.push x small) = (big', small')
          \<Longrightarrow> Small.size small' = Suc (Small.size small)"
  using 
    invariant_push_small[of big small x]
    tick_sizeSmall[of big "Small.push x small" big' small']
    size_push[of small x]
  by simp

lemma tick_pushBig_newSizeBig: "invariant (big, small) 
          \<Longrightarrow> tick (Big.push x big, small) = (big', small')
          \<Longrightarrow> Big.newSize big' = Suc (Big.newSize big)"
  using 
    invariant_push_big[of big small x] 
    tick_newSizeBig[of "Big.push x big" small big' small']
    Big_Proof.newSize_push[of big x]
  by auto

lemma tick_popBig_sizeBig: "invariant (big, small) 
          \<Longrightarrow> 0 < Big.size big 
          \<Longrightarrow> Big.pop big = (x, bigP) 
          \<Longrightarrow> tick (bigP, small) = (big', small')
          \<Longrightarrow> Big.size big = Suc (Big.size big')"
  using 
    invariant_pop_big_size[of big small x bigP] 
    tick_sizeBig[of bigP small big' small']  
    Big_Proof.size_pop[of big]
  by auto

lemma tick_popBig_newSizeBig: "invariant (big, small) 
          \<Longrightarrow> 0 < Big.size big 
          \<Longrightarrow> Big.pop big = (x, bigP) 
          \<Longrightarrow> tick (bigP, small) = (big', small')
          \<Longrightarrow> Big.newSize big = Suc (Big.newSize big')"
  using 
    invariant_pop_big_size[of big small x bigP] 
    Big_Proof.size_newSize[of big]
    tick_newSizeBig[of bigP small big' small']  
    Big_Proof.newSize_pop[of big]
  by auto

lemma tick_pushBig_sizeBig: "invariant (big, small) 
          \<Longrightarrow> tick (Big.push x big, small) = (big', small')
          \<Longrightarrow> Big.size big' = Suc (Big.size big)"
  using 
    invariant_push_big[of big small x]
    Big_Proof.size_push[of big]
    tick_sizeBig[of "Big.push x big" small big' small']
  by auto

lemma tickN_sizeSmall: "invariant (big, small) 
          \<Longrightarrow> (tick ^^ n) (big, small) = (big', small')
          \<Longrightarrow> Small.size small' =  Small.size small"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have invariant1: "invariant (tick (big, small))"
    using invariant_tick 
    by blast

  then obtain big1 small1 where tick: "tick (big, small) = (big1, small1)"
    by auto

  with tick_sizeSmall invariant1 have "Small.size small = Small.size small1"
    by (metis Suc.prems(1))


  then have nTicks: "(tick ^^ n) (big1, small1) = (big', small')"
    using Suc 
    by (metis \<open>States.tick (big, small) = (big1, small1)\<close> funpow_simps_right(2) o_apply)

  have invariant2: "invariant (big1, small1)" using tick invariant1 by auto

  from Suc nTicks invariant2 have "Small.size small' = Small.size small1"
    by auto


  with Suc show ?case
    using \<open>Small.size small = Small.size small1\<close> by presburger
qed

lemma tickN_sizeBig: "invariant (big, small) 
          \<Longrightarrow> (tick ^^ n) (big, small) = (big', small')
          \<Longrightarrow> Big.size big' = Big.size big"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have invariant1: "invariant (tick (big, small))"
    using invariant_tick 
    by blast

  then obtain big1 small1 where tick: "tick (big, small) = (big1, small1)"
    by auto

  with invariant1 have "Big.size big = Big.size big1"
    by (metis Suc.prems(1) tick_sizeBig)


  then have nTicks: "(tick ^^ n) (big1, small1) = (big', small')"
    using Suc 
    by (metis \<open>States.tick (big, small) = (big1, small1)\<close> funpow_simps_right(2) o_apply)

  have invariant2: "invariant (big1, small1)" using tick invariant1 by auto

  from Suc nTicks invariant2 have "Big.size big' = Big.size big1"
    by auto


  with Suc show ?case
    using \<open>Big.size big = Big.size big1\<close> by presburger
qed

lemma tickN_newSizeSmall: "invariant (big, small) 
          \<Longrightarrow> (tick ^^ n) (big, small) = (big', small')
          \<Longrightarrow> Small.newSize small' =  Small.newSize small"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have invariant1: "invariant (tick (big, small))"
    using invariant_tick 
    by blast

  then obtain big1 small1 where tick: "tick (big, small) = (big1, small1)"
    by auto

  with tick_newSizeSmall invariant1 have "Small.newSize small = Small.newSize small1"
    by (metis Suc.prems(1))


  then have nTicks: "(tick ^^ n) (big1, small1) = (big', small')"
    using Suc 
    by (metis \<open>States.tick (big, small) = (big1, small1)\<close> funpow_simps_right(2) o_apply)

  have invariant2: "invariant (big1, small1)" using tick invariant1 by auto

  from Suc nTicks invariant2 have "Small.newSize small' = Small.newSize small1"
    by auto


  with Suc show ?case
    using \<open>Small.newSize small = Small.newSize small1\<close> by presburger
qed

lemma tickN_newSizeBig: "invariant (big, small) 
          \<Longrightarrow> (tick ^^ n) (big, small) = (big', small')
          \<Longrightarrow> Big.newSize big' =  Big.newSize big"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have invariant1: "invariant (tick (big, small))"
    using invariant_tick 
    by blast

  then obtain big1 small1 where tick: "tick (big, small) = (big1, small1)"
    by auto

  with tick_newSizeBig invariant1 have "Big.newSize big = Big.newSize big1"
    by (metis Suc.prems(1))


  then have nTicks: "(tick ^^ n) (big1, small1) = (big', small')"
    using Suc 
    by (metis \<open>States.tick (big, small) = (big1, small1)\<close> funpow_simps_right(2) o_apply)

  have invariant2: "invariant (big1, small1)" using tick invariant1 by auto

  from Suc nTicks invariant2 have "Big.newSize big' = Big.newSize big1"
    by auto


  with Suc show ?case
    using \<open>Big.newSize big = Big.newSize big1\<close> by presburger
qed

lemma tickN_pushSmall_sizeSmall: "invariant (big, small) 
          \<Longrightarrow> (tick ^^ n) (big, Small.push x small) = (big', small')
          \<Longrightarrow> Small.size small' = Suc (Small.size small)"
  by (metis invariant_push_small old.prod.exhaust tick_pushSmall_sizeSmall tickN_sizeSmall tick_sizeSmall)

lemma tickN_pushSmall_newSizeSmall: "invariant (big, small) 
          \<Longrightarrow> (tick ^^ n) (big, Small.push x small) = (big', small')
          \<Longrightarrow> Small.newSize small' = Suc (Small.newSize small)"
  by (metis invariant_push_small old.prod.exhaust tick_pushSmall_newSizeSmall tickN_newSizeSmall tick_newSizeSmall)

lemma tickN_pushBig_sizeBig: "invariant (big, small) 
          \<Longrightarrow> (tick ^^ n) (Big.push x big, small) = (big', small')
          \<Longrightarrow> Big.size big' = Suc (Big.size big)"
  by (metis invariant_push_big old.prod.exhaust tick_pushBig_sizeBig tickN_sizeBig tick_sizeBig)

lemma tickN_pushBig_newSizeBig: "invariant (big, small) 
          \<Longrightarrow> (tick ^^ n) (Big.push x big, small) = (big', small')
          \<Longrightarrow> Big.newSize big' = Suc (Big.newSize big)"
  by (metis invariant_push_big old.prod.exhaust tick_pushBig_newSizeBig tickN_newSizeBig tick_newSizeBig)

lemma tickN_popSmall_sizeSmall: "invariant (big, small) 
          \<Longrightarrow> 0 < Small.size small 
          \<Longrightarrow> Small.pop small = (x, smallP) 
          \<Longrightarrow> (tick ^^ n) (big, smallP) = (big', small')
          \<Longrightarrow> Small.size small = Suc (Small.size small')"
  using invariant_pop_small_size size_pop tickN_sizeSmall by fastforce

lemma tickN_popSmall_newSizeSmall: "invariant (big, small) 
          \<Longrightarrow> 0 < Small.size small 
          \<Longrightarrow> Small.pop small = (x, smallP) 
          \<Longrightarrow> (tick ^^ n) (big, smallP) = (big', small')
          \<Longrightarrow> Small.newSize small = Suc (Small.newSize small')"
  using invariant_pop_small_size newSize_pop tickN_newSizeSmall size_newSize by fastforce

lemma tickN_popBig_sizeBig: "invariant (big, small) 
          \<Longrightarrow> 0 < Big.size big 
          \<Longrightarrow> Big.pop big = (x, bigP) 
          \<Longrightarrow> (tick ^^ n) (bigP, small) = (big', small')
          \<Longrightarrow> Big.size big = Suc (Big.size big')"
  using invariant_pop_big_size Big_Proof.size_pop tickN_sizeBig by fastforce

lemma tickN_popBig_newSizeBig: "invariant (big, small) 
          \<Longrightarrow> 0 < Big.size big 
          \<Longrightarrow> Big.pop big = (x, bigP) 
          \<Longrightarrow> (tick ^^ n) (bigP, small) = (big', small')
          \<Longrightarrow> Big.newSize big = Suc (Big.newSize big')"
  by (metis (no_types, hide_lams) States.remainingSteps.cases invariant_pop_big_size tick_popBig_newSizeBig tick_newSizeBig tickN_newSizeBig)

lemma remainingSteps_pushSmall: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) = remainingSteps (big, Small.push x small)"
proof(induction x small rule: Small.push.induct)
  case (1 x state)
  then show ?case 
    apply(auto simp: max_def Common_Proof.remainingSteps_push)
    by (metis Common_Proof.remainingSteps_push)+
next
  case (2 x current small auxS)
  then show ?case 
  proof(induction x current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case by auto
  qed
next
  case (3 x current auxS big newS count)
  then show ?case
  proof(induction x current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case by auto
  qed
qed    

lemma remainingSteps_popSmall: "
          invariant (big, small)
     \<Longrightarrow> 0 < Small.size small 
     \<Longrightarrow> Small.pop small = (x, smallP) 
     \<Longrightarrow> remainingSteps (big, small) \<ge> remainingSteps (big, smallP)"
proof(induction small rule: Small.pop.induct)
  case (1 state)
  then show ?case apply(auto simp: max_def Common_Proof.remainingSteps_pop split: prod.splits)
    using Common_Proof.remainingSteps_pop by fastforce 
next
  case (2 current small auxS)
  then show ?case
  proof(induction current rule: get.induct)
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
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma remainingSteps_popBig: "
      invariant (big, small)
       \<Longrightarrow> 0 < Big.size big 
       \<Longrightarrow> Big.pop big = (x, bigP) 
       \<Longrightarrow> remainingSteps (big, small) \<ge> remainingSteps (bigP, small)"
proof(induction big rule: Big.pop.induct)
  case (1 state)
  then show ?case 
  proof(induction state rule: Common.pop.induct)
    case (1 current idle)
    then show ?case 
    proof(induction idle rule: Idle.pop.induct)
      case (1 stack stackSize)
      then show ?case 
      proof(induction current rule: get.induct)
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
    proof(induction current rule: get.induct)
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
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case by(auto split: Small.state.splits current.splits)
  next
    case (2 x xs added old remained)
    then show ?case by(auto split: Small.state.splits current.splits)
  qed
qed

lemma remainingSteps_pushBig: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) = remainingSteps (Big.push x big, small)"
proof(induction x big rule: Big.push.induct)
  case (1 x state)
  then show ?case 
    apply(auto simp: max_def Common_Proof.remainingSteps_push split: Small.state.splits)
    using Common_Proof.remainingSteps_push by fastforce+
next
  case (2 x current big aux count)
  then show ?case
  proof(induction current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case 
      apply(auto split: Small.state.splits)
      by (metis Big.state.simps(5))
  qed
qed


lemma tick4_remainingSteps_popSmall: "invariant (big, small)
      \<Longrightarrow> 0 < Small.size small 
      \<Longrightarrow> Small.pop small = (x, smallP) 
       \<Longrightarrow> remainingSteps (big, smallP) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, smallP)) = (big', small')
       \<Longrightarrow> remainingSteps (big', small') \<le> remainingSteps (big, small) - 4"
  by (metis diff_le_mono invariant_pop_small_size remSteps_4 remainingSteps_popSmall)

lemma tick4_remainingSteps_pushBig: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow> remainingSteps (big', small') = remainingSteps (big, small) - 4"
  by (metis invariant_push_big remSteps_4 remainingSteps_pushBig)

lemma tick4_remainingSteps_pushSmall: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow> remainingSteps (big', small') = remainingSteps (big, small) - 4"
  by (metis invariant_push_small remSteps_4 remainingSteps_pushSmall)

lemma tick4_remainingSteps_popBig: "invariant (big, small)
       \<Longrightarrow> 0 < Big.size big 
       \<Longrightarrow> Big.pop big = (x, bigP) 
       \<Longrightarrow> remainingSteps (bigP, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (bigP, small)) = (big', small')
       \<Longrightarrow> remainingSteps (big', small') \<le> remainingSteps (big, small) - 4"
  by (metis add_le_imp_le_diff invariant_pop_big_size remainingSteps_popBig tick_remainingSteps)

lemma tick4_popSmall_sizeWindow1': "
            0 < Small.size small 
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> (remainingSteps (big, small) - 4) + 1 \<le> 4 * (Small.size small - 1)"
  by linarith

lemma tick4_popSmall_sizeWindow1: "invariant (big, small)
       \<Longrightarrow> 0 < Small.size small 
       \<Longrightarrow> Small.pop small = (x, smallP)
       \<Longrightarrow> remainingSteps (big, smallP) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, smallP)) = (big', small')
       \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Small.size small'"
  using tick4_popSmall_sizeWindow1' remSteps_4 tickN_popSmall_sizeSmall remainingSteps_popSmall
  by (smt (verit, ccfv_SIG) Suc_diff_1 Suc_inject add_le_cancel_right order_trans tick4_remainingSteps_popSmall)

lemma tick4_popBig_sizeWindow1: "invariant (big, small)
       \<Longrightarrow> 0 < Big.size big 
       \<Longrightarrow> Big.pop big = (x, bigP) 
       \<Longrightarrow> remainingSteps (bigP, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (bigP, small)) = (big', small')
       \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Small.size small'"
  by (metis (no_types, lifting) add_leD1 add_mono_thms_linordered_semiring(3) invariant_pop_big_size order.trans tickN_sizeSmall remainingSteps_popBig tick_remainingSteps)

lemma tick4_popSmall_sizeWindow2: "invariant (big, small)
       \<Longrightarrow> 0 < Small.size small 
       \<Longrightarrow> Small.pop small = (x, smallP)
       \<Longrightarrow> remainingSteps (big, smallP) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, smallP)) = (big', small')
       \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Big.size big
       \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Big.size big'"
  by (smt (z3) add.commute add_leE invariant_pop_small_size le_add_diff_inverse2 nat_add_left_cancel_le remSteps_4 tickN_sizeBig remainingSteps_popSmall)

lemma tick4_popBig_sizeWindow2: 
  assumes
    "invariant (big, small)"
    "0 < Big.size big"
    "Big.pop big = (x, bigP)"
    "remainingSteps (bigP, small) \<ge> 4"
    "((tick ^^ 4) (bigP, small)) = (big', small')"
    "remainingSteps (big, small) + 1 \<le> 4 * Big.size big"
  shows
    "remainingSteps (big', small') + 1 \<le> 4 * Big.size big'"
proof -
  from assms have "remainingSteps (bigP, small) + 1 \<le> 4 * Big.size big"
    by (meson add_le_cancel_right order.trans remainingSteps_popBig)

  with assms show ?thesis
    by (smt (z3) Suc_diff_le Suc_eq_plus1 add_mult_distrib2 diff_diff_add diff_is_0_eq invariant_pop_big_size mult_numeral_1_right numerals(1) plus_1_eq_Suc remSteps_4 tickN_popBig_sizeBig)
qed

lemma tick4_popSmall_sizeWindow3: "invariant (big, small)
       \<Longrightarrow> 0 < Small.size small 
       \<Longrightarrow> Small.pop small = (x, smallP)
       \<Longrightarrow> remainingSteps (big, smallP) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, smallP)) = (big', small')
       \<Longrightarrow>  Small.newSize small + remainingSteps (big, small) + 2 \<le> 3 * Big.newSize big
       \<Longrightarrow>  Small.newSize small' + remainingSteps (big', small') + 2 \<le> 3 * Big.newSize big'"
  by (smt (verit, best) add_le_mono diff_Suc_1 diff_le_self dual_order.eq_iff invariant_pop_small_size nat_less_le order.trans remSteps_4 tickN_newSizeBig tickN_popSmall_newSizeSmall remainingSteps_popSmall)

lemma tick4_popBig_sizeWindow3': "
            0 < Big.size big 
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow>  Small.newSize small + remainingSteps (big, small) + 2 \<le> 3 * Big.newSize big
       \<Longrightarrow> Small.newSize small + (remainingSteps (big, small) - 4) + 2 \<le> 3 * (Big.newSize big - 1)"
  using invariant_pop_big_size tickN_newSizeBig tickN_newSizeSmall tickN_popBig_newSizeBig tick4_remainingSteps_popBig remSteps_4 remainingSteps_popBig
  by linarith

lemma tick4_popBig_sizeWindow3: 
    assumes
      "invariant (big, small)"
      "0 < Big.size big" 
      "Big.pop big = (x, bigP) "
      "remainingSteps (bigP, small) \<ge> 4"
      "((tick ^^ 4) (bigP, small)) = (big', small')"
      "Small.newSize small + remainingSteps (big, small) + 2 \<le> 3 * Big.newSize big"
    shows
      "Small.newSize small' + remainingSteps (big', small') + 2 \<le> 3 * Big.newSize big'"
proof-
  from assms have "Small.newSize small + (remainingSteps (big, small) - 4) + 2 \<le> 3 * (Big.newSize big - 1)"
    by (meson dual_order.trans remainingSteps_popBig tick4_popBig_sizeWindow3')

  then have  "Small.newSize small + remainingSteps (big', small') + 2 \<le> 3 * (Big.newSize big - 1)"
    by (smt (verit, ccfv_SIG) add_le_mono assms(1) assms(2) assms(3) assms(4) assms(5) dual_order.trans le_antisym less_or_eq_imp_le nat_less_le tick4_remainingSteps_popBig)

  with assms show ?thesis 
    by (metis diff_Suc_1 invariant_pop_big_size tickN_newSizeSmall tickN_popBig_newSizeBig)
qed

lemma tick4_popSmall_sizeWindow4': "
            0 < Small.size small 
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small
       \<Longrightarrow> Big.newSize big + (remainingSteps (big, small) - 4) + 2 \<le> 3 * (Small.newSize small - 1)"
  by linarith

lemma tick4_popSmall_sizeWindow4:
    assumes
      "invariant (big, small)"
      "0 < Small.size small"
      "Small.pop small = (x, smallP)"
      "remainingSteps (big, smallP) \<ge> 4"
      "((tick ^^ 4) (big, smallP)) = (big', small')"
      "Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small"
    shows
       "Big.newSize big' + remainingSteps (big', small') + 2 \<le> 3 * Small.newSize small'"
proof-
  from assms tick4_popSmall_sizeWindow4' have  "Big.newSize big + (remainingSteps (big, small) - 4) + 2 \<le> 3 * (Small.newSize small - 1)"
    by (smt (verit, best) add_leE le_add_diff_inverse remainingSteps_popSmall)

  with assms have "Big.newSize big + remainingSteps (big', small') + 2 \<le> 3 * (Small.newSize small - 1)"
    by (meson add_le_mono le_refl order_trans tick4_remainingSteps_popSmall)

  with assms show ?thesis 
    by (metis diff_Suc_1 invariant_pop_small_size tickN_newSizeBig tickN_popSmall_newSizeSmall)
qed

lemma tick4_popBig_sizeWindow4': "
           0 < Big.size big 
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow>  Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small
       \<Longrightarrow>  (Big.newSize big - 1) + (remainingSteps (big, small) - 4) + 2 \<le> 3 * Small.newSize small"
  by linarith

lemma tick4_popBig_sizeWindow4: 
  assumes
    "invariant (big, small)"
    "0 < Big.size big "
    "Big.pop big = (x, bigP)"
    "remainingSteps (bigP, small) \<ge> 4"
    "((tick ^^ 4) (bigP, small)) = (big', small')"
    "Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small"
  shows
    "Big.newSize big' + remainingSteps (big', small') + 2 \<le> 3 * Small.newSize small'"
proof -
  from assms tick4_popBig_sizeWindow4' 
  have "(Big.newSize big - 1) + (remainingSteps (big, small) - 4) + 2 \<le> 3 * Small.newSize small"
    by linarith

  with assms have  "(Big.newSize big - 1) + remainingSteps (big', small') + 2 \<le> 3 * Small.newSize small"
    by (meson add_le_mono dual_order.eq_iff order_trans tick4_remainingSteps_popBig)

  with assms show ?thesis 
    by (metis diff_Suc_1 invariant_pop_big_size tickN_newSizeSmall tickN_popBig_newSizeBig)
qed

lemma tick4_pushSmall_sizeWindow1: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Small.size small'"
  by (smt (z3) add.commute add_leD1 add_le_mono le_add1 le_add_diff_inverse2 mult_Suc_right nat_1_add_1 numeral_Bit0 tickN_pushSmall_sizeSmall tick4_remainingSteps_pushSmall)

lemma tick4_pushBig_sizeWindow1: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Small.size small
       \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Small.size small'"
  by (metis (full_types) Suc_diff_le add.commute invariant_push_big less_Suc_eq_le less_imp_diff_less plus_1_eq_Suc tickN_sizeSmall tick4_remainingSteps_pushBig)

lemma tick4_pushSmall_sizeWindow2: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Big.size big
       \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Big.size big'"
  by (metis (full_types) Suc_diff_le add.commute invariant_push_small less_Suc_eq_le less_imp_diff_less plus_1_eq_Suc tickN_sizeBig tick4_remainingSteps_pushSmall)

lemma tick4_pushBig_sizeWindow2: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow> remainingSteps (big, small) + 1 \<le> 4 * Big.size big
       \<Longrightarrow> remainingSteps (big', small') + 1 \<le> 4 * Big.size big'"
  by (smt (z3) Suc_diff_le Suc_eq_plus1 less_Suc_eq_le less_imp_diff_less mult.commute mult_Suc tickN_pushBig_sizeBig tick4_remainingSteps_pushBig trans_le_add2)

lemma tick4_pushSmall_sizeWindow3': "
            remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> Small.newSize small + remainingSteps (big, small) + 2 \<le> 3 * Big.newSize big
       \<Longrightarrow> (Suc (Small.newSize small)) + (remainingSteps (big, small) - 4) + 2 \<le> 3 * Big.newSize big"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma tick4_pushSmall_sizeWindow3: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow>  Small.newSize small + remainingSteps (big, small) + 2 \<le> 3 * Big.newSize big
       \<Longrightarrow>  Small.newSize small' + remainingSteps (big', small') + 2 \<le> 3 * Big.newSize big'"
  using tickN_newSizeBig tickN_pushSmall_newSizeSmall tick4_remainingSteps_pushSmall
  by (metis invariant_push_small tick4_pushSmall_sizeWindow3')

lemma tick4_pushBig_sizeWindow3': "
            remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> Small.newSize small + remainingSteps (big, small) + 2 \<le> 3 * Big.newSize big
       \<Longrightarrow> Small.newSize small + (remainingSteps (big, small) - 4) + 2 \<le> 3 * (Suc (Big.newSize big))"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma tick4_pushBig_sizeWindow3: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow>  Small.newSize small + remainingSteps (big, small) + 2 \<le> 3 * Big.newSize big
       \<Longrightarrow>  Small.newSize small' + remainingSteps (big', small') + 2 \<le> 3 * Big.newSize big'"
  by (metis invariant_push_big tickN_newSizeSmall tickN_pushBig_newSizeBig tick4_remainingSteps_pushBig tick4_pushBig_sizeWindow3')

lemma tick4_pushSmall_sizeWindow4': "
            remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small
       \<Longrightarrow> Big.newSize big + (remainingSteps (big, small) - 4) + 2 \<le> 3 * (Suc (Small.newSize small))"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma tick4_pushSmall_sizeWindow4: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (big, Small.push x small)) = (big', small')
       \<Longrightarrow>  Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small
       \<Longrightarrow>  Big.newSize big' + remainingSteps (big', small') + 2 \<le> 3 * Small.newSize small'"
  by (metis invariant_push_small tickN_newSizeBig tickN_pushSmall_newSizeSmall tick4_remainingSteps_pushSmall tick4_pushSmall_sizeWindow4')

lemma tick4_pushBig_sizeWindow4': "
            remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small
       \<Longrightarrow> (Suc (Big.newSize big)) + (remainingSteps (big, small) - 4) + 2 \<le> 3 * Small.newSize small"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma tick4_pushBig_sizeWindow4: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> ((tick ^^ 4) (Big.push x big, small)) = (big', small')
       \<Longrightarrow>  Big.newSize big + remainingSteps (big, small) + 2 \<le> 3 * Small.newSize small
       \<Longrightarrow>  Big.newSize big' + remainingSteps (big', small') + 2 \<le> 3 * Small.newSize small'"
  by (metis invariant_push_big tickN_newSizeSmall tickN_pushBig_newSizeBig tick4_remainingSteps_pushBig tick4_pushBig_sizeWindow4')

lemma tick4_pushSmall_sizeWindow: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> inSizeWindow (big, small)
       \<Longrightarrow> inSizeWindow ((tick ^^ 4) (big, Small.push x small))"
  using tick4_pushSmall_sizeWindow1 tick4_pushSmall_sizeWindow2 tick4_pushSmall_sizeWindow3 tick4_pushSmall_sizeWindow4 
  by (smt (verit) inSizeWindow'.elims(3) inSizeWindow'.simps inSizeWindow.elims(2) inSizeWindow.elims(3))

lemma tick4_pushBig_sizeWindow: "invariant (big, small)
       \<Longrightarrow> remainingSteps (big, small) \<ge> 4
       \<Longrightarrow> inSizeWindow (big, small)
       \<Longrightarrow> inSizeWindow ((tick ^^ 4) (Big.push x big, small))"
  using tick4_pushBig_sizeWindow1 tick4_pushBig_sizeWindow2 tick4_pushBig_sizeWindow3 tick4_pushBig_sizeWindow4
  by (smt (verit) inSizeWindow'.elims(3) inSizeWindow'.simps inSizeWindow.elims(2) inSizeWindow.elims(3))

lemma tick4_popSmall_sizeWindow: "invariant (big, small)
       \<Longrightarrow> 0 < Small.size small 
       \<Longrightarrow> Small.pop small = (x, smallP)
       \<Longrightarrow> remainingSteps (big, smallP) \<ge> 4
       \<Longrightarrow> inSizeWindow (big, small)
       \<Longrightarrow> inSizeWindow ((tick ^^ 4) (big, smallP))"
  using tick4_popSmall_sizeWindow1 tick4_popSmall_sizeWindow2 tick4_popSmall_sizeWindow3 tick4_popSmall_sizeWindow4 
  by (smt (verit) inSizeWindow'.elims(3) inSizeWindow'.simps inSizeWindow.elims(2) inSizeWindow.elims(3))

lemma tick4_popBig_sizeWindow: "invariant (big, small)
       \<Longrightarrow> 0 < Big.size big 
       \<Longrightarrow> Big.pop big = (x, bigP) 
       \<Longrightarrow> remainingSteps (bigP, small) \<ge> 4
       \<Longrightarrow> inSizeWindow (big, small)
       \<Longrightarrow> inSizeWindow ((tick ^^ 4) (bigP, small))"
  using tick4_popBig_sizeWindow1 tick4_popBig_sizeWindow2 tick4_popBig_sizeWindow3 tick4_popBig_sizeWindow4
  by (smt (verit) inSizeWindow'.elims(3) inSizeWindow'.simps inSizeWindow.elims(2) inSizeWindow.elims(3))

lemma sizeWindow_smallSize: "inSizeWindow (big, small) \<Longrightarrow> 0 < Small.size small"
  apply(induction small arbitrary: big)
  by auto

lemma sizeWindow_bigSize: "inSizeWindow (big, small) \<Longrightarrow> 0 < Big.size big"
  apply(induction big arbitrary: small)
  by auto

lemma sizeWindow_smallNewSize: "inSizeWindow (big, small) \<Longrightarrow> 0 < Small.newSize small"
  apply(induction small arbitrary: big)
  by auto

lemma sizeWindow_bigNewSize: "inSizeWindow (big, small) \<Longrightarrow> 0 < Big.newSize big"
  apply(induction big arbitrary: small)
  by auto

lemma remainingSteps_tickN: "invariant states \<Longrightarrow>  n < remainingSteps states 
    \<Longrightarrow>  remainingSteps states - n = remainingSteps ((tick ^^ n) states)"
  by (metis diff_add_inverse2 less_or_eq_imp_le tick_remainingSteps)

lemma tick_inSizeWindow': "invariant states \<Longrightarrow>
    inSizeWindow' states x \<Longrightarrow> 
    inSizeWindow' (tick states) x"
proof(induction states x rule: inSizeWindow'.induct)
  case (1 big small steps)
  then show ?case 
    using tick_newSizeBig[of big small] tick_newSizeSmall[of big small] tick_sizeBig[of big small] tick_sizeSmall[of big small]
    apply(auto split: )
  proof -
    assume a1: "\<And>big' small'. States.tick (big, small) = (big', small') \<Longrightarrow> Big.newSize big = Big.newSize big'"
    assume a2: "\<And>big' small'. States.tick (big, small) = (big', small') \<Longrightarrow> Small.newSize small = Small.newSize small'"
    assume a3: "\<And>big' small'. States.tick (big, small) = (big', small') \<Longrightarrow> Big.size big = Big.size big'"
    assume a4: "\<And>big' small'. States.tick (big, small) = (big', small') \<Longrightarrow> Small.size small = Small.size small'"
    assume a5: "Suc (Suc (Small.newSize small + steps)) \<le> 3 * Big.newSize big"
    assume a6: "Suc (Suc (Big.newSize big + steps)) \<le> 3 * Small.newSize small"
    assume a7: "Suc steps \<le> 4 * Small.size small"
    assume a8: "Suc steps \<le> 4 * Big.size big"
  
      have "\<forall>p n. (\<exists>s sa. (\<not> n + 1 \<le> 4 * Big.size (s::'a Big.state) \<or> \<not> n + 1 \<le> 4 * Small.size sa \<or> \<not> Big.newSize s + n + 2 \<le> 3 * Small.newSize sa \<or> \<not> Small.newSize sa + n + 2 \<le> 3 * Big.newSize s) \<and> (s, sa) = p) \<or> inSizeWindow' p n"
        by simp
      then show ?thesis
        using a8 a7 a6 a5 a4 a3 a2 a1 by (smt (z3) Suc_1 Suc_eq_plus1 add_Suc_shift)
    qed
qed

  
end
