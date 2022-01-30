theory States_Proof
  imports States Big_Proof Small_Proof HOL.Real Complex_Main
begin

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits
lemmas invariant_ticks = Big_Proof.invariant_tick Common_Proof.invariant_tick Small_Proof.invariant_tick

lemma inSizeWindow'_Suc: "inSizeWindow' states (Suc steps) \<Longrightarrow> inSizeWindow' states steps"
  apply(induction states steps rule: inSizeWindow'.induct)
  by auto

lemma invariant_listBigFirst: "invariant states \<Longrightarrow> toListBigFirst states = toCurrentListBigFirst states"
  apply(auto split: prod.splits)
  by (metis rev_append rev_rev_ident)

lemma tick_toList: "invariant states \<Longrightarrow> toList (tick states) = toList states"
proof(induction states)
  case (Pair big small)
  then show ?case
 proof(induction small)
    case (Reverse1 currentS small auxS)
    then show ?case 
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
            apply (metis toList_isEmpty funpow_swap1 reverseN.elims reverseN.simps(2))
            by (metis first_pop funpow_swap1 reverseN.simps(3))
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
      using toList_isEmpty apply blast
          apply (metis first_pop rev.simps(2))
      using size_isNotEmpty apply blast
      apply (metis add.left_neutral toList_isEmpty neq0_conv size_isNotEmpty rev.simps(1) self_append_conv2)
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


(*

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

lemma invariant_pop_big_1: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow>  Big.invariant big'  \<and> Small.invariant small"
  by(auto simp: Big_Proof.invariant_pop)

lemma helper: "Stack.toList ((Stack.pop ^^ n) stack) = drop n (Stack.toList stack)" 
  apply(induction n)
   apply auto
  by (metis Stack.isEmpty.elims(2) Stack.pop.simps(1) Stack.toList.simps append_Nil drop_Suc first_pop list.sel(2) list.sel(3) tl_drop)

lemma helper_2: "Stack.size ((Stack.pop ^^ n) stack) = (Stack.size stack) - n"
  apply(induction n)
   apply auto
  by (metis (no_types, hide_lams) One_nat_def Stack.isEmpty.elims(2) Stack.pop.simps(1) Stack.toList.simps Stack_Proof.size_pop append_Nil diff_Suc_eq_diff_pred diff_commute diff_is_0_eq le_Suc_eq list.size(3) size_listLength)

lemma smart: "toListSmallFirst (big, small) = toCurrentListSmallFirst (big, small) \<longleftrightarrow>
              toListBigFirst (big, small) = toCurrentListBigFirst (big, small)"
  apply(auto split: prod.splits)
  by (metis rev_append rev_rev_ident)+

lemma invariant_pop_big_2_1_1: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> tl (toListBigFirst (big, small)) = toListBigFirst (big', small)"
proof(induction "(big, small)" rule: toList.induct)
  case (1 currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction currentB rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: reverseN_drop)
      by (smt (z3) Suc_diff_le add.commute add_diff_cancel_left drop_Suc le_add_diff_inverse2 le_cases3 nat_add_left_cancel_le size_listLength tl_drop)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case ("2_1" v)
  then show ?case 
    by(auto simp: list_pop split: prod.splits)
next
  case ("2_2" v va vb vc vd)
  then show ?case 
    apply(auto simp: pop_2)
    using helper_3 tl_append2 by blast
next
  case ("2_3" v)
  then show ?case 
    apply(auto simp: pop_2)
    using helper_3 tl_append2 by blast
qed

lemma invariant_pop_big_2_1_2: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> tl (toCurrentListBigFirst (big, small)) = toCurrentListBigFirst (big', small)"
  apply(auto simp: currentList_pop split: prod.splits)
  using Big_Proof.currentList_empty Big_Proof.currentList_pop by fastforce  

lemma invariant_pop_big_2_1: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> toListBigFirst (big', small) = toCurrentListBigFirst (big', small)"
  by (metis invariant_listBigFirst invariant_pop_big_2_1_1 invariant_pop_big_2_1_2)

lemma invariant_pop_big_2: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> toListSmallFirst (big', small) = toCurrentListSmallFirst (big', small)"
  by (meson invariant_pop_big_2_1 smart)


lemma invariant_pop_big_3: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
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


lemma invariant_pop_big: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> invariant (big', small)"
  using invariant_pop_big_1[of big small x big']  
        invariant_pop_big_2[of big small x big']
        invariant_pop_big_3[of big small x big']
  by auto

lemma invariant_pop_small_1: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow>  Big.invariant big  \<and> Small.invariant small'"
  by(auto simp: Small_Proof.invariant_pop)

lemma invariant_pop_small_2_1: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> tl (toListSmallFirst (big, small)) = toListSmallFirst (big, small')"
proof(induction "(big, small)" rule: toList.induct)
  case (1 currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction currentS rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: helper helper_2 reverseN_drop rev_drop)
      by (smt (z3) Small_Proof.invariant_pop_2_helper Stack_Proof.pop_toList Stack_Proof.size_pop Suc_diff_le Suc_pred append_assoc diff_Suc_Suc diff_add_inverse diff_commute diff_diff_cancel diff_is_0_eq' diff_zero drop0 length_rev rev_drop rev_rev_ident rev_take size_isNotEmpty size_listLength tl_append2 toList_isNotEmpty)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case ("2_1" v)
  then show ?case 
    apply(auto simp:  split: prod.splits Small.state.splits)
    apply (metis (no_types, lifting) "2_1.prems"(1) "2_1.prems"(3) Small.isEmpty.simps(3) States.invariant.elims(2) case_prodD list.distinct(1) list.sel(3) pop_toList_reverse2 tl_append2)
    by (metis list.distinct(1) list.sel(3) list_pop tl_append2)
next
  case ("2_2" current auxS big newS count)
  then show ?case 
    apply(simp split: Big.state.splits Small.state.splits)
    by (metis (no_types, lifting) "2_2"(2) "2_2"(4) Small.isEmpty.simps(3) States.invariant.elims(2) case_prodD list.distinct(1) list.sel(3) pop_toList_reverse2 tl_append2)
next
  case ("2_3" v)
  then show ?case 
    apply(auto split: prod.splits Big.state.splits)
    by (metis list.distinct(1) list.sel(3) list_pop tl_append2)
qed

lemma invariant_pop_small_2_2: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> tl (toCurrentListSmallFirst (big, small)) = toCurrentListSmallFirst (big, small')"
  apply(auto simp: currentList_pop  split: prod.splits)
  using Small_Proof.currentList_empty tl_append2 by blast

lemma invariant_pop_small_2: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> toListSmallFirst (big, small') = toCurrentListSmallFirst (big, small')"
  using invariant_pop_small_2_1 invariant_pop_small_2_2 by fastforce

lemma invariant_pop_small_3: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
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
      by(auto simp: Stack_Proof.size_pop size_isNotEmpty split: Big.state.splits)
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
  
lemma invariant_pop_small: "\<lbrakk>
  invariant (big, small);
  \<not>isEmpty (big, small);
  Small.pop small = (x, small')\<rbrakk>
   \<Longrightarrow> invariant (big, small')"
  using invariant_pop_small_1[of big small x small']  
        invariant_pop_small_2[of big small x small']
        invariant_pop_small_3[of big small x small']
  by fastforce  

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
      apply(auto simp: helper helper_2 reverseN_drop rev_drop)
      by (smt (z3) Small_Proof.invariant_pop_2_helper Stack_Proof.pop_toList Stack_Proof.size_pop Suc_diff_le Suc_pred append_assoc diff_Suc_Suc diff_add_inverse diff_commute diff_diff_cancel diff_is_0_eq' diff_zero drop0 length_rev rev_drop rev_rev_ident rev_take size_isNotEmpty size_listLength tl_append2 toList_isNotEmpty)
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
        by (smt (z3) Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc length_greater_0_conv less_le_trans neq0_conv rev_is_Nil_conv rev_take take_eq_Nil tl_append2 tl_drop)
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
           proof(induction stackSize)
             case 0
             have "\<lbrakk>0 < Stack.size old; big = Big.state.Common v; Common.invariant v;
     small' = Small.state.Common (state.Idle (Current [] 0 (Stack.pop old) 0) (idle.Idle (Stack.pop stack) 0)); Stack.size stack = 0; added = 0;
     remained = 0; Stack.toList stack @ rev (Common.toList v) = Stack.toList old @ rev (Common.toCurrentList v)\<rbrakk>
    \<Longrightarrow> tl (Stack.toList old @ rev (Common.toCurrentList v)) = Stack.toList (Stack.pop stack) @ rev (Common.toList v)"
               sorry

             from 0 show ?case apply auto
               sorry
           next
             case (Suc stackSize)
             then show ?case 
               apply auto
               by (metis Stack_Proof.pop_toList Stack_Proof.size_isEmpty old.nat.distinct(2) tl_append2 toList_isNotEmpty)
           qed
         qed
      next
        case (2 x xs added old remained)
        then show ?case apply(auto split: prod.splits)  sorry
      qed
    next
      case (2 current aux new moved)
      then show ?case apply auto
        sorry
    qed
  qed
next
  case ("2_2" current auxS big newS count)
  then show ?case 
    apply(simp split: Big.state.splits Small.state.splits)
    sorry
next
  case ("2_3" v)
  then show ?case 
    apply(auto split: prod.splits Big.state.splits)
    sorry
qed

lemma invariant_pop_small_size_2_2: "\<lbrakk>
  invariant (big, small);
  0 < Small.size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> tl (toCurrentListSmallFirst (big, small)) = toCurrentListSmallFirst (big, small')"
  apply(auto simp: currentList_pop_2  split: prod.splits)
  using Small_Proof.currentList_empty_2 tl_append2 by blast

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
      by(auto simp: Stack_Proof.size_pop size_isNotEmpty split: Big.state.splits)
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

lemma tick_size_big: "invariant (big, small) \<Longrightarrow> tick (big, small) = (big', small') \<Longrightarrow> Big.size big = Big.size big'"
  apply(induction "(big, small)" rule: tick.induct)
  by(auto simp: Big_Proof.tick_size split: current.splits)

lemma tick_size_small: "invariant (big, small) \<Longrightarrow> tick (big, small) = (big', small') \<Longrightarrow> Small.size small = Small.size small'"
  apply(induction "(big, small)" rule: tick.induct)
  by(auto simp: Small_Proof.tick_size split: current.splits)

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

lemma remainingStepsDecline_3: "invariant states \<Longrightarrow> Suc n < remainingSteps states \<Longrightarrow> n < remainingSteps (tick states)"
  apply(induction n)
   apply (metis Suc_lessD gr_zeroI less_not_refl3 remainingStepsDecline_2)
  by (metis Suc_lessD Suc_lessE Suc_lessI dual_order.strict_implies_not_eq remainingStepsDecline_2 zero_less_Suc)

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
  sorry (* TODO *)

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
      subgoal  sorry 
      using Common_Proof.some_empty sorry
  qed
qed

(* TODO: check if this is still correct! *)
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

lemma same_3: "invariant (big, small) \<Longrightarrow> remainingSteps (big, small) \<ge> 4 \<Longrightarrow> inSizeWindow (big, small) \<Longrightarrow> inSizeWindow ((tick ^^ 6) (big, Small.push x small))"
  apply auto
  sorry

lemma sizeWindow_smallSize: "0 < remainingSteps (big, small) \<Longrightarrow> inSizeWindow (big, small) \<Longrightarrow> 0 < Small.size small"
  apply(induction small arbitrary: big)
  by auto

lemma sizeWindow_bigSize: "0 < remainingSteps (big, small) \<Longrightarrow> inSizeWindow (big, small) \<Longrightarrow> 0 < Big.size big"
  apply(induction big arbitrary: small)
  by auto

end
