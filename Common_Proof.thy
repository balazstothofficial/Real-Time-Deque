theory Common_Proof
  imports Common Idle_Proof Current_Proof
begin

lemma revN_take: "revN n xs acc = rev (take n xs) @ acc"
  apply(induction n xs acc rule: revN.induct)
  by auto

lemma revN_revN: "(revN n (revN n xs []) []) = take n xs"
  by(auto simp: revN_take)

lemma tt: "aux \<noteq> [] \<Longrightarrow> take 1 (rev aux) = [last aux]"
  apply(induction aux)
   apply auto
  by (meson Suc_leI length_greater_0_conv)

lemma take_hd: "xs \<noteq> [] \<Longrightarrow> take (Suc 0) xs = [hd xs]"
  apply(induction xs)
  by auto

lemma ttt: "\<not>Stack.isEmpty old \<Longrightarrow> [first old] = take 1 (Stack.toList old)"
  by(auto simp:  first not_empty_2 take_hd)

lemma tick_toList_helper: "\<lbrakk>a \<le> Suc b; b < a\<rbrakk> \<Longrightarrow> a - b = 1"
  by auto

lemma tick_toList: "invariant common \<Longrightarrow> toList (tick common) = toList common"
proof(induction common rule: tick.induct)
  case (1 idle)
  then show ?case by auto
next
  case (2 current aux new moved)
  then show ?case 
    apply (auto split: current.splits)
    subgoal for x1a x3a x4a
       apply(induction "x4a - length new" aux new rule: revN.induct)
      by(auto simp: tick_toList_helper)
    by (metis Nitpick.size_list_simp(2) Suc_diff_Suc gen_length_def le_SucI length_code list.exhaust_sel not_le revN.simps(3))
qed

lemma tick_toList_2: "invariant common \<Longrightarrow> tick common = common' \<Longrightarrow> toList common = toList common'" 
  using tick_toList by fastforce

lemma tick_toCurrentList: "invariant common \<Longrightarrow> toCurrentList (tick common) = toCurrentList common"
  apply(induction common)
  by(auto split: current.splits)


lemma push: "toList (push x common) = x # toList common"
proof(induction x common rule: push.induct)
  case (1 x stack stackSize)
  then show ?case by(auto simp: Stack_Proof.push)
next
  case (2 x current aux new moved)
  then show ?case 
    apply(induction x current rule: put.induct)
    by auto
qed

lemma invariant_tick: "invariant common \<Longrightarrow> invariant (tick common)" 
proof(induction "common" rule: invariant.induct)
  case (1 idle)
  then show ?case
    by auto
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current)
    case (Current extra added old remained)
    then show ?case
    proof(induction aux)
      case Nil
      then show ?case
        by auto
    next
      case (Cons a as)
      then show ?case
        apply auto
        by (metis Suc_diff_Suc le_SucI not_le revN.simps(3))
     qed
  qed
qed

  
lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
  apply(induction x common rule: push.induct)
   apply(auto simp: invariant_put Stack_Proof.size_push split: stack.splits current.splits)
  by (metis Current.newSize.simps Current.toList.elims Nat.add_0_right One_nat_def add_Suc add_Suc_right put.simps)


lemma something: "\<not>Stack.isEmpty old \<Longrightarrow> remained > 0 \<Longrightarrow> first old # take (remained - Suc 0) (Stack.toList (Stack.pop old)) = take remained (Stack.toList old)"
  apply(induction old rule: Stack.pop.induct)
    apply auto
   apply (metis One_nat_def diff_Suc_eq_diff_pred gr_implies_not0 take_Cons' take_append)
  by (simp add: take_Cons')
  
lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty common; 
  invariant common;
  pop common = (x, common')
\<rbrakk> \<Longrightarrow> invariant common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case 
    apply(induction idle arbitrary: x rule: Idle.pop.induct)
    apply(induction current rule: get.induct)
    by (auto simp: Stack_Proof.size_pop)
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then have t: "x # take (remained - Suc 0) (Stack.toList (Stack.pop old)) = take remained (Stack.toList old)"
      apply(auto simp: revN_take split: if_splits)
       apply (metis less_imp_Suc_add something zero_less_Suc)
      by (metis less_imp_Suc_add something zero_less_Suc)

    from 1 have tt: "take (Stack.size old) (rev (take (remained - length new) aux)) = x # take (Stack.size old - Suc 0) (rev (take (remained - Suc (length new)) aux))"
      apply(auto simp: revN_take split: if_splits)
      apply (smt (z3) Suc_leI diff_Suc_eq_diff_pred diff_commute diff_is_0_eq hd_append2 length_greater_0_conv length_take less_add_same_cancel2 less_le_trans list.sel(1) min.absorb2 not_empty_2 rev_is_Nil_conv rev_rev_ident singleton_rev_conv size_listLength t take_all tt zero_less_diff)
      (* TODO: just times out but works! *)
      sorry
 

    from 1 have ttt: "take (Stack.size old - min (length aux) (remained - length new)) new = take (Stack.size old - Suc (min (length aux) (remained - Suc (length new)))) new"
      apply(auto split: if_splits)
       apply (metis One_nat_def Suc_diff_Suc diff_Suc_eq_diff_pred diff_is_0_eq' le_diff_conv min.absorb2)
      by (simp add: min.absorb2)

    from 1 show ?case
      apply(auto)
      apply linarith+
      apply(auto simp: revN_take Stack_Proof.size_pop t tt ttt)
      using t by force
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma currentList_push: "toCurrentList (push x left) = x # toCurrentList left"
  apply(induction x left rule: push.induct)
  by(auto simp: put)


lemma list_pop: "invariant common \<Longrightarrow> \<not>isEmpty common \<Longrightarrow> pop common = (x, common') \<Longrightarrow>
   toList common = x # toList common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case
    by(auto simp: Idle_Proof.pop split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
    proof(induction "remained - Suc 0 \<le> length new")
      case True

      then have hd: "first old = hd aux"
        apply(auto simp: revN_take)
        by (smt (z3) Suc_diff_Suc diff_add_inverse diff_commute diff_is_0_eq first hd_append2 hd_conv_nth hd_drop_conv_nth hd_take le_add1 le_add_diff_inverse2 length_greater_0_conv length_rev lessI less_add_same_cancel2 less_le_trans less_or_eq_imp_le not_empty_2 rev_nth rev_take size_listLength take_eq_Nil)

      from True have 1: "remained - length new = Suc 0"
        by auto
     
      with 1 True take_hd show ?case 
        apply(auto simp: revN_take)
        by (smt (z3) Nat.add_0_right add.commute hd leD list.size(3) take_hd)
    next
      case False
    
      from False show ?case 
      proof(induction "length aux = remained - length new")
        case True

        then have a: "aux \<noteq> []"
          by auto

        from True have b: "\<not>Stack.isEmpty old"
          by auto
        
        from True have "take 1 (Stack.toList old) = take 1 (rev aux)"
          apply(auto simp: revN_take)
          by (smt (z3) add_gr_0 hd_append2 hd_take le_add_diff_inverse2 length_greater_0_conv length_rev less_imp_le_nat not_empty_2 size_listLength take_eq_Nil take_hd zero_less_diff)

        then have "[last aux] = [first old]"
          using tt ttt a b 
          by fastforce

        then have "last aux = first old"
          by auto

        with True show ?case 
          apply(auto simp: revN_take min_def split: if_splits)
          by (metis Suc_eq_plus1 butlast_conv_take diff_diff_left diff_less_mono2 less_nat_zero_code list.size(3) snoc_eq_iff_butlast)
      next
        case False

        then have a: "take (remained - length new) aux \<noteq> []"
          by auto

        from False have b: "\<not>Stack.isEmpty old"
          by auto

        from False have "take 1 (Stack.toList old) = take 1 (rev (take (remained - length new) aux))"
          apply(auto simp: revN_take)
          by (smt (verit, ccfv_threshold) Nil_is_append_conv Nil_is_rev_conv bot_nat_0.extremum_uniqueI diff_is_0_eq hd_append2 hd_take length_greater_0_conv less_add_same_cancel2 less_le_trans not_empty_2 not_le size_listLength take_eq_Nil take_hd)


        then have c: "[first old] = [last (take (remained - length new) aux)]"
          using tt ttt a b
          by metis


        with False show ?case 
          apply(auto simp: revN_take min_def split: if_splits)
          by (smt (z3) Nil_is_rev_conv Suc_diff_Suc first hd_append2 hd_rev hd_take last_snoc le_Suc_eq length_greater_0_conv less_imp_Suc_add not_empty_2 not_le size_listLength take_eq_Nil take_hd_drop zero_less_Suc)
      qed
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma currentList_pop: "\<not>isEmpty common \<Longrightarrow> pop common = (x, common') \<Longrightarrow> toCurrentList common' = tl (toCurrentList common)"
  apply(induction common arbitrary: x rule: pop.induct)
   apply(auto simp: get split: prod.splits current.splits if_splits)
    apply (metis get list.sel(3))
   apply (metis Current.toList.simps get list.sel(3))
  by (metis Current.toList.simps get list.sel(3))

lemma some_empty: "\<lbrakk>isEmpty (tick common); \<not> isEmpty common; invariant common\<rbrakk> \<Longrightarrow> False"
  apply(induction common rule: tick.induct)
  by(auto split: current.splits if_splits)

lemma currentList_empty: "\<lbrakk>\<not> Common.isEmpty common; Common.toCurrentList common = []; Common.invariant common\<rbrakk>
   \<Longrightarrow> False"
  apply(induction common)
   apply(auto split: current.splits)
  using not_empty_2 apply blast
  by (metis get list.discI surj_pair)

lemma tick_size: "invariant common \<Longrightarrow> size common = size (tick common)"
  apply(induction common rule: tick.induct)
  by(auto split: current.splits)

lemma tick_not_empty: "invariant common \<Longrightarrow> \<not>isEmpty common \<Longrightarrow> \<not>isEmpty (tick common)"
  apply(induction common rule: tick.induct)
  by(auto split: current.splits)

lemma push_not_empty: "\<lbrakk>\<not> isEmpty state; isEmpty (push x state)\<rbrakk> \<Longrightarrow> False"
  apply(induction x state rule: push.induct)
   apply(auto simp: put_not_empty push_not_empty split: current.splits)
  using put_not_empty push_not_empty by fastforce+

end