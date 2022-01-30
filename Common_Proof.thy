theory Common_Proof
  imports Common Idle_Proof Current_Proof ReverseN_Proof
begin

(* TODO: *)
lemma tick_toList_helper: "\<lbrakk>a \<le> Suc b; b < a\<rbrakk> \<Longrightarrow> a - b = 1"
  by auto

(* TODO: *)
lemma tick_toList: "invariant common \<Longrightarrow> toList (tick common) = toList common"
proof(induction common rule: tick.induct)
  case (1 idle)
  then show ?case by auto
next
  case (2 current aux new moved)
  then show ?case 
    apply (auto split: current.splits)
    subgoal for x1a x3a x4a
      apply(induction "x4a - length new" aux new rule: reverseN.induct)
      by(auto simp: tick_toList_helper)
    by (metis Nitpick.size_list_simp(2) Suc_diff_Suc gen_length_def le_SucI length_code list.exhaust_sel not_le reverseN.simps(3))
qed

lemma tick_toList_2: "invariant common \<Longrightarrow> tick common = common' \<Longrightarrow> toList common = toList common'" 
  using tick_toList by fastforce

lemma tick_toCurrentList: "invariant common \<Longrightarrow> toCurrentList (tick common) = toCurrentList common"
  apply(induction common)
  by(auto split: current.splits)

lemma push_toList: "toList (push x common) = x # toList common"
proof(induction x common rule: push.induct)
  case (1 x stack stackSize)
  then show ?case 
    by(auto simp: Stack_Proof.push_toList)
next
  case (2 x current aux new moved)
  then show ?case 
    apply(induction x current rule: put.induct)
    by auto
qed

(* TODO: *)
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
        apply(auto)
        by (metis Suc_diff_Suc le_SucI not_le reverseN.simps(3))
     qed
  qed
qed

lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
  apply(induction x common rule: push.induct)
  by(auto simp: invariant_put Stack_Proof.size_push put_size split: stack.splits current.splits)

(* TODO: *)
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
  proof(induction current arbitrary: common' rule: get.induct)
    case (1 added old remained)

    from 1 have a: "
         take (Stack.size (Stack.pop old) - min (length aux) (remained - Suc (length new))) new =
         take (Stack.size old - min (length aux) (remained - length new)) new"
      apply(auto simp: reverseN_take min_def split: if_splits)
      apply (smt (z3) Nat.le_imp_diff_is_add Stack_Proof.size_pop Suc_pred add.commute diff_Suc_diff_eq2 le_add2 le_diff_conv less_imp_le size_isNotEmpty verit_la_disequality)
      apply (smt (z3) add_diff_cancel_right' diff_Suc_diff_eq2 le_add2 le_add_diff_inverse le_diff_conv less_imp_le pop_listLength size_listLength verit_la_disequality)
      by (metis add_Suc pop_listLength size_listLength)+

    with 1 have b: "first old # (rev (take (remained - Suc (length new)) aux)) =
         (rev (take (remained - length new) aux))"
      apply(auto simp: reverseN_take split: if_splits)
      apply (smt (z3) One_nat_def Suc_diff_Suc append_self_conv2 diff_Suc_1 diff_Suc_Suc diff_is_0_eq' first_pop hd_append2 hd_take le_diff_conv length_greater_0_conv length_take less_imp_Suc_add list.sel(1) min.absorb2 rev_singleton_conv size_isNotEmpty take_append take_eq_Nil take_hd_drop zero_less_Suc)
      by (smt (z3) Cons_nth_drop_Suc Nat.diff_diff_right Suc_diff_le Suc_leI add_Suc_right diff_le_self first_pop hd_append2 hd_take length_greater_0_conv length_rev lessI less_le less_le_trans list.sel(1) rev_take size_isNotEmpty take_eq_Nil zero_less_diff)
    
    from 1 have c: "
      x # take (Stack.size (Stack.pop old)) (reverseN (remained - Suc (length new)) aux new) = 
          take (Stack.size old) (reverseN (remained - length new) aux new)"
      apply(auto simp: reverseN_take a split: if_splits)
      apply (smt (z3) Nil_is_append_conv Stack_Proof.size_pop Suc_le_eq append_take_drop_id diff_commute diff_is_0_eq' first_pop hd_append2 le_diff_conv length_greater_0_conv length_take list.sel(1) min.absorb2 rev.simps(2) rev_append rev_is_Nil_conv rev_rev_ident rev_take size_isNotEmpty take_eq_Nil take_hd_drop zero_less_diff)
      by (metis pop_listLength size_listLength take_Suc_Cons b)

    from 1 show ?case 
      apply auto
        apply linarith+
      by (metis One_nat_def c first_pop list.sel(3) tl_take)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma invariant_pop_2_helper: "\<lbrakk>
  0 < Current.size current; 
  Current.invariant current; 
  Current.newSize current = Stack.size stack; 
  get current = (x, current')
\<rbrakk> \<Longrightarrow> Current.newSize current' = Stack.size (Stack.pop stack) "
proof(induction current rule: get.induct)
  case (1 added old remained)
  then show ?case
    apply auto
    apply(induction stack rule: Stack.pop.induct)
    by auto
next
  case (2 x xs added old remained)
  then show ?case 
    apply auto
    apply(induction stack rule: Stack.pop.induct)
    by auto
qed

(* TODO: *)
lemma invariant_pop_2: "\<lbrakk>
  0 < size common; 
  invariant common;
  pop common = (x, common')
\<rbrakk> \<Longrightarrow> invariant common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case 
  proof(induction idle rule: Idle.pop.induct)
    case (1 stack stackSize)
    then show ?case 
      apply(auto simp: invariant_pop_2_helper invariant_get_size split: prod.splits)
      by (metis One_nat_def Stack.isEmpty.simps(1) Stack.pop.simps(1) Stack_Proof.size_isEmpty Stack_Proof.size_pop invariant_pop_2_helper length_tl list.sel(2) list.size(3))
  qed
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)

    from 1 have a: "first old # rev (take (remained - Suc (length new)) aux) =
          rev (take (remained - length new) aux)"
      apply(auto simp: reverseN_take split: if_splits)
      apply (smt (verit, best) Nil_is_append_conv Suc_pred append_self_conv2 bot_nat_0.not_eq_extremum diff_commute first_pop hd_append2 hd_take leD length_greater_0_conv less_add_same_cancel2 less_le_trans list.sel(1) rev.simps(1) rev.simps(2) size_isNotEmpty take_eq_Nil take_hd_drop zero_less_diff)
      by (smt (verit, best) Nat.diff_diff_right Suc_diff_Suc Suc_diff_le Suc_leI add_Suc_right bot_nat_0.not_eq_extremum first_pop hd_append2 hd_take leD length_greater_0_conv list.sel(1) rev_eq_Cons_iff rev_is_Nil_conv rev_rev_ident size_isNotEmpty take_eq_Nil take_hd_drop zero_less_Suc zero_less_diff)

    from 1 have b: "
      x # take (Stack.size (Stack.pop old)) (rev (take (remained - Suc (length new)) aux)) = 
      take (Stack.size old) (rev (take (remained - length new) aux))"
      apply(auto simp: reverseN_take split: if_splits)
      apply (smt (z3) Nil_is_append_conv One_nat_def Suc_diff_Suc append_assoc append_eq_conv_conj append_self_conv2 append_take_drop_id diff_Suc_eq_diff_pred diff_is_0_eq' first_pop hd_conv_nth hd_drop_conv_nth le_diff_conv length_greater_0_conv length_take list.sel(1) min.absorb2 singleton_rev_conv size_isNotEmpty take_eq_Nil take_hd_drop)
      by (metis One_nat_def Stack_Proof.size_pop a bot_nat_0.not_eq_extremum size_isNotEmpty take_Cons')

    from 1 show ?case 
      apply(auto simp: reverseN_take)
      apply linarith+
      by (smt (verit, del_insts) One_nat_def Stack_Proof.size_pop Suc_diff_Suc append_Cons b diff_Suc_eq_diff_pred diff_le_self dual_order.trans first_take_pop le_diff_conv length_greater_0_conv less_le_trans less_or_eq_imp_le list.inject list.size(3) min.absorb2 size_isNotEmpty)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma currentList_push: "toCurrentList (push x left) = x # toCurrentList left"
  apply(induction x left rule: push.induct)
  by(auto simp: put_toList)

(* TODO: *)
lemma list_pop: "invariant common \<Longrightarrow> \<not>isEmpty common \<Longrightarrow> pop common = (x, common') \<Longrightarrow>
   toList common = x # toList common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case
    by(auto simp: Idle_Proof.pop_toList split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
    proof(induction "remained - Suc 0 \<le> length new")
      case True

      then have hd: "first old = hd aux"
        apply(auto simp: reverseN_take)
        by (smt (z3) Suc_diff_Suc diff_add_inverse diff_commute diff_is_0_eq first_toList hd_append2 hd_conv_nth hd_drop_conv_nth hd_take le_add1 le_add_diff_inverse2 length_greater_0_conv length_rev lessI less_add_same_cancel2 less_le_trans less_or_eq_imp_le toList_isNotEmpty rev_nth rev_take size_listLength take_eq_Nil)

      from True have 1: "remained - length new = Suc 0"
        by auto
     
      with 1 True take_hd show ?case 
        apply(auto simp: reverseN_take)
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
          apply(auto simp: reverseN_take)
          by (smt (z3) add_gr_0 hd_append2 hd_take le_add_diff_inverse2 length_greater_0_conv length_rev less_imp_le_nat toList_isNotEmpty size_listLength take_eq_Nil take_hd zero_less_diff)

        then have "[last aux] = [first old]"
          using take_last first_take a b 
          by fastforce

        then have "last aux = first old"
          by auto

        with True show ?case 
          apply(auto simp: reverseN_take min_def split: if_splits)
          by (metis Suc_eq_plus1 butlast_conv_take diff_diff_left diff_less_mono2 less_nat_zero_code list.size(3) snoc_eq_iff_butlast)
      next
        case False

        then have a: "take (remained - length new) aux \<noteq> []"
          by auto

        from False have b: "\<not>Stack.isEmpty old"
          by auto

        from False have "take 1 (Stack.toList old) = take 1 (rev (take (remained - length new) aux))"
          apply(auto simp: reverseN_take)
          by (smt (verit, ccfv_threshold) Nil_is_append_conv Nil_is_rev_conv bot_nat_0.extremum_uniqueI diff_is_0_eq hd_append2 hd_take length_greater_0_conv less_add_same_cancel2 less_le_trans toList_isNotEmpty not_le size_listLength take_eq_Nil take_hd)


        then have c: "[first old] = [last (take (remained - length new) aux)]"
          using take_last first_take a b
          by metis


        with False show ?case 
          apply(auto simp: reverseN_take min_def split: if_splits)
          by (smt (z3) Nil_is_rev_conv Suc_diff_Suc first_toList hd_append2 hd_rev hd_take last_snoc le_Suc_eq length_greater_0_conv less_imp_Suc_add toList_isNotEmpty not_le size_listLength take_eq_Nil take_hd_drop zero_less_Suc)
      qed
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed


(* TODO: *)
lemma currentList_pop: "\<not>isEmpty common \<Longrightarrow> pop common = (x, common') \<Longrightarrow> toCurrentList common' = tl (toCurrentList common)"
  apply(induction common arbitrary: x rule: pop.induct)
  apply(auto simp: get_toList split: prod.splits current.splits if_splits)
  apply (metis get_toList list.sel(3))
  by (metis Current.toList.simps get_toList list.sel(3))+ 

(* TODO: *)
lemma currentList_pop_2: "invariant common \<Longrightarrow> 0 < size common \<Longrightarrow> pop common = (x, common') \<Longrightarrow> toCurrentList common' = tl (toCurrentList common)"
  apply(induction common arbitrary: x rule: pop.induct)
  apply(auto simp: get_toList_size split: prod.splits current.splits if_splits)
  apply (metis get_toList_size list.sel(3))
  apply (smt (z3) Current.isEmpty.simps Current.toList.simps append_Cons get_toList less_nat_zero_code list.exhaust_sel list.inject)
  apply (metis Current.isEmpty.simps Current.toList.simps get_toList less_nat_zero_code list.sel(3) size_isNotEmpty)
  apply (metis Current.isEmpty.simps Current.toList.simps get_toList length_0_conv less_irrefl_nat less_or_eq_imp_le list.sel(3) reverseN.simps(1) reverseN_reverseN take_all tl_append2)
  by (metis Current.isEmpty.simps Current.toList.simps Suc_diff_Suc get_toList list.sel(3) size_isNotEmpty not_gr_zero zero_diff zero_less_Suc)

lemma some_empty: "\<lbrakk>isEmpty (tick common); \<not> isEmpty common; invariant common\<rbrakk> \<Longrightarrow> False"
  apply(induction common rule: tick.induct)
  by(auto split: current.splits if_splits)

(* TODO: *)
lemma currentList_empty: "\<lbrakk>\<not> Common.isEmpty common; Common.toCurrentList common = []; Common.invariant common\<rbrakk>
   \<Longrightarrow> False"
  apply(induction common)
   apply(auto split: current.splits)
  using toList_isNotEmpty apply blast
  by (metis get_toList list.discI surj_pair)

(* TODO: *)
lemma currentList_empty_2: "\<lbrakk>0 < Common.size x; Common.toCurrentList x = []; Common.invariant x\<rbrakk> \<Longrightarrow> False"
  apply(induction x)
   apply(auto simp: reverseN_take split: current.splits)
  by (metis get_toList_size list.distinct(1) surj_pair)

lemma tick_size: "invariant common \<Longrightarrow> size common = size (tick common)"
  apply(induction common rule: tick.induct)
  by(auto split: current.splits)

lemma tick_not_empty: "invariant common \<Longrightarrow> \<not>isEmpty common \<Longrightarrow> \<not>isEmpty (tick common)"
  apply(induction common rule: tick.induct)
  by(auto split: current.splits)

(* TODO: *)
lemma push_not_empty: "\<lbrakk>\<not> isEmpty state; isEmpty (push x state)\<rbrakk> \<Longrightarrow> False"
  apply(induction x state rule: push.induct)
  apply(auto simp: put_isNotEmpty push_isNotEmpty split: current.splits)
  using put_isNotEmpty push_isNotEmpty by fastforce+

lemma size_isEmpty: "invariant common \<Longrightarrow> size common = 0 \<Longrightarrow> isEmpty common"
  apply(induction common)
  by(auto simp: Stack_Proof.size_isEmpty size_isEmpty split: current.splits)

end