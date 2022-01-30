theory Small_Proof 
  imports Common_Proof Small
begin

lemma tick_toCurrentList: "invariant small \<Longrightarrow> toCurrentList (tick small) = toCurrentList small"
  apply(induction small rule: tick.induct)
  by(auto simp: tick_toCurrentList split: current.splits)

lemma tick_toList_common: "small = Common common \<Longrightarrow> invariant small \<Longrightarrow> toList (tick small) = toList small"
  by(auto simp: tick_toList)

(* TODO: *)
lemma tick_toList_reverse2: "small = (Reverse2 current aux big new count) \<Longrightarrow> invariant small \<Longrightarrow> toList (tick small) = toList small"
  apply(auto simp: reverseN_take split: current.splits)
  using toList_isEmpty apply blast
  using Stack_Proof.size_isEmpty apply blast
  using size_isNotEmpty apply blast
  using Stack_Proof.size_isEmpty toList_isEmpty apply force
   apply (metis add_diff_cancel_left' first_pop pop_listLength rev.simps(2) size_listLength)
  by (metis add_diff_cancel_left' first_pop pop_listLength rev.simps(2) size_listLength)
 
lemma invariant_tick: "invariant small \<Longrightarrow> invariant (tick small)" 
proof(induction small rule: tick.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invariant_tick)
next
  case (2 current small aux)
  then show ?case
  proof(induction "Stack.toList small")
    case Nil
    then show ?case
      using toList_isNotEmpty by fastforce
  next
    case (Cons a x)
    then show ?case 
    proof(induction current)
      case (Current extra added old remained)
      then have notEmpty: "\<not>Stack.isEmpty small"
        apply auto
        by (metis list.distinct(1) toList_isEmpty)


      from Current have a: "rev aux @ Stack.toList small =
         rev (take (List.length aux + List.length (Stack.toList small) - (List.length (Stack.toList small) - Suc 0)) (first small # aux)) @
         tl (Stack.toList small)"
        apply(auto simp: notEmpty split: if_splits)
        by (smt (verit, ccfv_threshold) Nat.add_diff_assoc One_nat_def append_Cons append_eq_append_conv2 diff_add_inverse diff_le_self first_pop length_tl list.sel(3) list.size(4) nat_le_linear rev.simps(2) self_append_conv2 take_all toList_isEmpty)

      have b: "\<lbrakk>
      x = Stack.toList small \<Longrightarrow>
     Stack.size old \<le> Suc (Stack.size (Stack.pop small) + List.length aux) \<and>
     rev (take (Stack.size old - List.length (Stack.toList small)) aux) @ Stack.toList small =
     rev (take (Stack.size old - List.length (Stack.toList (Stack.pop small))) (first small # aux)) @
     rev (take (Stack.size old) (rev (Stack.toList (Stack.pop small))));

     a # x = Stack.toList small; 
     added = List.length extra; 
     Stack.size old \<le> remained; 
     Stack.size old \<le> Stack.size small + List.length aux;
     Stack.toList old = rev (take (Stack.size old - List.length (Stack.toList small)) aux) @ Stack.toList small;
     \<not> List.length aux \<le> Stack.size old - List.length (Stack.toList small); 
     aux \<noteq> []; 
      List.length (Stack.toList small) \<le> Stack.size old
    \<rbrakk>  \<Longrightarrow>  rev (take (Stack.size old - (List.length (Stack.toList small) - Suc 0)) (first small # aux)) = 
            rev (take (Stack.size old - List.length (Stack.toList small)) aux) @ [first small]"
        by (metis One_nat_def Suc_diff_eq_diff_pred Suc_diff_le length_greater_0_conv list.distinct(1) rev.simps(2) take_Suc_Cons)

       
    from Current have "
     rev (take (List.length (Stack.toList old) - List.length (Stack.toList small)) aux) @
     rev (take (List.length (Stack.toList old)) (rev (Stack.toList small))) =
         rev (take (List.length (Stack.toList old) - (List.length (Stack.toList small) - Suc 0)) (first small # aux)) @
         rev (take (List.length (Stack.toList old)) (rev (tl (Stack.toList small))))"
      apply(auto simp: min_def)
      apply (smt (verit, ccfv_threshold) One_nat_def Stack_Proof.pop_toList Suc_diff_eq_diff_pred Suc_diff_le append_Cons append_eq_append_conv2 append_self_conv diff_is_0_eq first_pop length_greater_0_conv length_tl list.size(3) rev_is_Nil_conv rev_singleton_conv size_listLength take_all take_eq_Nil tl_Nil toList_isEmpty)
      apply (smt (z3) append_same_eq append_take_drop_id butlast_append butlast_rev drop_all_iff drop_butlast length_rev)
      subgoal by(auto simp: a)
      subgoal 
        apply(auto simp: b notEmpty) 
        by (metis Stack_Proof.pop_toList first_pop notEmpty)
      by (metis append_eq_conv_conj append_take_drop_id butlast_append butlast_rev drop_all_iff length_rev size_listLength)    

    with Current show ?case 
      by(auto simp: Stack_Proof.pop_toList size_listLength)
  qed
  qed

  
next
  case (3 current auxS big newS count)
  then show ?case
    apply(auto simp: split: current.splits) 
          apply (metis length_0_conv toList_isNotEmpty size_listLength)
    using size_isNotEmpty apply blast
        apply (meson add_decreasing le_less_linear size_isNotEmpty)
    using size_isNotEmpty apply blast
      apply(auto simp: reverseN_take)
      apply (metis Nat.add_0_right add.commute toList_isNotEmpty le_refl list.size(3) size_listLength take_all)
     apply (simp add: Stack_Proof.size_pop)
    by (metis first_pop length_Cons size_listLength)
qed

lemma invariant_push: "invariant small \<Longrightarrow> invariant (push x small)"
  apply(induction x small rule: push.induct)
  by(auto simp: invariant_push split: current.splits)
    
lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty small; 
  invariant small;
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> invariant small'"
proof(induction small arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: invariant_pop split: prod.splits)
next
  case (2 current small aux)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto simp: Stack_Proof.size_pop)
        apply linarith+
      proof(induction "Stack.size old \<le> List.length (Stack.toList small)")
        case True
        then show ?case apply auto 
          by (metis One_nat_def Stack_Proof.pop_toList Suc_diff_eq_diff_pred Suc_diff_le drop_Suc length_rev rev_take size_isNotEmpty tl_drop)
      next
        case False
        then show ?case 
        proof(induction "Stack.size old \<le> Suc (List.length (Stack.toList small))")
          case True
          then show ?case apply auto
            by (smt (z3) One_nat_def Stack_Proof.pop_toList Suc_le_lessD append.left_neutral diff_add_inverse2 le_SucE less_add_same_cancel1 plus_1_eq_Suc rev.simps(1) rev_eq_Cons_iff size_listLength take_eq_Nil take_hd_drop take_tl tl_append2)
        next
          case False
          then have a: "rev (take (Stack.size old - List.length (Stack.toList small)) aux) = 
                 x # rev (take (Stack.size old - Suc (List.length (Stack.toList small))) aux)"
            apply auto 
            by (smt (z3) Suc_diff_Suc diff_add_inverse2 first_pop hd_append2 hd_rev last_snoc le_Suc_eq length_append length_rev lessI list.sel(1) not_le size_listLength take_all_iff take_eq_Nil take_hd_drop)
  

          from False show ?case 
            by(auto simp: a Stack_Proof.pop_toList)
        qed
      qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case (3 current auxS big newS count)
  then show ?case 
     apply(induction current rule: get.induct)
     apply(auto simp: Stack_Proof.size_pop)
     apply (metis length_greater_0_conv less_eq_Suc_le toList_isNotEmpty ordered_cancel_comm_monoid_diff_class.diff_add_assoc size_listLength)
     using diff_le_mono le_add2 apply blast
     apply (meson diff_le_self le_trans)
     apply (smt (z3) Stack_Proof.pop_toList Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc rev_take size_isNotEmpty tl_drop)
     apply (simp add: Suc_leI size_isNotEmpty)
     apply (simp add: diff_le_mono)
     apply linarith
     apply (smt (z3) Stack_Proof.pop_toList Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc rev_take size_isNotEmpty tl_drop)
     apply linarith+
     by (simp add: Stack_Proof.pop_toList Suc_diff_le drop_Suc rev_take tl_drop)
qed

lemma invariant_pop_2_helper: "\<lbrakk>
  0 < Stack.size old; 
  Stack.size old \<le> Stack.size small + List.length auxS;
  Stack.toList old = 
    rev (take (Stack.size old - List.length (Stack.toList small)) auxS) @ 
    rev (take (Stack.size old) (rev (Stack.toList small)))
\<rbrakk> \<Longrightarrow> Stack.toList (Stack.pop old) =
        rev (take (Stack.size (Stack.pop old) - List.length (Stack.toList small)) auxS) @
        rev (take (Stack.size (Stack.pop old)) (rev (Stack.toList small)))"
proof(induction "Stack.size old \<le> Stack.size small")
  case True
  then show ?case 
    apply auto
    by (smt (z3) Stack_Proof.pop_toList Stack_Proof.size_pop Suc_diff_le Suc_pred diff_Suc_Suc diff_is_0_eq' drop_Suc length_rev nat_le_linear size_isNotEmpty not_less_eq_eq rev.simps(1) rev_take self_append_conv2 size_listLength take_eq_Nil tl_drop)
next
  case False
  then show ?case
    apply auto
    by (smt (verit) False(2) Stack_Proof.pop_toList Stack_Proof.size_pop Suc_diff_le Suc_pred diff_Suc_Suc diff_diff_left diff_is_0_eq drop_Suc le_add_diff_inverse length_0_conv length_rev less_Suc_eq_le less_imp_diff_less size_isNotEmpty not_less_eq_eq rev_take size_listLength take_eq_Nil tl_append2 tl_drop)
qed

lemma invariant_pop_2: "\<lbrakk>
  0 < Small.size small; 
  invariant small;
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> invariant small'"
proof(induction small arbitrary: x rule: pop.induct)
case (1 state)
  then show ?case by(auto simp: invariant_pop_2 split: prod.splits)
next
  case (2 current small auxS)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto)
        apply (simp add: Stack_Proof.size_pop size_isNotEmpty)
       apply (simp add: Stack_Proof.size_pop size_isNotEmpty)
      by (simp add: invariant_pop_2_helper)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case (3 current auxS big newS count)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      apply auto 
      apply (auto simp: Stack_Proof.size_pop size_isNotEmpty Suc_leI)
      by (metis One_nat_def Suc_diff_eq_diff_pred Suc_diff_le drop_Suc first_pop list.sel(3) rev_take size_isNotEmpty tl_drop)
  next
    case (2 x xs added old remained)
    then show ?case by auto 
  qed
qed

lemma push_toList_common: "small = Common common \<Longrightarrow> toList (push x small) = x # toList small"
  by(auto simp: Common_Proof.push_toList)

lemma push_toList_reverse2: "small = (Reverse2 current auxS big newS count) \<Longrightarrow> toList (push x small) = x # toList small"
proof(induction x current rule: put.induct)
  case (1 element extra added old remained)
  then show ?case by auto
qed

lemma pop_toList_common: "\<lbrakk>
  small = Common common;
  \<not>isEmpty small; 
  invariant small; 
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> x # toList small' = toList small"
  by(auto simp: Common_Proof.list_pop split: prod.splits)


lemma pop_toList_reverse2: "\<lbrakk>
  small = (Reverse2 current auxS big newS count);
  \<not>isEmpty small; 
  invariant small; 
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> x # toList small' = toList small"
proof(induction current arbitrary: x rule: get.induct)
  case (1 added old remained)
  then show ?case 
    apply(auto simp: reverseN_take)
    by (smt (z3) Stack_Proof.pop_toList Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc first_pop rev_take size_isNotEmpty tl_drop)+
next
  case (2 x xs added old remained)
  then show ?case by auto
qed

lemma currentList_push: "toCurrentList (push x small) = x # toCurrentList small"
  apply(induction x small rule: push.induct)
  by(auto simp: currentList_push put_toList)

lemma currentList_pop: "\<not> isEmpty small \<Longrightarrow> pop small = (x, small') \<Longrightarrow> toCurrentList small' = tl (toCurrentList small)"
  apply(induction small arbitrary: x rule: pop.induct)
    apply(auto simp: currentList_pop put_toList split: prod.splits)
   apply (metis get_toList list.sel(3))
  by (metis get_toList list.sel(3))

lemma currentList_pop_2: "invariant small \<Longrightarrow> 0 < size small \<Longrightarrow> pop small = (x, small') \<Longrightarrow> toCurrentList small' = tl (toCurrentList small)"
  apply(induction small arbitrary: x rule: pop.induct)
  apply(auto simp: Common_Proof.currentList_pop_2 put_toList get_toList_size split: prod.splits current.splits)
  subgoal
    by (metis Current.toList.simps Pair_inject get.simps(2) list.exhaust_sel)
  apply (smt (z3) Current.invariant.simps Current.size.simps Current.toList.simps Suc_diff_Suc Suc_pred \<open>\<And>x4 x3 x2 x1a x1 smalla auxS. \<lbrakk>get (Current x1a (List.length x1a) x3 x4) = (x1, x2); small' = Reverse1 x2 smalla auxS; Stack.size x3 \<le> x4; Stack.size x3 \<le> Stack.size smalla + List.length auxS; Stack.toList x3 = rev (take (Stack.size x3 - List.length (Stack.toList smalla)) auxS) @ rev (take (Stack.size x3) (rev (Stack.toList smalla))); x1a \<noteq> []\<rbrakk> \<Longrightarrow> Current.toList x2 = tl x1a @ rev (take (Stack.size x3 - List.length (Stack.toList smalla)) auxS) @ rev (take (Stack.size x3) (rev (Stack.toList smalla)))\<close> diff_add_inverse get_toList_size less_imp_add_positive list.sel(3) list.size(3) tl_append2)
  apply (metis Current.toList.simps Pair_inject get.simps(2) list.exhaust_sel)
  by (metis Current.isEmpty.simps Current.toList.simps add_eq_0_iff_both_eq_0 get_toList list.sel(3) neq0_conv size_isNotEmpty)

lemma currentList_empty: "\<lbrakk>\<not> isEmpty small; toCurrentList small = []; invariant small\<rbrakk> \<Longrightarrow> False"
  apply(induction small)
  apply (metis Small.isEmpty.simps(2) Small.toCurrentList.simps(3) get_toList list.distinct(1) surj_pair)
  apply (metis Small.isEmpty.simps(3) Small.toCurrentList.simps(2) get_toList list.distinct(1) surj_pair)
  using currentList_empty by auto

lemma currentList_empty_2: "\<lbrakk>0 < size small; toCurrentList small = []; invariant small\<rbrakk> \<Longrightarrow> False"
  apply(induction small)
    apply(auto  split: current.splits)
   apply (simp add: size_listLength)
  using currentList_empty_2 by blast

lemma tick_size: "invariant small \<Longrightarrow> size small = size (tick small)"
  apply(induction small rule: tick.induct)
  by(auto simp: tick_size split: current.splits)

lemma tick_not_empty: "invariant small \<Longrightarrow> \<not>isEmpty small \<Longrightarrow> \<not>isEmpty (tick small)"
  apply(induction small rule: tick.induct)
  apply(auto simp: tick_not_empty split: current.splits)
  using toList_isNotEmpty apply blast
  using Stack.isEmpty.elims(2) by blast
  
lemma push_not_empty: "\<lbrakk>\<not> isEmpty small; isEmpty (push x small)\<rbrakk> \<Longrightarrow> False"
  apply(induction x small rule: push.induct)
  apply(auto simp: push_not_empty put_isNotEmpty)
  apply (meson Common_Proof.push_not_empty)
  by (meson put_isNotEmpty)+

lemma size_isEmpty: "invariant small \<Longrightarrow> size small = 0 \<Longrightarrow> isEmpty small"
  apply(induction small)
  by(auto simp: size_isEmpty Current_Proof.size_isEmpty toList_isEmpty split: current.splits)

end