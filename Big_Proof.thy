theory Big_Proof
  imports Big Common_Proof
begin

(* TODO: *)
lemma tick_toList: "invariant big \<Longrightarrow> toList (tick big) = toList big"
  apply(induction big rule: tick.induct)
    apply(auto simp: tick_toList split: current.splits)
  by (metis Suc_neq_Zero bot_nat_0.extremum_uniqueI toList_isEmpty first_pop list.size(3) reverseN.simps(3) Stack_Proof.size_listLength)

lemma tick_toCurrentList: "invariant big \<Longrightarrow> toCurrentList (tick big) = toCurrentList big"
  apply(induction big rule: tick.induct)
  by(auto simp: tick_toCurrentList split: current.splits)

lemma push: "toList (push x big) = x # toList big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: push_toList)
next
  case (2 x current big aux count)
  then show ?case
    apply(induction x current rule: put.induct)
    by auto
qed

(* TODO: *)
lemma helper_size: "0 < Big.size (Reverse current big aux count) \<Longrightarrow> invariant (Reverse current big aux count) \<Longrightarrow> 
    top current = hd (Big.toList (Reverse current big aux count))"
proof(induction current rule: get.induct)
  case (1 added old remained)
  then show ?case 
    apply(auto simp: reverseN_take rev_take)
    by (smt (z3) Nat.diff_diff_right add.commute diff_is_0_eq drop_all_iff first_toList hd_append hd_take le_add_diff length_rev minus_nat.diff_0 nat_le_linear Stack_Proof.size_isNotEmpty take_eq_Nil)
   
next
  case (2 x xs added old remained)
  then show ?case by auto
qed

lemma helper_2_size: "0 < Big.size (Reverse current big aux count) \<Longrightarrow> invariant (Reverse current big aux count) \<Longrightarrow> 
    Big.toList (Reverse (bottom current) big aux count) = tl (Big.toList (Reverse current big aux count))"
proof(induction current rule: get.induct)
  case (1 added old remained)
  then have "
         drop (Suc (length (Stack.toList big) + length aux) - (length (Stack.toList big) - count + remained)) (rev aux) =
         tl (drop (length (Stack.toList big) + length aux - (length (Stack.toList big) - count + remained)) (rev aux))"
    apply(auto simp: reverseN_drop)
    by (smt (verit, del_insts) Nat.add_diff_assoc Nat.diff_diff_right add.commute diff_diff_cancel diff_le_self drop_Suc le_diff_conv plus_1_eq_Suc Stack_Proof.size_listLength tl_drop)

  with 1  show ?case 
    apply(auto simp: reverseN_take rev_take tl_drop  Stack_Proof.size_listLength)
    by (smt (verit, best) Nat.add_diff_assoc One_nat_def add.commute append_self_conv2 diff_add_inverse2 diff_is_0_eq' drop_Suc drop_all le_add2 le_diff_conv length_drop length_rev list.size(3) not_less_eq_eq plus_1_eq_Suc tl_append2 tl_drop)
next
  case (2 x xs added old remained)
  then show ?case by auto
qed

lemma helper_3_size: "0 < Big.size big \<Longrightarrow> invariant big \<Longrightarrow> toList big \<noteq> []"
  apply(induction big)
   apply(auto simp: toList_size split: current.splits)
   apply (simp add: reverseN_take)
  apply (metis bot_nat_0.extremum_uniqueI diff_zero leD list.size(3) Stack_Proof.size_listLength)
  using toList_size by blast

(* TODO: *)
lemma pop_size: "0 < size big \<Longrightarrow> invariant big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> x # toList big' = toList big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case
    by(auto simp: toList_pop split: prod.splits)
next
  case (2 x current big aux count)
  
  
  from 2 show ?case 
    using helper_size[of current big aux count] helper_2_size[of current big aux count] helper_3_size 
    by(auto simp: helper_3_size split: current.splits)
qed 

(* TODO: *)
lemma pop_2_size: "0 < size big \<Longrightarrow> invariant big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> toList big' = tl (toList big)"
  using pop_size cons_tl[of x "toList big'" "toList big"] 
  by force

(* TODO: *)
lemma invariant_tick: "invariant big \<Longrightarrow> invariant (tick big)" 
proof(induction big rule: tick.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invariant_tick)
next
  case (2 current uu aux)
  then show ?case
    apply(auto simp: reverseN_take split: current.splits)
    by (metis length_rev length_take min.absorb2 Stack_Proof.size_listLength take_append take_take)
next
  case (3 current big aux count)
  then have a: "rev (Stack.toList big) @ aux = rev (Stack.toList (Stack.pop big)) @ first big # aux"
    apply(auto split: current.splits)
    by (metis Zero_not_Suc bot_nat_0.extremum_uniqueI first_pop list.size(3) rev.simps(2) Stack_Proof.size_listLength Stack_Proof.toList_isNotEmpty)

  from 3 have b: "reverseN (Suc count) (Stack.toList big) aux = reverseN count (Stack.toList (Stack.pop big)) (first big # aux)"
    apply(auto simp: reverseN_take split: current.splits)
    by (metis Stack_Proof.size_isEmpty Zero_not_Suc bot_nat_0.extremum_uniqueI first_pop rev.simps(2) take_Suc_Cons)

  from 3 a b show ?case
    apply(auto split: current.splits)
    by (metis Suc_le_lessD length_append_singleton length_rev less_Suc_eq_le Stack_Proof.size_listLength)
qed

lemma invariant_push: "invariant big \<Longrightarrow> invariant (push x big)"
  apply(induction x big rule: push.induct)
  by(auto simp: invariant_push split: current.splits)

lemma invariant_pop_2: "\<lbrakk>
  0 < size big; 
  invariant big;
  pop big = (x, big')
\<rbrakk> \<Longrightarrow> invariant big'"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: invariant_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    have a: "Stack.toList (Stack.pop old) = tl (Stack.toList old)"
      apply(induction old rule: Stack.pop.induct)
      by auto


    from 1 have b: "
     tl (rev (take (Stack.size old - length (Stack.toList big)) aux) @ rev (take (Stack.size old) (rev (Stack.toList big)))) =
         rev (take (Stack.size (Stack.pop old) - length (Stack.toList big)) aux) @ rev (take (Stack.size (Stack.pop old)) (rev (Stack.toList big)))"
    proof(induction "Stack.size old < length (Stack.toList big)")
      case True
      then show ?case 
        apply(auto simp: reverseN_take)
        by (smt (z3) One_nat_def Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_diff_eq_diff_pred Suc_diff_le bot_nat_0.not_eq_extremum diff_is_0_eq drop_Suc length_rev less_imp_le nat_le_linear not_less_eq_eq rev_is_Nil_conv rev_take self_append_conv2 take_eq_Nil tl_drop)
    next
      case False
     
        

      from False show ?case
      proof(induction "Stack.size (Stack.pop old) < length (Stack.toList big)")
        case True
        then show ?case
          apply auto
          by (smt (verit, best) Cons_nth_drop_Suc One_nat_def Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_le_eq a add.commute add_leE diff_add_inverse2 first_pop gen_length_def le_add_diff_inverse2 le_eq_less_or_eq length_code length_rev list.inject not_le_imp_less plus_1_eq_Suc rev_is_Nil_conv rev_rev_ident rev_take self_append_conv2 take_all_iff take_eq_Nil)
      next
        case False
        then show ?case apply auto
          by (smt (z3) Stack_Proof.size_isEmpty Stack_Proof.size_pop Suc_diff_le Suc_le_lessD Suc_pred bot_nat_0.not_eq_extremum diff_Suc_Suc diff_add_inverse2 diff_is_0_eq drop_Suc length_append length_rev list.size(3) nat_le_linear not_le_imp_less rev_take Stack_Proof.size_listLength take_all_iff tl_append2 tl_drop)
      qed
    qed
             
    from 1 show ?case  
      apply auto
         apply linarith+
      subgoal 
        by(auto simp: a b reverseN_take)
      apply(auto simp: a reverseN_take  take_tl)
      apply(auto simp: rev_take)
      proof(induction "drop (length aux - (remained - min (length (Stack.toList big)) count)) (rev aux) = []")
        case True
        then show ?case apply auto 
          by (smt (z3) Suc_diff_le diff_diff_cancel diff_diff_left diff_is_0_eq diff_le_self drop_Suc min.commute min_def Stack_Proof.size_listLength tl_drop)
      next
        case False
        then show ?case apply auto
          by (metis Suc_diff_le drop_Suc le_diff_conv min.commute min_def Stack_Proof.size_listLength tl_drop)
      qed
  next
    case (2 x xs added old remained)
    then show ?case
      by auto
  qed
qed

lemma push_toCurrentList: "toCurrentList (push x big) = x # toCurrentList big"
  apply(induction x big rule: push.induct)
  by(auto simp: push_toCurrentList put_toList)

lemma pop_toCurrentList: "invariant big \<Longrightarrow> 0 < size big \<Longrightarrow> pop big = (x, big') \<Longrightarrow> x # toCurrentList big' = toCurrentList big"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: pop_toCurrentList split: prod.splits)
next
  case (2 current big aux count)
  
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
      apply auto
      by (metis first_pop Stack_Proof.size_isNotEmpty)
  next
    case (2 x xs added old remained)
    then show ?case
      by auto
  qed
qed

(* TODO: *)
lemma toCurrentList_size: "\<lbrakk>0 < size big; toCurrentList big = []; invariant big\<rbrakk> \<Longrightarrow> False"
  apply(induction big)
    apply(auto  split: current.splits)
    apply (simp add: Stack_Proof.size_listLength)
  using toCurrentList_size by blast

lemma tick_size: "invariant big \<Longrightarrow> size big = size (tick big)"
  apply(induction big rule: tick.induct)
  by(auto simp: tick_size split: current.splits)

(* TODO: *)
lemma size_isEmpty: "invariant big \<Longrightarrow> size big = 0 \<Longrightarrow> isEmpty big"
  apply(induction big)
   apply(auto simp: size_isEmpty Current_Proof.size_isEmpty split: current.splits)
   apply (metis Stack_Proof.size_isEmpty add.commute add_diff_cancel_right' bot_nat_0.extremum min_def zero_diff)
  by (metis add_gr_0 length_greater_0_conv less_numeral_extra(3) min_less_iff_conj)

lemma remainingSteps_tick: "\<lbrakk>invariant big; remainingSteps big > 0\<rbrakk>
   \<Longrightarrow> remainingSteps big = Suc (remainingSteps (tick big))"
  apply(induction big rule: Big.tick.induct)
  by(auto simp: remainingSteps_tick split: current.splits)

lemma remainingSteps_tick_0: "\<lbrakk>invariant big; remainingSteps big = 0\<rbrakk> 
  \<Longrightarrow> remainingSteps (tick big) = 0"
  apply(induction big)
  by(auto simp: remainingSteps_tick_0 split: current.splits)

lemma remainingSteps_push: "invariant big \<Longrightarrow> remainingSteps big = remainingSteps (push x big)"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: remainingSteps_push)
next
  case (2 x current big aux count)
  then show ?case
  proof(induction current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case 
      by auto
  qed
qed

lemma remainingSteps_pop_big: "\<lbrakk>invariant big; 0 < size big; pop big = (x, big')\<rbrakk>
   \<Longrightarrow> remainingSteps big' \<le> remainingSteps big"
proof(induction big rule: Big.pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: remainingSteps_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma size_push: "invariant big \<Longrightarrow> Suc (size big) = size (Big.push x big)"
proof(induction x big rule: Big.push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: size_push)
next
  case (2 x current small auxS)
  then show ?case 
    by(auto simp: size_put split: current.splits)
qed

lemma newSize_push: "invariant big \<Longrightarrow> Suc (newSize big) = newSize (push x big)"
proof(induction x big rule: Big.push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: newSize_push)
next
  case (2 x current small auxS)
  then show ?case 
    by(auto simp: size_put split: current.splits)
qed

lemma size_pop: "\<lbrakk>invariant big; 0 < size big; pop big = (x, big')\<rbrakk>
   \<Longrightarrow> Suc (size big') = size big"
proof(induction big rule: Big.pop.induct)
  case (1 state)
  then show ?case by(auto simp: size_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case
    using size_get[of current] apply(induction current rule: get.induct)
    by auto
qed

lemma newSize_pop: "\<lbrakk>invariant big; 0 < newSize big; pop big = (x, big')\<rbrakk>
    \<Longrightarrow> Suc (newSize big') = newSize big"
proof(induction big rule: Big.pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: newSize_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case
    by(induction current rule: get.induct) auto
qed

lemma size_newSize: "\<lbrakk>invariant big; 0 < size big\<rbrakk> \<Longrightarrow> 0 < newSize big"
  by(induction big)(auto simp: size_newSize)

end
