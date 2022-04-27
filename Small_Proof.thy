theory Small_Proof 
  imports Common_Proof Small
begin

lemma step_list_current: "invar small \<Longrightarrow> list_current (step small) = list_current small"
  apply(induction small rule: step.induct)
  by(auto simp: step_list_current split: current.splits)

lemma step_list_common: "small = Common common \<Longrightarrow> invar small \<Longrightarrow> list (step small) = list small"
  by(auto simp: step_list)

(* TODO: *)
lemma step_list_reverse2: "small = (Reverse2 current aux big new count) \<Longrightarrow> invar small
  \<Longrightarrow> list (step small) = list small"
  apply(auto simp: reverseN_take split: current.splits)
  using list_empty apply blast
  using Stack_Proof.size_empty apply blast
  using Stack_Proof.size_not_empty apply blast
  using Stack_Proof.size_empty list_empty apply force
  apply (metis add_diff_cancel_left' first_pop pop_list_length rev.simps(2) Stack_Proof.size_list_length)
  by (metis add_diff_cancel_left' first_pop pop_list_length rev.simps(2) Stack_Proof.size_list_length)

(* TODO: *)
lemma invar_step: "invar small \<Longrightarrow> invar (step small)" 
proof(induction small rule: step.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invar_step)
next
  case (2 current small aux)
  then show ?case
  proof(induction "Stack.list small")
    case Nil
    then show ?case
      using Stack_Proof.list_not_empty by fastforce
  next
    case (Cons a x)
    then show ?case 
    proof(induction current)
      case (Current extra added old remained)
      then have not_empty: "\<not> is_empty small"
        apply auto
        by (metis list.distinct(1) list_empty)


      from Current have a: "rev aux @ Stack.list small =
         rev (take (List.length aux + List.length (Stack.list small) - (List.length (Stack.list small) - Suc 0)) (Stack.first small # aux)) @
         tl (Stack.list small)"
        apply(auto simp: not_empty split: if_splits)
        by (smt (verit, ccfv_threshold) Nat.add_diff_assoc One_nat_def append_Cons append_eq_append_conv2 diff_add_inverse diff_le_self first_pop length_tl list.sel(3) list.size(4) nat_le_linear rev.simps(2) self_append_conv2 take_all list_empty)

      have b: "\<lbrakk>
      x = Stack.list small \<Longrightarrow>
     size old \<le> Suc (size (Stack.pop small) + List.length aux) \<and>
     rev (take (size old - List.length (Stack.list small)) aux) @ Stack.list small =
     rev (take (size old - List.length (Stack.list (Stack.pop small))) (Stack.first small # aux)) @
     rev (take (size old) (rev (Stack.list (Stack.pop small))));

     a # x = Stack.list small; 
     added = List.length extra; 
     size old \<le> remained; 
     size old \<le> size small + List.length aux;
     Stack.list old = rev (take (size old - List.length (Stack.list small)) aux) @ Stack.list small;
     \<not> List.length aux \<le> size old - List.length (Stack.list small); 
     aux \<noteq> []; 
      List.length (Stack.list small) \<le> size old
    \<rbrakk>  \<Longrightarrow>  rev (take (size old - (List.length (Stack.list small) - Suc 0)) (Stack.first small # aux)) = 
            rev (take (size old - List.length (Stack.list small)) aux) @ [Stack.first small]"
        by (metis One_nat_def Suc_diff_eq_diff_pred Suc_diff_le length_greater_0_conv list.distinct(1) rev.simps(2) take_Suc_Cons)

       
    from Current have "
     rev (take (List.length (Stack.list old) - List.length (Stack.list small)) aux) @
     rev (take (List.length (Stack.list old)) (rev (Stack.list small))) =
         rev (take (List.length (Stack.list old) - (List.length (Stack.list small) - Suc 0)) (Stack.first small # aux)) @
         rev (take (List.length (Stack.list old)) (rev (tl (Stack.list small))))"
      apply(auto simp: min_def)
      apply (smt (verit, ccfv_threshold) One_nat_def Stack_Proof.pop_list Suc_diff_eq_diff_pred Suc_diff_le append_Cons append_eq_append_conv2 append_self_conv diff_is_0_eq first_pop length_greater_0_conv length_tl list.size(3) rev_is_Nil_conv rev_singleton_conv Stack_Proof.size_list_length take_all take_eq_Nil tl_Nil list_empty)
      apply (metis Stack_Proof.pop_list append.right_neutral diff_is_0_eq' length_rev list.sel(3) not_empty not_less_eq_eq pop_list_length rev.simps(2) take_Cons' take_append)
      subgoal by(auto simp: a)
      subgoal 
        apply(auto simp: b not_empty) 
        by (metis Stack_Proof.pop_list first_pop not_empty)
      by (metis add.right_neutral add_Suc_right append.right_neutral diff_is_0_eq' length_rev list.sel(3) list.size(4) not_less_eq_eq rev.simps(2) take0 take_append)

    with Current show ?case 
      by(auto simp: Stack_Proof.pop_list Stack_Proof.size_list_length)
  qed
  qed
  next
    case (3 current auxS big newS count)
    then show ?case
      apply(auto simp: split: current.splits) 
            apply (metis length_0_conv Stack_Proof.list_not_empty Stack_Proof.size_list_length)
      using Stack_Proof.size_not_empty apply blast
          apply (meson add_decreasing le_less_linear Stack_Proof.size_not_empty)
      using Stack_Proof.size_not_empty apply blast
        apply(auto simp: reverseN_take)
        apply (metis Nat.add_0_right add.commute Stack_Proof.list_not_empty le_refl list.size(3) Stack_Proof.size_list_length take_all)
       apply (simp add: Stack_Proof.size_pop)
      by (metis first_pop length_Cons Stack_Proof.size_list_length)
qed

lemma invar_push: "invar small \<Longrightarrow> invar (push x small)"
  apply(induction x small rule: push.induct)
  by(auto simp: invar_push split: current.splits)

(* TODO: *)
lemma invar_pop_2_helper: "\<lbrakk>
  0 < size old; 
  size old \<le> size small + List.length auxS;
  Stack.list old = 
    rev (take (size old - List.length (Stack.list small)) auxS) @ 
    rev (take (size old) (rev (Stack.list small)))
\<rbrakk> \<Longrightarrow> Stack.list (Stack.pop old) =
        rev (take (size (Stack.pop old) - List.length (Stack.list small)) auxS) @
        rev (take (size (Stack.pop old)) (rev (Stack.list small)))"
proof(induction "size old \<le> size small")
  case True
  then show ?case 
    apply auto
    by (smt (z3) Stack_Proof.pop_list Stack_Proof.size_pop Suc_diff_le Suc_pred diff_Suc_Suc diff_is_0_eq' drop_Suc length_rev nat_le_linear Stack_Proof.size_not_empty not_less_eq_eq rev.simps(1) rev_take self_append_conv2 Stack_Proof.size_list_length take_eq_Nil tl_drop)
next
  case False
  then show ?case
    apply auto
    by (smt (verit) False(2) Stack_Proof.pop_list Stack_Proof.size_pop Suc_diff_le Suc_pred diff_Suc_Suc diff_diff_left diff_is_0_eq drop_Suc le_add_diff_inverse length_0_conv length_rev less_Suc_eq_le less_imp_diff_less Stack_Proof.size_not_empty not_less_eq_eq rev_take Stack_Proof.size_list_length take_eq_Nil tl_append2 tl_drop)
qed

lemma invar_pop_2: "\<lbrakk>
  0 < size small; 
  invar small;
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> invar small'"
proof(induction small arbitrary: x rule: pop.induct)
case (1 state)
  then show ?case by(auto simp: invar_pop split: prod.splits)
next
  case (2 current small auxS)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      apply(auto)
      apply (simp add: Stack_Proof.size_pop Stack_Proof.size_not_empty)
      apply (simp add: Stack_Proof.size_pop Stack_Proof.size_not_empty)
      by (simp add: invar_pop_2_helper)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case (3 current auxS big newS count)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      apply auto 
      apply (auto simp: Stack_Proof.size_pop Stack_Proof.size_not_empty Suc_leI)
      by (smt (verit, best) Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc first_pop list.sel(3) rev_take Stack_Proof.size_not_empty tl_drop)+
  next
    case (2 x xs added old remained)
    then show ?case by auto 
  qed
qed

lemma push_list_common: "small = Common common \<Longrightarrow> list (push x small) = x # list small"
  by(auto simp: Common_Proof.push_list)

lemma push_list_reverse2: "small = (Reverse2 current auxS big newS count)
  \<Longrightarrow> list (push x small) = x # list small"
proof(induction x current rule: Current.push.induct)
  case (1 x extra added old remained)
  then show ?case by auto
qed

(* TODO: *)
lemma pop_list_reverse2: "\<lbrakk>
  small = (Reverse2 current auxS big newS count);
  \<not>is_empty small; 
  invar small; 
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> x # list small' = list small"
proof(induction current arbitrary: x rule: Current.pop.induct)
  case (1 added old remained)
  then show ?case 
    apply(auto simp: reverseN_take)
    by (smt (z3) Stack_Proof.pop_list Suc_diff_le Suc_pred diff_Suc_Suc drop_Suc first_pop rev_take Stack_Proof.size_not_empty tl_drop)+
next
  case (2 x xs added old remained)
  then show ?case by auto
qed

lemma push_list_current: "list_current (push x small) = x # list_current small"
  apply(induction x small rule: push.induct)
  by(auto simp: push_list_current Current_Proof.push_list)

lemma pop_list_current: "invar small \<Longrightarrow> 0 < size small \<Longrightarrow> pop small = (x, small')
  \<Longrightarrow> x # list_current small' = list_current small"
proof(induction small arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case by(auto simp: pop_list_current split: prod.splits)
next
  case (2 current small auxS)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      apply auto
      by (simp add: first_pop Stack_Proof.size_not_empty)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
next
  case (3 current auxS big newS count)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      by(auto simp: first_pop Stack_Proof.size_not_empty)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma list_current_size: "\<lbrakk>0 < size small; list_current small = []; invar small\<rbrakk> \<Longrightarrow> False"
  apply(induction small)
  apply(auto  split: current.splits)
  apply (simp add: Stack_Proof.size_list_length)
  using list_current_size by blast

lemma step_size: "invar small \<Longrightarrow> size small = size (step small)"
  apply(induction small rule: step.induct)
  by(auto simp: step_size split: current.splits)

lemma size_empty: "invar (small :: 'a state) \<Longrightarrow> size small = 0 \<Longrightarrow> is_empty small"
  apply(induction small)
  by(auto simp: size_empty Current_Proof.size_empty list_empty split: current.splits)

lemma size_push: "invar small \<Longrightarrow> Suc (size small) = size (push x small)"
proof(induction x small rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: size_push)
next
  case (2 x current small auxS)
  then show ?case 
    by(auto simp: size_push split: current.splits)
next
  case (3 x current auxS big newS count)
  then show ?case 
    by(auto simp: size_push split: current.splits)
qed

lemma size_new_push: "invar small \<Longrightarrow> Suc (size_new small) = size_new (push x small)"
proof(induction x small rule: push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: size_new_push)
next
  case (2 x current small auxS)
  then show ?case 
    by(auto simp: size_push split: current.splits)
next
  case (3 x current auxS big newS count)
  then show ?case 
    by(auto simp: size_push split: current.splits)
qed

lemma size_pop: "\<lbrakk>invar small; 0 < size small; pop small = (x, small')\<rbrakk>
   \<Longrightarrow> Suc (size small') = size small"
proof(induction small rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: size_pop split: prod.splits)
next
  case (2 current small auxS)
  then show ?case
    using Current_Proof.size_pop[of current] apply(induction current rule: Current.pop.induct)
    by auto
next
  case (3 current auxS big newS count)
  then show ?case 
    using Current_Proof.size_pop[of current] apply(induction current rule: Current.pop.induct)
    by auto
qed

lemma size_new_pop: "\<lbrakk>invar small; 0 < size_new small; pop small = (x, small')\<rbrakk>
   \<Longrightarrow> Suc (size_new small') = size_new small"
proof(induction small rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: size_new_pop split: prod.splits)
next
  case (2 current small auxS)
  then show ?case 
  by(induction current rule: Current.pop.induct) auto
next
  case (3 current auxS big newS count)
  then show ?case 
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_size_new: "\<lbrakk>invar small; 0 < size small\<rbrakk> \<Longrightarrow> 0 < size_new small"
  by(induction small)(auto simp: size_size_new)

end