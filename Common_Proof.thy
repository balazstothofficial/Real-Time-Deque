theory Common_Proof
  imports Common Idle_Proof Current_Proof ReverseN_Proof
begin

lemma step_list: "invar common \<Longrightarrow> list (step common) = list common"
proof(induction common rule: step.induct)
  case (1 idle)
  then show ?case by auto
next
  case (2 current aux new moved)

  then show ?case 
  proof(induction current)
    case (Current extra added old remained)
    
    then have aux_not_empty: "aux \<noteq> []"
        by auto

    from Current show ?case 
    proof(induction "remained \<le> Suc moved")
      case True
     
      then have "remained - length new = 1"
        by auto

      with True aux_not_empty show ?case 
        by(auto simp: reverseN_take take_hd)
    next
      case False
      then show ?case 
        by(auto simp: aux_not_empty reverseN_step Suc_diff_Suc)
    qed
  qed
qed

lemma step_list_current: "invar common \<Longrightarrow> list_current (step common) = list_current common"
  apply(induction common)
  by(auto split: current.splits)

lemma push_list: "list (push x common) = x # list common"
proof(induction x common rule: push.induct)
  case (1 x stack stackSize)
  then show ?case 
    by(auto simp: Stack_Proof.push_list)
next
  case (2 x current aux new moved)
  then show ?case 
    apply(induction x current rule: Current.push.induct)
    by auto
qed

lemma invar_step: "invar common \<Longrightarrow> invar (step common)" 
proof(induction "common" rule: invar.induct)
  case (1 idle)
  then show ?case
    by auto
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current)
    case (Current extra added old remained)
    then show ?case
    proof(induction "aux = []")
      case True
      then show ?case by auto 
    next
      case False
      then show ?case
      proof(induction "remained \<le> Suc (length new)")
        case True
        then have "take (Suc (length new)) (Stack.list old) = take (Stack.size old) (hd aux # new)"
          apply(induction "(remained - length new)" aux new rule: reverseN.induct)
          by(auto simp: le_Suc_eq)
         
        with True show ?case 
          by auto
      next
        case False
        then show ?case 
          by(auto simp: reverseN_step Suc_diff_Suc)
      qed
    qed
  qed
qed

lemma invar_push: "invar common \<Longrightarrow> invar (push x common)"
proof(induction x common rule: push.induct)
  case (1 x current stack stackSize)
  then show ?case
  proof(induction x current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case
    proof(induction x stack rule: Stack.push.induct)
      case (1 x left right)
      then show ?case by auto
    qed
  qed
next
  case (2 x current aux new moved)
  then show ?case
  proof(induction x current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case by auto
  qed
qed


lemma invar_pop: "\<lbrakk>
  0 < size common; 
  invar common;
  pop common = (x, common')
\<rbrakk> \<Longrightarrow> invar common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then obtain idle' where idle: "Idle.pop idle = (x, idle')"
    by(auto split: prod.splits)

  obtain current' where current: "drop_first current = current'"
    by auto

  from 1 idle have prop_1: "Idle.invar idle'"
    by(auto simp: size_not_empty Idle_Proof.invar_pop)

  from 1 current have prop_2: "Current.invar current'"
    by(auto simp: invar_size_pop eq_snd_iff split: prod.splits)

  from 1 current idle have prop_3: "Current.size_new current' = Idle.size idle'"
    using Idle_Proof.size_pop[of idle x idle'] size_new_pop[of current]
    by(auto simp: size_not_empty)

  from 1 current idle have prop_4: "take (Idle.size idle') (Current.list current') = 
      take (Current.size current') (Idle.list idle')"
    using Idle_Proof.size_pop[of idle x idle'] 
          size_not_empty[of idle] 
          size_pop[of current] 
          drop_first_list_size[of current]
          pop_list_2[of idle x idle'] cons_tl[of x "Idle.list idle'"]
    by(auto simp: take_tl split: prod.splits)

  from 1 prop_1 prop_2 prop_3 prop_4 current idle show ?case 
    by auto
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case
    proof(induction "remained - Suc 0 \<le> length new")
      case True
      
      then have "length new = remained - Suc 0" by auto

      with True show ?case 
        using Stack_Proof.pop_list[of old] 
              Stack_Proof.size_not_empty[of old] 
              Stack_Proof.size_pop[of old]
        by(auto simp: reverseN_take rev_take take_tl tl_drop) 
    next
      case False
      then have "remained - Suc 0 \<le> length aux + length new" by auto

      with False show ?case 
        using Stack_Proof.pop_list[of old] 
              Stack_Proof.size_not_empty[of old] 
              Stack_Proof.size_pop[of old]
        by(auto simp: reverseN_tl Suc_diff_Suc take_tl)
    qed
   next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma push_list_current: "list_current (push x left) = x # list_current left"
  apply(induction x left rule: push.induct)
  by(auto simp: Current_Proof.push_list)

lemma take_1: "0 < x \<and> 0 < y \<Longrightarrow> take x xs = take y ys \<Longrightarrow> take 1 xs = take 1 ys"
  by (metis One_nat_def bot_nat_0.not_eq_extremum hd_take take_Suc take_eq_Nil)

lemma pop_list: "invar common \<Longrightarrow> 0 < size common \<Longrightarrow> pop common = (x, common') \<Longrightarrow>
   list common = x # list common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case
    by(auto simp: Idle_Proof.pop_list_2 split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case
    proof(induction "remained - Suc 0 \<le> length new")
      case True

      then have hd: "Stack.first old = hd aux"
        apply(auto simp: reverseN_take)
        by (smt (z3) Suc_diff_Suc diff_add_inverse diff_commute diff_is_0_eq first_list hd_append2 hd_conv_nth hd_drop_conv_nth hd_take le_add1 le_add_diff_inverse2 length_greater_0_conv length_rev lessI less_add_same_cancel2 less_le_trans less_or_eq_imp_le Stack_Proof.list_not_empty rev_nth rev_take Stack_Proof.size_list_length take_eq_Nil)

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

        then have aux_not_empty: "aux \<noteq> []"
          by auto

        from True have old_not_empty: "\<not>Stack.is_empty old"
          apply auto
          using Stack_Proof.size_not_empty by blast
        
        from True have "take 1 (Stack.list old) = take 1 (rev aux)"
          apply(auto simp: reverseN_take)
          by (smt (z3) add_gr_0 hd_append2 hd_take le_add_diff_inverse2 length_greater_0_conv length_rev less_imp_le_nat list_not_empty Stack_Proof.size_list_length take_eq_Nil take_hd zero_less_diff)

        then have "[last aux] = [Stack.first old]"
          using take_last first_take aux_not_empty old_not_empty
          by fastforce

        then have "last aux = Stack.first old"
          by auto

        with True show ?case 
          apply(auto simp: reverseN_take min_def split: if_splits)
          by (metis Suc_eq_plus1 butlast_conv_take diff_diff_left diff_less_mono2 less_nat_zero_code list.size(3) snoc_eq_iff_butlast)+
      next
        case False

        then have a: "take (remained - length new) aux \<noteq> []"
          by auto

        from False have b: "\<not>Stack.is_empty old"
          apply auto
          using Stack_Proof.size_not_empty by blast

     


        from False have "take 1 (Stack.list old) = take 1 (rev (take (remained - length new) aux))"
          apply(auto simp: reverseN_take)
          apply(induction "0 < Stack.size old \<and> 0 < remained")
          using take_1[of 
                remained 
                "Stack.size old" 
                "Stack.list old" 
                "(rev (take (remained - length new) aux)) @ take (Stack.size old + length new - remained) new"
              ]
          by auto
          
        then have c: "[Stack.first old] = [last (take (remained - length new) aux)]"
          using take_last first_take a b
          by metis

        with False show ?case 
          apply(auto simp: reverseN_take min_def split: if_splits)
          by (smt (z3) Nil_is_rev_conv Suc_diff_Suc first_list hd_append2 hd_rev hd_take last_snoc le_Suc_eq length_greater_0_conv less_imp_Suc_add list_not_empty not_le Stack_Proof.size_list_length take_eq_Nil take_hd_drop zero_less_Suc)+
      qed
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed


(* TODO: *)
lemma pop_list_current: "invar common \<Longrightarrow> 0 < size common \<Longrightarrow> pop common = (x, common')
   \<Longrightarrow> x # list_current common' = list_current common"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case 
  proof(induction idle rule: Idle.pop.induct)
    case (1 stack stackSize)
    then show ?case
    proof(induction current rule: Current.pop.induct)
      case (1 added old remained)
      then show ?case apply auto
        by (metis first_pop hd_take list.sel(1) Stack_Proof.size_not_empty)
    next
      case (2 x' xs added old remained)
      then show ?case apply auto
        by (metis Stack_Proof.size_empty first_pop hd_take list.sel(1) old.nat.distinct(2) zero_less_Suc)
    qed
  qed
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case apply(auto split: if_splits)
      using first_pop Stack_Proof.size_not_empty by blast+
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed
  
lemma list_current_size: "\<lbrakk>0 < size common; list_current common = []; invar common\<rbrakk> \<Longrightarrow> False"
proof(induction common rule: invar.induct)
  case (1 current idle)
  then show ?case
    using list_size by auto
next
  case (2 current aux new moved)
  then have "Current.invar current" 
            "Current.list current = []"  
            "0 < Current.size current" 
    by(auto split: current.splits)
 
  then show ?case using list_size by auto
qed

lemma list_size: "\<lbrakk>0 < size common; list common = []; invar common\<rbrakk> \<Longrightarrow> False"
proof(induction common rule: invar.induct)
  case (1 current idle)
  then show ?case
    using list_size by auto
next
  case (2 current aux new moved)
  then have "Current.invar current" 
            "Current.list current = []"  
            "0 < Current.size current" 
    by(auto split: current.splits)
 
  then show ?case using list_size by auto
qed

lemma size_empty: "invar common \<Longrightarrow> size common = 0 \<Longrightarrow> is_empty common"
proof(induction common rule: is_empty.induct)
  case (1 current idle)
  then show ?case 
    by(auto simp: min_def size_empty size_new_empty split: if_splits)
next
  case (2 current)
  then have "Current.invar current" 
    by(auto split: current.splits)

  with 2 show ?case 
    by(auto simp: min_def size_empty size_new_empty split: if_splits)
qed
  
lemma step_size: "invar x \<Longrightarrow> size x = size (step x)"
proof(induction x rule: step.induct)
  case (1 current idle)
  then show ?case by auto
next
  case (2 current aux new moved)
  then show ?case 
    by(auto simp: min_def split: current.splits)
qed

lemma step_size_new: "invar x \<Longrightarrow> size_new x = size_new (step x)"
proof(induction x rule: step.induct)
  case (1 current idle)
  then show ?case by auto
next
  case (2 current aux new moved)
  then show ?case by(auto split: current.splits)
qed

lemma remaining_steps_step: "\<lbrakk>invar common; remaining_steps common > 0\<rbrakk>
   \<Longrightarrow> remaining_steps common = Suc (remaining_steps (step common))"
  apply(induction common)
  by(auto split: current.splits)

lemma remaining_steps_step_0: "\<lbrakk>invar common; remaining_steps common = 0\<rbrakk>
   \<Longrightarrow> remaining_steps (step common) = 0"
  apply(induction common)
  by(auto split: current.splits)

lemma remaining_steps_push: "invar common \<Longrightarrow> 
  remaining_steps common = remaining_steps (push x common)"
proof(induction x common rule: Common.push.induct)
  case (1 x current stack stackSize)
  then show ?case by auto
next
  case (2 x current aux new moved)
  then show ?case by(auto split: current.splits)
qed

lemma remaining_steps_pop: "\<lbrakk>invar common; 0 < size common; pop common = (x, common')\<rbrakk> 
  \<Longrightarrow> remaining_steps common' \<le> remaining_steps common"
proof(induction common rule: pop.induct)
  case (1 current idle)
  then show ?case 
  proof(induction idle rule: Idle.pop.induct)
    case (1 stack stackSize)
    then show ?case  
    proof(induction current rule: Current.pop.induct)
      case (1 added old remained)
      then show ?case by auto
    next
      case (2 x xs added old remained)
      then show ?case by auto
    qed
  qed
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma size_push: "invar common \<Longrightarrow> Suc (size common) = size (push x common)"
proof(induction x common rule: push.induct)
  case (1 x current stack stackSize)
  then show ?case 
    by(auto simp: min_def size_push Stack_Proof.size_push)
next
  case (2 x current aux new moved)
  then show ?case 
    by(auto simp: size_push split: current.splits)
qed

lemma size_new_push: "invar common \<Longrightarrow> Suc (size_new common) = size_new (push x common)"
proof(induction x common rule: Common.push.induct)
  case (1 x current stack stackSize)
  then show ?case 
    by(auto simp: min_def size_push size_new_push)
next
  case (2 x current aux new moved)
  then show ?case 
    by(auto split: current.splits)
qed

lemma size_pop: "\<lbrakk>invar common; 0 < size common; pop common = (x, common')\<rbrakk>
   \<Longrightarrow> Suc (size common') = size common"
proof(induction common rule: Common.pop.induct)
  case (1 current idle)
  then show ?case 
    using size_pop[of current] Idle_Proof.size_pop[of idle] size_not_empty[of idle]
    by(auto split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case 
    using size_pop[of current] apply(induction current rule: Current.pop.induct)
    by auto
qed

lemma size_new_pop: "\<lbrakk>invar common; 0 < size_new common; pop common = (x, common')\<rbrakk>
   \<Longrightarrow>  Suc (size_new common') = size_new common"
proof(induction common rule: Common.pop.induct)
  case (1 current idle)
  then show ?case
    using size_new_pop[of current]
    by(auto split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma size_size_new: "\<lbrakk>invar common; 0 < size common\<rbrakk> \<Longrightarrow> 0 < size_new common"
  by(induction common) auto

end