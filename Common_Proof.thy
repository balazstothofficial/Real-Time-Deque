theory Common_Proof
  imports Common Idle_Proof Current_Proof ReverseN_Proof
begin

lemma tick_toList: "invariant common \<Longrightarrow> toList (tick common) = toList common"
proof(induction common rule: tick.induct)
  case (1 idle)
  then show ?case by auto
next
  case (2 current aux new moved)

  then show ?case 
  proof(induction current)
    case (Current extra added old remained)
    
    then have auxIsNotEmpty: "aux \<noteq> []"
        by auto

    from Current show ?case 
    proof(induction "remained \<le> Suc moved")
      case True
     
      then have "remained - length new = 1"
        by auto

      with True auxIsNotEmpty show ?case 
        by(auto simp: reverseN_take take_hd)
    next
      case False
      then show ?case 
        by(auto simp: auxIsNotEmpty reverseN_step Suc_diff_Suc)
    qed
  qed
qed

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
    proof(induction "aux = []")
      case True
      then show ?case by auto 
    next
      case False
      then show ?case
      proof(induction "remained \<le> Suc (length new)")
        case True
        then have "take (Suc (length new)) (Stack.toList old) = take (Stack.size old) (hd aux # new)"
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

lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
proof(induction x common rule: push.induct)
  case (1 x current stack stackSize)
  then show ?case
  proof(induction x current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case
    proof(induction element stack rule: Stack.push.induct)
      case (1 element left right)
      then show ?case by auto
    qed
  qed
next
  case (2 x current aux new moved)
  then show ?case
  proof(induction x current rule: put.induct)
    case (1 element extra added old remained)
    then show ?case by auto
  qed
qed


lemma invariant_pop: "\<lbrakk>
  0 < size common; 
  invariant common;
  pop common = (x, common')
\<rbrakk> \<Longrightarrow> invariant common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then obtain idle' where idle: "Idle.pop idle = (x, idle')"
    by(auto split: prod.splits)

  obtain current' where current: "bottom current = current'"
    by auto

  from 1 idle have firstProperty: "Idle.invariant idle'"
    by(auto simp: size_isNotEmpty invariant_pop)

  from 1 current have secondProperty: "Current.invariant current'"
    by(auto simp: invariant_size_get eq_snd_iff split: prod.splits)

  from 1 current idle have thirdProperty: "Current.newSize current' = Idle.size idle'"
    using size_pop[of idle x idle'] newSize_get[of current] 
    by(auto simp: size_isNotEmpty)

  from 1 current idle have fourthProperty: "take (Idle.size idle') (Current.toList current') = 
      take (Current.size current') (Idle.toList idle')"
    using size_pop[of idle x idle'] 
          size_isNotEmpty[of idle] 
          size_get[of current] 
          bottom_toList_size[of current]
          pop_toList_2[of idle x idle'] cons_tl[of x "Idle.toList idle'"]
    by(auto simp: take_tl split: prod.splits)

  from 1 firstProperty secondProperty thirdProperty fourthProperty current idle show ?case 
    by auto
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
    proof(induction "remained - Suc 0 \<le> length new")
      case True
      
      then have "length new = remained - Suc 0" by auto

      with True show ?case 
        using Stack_Proof.pop_toList[of old] 
              Stack_Proof.size_isNotEmpty[of old] 
              Stack_Proof.size_pop[of old]
        by(auto simp: reverseN_take rev_take min.absorb2 take_tl tl_drop) 
    next
      case False
      then have "remained - Suc 0 \<le> length aux + length new" by auto

      with False show ?case 
        using Stack_Proof.pop_toList[of old] 
              Stack_Proof.size_isNotEmpty[of old] 
              Stack_Proof.size_pop[of old]
        by(auto simp: reverseN_tl Suc_diff_Suc take_tl)
    qed
   next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma push_toCurrentList: "toCurrentList (push x left) = x # toCurrentList left"
  apply(induction x left rule: push.induct)
  by(auto simp: put_toList)

(* TODO: Also rename to "pop_toList" *)
lemma toList_pop: "invariant common \<Longrightarrow> 0 < size common \<Longrightarrow> pop common = (x, common') \<Longrightarrow>
   toList common = x # toList common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case
    by(auto simp: Idle_Proof.pop_toList_2 split: prod.splits)
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
        by (smt (z3) Suc_diff_Suc diff_add_inverse diff_commute diff_is_0_eq first_toList hd_append2 hd_conv_nth hd_drop_conv_nth hd_take le_add1 le_add_diff_inverse2 length_greater_0_conv length_rev lessI less_add_same_cancel2 less_le_trans less_or_eq_imp_le Stack_Proof.toList_isNotEmpty rev_nth rev_take Stack_Proof.size_listLength take_eq_Nil)

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
          apply auto
          using Stack_Proof.size_isNotEmpty by blast
        
        from True have "take 1 (Stack.toList old) = take 1 (rev aux)"
          apply(auto simp: reverseN_take)
          by (smt (z3) add_gr_0 hd_append2 hd_take le_add_diff_inverse2 length_greater_0_conv length_rev less_imp_le_nat toList_isNotEmpty Stack_Proof.size_listLength take_eq_Nil take_hd zero_less_diff)

        then have "[last aux] = [first old]"
          using take_last first_take a b 
          by fastforce

        then have "last aux = first old"
          by auto

        with True show ?case 
          apply(auto simp: reverseN_take min_def split: if_splits)
          by (metis Suc_eq_plus1 butlast_conv_take diff_diff_left diff_less_mono2 less_nat_zero_code list.size(3) snoc_eq_iff_butlast)+
      next
        case False

        then have a: "take (remained - length new) aux \<noteq> []"
          by auto

        from False have b: "\<not>Stack.isEmpty old"
          apply auto
          using Stack_Proof.size_isNotEmpty by blast

        from False have "take 1 (Stack.toList old) = take 1 (rev (take (remained - length new) aux))"
          apply(auto simp: reverseN_take)
          by (smt (verit, ccfv_threshold) Nil_is_append_conv Nil_is_rev_conv bot_nat_0.extremum_uniqueI diff_is_0_eq hd_append2 hd_take length_greater_0_conv less_add_same_cancel2 less_le_trans toList_isNotEmpty not_le Stack_Proof.size_listLength take_eq_Nil take_hd)


        then have c: "[first old] = [last (take (remained - length new) aux)]"
          using take_last first_take a b
          by metis


        with False show ?case 
          apply(auto simp: reverseN_take min_def split: if_splits)
          by (smt (z3) Nil_is_rev_conv Suc_diff_Suc first_toList hd_append2 hd_rev hd_take last_snoc le_Suc_eq length_greater_0_conv less_imp_Suc_add toList_isNotEmpty not_le Stack_Proof.size_listLength take_eq_Nil take_hd_drop zero_less_Suc)+
      qed
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed


(* TODO: *)
lemma pop_toCurrentList: "invariant common \<Longrightarrow> 0 < size common \<Longrightarrow> pop common = (x, common') \<Longrightarrow> x # toCurrentList common' = toCurrentList common"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case 
  proof(induction idle rule: Idle.pop.induct)
    case (1 stack stackSize)
    then show ?case
    proof(induction current rule: get.induct)
      case (1 added old remained)
      then show ?case apply auto
        by (metis first_pop hd_take list.sel(1) Stack_Proof.size_isNotEmpty)
    next
      case (2 x' xs added old remained)
      then show ?case apply auto
        by (metis Stack_Proof.size_isEmpty first_pop hd_take list.sel(1) old.nat.distinct(2) zero_less_Suc)
    qed
  qed
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case apply(auto split: if_splits)
      using first_pop Stack_Proof.size_isNotEmpty by blast+
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed
  
lemma toCurrentList_size: "\<lbrakk>0 < size common; toCurrentList common = []; invariant common\<rbrakk> \<Longrightarrow> False"
proof(induction common rule: invariant.induct)
  case (1 current idle)
  then show ?case
    using toList_size by auto
next
  case (2 current aux new moved)
  then have "Current.invariant current" 
            "Current.toList current = []"  
            "0 < Current.size current" 
    by(auto split: current.splits)
 
  then show ?case using toList_size by auto
qed

lemma toList_size: "\<lbrakk>0 < size common; toList common = []; invariant common\<rbrakk> \<Longrightarrow> False"
proof(induction common rule: invariant.induct)
  case (1 current idle)
  then show ?case
    using toList_size by auto
next
  case (2 current aux new moved)
  then have "Current.invariant current" 
            "Current.toList current = []"  
            "0 < Current.size current" 
    by(auto split: current.splits)
 
  then show ?case using toList_size by auto
qed

lemma size_isEmpty: "invariant common \<Longrightarrow> size common = 0 \<Longrightarrow> isEmpty common"
proof(induction common rule: isEmpty.induct)
  case (1 current idle)
  then show ?case 
    by(auto simp: min_def size_isEmpty newSize_isEmpty split: if_splits)
next
  case (2 current)
  then have "Current.invariant current" 
    by(auto split: current.splits)

  with 2 show ?case 
    by(auto simp: min_def size_isEmpty newSize_isEmpty split: if_splits)
qed
  
lemma tick_size: "invariant x \<Longrightarrow> Common.size x = Common.size (Common.tick x)"
proof(induction x rule: Common.tick.induct)
  case (1 current idle)
  then show ?case by auto
next
  case (2 current aux new moved)
  then show ?case 
    by(auto simp: min_def split: current.splits)
qed

lemma tick_newSize: "invariant x \<Longrightarrow> newSize x = newSize (tick x)"
proof(induction x rule: Common.tick.induct)
  case (1 current idle)
  then show ?case by auto
next
  case (2 current aux new moved)
  then show ?case by(auto split: current.splits)
qed

lemma remainingSteps_tick: "\<lbrakk>invariant common; remainingSteps common > 0\<rbrakk>
   \<Longrightarrow> remainingSteps common = Suc (remainingSteps (tick common))"
  apply(induction common)
  by(auto split: current.splits)

lemma remainingSteps_tick_0: "\<lbrakk>invariant common; remainingSteps common = 0\<rbrakk>
   \<Longrightarrow> remainingSteps (tick common) = 0"
  apply(induction common)
  by(auto split: current.splits)

lemma remainingSteps_push: "invariant common \<Longrightarrow> 
  remainingSteps common = remainingSteps (push x common)"
proof(induction x common rule: Common.push.induct)
  case (1 x current stack stackSize)
  then show ?case by auto
next
  case (2 x current aux new moved)
  then show ?case by(auto split: current.splits)
qed

lemma remainingSteps_pop: "\<lbrakk>invariant common; 0 < size common; Common.pop common = (x, common')\<rbrakk> 
  \<Longrightarrow> Common.remainingSteps common' \<le> Common.remainingSteps common"
proof(induction common rule: Common.pop.induct)
  case (1 current idle)
  then show ?case 
  proof(induction idle rule: Idle.pop.induct)
    case (1 stack stackSize)
    then show ?case  
    proof(induction current rule: get.induct)
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
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case 
      by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma size_push: "invariant common \<Longrightarrow> Suc (size common) = size (push x common)"
proof(induction x common rule: Common.push.induct)
  case (1 x current stack stackSize)
  then show ?case 
    by(auto simp: min_def size_put Stack_Proof.size_push)
next
  case (2 x current aux new moved)
  then show ?case 
    by(auto simp: size_put split: current.splits)
qed

lemma newSize_push: "invariant common \<Longrightarrow> Suc (newSize common) = newSize (push x common)"
proof(induction x common rule: Common.push.induct)
  case (1 x current stack stackSize)
  then show ?case 
    by(auto simp: min_def size_put newSize_put)
next
  case (2 x current aux new moved)
  then show ?case 
    by(auto split: current.splits)
qed

lemma size_pop: "\<lbrakk>invariant common; 0 < size common; pop common = (x, common')\<rbrakk>
   \<Longrightarrow> Suc (size common') = size common"
proof(induction common rule: Common.pop.induct)
  case (1 current idle)
  then show ?case 
    using size_get[of current] size_pop[of idle] size_isNotEmpty[of idle]
    by(auto split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case 
    using size_get[of current] apply(induction current rule: get.induct)
    by auto
qed

lemma newSize_pop: "\<lbrakk>invariant common; 0 < newSize common; pop common = (x, common')\<rbrakk>
   \<Longrightarrow>  Suc (newSize common') = newSize common"
proof(induction common rule: Common.pop.induct)
  case (1 current idle)
  then show ?case
    using newSize_get[of current]
    by(auto split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma size_newSize: "\<lbrakk>invariant common; 0 < size common\<rbrakk> \<Longrightarrow> 0 < newSize common"
  by(induction common) auto

end