theory Common_Proof
  imports Common Idle_Proof Current_Proof
begin

lemma take_hd: "xs \<noteq> [] \<Longrightarrow> take (Suc 0) xs = [hd xs]"
  apply(induction xs)
  by auto

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
        by auto
     qed
  qed
qed

  
lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
  apply(induction x common rule: push.induct)
  by(auto simp: invariant_put Stack_Proof.size_push split: stack.splits current.splits)

lemma invariant_pop: "\<lbrakk>
  \<not> isEmpty common; 
  invariant common;
  pop common = (x, common')
\<rbrakk> \<Longrightarrow> invariant common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 idle)
  then show ?case 
    by(auto simp: invariant_get invariant_pop split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: get.induct)
    case (1 added old remained)
    then show ?case
    proof(induction old rule: Stack.pop.induct)
      case 1
      then show ?case 
        by auto
    next
      case (2  x left right)
      then show ?case
        by auto
    next
      case (3 x right)
      then show ?case 
        by auto
    qed
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma currentList_push: "toCurrentList (push x left) = x # toCurrentList left"
  apply(induction x left rule: push.induct)
  by(auto simp: put)

lemma some_empty: "\<lbrakk>isEmpty (tick common); \<not> isEmpty common; invariant common\<rbrakk> \<Longrightarrow> False"
  apply(induction common rule: tick.induct)
  by(auto split: current.splits if_splits)

end