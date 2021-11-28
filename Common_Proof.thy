theory Common_Proof
  imports Common Current_Proof
begin

lemma tick: "toList (tick common) = toList common"
  apply(induction common)
  by(auto split: current.splits)

lemma tick_2: "Common.tick common = common' \<Longrightarrow> Common.toList common = Common.toList common'"
  by(auto simp: tick)

lemma pop: "\<lbrakk>\<not> isEmpty common; pop common = (x, common')\<rbrakk> \<Longrightarrow> x # toList common' = toList common"
  apply(induction common arbitrary: x rule: pop.induct)
   apply(auto simp: get  split: prod.splits current.splits if_splits)
  using get by fastforce+

lemma push: "toList (push x common) = x # toList common"
  apply(induction x common rule: push.induct)
  by(auto simp: put)

lemma take_hd: "xs \<noteq> [] \<Longrightarrow> take (Suc 0) xs = [hd xs]"
  apply(induction xs)
  by auto

lemma invariant_tick: "invariant common \<Longrightarrow> invariant (tick common)" 
  apply(induction common rule: tick.induct)
   apply(auto split: current.splits)
    (* TODO: *)
  apply (metis Suc_diff_Suc append_Nil diff_is_0_eq' nat_neq_iff rev_append rev_rev_ident size_listLength take_Nil take_hd)
    by (metis Suc_diff_Suc gen_length_def hd_Cons_tl hd_take le_SucI length_append length_code length_rev list.size(3) nat_le_linear not_le rev.simps(2) size_listLength take_tl zero_less_Suc)

lemma invariant_push: "invariant common \<Longrightarrow> invariant (push x common)"
  apply(induction x common rule: push.induct)
  by(auto simp: invariant_put size_push put Stack_Proof.push split: current.splits)

(* TODO: *)

lemma helper_2: "n < length xs \<Longrightarrow> tl (rev (take (Suc n) xs)) = rev (take n xs)"
  apply(induction xs; induction n)
     apply auto
  by (metis Suc_diff_Suc drop_Suc gr_implies_not0 length_0_conv old.nat.distinct(2) rev_is_Nil_conv rev_take take_eq_Nil tl_append2 tl_drop)

lemma helper_1: 
assumes
  "\<not> Stack.isEmpty old"
  "Stack.toList old = rev (take (Stack.size old - length new) aux) @ new"
  "length new < Stack.size old"
  "common' = Copy (Current [] 0 (Stack.pop old) (Stack.size old - Suc 0)) aux new (length new)" 
  "\<not> Stack.size old - Suc 0 \<le> length new"
  "x = first old"
  "extra' = []" 
  "added' = 0" 
  "old' = Stack.pop old"
  "remaining' = Stack.size old - Suc 0"
shows
  "Stack.toList (Stack.pop old) = rev (take (Stack.size old - Suc (length new)) aux) @ new"
proof -
  from assms have tl: "Stack.toList (Stack.pop old) = tl (Stack.toList old)"
    by(auto simp: Stack_Proof.pop)
  
  with assms have "tl (rev (take (Stack.size old - length new) aux)) = 
                       rev (take (Stack.size old - Suc (length new)) aux)"
    by (smt (z3) Suc_diff_Suc Suc_le_lessD append_eq_conv_conj diff_le_self helper_2 length_drop length_rev length_rotate rev_take rotate_append size_listLength)

  with assms tl have "tl (rev (take (Stack.size old - length new) aux) @ new) = 
                       rev (take (Stack.size old - Suc (length new)) aux) @ new"
    by (metis append_Nil nat_neq_iff size_listLength tl_append2)

  with assms tl show ?thesis
    by auto
  
qed

lemma helper: 
  assumes
  "\<not> Current.isEmpty (Current extra (length extra) old (Stack.size old))"
  "get (Current extra (length extra) old (Stack.size old)) = (x, Current extra' added' old' remaining')"
  "Stack.toList old = rev (take (Stack.size old - length new) aux) @ new"
  "length new < Stack.size old"
  "common' = Copy (Current extra' added' old' remaining') aux new (length new)"
  " \<not> remaining' \<le> length new"
  shows 
  "Stack.toList old' = rev (take (remaining' - length new) aux) @ new"
  using assms apply(induction extra)
  by(auto simp: helper_1)
  

lemma invariant_pop: "\<lbrakk>\<not> isEmpty common; invariant common; pop common = (x, common')\<rbrakk>
   \<Longrightarrow> invariant common'"
  apply(induction common arbitrary: x rule: pop.induct)
   apply(auto simp:  invariant_get get Stack_Proof.pop size_pop empty not_empty split: prod.splits current.splits)
    (* TODO: *)   
         apply (metis Stack_Proof.pop get length_Cons list.sel(3) not_empty size_listLength zero_less_Suc)
        apply (metis empty get list.discI size_pop)
  apply (smt (verit, ccfv_threshold) Current.invariant.simps Current.isEmpty.elims(1) Current.toList.simps append_eq_append_conv current.simps(1) get get.simps(1) get.simps(2) invariant_get leD length_Cons not_less_eq_eq order_class.order.antisym prod.simps(1) self_append_conv2 size_listLength)
    apply (meson Current.invariant.simps invariant_get)
  apply (meson Current.invariant.simps invariant_get)
    apply(simp add: helper)
   apply (meson Current.invariant.simps invariant_get)
  by (meson Current.invariant.simps invariant_get)

end