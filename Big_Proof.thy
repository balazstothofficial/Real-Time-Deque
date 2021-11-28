theory Big_Proof
  imports Big Common_Proof
begin

lemma helper: "Big.toList (Big.tick (Reverse x1 x2a x3 x4)) = Current.toList x1"
  apply(induction x4)
  by(auto split: current.splits)

lemma tick: "toList (tick state) = toList state"
  apply(induction state)
  by(auto simp: helper tick)

lemma helper_1: "tick (Reverse current big auxB count) = Reverse current' big' auxB' count' 
            \<Longrightarrow> Current.invariant current 
            \<Longrightarrow> Current.invariant current'"
  apply(induction "(Reverse current big auxB count)" arbitrary: big auxB count big' auxB' count' rule: tick.induct)
  by auto

lemma invariant_tick: "invariant state \<Longrightarrow> invariant (tick state)"
  apply(induction state rule: tick.induct)
    apply(auto simp: rev_take invariant_tick split: current.splits)
  (* TODO: *)
  by (smt (z3) Nat.diff_diff_right Stack_Proof.pop Suc_le_D add_Suc_right append_Nil2 diff_diff_cancel diff_less empty first length_drop length_rev nat_less_le size_listLength take_Nil take_Suc zero_less_Suc)

lemma pop: "\<lbrakk>\<not> isEmpty big; pop big = (x, big')\<rbrakk> \<Longrightarrow> x # toList big' = toList big"
  apply(induction big arbitrary: x rule: pop.induct)
  by(auto simp: get Common_Proof.pop split: prod.splits current.splits if_splits)

lemma push: "toList (push x big) = x # toList big"
  apply(induction x big rule: push.induct)
  by(auto simp: put Common_Proof.push)

lemma invariant_push: "invariant big \<Longrightarrow> invariant (push x big)"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case by(auto simp: invariant_push)
next
  case (2 x current big auxB count)
  then show ?case by(auto split: current.splits)
qed

lemma helper_2: "\<lbrakk>
  current = Current x1 (List.length x1) x3 (Stack.size x3); count < Stack.size x3;
  \<not> Current.isEmpty (Current x1 (List.length x1) x3 (Stack.size x3));
  Stack.toList x3 = drop (List.length auxB + count - Stack.size x3) (rev auxB) @ take count (Stack.toList big);
  Stack.size x3 - count \<le> List.length auxB; 
  get (Current x1 (List.length x1) x3 (Stack.size x3)) = (x, Current x1a x2a x3a x4);
  big' = Reverse (Current x1a x2a x3a x4) big auxB count\<rbrakk>
       \<Longrightarrow> Stack.toList x3a = drop (List.length auxB + count - x4) (rev auxB) @ drop (count - x4) (take count (Stack.toList big))"
proof(induction "Current x1 (List.length x1) x3 (Stack.size x3)" rule: get.induct)
  case 1
  then show ?case 
    apply auto
    (* TODO *)
    by (smt (z3) Nat.diff_diff_right Stack_Proof.pop Suc_diff_Suc Suc_diff_le diff_diff_cancel diff_is_0_eq helper_2 leD le_diff_conv length_0_conv length_drop length_rev less_imp_le not_less_eq rev_take tl_append2)
next
  case (2 x xs)
  then show ?case by auto
qed

lemma helper_3: "\<lbrakk>current = Current x1 (List.length x1) x3 (Stack.size x3); count < Stack.size x3;
        \<not> Current.isEmpty (Current x1 (List.length x1) x3 (Stack.size x3));
        Stack.toList x3 = drop (List.length auxB + count - Stack.size x3) (rev auxB) @ take count (Stack.toList big);
        Stack.size x3 - count \<le> List.length auxB; get (Current x1 (List.length x1) x3 (Stack.size x3)) = (x, Current x1a x2a x3a x4);
        big' = Reverse (Current x1a x2a x3a x4) big auxB count\<rbrakk>
       \<Longrightarrow> x4 - count \<le> List.length auxB"
proof(induction "Current x1 (List.length x1) x3 (Stack.size x3)" rule: get.induct)
  case 1
then show ?case by auto
next
  case (2 x xs)
  then show ?case by auto
qed

lemma helper_4: "\<lbrakk>
  current = Current x1 (List.length x1) x3 (Stack.size x3);
  count < Stack.size x3;
  \<not> Current.isEmpty (Current x1 (List.length x1) x3 (Stack.size x3));
  Stack.toList x3 = drop (List.length auxB + count - Stack.size x3) (rev auxB) @ take count (Stack.toList big);
  Stack.size x3 - count \<le> List.length auxB; get (Current x1 (List.length x1) x3 (Stack.size x3)) = (x, Current x1a x2a x3a x4);
  big' = Reverse (Current x1a x2a x3a x4) big auxB count
\<rbrakk> \<Longrightarrow> count \<le> x4"
proof(induction "Current x1 (List.length x1) x3 (Stack.size x3)" rule: get.induct)
case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case by auto
qed

lemma invariant_pop: "\<lbrakk>\<not> isEmpty big; invariant big; pop_invariant big; pop big = (x, big')\<rbrakk>
   \<Longrightarrow> invariant big'"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: Common_Proof.invariant_pop split: prod.splits)
next
  case (2 current big auxB count)
  then show ?case
    apply(auto split: current.splits prod.splits)
  (* TODO: *)
    apply (meson Big_Proof.helper_2)
       apply (meson Current.invariant.simps invariant_get)+
     apply (meson helper_3)
    by (meson helper_4)
qed

end
