theory Transformation_Proof
  imports  Transformation States_Proof
begin

lemma invariant_tick: "invariant transformation \<Longrightarrow> invariant (tick transformation)"
proof(induction transformation rule: tick.induct)
  case (1 small big)

  then have "States.invariant (big, small)"
    by auto
  
  then have "States.invariant (States.tick (big, small))"
    using States_Proof.invariant_tick by blast

  then have "Transformation.invariant (case States.tick (big, small) of (big, small) \<Rightarrow> Left small big)"
    by(auto split: prod.split)

  then show ?case by auto
next
  case (2 big small)

  then have "States.invariant (big, small)"
    by auto
  
  then have "States.invariant (States.tick (big, small))"
    using States_Proof.invariant_tick by blast

  then have "Transformation.invariant (case States.tick (big, small) of (big, small) \<Rightarrow> Right big small)"
    by(auto split: prod.split)

  then show ?case by auto
qed

lemma tick_toList: "invariant transformation \<Longrightarrow> toListLeft (tick transformation) = toListLeft transformation"
proof(induction transformation rule: tick.induct)
  case (1 small big)

  then have "States.toListSmallFirst (big, small) = Small.toCurrentList small @ rev (Big.toCurrentList big)"
    by auto

  then have "States.toListSmallFirst (States.tick (big, small)) = Small.toCurrentList small @ rev (Big.toCurrentList big)"
    using "1.prems" States_Proof.tick_toList by force

  then have "toListLeft (case States.tick (big, small) of (big, small) \<Rightarrow> transformation.Left small big) =
         Small.toCurrentList small @ rev (Big.toCurrentList big)"
    by(auto split: prod.splits)

  with 1 show ?case 
    by auto
next
  case (2 big small)
  
  then have statesToList: "States.toListBigFirst (big, small) = Big.toCurrentList big @ rev (Small.toCurrentList small)"
    using invariant_listBigFirst by fastforce

  then have "States.toListBigFirst (States.tick (big, small)) = Big.toCurrentList big @ rev (Small.toCurrentList small)"
    using "2.prems" States_Proof.tick_toList by force

  then have "toListLeft (case States.tick (big, small) of (big, small) \<Rightarrow> Right big small) =
         Big.toCurrentList big @ rev (Small.toCurrentList small)"
   by(auto split: prod.splits)

  with 2 show ?case 
    using statesToList by fastforce
qed

lemma invariant_pop_small_left: "invariant (Left small big) \<Longrightarrow> \<not>Small.isEmpty small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invariant (Left small' big)"
  by (metis (no_types, lifting) Small_Proof.size_isEmpty States.invariant.elims(2) Transformation.invariant.simps(1) bot_nat_0.extremum case_prodD invariant_pop_small_size le_eq_less_or_eq)

lemma invariant_pop_small_left_2: "invariant (Left small big) \<Longrightarrow> 0 < Small.size small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invariant (Left small' big)"
  by (meson Transformation.invariant.simps(1) invariant_pop_small_size)

lemma invariant_pop_big_left: "invariant (Left small big) \<Longrightarrow> \<not>Big.isEmpty big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invariant (Left small big')"
  by (metis (no_types, lifting) Big_Proof.size_isEmpty States.invariant.elims(2) Transformation.invariant.simps(1) case_prodD invariant_pop_big_size neq0_conv)

lemma invariant_pop_big_left_2: "invariant (Left small big) \<Longrightarrow> 0 < Big.size big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invariant (Left small big')"
  by (meson Transformation.invariant.simps(1) invariant_pop_big_size)

lemma invariant_pop_small_right: "invariant (Right big small) \<Longrightarrow> \<not>Small.isEmpty small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invariant (Right big small')"
  by (metis (no_types, lifting) Small_Proof.size_isEmpty States.invariant.elims Transformation.invariant.simps bot_nat_0.extremum case_prodD invariant_pop_small_size le_eq_less_or_eq)

lemma invariant_pop_small_right_2: "invariant  (Right big small) \<Longrightarrow> 0 < Small.size small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invariant (Right big small')"
  by (meson Transformation.invariant.simps invariant_pop_small_size)

lemma invariant_pop_big_right: "invariant  (Right big small) \<Longrightarrow> \<not>Big.isEmpty big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invariant (Right big' small)"
  by (metis (no_types, lifting) Big_Proof.size_isEmpty States.invariant.elims Transformation.invariant.simps case_prodD invariant_pop_big_size neq0_conv)

lemma invariant_pop_big_right_2: "invariant  (Right big small) \<Longrightarrow> 0 < Big.size big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invariant (Right big' small)"
  by (meson Transformation.invariant.simps invariant_pop_big_size)

lemma nTicks: "invariant transformation \<Longrightarrow> toListLeft ((tick^^n) transformation) = toListLeft transformation"
  apply(induction n arbitrary: transformation)
  by(auto simp: funpow_swap1 tick_toList invariant_tick)

lemma fourTicks: "invariant transformation \<Longrightarrow> toListLeft (fourTicks transformation) = toListLeft transformation"
  by(auto simp: fourTicks_def nTicks)

lemma sixTicks: "invariant transformation \<Longrightarrow> toListLeft (sixTicks transformation) = toListLeft transformation"
  by(auto simp: sixTicks_def nTicks)

lemmas ticks = States_Proof.tick_toList Big_Proof.tick_toList Common_Proof.tick_toList tick_toList nTicks sixTicks fourTicks

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits

lemma invariant_nTicks: "invariant transformation \<Longrightarrow> invariant ((tick^^n) transformation)"
  apply(induction n arbitrary: transformation)
  by(auto simp: invariant_tick)

lemma invariant_fourTicks: "invariant transformation \<Longrightarrow> invariant (fourTicks transformation)"
  by(auto simp: invariant_nTicks fourTicks_def)

lemma invariant_sixTicks: "invariant transformation \<Longrightarrow> invariant (sixTicks transformation)"
  by(auto simp: invariant_nTicks sixTicks_def)

lemma tick_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (tick transformation)"
  apply(induction transformation)
  apply (metis Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) prod.case_eq_if prod.exhaust_sel tick_inSizeWindow)
  by (metis Transformation.inSizeWindow.simps(2) Transformation.invariant.simps(2) Transformation.tick.simps(2) prod.case_eq_if prod.exhaust_sel tick_inSizeWindow)
 
lemma nTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow ((tick ^^ n) transformation)"
  apply(induction n)
   apply(auto simp: funpow_swap1 invariant_nTicks tick_inSizeWindow)
  by (metis Transformation_Proof.tick_inSizeWindow funpow_swap1 invariant_nTicks)

lemma fourTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (fourTicks transformation)"
  by(auto simp: nTicks_inSizeWindow fourTicks_def)

lemma sixTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (sixTicks transformation)"
  by(auto simp: nTicks_inSizeWindow sixTicks_def)

lemma remainingStepsDecline_3: "invariant transformation \<Longrightarrow> Suc n < remainingSteps transformation \<Longrightarrow> n < remainingSteps (tick transformation)"
proof(induction transformation)
  case (Left small big)
  then show ?case using remainingStepsDecline_3[of "(big, small)" n] 
    by(auto split: prod.splits)
next
case (Right big small)
  then show ?case using remainingStepsDecline_3[of "(big, small)" n] 
    by(auto split: prod.splits)
qed

lemma remainingStepsDecline_4: "invariant transformation \<Longrightarrow> Suc n < remainingSteps ((tick ^^ m) transformation) \<Longrightarrow> n < remainingSteps ((tick ^^ Suc m) transformation)"
  by(auto simp: remainingStepsDecline_3 invariant_nTicks)

lemma remainingStepsDecline_5': "invariant transformation \<Longrightarrow> remainingSteps transformation = 1 \<Longrightarrow> remainingSteps (tick transformation) = 0"
proof(induction transformation)
  case (Left small big)
  then show ?case using States_Proof.remainingStepsDecline_2[of "(big, small)"]
    by(auto split: prod.splits)
next
  case (Right big small)
  then show ?case using States_Proof.remainingStepsDecline_2[of "(big, small)"]
    by(auto split: prod.splits)
qed

lemma tooEasy: "States.remainingSteps ((States.tick ^^ n) (big, small)) = remainingSteps ((tick ^^ n) (Left small big))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case apply(auto split: prod.splits)
    by (metis Transformation.tick.simps(1) case_prod_unfold funpow_swap1 prod.exhaust_sel) 
qed

lemma tooEasy_2: "States.remainingSteps ((States.tick ^^ n) (big, small)) = remainingSteps ((tick ^^ n) (Right big small))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case apply(auto split: prod.splits)
    by (metis Transformation.tick.simps(2) case_prod_unfold funpow_swap1 prod.exhaust_sel) 
qed

lemma remainingStepsDecline_5: "invariant transformation \<Longrightarrow> remainingSteps transformation \<le> n \<Longrightarrow> remainingSteps ((tick ^^ n) transformation) = 0"
proof(induction transformation)
  case (Left small big)
  then show ?case using remainingStepsDecline_5[of "(big, small)" n]
    by(auto simp: tooEasy split: prod.splits)
next
  case (Right big small)
  then show ?case using remainingStepsDecline_5[of "(big, small)"]
    by(auto simp: tooEasy_2 split: prod.splits)
qed

lemma sizeWindow_steps: "invariant transformation \<Longrightarrow> n < remainingSteps transformation \<Longrightarrow> inSizeWindow' transformation (remainingSteps transformation - n) \<Longrightarrow> inSizeWindow' ((tick ^^ n) transformation) (remainingSteps ((tick ^^ n) transformation))"
proof(induction n arbitrary: transformation)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
  proof(induction transformation)
    case (Left x1 x2)
    then show ?case
      sorry
  next
    case (Right x1 x2)
    then show ?case 
      sorry
  qed
qed

lemma sizeWindow'_sizeWindow: "inSizeWindow' transformation (remainingSteps transformation) = inSizeWindow transformation"
  apply(induction transformation rule: inSizeWindow.induct)
  by auto

lemma size_tick: "invariant (Left left right) \<Longrightarrow> tick (Left left right) = Left left' right' \<Longrightarrow> Small.size left = Small.size left'"
  using same_b_1[of right left right' left']
  by(auto split: prod.splits)

lemma size_tick_2: "invariant (Left left right) \<Longrightarrow> tick (Left left right) = Left left' right' \<Longrightarrow> Small.newSize left = Small.newSize left'"
  using same_b_2[of right left right' left']
  by(auto split: prod.splits)

lemma size_tick_3: "invariant (Right left right) \<Longrightarrow> tick (Right left right) = Right left' right' \<Longrightarrow> Small.size right = Small.size right'"
  using same_b_1[of left right left' right']
  by(auto split: prod.splits)

lemma size_tick_4: "invariant (Right left right) \<Longrightarrow> tick (Right left right) = Right left' right' \<Longrightarrow> Small.newSize right = Small.newSize right'"
  using same_b_2[of left right left' right']
  by(auto split: prod.splits)

lemma size_tick_5: "invariant (Left left right) \<Longrightarrow> tick (Left left right) = Left left' right' \<Longrightarrow> Big.size right = Big.size right'"
  using same_b_1_1[of right left right' left']
  by(auto split: prod.splits)

lemma size_tick_6: "invariant (Left left right) \<Longrightarrow> tick (Left left right) = Left left' right' \<Longrightarrow> Big.newSize right = Big.newSize right'"
  using same_b_2_1[of right left right' left']
  by(auto split: prod.splits)

lemma size_tick_7: "invariant (Right left right) \<Longrightarrow> tick (Right left right) = Right left' right' \<Longrightarrow> Big.size left = Big.size left'"
  using same_b_1_1[of left right left' right']
  by(auto split: prod.splits)

lemma size_tick_8: "invariant (Right left right) \<Longrightarrow> tick (Right left right) = Right left' right' \<Longrightarrow> Big.newSize left = Big.newSize left'"
  using same_b_2_1[of left right left' right']
  by(auto split: prod.splits)

lemma size_tick_n: "invariant (Left left right) \<Longrightarrow> (tick ^^ n) (Left left right) = Left left' right' \<Longrightarrow> Small.size left = Small.size left'"
  using same_b[of right left n right' left']
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
      by (smt (z3) Suc.IH Suc.prems(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) Transformation_Proof.invariant_tick case_prod_unfold funpow_swap1 prod.exhaust_sel tick_inSizeWindow_3)
  qed

lemma size_tick_n_2: "invariant (Left left right) \<Longrightarrow> (tick ^^ n) (Left left right) = Left left' right' \<Longrightarrow> Small.newSize left = Small.newSize left'"
  using same_bb[of right left n right' left']
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) Transformation_Proof.invariant_tick case_prod_unfold funpow_swap1 prod.exhaust_sel tick_inSizeWindow_1)
qed

lemma size_tick_n_3: "invariant (Right left right) \<Longrightarrow> (tick ^^ n) (Right left right) = Right left' right' \<Longrightarrow> Small.size right = Small.size right'"
  using same_b[of left right n left' right']
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) Transformation.invariant.simps(2) Transformation.tick.simps(2) Transformation_Proof.invariant_tick case_prodE case_prod_unfold funpow_swap1 invariant_tick_3 same_b snd_conv tick_inSizeWindow_3)
  qed

lemma size_tick_n_4: "invariant (Right left right) \<Longrightarrow> (tick ^^ n) (Right left right) = Right left' right' \<Longrightarrow> Small.newSize right = Small.newSize right'"
  using same_bb[of left right n left' right']
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) Transformation.invariant.simps(2) Transformation.tick.simps(2) Transformation_Proof.invariant_tick case_prod_unfold funpow_swap1 prod.exhaust_sel same_b_2)
qed

lemma size_tick_n_5: "invariant (Left left right) \<Longrightarrow> (tick ^^ n) (Left left right) = Left left' right' \<Longrightarrow> Big.size right = Big.size right'"
  using same_b1[of right left n right' left']
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) States_Proof.invariant_tick Suc.IH Suc.prems(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) case_prodE funpow_swap1 invariant_tick_3 old.prod.case same_b_1_1)
  qed

lemma size_tick_n_6: "invariant (Left left right) \<Longrightarrow> (tick ^^ n) (Left left right) = Left left' right' \<Longrightarrow> Big.newSize right = Big.newSize right'"
  using same_bb[of right left n right' left']
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) States.toCurrentList.simps States_Proof.tick_toCurrentList States_Proof.tick_toList Suc.prems(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) case_prodE case_prod_conv funpow_swap1 invariant_tick_1 invariant_tick_3 tick_inSizeWindow_1 tick_inSizeWindow_2)
qed

lemma size_tick_n_7: "invariant (Right left right) \<Longrightarrow> (tick ^^ n) (Right left right) = Right left' right' \<Longrightarrow> Big.size left = Big.size left'"
  using same_b[of left right n left' right']
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (verit, best) Suc.IH Suc.prems(1) Transformation.tick.simps(2) Transformation_Proof.invariant_tick funpow_swap1 size_tick_7 size_tick_n_3 split_beta)
  qed

lemma size_tick_n_8: "invariant (Right left right) \<Longrightarrow> (tick ^^ n) (Right left right) = Right left' right' \<Longrightarrow> Big.newSize left = Big.newSize left'"
  using same_bb[of left right n left' right']
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (verit, best) Suc.IH Suc.prems(1) Transformation.tick.simps(2) Transformation_Proof.invariant_tick funpow_swap1 size_tick_8 size_tick_n_4 split_beta)
qed

end
