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

lemma invariant_pop_small_left: "invariant (Left small big) \<Longrightarrow> 0 < Small.size small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invariant (Left small' big)"
  by (meson Transformation.invariant.simps(1) invariant_pop_small_size)

lemma invariant_pop_big_left: "invariant (Left small big) \<Longrightarrow> 0 < Big.size big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invariant (Left small big')"
  by (meson Transformation.invariant.simps(1) invariant_pop_big_size)

lemma invariant_pop_small_right: "invariant  (Right big small) \<Longrightarrow> 0 < Small.size small \<Longrightarrow> Small.pop small = (x, small') \<Longrightarrow> invariant (Right big small')"
  by (meson Transformation.invariant.simps invariant_pop_small_size)

lemma invariant_pop_big_right: "invariant  (Right big small) \<Longrightarrow> 0 < Big.size big \<Longrightarrow> Big.pop big = (x, big') \<Longrightarrow> invariant (Right big' small)"
  by (meson Transformation.invariant.simps invariant_pop_big_size)

lemma nTicks: "invariant transformation \<Longrightarrow> toListLeft ((tick^^n) transformation) = toListLeft transformation"
  apply(induction n arbitrary: transformation)
  by(auto simp: funpow_swap1 tick_toList invariant_tick)

lemma fourTicks: "invariant transformation \<Longrightarrow> toListLeft (fourTicks transformation) = toListLeft transformation"
  by(auto simp: nTicks)

lemma sixTicks: "invariant transformation \<Longrightarrow> toListLeft (sixTicks transformation) = toListLeft transformation"
  by(auto simp: nTicks)

lemmas ticks = States_Proof.tick_toList Big_Proof.tick_toList Common_Proof.tick_toList tick_toList nTicks sixTicks fourTicks

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits

lemma invariant_nTicks: "invariant transformation \<Longrightarrow> invariant ((tick^^n) transformation)"
  apply(induction n arbitrary: transformation)
  by(auto simp: invariant_tick)

lemma invariant_fourTicks: "invariant transformation \<Longrightarrow> invariant (fourTicks transformation)"
  by(auto simp: invariant_nTicks)

lemma invariant_sixTicks: "invariant transformation \<Longrightarrow> invariant (sixTicks transformation)"
  by(auto simp: invariant_nTicks)

lemma tick_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (tick transformation)"
  apply(induction transformation)
  apply (metis Transformation.inSizeWindow.simps(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) prod.case_eq_if prod.exhaust_sel tick_inSizeWindow)
  by (metis Transformation.inSizeWindow.simps(2) Transformation.invariant.simps(2) Transformation.tick.simps(2) prod.case_eq_if prod.exhaust_sel tick_inSizeWindow)
 
lemma nTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow ((tick ^^ n) transformation)"
  apply(induction n)
   apply(auto simp: funpow_swap1 invariant_nTicks tick_inSizeWindow)
  by (metis Transformation_Proof.tick_inSizeWindow funpow_swap1 invariant_nTicks)

lemma fourTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (fourTicks transformation)"
  by(auto simp: nTicks_inSizeWindow)

lemma sixTicks_inSizeWindow: "invariant transformation \<Longrightarrow> inSizeWindow transformation \<Longrightarrow> inSizeWindow (sixTicks transformation)"
  by(auto simp: nTicks_inSizeWindow)

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

lemma remainingStepsStates_remainingStepsLeft: "States.remainingSteps ((States.tick ^^ n) (big, small)) = remainingSteps ((tick ^^ n) (Left small big))"
proof(induction n arbitrary: big small)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case apply(auto split: prod.splits)
    by (metis Transformation.tick.simps(1) case_prod_unfold funpow_swap1 prod.exhaust_sel) 
qed

lemma remainingStepsStates_remainingStepsRight: "States.remainingSteps ((States.tick ^^ n) (big, small)) = remainingSteps ((tick ^^ n) (Right big small))"
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
    by(auto simp: remainingStepsStates_remainingStepsLeft split: prod.splits)
next
  case (Right big small)
  then show ?case using remainingStepsDecline_5[of "(big, small)"]
    by(auto simp: remainingStepsStates_remainingStepsRight split: prod.splits)
qed


lemma remainingSteps_tickN: "invariant transformation \<Longrightarrow>  n < remainingSteps transformation \<Longrightarrow>  remainingSteps transformation - n = remainingSteps ((tick ^^ n) transformation)"
proof(induction transformation)
  case (Left small big)
  then show ?case 
    using remainingSteps_tickN[of "(big, small)" n]
    by (metis Transformation.invariant.simps(1) Transformation.remainingSteps.simps(1) remainingStepsStates_remainingStepsLeft)
next
  case (Right big small)
  then show ?case
    by (metis Transformation.invariant.simps(2) remainingSteps_tickN funpow_0 remainingStepsStates_remainingStepsRight)
qed

lemma tick_inSizeWindow': "invariant transformation \<Longrightarrow>
    inSizeWindow' transformation x \<Longrightarrow> 
    inSizeWindow' (tick transformation) x"
proof(induction transformation)
  case (Left small big)
  then show ?case
    by (smt (verit, best) States.inSizeWindow'.elims(2) States.inSizeWindow'.elims(3) Transformation.inSizeWindow'.simps(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) Transformation_Proof.invariant_tick case_prodE2 case_prod_conv tick_sizeBig tick_newSizeSmall tick_newSizeBig tick_sizeSmall)
next
  case (Right big small)
  then show ?case 
    using tick_inSizeWindow'
    by (smt (verit, ccfv_threshold) Transformation.inSizeWindow'.simps(2) Transformation.invariant.simps(2) Transformation.tick.simps(2) Transformation_Proof.invariant_tick case_prodE2 case_prod_unfold fst_conv snd_conv tick_inSizeWindow')
qed

lemma tickN_inSizeWindow': "invariant transformation \<Longrightarrow>
    inSizeWindow' transformation x \<Longrightarrow> 
    inSizeWindow' ((tick ^^ n) transformation) x"
proof(induction n arbitrary: transformation)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case using tick_inSizeWindow' 
    by (metis Transformation_Proof.invariant_tick comp_eq_dest_lhs funpow_Suc_right) 
qed

lemma sizeWindow_steps: "invariant transformation \<Longrightarrow>
     n < remainingSteps transformation \<Longrightarrow> 
    inSizeWindow' transformation (remainingSteps transformation - n) \<Longrightarrow> 
    inSizeWindow' ((tick ^^ n) transformation) (remainingSteps ((tick ^^ n) transformation))"
  by (simp add: remainingSteps_tickN tickN_inSizeWindow')

lemma sizeWindow'_sizeWindow: "inSizeWindow' transformation (remainingSteps transformation) = inSizeWindow transformation"
  apply(induction transformation rule: inSizeWindow.induct)
  by auto

lemma tickN_left_newSizeSmall: "invariant (Left left right) \<Longrightarrow> (tick ^^ n) (Left left right) = Left left' right' \<Longrightarrow> Small.newSize left = Small.newSize left'"
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) Transformation_Proof.invariant_tick case_prod_unfold funpow_swap1 prod.exhaust_sel tick_newSizeSmall)
qed

lemma tickN_right_newSizeSmall: "invariant (Right left right) \<Longrightarrow> (tick ^^ n) (Right left right) = Right left' right' \<Longrightarrow> Small.newSize right = Small.newSize right'"
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) Transformation.invariant.simps(2) Transformation.tick.simps(2) Transformation_Proof.invariant_tick case_prod_unfold funpow_swap1 prod.exhaust_sel tick_newSizeSmall)
qed


lemma tickN_left_newSizeBig: "invariant (Left left right) \<Longrightarrow> (tick ^^ n) (Left left right) = Left left' right' \<Longrightarrow> Big.newSize right = Big.newSize right'"
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) States.toCurrentList.simps States_Proof.tick_toCurrentList States_Proof.tick_toList Suc.prems(1) Transformation.invariant.simps(1) Transformation.tick.simps(1) case_prodE case_prod_conv funpow_swap1 invariant_tick_1 invariant_tick_3 tick_newSizeSmall tick_newSizeBig)
qed

lemma tickN_right_newSizeBig: "invariant (Right left right) \<Longrightarrow> (tick ^^ n) (Right left right) = Right left' right' \<Longrightarrow> Big.newSize left = Big.newSize left'"
proof(induction n arbitrary: right left right' left')
case 0
then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto split: prod.splits)
    by (smt (z3) Suc.IH Suc.prems(1) Transformation.invariant.simps(2) Transformation.tick.simps(2) Transformation_Proof.invariant_tick case_prodE funpow_swap1 invariant_tick_3 old.prod.case tickN_right_newSizeSmall tick_newSizeBig)
qed

end
