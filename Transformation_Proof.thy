theory Transformation_Proof
  imports Transformation Small_Proof Big_Proof Stack_Proof Current_Proof 
begin

lemmas tick = Small_Proof.tick Big_Proof.tick Common_Proof.tick

(* TODO: Naming *)
lemma ticks_help: "tickStates (big, small) = (newBig, newSmall) \<Longrightarrow> Big.toList big = Big.toList newBig"
  apply(induction "(big, small)" rule: tickStates.induct)
  by(auto simp: tick split: current.splits if_splits)

lemma ticks_help2: "tickStates (big, small) = (newBig, newSmall) \<Longrightarrow> Small.toList small = Small.toList newSmall"
  apply(induction "(big, small)" rule: tickStates.induct)
  by(auto simp: tick split: current.splits if_splits)

lemma ticks_help': "tickStates (tickStates (tickStates (tickStates (big, small))))
         = (newBig, newSmall) \<Longrightarrow> Big.toList big = Big.toList newBig"
  by (metis prod.exhaust_sel ticks_help)

lemma ticks_help2': "tickStates (tickStates (tickStates (tickStates  (big, small))))
     = (newBig, newSmall) \<Longrightarrow> Small.toList small = Small.toList newSmall"
  by (metis prod.exhaust_sel ticks_help2)


lemma ticks_helpFUCK: "tickStates (big, push x small) = (newBig, newSmall) \<Longrightarrow> x #  Small.toList small = Small.toList newSmall"
  apply(induction "(big, push x small)" rule: tickStates.induct)
  by(auto simp: Small_Proof.push ticks_help2 split: current.splits if_splits)

lemma fourTicks_helpFUCK: "tickStates (tickStates (tickStates (tickStates (big, push x small)))) = (newBig, newSmall) \<Longrightarrow> x #  Small.toList small = Small.toList newSmall"
  by (simp add: Small_Proof.push ticks_help2')

lemma ticks_helpFUCK': "tickStates (Big.push x big, small) = (newBig, newSmall) \<Longrightarrow> x # Big.toList big = Big.toList newBig"
  apply(induction "(Big.push x big, small)" rule: tickStates.induct)
      apply (smt (verit) Big.push.elims Big.state.simps Big.toList.simps put ticks_help)
     apply (smt (verit) Big.push.elims Big.state.simps(4) Big.toList.simps(2) put ticks_help)
  
  apply (smt (verit) Big.push.elims Big.state.simps(4) Big.toList.simps(1) Common_Proof.push ticks_help)

   apply (smt (verit, best) Big.push.elims Big.toList.simps(1) Big.toList.simps(2) Common_Proof.push put ticks_help)
  by (smt (verit, best) Big.push.elims Big.toList.simps(1) Big.toList.simps(2) Common_Proof.push put ticks_help)

lemma fourTicks_helpFUCK': "tickStates (tickStates (tickStates (tickStates (Big.push x big, small)))) = (newBig, newSmall) \<Longrightarrow> x # Big.toList big = Big.toList newBig"
  by (metis prod.exhaust_sel ticks_help ticks_helpFUCK')
  
lemma ticks_helpFUCK_2: "tickStates (big, push x small) = (newBig, push y newSmall) \<Longrightarrow> Small.toList small = Small.toList newSmall"
  apply(induction "(big, push x small)" rule: tickStates.induct)
      apply(auto simp: tick push put split: current.splits if_splits)
      apply (metis Small_Proof.push list.inject ticks_helpFUCK)
     apply (metis Small_Proof.push Small_Proof.tick list.inject)
    apply (metis Small_Proof.push Small_Proof.tick list.inject)
   apply (metis Small_Proof.push list.inject ticks_helpFUCK)
  by (metis Small_Proof.push list.inject ticks_helpFUCK)

lemma ticks: "toListLeft (ticks transformation) = toListLeft transformation"
  apply(induction transformation rule: toListLeft.induct)
  by(auto simp: ticks_help ticks_help2 split: prod.splits)

lemma fourTicks: "toListLeft (fourTicks transformation) = toListLeft transformation"
  by(auto simp: ticks)

lemma sixTicks: "toListLeft (sixTicks transformation) = toListLeft transformation"
  by(auto simp: ticks)

lemmas all_ticks = tick ticks sixTicks fourTicks

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits

(* TODO: *)
lemma ticks_helper: "\<lbrakk>
  tickStates
         (Reverse (Current [] 0 (Stack.push x leftValues) (Stack.size leftValues - Stack.size rightValues)) (Stack.push x leftValues) [] (Stack.size leftValues - Stack.size rightValues),
         Reverse1 (Current [] 0 rightValues (Suc (2 * Stack.size rightValues))) rightValues []) = (left, right)
    \<rbrakk>
       \<Longrightarrow> Big.toList left @ rev (Small.toList right) = x # Stack.toList leftValues @ rev (Stack.toList rightValues)"
proof(induction  
         "(Reverse (Current [] 0 (Stack.push x leftValues) (Stack.size leftValues - Stack.size rightValues)) (Stack.push x leftValues) [] (Stack.size leftValues - Stack.size rightValues)
         , Reverse1 (Current [] 0 rightValues (Suc (2 * Stack.size rightValues))) rightValues [])"
        rule: tickStates.induct
        )
  case 1
  then show ?case 
    by(auto simp: Stack_Proof.push)
next
  case ("2_1" vd)
   then have left: "left = Big.tick (Reverse (Current [] 0 (Stack.push x leftValues) (Stack.size leftValues - Stack.size rightValues)) (Stack.push x leftValues) [] (Stack.size leftValues - Stack.size rightValues))"
     by (metis tickStates.simps(2) prod.inject)
   then have right: "right = Small.tick (Reverse1 (Current [] 0 rightValues (Suc (2 * Stack.size rightValues))) rightValues [])"
     by (metis "2_1.hyps" "2_1.prems" tickStates.simps(2) old.prod.inject)
   from left right show ?case
     by (simp add: Big_Proof.tick Stack_Proof.push)
 qed

lemma test_2_1: "put x current = Current x1 x2 x3 x4 
        \<Longrightarrow> x1 @ Stack.toList x3 = x # Current.toList current"
  apply(induction x current rule: put.induct)
  by auto

lemma small_push: "x # Small.toList small = Small.toList (Small.push x small) "
  apply(induction x small rule: Small.push.induct)
  by(auto simp: Common_Proof.push put)

lemma small_push_2: "Small.toList (Small.push x small) = x # Small.toList small"
  apply(induction x small rule: Small.push.induct)
  by(auto simp: Common_Proof.push put)

lemma test_2: "tickStates (big, Small.push x small) = (big', small')
           \<Longrightarrow> Small.toList small' = x # Small.toList small"
  by(auto simp: small_push ticks_help2)

lemma test: " \<lbrakk>
    tickStates (x1b, x2b) = (x1c, small'); 
    tickStates (x1a, x2a) = (x1b, x2b); 
    tickStates (x1, x2) = (x1a, x2a);
    tickStates (right, Small.push x left) = (x1, x2)\<rbrakk>
       \<Longrightarrow> Small.toList small' = x # Small.toList left"
  by (metis ticks_help2 test_2)

end
