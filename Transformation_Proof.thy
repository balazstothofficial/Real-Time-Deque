theory Transformation_Proof
  imports Transformation Small_Proof Big_Proof Stack_Proof Current_Proof
begin

lemmas tick = Small_Proof.tick Big_Proof.tick Common_Proof.tick

lemma ticks_help: "ticksHelper (big, small) = (newBig, newSmall) \<Longrightarrow> Big.toList big = Big.toList newBig"
  apply(induction "(big, small)" rule: ticksHelper.induct)
  by(auto simp: tick split: current.splits if_splits)

lemma ticks_help2: "ticksHelper (big, small) = (newBig, newSmall) \<Longrightarrow> Small.toList small = Small.toList newSmall"
  apply(induction "(big, small)" rule: ticksHelper.induct)
  by(auto simp: tick split: current.splits if_splits)

lemma ticks: "toListLeft (ticks transformation) = toListLeft transformation"
  apply(induction transformation rule: toListLeft.induct)
  by(auto simp: ticks_help ticks_help2 split: prod.splits)


lemmas all_ticks = tick ticks

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits 


lemma ticks_helper: "\<lbrakk>
  ticksHelper
         (Reverse (Current [] 0 (Stack.push x leftValues) (Stack.size leftValues - Stack.size rightValues)) (Stack.push x leftValues) [] (Stack.size leftValues - Stack.size rightValues),
         Reverse1 (Current [] 0 rightValues (Suc (2 * Stack.size rightValues))) rightValues []) = (left, right)
    \<rbrakk>
       \<Longrightarrow> Big.toList left @ rev (Small.toList right) = x # Stack.toList leftValues @ rev (Stack.toList rightValues)"
proof(induction  
         "(Reverse (Current [] 0 (Stack.push x leftValues) (Stack.size leftValues - Stack.size rightValues)) (Stack.push x leftValues) [] (Stack.size leftValues - Stack.size rightValues)
         , Reverse1 (Current [] 0 rightValues (Suc (2 * Stack.size rightValues))) rightValues [])"
        rule: ticksHelper.induct
        )
  case 1
  then show ?case 
    by(auto simp: push)
next
  case ("2_1" vd)
   then have left: "left = Big.tick (Reverse (Current [] 0 (Stack.push x leftValues) (Stack.size leftValues - Stack.size rightValues)) (Stack.push x leftValues) [] (Stack.size leftValues - Stack.size rightValues))"
     by (metis ticksHelper.simps(2) prod.inject)
   then have right: "right = Small.tick (Reverse1 (Current [] 0 rightValues (Suc (2 * Stack.size rightValues))) rightValues [])"
     by (metis "2_1.hyps" "2_1.prems" ticksHelper.simps(2) old.prod.inject)
   from left right show ?case
     by(auto simp: push split: if_splits)
 qed



lemma test_2_1: "put x current = Current x1 x2 x3 x4 
        \<Longrightarrow> x1 @ Stack.toList x3 = x # Current.toList current"
  apply(induction x current rule: put.induct)
  by auto

lemma small_push: "x # Small.toList small = Small.toList (Small.push x small) "
  apply(induction x small rule: Small.push.induct)
  by(auto simp: Common_Proof.push put)

lemma test_2: "ticksHelper (big, Small.push x small) = (big', small')
           \<Longrightarrow> Small.toList small' = x # Small.toList small"
  by(auto simp: small_push ticks_help2)


lemma test: " \<lbrakk>
    ticksHelper (x1b, x2b) = (x1c, small'); 
    ticksHelper (x1a, x2a) = (x1b, x2b); 
    ticksHelper (x1, x2) = (x1a, x2a);
    ticksHelper (right, Small.push x left) = (x1, x2)\<rbrakk>
       \<Longrightarrow> Small.toList small' = x # Small.toList left"
  by (metis ticks_help2 test_2)

lemma something_1_1: "\<lbrakk>
      ticksHelper (right, Small.push x left) = (Big.state.Common (state.Idle x21a (idle.Idle x1e x2f)), Small.state.Common (state.Idle x21 (idle.Idle x1d x2d)))
    \<rbrakk> \<Longrightarrow> Stack.toList x1d  = x # Small.toList left"
    apply(induction "(right, Small.push x left)" rule: ticksHelper.induct;
        induction x left rule: Small.push.induct;
        induction x1d rule: Stack.toList.induct;
        induction x1e rule: Stack.toList.induct;
        induction right;
        induction x21a arbitrary:  x2d x2f rule: Current.toList.induct;
        induction x21 rule: Current.toList.induct)
                      apply(auto simp: tick split: if_splits current.splits)
  
  sorry

lemma something_1: "\<lbrakk>
      ticksHelper (right, Small.push x left) = (Big.state.Common (state.Idle x21a (idle.Idle x1e x2f)), Small.state.Common (state.Idle x21 (idle.Idle x1d x2d)))
    \<rbrakk> \<Longrightarrow> Stack.toList x1d @ rev (Stack.toList x1e) = x # Small.toList left @ rev (Current.toList x21a)"
  apply(auto simp: something_1_1)
  apply(induction x1e rule: Stack.toList.induct;
        induction x21a rule: Current.toList.induct;
        induction x left rule: Small.push.induct;
        induction right
        )
       apply(auto split: if_splits current.splits)    
    apply(induction x21 arbitrary: x2f x2d; induction x1d  rule: Stack.toList.induct)
  
  sorry

lemma something: " \<lbrakk>
        ticksHelper (x1b, x2b) = (Big.state.Common (state.Idle x21a (idle.Idle x1e x2f)), Small.state.Common (state.Idle x21 (idle.Idle x1d x2d)));
        ticksHelper (x1a, x2a) = (x1b, x2b); 
        ticksHelper (x1, x2) = (x1a, x2a); 
      ticksHelper (right, Small.push x left) = (x1, x2)
    \<rbrakk> \<Longrightarrow> Stack.toList x1d @ rev (Stack.toList x1e) = x # Small.toList left @ rev (Current.toList x21a)"
  apply(induction "(right, Small.push x left)" rule: ticksHelper.induct;
        induction x1d rule: Stack.toList.induct;
        induction x1e rule: Stack.toList.induct;
        induction left arbitrary: x rule: Small.toList.induct)
  (*apply(auto split: current.splits if_splits)*)
  sorry

(*
lemma test1_1_1: "put x r1 = Current r1' r2' r3' r4' \<Longrightarrow> r1' @ Stack.toList r3' = x # Current.toList r1"
  apply(induction r1 rule: Current.toList.induct)
  by auto

lemma test1_1: "
       ticksHelper (Reverse l1 l2 l3 l4) (Reverse1 (put x r1) r2 r3) =
       (Reverse l1' l2' l3' l4', Reverse1 (Current r1' r2' r3' r4') small auxS) \<Longrightarrow>
       r1' @ Stack.toList r3' @ rev (Current.toList l1') = x # Current.toList r1 @ rev (Current.toList l1)"
  apply(induction "Reverse l1 l2 l3 l4" "Reverse1 (put x r1) r2 r3" rule: ticksHelper.induct)
  by(auto simp: test1_1_1 split: if_splits)

lemma test1_2: "\<lbrakk>
    put x current = Current extra added old remained
  \<rbrakk> \<Longrightarrow> extra @ Stack.toList old @ rev (Common.toList (Common.tick common)) = x # Current.toList current @ rev (Common.toList common)"
  apply(induction current rule: Current.toList.induct)
  by(auto simp: tick)

lemma test1_3: "
      ticksHelper (Reverse x1 x2aa x3 x4) (Reverse1 (put xa x1aa) x2 x3aa) = 
      (Big.state.Common x, Reverse1 (Current x1a x2a x3a x4a) small auxS)
       \<Longrightarrow>
      x1a @ Stack.toList x3a @ rev (Common.toList x) = xa # Current.toList x1aa @ rev (Current.toList x1)"
  apply(induction "Reverse x1 x2aa x3 x4" "Reverse1 (put xa x1aa) x2 x3aa" rule: ticksHelper.induct)
  by auto

lemma test1: "\<lbrakk>
  ticksHelper right (Small.push x left) = (big, Reverse1 current small auxS)
  \<rbrakk> \<Longrightarrow> Current.toList current @ rev (Big.toList big) = x # Small.toList left @ rev (Big.toList right)"
  apply(induction left; induction right; induction big; induction current arbitrary: x small auxS)
  by(auto simp: test1_1 test1_2 test1_3 split: if_splits)

lemma test2_1: "\<lbrakk>
  Reverse1 currentS uu auxS = Small.push x left;
  Small.tick right = Reverse1 x11 x12 x13;
  ticksHelper (Reverse currentB big auxB 0) (Small.push x left) = (Reverse v va vb (Suc vd), right)
  \<rbrakk> \<Longrightarrow> Current.toList x11 @ rev (Current.toList v) = x # Small.toList left @ rev (Current.toList currentB)"
  apply(induction "Reverse currentB big auxB 0" "Small.push x left" rule: ticksHelper.induct;
        induction x11 rule: Current.toList.induct;
        induction currentB rule: Current.toList.induct;
        induction left rule: Small.toList.induct;
        induction v arbitrary: x rule: Current.toList.induct)
  by auto

lemma test2: "\<lbrakk>
  ticksHelper x1 x2 = (x1c, Reverse1 x11 x12 x13); 
  ticksHelper right (Small.push x left) = (x1, x2)
  \<rbrakk> \<Longrightarrow> Current.toList x11 @ rev (Big.toList x1c) = x # Small.toList left @ rev (Big.toList right)"
  apply(induction right "Small.push x left" rule: ticksHelper.induct;
        induction x1 x2 arbitrary: x left x11 x12 x13 x1c  rule: ticksHelper.induct)
   apply(auto simp: test2_1 split: if_splits)
  sorry

lemma test: "\<lbrakk>
  ticksHelper x1b x2b = (x1c, Reverse1 x11 x12 x13); 
  ticksHelper x1a x2a = (x1b, x2b); 
  ticksHelper x1 x2 = (x1a, x2a);
  ticksHelper right (Small.push x left) = (x1, x2)
  \<rbrakk> \<Longrightarrow> Current.toList x11 @ rev (Big.toList x1c) = x # Small.toList left @ rev (Big.toList right)"
  apply(auto simp: ticks_help ticks_help2)
(*apply(induction right "Small.push x left" rule: ticksHelper.induct;
        induction x1 x2 rule: ticksHelper.induct;
        induction x1a x2a rule: ticksHelper.induct)*)
  sorry*)

end
