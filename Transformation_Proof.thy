theory Transformation_Proof
  imports Transformation Small_Proof Big_Proof Stack_Proof
begin

lemmas tick = Small_Proof.tick Big_Proof.tick Common_Proof.tick

lemma ticks: "toListLeft (ticks transformation) = toListLeft transformation"
proof(induction transformation rule: toListLeft.induct)
  case (1 small big)
  
  have "\<And>x1 x2. 
        ticksHelper big small = (x1, x2) \<Longrightarrow>
        Small.toList small @ rev (Big.toList big) = Small.toList x2 @ rev (Big.toList x1)"
    apply(induction big small rule: ticksHelper.induct)
    by(auto simp: tick split: current.splits)

  then show ?case by (auto split: prod.splits)
next
  case (2 big small)

  have "\<And>x1 x2. 
        ticksHelper big small = (x1, x2) \<Longrightarrow>
        Big.toList big @ rev (Small.toList small) = Big.toList x1 @ rev (Small.toList x2)"
    apply(induction big small rule: ticksHelper.induct)
    by(auto simp: tick split: current.splits)

  then show ?case
    by(auto split: prod.splits)
qed

lemma ticks_helper: "\<lbrakk>
  ticksHelper
         (Reverse (Current [] 0 (Stack.push x leftValues) (Stack.size leftValues - Stack.size rightValues)) (Stack.push x leftValues) [] (Stack.size leftValues - Stack.size rightValues))
         (Reverse1 (Current [] 0 rightValues (Suc (2 * Stack.size rightValues))) rightValues []) = (left, right)
    \<rbrakk>
       \<Longrightarrow> Big.toList left @ rev (Small.toList right) = x # Stack.toList leftValues @ rev (Stack.toList rightValues)"
proof(induction  
         "Reverse (Current [] 0 (Stack.push x leftValues) (Stack.size leftValues - Stack.size rightValues)) (Stack.push x leftValues) [] (Stack.size leftValues - Stack.size rightValues)"
         "Reverse1 (Current [] 0 rightValues (Suc (2 * Stack.size rightValues))) rightValues []"
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

lemmas all_ticks = tick ticks ticks_helper

lemmas state_splits = idle.splits Common.state.splits Small.state.splits Big.state.splits 

end
