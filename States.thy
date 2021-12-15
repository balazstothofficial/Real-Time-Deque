theory States 
  imports Big Small
begin

type_synonym 'a states = "'a Big.state * 'a Small.state"

fun tick :: "'a states \<Rightarrow> 'a states" where
  "tick (Reverse currentB big auxB 0, Reverse1 currentS _ auxS) =
    (Big.tick (Reverse currentB big auxB 0), Reverse2 currentS auxS big [] 0)"
| "tick (left, right) = (Big.tick left, Small.tick right)"

definition invariant :: "'a states \<Rightarrow> bool" where
  "invariant states \<longleftrightarrow> (
    let (big, small) = states in
      Big.invariant big 
   \<and>  Small.invariant small
   \<and> (
      case states of 
        (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow>
             Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
      | (_, Reverse1 _ _ _) \<Rightarrow> False
      | _ \<Rightarrow> True
    )
  )"

fun toList :: "'a states \<Rightarrow> ('a list * 'a list)" where
  "toList (Reverse currentB big auxB count, small) = ([], [])"

fun remainingSteps :: "'a states \<Rightarrow> nat" where
  "remainingSteps (big, small) = max 
    (Big.remainingSteps big) 
    (case small of 
       Small.Common common \<Rightarrow> Common.remainingSteps common
     | Reverse2 (Current _ _ _ remaining) _ big _ _ \<Rightarrow> remaining + Stack.size big + 2
     | Reverse1 (Current _ _ _ remaining) _ _ \<Rightarrow>
         case big of
           Reverse currentB big auxB count \<Rightarrow> Stack.size big + remaining + 3
    )"

lemma helper_1:  "States.invariant (Reverse v va vb vc, small) \<Longrightarrow>
       (States.tick (Reverse v va vb vc, small), Reverse v va vb vc, small) \<in> measure States.remainingSteps"
proof(induction "(Reverse v va vb vc, small)" rule: tick.induct)
  case (1 currentS uu auxS)
  then show ?case
    by(auto split: current.splits)
next
  case ("2_1" vd)
  then show ?case 
    apply(auto simp: Let_def invariant_def split: current.splits Small.state.splits)
    apply (meson lessI max.strict_coboundedI1)
        apply(induction va rule: Stack.pop.induct)
          apply auto
    subgoal for x1 x3 x4 x22a x23a x1b x3b x24a
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for x1 x3 x4 x22a x23a x1b x3b x24a
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for x1 x3 x4 x22a x23a x1b x3b x24a
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    apply(auto simp: max_def)
    subgoal for x1 x3 x4 x3a
      apply(induction x3a)
      by(auto split: current.splits)
    subgoal for x1 x3 x4 x3a
      apply(induction x3a)
      by(auto split: current.splits)
    .
next
  case ("2_3" v va vb vc vd)
  then show ?case 
    apply(auto simp: invariant_def split: current.splits)
              apply (metis helper max.strict_coboundedI1 max_Suc_Suc)
             apply (metis helper max.strict_coboundedI1 max_Suc_Suc)
            apply(induction vb rule: Stack.pop.induct)
              apply auto
         apply (metis Stack.isEmpty.elims(2) Stack.size.simps gen_length_def length_code list.size(3) neq0_conv)
        apply (metis helper max.strict_coboundedI1 max_Suc_Suc)
       apply (metis helper max.strict_coboundedI1 max_Suc_Suc)
    apply (metis helper max.strict_coboundedI1 max_Suc_Suc)
     apply(induction vb rule: Stack.pop.induct)
       apply auto
    apply(induction vb rule: Stack.pop.induct)
    by auto
next
  case ("2_4" common)
  then show ?case 
    apply(auto simp: invariant_def split: current.splits)
     apply (meson helper max.strict_coboundedI1)
    apply(induction common rule: Common.tick.induct)
    by(auto split: current.splits)
qed

lemma helper_2_1: " \<lbrakk>va = Current x1c (List.length x1c) x3c x4b;
        small = Reverse2 (Current x1b (List.length x1b) x3b (List.length x24a)) x22a x23a x24a (List.length x24a);
        Stack.toList x3c =
        take (Stack.size x3c) (drop (List.length vb + List.length vc - x4b) (rev vb)) @ take (Stack.size x3c + List.length vc - x4b) vc;
        vd = List.length vc; x4b \<le> List.length vb + List.length vc; Stack.toList x3b = []; \<not> Stack.isEmpty x23a; x4b \<le> Suc (List.length vc);
        List.length vc < x4b; Stack.size x23a = 0; Stack.size x3b = 0\<rbrakk>
       \<Longrightarrow> Suc (List.length x24a + Stack.size (Stack.pop x23a)) < max (x4b - List.length vc) (Suc (List.length x24a))"
  apply(induction x23a rule: Stack.pop.induct)
  by auto

lemma helper_2_2: " \<lbrakk>va = Current x1c (List.length x1c) x3c x4b;
        small = Reverse2 (Current x1b (List.length x1b) x3b (List.length x24a)) x22a x23a x24a (List.length x24a);
        Stack.toList x3c =
        take (Stack.size x3c) (drop (List.length vb + List.length vc - x4b) (rev vb)) @ take (Stack.size x3c + List.length vc - x4b) vc;
        vd = List.length vc; x4b \<le> List.length vb + List.length vc; Stack.toList x3b = []; \<not> Stack.isEmpty x23a; \<not> x4b \<le> Suc (List.length vc);
        Stack.size x23a = 0; Stack.size x3b = 0\<rbrakk>
       \<Longrightarrow> Suc (List.length x24a + Stack.size (Stack.pop x23a)) < max (x4b - List.length vc) (Suc (List.length x24a))"
  apply(induction x23a rule: Stack.pop.induct)
  by auto 


lemma helper_2: " States.invariant (Big.state.Common (Copy va vb vc vd), small) \<Longrightarrow>
       (States.tick (Big.state.Common (Copy va vb vc vd), small), Big.state.Common (Copy va vb vc vd), small) \<in> measure States.remainingSteps"
proof(induction "(Big.state.Common (Copy va vb vc vd), small)" rule: tick.induct)
  case "2_2"
  then show ?case 
    apply(auto simp: invariant_def split: current.splits Small.state.splits)
    subgoal for x22a x23a x1b x3b x24a x1c x3c x4b
      apply(induction x23a)
      by auto
    subgoal for x22a x23a x1b x3b x24a x1c x3c x4b
      apply(induction x23a)
      by auto
    subgoal for x22a x23a x1b x3b x24a x1c x3c x4b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for x22a x23a x1b x3b x24a x1c x3c x4b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for x22a x23a x1b x3b x24a x1c x3c x4b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for x22a x23a x1b x3b x24a x1c x3c x4b
      apply(induction x23a rule: Stack.pop.induct)
      by auto
    subgoal for x3a x1a x3b x4a
      apply(auto simp: max_def)
       apply(induction x3a)
        apply(auto split: current.splits)
      apply(induction x3a)
      by(auto split: current.splits)
    subgoal for x3a x1a x3b x4a
      apply(auto simp: max_def)
       apply(induction x3a)
        apply(auto split: current.splits)
      apply(induction x3a)
      by(auto split: current.splits)
    .
next
  case ("2_3" v va vb vc vd)
  then show ?case
    apply(induction vb rule: Stack.pop.induct)
    by(auto split: current.splits)
next
  case ("2_4" v)
  then show ?case
    apply(induction v)
    by(auto simp: invariant_def split: current.splits)
qed

lemma helper_3: "\<lbrakk>States.invariant states; (x, y) = states; x = Big.state.Common x2; x2 = state.Idle x21 x22; y = Reverse1 x11 x12 x13\<rbrakk>
       \<Longrightarrow> (States.tick states, states) \<in> measure States.remainingSteps"
  apply(induction states rule: tick.induct)
      apply blast+
  by(auto simp: invariant_def)


function (sequential) terminateTicks :: "'a states \<Rightarrow> 'a states option" where
  "terminateTicks states = (
    if invariant states 
    then case states of
      (Big.Common (Idle _ _), Small.Common (Idle _ _)) \<Rightarrow> Some states
    | _ \<Rightarrow>  terminateTicks (tick states)
    else None
  )"
  by pat_completeness auto
  termination
    apply (relation "measure remainingSteps")
         apply simp
    using helper_1 apply blast
    using helper_2 apply blast
    using helper_3 apply blast
     apply(auto simp: invariant_def split: idle.splits current.splits stack.splits)
      apply (metis Stack.isEmpty.simps(1) Stack.size.elims add_eq_0_iff_both_eq_0 length_0_conv)
    subgoal for x21 x22a x23 x2 x1b x2a x3a
      apply(induction x23 rule: Stack.pop.induct)
      by auto
    subgoal for x21 x22a x23 x2 x1b x2a x3a
      apply(induction x23 rule: Stack.pop.induct)
      by auto
    .

end
