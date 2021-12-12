theory States 
  imports Big Small
begin

type_synonym 'a states = "'a Big.state * 'a Small.state"

fun tick :: "'a states \<Rightarrow> 'a states" where
  "tick (Reverse currentB big auxB 0, Reverse1 currentS _ auxS) =
    (Big.tick (Reverse currentB big auxB 0), Reverse2 currentS auxS big [] 0)"
| "tick (left, right) = (Big.tick left, Small.tick right)"

fun invariant :: "'a states \<Rightarrow> bool" where
  "invariant (big, small) \<longleftrightarrow> 
    Big.invariant big 
  \<and> Small.invariant small
  \<and> (
    case (big, small) of 
      (Reverse _ big _ count, Reverse1 (Current _ _ old remained) small _) \<Rightarrow>
           Stack.size big - count = remained - Stack.size old \<and> count \<ge> Stack.size small
    | (_, Reverse1 _ _ _) \<Rightarrow> False
    | _ \<Rightarrow> True
)"

fun remainingSteps :: "'a states \<Rightarrow> nat" where
  "remainingSteps (big, small) = max 
    (Big.remainingSteps big) 
    (case small of 
       Small.Common common \<Rightarrow> Common.remainingSteps common
     | Reverse2 (Current _ _ _ remaining) _ big _ _ \<Rightarrow> remaining + Stack.size big + 1
     | Reverse1 (Current _ _ _ remaining) _ _ \<Rightarrow>
         case big of
           Reverse currentB big auxB count \<Rightarrow> Stack.size big + remaining + 2
    )"

lemma helper_1_1: "\<lbrakk>v = Current x1 (List.length x1) x3 x4;
        small = Reverse2 (Current x1b (List.length x1b) x3b (List.length x24a)) x22a x23a x24a (List.length x24a); vc = Suc vd;
        Stack.toList x3 = drop (Suc (List.length vb + vd) - x4) (rev vb) @ take (Suc vd) (Stack.toList va); x4 - Suc vd \<le> List.length vb;
        Suc vd \<le> x4; Suc vd \<le> Stack.size va; Stack.toList x3b = []; \<not> Stack.isEmpty x23a; Stack.size x23a = 0; Stack.size x3b = 0\<rbrakk>
       \<Longrightarrow> List.length x24a + Stack.size (Stack.pop x23a) < max (Suc (vd + x4)) (List.length x24a)"
  apply(induction x23a rule: Stack.pop.induct)
  by auto

lemma helper_1_2: "\<lbrakk>v = Current x1 (List.length x1) x3 x4;
        small = Reverse2 (Current x1b (List.length x1b) x3b (List.length x24a + Stack.size x23a + Stack.size x3b)) x22a x23a x24a (List.length x24a);
        vc = Suc vd; Stack.toList x3 = drop (Suc (List.length vb + vd) - x4) (rev vb) @ take (Suc vd) (Stack.toList va);
        x4 - Suc vd \<le> List.length vb; Suc vd \<le> x4; Suc vd \<le> Stack.size va; Stack.toList x3b = drop (List.length x22a - Stack.size x3b) (rev x22a);
        Stack.size x3b \<le> List.length x22a; \<not> Stack.isEmpty x23a; 0 < Stack.size x23a\<rbrakk>
       \<Longrightarrow> List.length x24a + Stack.size x23a + Stack.size x3b + Stack.size (Stack.pop x23a)
            < max (Suc (vd + x4)) (List.length x24a + Stack.size x23a + Stack.size x3b + Stack.size x23a)"
  apply(induction x23a rule: Stack.pop.induct)
  by auto

lemma helper_1_3: "\<lbrakk>v = Current x1 (List.length x1) x3 x4;
        small = Reverse2 (Current x1b (List.length x1b) x3b (List.length x24a + Stack.size x23a + Stack.size x3b)) x22a x23a x24a (List.length x24a);
        vc = Suc vd; Stack.toList x3 = drop (Suc (List.length vb + vd) - x4) (rev vb) @ take (Suc vd) (Stack.toList va);
        x4 - Suc vd \<le> List.length vb; Suc vd \<le> x4; Suc vd \<le> Stack.size va; Stack.toList x3b = drop (List.length x22a - Stack.size x3b) (rev x22a);
        Stack.size x3b \<le> List.length x22a; \<not> Stack.isEmpty x23a; 0 < Stack.size x3b\<rbrakk>
       \<Longrightarrow> List.length x24a + Stack.size x23a + Stack.size x3b + Stack.size (Stack.pop x23a)
            < max (Suc (vd + x4)) (List.length x24a + Stack.size x23a + Stack.size x3b + Stack.size x23a)"
  apply(induction x23a rule: Stack.pop.induct)
  by auto

lemma helper_1_4: " \<lbrakk>v = Current x1 (List.length x1) x3 x4; small = Small.state.Common x3a; vc = Suc vd;
        Stack.toList x3 = drop (Suc (List.length vb + vd) - x4) (rev vb) @ take (Suc vd) (Stack.toList va); x4 - Suc vd \<le> List.length vb;
        Suc vd \<le> x4; Suc vd \<le> Stack.size va; Common.invariant x3a\<rbrakk>
       \<Longrightarrow> Common.remainingSteps (Common.tick x3a) < max (Suc (Suc (vd + x4))) (Common.remainingSteps x3a)"
  apply(induction x3a rule: Common.tick.induct)
  by(auto split: current.splits)

lemma helper_1:  "States.invariant (Reverse v va vb vc, small) \<Longrightarrow>
       (States.tick (Reverse v va vb vc, small), Reverse v va vb vc, small) \<in> measure States.remainingSteps"
proof(induction "(Reverse v va vb vc, small)" rule: tick.induct)
  case (1 currentS uu auxS)
  then show ?case
    by(auto split: current.splits)
next
  case ("2_1" vd)
  then show ?case 
    apply(auto simp: Let_def split: current.splits Small.state.splits)
         apply (meson lessI max_less_iff_conj)
        apply(induction va rule: Stack.pop.induct)
          apply auto
    apply (meson helper_1_1)
      apply (meson helper_1_2)
     apply (meson helper_1_3)
    by (meson helper_1_4)
next
  case ("2_3" v va vb vc vd)
  then show ?case 
    apply(auto split: current.splits)
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
    apply(auto split: current.splits)
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
    apply(auto split: current.splits Small.state.splits)
    using helper_2_1 apply blast
    using helper_2_2 apply blast
    sorry
next
  case ("2_3" v va vb vc vd)
  then show ?case sorry
next
  case ("2_4" v)
  then show ?case sorry
qed
  
function (sequential) terminateTicks :: "'a states \<Rightarrow> ('a idle * 'a idle) option" where
  "terminateTicks (Big.Common (Idle _ big), Small.Common (Idle _ small)) = Some (big, small)"
| "terminateTicks (big, small) = (
    if invariant (big, small) 
    then terminateTicks (tick (big, small)) 
    else None
  )"
  by pat_completeness auto
  termination
    apply (relation "measure remainingSteps")
    apply simp
    using helper_1 apply blast
    using helper_2 apply blast
    sorry

end
