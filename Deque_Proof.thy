theory Deque_Proof
  imports Deque Stack_Proof
begin

locale Deque =
fixes empty :: "'q"
fixes enqueueLeft :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes enqueueRight :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes firstLeft :: "'q \<Rightarrow> 'a"
fixes firstRight :: "'q \<Rightarrow> 'a"
fixes dequeueLeft :: "'q \<Rightarrow> 'q"
fixes dequeueRight :: "'q \<Rightarrow> 'q"
fixes isEmpty :: "'q \<Rightarrow> bool"
fixes listLeft :: "'q \<Rightarrow> 'a list"
fixes listRight :: "'q \<Rightarrow> 'a list"
fixes invariant :: "'q \<Rightarrow> bool"
assumes listLeft_empty:     "listLeft empty = []"
assumes listRight_empty:    "listRight empty = []"
assumes list_enqueueLeft:   "invariant q \<Longrightarrow> listLeft(enqueueLeft x q) = x # listLeft q"
assumes list_enqueueRight:  "invariant q \<Longrightarrow> listRight(enqueueRight x q) = x # listRight q"
assumes list_dequeueLeft:   "invariant q \<Longrightarrow> \<not> listLeft q = [] \<Longrightarrow> listLeft(dequeueLeft q) = tl(listLeft q)"
assumes list_dequeueRight:  "invariant q \<Longrightarrow> \<not> listRight q = [] \<Longrightarrow> listRight(dequeueRight q) = tl(listRight q)"
assumes list_firstLeft:     "invariant q \<Longrightarrow> \<not> listLeft q = [] \<Longrightarrow> firstLeft q = hd(listLeft q)"
assumes list_firstRight:    "invariant q \<Longrightarrow> \<not> listRight q = [] \<Longrightarrow> firstRight q = hd(listRight q)"
assumes listLeft_isEmpty:   "invariant q \<Longrightarrow> isEmpty q = (listLeft q = [])"
assumes listRight_isEmpty:  "invariant q \<Longrightarrow> isEmpty q = (listRight q = [])"
assumes invariant_empty:        "invariant empty"
assumes invariant_enqueueLeft:  "invariant q \<Longrightarrow> invariant(enqueueLeft x q)"
assumes invariant_enqueueRight: "invariant q \<Longrightarrow> invariant(enqueueRight x q)"
assumes invariant_dequeueLeft:  "invariant q \<Longrightarrow> \<not> isEmpty q  \<Longrightarrow> invariant(dequeueLeft q)"
assumes invariant_dequeueRight: "invariant q \<Longrightarrow> \<not> isEmpty q  \<Longrightarrow> invariant(dequeueRight q)"

lemma head: "xs \<noteq> [] \<Longrightarrow> hd xs = hd (xs @ ys)"
  apply (induction xs arbitrary: ys)
  by auto


lemma test: "\<lbrakk>leftLength = length ll + length lr; rightLength = length rl + length rr; 2 \<le> length ll + length lr;
        State2.ticks x1d x2d = (Reverse x11 x12 x13 x14, Reverse1 x11a x12a x13a); State2.ticks x1c x2c = (x1d, x2d);
        State2.ticks x1b x2b = (x1c, x2c); State2.ticks x1a x2a = (x1b, x2b); State2.ticks x1 x2 = (x1a, x2a);
        State2.ticks
         (Reverse (Current [] 0 (Stack (x # ll) lr) (length ll + length lr - (length rl + length rr))) (Stack (x # ll) lr) []
           (length ll + length lr - (length rl + length rr)))
         (Reverse1 (Current [] 0 (Stack rl rr) (Suc (2 * length rl + 2 * length rr))) (Stack rl rr) []) =
        (x1, x2);
        \<not> Suc (length ll + length lr) \<le> 3 * length rl + 3 * length rr\<rbrakk>
       \<Longrightarrow> Current.toList x11 @ rev (Current.toList x11a) = x # ll @ lr @ rev rr @ rev rl"
  sorry

lemma test3: 
  assumes "2 \<le> length x1 + length x2"  
          "Suc (length x1 + length x2) \<le> 3 * rightLength"
          "rightLength \<le> 2"
        shows "Deque.invariant (swap (toSmallDeque x1 x2))"
proof-
  from assms have "rightLength = 0 \<or> rightLength = 1 \<or> rightLength = 2"
    by auto
  
  then show ?thesis 
  proof
    assume "rightLength = 0"
    with assms show ?thesis
      by auto
  next
    assume "rightLength = 1 \<or> rightLength = 2"
    then have "rightLength = 1 \<or> rightLength = 2" .
    then show ?thesis
    proof
      assume "rightLength = 1"
      with assms show ?thesis
        apply(induction x1 x2 rule: toSmallDeque.induct)
        by auto
    next
      assume "rightLength = 2"
      with assms show ?thesis
        apply(induction x1 x2 rule: toSmallDeque.induct)
        apply auto
      sorry
    qed
  qed
qed

lemma testing: " \<lbrakk>
  State2.ticks left3 right3 = (left4, Reverse1 current' small' auxS'); 
  State2.ticks left2 right2 = (left3, right3); 
  State2.ticks left1 right1 = (left2, right2);
  State2.ticks (Reverse currentl big auxB count) (Reverse1 (put x currentr) small auxS) = (left1, right1)
\<rbrakk> \<Longrightarrow> 
  Current.toList current' @ rev (bToList left4 False) = x # Current.toList currentr @ rev (Current.toList currentl)"
  apply(induction current' arbitrary: x small' auxS' rule: Current.toList.induct )
  apply auto
  apply(induction currentr rule: Current.toList.induct)
  apply auto
  apply(induction currentl rule: Current.toList.induct)
  apply auto
  apply(induction left4)
   apply auto
   apply(induction left3)
    apply auto
   apply(induction right3)
     apply auto    
  apply(induction left2)
    apply auto
   apply(induction right2)
      apply auto
   apply(induction left1)
    apply auto
   apply(induction right1 arbitrary: big auxB count small auxS)
  apply auto
  sorry


interpretation RealtimeDeque: Deque where
  empty    = empty    and
  enqueueLeft = enqueueLeft and
  enqueueRight = enqueueRight and
  firstLeft = firstLeft and
  firstRight = firstRight and
  dequeueLeft = dequeueLeft and
  dequeueRight = dequeueRight and
  isEmpty = isEmpty and
  listLeft = listLeft and
  listRight = listRight and
  invariant = invariant
proof (standard, goal_cases)
  case 1
  then show ?case by (simp add: empty_def)
next
  case 2
  then show ?case by (simp add: empty_def)
next
  case (3 q x)
  then show ?case
  proof(induction q arbitrary: x)
    case Empty
    then show ?case by auto
  next
    case (One x)
    then show ?case by auto
  next
    case (Two x1 x2a)
    then show ?case by auto
  next
    case (Three x1 x2a x3)
    then show ?case by auto
  next
    case (Idle left right)
    then show ?case 
    proof(induction left)
      case (Idle leftValues leftLength)
      then show ?case
      proof(induction right)
        case (Idle rightValues rightLength)
        then show ?case 
        proof(induction leftValues)
          case (Stack ll lr)
          then show ?case 
          proof(induction rightValues)
            case (Stack rl rr)
            then show ?case 
              (* apply(auto simp: Let_def split: prod.splits stateS.splits stateB.splits) *)
              sorry
          qed
        qed
      qed
    qed
  next
    case (Transforming t x)
    then show ?case 
    proof(induction t arbitrary: x)
      case (Left left right)
      then show ?case 
      proof(induction left)
        case (Reverse1 currentl small auxS)
        then show ?case
        proof(induction right)
          case (Reverse currentr big auxB count)
          then show ?case
            apply(auto simp: Let_def split: prod.splits stateS.splits stateB.splits)
            sorry
        next
          case (Common x)
          then show ?case sorry
        qed
      next
        case (Reverse2 x1 x2 x3a x4 x5)
        then show ?case sorry
      next
        case (Common x)
        then show ?case sorry
      qed
    next
      case (Right x1 x2)
      then show ?case sorry
    qed
  qed
next
case (4 q x)
  then show ?case
    sorry
next
  case (5 q)
  then show ?case
  proof(induction q)
  case Empty
    then show ?case by auto
  next
    case (One x)
    then show ?case by auto
  next
    case (Two x1 x2a)
    then show ?case by auto
  next
    case (Three x1 x2a x3)
    then show ?case by auto
  next
    case (Idle left right)
    then show ?case
    proof(induction left)
      case (Idle stackl l)
      then show ?case
      proof(induction right)
        case (Idle stackr r)
        then show ?case 
        proof(induction stackl arbitrary: l)
          case (Stack ll lr)
          then show ?case
          proof(induction stackr arbitrary: r)
            case (Stack rl rr)
            then show ?case
              apply(cases ll; cases lr; cases rl; cases rr)
              subgoal 
                by auto
              subgoal
                apply auto
                sorry
       
              sorry 
          qed
        qed
      qed
    qed
  next
    case (Transforming x)
    then show ?case sorry
  qed 
next
  case (6 q)
  then show ?case sorry
next
  case (7 q)
  then show ?case sorry
next
  case (8 q)
  then show ?case sorry
next
  case (9 q)
  then show ?case sorry
next
  case (10 q)
  then show ?case sorry
next
  case 11
  then show ?case sorry
next
  case (12 q x)
  then show ?case sorry
next
  case (13 q x)
  then show ?case sorry
next
  case (14 q)
  then show ?case sorry
next
  case (15 q)
  then show ?case
  proof(induction q)
    case Empty
    then show ?case by auto
    next
    case (One x)
    then show ?case by auto
    next
      case (Two x1 x2a)
      then show ?case by auto
    next
      case (Three x1 x2a x3)
      then show ?case by auto
    next
      case (Idle left right)
      then show ?case 
      proof(induction left)
        case (Idle leftValues leftLength)
        then show ?case
        proof(induction right)
          case (Idle rightValues rightLength)
          then show ?case
            apply(auto simp: Let_def pop size_pop not_empty)
                   apply(auto simp: test3 split: prod.splits stack.splits)
            sorry
        qed
      qed
    next
      case (Transforming x)
      then show ?case sorry
    qed
  qed

   


end