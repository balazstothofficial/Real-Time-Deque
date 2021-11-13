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
  then show ?case
    by (simp add: empty_def)
next
case 2
  then show ?case 
    by (simp add: empty_def) 
next
  case (3 q x)
  then show ?case 
    proof (induction q arbitrary: x)
      case Empty
      then show ?case by simp 
    next
      case (One x)
      then show ?case by simp
    next
      case (Two x y)
      then show ?case by simp
    next
      case (Three x y z)
      then show ?case by auto
    next
      case (Deque left right)
      then show ?case
      proof (induction left arbitrary: x)
        case (Norm leftValues leftSize)
        then show ?case
        proof(induction right arbitrary: x)
          case (Norm rightValues rightSize)
          then show ?case 
            apply (auto simp: push Let_def split: prod.splits)
            sorry
        next
          case (RevB x1 x2 x3 x4)
          then show ?case sorry
        next
          case (RevS1 x1 x2 x3)
          then show ?case sorry
        next
          case (RevS2 x1 x2 x3 x4 x5)
          then show ?case sorry
        next
          case (Copy x1 x2 x3 x4)
          then show ?case sorry
        qed
      next
        case (RevB x1 x2 x3 x4)
        then show ?case sorry
      next
        case (RevS1 x1 x2 x3)
        then show ?case sorry
      next
        case (RevS2 x1 x2 x3 x4 x5)
        then show ?case sorry
      next
        case (Copy x1 x2 x3 x4)
        then show ?case sorry
      qed
    qed
next
  case (4 q x)
  then show ?case
  proof (induction q arbitrary: x)
      case Empty
      then show ?case by auto
    next
      case (One x)
      then show ?case by auto
    next
      case (Two x y)
      then show ?case by auto
    next
      case (Three x y z)
      then show ?case by auto
    next
      case (Deque left right)
      then show ?case sorry
    qed
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
    case (Deque left right)
    then show ?case 
    proof(induction left)
      case (Norm leftValues leftLength)
      then show ?case 
      proof(induction right arbitrary: leftValues leftValues)
        case (Norm rightValues rightLength)
        then show ?case
          (*apply(auto simp: Let_def pop not_empty split: prod.splits stack.splits)*)
          sorry
        next
          case (RevB x1 x2 x3 x4)
          then show ?case sorry
        next
          case (RevS1 x1 x2 x3)
          then show ?case sorry
        next
          case (RevS2 x1 x2 x3 x4 x5)
          then show ?case sorry
        next
          case (Copy x1 x2 x3 x4)
          then show ?case sorry
        qed        
    next
      case (RevB x1 x2 x3 x4)
      then show ?case sorry
    next
      case (RevS1 x1 x2 x3)
      then show ?case sorry
    next
      case (RevS2 x1 x2 x3 x4 x5)
      then show ?case sorry
    next
      case (Copy x1 x2 x3 x4)
      then show ?case sorry
    qed  
  qed
next
  case (6 q)
  then show ?case sorry
next
  case (7 q)
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
    case (Deque left right)
    then show ?case 
      apply(induction left; induction right)
      (*apply(auto simp: Let_def first head not_empty not_empty_2 empty split: prod.splits stack.splits)*)
      sorry
  qed
next
  case (8 q)
  then show ?case sorry
next
  case (9 q)
  then show ?case 
  proof induction
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
    case (Deque left right)
    then show ?case 
  
      apply auto sorry
  qed 
next
  case (10 q)
  then show ?case sorry
next
  case 11
  then show ?case 
    by (simp add: empty_def)
next
  case (12 q x)
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
  case (Deque left right)
  then show ?case
    sorry
  qed
next
  case (13 q x)
  then show ?case sorry
next
  case (14 q)
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
  case (Deque left right)
  then show ?case 
    apply(induction left; induction right)
    apply (auto simp: Let_def split: stack.splits prod.splits)
    sorry
  qed
next
  case (15 q)
  then show ?case sorry
qed

end