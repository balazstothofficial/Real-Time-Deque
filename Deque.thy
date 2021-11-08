theory Deque
  imports Stack
begin

datatype 'a current = Current "'a list" nat "'a stack" nat

datatype 'a state =
  Norm "'a stack" nat |
  RevB "'a current" "'a stack" "'a list" nat |
  RevS1 "'a current" "'a stack" "'a list" |
  RevS2 "'a current" "'a list" "'a stack" "'a list" nat |
  Copy "'a current" "'a list" "'a list" nat

fun put :: "'a \<Rightarrow> 'a current \<Rightarrow> 'a current" where
  "put element (Current extra added old remained) = Current (element#extra) (Suc added) old remained"

fun get :: "'a current \<Rightarrow> 'a * 'a current" where
  "get (Current [] added old remained)     = (first old, Current [] added (pop old) (remained - 1))"
| "get (Current (x#xs) added old remained) = (x, Current xs (added - 1) old remained)"

fun top :: "'a current \<Rightarrow> 'a" where
  "top current = (let (element, _) = get current in element)"

fun bottom :: "'a current \<Rightarrow> 'a current" where
  "bottom current = (let (_, bottom) = get current in bottom)"

fun normalize :: "'a state \<Rightarrow> 'a state" where
  "normalize (Copy current old new moved) = (
      case current of Current extra added _ remained \<Rightarrow> 
      if moved = remained
      then Norm (Stack extra new) (added + moved)
      else Copy current old new moved
  )"
| "normalize state = state"

fun tick :: "'a state \<Rightarrow> 'a state" where
  "tick state = (
    case state of
         Norm _ _ \<Rightarrow> state
       | RevB current big auxB count \<Rightarrow> RevB current (pop big) ((first big)#auxB) (count - 1)
       | RevS1 current small auxS \<Rightarrow> 
          if isEmpty small 
          then state 
          else RevS1 current (pop small) ((first small)#auxS)
       | RevS2 current auxS big newS count \<Rightarrow>
          if isEmpty big
          then normalize (Copy current auxS newS count)
          else RevS2 current auxS (pop big) ((first big)#newS) (count + 1)
       | Copy current aux new moved \<Rightarrow> case current of Current _ _ _ remained \<Rightarrow>
          if moved < remained
          then normalize (Copy current (tl aux) ((hd aux)#new) (moved + 1))
          else normalize state
  )"

fun ticks :: "'a state \<Rightarrow> 'a state \<Rightarrow> 'a state * 'a state" where
  "ticks (RevB currentB big auxB 0) (RevS1 currentS _ auxS) =
    (normalize (Copy currentB auxB [] 0), RevS2 currentS auxS big [] 0)"
| "ticks (RevS1 currentS _ auxS) (RevB currentB big auxB 0) =
    (RevS2 currentS auxS big [] 0, normalize (Copy currentB auxB [] 0))"
| "ticks left right = (tick left, tick right)"

fun twice :: "('a \<Rightarrow> 'b \<Rightarrow> ('a * 'b)) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('a * 'b))" where
  "twice f = (\<lambda>a b. let (a', b') = f a b in f a' b')"

definition fourTicks where
  "fourTicks \<equiv> twice (twice ticks)"

definition sixTicks where
  "sixTicks \<equiv> twice (twice (twice ticks))"

datatype side = Left | Right

datatype 'a deque =
   List "'a list"
| Deque "'a state" "'a state"

definition empty where
  "empty \<equiv> List []"

fun isEmpty :: "'a deque \<Rightarrow> bool" where
  "isEmpty (List []) = True"
| "isEmpty _ = False"

fun swap :: "'a deque \<Rightarrow> 'a deque" where
  "swap (List xs) = List (rev xs)"
| "swap (Deque left right) = Deque left right"

fun popState :: "'a state \<Rightarrow> 'a * 'a state" where
  "popState (Norm a b)        = (first a, Norm (pop a) (b - 1))"
| "popState (RevB a b c d)    = (top a,   RevB (bottom a) b c d)"
| "popState (RevS1 a b c)     = (top a,   RevS1 (bottom a) b c)"
| "popState (RevS2 a b c d e) = (top a,   RevS2 (bottom a) b c d e)"
| "popState (Copy a b c d)    = (top a,   Copy (bottom a) b c d)"

fun pushState :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "pushState x (Norm a b)        = Norm  (push x a) (Suc b)"
| "pushState x (RevB a b c d)    = RevB  (put x a) b c d"
| "pushState x (RevS1 a b c)     = RevS1 (put x a) b c"
| "pushState x (RevS2 a b c d e) = RevS2 (put x a) b c d e"
| "pushState x (Copy a b c d)    = Copy  (put x a) b c d"

fun dequeueLeft' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "dequeueLeft' (List (x#xs)) = (x, List xs)"
| "dequeueLeft' (Deque (Norm L l) (Norm R r)) = (
   let head = first L in
   let tail = pop L in
    if 3 * (l - 1) \<ge> r 
    then (head, Deque (Norm tail (l - 1)) (Norm R r))
    else if l \<ge> 2
    then let (newLeft, newRight) = sixTicks (RevS1 (Current [] 0 L (2 * l - 1)) L [])
                                            (RevB  (Current [] 0 R (r - l)) R [] (r - l)) 
         in (head, Deque newLeft newRight)
    else case R of Stack r1 r2 \<Rightarrow> (head, List (rev (r1@r2)))
  )"
| "dequeueLeft' (Deque left right) = (
    let (x, L) = popState left in 
    let (newLeft, newRight) = fourTicks left right in
      (x, Deque newLeft newRight)
  )"

fun dequeueRight' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "dequeueRight' deque = (
    let (x, deque) = dequeueLeft' (swap deque) 
    in (x, swap deque)
  )"

fun dequeueLeft :: "'a deque \<Rightarrow> 'a deque" where
  "dequeueLeft deque = (let (_, deque) = dequeueLeft' deque in deque)"

fun dequeueRight :: "'a deque \<Rightarrow> 'a deque" where
  "dequeueRight deque = (let (_, deque) = dequeueRight' deque in deque)"

fun firstLeft :: "'a deque \<Rightarrow> 'a" where
  "firstLeft deque = (let (x, _) = dequeueLeft' deque in x)" 

fun firstRight :: "'a deque \<Rightarrow> 'a" where
  "firstRight deque = (let (x, _) = dequeueRight' deque in x)" 

fun enqueueLeft :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueLeft x (List xs) = (
    if length xs \<le> 2
    then List (x#xs)
    else Deque (Norm (Stack [x, hd xs] []) 2) (Norm (Stack [hd (tl (tl xs)), hd (tl xs)] []) 2)
  )"
| "enqueueLeft x (Deque (Norm L l) (Norm R r)) = (
    let L = push x L in 
    if 3 * r \<ge> Suc l
    then Deque (Norm L (Suc l)) (Norm R r)
    else let (newLeft, newRight) = sixTicks (RevB  (Current [] 0 L (l - r)) L [] (r - l))
                                            (RevS1 (Current [] 0 R (2 * r + 1)) R []) 
         in Deque newLeft newRight
  )"
| "enqueueLeft x (Deque left right) = (
    let (newLeft, newRight) = fourTicks (pushState x left) right 
    in Deque newLeft newRight
  )"

fun enqueueRight :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueRight x deque = (
    let deque = enqueueLeft x (swap deque) 
    in swap deque
  )"

fun invar :: "'a deque \<Rightarrow> bool" where
  "invar _ = True"

lemma [simp]:"\<lbrakk>(x, deque') = dequeueLeft' (Deque left right)\<rbrakk>
       \<Longrightarrow> size deque' < Suc (size left + size right)"
  apply (
        induction deque' arbitrary: x; 
        induction left; 
        induction right; 
        auto simp: Let_def split: if_splits prod.splits stack.splits
         )
  sorry

lemma [simp]:"\<lbrakk>(a, b) = (case dequeueLeft' (Deque v va) of (x, deque) \<Rightarrow> (x, swap deque));
        (xa, y) = (case dequeueLeft' (Deque v va) of (x, deque) \<Rightarrow> (x, swap deque))\<rbrakk>
       \<Longrightarrow> size y < Suc (size v + size va)"
  sorry

lemma [simp]: " \<lbrakk>(a, b) = (case dequeueLeft' (List (rev vb @ [va])) of (x, deque) \<Rightarrow> (x, swap deque));
        (xa, y) = (case dequeueLeft' (List (rev vb @ [va])) of (x, deque) \<Rightarrow> (x, swap deque))\<rbrakk>
       \<Longrightarrow> size y < Suc (Suc (length vb))"
  sorry

fun listLeft :: "'a deque \<Rightarrow> 'a list" where
  "listLeft (List []) = []"
| "listLeft deque = (
    let (x, deque) = dequeueLeft' deque in
      x # (listLeft deque)
  )"

fun listRight :: "'a deque \<Rightarrow> 'a list" where
  "listRight (List []) = []"
| "listRight deque = (
    let (x, deque) = dequeueRight' deque in
      x # (listRight deque)
  )"


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
fixes invar :: "'q \<Rightarrow> bool"
assumes listLeft_empty:     "listLeft empty = []"
assumes listRight_empty:    "listRight empty = []"
assumes list_enqueueLeft:   "invar q \<Longrightarrow> listLeft(enqueueLeft x q) = x # listLeft q"
assumes list_enqueueRight:  "invar q \<Longrightarrow> listRight(enqueueRight x q) = x # listRight q"
assumes list_dequeueLeft:   "invar q \<Longrightarrow> listLeft(dequeueLeft q) = tl(listLeft q)"
assumes list_dequeueRight:  "invar q \<Longrightarrow> listRight(dequeueRight q) = tl(listRight q)"
assumes list_firstLeft:     "invar q \<Longrightarrow> \<not> listLeft q = [] \<Longrightarrow> firstLeft q = hd(listLeft q)"
assumes list_firstRight:    "invar q \<Longrightarrow> \<not> listRight q = [] \<Longrightarrow> firstRight q = hd(listRight q)"
assumes listLeft_isEmpty:   "invar q \<Longrightarrow> isEmpty q = (listLeft q = [])"
assumes listRight_isEmpty:  "invar q \<Longrightarrow> isEmpty q = (listRight q = [])"
assumes invar_empty:        "invar empty"
assumes invar_enqueueLeft:  "invar q \<Longrightarrow> invar(enqueueLeft x q)"
assumes invar_enqueueRight: "invar q \<Longrightarrow> invar(enqueueRight x q)"
assumes invar_dequeueLeft:  "invar q \<Longrightarrow> invar(dequeueLeft q)"
assumes invar_dequeueRight: "invar q \<Longrightarrow> invar(dequeueRight q)"

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
  invar = invar
proof (standard, goal_cases)
case 1
  then show ?case by(simp add: empty_def)
next
  case 2
  then show ?case 
    by(simp add: empty_def)
next
  case (3 q x)
  then show ?case
    apply(induction q arbitrary: x)
    apply(auto split: prod.splits)
    sorry
next
  case (4 q x)
  then show ?case
    apply(induction q arbitrary: x)
    apply(auto split: prod.splits)
    sorry
next
  case (5 q)
  then show ?case 
    apply(induction q)
    apply(auto split: prod.splits)
    sorry
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
then show ?case sorry
qed



end
