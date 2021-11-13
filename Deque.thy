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
  "put element (Current extra added old remained) = Current (element#extra) (added + 1) old remained"

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
  Empty
  | One 'a
  | Two 'a 'a
  | Three 'a 'a 'a 
  | Deque "'a state" "'a state"

definition empty where
  "empty \<equiv> Empty"

fun isEmpty :: "'a deque \<Rightarrow> bool" where
  "isEmpty Empty = True"
| "isEmpty _ = False"

fun swap :: "'a deque \<Rightarrow> 'a deque" where
  "swap Empty = Empty"  
| "swap (One x) = One x"
| "swap (Two x y) = Two y x"
| "swap (Three x y z) = Three z y x"
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

fun toSmall :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a deque" where
  "toSmall []     [] = Empty"

| "toSmall (x#[]) [] = One x"
| "toSmall [] (x#[]) = One x"

| "toSmall (x#[])(y#[]) = Two y x"
| "toSmall (x#y#[]) [] = Two y x"
| "toSmall [] (x#y#[])= Two y x"

| "toSmall [] (x#y#z#[])   = Three z y x"
| "toSmall (x#y#z#[]) []   = Three z y x"
| "toSmall (x#y#[]) (z#[]) = Three z y x"
| "toSmall (x#[]) (y#z#[]) = Three z y x"

fun dequeueLeft' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "dequeueLeft' (One x) = (x, Empty)"
| "dequeueLeft' (Two x y) = (x, One y)"
| "dequeueLeft' (Three x y z) = (x, Two y z)"
| "dequeueLeft' (Deque (Norm left leftLength) (Norm right rightLength)) = (
   let x = first left in
   let left = pop left in
    if 3 * (leftLength - 1) \<ge> rightLength 
    then (x, Deque (Norm left (leftLength - 1)) (Norm right rightLength))
    else if leftLength \<ge> 2
    then let (left, newRight) = sixTicks (RevS1 (Current [] 0 left (2 * leftLength - 1)) left [])
                                         (RevB  (Current [] 0 right (rightLength - leftLength)) right [] (rightLength - leftLength)) 
         in (x, Deque left newRight)
    else case right of Stack r1 r2 \<Rightarrow> (x, toSmall r1 r2)
  )"
| "dequeueLeft' (Deque left right) = (
    let (x, left) = popState left in 
    let (left, right) = fourTicks left right in
      (x, Deque left right)
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
  "enqueueLeft x Empty = One x"
| "enqueueLeft x (One y) = Two x y"
| "enqueueLeft x (Two y z) = Three x y z"
| "enqueueLeft x (Three a b c) = Deque (Norm (Stack [x, a] []) 2) (Norm (Stack [c, b] []) 2)"
| "enqueueLeft x (Deque (Norm left leftLength) (Norm right rightLength)) = (
    let left = push x left in 
      if 3 * rightLength \<ge> Suc leftLength
      then Deque (Norm left (Suc leftLength)) (Norm right rightLength)
      else let (left, right) = sixTicks (RevB  (Current [] 0 left (leftLength - rightLength)) left [] (leftLength - rightLength))
                                              (RevS1 (Current [] 0 right (2 * rightLength + 1)) right [])
            in Deque left right
  )"
| "enqueueLeft x (Deque left right) = (
    let (left, right) = fourTicks (pushState x left) right 
    in Deque left right
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

lemma [simp]:"\<lbrakk>(xa, y) = (case dequeueLeft' (Deque v va) of (x, deque) \<Rightarrow> (x, swap deque))\<rbrakk>
       \<Longrightarrow> size y < Suc (size v + size va)"
  sorry

lemma [simp]: " \<lbrakk>(xa, y) = (case dequeueLeft' (List (rev vb @ [va])) of (x, deque) \<Rightarrow> (x, swap deque))\<rbrakk>
       \<Longrightarrow> size y < Suc (Suc (length vb))"
  sorry

fun listLeft :: "'a deque \<Rightarrow> 'a list" where
  "listLeft Empty = []"
| "listLeft (One x) = [x]"
| "listLeft (Two x y) = [x, y]"
| "listLeft (Three x y z) = [x, y, z]"
| "listLeft deque = (
    let (x, deque) = dequeueLeft' deque in
      x # (listLeft deque)
  )"

fun listRight :: "'a deque \<Rightarrow> 'a list" where
  "listRight Empty = []"
| "listRight (One x) = [x]"
| "listRight (Two x y) = [y, x]"
| "listRight (Three x y z) = [z, y, x]"
| "listRight deque = (
    let (x, deque) = dequeueRight' deque in
      x # (listRight deque)
  )"

fun enqueueLeftAll :: "'a list \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueLeftAll [] deque = deque"
| "enqueueLeftAll (x#xs) deque = enqueueLeftAll xs (enqueueLeft x deque)" 

fun enqueueRightAll :: "'a list \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueRightAll [] deque = deque"
| "enqueueRightAll (x#xs) deque = enqueueRightAll xs (enqueueRight x deque)" 

fun dequeueLeftN :: "nat \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "dequeueLeftN 0 deque = deque"
| "dequeueLeftN (Suc n) deque = dequeueLeftN n (dequeueLeft deque)" 

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
(*fixes invar :: "'q \<Rightarrow> bool"*)
assumes listLeft_empty:     "listLeft empty = []"
assumes listRight_empty:    "listRight empty = []"
assumes list_enqueueLeft:   "listLeft(enqueueLeft x q) = x # listLeft q"
assumes list_enqueueRight:  "listRight(enqueueRight x q) = x # listRight q"
assumes list_dequeueLeft:   "\<not> listLeft q = [] \<Longrightarrow> listLeft(dequeueLeft q) = tl(listLeft q)"
assumes list_dequeueRight:  "\<not> listRight q = [] \<Longrightarrow> listRight(dequeueRight q) = tl(listRight q)"
assumes list_firstLeft:     "\<not> listLeft q = [] \<Longrightarrow> firstLeft q = hd(listLeft q)"
assumes list_firstRight:    "\<not> listRight q = [] \<Longrightarrow> firstRight q = hd(listRight q)"
assumes listLeft_isEmpty:   "isEmpty q = (listLeft q = [])"
assumes listRight_isEmpty:  "isEmpty q = (listRight q = [])"
(*assumes invar_empty:        "invar empty"
assumes invar_enqueueLeft:  "invar q \<Longrightarrow> invar(enqueueLeft x q)"
assumes invar_enqueueRight: "invar q \<Longrightarrow> invar(enqueueRight x q)"
assumes invar_dequeueLeft:  "invar q \<Longrightarrow> invar(dequeueLeft q)"
assumes invar_dequeueRight: "invar q \<Longrightarrow> invar(dequeueRight q)"*)

lemma "listLeft (dequeueLeft (enqueueLeft x deque)) = listLeft deque"
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
  listRight = listRight
proof (standard, goal_cases)
case 1
  then show ?case by(simp add: empty_def)
next
  case 2
  then show ?case 
    by(simp add: empty_def)
next
  case (3 x q)
  then show ?case
    apply(induction q arbitrary: x)
    apply(auto split: prod.splits)
    
    sorry
next
  case (4 x q)
  then show ?case
    apply(induction q arbitrary: x)
    apply (auto split: prod.splits)
    sorry
next
  case (5 q)
  then show ?case 
    apply (auto split: prod.splits)
    apply (induction q)
    by auto
next
  case (6 q)
  then show ?case 
    apply (auto split: prod.splits)
    apply (induction q)
    by auto
next
  case (7 q)
  then show ?case
    apply (induction q)
    by (auto split: prod.splits)
next
  case (8 q)
  then show ?case 
    apply(induction q)
    by(auto split: prod.splits)
next
  case (9 q)
  then show ?case
    apply(induction q)
    by(auto split: prod.splits)
next
  case (10 q)
  then show ?case
    apply(induction q)
    by(auto split: prod.splits)
qed



end