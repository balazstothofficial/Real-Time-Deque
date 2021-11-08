theory Realtime_Deque
  imports Main "HOL-Data_Structures.Queue_Spec"
begin

datatype 'a countedList =
 CountedList
  (* length *)
  nat
  (* values *)
  "'a list"

definition emptyCountedList where
  "emptyCountedList = CountedList 0 []"

datatype 'a copyState = 
 Copy 
  (* remaining steps *)
  nat
  (* from *)
  "'a countedList"
  (* to *)
  "'a countedList"

datatype 'a shortTransformation =
 FirstPhase 
  (* counter popped *)
  nat
  (* extra *)
  "'a countedList"
  (* reverse short end *)
  "'a copyState" |
 SecondPhase
  (* counter popped *)
  nat
  (* extra *)
  "'a countedList"
  (* reversed short end *)
  "'a countedList"
  (* reverse remaining of long end *)
  "'a copyState" |
 ThirdPhase
  (* extra *)
  "'a countedList"
  (* reverse reversed short end onto reversed remaining of long end *)
  "'a copyState" |
 ExtraPhase
  (* reverse extra *)
  "'a copyState"

datatype 'a longTransformation =
 FirstPhase 
  (* counter popped *)
  nat
  (* extra *)
  "'a countedList"
  (* reverse top of long end *)
  "'a copyState" |
 SecondPhase
  (* extra *)
  "'a countedList"
  (* reverse reversed top of long end *)
  "'a copyState" |
 ExtraPhase
  (* reverse extra *)
  "'a copyState"

datatype 'a transformation = 
  Short
    "'a shortTransformation" |
  Long
    "'a longTransformation"

datatype 'a deque = 
  Empty
| One 'a
| Two 'a 'a
| Three 'a 'a 'a
| Idle
  (* left end *)
  "'a countedList"
  (* right end *)
  "'a countedList"
  (*TODO: Would it be good to have "TransformingToLeft" and "TransformingToRight"? *)
| Transforming
  (* left transformation *)
  "'a transformation"
  (* right transformation *)
  "'a transformation"

datatype "end" = Left | Right

datatype 'a action = Enqueue "end" 'a | Dequeue "end"

fun push :: "'a \<Rightarrow> 'a countedList \<Rightarrow> 'a countedList" where
  "push x (CountedList l xs) = CountedList (Suc l) (x#xs)"

fun pop :: "'a countedList \<Rightarrow> 'a countedList" where
  "pop (CountedList (Suc l) (x#xs)) = CountedList l xs"

fun copy :: "'a copyState \<Rightarrow> 'a copyState" where
  "copy (Copy (Suc n) (CountedList (Suc l) (x#from)) to) = Copy n (CountedList l from) (push x to)"
| "copy (Copy  0       from    to)                       = Copy 0 from to"

(* TODO: generalize *)
fun fullCopyOnto :: "'a countedList \<Rightarrow> 'a countedList \<Rightarrow> 'a copyState" where
  "fullCopyOnto (CountedList l xs) other = Copy l (CountedList l xs) other"

fun fullCopyOntoBut :: "nat \<Rightarrow> 'a countedList \<Rightarrow> 'a countedList \<Rightarrow> 'a copyState" where
  "fullCopyOntoBut n (CountedList l xs) other = Copy (l -n) (CountedList l xs) other"

fun fullCopy :: "'a countedList \<Rightarrow> 'a copyState" where
  "fullCopy list = fullCopyOnto list emptyCountedList"

fun fullCopyBut :: "nat \<Rightarrow> 'a countedList \<Rightarrow> 'a copyState" where
  "fullCopyBut n list = fullCopyOntoBut n list emptyCountedList"

(* TODO: Find out how to remove "shortTransformation." *)
(* TODO: What to do with missing cases? *)
fun transform :: "'a shortTransformation \<Rightarrow> 'a longTransformation \<Rightarrow> ('a shortTransformation * 'a longTransformation)" where
  (* TODO: Invariant: short < steps first long phase *)
  "transform (shortTransformation.FirstPhase  poppedShort extraShort (Copy 0 _ reversedShort))              (FirstPhase poppedLong extraLong (Copy 0 remainingLong reversedLong))
     =       (shortTransformation.SecondPhase poppedShort extraShort reversedShort (fullCopy remainingLong), SecondPhase extraLong (fullCopyBut poppedLong reversedLong))"

| "transform (shortTransformation.FirstPhase poppedShort extraShort reverseShort)       (FirstPhase poppedLong extraLong reverseLong)
     =       (shortTransformation.FirstPhase poppedShort extraShort (copy reverseShort), FirstPhase poppedLong extraLong (copy reverseLong))"

| "transform (shortTransformation.SecondPhase poppedShort extraShort reversedShort (Copy 0 _ reversedRemainingLong))              (SecondPhase extraLong reverseLongTop)
     =       (shortTransformation.ThirdPhase  extraShort (copy (fullCopyOntoBut poppedShort reversedShort reversedRemainingLong)), SecondPhase extraLong (copy reverseLongTop))"

| "transform (shortTransformation.SecondPhase poppedShort extraShort reversedShort reverseRemainingLong)       (SecondPhase extraLong reverseLongTop)
     =       (shortTransformation.SecondPhase poppedShort extraShort reversedShort (copy reverseRemainingLong), SecondPhase extraLong (copy reverseLongTop))"

| "transform (shortTransformation.ThirdPhase extraShort (Copy 0 _ newShort))   (SecondPhase extraLong (Copy 0 _ newLong))
     =       (shortTransformation.ExtraPhase (fullCopyOnto extraShort newShort), ExtraPhase (fullCopyOnto extraLong newLong))"

| "transform (shortTransformation.ThirdPhase extraShort reverseNewShort)       (SecondPhase extraLong reverseLongTop)
     =       (shortTransformation.ThirdPhase extraShort (copy reverseNewShort), SecondPhase extraLong (copy reverseLongTop))"

| "transform (shortTransformation.ExtraPhase reverseShortExtra)   (ExtraPhase reverseLongExtra)
     =       (shortTransformation.ExtraPhase (copy reverseShortExtra), ExtraPhase (copy reverseLongExtra))"


fun twice :: "('a \<Rightarrow> 'b \<Rightarrow> ('a * 'b)) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('a * 'b))" where
  "twice f = (\<lambda>a b. let (a', b') = f a b in f a' b')"

definition transformFourTimes where
  "transformFourTimes \<equiv> twice (twice transform)"

definition transformSixTimes where
  "transformSixTimes \<equiv> twice (twice (twice transform))"

fun check' :: "'a countedList \<Rightarrow> 'a countedList \<Rightarrow> ('a shortTransformation * 'a longTransformation)" where
  "check' shortEnd longEnd = (
     case shortEnd of CountedList shortLength shortValues \<Rightarrow>
     case longEnd  of CountedList longLength  longValues \<Rightarrow>
     let k = longLength - 3 * shortLength in
      transformSixTimes
        (shortTransformation.FirstPhase 0 (Copy shortLength                shortEnd  emptyCountedList))
        (                    FirstPhase 0 (Copy (shortLength  * 2 + k - 1) longEnd   emptyCountedList))
  )"

fun check :: "'a countedList \<Rightarrow> 'a countedList \<Rightarrow> 'a deque" where
  "check leftEnd rightEnd = (
    
    case leftEnd of CountedList leftLength leftValues \<Rightarrow>
    case rightEnd of CountedList rightLength rightValues \<Rightarrow>
    
    if leftLength * 3 < rightLength
    then let (short, long) = check' leftEnd rightEnd 
         in Transforming (Short short) (Long long)

    else if rightLength * 3 < leftLength
    then let (short, long) = check' rightEnd leftEnd 
         in Transforming (Long long) (Short short) 

    else Idle leftEnd rightEnd
  )"

(*fun addToCopy :: "'a \<Rightarrow> 'a copyState \<Rightarrow> 'a copyState" where
  "addToCopy x (Copy from to) = Copy (x#from) to"

fun popFromCopy :: "'a copyState \<Rightarrow> 'a copyState" where
  "popFromCopy (Copy (_#from) to) = Copy from to"
| "popFromCopy (Copy [] (_#to)) = Copy [] to"

fun pushToTransformation :: "'a \<Rightarrow> 'a transformation \<Rightarrow> 'a transformation" where
  "pushToTransformation x (Short l xs) = DequeEnd (Suc l) (x#xs)"*)

fun operate :: "'a deque \<Rightarrow> 'a action \<Rightarrow> 'a deque" where
  "operate Empty (Dequeue _)   = Empty"
| "operate Empty (Enqueue _ x) = One x"

| "operate (One _) (Dequeue _)       = Empty"
| "operate (One x) (Enqueue Left y)  = Two y x"
| "operate (One x) (Enqueue Right y) = Two x y"

| "operate (Two x y) (Dequeue Left)    = One y"
| "operate (Two x y) (Dequeue Right)   = One x"
| "operate (Two x y) (Enqueue Left z)  = Three z x y"
| "operate (Two x y) (Enqueue Right z) = Three x y z"

| "operate (Three x y z) (Dequeue Left)    = Two y z"
| "operate (Three x y z) (Dequeue Right)   = Two x y"
| "operate (Three x y z) (Enqueue Left v)  = Idle (CountedList 2 [v, x]) (CountedList 2 [z, y])"
| "operate (Three x y z) (Enqueue Right v) = Idle (CountedList 2 [x, y]) (CountedList 2 [v, z])"

(* TODO: Would it be good to have the concrete lengths? Is it possible? *)
| "operate (Idle (CountedList _ (_#[])) (CountedList _ (x#y#z#[]))) (Dequeue Left) = Three z y x" 
| "operate (Idle (CountedList _ (_#[])) (CountedList _ (y#z#[])))   (Dequeue Left) = Two z y"
| "operate (Idle (CountedList _ (_#[])) (CountedList _ (z#[])))     (Dequeue Left) = One z"

| "operate (Idle (CountedList _ (x#y#z#[])) (CountedList _ (_#[]))) (Dequeue Right)  = Three x y z"
| "operate (Idle (CountedList _ (y#z#[]))   (CountedList _ (_#[]))) (Dequeue Right)  = Two y z"
| "operate (Idle (CountedList _ (z#[]))     (CountedList _ (_#[]))) (Dequeue Right)  = One z"

| "operate (Idle leftEnd rightEnd) (Enqueue Left x)  = check (push x leftEnd) rightEnd"
| "operate (Idle leftEnd rightEnd) (Enqueue Right x) = check leftEnd (push x rightEnd)"
| "operate (Idle leftEnd rightEnd) (Dequeue Left)    = check (pop leftEnd) rightEnd"
| "operate (Idle leftEnd rightEnd) (Dequeue Right)   = check leftEnd (pop rightEnd)"

| "operate (Transforming leftEnd rightEnd) operation = Transforming leftEnd rightEnd"


fun enqueueLeft :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueLeft x deque = operate deque (Enqueue Left x)"

fun enqueueRight :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
   "enqueueRight x deque = operate deque (Enqueue Right x)"

fun dequeueLeft :: "'a deque \<Rightarrow> 'a deque" where
 "dequeueLeft deque = operate deque (Dequeue Left)"

fun dequeueRight :: "'a deque \<Rightarrow> 'a deque" where
 "dequeueRight deque = operate deque (Dequeue Right)"

definition empty :: "'a deque" where
  "empty = Empty"

(*
fun firstLeft :: "'a deque \<Rightarrow> 'a" where
  "firstLeft (One x) = x"
| "firstLeft (Two x _) = x"
| "firstLeft (Three x _ _) = x"
| "firstLeft (Idle (DequeEnd _ (x#_)) _) = x"
| "firstLeft (Transforming (DequeEnd _ (x#_)) _ _) = x"

fun firstRight :: "'a deque \<Rightarrow> 'a" where
  "firstRight (One x) = x"
| "firstRight (Two _ x) = x"
| "firstRight (Three _ _ x) = x"
| "firstRight (Idle _ (DequeEnd _ (x#_)) ) = x"
| "firstRight (Transforming _ (DequeEnd _ (x#_)) _) = x"

fun isEmpty :: "'a deque \<Rightarrow> bool" where
  "isEmpty Empty = True"
| "isEmpty _ = False"

lemma addOne: "enqueueLeft x deque \<noteq> Empty"
  apply (induction deque arbitrary: x)
  by (auto split: dequeEnd.splits transformation.splits phase.splits) 

fun listLeft :: "'a deque \<Rightarrow> 'a list" where
  "listLeft Empty = []"
| "listLeft (One x) = [x]"
| "listLeft (Two x y) = [x, y]"
| "listLeft (Three x y z) = [x, y, z]"
| "listLeft (Idle (DequeEnd _ left) (DequeEnd _ right)) = left @ (rev right)"
| "listLeft (Transforming (DequeEnd _ left) (DequeEnd _ right) _) = left @ (rev right)"

fun invar :: "'a deque \<Rightarrow> bool" where
  "invar (Idle (DequeEnd _ left) (DequeEnd _ right)) = (left \<noteq> [] \<and> right  \<noteq> [])"
| "invar (Transforming (DequeEnd _ left) (DequeEnd _ right) (Transformation _ _
    (Done (DequeEnd _ short) (DequeEnd _ long)))) = (left \<noteq> [] \<and> right  \<noteq> [] \<and> short \<noteq> [] \<and> long  \<noteq> [])"
| "invar (Transforming (DequeEnd _ left) (DequeEnd _ right) _) = (left \<noteq> [] \<and> right  \<noteq> [])"
| "invar _ = True"


locale Deque =
fixes empty :: "'q"
fixes enqueueLeft :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes enqueueRight :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes firstLeft :: "'q \<Rightarrow> 'a"
fixes firstRight :: "'q \<Rightarrow> 'a"
fixes dequeueLeft :: "'q \<Rightarrow> 'q"
fixes dequeueRight :: "'q \<Rightarrow> 'q"
fixes isEmpty :: "'q \<Rightarrow> bool"
fixes list :: "'q \<Rightarrow> 'a list"
fixes invar :: "'q \<Rightarrow> bool"
assumes list_empty:         "list empty = []"
assumes list_enqueueLeft:   "invar q \<Longrightarrow> list(enqueueLeft x q) = x # list q"
assumes list_enqueueRight:  "invar q \<Longrightarrow> list(enqueueRight x q) = list q @ [x]"
assumes list_dequeueLeft:   "invar q \<Longrightarrow> list(dequeueLeft q) = tl(list q)"
assumes list_dequeueRight:  "invar q \<Longrightarrow> list(dequeueRight q) = butlast(list q)"
assumes list_firstLeft:     "invar q \<Longrightarrow> \<not> list q = [] \<Longrightarrow> firstLeft q = hd(list q)"
assumes list_firstRight:    "invar q \<Longrightarrow> \<not> list q = [] \<Longrightarrow> firstRight q = last(list q)"
assumes list_isEmpty:       "invar q \<Longrightarrow> isEmpty q = (list q = [])"
assumes invar_empty:        "invar empty"
assumes invar_enqueueLeft:  "invar q \<Longrightarrow> invar(enqueueLeft x q)"
assumes invar_enqueueRight: "invar q \<Longrightarrow> invar(enqueueRight x q)"
assumes invar_dequeueLeft:  "invar q \<Longrightarrow> invar(dequeueLeft q)"
assumes invar_dequeueRight: "invar q \<Longrightarrow> invar(dequeueRight q)"

interpretation LeftDequeSide: Deque where
  empty    = empty    and
  enqueueLeft = enqueueLeft and
  enqueueRight = enqueueRight and
  firstLeft = firstLeft and
  firstRight = firstRight and
  dequeueLeft = dequeueLeft and
  dequeueRight = dequeueRight and
  isEmpty = isEmpty and
  list = listLeft and
  invar = invar
proof (standard, goal_cases)
case 1
then show ?case by (simp add: empty_def)
next
case (2 q x)
  then show ?case 
    apply (induction q arbitrary: x) 
    apply (auto split: dequeEnd.splits)
       apply (metis append.elims append_Cons listLeft.simps(5))
    apply (metis append.elims append_Cons listLeft.simps(5))
    apply (metis append.elims append_Cons listLeft.simps(5))
    apply(auto split: transformation.splits dequeEnd.splits phase.splits)
    
             apply (metis append_Cons dequeEnd.exhaust listLeft.simps(6))
    apply (metis append_Cons dequeEnd.exhaust listLeft.simps(6))
    apply (metis append_Cons dequeEnd.exhaust listLeft.simps(6))
    apply (metis append_Cons dequeEnd.exhaust listLeft.simps(6))
    apply (metis append_Cons dequeEnd.exhaust listLeft.simps(6))
    apply (metis append_Cons dequeEnd.exhaust listLeft.simps(6))
    apply (metis append_Cons dequeEnd.exhaust listLeft.simps(6))
      apply (metis append_Cons dequeEnd.exhaust listLeft.simps(6))
    nitpick
    subgoal sorry
    nitpick
    sorry
next
  case (3 q x)
  then show ?case
    apply(induction q arbitrary: x)
         apply (auto split: dequeEnd.splits)
    sorry
next
case (4 q)
  then show ?case
    apply(induction q)
         apply(auto split: transformation.splits dequeEnd.splits phase.splits)    
      sorry
next
  case (5 q)
  then show ?case 
      apply(induction q)
         apply(auto split: transformation.splits dequeEnd.splits phase.splits)
      sorry
next
  case (6 q)
  then show ?case
    apply(induction q)
         apply auto
    sorry
next
  case (7 q)
  then show ?case
    apply (induction q) apply auto
    apply (metis append_assoc dequeEnd.exhaust firstRight.simps(4) invar.simps(1) last_snoc list.exhaust listLeft.simps(5) rev.simps(2))
    by (smt (verit) Nil_is_rev_conv deque.distinct(10) deque.distinct(18) deque.distinct(24) deque.distinct(28) deque.distinct(30) deque.inject(5) dequeEnd.inject firstRight.elims invar.elims(2) last_appendR last_rev list.sel(1) listLeft.elims)
next
  case (8 q)
  then show ?case 
    apply (induction q) apply auto
    using listLeft.elims apply force
    sorry
next
  case 9
  then show ?case by(auto simp: empty_def)
next
  case (10 q x)
  then show ?case
    apply(induction q arbitrary: x) 
    sorry
next
  case (11 q x)
  then show ?case apply(induction q arbitrary: x) apply auto sorry
next
  case (12 q)
  then show ?case apply(induction q) apply auto sorry
next
  case (13 q)
  then show ?case apply(induction q) apply auto sorry
qed


*)
    
value "
enqueueRight 3 (
enqueueRight 2 (
enqueueRight (1::nat) (empty)))"


value "
enqueueRight 9 (
enqueueRight 8 (
enqueueRight 7 (
enqueueRight 6 (
enqueueRight 5 (
enqueueRight 4 (
enqueueRight 3 (
enqueueRight 2 (
enqueueRight (1::nat) (empty)))))))))"

value "
enqueueRight 10 (
enqueueRight 9 (
enqueueRight 8 (
enqueueRight 7 (
enqueueRight 6 (
enqueueRight 5 (
enqueueRight 4 (
enqueueRight 3 (
enqueueRight 2 (
enqueueRight (1::nat) (empty))))))))))"

value "
enqueueRight 11 (
enqueueRight 10 (
enqueueRight 9 (
enqueueRight 8 (
enqueueRight 7 (
enqueueRight 6 (
enqueueRight 5 (
enqueueRight 4 (
enqueueRight 3 (
enqueueRight 2 (
enqueueRight (1::nat) (empty)))))))))))"

value "
enqueueRight 14 (
enqueueRight 13 (
enqueueRight 12 (
enqueueRight 11 (
enqueueRight 10 (
enqueueRight 9 (
enqueueRight 8 (
enqueueRight 7 (
enqueueRight 6 (
enqueueRight 5 (
enqueueRight 4 (
enqueueRight 3 (
enqueueRight 2 (
enqueueRight (1::nat) (empty))))))))))))))"


value "
enqueueLeft 5 (
enqueueLeft 4 (
enqueueLeft 3 (
enqueueLeft 2 (
enqueueLeft (1::nat) (empty)))))"


value "
enqueueLeft 8 (
enqueueLeft 7 (
enqueueLeft 6 (
enqueueLeft 5 (
enqueueLeft 4 (
enqueueLeft 3 (
enqueueLeft 2 (
enqueueLeft (1::nat) (empty))))))))"

value "
enqueueLeft 10 (
enqueueLeft 9 (
enqueueLeft 8 (
enqueueLeft 7 (
enqueueLeft 6 (
enqueueLeft 5 (
enqueueLeft 4 (
enqueueLeft 3 (
enqueueLeft 2 (
enqueueLeft (1::nat) (empty))))))))))"

value "
enqueueLeft 11 (
enqueueLeft 10 (
enqueueLeft 9 (
enqueueLeft 8 (
enqueueLeft 7 (
enqueueLeft 6 (
enqueueLeft 5 (
enqueueLeft 4 (
enqueueLeft 3 (
enqueueLeft 2 (
enqueueLeft (1::nat) (empty)))))))))))"

value "
enqueueLeft 13 (
enqueueLeft 12 (
enqueueLeft 11 (
enqueueLeft 10 (
enqueueLeft 9 (
enqueueLeft 8 (
enqueueLeft 7 (
enqueueLeft 6 (
enqueueLeft 5 (
enqueueLeft 4 (
enqueueLeft 3 (
enqueueLeft 2 (
enqueueLeft (1::nat) (empty)))))))))))))"

value "
enqueueLeft 17 (
enqueueLeft 16 (
enqueueLeft 15 (
enqueueLeft 14 (
enqueueRight (-14) (
enqueueRight (-13) (
enqueueRight (-12) (
enqueueRight (-11) (
enqueueRight (-10) (
enqueueRight (-9) (
enqueueRight (-8) (
enqueueRight (-7) (
enqueueLeft 13 (
enqueueLeft 12 (
enqueueLeft 11 (
enqueueLeft 10 (
enqueueLeft 9 (
enqueueLeft 8 (
enqueueLeft 7 (
enqueueLeft 6 (
enqueueLeft 5 (
enqueueLeft 4 (
enqueueLeft 3 (
enqueueLeft 2 (
enqueueLeft (1::int) (
empty)))))))))))))))))))))))))"


end
