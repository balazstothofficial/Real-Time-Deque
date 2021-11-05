theory Realtime_Deque
  imports Main "HOL-Data_Structures.Queue_Spec"
begin


datatype 'a copyState = 
  Copy 
    (* from *)
    "'a list"
    (* to *)
    "'a list"

datatype 'a dequeEnd =
  DequeEnd
    (* length *)
    nat
    (* values *)
    "'a list"

datatype 'a phase = 
  Initial |
  FirstPhase
    (* remaining steps (Is this really needed?)*)
    nat
    "'a copyState"
    "'a copyState" |
  SecondPhase
    (* aux short *)
    "'a list"
    "'a copyState"
    "'a copyState" |
  ThirdPhase
    "'a copyState"
    "'a copyState" |
  Done "'a dequeEnd" "'a dequeEnd"

datatype 'a transformation =
  Transformation 
  (* smaller *)
  "'a dequeEnd"
  (* bigger *)
  "'a dequeEnd"
  "'a phase"

datatype 'a deque = 
  Empty
| One 'a
| Two 'a 'a
| Three 'a 'a 'a
| Idle
  (* left end *)
  "'a dequeEnd"
  (* right end *)
  "'a dequeEnd"
| Transforming
  (* left end *)
  "'a dequeEnd"
  (* right end *)
  "'a dequeEnd"
  "'a transformation"

datatype "end" = Left | Right

datatype 'a action = Enqueue "end" 'a | Dequeue "end"

fun copy :: "'a copyState \<Rightarrow> 'a copyState" where
  "copy (Copy (x#from) to) = Copy from (x#to)"
| "copy (Copy []       to) = Copy []   to"

fun transform :: "'a transformation \<Rightarrow> 'a transformation" where
  "transform (Transformation shortEnd longEnd phase) = (
    let newPhase = (
       case shortEnd of DequeEnd shortLength shortValues \<Rightarrow>
       case longEnd  of DequeEnd longLength  longValues  \<Rightarrow>
       let k = longLength - 3 * shortLength in (
       case phase of
            Initial \<Rightarrow>
             FirstPhase (shortLength  * 2 + k - 1) (Copy shortValues []) (Copy longValues [])
          | FirstPhase (Suc n) shortCopy longCopy \<Rightarrow> 
             FirstPhase n (copy shortCopy) (copy longCopy)
          | FirstPhase 0 (Copy _ auxShort) (Copy remainderLong auxLong) \<Rightarrow> 
             SecondPhase auxShort (Copy remainderLong []) (Copy auxLong [])
          | SecondPhase auxShort (Copy [] newShort) longCopy \<Rightarrow> 
             ThirdPhase (copy (Copy auxShort newShort)) (copy longCopy)
          | SecondPhase auxShort shortCopy longCopy \<Rightarrow> 
              SecondPhase auxShort (copy shortCopy) (copy longCopy)
          | ThirdPhase (Copy [] newShort) (Copy [] newLong) \<Rightarrow> 
             Done (DequeEnd (shortLength * 2 + 1) newShort)(DequeEnd (shortLength * 2 - 1 + k) newLong)
          | ThirdPhase shortCopy longCopy \<Rightarrow> ThirdPhase (copy shortCopy) (copy longCopy)
          | done \<Rightarrow> done
      )) in Transformation shortEnd longEnd newPhase
  )"

fun transform4 :: "'a transformation \<Rightarrow> 'a transformation" where
  "transform4 x = transform (transform (transform (transform x)))"

fun transform6 :: "'a transformation \<Rightarrow> 'a transformation" where
  "transform6 x = transform ( transform (transform (transform (transform (transform x)))))"


fun check :: "'a dequeEnd \<Rightarrow> 'a dequeEnd \<Rightarrow> 'a deque" where
  "check leftEnd rightEnd = (
    
    case leftEnd of DequeEnd leftLength leftValues \<Rightarrow>
    case rightEnd of DequeEnd rightLength rightValues \<Rightarrow>
    
    if leftLength * 3 < rightLength
    then Transforming leftEnd rightEnd (transform6 (Transformation leftEnd rightEnd Initial))
    else if rightLength * 3 < leftLength
    then Transforming leftEnd rightEnd (transform6 (Transformation rightEnd leftEnd Initial))
    else Idle leftEnd rightEnd
  )"

fun addToCopy :: "'a \<Rightarrow> 'a copyState \<Rightarrow> 'a copyState" where
  "addToCopy x (Copy from to) = Copy (x#from) to"

fun popFromCopy :: "'a copyState \<Rightarrow> 'a copyState" where
  "popFromCopy (Copy (_#from) to) = Copy from to"
| "popFromCopy (Copy [] (_#to)) = Copy [] to"

fun append :: "'a \<Rightarrow> 'a dequeEnd \<Rightarrow> 'a dequeEnd" where
  "append x (DequeEnd l xs) = DequeEnd (Suc l) (x#xs)"

fun pop :: "'a dequeEnd \<Rightarrow> 'a dequeEnd" where
  "pop (DequeEnd (Suc l) (x#xs)) = DequeEnd l xs"

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

| "operate (Three x y z) (Dequeue Left) = Two y z"
| "operate (Three x y z) (Dequeue Right) = Two x y"
| "operate (Three x y z) (Enqueue Left v) = Idle (DequeEnd 2 [v, x]) (DequeEnd 2 [z, y])"
| "operate (Three x y z) (Enqueue Right v) = Idle (DequeEnd 2 [x, y]) (DequeEnd 2 [v, z])"

(* TODO: Would it be good to have the concrete lengths? *)
| "operate (Idle (DequeEnd _ (_#[])) (DequeEnd _ (x#y#z#[]))) (Dequeue Left) = Three z y x" 
| "operate (Idle (DequeEnd _ (_#[])) (DequeEnd _ (y#z#[])))   (Dequeue Left) = Two z y"
| "operate (Idle (DequeEnd _ (_#[])) (DequeEnd _ (z#[])))     (Dequeue Left) = One z"

| "operate (Idle (DequeEnd _ (x#y#z#[])) (DequeEnd _ (_#[]))) (Dequeue Right)  = Three x y z"
| "operate (Idle (DequeEnd _ (y#z#[]))   (DequeEnd _ (_#[]))) (Dequeue Right)  = Two y z"
| "operate (Idle (DequeEnd _ (z#[]))     (DequeEnd _ (_#[]))) (Dequeue Right)  = One z"

| "operate (Idle leftEnd rightEnd) (Enqueue Left x)  = check (append x leftEnd) rightEnd"
| "operate (Idle leftEnd rightEnd) (Enqueue Right x) = check leftEnd (append x rightEnd)"
| "operate (Idle leftEnd rightEnd) (Dequeue Left)    = check (pop leftEnd) rightEnd"
| "operate (Idle leftEnd rightEnd) (Dequeue Right)   = check leftEnd (pop rightEnd)"

| "operate (Transforming leftEnd rightEnd transformation) (Enqueue Left x) = (
    case transform4 transformation of Transformation shortEnd longEnd phase \<Rightarrow>
    case shortEnd of DequeEnd shortLength shortValues \<Rightarrow>
    case leftEnd of DequeEnd leftLength leftValues \<Rightarrow>
      if shortLength = leftLength
      then let newPhase = (
          case phase of
                  Initial \<Rightarrow> Initial
                | FirstPhase steps shortCopy longCopy \<Rightarrow>
                   FirstPhase (Suc steps) (addToCopy x shortCopy) longCopy
                | SecondPhase auxShort shortCopy longCopy \<Rightarrow>
                   SecondPhase (x#auxShort) shortCopy longCopy
                | ThirdPhase shortCopy longCopy \<Rightarrow>
                   ThirdPhase (addToCopy x shortCopy) longCopy
                | Done shortEnd longEnd \<Rightarrow>
                   Done (append x shortEnd) longEnd
          )
          in case newPhase of
                Done shortEnd longEnd 
                  \<Rightarrow> Idle shortEnd longEnd
            | _   \<Rightarrow> Transforming (append x leftEnd) rightEnd (Transformation (append x shortEnd) longEnd newPhase)
      else let newPhase = (
          case phase of
                  Initial \<Rightarrow> Initial
                | FirstPhase steps shortCopy longCopy \<Rightarrow>
                   FirstPhase (Suc steps) shortCopy (addToCopy x longCopy)
                | SecondPhase auxShort shortCopy longCopy \<Rightarrow>
                   SecondPhase auxShort shortCopy (addToCopy x longCopy)
                | ThirdPhase shortCopy longCopy \<Rightarrow>
                   ThirdPhase shortCopy (addToCopy x longCopy)
                | Done shortEnd longEnd \<Rightarrow>
                   Done shortEnd (append x longEnd)
          )
          in case newPhase of
                Done shortEnd longEnd 
                  \<Rightarrow> Idle longEnd shortEnd
            | _   \<Rightarrow> Transforming (append x leftEnd) rightEnd (Transformation shortEnd (append x longEnd) newPhase)
  )"
| "operate (Transforming leftEnd rightEnd transformation) (Enqueue Right x) = (
    case transform4 transformation of Transformation shortEnd longEnd phase \<Rightarrow>
    case shortEnd of DequeEnd shortLength shortValues \<Rightarrow>
    case rightEnd of DequeEnd rightLength rightValues \<Rightarrow>
      if shortLength = rightLength
      then let newPhase = (
          case phase of
                  Initial \<Rightarrow> Initial
                | FirstPhase steps shortCopy longCopy \<Rightarrow>
                   FirstPhase (Suc steps) (addToCopy x shortCopy) longCopy
                | SecondPhase auxShort shortCopy longCopy \<Rightarrow>
                   SecondPhase (x#auxShort) shortCopy longCopy
                | ThirdPhase shortCopy longCopy \<Rightarrow>
                   ThirdPhase (addToCopy x shortCopy) longCopy
                | Done shortEnd longEnd \<Rightarrow>
                   Done (append x shortEnd) longEnd
          )
          in case newPhase of
                Done shortEnd longEnd 
                  \<Rightarrow> Idle longEnd shortEnd
            | _   \<Rightarrow> Transforming leftEnd (append x rightEnd) (Transformation (append x shortEnd) longEnd newPhase)
      else let newPhase = (
          case phase of
                  Initial \<Rightarrow> Initial
                | FirstPhase steps shortCopy longCopy \<Rightarrow>
                   FirstPhase (Suc steps) shortCopy (addToCopy x longCopy)
                | SecondPhase auxShort shortCopy longCopy \<Rightarrow>
                   SecondPhase auxShort shortCopy (addToCopy x longCopy)
                | ThirdPhase shortCopy longCopy \<Rightarrow>
                   ThirdPhase shortCopy (addToCopy x longCopy)
                | Done shortEnd longEnd \<Rightarrow>
                   Done shortEnd (append x longEnd)
          )
          in case newPhase of
                Done shortEnd longEnd 
                  \<Rightarrow> Idle shortEnd longEnd
            | _   \<Rightarrow> Transforming leftEnd (append x rightEnd) (Transformation shortEnd (append x longEnd) newPhase)
  )"
| "operate (Transforming leftEnd rightEnd transformation) (Dequeue Left) = (
    case transform4 transformation of Transformation shortEnd longEnd phase \<Rightarrow>
    case shortEnd of DequeEnd shortLength shortValues \<Rightarrow>
    case leftEnd of DequeEnd leftLength leftValues \<Rightarrow>
      if shortLength = leftLength
      then let newPhase = (
          case phase of
                  Initial \<Rightarrow> Initial
                | FirstPhase steps shortCopy longCopy \<Rightarrow>
                   FirstPhase steps (popFromCopy shortCopy) longCopy
                | SecondPhase (_#auxShort) shortCopy longCopy \<Rightarrow>
                   SecondPhase auxShort shortCopy longCopy
                | ThirdPhase shortCopy longCopy \<Rightarrow>
                   ThirdPhase (popFromCopy shortCopy) longCopy
                | Done shortEnd longEnd \<Rightarrow>
                   Done (pop shortEnd) longEnd
          )
          in case newPhase of
                Done shortEnd longEnd 
                  \<Rightarrow> Idle shortEnd longEnd
            | _   \<Rightarrow> Transforming (pop leftEnd) rightEnd (Transformation (pop shortEnd) longEnd newPhase)
      else let newPhase = (
          case phase of
                  Initial \<Rightarrow> Initial
                | FirstPhase 0 shortCopy longCopy \<Rightarrow>
                   FirstPhase 0 shortCopy (popFromCopy longCopy)
                |  FirstPhase (Suc steps) shortCopy longCopy \<Rightarrow>
                   FirstPhase steps shortCopy (popFromCopy longCopy)
                | SecondPhase auxShort shortCopy longCopy \<Rightarrow>
                   SecondPhase auxShort shortCopy (popFromCopy longCopy)
                | ThirdPhase shortCopy longCopy \<Rightarrow>
                   ThirdPhase shortCopy (popFromCopy longCopy)
                | Done shortEnd longEnd \<Rightarrow>
                   Done shortEnd (pop longEnd)
          )
          in case newPhase of
                Done shortEnd longEnd 
                  \<Rightarrow> Idle longEnd shortEnd
            | _   \<Rightarrow> Transforming (pop leftEnd) rightEnd (Transformation shortEnd (pop longEnd) newPhase)
  )"
| "operate (Transforming leftEnd rightEnd transformation) (Dequeue Right) = (
    case transform4 transformation of Transformation shortEnd longEnd phase \<Rightarrow>
    case shortEnd of DequeEnd shortLength shortValues \<Rightarrow>
    case rightEnd of DequeEnd rightLength rightValues \<Rightarrow>
      if shortLength = rightLength
      then let newPhase = (
          case phase of
                  Initial \<Rightarrow> Initial
                | FirstPhase steps shortCopy longCopy \<Rightarrow>
                   FirstPhase steps (popFromCopy shortCopy) longCopy
                | SecondPhase (_#auxShort) shortCopy longCopy \<Rightarrow>
                   SecondPhase auxShort shortCopy longCopy
                | ThirdPhase shortCopy longCopy \<Rightarrow>
                   ThirdPhase (popFromCopy shortCopy) longCopy
                | Done shortEnd longEnd \<Rightarrow>
                   Done (pop shortEnd) longEnd
          )
           in case newPhase of
                Done shortEnd longEnd 
                  \<Rightarrow> Idle longEnd shortEnd
            | _   \<Rightarrow> Transforming leftEnd (pop rightEnd) (Transformation (pop shortEnd) longEnd newPhase)
      else let newPhase = (
          case phase of
                  Initial \<Rightarrow> Initial
                | FirstPhase 0 shortCopy longCopy \<Rightarrow>
                   FirstPhase 0 shortCopy (popFromCopy longCopy)
                |  FirstPhase (Suc steps) shortCopy longCopy \<Rightarrow>
                   FirstPhase steps shortCopy (popFromCopy longCopy)
                | SecondPhase auxShort shortCopy longCopy \<Rightarrow>
                   SecondPhase auxShort shortCopy (popFromCopy longCopy)
                | ThirdPhase shortCopy longCopy \<Rightarrow>
                   ThirdPhase shortCopy (popFromCopy longCopy)
                | Done shortEnd longEnd \<Rightarrow>
                   Done shortEnd (pop longEnd)
          )
           in case newPhase of
                Done shortEnd longEnd 
                  \<Rightarrow> Idle shortEnd longEnd
            | _   \<Rightarrow> Transforming leftEnd (pop rightEnd) (Transformation shortEnd (pop longEnd) newPhase)
  )"

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
