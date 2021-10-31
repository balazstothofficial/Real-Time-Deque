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
  Done "'a dequeEnd" "'a dequeEnd"

datatype 'a transformation =
  Transformation 
  (* smaller *)
  "'a dequeEnd"
  (* bigger *)
  "'a dequeEnd"
  "'a phase"

datatype 'a deque = 
  Deque
    (* left end *)
    "'a dequeEnd"
    (* left extra list *)
    "'a list"
    (* right end *)
    "'a dequeEnd" 
    (* right extra list *)
    "'a list"
    (* status *)
    "'a transformation option"
| ShortDeque
    (* less than 3 values *)
    "'a list"

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
          | SecondPhase _ (Copy [] newShort) (Copy [] newLong) \<Rightarrow> 
              Done (DequeEnd (shortLength * 2 + 1) newShort)(DequeEnd (shortLength * 2 - 1 + k) newLong)
          | SecondPhase auxShort (Copy [] newShort) longCopy \<Rightarrow> 
             SecondPhase auxShort (copy (Copy auxShort newShort)) (copy longCopy)
          | SecondPhase auxShort shortCopy longCopy \<Rightarrow> 
              SecondPhase auxShort (copy shortCopy) (copy longCopy)
          | done \<Rightarrow> done
      )) in Transformation shortEnd longEnd newPhase
  )"


fun transformN :: "nat \<Rightarrow> 'a transformation \<Rightarrow> 'a transformation" where
  "transformN 0 transformation = transformation"
| "transformN (Suc n) transformation = transformN n (transform transformation)"


fun sort :: "'a dequeEnd \<Rightarrow> 'a dequeEnd \<Rightarrow> ('a dequeEnd * 'a dequeEnd)" where
  "sort (DequeEnd leftLength left) (DequeEnd rightLength right) = (
  if leftLength < rightLength
  then ((DequeEnd leftLength left), (DequeEnd rightLength right))
  else ((DequeEnd rightLength right), (DequeEnd leftLength left)))"

fun check :: "'a deque \<Rightarrow> 'a deque" where
  "check (ShortDeque (a#b#c#d#[])) = Deque (DequeEnd 2 [a, b]) [] (DequeEnd 2 [d, c]) [] None" 
| "check (ShortDeque values      ) = ShortDeque values" 
| "check (Deque leftEnd _ rightEnd _ None) = (
    let (shortEnd, longEnd) = sort leftEnd rightEnd in
    case shortEnd of DequeEnd shortLength shortValues \<Rightarrow>
    case longEnd  of DequeEnd longLength longValues \<Rightarrow>
      if  shortLength * 3 \<ge> longLength 
      then Deque leftEnd [] rightEnd [] None 
      else Deque leftEnd [] rightEnd [] (Some (transformN 6 (Transformation shortEnd longEnd Initial)))
  )"
(* TODO: Extra list is not real-time! With Type-Class?*)
| "check (Deque leftEnd leftExtra rightEnd rightExtra (Some (Transformation _ _ (Done newShort newLong)))) = (
    case leftEnd of DequeEnd leftLength _ \<Rightarrow>
    case rightEnd of DequeEnd rightLength _ \<Rightarrow>
    case newShort of DequeEnd shortLength shortValues \<Rightarrow>
    case newLong of DequeEnd longLength longValues \<Rightarrow>
      if leftLength \<le> rightLength 
      then Deque (DequeEnd (length leftExtra + shortLength) (leftExtra@shortValues)) [] (DequeEnd (length rightExtra + longLength) (rightExtra@longValues))  [] None 
      else Deque (DequeEnd (length leftExtra + longLength)  (leftExtra@longValues))  [] (DequeEnd (length rightExtra + shortLength) (rightExtra@shortValues)) [] None
  )"
| "check (Deque leftEnd leftExtra rightEnd rightExtra (Some transformation)) = 
     Deque leftEnd leftExtra rightEnd rightExtra (Some (transformN 4 transformation))"

fun append :: "'a \<Rightarrow> 'a dequeEnd \<Rightarrow> 'a dequeEnd" where
  "append x (DequeEnd l xs) = DequeEnd (Suc l) (x#xs)"

fun pop :: "'a dequeEnd \<Rightarrow> 'a dequeEnd" where
  "pop (DequeEnd (Suc l) (x#xs)) = DequeEnd l xs"

fun enqueueLeft :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueLeft x (ShortDeque values) = check (ShortDeque (x#values))"
| "enqueueLeft x (Deque leftEnd leftExtra rightEnd rightExtra None) = 
    check (Deque (append x leftEnd) leftExtra rightEnd rightExtra None)"
| "enqueueLeft x (Deque leftEnd leftExtra rightEnd rightExtra status) = 
    check (Deque leftEnd (x#leftExtra) rightEnd rightExtra status)"

fun enqueueRight :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueRight x (ShortDeque values) = check (ShortDeque (values@[x]))"
| "enqueueRight x (Deque leftEnd leftExtra rightEnd rightExtra None) = 
    check (Deque leftEnd leftExtra (append x rightEnd) rightExtra None)"
| "enqueueRight x (Deque leftEnd leftExtra rightEnd rightExtra status) = 
    check (Deque leftEnd leftExtra rightEnd (x#rightExtra) status)"

fun firstLeft :: "'a deque \<Rightarrow> 'a" where
  "firstLeft (ShortDeque (x#_)) = x"
| "firstLeft (Deque (DequeEnd _ (x#_)) _ _ _ None) = x"
| "firstLeft (Deque _ (x#_) _ _ _) = x"
| "firstLeft (Deque (DequeEnd _ (x#_)) [] _ _ _) = x"

fun firstRight :: "'a deque \<Rightarrow> 'a" where
  "firstRight (ShortDeque (x#[])) = x"
| "firstRight (ShortDeque (_#x#[])) = x"
| "firstRight (ShortDeque (_#_#x#[])) = x"
| "firstRight (Deque _ _ (DequeEnd _ (x#_)) _ None) = x"
| "firstRight (Deque _ _ _(x#_) _) = x"
| "firstRight (Deque _ _ (DequeEnd _ (x#_)) [] _) = x"

(* TODO: Dequeue during transformation counter! *)
fun dequeueLeft :: "'a deque \<Rightarrow> 'a deque" where
  "dequeueLeft (ShortDeque []) = ShortDeque []"
| "dequeueLeft (ShortDeque (x#xs)) = ShortDeque xs"
| "dequeueLeft (Deque leftEnd (x#xs) rightEnd rightExtra status) =
     check (Deque leftEnd (x#xs) rightEnd rightExtra status)"
| "dequeueLeft (Deque leftEnd [] rightEnd rightExtra status) =
     check (Deque (pop leftEnd) [] rightEnd rightExtra status)"

(* TODO: Dequeue during transformation counter! *)
fun dequeueRight :: "'a deque \<Rightarrow> 'a deque" where
  "dequeueRight (ShortDeque []) = ShortDeque []"
| "dequeueRight (ShortDeque (x#[])) = ShortDeque []"
| "dequeueRight (ShortDeque (x#_#[])) = ShortDeque [x]"
| "dequeueRight (ShortDeque (x#y#_#[])) = ShortDeque [x, y]"
| "dequeueRight (Deque leftEnd leftExtra rightEnd (x#xs) status) =
     check (Deque leftEnd leftExtra rightEnd xs status)"
| "dequeueRight (Deque leftEnd leftExtra rightEnd [] status) =
     check (Deque leftEnd leftExtra (pop rightEnd) [] status)"

definition empty :: "'a deque" where
  "empty = ShortDeque []"

value "
enqueueRight 5 (
enqueueRight 4 (
enqueueRight 3 (
enqueueRight 2 (
enqueueRight (1::nat) (empty)))))"


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
enqueueRight (1::nat) (empty))))))))))))"


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
enqueueLeft (1::nat) (empty))))))))))))"

value "
enqueueRight (-14) (
enqueueRight (-13) (
enqueueRight (-12) (
enqueueRight (-11) (
enqueueRight (-10) (
dequeueLeft (
enqueueRight (-9) (
dequeueLeft (
dequeueLeft (
dequeueLeft (
dequeueLeft (
dequeueLeft (
enqueueRight (-8) (
enqueueRight (-7) (
enqueueLeft 13 (
enqueueLeft 12 (
enqueueRight (-6) (
enqueueLeft 11 (
enqueueLeft 10 (
enqueueLeft 9 (
enqueueLeft 8 (
enqueueLeft 7 (
enqueueLeft 6 (
enqueueLeft 5 (
enqueueRight (-5) (
enqueueLeft 4 (
enqueueLeft 3 (
enqueueLeft 2 (
enqueueLeft 1 (
enqueueRight (-4) (
enqueueRight (-3) (
enqueueRight (-2) (
enqueueRight (-1) (
enqueueRight (0::int) (empty))))))))))))))))))))))))))))))))))"


end
