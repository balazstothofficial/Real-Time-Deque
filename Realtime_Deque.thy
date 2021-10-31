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
    (* right end *)
    "'a dequeEnd" 
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
              Done (DequeEnd (shortLength * 2 + 1) newShort)(DequeEnd (shortLength * 2 - 2 + k) newLong)
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
  "check (ShortDeque (a#b#c#d#[])) = Deque (DequeEnd 2 [a, b]) (DequeEnd 2 [c, d]) None" 
| "check (ShortDeque values      ) = ShortDeque values" 
| "check (Deque leftEnd rightEnd None) = (
  let (shortEnd, longEnd) = sort leftEnd rightEnd in
  case shortEnd of (DequeEnd shortLength shortValues) \<Rightarrow>
  case longEnd  of (DequeEnd longLength longValues) \<Rightarrow>
    if  shortLength * 3 \<ge> longLength 
    then Deque leftEnd rightEnd None 
    else Deque (DequeEnd 0 []) (DequeEnd 0 []) (Some (transformN 6 (Transformation shortEnd longEnd Initial)))
  )"
(* TODO: Right order!! *)
| "check (Deque leftEnd rightEnd (Some (Transformation _ _ (Done newShort newLong)))) =
     Deque newShort newLong None"
| "check (Deque leftEnd rightEnd (Some transformation)) = 
     Deque leftEnd rightEnd (Some (transformN 4 transformation))"

fun append :: "'a \<Rightarrow> 'a dequeEnd \<Rightarrow> 'a dequeEnd" where
  "append x (DequeEnd l xs) = DequeEnd (Suc l) (x#xs)"

fun enqueueLeft :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueLeft x (ShortDeque values) = check (ShortDeque (x#values))"
| "enqueueLeft x (Deque leftEnd rightEnd status) = check (Deque (append x leftEnd) rightEnd status)"

fun enqueueRight :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueRight x (ShortDeque values) = check (ShortDeque (values@[x]))"
| "enqueueRight x (Deque leftEnd rightEnd status) = check (Deque leftEnd (append x rightEnd) status)"

definition empty :: "'a deque" where
  "empty = ShortDeque []"

value "
enqueueLeft 9 (
enqueueLeft 8 (
enqueueLeft 7 (
enqueueLeft 6 (
enqueueLeft 5 (
enqueueLeft 4 (
enqueueLeft 3 (
enqueueLeft 2 (
enqueueLeft (1::nat) (empty)))))))))"

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

end
