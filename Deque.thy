theory Deque
  imports State
begin

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
| "swap (Deque left right) = Deque right left"

fun toSmallDeque :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a deque" where
  "toSmallDeque []     [] = Empty"

| "toSmallDeque (x#[]) [] = One x"
| "toSmallDeque [] (x#[]) = One x"

| "toSmallDeque (x#[])(y#[]) = Two y x"
| "toSmallDeque (x#y#[]) [] = Two y x"
| "toSmallDeque [] (x#y#[])= Two y x"

| "toSmallDeque [] (x#y#z#[])   = Three z y x"
| "toSmallDeque (x#y#z#[]) []   = Three z y x"
| "toSmallDeque (x#y#[]) (z#[]) = Three z y x"
| "toSmallDeque (x#[]) (y#z#[]) = Three z y x"

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
    then 
        let left = RevS1 (Current [] 0 left (2 * leftLength - 1)) left [] in
        let right = RevB (Current [] 0 right (rightLength - leftLength)) right [] (rightLength - leftLength) in
        let (left, right) = sixTicks left right
        in (x, Deque left right)
    else case right of Stack r1 r2 \<Rightarrow> (x, toSmallDeque r1 r2)
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
      else 
      let left = RevB   (Current [] 0 left (leftLength - rightLength)) left [] (leftLength - rightLength) in
      let right = RevS1 (Current [] 0 right (2 * rightLength + 1)) right [] in
      let (left, right) = sixTicks left right
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

fun invariant :: "'a deque \<Rightarrow> bool" where
  "invariant Empty = True"
| "invariant (One _) = True"
| "invariant (Two _ _) = True"
| "invariant (Three _ _ _) = True"
| "invariant (Deque (Norm left leftLength) (Norm right rightLength)) = (
   size left = leftLength \<and>
   size right = rightLength \<and>
  (leftLength \<ge> 2 \<or> rightLength \<ge> 2) \<and>
   (3 * rightLength \<ge> Suc leftLength \<or> 3 * leftLength \<ge> Suc rightLength)
)"
| "invariant _ = True"

fun listLeft :: "'a deque \<Rightarrow> 'a list" where
  "listLeft Empty = []"
| "listLeft (One x) = [x]"
| "listLeft (Two x y) = [x, y]"
| "listLeft (Three x y z) = [x, y, z]"
| "listLeft (Deque left right) = (State.toList left) @ (rev (State.toList right))"

fun listRight :: "'a deque \<Rightarrow> 'a list" where
  "listRight Empty = []"
| "listRight (One x) = [x]"
| "listRight (Two x y) = [y, x]"
| "listRight (Three x y z) = [z, y, x]"
| "listRight (Deque left right) = (State.toList right) @ (rev (State.toList left))"

(*
For test purposes:

fun enqueueLeftAll :: "'a list \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueLeftAll [] deque = deque"
| "enqueueLeftAll (x#xs) deque = enqueueLeftAll xs (enqueueLeft x deque)" 

fun enqueueRightAll :: "'a list \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueRightAll [] deque = deque"
| "enqueueRightAll (x#xs) deque = enqueueRightAll xs (enqueueRight x deque)" 

fun dequeueLeftN :: "nat \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "dequeueLeftN 0 deque = deque"
| "dequeueLeftN (Suc n) deque = dequeueLeftN n (dequeueLeft deque)" 
*)

end
