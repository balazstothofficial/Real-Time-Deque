theory RealTimeDeque
  imports Transforming
begin

datatype 'a deque =
    Empty
  | One 'a
  | Two 'a 'a
  | Three 'a 'a 'a 
  | Idle "'a idle" "'a idle"
  | Transforming "'a states"

definition empty where
  "empty \<equiv> Empty"

instantiation deque::(type) emptyable
begin

fun is_empty :: "'a deque \<Rightarrow> bool" where
  "is_empty Empty = True"
| "is_empty _ = False"

instance..
end

fun swap :: "'a deque \<Rightarrow> 'a deque" where
  "swap Empty = Empty"  
| "swap (One x) = One x"
| "swap (Two x y) = Two y x"
| "swap (Three x y z) = Three z y x"
| "swap (Idle left right) = Idle right left"
| "swap (Transforming (Left small big)) = (Transforming (Right big small))"
| "swap (Transforming (Right big small)) = (Transforming (Left small big))"

fun small_deque :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a deque" where
  "small_deque []     [] = Empty"

| "small_deque (x#[]) [] = One x"
| "small_deque [] (x#[]) = One x"

| "small_deque (x#[])(y#[]) = Two y x"
| "small_deque (x#y#[]) [] = Two y x"
| "small_deque [] (x#y#[])= Two y x"

| "small_deque [] (x#y#z#[])   = Three z y x"
| "small_deque (x#y#z#[]) []   = Three z y x"
| "small_deque (x#y#[]) (z#[]) = Three z y x"
| "small_deque (x#[]) (y#z#[]) = Three z y x"

fun deqL' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "deqL' (One x) = (x, Empty)"
| "deqL' (Two x y) = (x, One y)"
| "deqL' (Three x y z) = (x, Two y z)"
| "deqL' (Idle left (idle.Idle right rightLength)) = (
   case Idle.pop left of (x, (idle.Idle left leftLength)) \<Rightarrow>
    if 3 * leftLength \<ge> rightLength 
    then 
      (x, Idle (idle.Idle left leftLength) (idle.Idle right rightLength))
    else if leftLength \<ge> 1
    then 
      let newLeftLength = 2 * leftLength + 1 in
      let newRightLength = rightLength - leftLength - 1 in

      let left  = Reverse1 (Current [] 0 left newLeftLength) left [] in
      let right = Reverse (Current [] 0 right newRightLength) right [] newRightLength in

      let states = Left left right in
      let states = six_steps states in
      
      (x, Transforming states)
    else 
      case right of Stack r1 r2 \<Rightarrow> (x, small_deque r1 r2)
  )"
| "deqL' (Transforming (Left left right)) = (
    let (x, left) = Small.pop left in 
    let states = four_steps (Left left right) in
    case states of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow>
            (x, Idle left right)
     | _ \<Rightarrow> (x, Transforming states)
  )"
| "deqL' (Transforming (Right left right)) = (
    let (x, left) = Big.pop left in 
    let states = four_steps (Right left right) in
    case states of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow>
            (x, Idle left right)
     | _ \<Rightarrow> (x, Transforming states)
  )"

fun deqR' :: "'a deque \<Rightarrow> 'a * 'a deque" where
  "deqR' deque = (
    let (x, deque) = deqL' (swap deque) 
    in (x, swap deque)
  )"

fun deqL :: "'a deque \<Rightarrow> 'a deque" where
  "deqL deque = (let (_, deque) = deqL' deque in deque)"

fun deqR :: "'a deque \<Rightarrow> 'a deque" where
  "deqR deque = (let (_, deque) = deqR' deque in deque)"

fun firstL :: "'a deque \<Rightarrow> 'a" where
  "firstL deque = (let (x, _) = deqL' deque in x)" 

fun firstR :: "'a deque \<Rightarrow> 'a" where
  "firstR deque = (let (x, _) = deqR' deque in x)" 

fun enqL :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqL x Empty = One x"
| "enqL x (One y) = Two x y"
| "enqL x (Two y z) = Three x y z"
| "enqL x (Three a b c) = Idle (idle.Idle (Stack [x, a] []) 2) (idle.Idle (Stack [c, b] []) 2)"
| "enqL x (Idle left (idle.Idle right rightLength)) = (
    case Idle.push x left of idle.Idle left leftLength \<Rightarrow> 
      if 3 * rightLength \<ge> leftLength
      then 
        Idle (idle.Idle left leftLength) (idle.Idle right rightLength)
      else 
        let newLeftLength = leftLength - rightLength - 1 in
        let newRightLength = 2 * rightLength + 1 in

        let left  = Reverse  (Current [] 0 left newLeftLength) left [] newLeftLength in
        let right = Reverse1 (Current [] 0 right newRightLength) right [] in
  
        let states = Right left right in
        let states = six_steps states in
        
        Transforming states
  )"
| "enqL x (Transforming (Left left right)) = (
    let left = Small.push x left in 
    let states = four_steps (Left left right) in
    case states of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming states
  )"
| "enqL x (Transforming (Right left right)) = (
    let left = Big.push x left in 
    let states = four_steps (Right left right) in
    case states of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming states
  )"

fun enqR :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqR x deque = (
    let deque = enqL x (swap deque) 
    in swap deque
  )"    
 
fun listL :: "'a deque \<Rightarrow> 'a list" where
  "listL Empty = []"
| "listL (One x) = [x]"
| "listL (Two x y) = [x, y]"
| "listL (Three x y z) = [x, y, z]"
| "listL (Idle left right) = Idle.list left @ (rev (Idle.list right))"
| "listL (Transforming states) = Transforming.listL states"

abbreviation listR :: "'a deque \<Rightarrow> 'a list" where
  "listR deque \<equiv> rev (listL deque)"

instantiation deque::(type) invar
begin

fun invar :: "'a deque \<Rightarrow> bool" where
  "invar Empty = True"
| "invar (One _) = True"
| "invar (Two _ _) = True"
| "invar (Three _ _ _) = True"
| "invar (Idle left right) \<longleftrightarrow>
   Idle.invar left  \<and>
   Idle.invar right \<and>
   \<not> Idle.is_empty left  \<and> 
   \<not> Idle.is_empty right \<and>
   3 * Idle.size right \<ge> Idle.size left \<and>
   3 * Idle.size left \<ge> Idle.size right
  "
| "invar (Transforming states) \<longleftrightarrow> 
   Transforming.invar states \<and>
   size_ok states \<and>
   0 < remaining_steps states
  "

instance..
end

(* For Test: *)
fun runningFold :: "('a deque \<Rightarrow> 'a deque) list \<Rightarrow> 'a deque \<Rightarrow> 'a deque list" where
  "runningFold [] _ = []"
| "runningFold (x#xs) deque = (
  let deque = x deque 
  in deque # runningFold xs deque
)"

value "runningFold 
  [
  enqL (0::int), 
  enqL 1, 
  enqL 2,
  enqL 3,
  enqL 4,   
  enqL 5,
  deqR,
  deqR
  ] 
  Empty"


end
