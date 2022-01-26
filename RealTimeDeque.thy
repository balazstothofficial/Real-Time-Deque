theory RealTimeDeque
  imports Transformation
begin

datatype 'a deque =
    Empty
  | One 'a
  | Two 'a 'a
  | Three 'a 'a 'a 
  | Idle "'a idle" "'a idle"
  | Transforming "'a transformation"

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
| "swap (Idle left right) = Idle right left"
| "swap (Transforming (Left small big)) = (Transforming (Right big small))"
| "swap (Transforming (Right big small)) = (Transforming (Left small big))"

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
| "dequeueLeft' (Idle left (idle.Idle right rightLength)) = (
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

      let transformation = Left left right in
      let transformation = sixTicks transformation in
      
      (x, Transforming transformation)
    else 
      case right of Stack r1 r2 \<Rightarrow> (x, toSmallDeque r1 r2)
  )"
| "dequeueLeft' (Transforming (Left left right)) = (
    let (x, left) = Small.pop left in 
    let transformation = fourTicks (Left left right) in
    case transformation of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow>
            (x, Idle left right)
     | _ \<Rightarrow> (x, Transforming transformation)
  )"
| "dequeueLeft' (Transforming (Right left right)) = (
    let (x, left) = Big.pop left in 
    let transformation = fourTicks (Right left right) in
    case transformation of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow>
            (x, Idle left right)
     | _ \<Rightarrow> (x, Transforming transformation)
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
| "enqueueLeft x (Three a b c) = Idle (idle.Idle (Stack [x, a] []) 2) (idle.Idle (Stack [c, b] []) 2)"
| "enqueueLeft x (Idle left (idle.Idle right rightLength)) = (
    case Idle.push x left of idle.Idle left leftLength \<Rightarrow> 
      if 3 * rightLength \<ge> leftLength
      then 
        Idle (idle.Idle left leftLength) (idle.Idle right rightLength)
      else 
        let newLeftLength = leftLength - rightLength - 1 in
        let newRightLength = 2 * rightLength + 1 in

        let left  = Reverse  (Current [] 0 left newLeftLength) left [] newLeftLength in
        let right = Reverse1 (Current [] 0 right newRightLength) right [] in
  
        let transformation = Right left right in
        let transformation = sixTicks transformation in
        
        Transforming transformation
  )"
| "enqueueLeft x (Transforming (Left left right)) = (
    let left = Small.push x left in 
    let transformation = fourTicks (Left left right) in
    case transformation of 
        Left 
          (Small.Common (Common.Idle _ left)) 
          (Big.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming transformation
  )"
| "enqueueLeft x (Transforming (Right left right)) = (
    let left = Big.push x left in 
    let transformation = fourTicks (Right left right) in
    case transformation of 
        Right 
          (Big.Common (Common.Idle _ left)) 
          (Small.Common (Common.Idle _ right)) \<Rightarrow> Idle left right
     | _ \<Rightarrow> Transforming transformation
  )"

fun enqueueRight :: "'a \<Rightarrow> 'a deque \<Rightarrow> 'a deque" where
  "enqueueRight x deque = (
    let deque = enqueueLeft x (swap deque) 
    in swap deque
  )"    
 
fun listLeft :: "'a deque \<Rightarrow> 'a list" where
  "listLeft Empty = []"
| "listLeft (One x) = [x]"
| "listLeft (Two x y) = [x, y]"
| "listLeft (Three x y z) = [x, y, z]"
| "listLeft (Idle left right) = Idle.toList left @ (rev (Idle.toList right))"
| "listLeft (Transforming transformation) = toListLeft transformation"

fun listRight :: "'a deque \<Rightarrow> 'a list" where
  "listRight Empty = []"
| "listRight (One x) = [x]"
| "listRight (Two x y) = [y, x]"
| "listRight (Three x y z) = [z, y, x]"
| "listRight (Idle left right) = Idle.toList right @ (rev (Idle.toList left))"
| "listRight (Transforming transformation) = toListRight transformation"

fun invariant :: "'a deque \<Rightarrow> bool" where
  "invariant Empty = True"
| "invariant (One _) = True"
| "invariant (Two _ _) = True"
| "invariant (Three _ _ _) = True"
| "invariant (Idle left right) \<longleftrightarrow>
   Idle.invariant left  \<and>
   Idle.invariant right \<and>
   \<not> Idle.isEmpty left  \<and> 
   \<not> Idle.isEmpty right \<and>
   3 * Idle.size right \<ge> Idle.size left \<and>
   3 * Idle.size left \<ge> Idle.size right
  "
| "invariant (Transforming transformation) \<longleftrightarrow> 
   Transformation.invariant transformation \<and>
   inSizeWindow transformation \<and>
   0 < remainingSteps transformation
  "

fun runningFold :: "('a deque \<Rightarrow> 'a deque) list \<Rightarrow> 'a deque \<Rightarrow> 'a deque list" where
  "runningFold [] _ = []"
| "runningFold (x#xs) deque = (
  let deque = x deque 
  in deque # runningFold xs deque
)"

value "runningFold 
  [
  enqueueLeft (0::int), 
  enqueueLeft 1, 
  enqueueLeft 2,
  enqueueLeft 3,
  dequeueRight,
  enqueueLeft 4,
  enqueueLeft 5,
  enqueueRight 0,
  enqueueRight (-1),
  enqueueRight (-2),
  enqueueRight (-3)
  ] 
  Empty"

end
