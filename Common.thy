theory Common
  imports Current Idle
begin

datatype 'a state = 
    Copy "'a current" "'a list" "'a list" nat
    | Idle "'a current" "'a idle"

fun revN :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "revN 0 xs acc = acc"
| "revN n [] acc = acc"
| "revN (Suc n) (x#xs) acc = revN n xs (x#acc)"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Idle _ idle) = Idle.toList idle"
| "toList (Copy (Current extra _ _ remained) old new moved) 
   = extra @ revN (remained - moved) old new"

fun toCurrentList :: "'a state \<Rightarrow> 'a list" where
  "toCurrentList (Idle current _) = Current.toList current"
| "toCurrentList (Copy current _ _ _) = Current.toList current"

(* TODO: Maybe inline function? *)
fun normalize :: "'a state \<Rightarrow> 'a state" where
  "normalize (Copy current old new moved) = (
      case current of Current extra added _ remained \<Rightarrow> 
      if moved \<ge> remained
      then Idle current (idle.Idle (Stack extra new) (added + moved))
      else Copy current old new moved
  )"
| "normalize state = state"

fun tick :: "'a state \<Rightarrow> 'a state" where
  "tick (Idle current idle) = Idle current idle"
| "tick (Copy current aux new moved) = (
    case current of Current _ _ _ remained \<Rightarrow>
      normalize (
        if moved < remained
        then Copy current (tl aux) ((hd aux)#new) (moved + 1)
        else Copy current aux new moved
      )
  )"

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Idle current (idle.Idle stack stackSize)) = 
      Idle (put x current) (idle.Idle (Stack.push x stack) (Suc stackSize))"
| "push x (Copy current aux new moved) = Copy (put x current) aux new moved"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Idle current idle) = (let (x, idle) = Idle.pop idle in (x, Idle (bottom current) idle))"
| "pop (Copy current aux new moved) = 
      (top current, normalize (Copy (bottom current) aux new moved))"

fun isEmpty :: "'a state \<Rightarrow> bool" where
  "isEmpty (Idle current idle)  \<longleftrightarrow> Current.isEmpty current \<or> Idle.isEmpty idle"
| "isEmpty (Copy current _ _ _) \<longleftrightarrow> Current.isEmpty current"

fun invariant :: "'a state \<Rightarrow> bool" where
  "invariant (Idle current idle) \<longleftrightarrow>
      Idle.invariant idle 
    \<and> Current.invariant current 
    \<and> Current.newSize current = Idle.size idle"
| "invariant (Copy current aux new moved) \<longleftrightarrow> (
    case current of Current _ _ old remained \<Rightarrow>
      moved < remained
    \<and> moved = List.length new
    \<and> remained \<le> List.length aux + moved
    \<and> Current.invariant current
    \<and> take remained (Stack.toList old) = take (Stack.size old) (revN (remained - moved) aux new)
 )"

(* 
   Transforming
   (transformation.Right (Big.state.Common (Copy (Current [] 0 (Stack [23, 22, 21] [20, 19, 18, 17, 16, 15, 14, 13, 12, 11]) 8) [19, 20, 21, 22, 23, 24, 25] [18, 17, 16] 3))
     (Reverse2 (Current [] 0 (Stack [] [7, 8, 9, 10]) 9) [10, 9, 8, 7] (Stack [] [12, 11]) [13, 14, 15] 3)),
  Transforming
   (transformation.Right (Big.state.Common (state.Idle (Current [] 0 (Stack [22, 21] [20, 19, 18, 17, 16, 15, 14, 13, 12, 11]) 7) (idle.Idle (Stack [] [22, 21, 20, 19, 18, 17, 16]) 7)))
     (Small.state.Common (Copy (Current [] 0 (Stack [] [7, 8, 9, 10]) 9) [9, 8, 7] [10, 11, 12, 13, 14, 15] 6)))]"
*)

fun remainingSteps :: "'a state \<Rightarrow> nat" where
  "remainingSteps (Idle _ _) = 0"
| "remainingSteps (Copy (Current _ _ _ remained) aux new moved) = remained - moved"

fun size :: "'a state \<Rightarrow> nat" where
  "size (Idle current _) = Current.size current"
| "size (Copy current _ _ _) = Current.size current"

end
