theory Common
  imports Current Idle ReverseN
begin

datatype 'a state = 
    Copy "'a current" "'a list" "'a list" nat
    | Idle "'a current" "'a idle"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Idle _ idle) = Idle.toList idle"
| "toList (Copy (Current extra _ _ remained) old new moved) 
   = extra @ reverseN (remained - moved) old new"

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
    \<and> Current.newSize current = Idle.size idle
    \<and> take (Idle.size idle) (Current.toList current) = 
      take (Current.size current) (Idle.toList idle)"
| "invariant (Copy current aux new moved) \<longleftrightarrow> (
    case current of Current _ _ old remained \<Rightarrow>
      moved < remained
    \<and> moved = List.length new
    \<and> remained \<le> List.length aux + moved
    \<and> Current.invariant current
    \<and> take remained (Stack.toList old) = take (Stack.size old) (reverseN (remained - moved) aux new)
 )"

fun remainingSteps :: "'a state \<Rightarrow> nat" where
  "remainingSteps (Idle _ _) = 0"
| "remainingSteps (Copy (Current _ _ _ remained) aux new moved) = remained - moved"


(* Use size for emptiness? *)
fun size :: "'a state \<Rightarrow> nat" where
  "size (Idle current idle) = min (Current.size current) (Idle.size idle)"
| "size (Copy current _ _ _) = min (Current.size current) (Current.newSize current)"

fun newSize :: "'a state \<Rightarrow> nat" where
  "newSize (Idle current _) = Current.newSize current"
| "newSize (Copy current _ _ _) = Current.newSize current"

end
