theory Common
  imports Current Idle
begin

datatype 'a state = 
    Copy "'a current" "'a list" "'a list" nat
  | Idle "'a idle"


fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Idle idle) = Idle.toList idle"
| "toList (Copy (Current extra _ _ remained) old new moved) 
   = extra @ rev (take (remained - moved) old) @ new"

(* TODO: Maybe inline function? *)
fun normalize :: "'a state \<Rightarrow> 'a state" where
  "normalize (Copy current old new moved) = (
      case current of Current extra added _ remained \<Rightarrow> 
      if moved \<ge> remained
      then Idle (idle.Idle (Stack extra new) (added + moved))
      else Copy current old new moved
  )"
| "normalize state = state"

fun tick :: "'a state \<Rightarrow> 'a state" where
  "tick (Idle idle) = Idle idle"
| "tick (Copy current aux new moved) = (
    case current of Current _ _ _ remained \<Rightarrow>
      normalize (
        if moved < remained
        then Copy current (tl aux) ((hd aux)#new) (moved + 1)
        else Copy current aux new moved
      )
  )"

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Idle (idle.Idle stack stackSize)) = 
      Idle (idle.Idle (Stack.push x stack) (Suc stackSize))"
| "push x (Copy current aux new moved) = Copy (put x current) aux new moved"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Idle idle) = (let (x, idle) = Idle.pop idle in (x, Idle idle))"
| "pop (Copy current aux new moved) = 
      (top current, normalize (Copy (bottom current) aux new moved))"

fun isEmpty :: "'a state \<Rightarrow> bool" where
  "isEmpty (Idle idle)  \<longleftrightarrow> Idle.isEmpty idle"
| "isEmpty (Copy current _ _ _) \<longleftrightarrow> Current.isEmpty current"

fun invariant :: "'a state \<Rightarrow> bool" where
  "invariant (Idle idle) \<longleftrightarrow> Idle.invariant idle"
| "invariant (Copy current aux new moved) \<longleftrightarrow> (
    case current of Current _ _ old remained \<Rightarrow>
      Stack.toList old = take (Stack.size old)(drop ((length aux + length new) - remained)(rev aux @ new))
    \<and> moved < remained
    \<and> moved = List.length new
    \<and> remained \<le> List.length aux + moved
    \<and> Current.invariant current
 )"

fun remainingSteps :: "'a state \<Rightarrow> nat" where
  "remainingSteps (Idle idle) = 0"
| "remainingSteps (Copy (Current _ _ _ remained) aux new moved) = remained - moved"

end
