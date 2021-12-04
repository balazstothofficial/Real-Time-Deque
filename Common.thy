theory Common
  imports Current Idle
begin

datatype 'a state = 
    Copy "'a current" "'a list" "'a list" nat
  | Idle "'a current" "'a idle"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Idle current idle) = Current.toList current"
| "toList (Copy current old new _) = Current.toList current"

(* TODO: unnecessary function \<rightarrow> Should be inlined *)
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
      if moved < remained
      then normalize (Copy current (tl aux) ((hd aux)#new) (moved + 1))
      else normalize (Copy current aux new moved)
  )"

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Idle current (idle.Idle stack stackSize)) = 
      Idle (put x current) (idle.Idle (Stack.push x stack) (Suc stackSize))"
| "push x (Copy current aux new moved) = Copy (put x current) aux new moved"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Idle current (idle.Idle stack stackSize)) = 
      (top current, Idle (bottom current) (idle.Idle (Stack.pop stack) (stackSize - 1)))"
| "pop (Copy current aux new moved) = 
      (top current, normalize (Copy (bottom current) aux new moved))"

fun isEmpty :: "'a state \<Rightarrow> bool" where
  "isEmpty (Idle current idle)  \<longleftrightarrow> Current.isEmpty current \<or> Idle.isEmpty idle"
| "isEmpty (Copy current _ _ _) \<longleftrightarrow> Current.isEmpty current"

fun invariant :: "'a state \<Rightarrow> bool" where
  "invariant (Idle current idle) \<longleftrightarrow> (
     case idle of idle.Idle (Stack left right) idleLength \<Rightarrow>
     case current of Current extra added old remained \<Rightarrow>
     let idleList = Idle.toList idle in 
       drop (Stack.size old - List.length right) (Stack.toList old) = drop (List.length right - Stack.size old) right
     \<and> left = extra
     \<and> Idle.invariant idle
     \<and> Current.invariant current
  )"
| "invariant (Copy current aux new moved) \<longleftrightarrow> (
    case current of Current _ _ old remained \<Rightarrow>
      Stack.toList old = drop ((List.length aux + moved) - Stack.size old)(rev aux @ new)
    \<and> moved < remained
    \<and> moved = List.length new
    \<and> remained \<le> List.length aux + moved
    \<and> Current.invariant current
 )"

fun remainingSteps :: "'a state \<Rightarrow> nat" where
  "remainingSteps (Idle current idle) = 0"
| "remainingSteps (Copy (Current _ _ _ remained) aux new moved) = remained - moved"

end