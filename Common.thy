theory Common
  imports Current Idle
begin

datatype 'a state = 
    Copy "'a current" "'a list" "'a list" nat
  | Idle "'a current" "'a idle"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Idle current idle) = Current.toList current"
| "toList (Copy current old new _) = Current.toList current"

fun normalize :: "'a state \<Rightarrow> 'a state" where
  "normalize (Copy current old new moved) = (
      case current of Current extra added _ remained \<Rightarrow> 
      if moved = remained
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
      (top current, Copy (bottom current) aux new moved)"

fun isEmpty :: "'a state \<Rightarrow> bool" where
  "isEmpty (Idle current _) = Current.isEmpty current"
| "isEmpty (Copy current _ _ _) = Current.isEmpty current"

end
