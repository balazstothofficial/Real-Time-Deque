theory Common
  imports Current Idle ReverseN
begin

datatype (plugins del: size)'a state = 
      Copy "'a current" "'a list" "'a list" nat
    | Idle "'a current" "'a idle"

fun list :: "'a state \<Rightarrow> 'a list" where
  "list (Idle _ idle) = Idle.list idle"
| "list (Copy (Current extra _ _ remained) old new moved) 
   = extra @ reverseN (remained - moved) old new"

fun list_current :: "'a state \<Rightarrow> 'a list" where
  "list_current (Idle current _) = Current.list current"
| "list_current (Copy current _ _ _) = Current.list current"

(* TODO: Maybe inline function? *)
fun normalize :: "'a state \<Rightarrow> 'a state" where
  "normalize (Copy current old new moved) = (
      case current of Current extra added _ remained \<Rightarrow> 
      if moved \<ge> remained
      then Idle current (idle.Idle (Stack extra new) (added + moved))
      else Copy current old new moved
  )"
| "normalize state = state"

fun step :: "'a state \<Rightarrow> 'a state" where
  "step (Idle current idle) = Idle current idle"
| "step (Copy current aux new moved) = (
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

instantiation state ::(type) emptyable
begin

fun is_empty :: "'a state \<Rightarrow> bool" where
  "is_empty (Idle current idle)  \<longleftrightarrow> Current.is_empty current \<or> Idle.is_empty idle"
| "is_empty (Copy current _ _ _) \<longleftrightarrow> Current.is_empty current"

instance..
end

instantiation state::(type) invar
begin

fun invar :: "'a state \<Rightarrow> bool" where
  "invar (Idle current idle) \<longleftrightarrow>
      Idle.invar idle 
    \<and> Current.invar current 
    \<and> size_new current = size idle
    \<and> take (size idle) (Current.list current) = 
      take (Current.size current) (Idle.list idle)"
| "invar (Copy current aux new moved) \<longleftrightarrow> (
    case current of Current _ _ old remained \<Rightarrow>
      moved < remained
    \<and> moved = length new
    \<and> remained \<le> length aux + moved
    \<and> Current.invar current
    \<and> take remained (Stack.list old) = take (Stack.size old) (reverseN (remained - moved) aux new)
 )"

instance..
end

instantiation state::(type) size
begin

(* Use size for emptiness? *)
fun size :: "'a state \<Rightarrow> nat" where
  "size (Idle current idle) = min (Current.size current) (Idle.size idle)"
| "size (Copy current _ _ _) = min (Current.size current) (Current.size_new current)"

instance..
end

fun size_new :: "'a state \<Rightarrow> nat" where
  "size_new (Idle current _) = Current.size_new current"
| "size_new (Copy current _ _ _) = Current.size_new current"

fun remaining_steps :: "'a state \<Rightarrow> nat" where
  "remaining_steps (Idle _ _) = 0"
| "remaining_steps (Copy (Current _ _ _ remained) aux new moved) = remained - moved"

end
