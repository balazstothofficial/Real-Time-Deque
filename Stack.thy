theory Stack
  imports Main Type_Classes
begin

datatype (plugins del: size) 'a stack = Stack "'a list" "'a list"

(* TODO: Move into emptyable? *)
definition empty where
  "empty \<equiv> Stack [] []"

fun push :: "'a \<Rightarrow> 'a stack \<Rightarrow> 'a stack" where
  "push x (Stack left right) = Stack (x#left) right"

fun pop :: "'a stack \<Rightarrow> 'a stack" where
  "pop (Stack [] [])              = Stack [] []"
| "pop (Stack (x#left) right)     = Stack left right"
| "pop (Stack []       (x#right)) = Stack []   right"

fun first :: "'a stack \<Rightarrow> 'a" where
  "first (Stack (x#left) right)     = x"
| "first (Stack []       (x#right)) = x"

fun list :: "'a stack \<Rightarrow> 'a list" where
  "list (Stack left right) = left @ right"

instantiation stack ::(type) emptyable
begin

fun is_empty_stack where
  "is_empty_stack (Stack [] []) = True" 
| "is_empty_stack _             = False"

instance..
end

instantiation stack ::(type) size
begin

fun size_stack :: "'a stack \<Rightarrow> nat" where
  "size (Stack left right) = length left + length right"

instance..
end

end