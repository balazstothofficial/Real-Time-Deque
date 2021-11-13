theory Stack
  imports Main
begin

datatype 'a stack = Stack "'a list" "'a list"

definition empty where
  "empty \<equiv> Stack [] []"

fun isEmpty :: "'a stack \<Rightarrow> bool" where
  "isEmpty (Stack [] []) = True"
| "isEmpty _             = False"

fun push :: "'a \<Rightarrow> 'a stack \<Rightarrow> 'a stack" where
  "push element (Stack left right) = Stack (element#left) right"

fun pop :: "'a stack \<Rightarrow> 'a stack" where
  "pop (Stack (x#left) right)     = Stack left right"
| "pop (Stack []       (x#right)) = Stack []   right"

fun first :: "'a stack \<Rightarrow> 'a" where
  "first (Stack (x#left) right)     = x"
| "first (Stack []       (x#right)) = x"

fun size :: "'a stack \<Rightarrow> nat" where
  "size (Stack left right) = length left + length right"

fun toList :: "'a stack \<Rightarrow> 'a list" where
  "toList (Stack left right) = left @ right"

fun invariant :: "'a stack \<Rightarrow> bool" where
  "invariant (Stack [] []) = True"
| "invariant (Stack [] _) = False"
| "invariant _ = True"



end