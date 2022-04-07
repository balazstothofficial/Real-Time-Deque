theory Idle
  imports Stack
begin

datatype (plugins del: size) 'a idle = Idle "'a stack" nat

fun list :: "'a idle \<Rightarrow> 'a list" where
  "list (Idle stack _) = Stack.list stack"

fun push :: "'a \<Rightarrow> 'a idle \<Rightarrow> 'a idle" where
  "push x (Idle stack stackSize) = Idle (Stack.push x stack) (Suc stackSize)"

fun pop :: "'a idle \<Rightarrow> ('a * 'a idle)" where
  "pop (Idle stack stackSize) = (Stack.first stack, Idle (Stack.pop stack) (stackSize - 1))"

instantiation idle :: (type) size
begin

fun size :: "'a idle \<Rightarrow> nat" where
  "size (Idle stack _) = Stack.size stack"

instance..
end

instantiation idle :: (type) emptyable
begin

fun is_empty :: "'a idle \<Rightarrow> bool" where
  "is_empty (Idle stack _) \<longleftrightarrow> Stack.is_empty stack"

instance..
end

instantiation idle ::(type) invar
begin

fun invar :: "'a idle \<Rightarrow> bool" where
  "invar (Idle stack stackSize) \<longleftrightarrow> Stack.size stack = stackSize"

instance..
end
  
end
