theory Idle
  imports Stack
begin

datatype 'a idle = Idle "'a stack" nat

fun toList :: "'a idle \<Rightarrow> 'a list" where
  "toList (Idle stack _) = Stack.toList stack"

fun push :: "'a \<Rightarrow> 'a idle \<Rightarrow> 'a idle" where
  "push x (Idle stack stackSize) = Idle (Stack.push x stack) (Suc stackSize)"

fun pop :: "'a idle \<Rightarrow> ('a * 'a idle)" where
  "pop (Idle stack stackSize) = (Stack.first stack, Idle (Stack.pop stack) (stackSize - 1))"

fun size :: "'a idle \<Rightarrow> nat" where
  "size (Idle stack _) = Stack.size stack"

fun isEmpty :: "'a idle \<Rightarrow> bool" where
  "isEmpty (Idle stack _) \<longleftrightarrow> Stack.isEmpty stack"

fun invariant :: "'a idle \<Rightarrow> bool" where
  "invariant (Idle stack stackSize) \<longleftrightarrow> Stack.size stack = stackSize"
  
end
