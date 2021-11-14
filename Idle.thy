theory Idle
  imports Stack
begin

datatype 'a idle = Idle "'a stack" nat

fun toList :: "'a idle \<Rightarrow> 'a list" where
  "toList (Idle stack _) = Stack.toList stack"

end
