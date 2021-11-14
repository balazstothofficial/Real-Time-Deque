theory Big
  imports Common
begin

datatype 'a state = 
     Reverse "'a current" "'a stack" "'a list" nat
   | Common "'a Common.state"

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Common common) = Common.toList common"
| "toList (Reverse current _ _ _) = Current.toList current"

fun tick :: "'a state \<Rightarrow> 'a state" where
  "tick (Common state) = Common (Common.tick state)"
| "tick (Reverse current big auxB count) = 
     Reverse current (Stack.pop big) ((first big)#auxB) (count - 1)"

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Common state) = Common (Common.push x state)"
| "push x (Reverse current big auxB count) = Reverse (put x current) big auxB count"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Common state) = (let (x, state) = Common.pop state in (x, Common state))"
| "pop (Reverse current big auxB count) = (top current, Reverse (bottom current) big auxB count)"

end