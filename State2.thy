theory State2 
  imports Current
begin

datatype 'a idle = Idle "'a stack" nat

fun idleToList :: "'a idle \<Rightarrow> 'a list" where
  "idleToList (Idle stack _) = Stack.toList stack"

datatype 'a common = 
    Copy "'a current" "'a list" "'a list" nat
  | Idle "'a idle"

fun commonToList :: "'a common \<Rightarrow> 'a list" where
  "commonToList (Idle idle) = idleToList idle"
| "commonToList (Copy current _ _ _) = toList current"

fun normalize :: "'a common \<Rightarrow> 'a common" where
  "normalize (Copy current old new moved) = (
      case current of Current extra added _ remained \<Rightarrow> 
      if moved = remained
      then Idle (idle.Idle (Stack extra new) (added + moved))
      else Copy current old new moved
  )"
| "normalize state = state"

fun tickCommon :: "'a common \<Rightarrow> 'a common" where
  "tickCommon (Idle idle) = Idle idle"
| "tickCommon (Copy current aux new moved) = (
    case current of Current _ _ _ remained \<Rightarrow>
      if moved < remained
      then normalize (Copy current (tl aux) ((hd aux)#new) (moved + 1))
      else normalize (Copy current aux new moved)
  )"

fun pushCommon :: "'a \<Rightarrow> 'a common \<Rightarrow> 'a common" where
  "pushCommon x (Idle (idle.Idle stack stackSize)) = 
      Idle (idle.Idle (push x stack) (Suc stackSize))"
| "pushCommon x (Copy current aux new moved) = Copy (put x current) aux new moved"

fun popCommon :: "'a common \<Rightarrow> 'a * 'a common" where
  "popCommon (Idle (idle.Idle stack stackSize)) = 
      (first stack, Idle (idle.Idle (pop stack) (stackSize - 1)))"
| "popCommon (Copy current aux new moved) = 
      (top current, Copy (bottom current) aux new moved)"

datatype 'a stateB = 
     Reverse "'a current" "'a stack" "'a list" nat
   | Common "'a common"

fun bToList :: "'a stateB \<Rightarrow> 'a list" where
  "bToList (Common common) = commonToList common"
| "bToList (Reverse current _ _ _) = toList current"

fun tickB :: "'a stateB \<Rightarrow> 'a stateB" where
  "tickB (Common state) = Common (tickCommon state)"
| "tickB (Reverse current big auxB count) = 
     Reverse current (pop big) ((first big)#auxB) (count - 1)"

fun pushB :: "'a \<Rightarrow> 'a stateB \<Rightarrow> 'a stateB" where
  "pushB x (Common state) = Common (pushCommon x state)"
| "pushB x (Reverse current big auxB count) = Reverse (put x current) big auxB count"

fun popB :: "'a stateB \<Rightarrow> 'a * 'a stateB" where
  "popB (Common state) = (let (x, state) = popCommon state in (x, Common state))"
| "popB (Reverse current big auxB count) = (top current, Reverse (bottom current) big auxB count)"

datatype 'a stateS = 
   Reverse1 "'a current" "'a stack" "'a list"
 | Reverse2 "'a current" "'a list" "'a stack" "'a list" nat
 | Common "'a common"

fun sToList :: "'a stateS \<Rightarrow> 'a list" where
  "sToList (Common common) = commonToList common"
| "sToList (Reverse1 current _ _ ) = toList current"
| "sToList (Reverse2 current _ _ _ _) = toList current"

fun tickS :: "'a stateS \<Rightarrow> 'a stateS" where
  "tickS (Common state) = Common (tickCommon state)"
| "tickS (Reverse1 current small auxS) = (
    if isEmpty small 
    then Reverse1 current small auxS 
    else Reverse1 current (pop small) ((first small)#auxS)
  )"
| "tickS (Reverse2 current auxS big newS count) = (
    if isEmpty big
    then Common (normalize (Copy current auxS newS count))
    else Reverse2 current auxS (pop big) ((first big)#newS) (count + 1)
  )"

fun pushS :: "'a \<Rightarrow> 'a stateS \<Rightarrow> 'a stateS" where
  "pushS x (Common state) = Common (pushCommon x state)"
| "pushS x (Reverse1 current small auxS) = Reverse1 (put x current) small auxS"
| "pushS x (Reverse2 current auxS big newS count) = Reverse2 (put x current) auxS big newS count"

fun popS :: "'a stateS \<Rightarrow> 'a * 'a stateS" where
  "popS (Common state) = (let (x, state) = popCommon state in (x, Common state))"
| "popS (Reverse1 current small auxS) = (top current, Reverse1 (bottom current) small auxS)"
| "popS (Reverse2 current auxS big newS count) = 
    (top current, Reverse2 (bottom current) auxS big newS count)"

fun ticks :: "'a stateB \<Rightarrow> 'a stateS \<Rightarrow> 'a stateB * 'a stateS" where
  "ticks (Reverse currentB big auxB 0) (Reverse1 currentS _ auxS) =
    (stateB.Common (normalize (Copy currentB auxB [] 0)), Reverse2 currentS auxS big [] 0)"
| "ticks left right = (tickB left, tickS right)"

end
