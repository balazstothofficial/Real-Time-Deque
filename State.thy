theory State
  imports Current
begin       

datatype 'a state =
  Norm "'a stack" nat |
  RevB "'a current" "'a stack" "'a list" nat |
  RevS1 "'a current" "'a stack" "'a list" |
  RevS2 "'a current" "'a list" "'a stack" "'a list" nat |
  Copy "'a current" "'a list" "'a list" nat

fun toList :: "'a state \<Rightarrow> 'a list" where
  "toList (Norm stack _) = Stack.toList stack"
| "toList (RevB current _ _ _) = Current.toList current"
| "toList (RevS1 current _ _) = Current.toList current"
| "toList (RevS2 current _ _ _ _) = Current.toList current"
| "toList (Copy current _ _ _) = Current.toList current"

fun normalize :: "'a state \<Rightarrow> 'a state" where
  "normalize (Copy current old new moved) = (
      case current of Current extra added _ remained \<Rightarrow> 
      if moved = remained
      then Norm (Stack extra new) (added + moved)
      else Copy current old new moved
  )"
| "normalize state = state"

fun tick :: "'a state \<Rightarrow> 'a state" where
  "tick state = (
    case state of
         Norm _ _ \<Rightarrow> state
       | RevB current big auxB count \<Rightarrow> RevB current (pop big) ((first big)#auxB) (count - 1)
       | RevS1 current small auxS \<Rightarrow> 
          if isEmpty small 
          then state 
          else RevS1 current (pop small) ((first small)#auxS)
       | RevS2 current auxS big newS count \<Rightarrow>
          if isEmpty big
          then normalize (Copy current auxS newS count)
          else RevS2 current auxS (pop big) ((first big)#newS) (count + 1)
       | Copy current aux new moved \<Rightarrow> case current of Current _ _ _ remained \<Rightarrow>
          if moved < remained
          then normalize (Copy current (tl aux) ((hd aux)#new) (moved + 1))
          else normalize state
  )"

fun ticks :: "'a state \<Rightarrow> 'a state \<Rightarrow> 'a state * 'a state" where
  "ticks (RevB currentB big auxB 0) (RevS1 currentS _ auxS) =
    (normalize (Copy currentB auxB [] 0), RevS2 currentS auxS big [] 0)"
| "ticks (RevS1 currentS _ auxS) (RevB currentB big auxB 0) =
    (RevS2 currentS auxS big [] 0, normalize (Copy currentB auxB [] 0))"
| "ticks left right = (tick left, tick right)"

fun twice :: "('a \<Rightarrow> 'b \<Rightarrow> ('a * 'b)) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('a * 'b))" where
  "twice f = (\<lambda>a b. let (a', b') = f a b in f a' b')"

definition fourTicks where
  "fourTicks \<equiv> twice (twice ticks)"

definition sixTicks where
  "sixTicks \<equiv> twice (twice (twice ticks))"

fun popState :: "'a state \<Rightarrow> 'a * 'a state" where
  "popState (Norm a b)        = (first a, Norm (pop a) (b - 1))"
| "popState (RevB a b c d)    = (top a,   RevB (bottom a) b c d)"
| "popState (RevS1 a b c)     = (top a,   RevS1 (bottom a) b c)"
| "popState (RevS2 a b c d e) = (top a,   RevS2 (bottom a) b c d e)"
| "popState (Copy a b c d)    = (top a,   Copy (bottom a) b c d)"

fun pushState :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "pushState x (Norm a b)        = Norm  (push x a) (Suc b)"
| "pushState x (RevB a b c d)    = RevB  (put x a) b c d"
| "pushState x (RevS1 a b c)     = RevS1 (put x a) b c"
| "pushState x (RevS2 a b c d e) = RevS2 (put x a) b c d e"
| "pushState x (Copy a b c d)    = Copy  (put x a) b c d"

end
