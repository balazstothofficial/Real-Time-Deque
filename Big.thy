theory Big
  imports Common
begin

datatype (plugins del: size) 'a state = 
     Reverse "'a current" "'a stack" "'a list" nat
   | Common "'a Common.state"

fun list :: "'a state \<Rightarrow> 'a list" where
  "list (Common common) = Common.list common"
| "list (Reverse (Current extra _ _ remained) big aux count) = (
   let reversed = reverseN count (Stack.list big) aux in
    extra @ (reverseN remained reversed [])
  )"

fun list_current :: "'a state \<Rightarrow> 'a list" where
  "list_current (Common common) = Common.list_current common"
| "list_current (Reverse current _ _ _) = Current.list current"

fun step :: "'a state \<Rightarrow> 'a state" where
  "step (Common state) = Common (Common.step state)"
| "step (Reverse current _ aux 0) = Common (normalize (Copy current aux [] 0))"
| "step (Reverse current big aux count) = 
     Reverse current (Stack.pop big) ((Stack.first big)#aux) (count - 1)"

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Common state) = Common (Common.push x state)"
| "push x (Reverse current big aux count) = Reverse (Current.push x current) big aux count"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Common state) = (let (x, state) = Common.pop state in (x, Common state))"
| "pop (Reverse current big aux count) = (first current, Reverse (drop_first current) big aux count)"

instantiation state ::(type) emptyable
begin

fun is_empty :: "'a state \<Rightarrow> bool" where
  "is_empty (Common state) = Common.is_empty state"
| "is_empty (Reverse current _ _ count) = (
    case current of Current extra added old remained \<Rightarrow> 
      Current.is_empty current \<or> remained \<le> count
)"

instance..
end

instantiation state ::(type) invar
begin

fun invar :: "'a state \<Rightarrow> bool" where
  "invar (Common state) \<longleftrightarrow> Common.invar state"
| "invar (Reverse current big aux count) \<longleftrightarrow> (
   case current of Current extra added old remained \<Rightarrow>
      Current.invar current
    \<and> List.length aux \<ge> remained - count
    
    \<and> count \<le> Stack.size big
    \<and> Stack.list old = rev (take (Stack.size old) ((rev (Stack.list big)) @ aux))
    \<and> take remained (Stack.list old) = rev (take remained (reverseN count (Stack.list big) aux))
)"

instance..
end

instantiation state ::(type) size
begin

fun size :: "'a state \<Rightarrow> nat" where
  "size (Common state) = Common.size state"
| "size (Reverse current _ _ _) = min (Current.size current) (Current.size_new current)"

instance..
end

fun size_new :: "'a state \<Rightarrow> nat" where
  "size_new (Common state) = Common.size_new state"
| "size_new (Reverse current _ _ _) = Current.size_new current"

fun remaining_steps :: "'a state \<Rightarrow> nat" where
  "remaining_steps (Common state) = Common.remaining_steps state"
| "remaining_steps (Reverse (Current _ _ _ remaining) _ _ count) = count + remaining + 1"


end