theory Current
  imports Stack
begin

datatype 'a current = Current "'a list" nat "'a stack" nat

fun put :: "'a \<Rightarrow> 'a current \<Rightarrow> 'a current" where
  "put element (Current extra added old remained) = Current (element#extra) (added + 1) old remained"

fun get :: "'a current \<Rightarrow> 'a * 'a current" where
  "get (Current [] added old remained)     = (first old, Current [] added (pop old) (remained - 1))"
| "get (Current (x#xs) added old remained) = (x, Current xs (added - 1) old remained)"

fun top :: "'a current \<Rightarrow> 'a" where
  "top current = (let (element, _) = get current in element)"

fun bottom :: "'a current \<Rightarrow> 'a current" where
  "bottom current = (let (_, bottom) = get current in bottom)"

fun toList :: "'a current \<Rightarrow> 'a list" where
  "toList (Current extra _ old _) = extra @ (Stack.toList old)"

fun isEmpty :: "'a current \<Rightarrow> bool" where
  "isEmpty (Current extra _ old remained) \<longleftrightarrow> (Stack.isEmpty old \<and> extra = []) \<or> remained = 0"

fun invariant :: "'a current \<Rightarrow> bool" where
  "invariant (Current extra added old remained) \<longleftrightarrow> length extra = added"

fun newSize :: "'a current \<Rightarrow> nat" where
  "newSize (Current _ added _ remained) = added + remained"

fun size :: "'a current \<Rightarrow> nat" where
  "size (Current _ added old _) = added + Stack.size old"

end
