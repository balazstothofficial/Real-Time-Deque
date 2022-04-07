theory Current
  imports Stack
begin

datatype (plugins del: size) 'a current = Current "'a list" nat "'a stack" nat

fun put :: "'a \<Rightarrow> 'a current \<Rightarrow> 'a current" where
  "put x (Current extra added old remained) = Current (x#extra) (added + 1) old remained"

fun get :: "'a current \<Rightarrow> 'a * 'a current" where
  "get (Current [] added old remained)     = (first old, Current [] added (pop old) (remained - 1))"
| "get (Current (x#xs) added old remained) = (x, Current xs (added - 1) old remained)"

fun top :: "'a current \<Rightarrow> 'a" where
  "top current = fst (get current)"

fun bottom :: "'a current \<Rightarrow> 'a current" where
  "bottom current = snd (get current)"

fun list :: "'a current \<Rightarrow> 'a list" where
  "list (Current extra _ old _) = extra @ (Stack.list old)"

instantiation current::(type) emptyable
begin

(* TODO: Actually it should be "added + remained = 0" Maybe directly base it on size? *) 
fun is_empty :: "'a current \<Rightarrow> bool" where
  "is_empty (Current extra _ old remained) \<longleftrightarrow> Stack.is_empty old \<and> extra = [] \<or> remained = 0"

instance..
end

instantiation current::(type) invar
begin

fun invar :: "'a current \<Rightarrow> bool" where
  "invar (Current extra added _ _) \<longleftrightarrow> length extra = added"

instance..
end

instantiation current::(type) size
begin

fun size :: "'a current \<Rightarrow> nat" where
  "size (Current _ added old _) = added + Stack.size old"

instance..
end

fun size_new :: "'a current \<Rightarrow> nat" where
  "size_new (Current _ added _ remained) = added + remained"

end
