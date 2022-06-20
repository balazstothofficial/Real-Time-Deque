theory Current
  imports Stack
begin

datatype (plugins del: size) 'a current = Current "'a list" nat "'a stack" nat

fun push :: "'a \<Rightarrow> 'a current \<Rightarrow> 'a current" where
  "push x (Current extra added old remained) = Current (x#extra) (added + 1) old remained"

fun pop :: "'a current \<Rightarrow> 'a * 'a current" where
  "pop (Current [] added old remained)     = (first old, Current [] added (Stack.pop old) (remained - 1))"
| "pop (Current (x#xs) added old remained) = (x, Current xs (added - 1) old remained)"

fun first :: "'a current \<Rightarrow> 'a" where
  "first current = fst (pop current)"

abbreviation drop_first :: "'a current \<Rightarrow> 'a current" where
  "drop_first current \<equiv> snd (pop current)"

fun list :: "'a current \<Rightarrow> 'a list" where
  "list (Current extra _ old _) = extra @ (Stack.list old)"

instantiation current::(type) emptyable
begin

(* TODO: Actually it should be "added + remained = 0" Maybe directly base it on size? *) 
fun is_empty_current :: "'a current \<Rightarrow> bool" where
  "is_empty (Current extra _ old remained) \<longleftrightarrow> is_empty old \<and> extra = [] \<or> remained = 0"

instance..
end

instantiation current::(type) invar
begin

fun invar_current :: "'a current \<Rightarrow> bool" where
  "invar (Current extra added _ _) \<longleftrightarrow> length extra = added"

instance..
end

instantiation current::(type) size
begin

fun size_current :: "'a current \<Rightarrow> nat" where
  "size (Current _ added old _) = added + size old"

instance..
end

instantiation current::(type) size_new
begin

fun size_new_current :: "'a current \<Rightarrow> nat" where
  "size_new (Current _ added _ remained) = added + remained"

instance..
end

end
