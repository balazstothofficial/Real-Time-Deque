theory ReverseN 
  imports Main
begin

fun reverseN :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverseN 0 xs acc = acc"
| "reverseN n [] acc = acc"
| "reverseN (Suc n) (x#xs) acc = reverseN n xs (x#acc)"

(*abbreviation reverseN' where
  "reverseN' n xs acc \<equiv> rev (take n xs) @ acc"*)

end
