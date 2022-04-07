theory Type_Classes
  imports Main
begin

class emptyable = 
  fixes is_empty :: "'a \<Rightarrow> bool"

class invar =
  fixes invar :: "'a \<Rightarrow> bool"

class list =
  fixes list :: "'a \<Rightarrow> 'a list"

end
