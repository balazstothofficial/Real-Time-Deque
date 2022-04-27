theory Type_Classes
  imports Main
begin

class emptyable = 
  fixes is_empty :: "'a \<Rightarrow> bool"

class invar =
  fixes invar :: "'a \<Rightarrow> bool"

class size_new =
  fixes size_new :: "'a \<Rightarrow> nat"

class step =
  fixes step :: "'a \<Rightarrow> 'a"

class remaining_steps =
  fixes remaining_steps :: "'a \<Rightarrow> nat"

end
