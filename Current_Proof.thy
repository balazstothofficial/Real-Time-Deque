theory Current_Proof
  imports Current
begin

lemma put: "toList (put x current) = x # Current.toList current"
  apply(induction x current rule: put.induct)
  by auto

end