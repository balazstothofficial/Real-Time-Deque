theory Deque
  imports Main
begin

locale Deque =
fixes empty :: "'q"
fixes enqL :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes enqR :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes firstL :: "'q \<Rightarrow> 'a"
fixes firstR :: "'q \<Rightarrow> 'a"
fixes deqL :: "'q \<Rightarrow> 'q"
fixes deqR :: "'q \<Rightarrow> 'q"
fixes is_empty :: "'q \<Rightarrow> bool"
fixes listL :: "'q \<Rightarrow> 'a list"
fixes listR :: "'q \<Rightarrow> 'a list"
fixes invar :: "'q \<Rightarrow> bool"

assumes listL_empty:
 "listL empty = []"
assumes listR_empty:
 "listR empty = []"

assumes list_enqL:   
 "invar q \<Longrightarrow> listL(enqL x q) = x # listL q"
assumes list_enqueueRight:  
 "invar q \<Longrightarrow> listR(enqR x q) = x # listR q"
assumes list_dequeueLeft:   
 "\<lbrakk>invar q; \<not> listL q = []\<rbrakk> \<Longrightarrow> listL(deqL q) = tl(listL q)"
assumes list_dequeueRight: 
 "\<lbrakk>invar q; \<not> listR q = []\<rbrakk> \<Longrightarrow> listR(deqR q) = tl(listR q)"

assumes list_firstL:
 "\<lbrakk>invar q; \<not> listL q = []\<rbrakk> \<Longrightarrow> firstL q = hd(listL q)"
assumes list_firstR:
 "\<lbrakk>invar q; \<not> listR q = []\<rbrakk> \<Longrightarrow> firstR q = hd(listR q)"

assumes listL_is_empty:  
 "invar q \<Longrightarrow> is_empty q = (listL q = [])"
assumes listRight_isEmpty:
 "invar q \<Longrightarrow> is_empty q = (listR q = [])"

assumes invar_empty: 
 "invar empty"

assumes invar_enqL:  
 "invar q \<Longrightarrow> invar(enqL x q)"
assumes invar_enqR: 
 "invar q \<Longrightarrow> invar(enqR x q)"
assumes invar_deqL: 
 "\<lbrakk>invar q; \<not> is_empty q\<rbrakk>  \<Longrightarrow> invar(deqL q)"
assumes invar_deqR: 
 "\<lbrakk>invar q; \<not> is_empty q\<rbrakk>  \<Longrightarrow> invar(deqR q)"
assumes listL_listR: 
 "invar q \<Longrightarrow> listL q = rev (listR q)"

end
