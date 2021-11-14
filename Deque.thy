theory Deque
  imports Main
begin

locale Deque =
fixes empty :: "'q"
fixes enqueueLeft :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes enqueueRight :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes firstLeft :: "'q \<Rightarrow> 'a"
fixes firstRight :: "'q \<Rightarrow> 'a"
fixes dequeueLeft :: "'q \<Rightarrow> 'q"
fixes dequeueRight :: "'q \<Rightarrow> 'q"
fixes isEmpty :: "'q \<Rightarrow> bool"
fixes listLeft :: "'q \<Rightarrow> 'a list"
fixes listRight :: "'q \<Rightarrow> 'a list"
fixes invariant :: "'q \<Rightarrow> bool"

assumes listLeft_empty:
 "listLeft empty = []"
assumes listRight_empty:
 "listRight empty = []"

assumes list_enqueueLeft:   
 "invariant q \<Longrightarrow> listLeft(enqueueLeft x q) = x # listLeft q"
assumes list_enqueueRight:  
 "invariant q \<Longrightarrow> listRight(enqueueRight x q) = x # listRight q"
assumes list_dequeueLeft:   
 "\<lbrakk>invariant q; \<not> listLeft q = []\<rbrakk> \<Longrightarrow> listLeft(dequeueLeft q) = tl(listLeft q)"
assumes list_dequeueRight: 
 "\<lbrakk>invariant q; \<not> listRight q = []\<rbrakk> \<Longrightarrow> listRight(dequeueRight q) = tl(listRight q)"

assumes list_firstLeft:
 "\<lbrakk>invariant q; \<not> listLeft q = []\<rbrakk> \<Longrightarrow> firstLeft q = hd(listLeft q)"
assumes list_firstRight:
 "\<lbrakk>invariant q; \<not> listRight q = []\<rbrakk> \<Longrightarrow> firstRight q = hd(listRight q)"

assumes listLeft_isEmpty:  
 "invariant q \<Longrightarrow> isEmpty q = (listLeft q = [])"
assumes listRight_isEmpty:
 "invariant q \<Longrightarrow> isEmpty q = (listRight q = [])"

assumes invariant_empty: 
 "invariant empty"

assumes invariant_enqueueLeft:  
 "invariant q \<Longrightarrow> invariant(enqueueLeft x q)"
assumes invariant_enqueueRight: 
 "invariant q \<Longrightarrow> invariant(enqueueRight x q)"
assumes invariant_dequeueLeft: 
 "\<lbrakk>invariant q; \<not> isEmpty q\<rbrakk>  \<Longrightarrow> invariant(dequeueLeft q)"
assumes invariant_dequeueRight: 
 "\<lbrakk>invariant q; \<not> isEmpty q\<rbrakk>  \<Longrightarrow> invariant(dequeueRight q)"

end
