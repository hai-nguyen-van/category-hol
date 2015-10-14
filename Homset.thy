theory Homset

imports
  Main
  "Category2/Category"
  "Category2/Functors"

begin

definition Hom :: "('o, 'm) Category \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'm set" where
  "Hom C A B = { f. \<exists>f \<in> Mor C. Dom C f = A \<and> Cod C f = B }"

end