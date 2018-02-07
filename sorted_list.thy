theory sorted_list
  imports Main
begin


subsubsection \<open>\<open>sorted_list_of_set2\<close>\<close>

text\<open>This function maps (finite) linearly ordered sets to sorted
lists. Warning: in most cases it is not a good idea to convert from
sets to lists but one should convert in the other direction (via
@{const set}).\<close>

context linorder
begin

definition sorted_list_of_set2 :: "'a set \<Rightarrow> 'a list" where
  "sorted_list_of_set2 = folding.F insort []"

lemma sorted_list_of_set2_sort_remdups [code]:
  "sorted_list_of_set2 (set xs) = sort (remdups xs)"
  using local.sorted_list_of_set_def local.sorted_list_of_set_sort_remdups sorted_list_of_set2_def by auto

end


end