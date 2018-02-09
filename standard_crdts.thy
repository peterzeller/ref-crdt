theory standard_crdts
  imports Main system_model_types
begin

section {* Standard CRDTs *}

text {* Here we define some standard CRDTs, which we use to implement our reference CRDTs. *}

subsection {* Two-phase set *}

text {* The two-phase set consists of a set of added elements and a set of removed elements (tombstones).  *}

type_synonym 'a two_phase_set_state = "'a set \<times> 'a set"

fun two_phase_set_add where 
"two_phase_set_add (A,R) x = (insert x A, R)"

fun two_phase_set_remove where 
"two_phase_set_remove (A,R) x = (A,insert x R)"

definition two_phase_set_get :: "'a two_phase_set_state \<Rightarrow> 'a set" where
"two_phase_set_get s \<equiv> fst s - snd s"

subsection {* Multi-value register *}

type_synonym 'a mv_register_state = "('a \<times> uid) set"

definition mv_reg_getall :: "'a mv_register_state \<Rightarrow> 'a set" where
"mv_reg_getall s = (fst ` s)"

definition mv_reg_get1 :: "'a::linorder mv_register_state \<Rightarrow> 'a \<Rightarrow> 'a" where
"mv_reg_get1 s d \<equiv> let all = mv_reg_getall s in if all = {} then d else Max (mv_reg_getall s)"

definition mv_reg_get1' where
"mv_reg_get1' s \<equiv> mv_reg_get1 s None"

definition mv_reg_count :: "'a mv_register_state \<Rightarrow> nat" where
"mv_reg_count s = card (mv_reg_getall s)"




end