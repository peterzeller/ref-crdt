theory fmap_functions
  imports Main
    "~~/src/HOL/Library/Finite_Map"
begin

section {* Finite maps *}

text {* To keep out model executable, we use finite maps.
In this theory, we extend the standard library with additional syntax and functions. *}

abbreviation lookupsyntax ("_ .[_]"[25,25]25) where
"m.[x] \<equiv> fmlookup m x"

abbreviation lookupsyntax2 ("_ ![_]"[25,25]25) where
"m![x] \<equiv> the (fmlookup m x)"

definition fmap_entries :: "('k, 'v) fmap \<Rightarrow> ('k\<times>'v) set" where
"fmap_entries m \<equiv> (\<lambda>k. (k, m![k])) ` fmdom' m" 

syntax
  "_fm_all"       :: "pttrn \<Rightarrow> pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>[_\<mapsto>_]\<in>_./ _)" [0, 0, 10] 10)

translations
  "\<forall>[k\<mapsto>v]\<in>A. P" \<rightleftharpoons> "CONST fmpred (\<lambda>k v. P) A"

term "\<forall>[x\<mapsto>y]\<in>m. y < x"


lemma fmap_entries_forall[code_abbrev]: "fmpred P m \<longleftrightarrow> (\<forall>(k,v)\<in>fmap_entries m. P k v)"
  apply (auto simp add: fmap_entries_def)
  apply (meson fmdom'_notI fmpredD option.exhaust_sel)
  by (metis fmdom'I fmpredI option.sel)

lemma fmap_entries_exists[code_abbrev]: "(\<not>fmpred (\<lambda>k v. \<not>P k v) m) \<longleftrightarrow> (\<exists>(k,v)\<in>fmap_entries m. P k v)"
  by (subst fmap_entries_forall, auto)

lemma in_fmap_entries: "(m.[x]) = Some y \<Longrightarrow> (x,y)\<in>fmap_entries m"
  by (simp add: fmap_entries_def fmdom'I image_iff)


end