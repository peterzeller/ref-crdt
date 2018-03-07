theory snapshot
  imports Main 
    system_model_types
    fmap_functions
sugar
begin


section {* Snapshots *}



datatype snapshot = Snapshot (snapshot_map: "(event,nat) fmap")

abbreviation "snapshot_events s \<equiv> fmdom' (snapshot_map s)"
abbreviation "snapshot_entries s \<equiv> fmap_entries (snapshot_map s)"
abbreviation "snapshot_num s e \<equiv> case (snapshot_map s).[e] of Some n \<Rightarrow> Suc n | None \<Rightarrow> 0"
definition includedIn where
"includedIn e n snapshot \<equiv> n < snapshot_num snapshot e"

definition includedIn' (infixl "\<in>\<^sub>s" 40) where
"e \<in>\<^sub>s snapshot \<equiv> snd e < snapshot_num snapshot (fst e)"

find_consts "'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) fmap \<Rightarrow> ('k,'v) fmap"

definition snapshot_update  :: "snapshot \<Rightarrow> event \<Rightarrow> nat \<Rightarrow> snapshot" where
"snapshot_update s e n = Snapshot (fmupd e n (snapshot_map s))"

instantiation snapshot :: preorder begin


definition less_eq_snapshot  :: "snapshot \<Rightarrow> snapshot \<Rightarrow> bool"  where
"less_eq_snapshot x y \<equiv> \<forall>(e,n)\<in>snapshot_entries x. Suc n \<le> snapshot_num y e"
definition "less_snapshot x y \<equiv> (\<forall>(e,n)\<in>snapshot_entries x. Suc n \<le> snapshot_num y e) \<and> (\<exists>(e,n)\<in>snapshot_entries y. n \<ge> snapshot_num x e )"


instance
proof 
  fix x y z :: snapshot
  obtain x' y' z' where [simp]: "x = Snapshot x'" and [simp]: "y = Snapshot y'" and [simp]: "z = Snapshot z'"
    by (metis snapshot.collapse)

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    apply (auto simp add: less_eq_snapshot_def less_snapshot_def  orElse_def fmap_entries_def fmlookup_dom'_iff  split: option.splits)
    using fmdom'I apply force
    by (metis fmdom'I not_less_eq_eq option.sel)


  show "x \<le> x"
    by (auto simp add: less_eq_snapshot_def fmap_entries_def orElse_def fmdom'_notI fmlookup_dom'_iff split: option.splits)

  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    apply (auto simp add: less_eq_snapshot_def fmap_entries_def orElse_def fmdom'_notI split: option.splits)
    apply (meson fmdom'I)
    by fastforce
    
qed

end

definition concurrent :: "'a::preorder \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<parallel> _)"  [51, 51] 50)  where
"x \<parallel> y \<longleftrightarrow> \<not>(x \<le> y \<or> y \<le> x)"


end