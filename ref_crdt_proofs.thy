theory ref_crdt_proofs
imports ref_crdt
begin



lemma findMinimal_depends:
  assumes same: "\<And>x y. \<lbrakk>x\<in>set xs; y\<in> set xs\<rbrakk> \<Longrightarrow> (x,y)\<in>R1 \<longleftrightarrow>(x,y)\<in>R2"
  shows "findMinimal R1 xs = findMinimal R2 xs"
  using assms 
  by (auto simp add: findMinimal_def  split: option.splits cong: find_cong)


lemma topSort_depends:
  assumes "\<And>x y. \<lbrakk>x\<in>set xs; y\<in> set xs\<rbrakk> \<Longrightarrow> (x,y)\<in>R1 \<longleftrightarrow>(x,y)\<in>R2"
  shows "topSort R1 xs = topSort R2 xs"
  using assms  apply (induct R1 xs rule: topSort.induct)
   apply simp
  by (metis findMinimal_depends notin_set_remove1 topSort.simps(2))



lemma topSortRest: "topSort (Restr R (set xs)) xs = topSort R xs"
  by (rule topSort_depends, auto)

lemma topSortRest2: "set xs \<subseteq> S \<Longrightarrow> topSort (Restr R S) xs = topSort R xs"
  by (smt Int_iff mem_Sigma_iff subset_iff topSort_depends)


lemma topSort_set[simp]: "set (topSort R xs) = set xs"
  apply (induct R xs rule: topSort.induct)
   apply (auto simp add: Let_def )
  by (metis findMinimal_termination2 length_remove1 nat_neq_iff)

lemma topSort_length: "length (topSort R xs) = length xs"
  apply (induct R xs rule: topSort.induct)
   apply (auto simp add: Let_def )
  by (metis One_nat_def Suc_pred findMinimal_termination2 length_greater_0_conv length_remove1 nat_neq_iff remove1.simps(1))


lemma nth_inset: "\<lbrakk>xs!i = x; i<length xs\<rbrakk> \<Longrightarrow> x\<in>set xs"
  by auto

lemma exists_minimal_partial_order:
  assumes "finite S"
and "S \<noteq> {}"
and po1: "antisym R"
and po2: "trans R"
shows "\<exists>x\<in>S. \<forall>y\<in>S. y=x \<or> (y,x)\<notin>R"

  using `finite S` `S \<noteq> {}` proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a F)

  show ?case
  proof (cases "F={}")
    case True
    then show ?thesis
      by auto 
  next
    case False

    obtain min where "min\<in>F" and "\<forall>y\<in>F. y = min \<or> (y, min) \<notin> R"
      using False insert.hyps(3) by blast


    show ?thesis 
    proof (cases "(a,min)\<in>R")
      case True

      have "\<forall>y\<in>F. y = a \<or> (y, a) \<notin> R"
        apply auto
        by (metis True \<open>\<forall>y\<in>F. y = min \<or> (y, min) \<notin> R\<close> antisymD po1 po2 transE)

      then show ?thesis
        by blast 
    next
      case False
      then show ?thesis
        using \<open>\<forall>y\<in>F. y = min \<or> (y, min) \<notin> R\<close> \<open>min \<in> F\<close> by auto 

    qed
  qed
qed




lemma findMinimal_min1:
  assumes in_set: "a\<in>set xs"
and not_min: "a\<noteq>findMinimal R xs"
and nonempty: "xs \<noteq> []"
and po1: "antisym R"
and po2: "trans R"
shows "(a, findMinimal R xs) \<notin> R"
  using in_set not_min nonempty apply (auto simp add: findMinimal_def  split: option.splits)
   apply (auto simp add: find_None_iff find_Some_iff)
  by (meson List.finite_set exists_minimal_partial_order po1 po2 set_empty)


lemma findMinimal_min2:
  fixes R :: "'a rel"
  assumes in_set: "a\<in>set xs"
and not_min: "a\<noteq>findMinimal R xs"
and nonempty: "xs \<noteq> []"
and po1: "antisym R"
and po2: "trans R"
shows "(findMinimal R xs, a) \<notin> R"
  oops

lemma findMinimal_min3:
  assumes "(x, findMinimal R xs) \<in> R"
and "x\<in>set xs"
and nonempty: "xs \<noteq> []"
and po1: "antisym R"
and po2: "trans R"
shows "x = findMinimal R xs"
  by (meson assms(1) assms(2) findMinimal_min1 nonempty po1 po2)

lemma notin_remove1: "distinct xs \<Longrightarrow> x \<notin> set (remove1 x xs)"
  by simp


lemma topSort_sorted:
  assumes "True" (*"partial_order_on (set xs) R" *)
    and "distinct xs"
and po1: "antisym R"
and po2: "trans R"
  shows "sorted_partial (topSort R xs) R"
using assms proof (induct "length xs" arbitrary: xs rule: less_induct)
  case less
  show ?case 
  proof (cases xs)
    case Nil
    then show ?thesis 
      by (simp add: sorted_partial_def)
  next
    case (Cons y ys)
    hence [simp]: "xs = y # ys" .

    have "distinct ys"
      using less.prems(2) by auto


    show ?thesis 
      apply (subst `xs = y # ys`)
      apply (subst topSort.simps)
      apply (auto simp add: sorted_partial_def Let_def nth_Cons' topSort_length length_remove1 simp del: topSort.simps)
      using `distinct xs` apply auto[1]
      using `distinct xs` apply auto[1]
           apply (frule findMinimal_min3)
      apply (smt Suc_less_eq Suc_pred diff_Suc_1 length_Cons length_pos_if_in_set length_remove1 n_not_Suc_n nth_inset remove1.simps(2) remove1_commute remove1_idem topSort_length topSort_set)
      apply simp
      using po1 apply simp
      using po2 apply simp
           apply (drule nth_inset)
            apply (simp add: topSort_length length_remove1 del: topSort.simps)
           apply (simp add:  del: topSort.simps)
      using \<open>distinct ys\<close> apply auto[1]
      apply (smt One_nat_def Suc_less_SucD Suc_pred distinct.simps(2) distinct_remove1 in_set_remove1 length_Cons length_pos_if_in_set length_remove1 less.hyps less.prems(2) lessI less_trans local.Cons po1 po2 sorted_partial_def topSort_length)
      apply (metis Suc_less_eq Suc_pred findMinimal_min1 insert_iff list.discI list.set(2) nth_inset po1 po2 topSort_length topSort_set)
      apply (metis Suc_less_SucD Suc_pred \<open>distinct ys\<close> length_Cons less.hyps lessI less_trans local.Cons po1 po2 sorted_partial_def topSort_length)
      apply (meson findMinimalIn list.simps(3) set_ConsD)
      by (meson findMinimalIn list.simps(3) set_ConsD)
  qed
qed



lemma valid_event_sequence_topSort:
  assumes "finite S"
and po1: "antisym hb"
and po2: "trans hb"
shows "valid_event_sequence (topSort hb (sorted_list_of_set S)) S hb"
proof (auto simp add: valid_event_sequence_def `finite S`)
  show "distinct (topSort hb (sorted_list_of_set S))"
    by (simp add: card_distinct distinct_card distinct_sorted_list_of_set topSort_length)

  show "sorted_partial (topSort hb (sorted_list_of_set S)) hb"
    by (simp add: distinct_sorted_list_of_set po1 po2 topSort_sorted)
qed

end