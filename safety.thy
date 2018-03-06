theory safety
imports ref_crdt_proofs
begin

lemma executeEffectors_split:
"executeEffectors (xs@ys) initial eff = executeEffectors ys (executeEffectors xs initial eff) eff"
  by (auto simp add: executeEffectors_def)

lemma get_effectors_split:
"get_effectors E (xs@ys) = get_effectors E xs @ get_effectors E ys"
  by (auto simp add: get_effectors_def compose_forward_def)

lemma wf_valid_event_sequence:
  assumes wf: "wellFormed_impl E"
  and eInfo_def: "(events E .[ev]) = Some eInfo"
shows "valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBeforeE E)"
  by (smt compose_forward_def eInfo_def fmpredD local.wf wellFormed_def wellFormed_impl_def wf_correct_execution_lists_def)

lemma execution_order_in_snapshot:
  assumes wf: "wellFormed_impl E"
    and eInfo_def: "(events E .[e]) = Some eInfo"
    and i: "i < length (event_executionOrder eInfo)"
shows "fst (event_executionOrder eInfo ! i) \<in> snapshot_events (event_snapshot eInfo)"
proof -

  have i_in: "event_executionOrder eInfo ! i \<in> set (event_executionOrder eInfo)"
    by (simp add: i)

  have ves: "valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBeforeE E)"
    using eInfo_def local.wf wf_valid_event_sequence by auto
  hence "0 < snapshot_num (event_snapshot eInfo) (fst (event_executionOrder eInfo ! i))"
    using i_in by (auto simp add: valid_event_sequence_def)

  thus "fst (event_executionOrder eInfo ! i) \<in> snapshot_events (event_snapshot eInfo)"
    using fmdom'_notD by fastforce


qed


lemma show_all_states:
  assumes wf: "wellFormed_impl E"
    and p: "\<And>state effectors exec_order snapshot. \<lbrakk>
          state = executeEffectors effectors initialState effector_impl;
          effectors = get_effectors E exec_order;
          valid_event_sequence exec_order snapshot (happensBeforeE E)
        \<rbrakk> \<Longrightarrow> P state"
  shows "forallStates E P"
proof (auto simp add: forallStates_def forallEvents_def compose_forward_def fmpred_iff)
  fix e eInfo
  assume eInfo_def: "(events E .[e]) = Some eInfo"

  have 1: "event_state_pre eInfo = executeEffectors (get_effectors E (event_executionOrder eInfo)) initialState effector_impl"
    by (smt eInfo_def compose_forward_def fmdom'I fmdom'_notI fmpred_cases local.wf option.sel wellFormed_def wellFormed_impl_def wf_effector_def)
  show "P (event_state_pre eInfo)"
  proof (rule p[OF 1])
    show "get_effectors E (event_executionOrder eInfo) = get_effectors E (event_executionOrder eInfo)"
      by simp
    show "valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBeforeE E)"
      using eInfo_def local.wf wf_valid_event_sequence by auto

  qed


  show "P (event_state_post eInfo)"
  proof (rule p)
    have post_def: "event_state_post eInfo = executeEffectors (event_effectors eInfo) (event_state_pre eInfo) effector_impl"
      using wf eInfo_def by (auto simp add: wellFormed_impl_def wellFormed_def wf_effector_def compose_forward_def  )

    have event_effectors_def: "get_effectors E (map (Pair e) [0..<length (event_effectors eInfo)]) = event_effectors eInfo"
      by (auto simp add: get_effectors_def compose_forward_def eInfo_def nth_equalityI)

    have sorted_before: "sorted_partial' (event_executionOrder eInfo) (happensBeforeE E)"
      using eInfo_def local.wf valid_event_sequence_def wf_valid_event_sequence by blast


    show "event_state_post eInfo = executeEffectors (get_effectors E (event_executionOrder eInfo@map (\<lambda>i. (e,i)) [0..<length (event_effectors eInfo)] )) initialState effector_impl"
      by (simp add: "1" executeEffectors_split get_effectors_split local.event_effectors_def post_def)

    show "get_effectors E (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)]) = get_effectors E (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)])"
      by simp

    have valid_seq: "valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBeforeE E)"
      using eInfo_def local.wf wf_valid_event_sequence by blast


    have e_notin_snapshot: "e \<notin> snapshot_events (event_snapshot eInfo)"
      using wf apply (auto simp add: wellFormed_impl_def wellFormed_def wf_acyclic_def fmap_entries_def)
      by (metis eInfo_def fmlookup_dom'_iff option.distinct(1) option.sel)

    hence e_notin_exec_order: "(e,i) \<notin> set (event_executionOrder eInfo)" for i
      using valid_event_sequence_def valid_seq by fastforce

    show "valid_event_sequence (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)]) (snapshot_update (event_snapshot eInfo) e (length (event_effectors eInfo)) ) (happensBeforeE E)"
      unfolding valid_event_sequence_def proof (intro conjI)

      show " \<forall>(ea, i)\<in>snapshot_entries (snapshot_update (event_snapshot eInfo) e (length (event_effectors eInfo))).
                \<forall>i'<i. (ea, i') \<in> set (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)])"
        using valid_seq by (auto simp add: valid_event_sequence_def snapshot_update_def fmap_entries_def)

      show "\<forall>(e', i)\<in>set (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)]).
         i < snapshot_num (snapshot_update (event_snapshot eInfo) e (length (event_effectors eInfo))) e'"
        using valid_seq e_notin_exec_order by (auto simp add: valid_event_sequence_def snapshot_update_def fmap_entries_def)

      show "sorted_partial' (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)]) (happensBeforeE E)"
        apply (auto simp add: sorted_partial'_def nth_append happensBeforeE_def)
        using  sorted_before apply (simp add: happensBeforeE_def sorted_partial'_def) 
         apply (auto simp add: happensBeforeP2_def split: if_splits option.splits)
         apply (metis e_notin_exec_order eq_fst_iff nth_mem)
        apply (auto simp add: includedIn_def)
      proof -
        fix j i x2
        assume a0: "\<not> j < length (event_executionOrder eInfo)"
          and a1: "j < length (event_executionOrder eInfo) + length (event_effectors eInfo)"
          and a2: "i < length (event_executionOrder eInfo)"
          and a3: "e \<noteq> fst (event_executionOrder eInfo ! i)"
          and a4: "(events E .[fst (event_executionOrder eInfo ! i)]) = Some x2"
          and a5: "j - length (event_executionOrder eInfo) < snapshot_num (event_snapshot x2) e"
        have "event_snapshot x2 \<le> event_snapshot eInfo"
          using wf apply (auto simp add: wellFormed_impl_def wellFormed_def wf_causallyConsistent_def)
          apply (drule_tac x="(e, eInfo)" in bspec)
          apply (simp add: eInfo_def in_fmap_entries)
          apply (auto split: option.splits)
          apply (drule_tac x="fst (event_executionOrder eInfo ! i)" in bspec)
          using wf apply (auto simp add: wellFormed_impl_def wellFormed_def wf_correct_execution_lists_def compose_forward_def)[1]
           apply (drule_tac x=e and y=eInfo in fmpredD)
          using eInfo_def apply simp
           apply (auto simp add:  valid_event_sequence_def)[1]
           apply (drule_tac x="event_executionOrder eInfo ! i" in bspec) back
          using a2 apply simp


          using  apply blast

          find_theorems fmpred

          apply (simp add: a4 in_fmap_entries)
          apply (auto split: option.splits)

           apply (simp add: fmap_entries_def)

          sorry (* using causal consistency *)
        hence "snapshot_num (event_snapshot x2) e = 0"
          sorry
        thus "False"
          using a5 by linarith
      qed
    qed
  qed
qed


(*
definition wf_effector :: "('operation, 'operation_result, 'operation_effector, 'state)execution \<Rightarrow> 'state \<Rightarrow> ('operation_effector, 'state) effector_function \<Rightarrow> bool" where
"wf_effector execution initS eff \<equiv>
events execution |> fmpred (\<lambda>e eInfo. 
  let effectors = event_executionOrder eInfo |> List.maps (\<lambda>e'. 
      case (events execution).[e'] of Some eInfo' \<Rightarrow> take (snapshot_num (event_snapshot eInfo) e') (event_effectors eInfo') | None \<Rightarrow> [])
  in
  event_state_pre eInfo = executeEffectors effectors initS eff
  \<and> event_state_post eInfo = executeEffectors (event_effectors eInfo) (event_state_pre eInfo) eff)
"
*)

lemma 
  assumes wf: "wellFormed_impl E"
  shows "invariant1 E"
  unfolding invariant1_def proof (rule show_all_states[OF wf])


qed

end