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
shows "valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBefore E)"
  by (smt compose_forward_def eInfo_def fmpredD local.wf wellFormed_def wellFormed_impl_def wf_correct_execution_lists_def)

lemma show_all_states:
  assumes wf: "wellFormed_impl E"
    and p: "\<And>state effectors exec_order snapshot. \<lbrakk>
          state = executeEffectors effectors initialState effector_impl;
          effectors = get_effectors E exec_order;
          valid_event_sequence exec_order snapshot (happensBefore E)
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
    show "valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBefore E)"
      using eInfo_def local.wf wf_valid_event_sequence by auto

  qed


  show "P (event_state_post eInfo)"
  proof (rule p)
    have post_def: "event_state_post eInfo = executeEffectors (event_effectors eInfo) (event_state_pre eInfo) effector_impl"
      using wf eInfo_def by (auto simp add: wellFormed_impl_def wellFormed_def wf_effector_def compose_forward_def  )

    have event_effectors_def: "get_effectors E (map (Pair e) [0..<length (event_effectors eInfo)]) = event_effectors eInfo"
      by (auto simp add: get_effectors_def compose_forward_def eInfo_def nth_equalityI)

    show "event_state_post eInfo = executeEffectors (get_effectors E (event_executionOrder eInfo@map (\<lambda>i. (e,i)) [0..<length (event_effectors eInfo)] )) initialState effector_impl"
      by (simp add: "1" executeEffectors_split get_effectors_split local.event_effectors_def post_def)

    show "get_effectors E (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)]) = get_effectors E (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)])"
      by simp

    show "valid_event_sequence (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)]) (snapshot_update (event_snapshot eInfo) e (length (event_effectors eInfo)) ) (happensBefore E)"
      apply (auto simp add: valid_event_sequence_def snapshot_update_def fmap_entries_def)



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