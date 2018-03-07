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


lemma snapshot_smaller:
  assumes wf: "wellFormed_impl E"
    and eInfo_def: "(events E .[e]) = Some eInfo"
    and a2: "i < length (event_executionOrder eInfo)"
    and a4: "(events E .[fst (event_executionOrder eInfo ! i)]) = Some x2"
  shows "event_snapshot x2 \<le> event_snapshot eInfo"
  using wf apply (auto simp add: wellFormed_impl_def wellFormed_def wf_causallyConsistent_def)
  apply (drule_tac x="(e, eInfo)" in bspec)
   apply (simp add: eInfo_def in_fmap_entries)
  apply (auto split: option.splits)
  apply (drule_tac x="fst (event_executionOrder eInfo ! i)" in bspec)
  using a2 eInfo_def execution_order_in_snapshot local.wf apply blast
  using a4 by blast

lemma snapshot_smaller_num:
  assumes "x \<le> y"
  shows "snapshot_num x e \<le> snapshot_num y e"
  using assms apply (auto simp add: less_eq_snapshot_def fmap_entries_def)
  by (metis fmdom'_notD le0 option.case_eq_if)


lemma show_all_states:
  assumes wf: "wellFormed_impl E"
    and p: "\<And>state effectors exec_order snapshot. \<lbrakk>
          state = executeEffectors effectors initialState effector_impl;
          effectors = get_effectors E exec_order;
          valid_event_sequence exec_order snapshot (happensBeforeE E);
          valid_snapshot E snapshot 
        \<rbrakk> \<Longrightarrow> P state"
  shows "forallStates E P"
proof (auto simp add: forallStates_def forallEvents_def compose_forward_def fmpred_iff)
  fix e eInfo
  assume eInfo_def: "(events E .[e]) = Some eInfo"

  have 1: "event_state_pre eInfo = executeEffectors (get_effectors E (event_executionOrder eInfo)) initialState effector_impl"
    by (smt eInfo_def compose_forward_def fmdom'I fmdom'_notI fmpred_cases local.wf option.sel wellFormed_def wellFormed_impl_def wf_effector_def)

  have valid_snapshot_eInfo: "valid_snapshot E (event_snapshot eInfo)"
    using eInfo_def in_fmap_entries local.wf wellFormed_def wellFormed_impl_def wf_valid_snapshots_def by fastforce

  show "P (event_state_pre eInfo)"
  proof (rule p[OF 1])
    show "get_effectors E (event_executionOrder eInfo) = get_effectors E (event_executionOrder eInfo)"
      by simp
    show "valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBeforeE E)"
      using eInfo_def local.wf wf_valid_event_sequence by auto
    show "valid_snapshot E (event_snapshot eInfo)"
      by (simp add: valid_snapshot_eInfo)

  qed

  show "P (event_state_post eInfo)"
  proof (cases "event_effectors eInfo")
    case Nil
    text {* if there are no effectors, the post-state is equivalent to the pre-state: *}
    hence "event_state_post eInfo = event_state_pre eInfo"
      by (smt append_Nil2 compose_forward_def eInfo_def executeEffectors_split fmdom'I fmdom'_notI fmpred_cases local.wf option.sel wellFormed_def wellFormed_impl_def wf_effector_def)
    thus "P (event_state_post eInfo)"
      by (simp add: \<open>P (event_state_pre eInfo)\<close>)
  next
    case (Cons e' effs)
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

      show "valid_snapshot E (snapshot_update (event_snapshot eInfo) e (length effs))"
        unfolding valid_snapshot_def proof (standard, clarsimp)
        fix a n
        assume entry: "(a, n) \<in> snapshot_entries (snapshot_update (event_snapshot eInfo) e (length effs))"

        from valid_snapshot_eInfo
        obtain eInfo' where pre: "(events E .[a]) = Some eInfo' \<and> n < length (event_effectors eInfo')"
          if  "(a, n) \<in> snapshot_entries (event_snapshot eInfo)"
          using that apply (auto simp add: valid_snapshot_def)
          by (smt case_prodD)




        show "\<exists>eInfo. (events E .[a]) = Some eInfo \<and> n < length (event_effectors eInfo)"
        proof (cases "(a, n) \<in> snapshot_entries (event_snapshot eInfo)")
          case True
          hence pre': "(events E .[a]) = Some eInfo' \<and> n < length (event_effectors eInfo')"
            using pre by simp
          thus ?thesis by simp
        next
          case False
          hence a: "a = e" and n: "n = length effs"
            using entry
            by (auto simp add: snapshot_update_def fmap_entries_def)

          have "(events E .[a]) = Some eInfo"
            by (simp add: a eInfo_def)

          moreover have "n < length (event_effectors eInfo)"
            by (simp add: n local.Cons)

          ultimately show ?thesis by force
        qed
      qed


      show "valid_event_sequence (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)]) (snapshot_update (event_snapshot eInfo) e (length effs) ) (happensBeforeE E)"
        unfolding valid_event_sequence_def proof (intro conjI)

        have len_simp: "length (event_effectors eInfo) = Suc (length effs)"
          by (simp add: local.Cons)


        show " \<forall>(ea, i)\<in>snapshot_entries (snapshot_update (event_snapshot eInfo) e (length effs)).
                \<forall>i'<i. (ea, i') \<in> set (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)])"
          using valid_seq by (auto simp add: valid_event_sequence_def snapshot_update_def fmap_entries_def len_simp)


        show "\<forall>(e', i)\<in>set (event_executionOrder eInfo @ map (Pair e) [0..<length (event_effectors eInfo)]).
         i < snapshot_num (snapshot_update (event_snapshot eInfo) e (length effs)) e'"
          using valid_seq e_notin_exec_order by (auto simp add: valid_event_sequence_def snapshot_update_def fmap_entries_def len_simp)

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

          have "snapshot_num (event_snapshot eInfo) e = 0"
            by (simp add: e_notin_snapshot fmdom'_notD)

          have "event_snapshot x2 \<le> event_snapshot eInfo"
            using a2 a4 eInfo_def local.wf snapshot_smaller by auto
          hence "snapshot_num (event_snapshot x2) e = 0"
            using `snapshot_num (event_snapshot eInfo) e = 0`
            by (metis le_zero_eq snapshot_smaller_num)
          thus "False"
            using a5 by linarith
        qed
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

lemma includedIn_snapshot_events: "includedIn e n snapshot \<Longrightarrow> e\<in>snapshot_events snapshot"
  by (auto simp add: includedIn_def fmdom'I split: option.splits)


lemma valid_snapshot_includedIn:
  assumes "valid_snapshot E snapshot"
and "includedIn e n snapshot"
shows "\<exists>eInfo. (events E.[e]) = Some eInfo \<and> n < length (event_effectors eInfo)"
  using assms  apply (auto simp add: valid_snapshot_def includedIn_def fmap_entries_def)
  by (metis (no_types, lifting) Suc_leI assms(2) includedIn_snapshot_events less_le_trans not_less0 option.case_eq_if)

lemma showCases: "\<lbrakk>x = None \<Longrightarrow> A; \<And>y. x = Some y \<Longrightarrow> P y\<rbrakk> \<Longrightarrow> (case x of None \<Rightarrow> A | Some y \<Rightarrow> P y)"
  by (auto split: option.splits)

lemma wellformed_generator:
  assumes wf: "wellFormed_impl E"
    and e: "(events E.[e]) = Some eInfo"
  shows "generator_impl (event_operation eInfo) e (event_state_pre eInfo) = (event_result eInfo, event_effectors eInfo)"
  using wf  apply (auto simp add: wellFormed_impl_def wellFormed_def wf_generator_def compose_forward_def)
  using e by auto

lemma set_maps: "set (List.maps f xs) = \<Union>( (set \<circ> f) ` set xs)"
  apply (induct xs)
  by (auto simp add: maps_simps)


lemma maps_sorted_list_of_set:
  assumes "finite S"
  shows "set (List.maps f (sorted_list_of_set S)) = \<Union>(set ` f ` S)"
  by (simp add: assms set_maps)

lemma sorted_list_of_set2_same: "sorted_list_of_set2 = sorted_list_of_set"
  by (simp add: sorted_list_of_set2_def sorted_list_of_set_def)


lemma maps_sorted_list_of_set2:
  assumes "finite S"
  shows "set (List.maps f (sorted_list_of_set2 S)) = \<Union>(set ` f ` S)"
  by (simp add: assms maps_sorted_list_of_set sorted_list_of_set2_same)

lemma wf_effector_pre:
  assumes wf: "wellFormed_impl E" 
    and e: "(events E.[e]) = Some eInfo"
  shows "event_state_pre eInfo = executeEffectors (get_effectors E (event_executionOrder eInfo)) initialState effector_impl"
  using wf e  by (auto simp add: wellFormed_impl_def wellFormed_def wf_effector_def compose_forward_def)


lemma wf_effector_post:
  assumes wf: "wellFormed_impl E" 
    and e: "(events E.[e]) = Some eInfo"
  shows"event_state_post eInfo = executeEffectors (event_effectors eInfo) (event_state_pre eInfo) effector_impl"
using wf e  by (auto simp add: wellFormed_impl_def wellFormed_def wf_effector_def compose_forward_def)

lemma filter_finite: "finite S \<Longrightarrow> finite (Set.filter P S)"
  by (auto simp add: Set.filter_def)

lemma dest_keys_finite_pre[simp]:
  assumes wf: "wellFormed_impl E"
    and e: "(events E.[e]) = Some eInfo"
  shows "finite (dest_keys (ref_state (event_state_pre eInfo) ref))"
  using wf_effector_pre[OF wf, OF e] apply (auto simp add: ref_state_def split: option.splits)
proof -

  have h: "\<lbrakk>(state_refs (executeEffectors effs S effector_impl) .[ref]) = Some x; \<And>x. (state_refs S.[ref]) = Some x \<Longrightarrow> finite (dest_keys x)\<rbrakk> \<Longrightarrow> finite (dest_keys x)" for effs x S
  proof  (induct effs arbitrary: S x)
    case Nil
    then show ?case by (auto simp add: executeEffectors_def initialState_def)
  next
    case (Cons a effs)
    from `(state_refs (executeEffectors (a # effs) S effector_impl) .[ref]) = Some x`
    show ?case 
      apply (auto simp add: executeEffectors_def initialState_def)
      apply (fold executeEffectors_def)
      apply (erule Cons.hyps)
      using `\<And>x. (state_refs S .[ref]) = Some x \<Longrightarrow> finite (dest_keys x)`
      apply (auto simp add: effector_impl_def inUse_update_def s_update_inref_def s_update_ref_def ref_state_def Set.filter_def  split: operation_effector.splits if_splits option.splits)
      done
  qed
  show "finite (dest_keys x2)"
    if c0: "event_state_pre eInfo = executeEffectors (get_effectors E (event_executionOrder eInfo)) initialState effector_impl"
      and c1: "(state_refs (executeEffectors (get_effectors E (event_executionOrder eInfo)) initialState effector_impl) .[ref]) = Some x2"
    for  x2
    using c1 proof (rule h)
    show "\<And>x. (state_refs initialState .[ref]) = Some x \<Longrightarrow> finite (dest_keys x)"
      by (simp add: initialState_def)
  qed
qed


text {* First establish some general facts: 
How does the state depend on executed effectors (depending on snapshot)
and which operations can generate which effectors... *}

lemma state_refs_dest_keys:
  assumes wf: "wellFormed_impl E"
    and state_def: "state = executeEffectors effectors initialState effector_impl"
    and effectors_def: "effectors = get_effectors E exec_order"
    and valid_event_seq: "valid_event_sequence exec_order snapshot (happensBeforeE E)"
    and snapshot_valid: "valid_snapshot E snapshot"
    and r: "(state_refs state.[r]) = Some rState"
  shows "dest_keys rState = {(x,uid) | x uid e_a oldUids. 
                 e_a \<in>\<^sub>s snapshot \<and> get_effector E e_a = effector_ref_dest_keys_assign ref x uid oldUids
                \<and> (\<nexists>e_a' x' uid' oldUids'. (e_a happened before e_a' in E) \<and> e_a' \<in>\<^sub>s snapshot \<and> get_effector E e_a = effector_ref_dest_keys_assign ref x' uid' oldUids')}"
proof auto
  show  "\<exists>aa ba. (aa, ba) \<in>\<^sub>s snapshot \<and>
                   (\<exists>oldUids. get_effector E (aa, ba) = effector_ref_dest_keys_assign ref x uid oldUids) \<and>
                   (\<forall>a b. (a, b) \<in>\<^sub>s snapshot \<longrightarrow>
                          ((aa, ba) happened before (a, b) in E) \<longrightarrow> (\<forall>x' uid' oldUids'. get_effector E (aa, ba) \<noteq> effector_ref_dest_keys_assign ref x' uid' oldUids'))"
    if x: "(x, uid) \<in> dest_keys rState"
    for x uid
  proof -




  qed

lemma safety_inv1:
  assumes wf: "wellFormed_impl E"
  shows "invariant1 E"
  unfolding invariant1_def compose_forward_def proof (rule show_all_states[OF wf])

  show "\<forall>[r\<mapsto>rState]\<in>state_refs state.
              \<forall>(k, u)\<in>dest_keys rState.
                 case k of 
                   None \<Rightarrow> True 
                 | Some inref \<Rightarrow> (
                     case state_inrefs state .[inref] of 
                         None \<Rightarrow> False 
                       | Some inrefState \<Rightarrow> (r, u) \<in> two_phase_set_get (rev_refs inrefState))"
    if c0: "state = executeEffectors effectors initialState effector_impl"
      and c1: "effectors = get_effectors E exec_order"
      and c2: "valid_event_sequence exec_order snapshot (happensBeforeE E)"
      and snapshot_valid: "valid_snapshot E snapshot"
    for  state effectors exec_order snapshot
  proof (standard+, auto split: option.splits)
    fix ref refState u inref
    assume a0: "(state_refs state .[ref]) = Some refState"
      and a1: "(Some inref, u) \<in> dest_keys refState"

    text {* Since we have an inref in the destination keys, there must be a corresponding event in the snapshot... *}

    (* from `(Some inref, u) \<in> dest_keys refState` *)
    have "case events E.[u] of
            None \<Rightarrow> False
          | Some uInfo \<Rightarrow>
           event_operation uInfo = init ref inref \<and> includedIn u 2 snapshot
         \<or> (\<exists>ref'. event_operation uInfo = assign ref ref' 
            \<and> (case state_refs (event_state_pre uInfo).[ref'] of 
                   None \<Rightarrow> False
                 | Some ref'_state \<Rightarrow> mv_reg_get1' (dest_keys ref'_state) = Some inref  \<and> includedIn u 1 snapshot ))"
        (* TODO and there does not exists an event after u overriding the assignment. *)
    proof -
      have "length exec_order  = length effectors"
        using c1 by (simp add: get_effectors_def compose_forward_def)

      text {* The only way to change the dest_keys is via a effector_ref_dest_keys_assign effector. *}
      obtain oldUids 
        where "effector_ref_dest_keys_assign ref (Some inref) u oldUids \<in> set effectors"
        sorry

      from this obtain eff_i 
        where eff_i_def: "effectors ! eff_i = effector_ref_dest_keys_assign ref (Some inref) u oldUids" and "eff_i < length effectors"
        by (meson in_set_conv_nth)

      text {* the effector must come from the exec order *}
      from this obtain eff_e eff_n
        where "exec_order ! eff_i = (eff_e, eff_n)" and "eff_i < length exec_order"
        using \<open>length exec_order = length effectors\<close> by fastforce


      text {* so the effector must be i the snapshot: *}
      have "includedIn eff_e eff_n snapshot"
        using `valid_event_sequence exec_order snapshot (happensBeforeE E)`
        apply (simp add: valid_event_sequence_def)
        using \<open>eff_i < length exec_order\<close> \<open>exec_order ! eff_i = (eff_e, eff_n)\<close> includedIn_def nth_mem by fastforce

      text {* The event eff_e must exist. *}
      obtain eff_e_info where eff_e_info_def: "(events E.[eff_e]) = Some eff_e_info"
        using `includedIn eff_e eff_n snapshot` snapshot_valid
        apply (auto simp add: valid_snapshot_def includedIn_def fmap_entries_def split: nat.splits option.splits)
        by (meson fmdom'I)

      text {* The event eff_e must have generated the effect. *}
      have eff_e_info_effectors: "event_effectors eff_e_info ! eff_n = effector_ref_dest_keys_assign ref (Some inref) u oldUids"
        using `effectors = get_effectors E exec_order` eff_i_def by (auto simp add: get_effectors_def compose_forward_def \<open>eff_i < length exec_order\<close> \<open>exec_order ! eff_i = (eff_e, eff_n)\<close> eff_e_info_def)

      have eff_n_range: "eff_n < length (event_effectors eff_e_info)"
        using `includedIn eff_e eff_n snapshot` `valid_snapshot E snapshot` eff_e_info_def
        apply (auto simp add: includedIn_def valid_snapshot_def fmap_entries_def split: option.splits)
        using \<open>includedIn eff_e eff_n snapshot\<close> snapshot_valid valid_snapshot_includedIn by fastforce

      find_theorems "events E .[u]"

      have eff_e_info_effectors_set: "effector_ref_dest_keys_assign ref (Some inref) u oldUids \<in> set (event_effectors eff_e_info)"
        using eff_e_info_effectors eff_n_range nth_inset by fastforce


      have dest_keys_fin[simp]: "finite (dest_keys (ref_state (event_state_pre eff_e_info) x))" for x
        using eff_e_info_def local.wf by auto


      have "u = eff_e"
        using eff_e_info_effectors_set wellformed_generator[OF wf, OF eff_e_info_def, symmetric]
        by (auto simp add: generator_impl_def compose_forward_def inref_inuse_enable_def outref_update_def return_def ref_reset_targets_def Let_def 
                inref_rev_refs_add_def inref_rev_refs_remove_def  ref_dest_keys_assign_def maps_sorted_list_of_set2 skip_def
                split: operation.splits option.splits)

      text {* Now distinguish the cases how the effect could have been generated via case distinction over the different operations. *}
      show " case events E .[u] of None \<Rightarrow> False
            | Some uInfo \<Rightarrow>
                event_operation uInfo = init ref inref \<and> includedIn u 2 snapshot \<or>
                (\<exists>ref'. event_operation uInfo = assign ref ref' \<and>
                        (case state_refs (event_state_pre uInfo) .[ref'] of None \<Rightarrow> False | Some ref'_state \<Rightarrow> mv_reg_get1' (dest_keys ref'_state) = Some inref \<and> includedIn u 1 snapshot)) "
      proof (simp add: \<open>u = eff_e\<close> eff_e_info_def)
        show "event_operation eff_e_info = init ref inref \<and> includedIn eff_e 2 snapshot 
             \<or> (\<exists>ref'. event_operation eff_e_info = assign ref ref' \<and>
                  (case state_refs (event_state_pre eff_e_info) .[ref'] of 
                         None \<Rightarrow> False 
                       | Some ref'_state \<Rightarrow> mv_reg_get1' (dest_keys ref'_state) = Some inref \<and> includedIn u 1 snapshot))"



    show "False" if "(state_inrefs state .[inref]) = None"

      sorry
    show "(ref, u) \<in> two_phase_set_get (rev_refs x2a)" if "(state_inrefs state .[inref]) = Some x2a" for x2a
      sorry


  qed

end