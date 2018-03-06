(*<*)
theory system_model
  imports fmap_functions
    system_model_types
    standard_crdts
    snapshot
begin 
(*>*)

section {* System model *}

text {*
We parameterize our Model based on four type parameters:

 - The operation type describes which operations can be executed via the API.
 - The operation-result type determines what are possible results of operations.
 - The operation-effector type describes, which messages can be sent to other replicas as effectors.
 - The state type describes the state at each replica.

*}

record ('operation, 'operation_result, 'operation_effector, 'state) eventInfo =
  event_operation :: "'operation"
  event_result :: 'operation_result
  event_effectors :: "'operation_effector list" (* downstream messages generated here *)
  event_executionOrder :: "(event \<times> nat) list" (* execution order: event, number of effector  *)
  event_state_pre :: 'state (* state before executing the event *)
  event_state_post :: 'state (* state after executing the event *)
  event_snapshot :: snapshot  (* events that happened before and how many of their effectors are included in the snapshot *)
                          
record ('operation, 'operation_result, 'operation_effector, 'state) execution =
  events :: "(event, ('operation, 'operation_result, 'operation_effector, 'state) eventInfo) fmap"
  
abbreviation "events' E \<equiv> fmap_entries (events E)"
abbreviation "eventsIds E \<equiv> fmdom' (events E)"

definition happensBeforeP :: "(event\<times>nat) \<Rightarrow> (event\<times>nat) \<Rightarrow> (event \<rightharpoonup> snapshot) \<Rightarrow> bool" ("_ happened before _ with _" [25,25,25]25) where
"x happened before y with snapshots \<equiv> 
   if fst x = fst y then snd x < snd y else
   case snapshots (fst y) of 
     None \<Rightarrow> False 
   | Some snapshot \<Rightarrow> includedIn (fst x) (snd x) snapshot"                 

definition happensBeforeP2 :: "(event\<times>nat) \<Rightarrow> (event\<times>nat) \<Rightarrow> ('operation, 'operation_result, 'operation_effector, 'state) execution \<Rightarrow> bool" ("_ happened before _ in _" [25,25,25]25) where
"x happened before y in E \<equiv> 
   if fst x = fst y then snd x < snd y else
   case (events E).[fst y] of 
     None \<Rightarrow> False 
   | Some yInfo \<Rightarrow> includedIn (fst x) (snd x) (event_snapshot yInfo)"  

lemma happensBeforeP2_def2:
"(x happened before y in E) \<longleftrightarrow> (x happened before y with (\<lambda>e. map_option event_snapshot ((events E).[e])))"
  by (auto simp add: happensBeforeP_def happensBeforeP2_def split: option.splits)

definition "happensBeforeE E x y \<equiv> x happened before y in E"


type_synonym ('operation, 'operation_result, 'operation_effector, 'state) generator_function = "('operation \<Rightarrow> uid \<Rightarrow> 'state \<Rightarrow> 'operation_result \<times> ('operation_effector list))"
type_synonym ('operation_effector, 'state) effector_function = "('operation_effector \<Rightarrow> 'state \<Rightarrow> 'state)"



definition "wf_causallyConsistent E \<equiv> 
\<forall>(e,eInfo)\<in>events' E. \<forall>e'\<in>snapshot_events(event_snapshot eInfo). 
  case (events E).[e'] of
      None \<Rightarrow> False
    | Some eInfo' \<Rightarrow> event_snapshot eInfo' \<le> event_snapshot eInfo
"

definition "wf_acyclic E \<equiv> 
\<forall>(e,eInfo)\<in>events' E.  ((snapshot_map (event_snapshot eInfo)).[e]) = None
"



definition wf_generator :: "('operation, 'operation_result, 'operation_effector, 'state) execution \<Rightarrow> ('operation, 'operation_result, 'operation_effector, 'state)generator_function \<Rightarrow> bool" where
"wf_generator execution gen \<equiv>
events execution |> fmpred (\<lambda>e eInfo.
  gen (event_operation eInfo)  e (event_state_pre eInfo) = (event_result eInfo, event_effectors eInfo)) 
"



definition executeEffectors :: "'operation_effector list \<Rightarrow> 'state \<Rightarrow> ('operation_effector, 'state) effector_function \<Rightarrow> 'state" where
"executeEffectors effectors initial eff \<equiv> foldl (\<lambda>s e. eff e s) initial effectors "

definition sorted_partial :: "'a list \<Rightarrow> 'a rel \<Rightarrow> bool" where
"sorted_partial list rel \<equiv> (\<forall>j<length list. \<forall>i<j. (list!j, list!i)\<notin>rel)"

definition sorted_partial' :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"sorted_partial' list rel \<equiv> (\<forall>j<length list. \<forall>i<j. \<not>rel (list!j) (list!i))"



definition
"valid_event_sequence eventList snapshot hb \<equiv> 
   (\<forall>(e,i)\<in>snapshot_entries snapshot.\<forall>i'<i. (e,i')\<in>set eventList )
 \<and> (\<forall>(e,i)\<in>set eventList. i < snapshot_num snapshot e)
 \<and> sorted_partial' eventList hb"


definition "previous_events hb e \<equiv> fst ` Set.filter (\<lambda>(x,y). y = e \<and> x\<noteq>e) hb"  (* or {e'.  e'\<noteq>e \<and> (e',e)\<in>hb}*)
definition "downwards_closure S E \<equiv> S \<union>  (\<Union>e\<in>S. case (events E).[e] of None \<Rightarrow> {} | Some info \<Rightarrow> snapshot_events (event_snapshot info))"
definition "parallel_closure S A hb \<equiv> Set.filter (\<lambda>x. x\<in>S \<or> (\<exists>y\<in>S. \<not>hb y x)) A"


value "parallel_closure {1,2::int} {1,2,3,4,5} (\<lambda>x y. (x,y)\<in> {(2,3), (2,4), (1,4), (1,1), (2,2), (3,3), (4,4), (5,5)}\<^sup>+)"

value "parallel_closure {} {1::int,2,3,4,5} (\<lambda>x y. (x,y)\<in> {(2,3), (1,4), (1,1), (2,2), (3,3), (4,4), (5,5)}\<^sup>+)"


export_code previous_events in Haskell


definition 
"wf_correct_execution_lists execution \<equiv> 
events execution |> fmpred (\<lambda>e eInfo. valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBeforeE execution))
"

export_code wf_correct_execution_lists

find_consts "('a \<Rightarrow> 'b list) => 'a list => 'b list"

definition get_effectors :: "('operation, 'operation_result, 'operation_effector, 'state) execution \<Rightarrow> (event \<times> nat) list \<Rightarrow> 'operation_effector list" where
"get_effectors execution exec_order \<equiv> exec_order |> map (\<lambda>(e',i'). (event_effectors ((events execution)![e'])) ! i')"

definition wf_effector :: "('operation, 'operation_result, 'operation_effector, 'state)execution \<Rightarrow> 'state \<Rightarrow> ('operation_effector, 'state) effector_function \<Rightarrow> bool" where
"wf_effector execution initS eff \<equiv>
events execution |> fmpred (\<lambda>e eInfo. 
  let effectors = get_effectors execution (event_executionOrder eInfo)
  in
  event_state_pre eInfo = executeEffectors effectors initS eff
  \<and> event_state_post eInfo = executeEffectors (event_effectors eInfo) (event_state_pre eInfo) eff)
"

definition 
"wf_localPreconditions execution localPred \<equiv>
events execution |> fmpred (\<lambda>e eInfo.  localPred (event_operation eInfo) (event_state_pre eInfo))
"

text {*
A snapshot S is stable in an execution E, if the execution does not contain any event 
which has a snapshot concurrent to snapshot S.
*}

definition stable :: "snapshot \<Rightarrow> ('operation, 'operation_result, 'operation_effector, 'state) execution \<Rightarrow> bool" where
"stable S E \<equiv> \<not>(\<exists>(e,eInfo)\<in>fmap_entries (events E). event_snapshot eInfo \<parallel> S)"

definition 
"wf_stablePreconditions execution pred \<equiv>
events execution |> fmpred (\<lambda>e eInfo. 
    case pred (event_operation eInfo) of 
       None \<Rightarrow> True
     | Some cond \<Rightarrow> 
        stable (event_snapshot eInfo) execution
      \<and> cond (event_state_pre eInfo))
"


definition wellFormed :: "('operation, 'operation_result, 'operation_effector, 'state) execution \<Rightarrow> 'state \<Rightarrow> ('operation, 'operation_result, 'operation_effector, 'state) generator_function \<Rightarrow> ( 'operation_effector, 'state) effector_function \<Rightarrow> ('operation \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> ('operation \<rightharpoonup> 'state \<Rightarrow> bool) \<Rightarrow> bool"
where
"wellFormed execution initS gen eff localPre pre \<equiv>
    wf_causallyConsistent execution 
  \<and> wf_acyclic execution
  \<and> wf_correct_execution_lists execution
  \<and> wf_generator execution gen
  \<and> wf_effector execution initS eff
  \<and> wf_localPreconditions execution localPre
  \<and> wf_stablePreconditions execution pre"





end