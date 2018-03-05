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

definition happensBeforeP :: "event \<Rightarrow> event \<Rightarrow> ('operation, 'operation_result, 'operation_effector, 'state) execution \<Rightarrow> bool" ("_ happened before _ in _" [25,25,25]25) where
"x happened before y in E \<equiv> 
   case (events E).[y] of 
     None \<Rightarrow> False 
   | Some yInfo \<Rightarrow> (
      case (events E).[x] of
       None \<Rightarrow> False 
     | Some xInfo \<Rightarrow> includedIn x (length (event_effectors xInfo)) (event_snapshot yInfo)
  ) "

definition happensBefore :: "('operation, 'operation_result, 'operation_effector, 'state) execution \<Rightarrow> event rel"  where
"happensBefore E \<equiv> {(x,y). x happened before y in E}"


lemma happensBefore_code[code]:
"happensBefore E = \<Union> ((\<lambda>(e,eInfo). (Set.filter (\<lambda>e'. e' happened before e in E) (snapshot_events (event_snapshot eInfo))) \<times> {e} )  ` fmap_entries (events E))"
  apply (auto simp add: happensBefore_def happensBeforeP_def  split: option.splits)
  apply (rule_tac x="(b,y)" in bexI)
  apply (auto simp add: fmap_entries_def fmdom'I image_iff)
  using fmlookup_dom'_iff includedIn_def by fastforce


lemma in_happensBefore_code[code_abbrev]: "(x happened before y in E) \<longleftrightarrow> (x,y)\<in>happensBefore E"
  by (auto simp add: happensBefore_def happensBeforeP_def fmdom'I split: option.splits)

export_code happensBefore in Haskell


definition "foo x y E \<equiv> \<forall>(e,ei)\<in>fmap_entries(events E). True" 

export_code foo in Haskell

type_synonym ('operation, 'operation_result, 'operation_effector, 'state) generator_function = "('operation \<Rightarrow> uid \<Rightarrow> 'state \<Rightarrow> 'operation_result \<times> ('operation_effector list))"
type_synonym ('operation_effector, 'state) effector_function = "('operation_effector \<Rightarrow> 'state \<Rightarrow> 'state)"



definition "wf_causallyConsistent E \<equiv> 
\<forall>(e,eInfo)\<in>events' E. \<forall>(e',i)\<in>snapshot_entries(event_snapshot eInfo). 
  case (events E).[e'] of
      None \<Rightarrow> False
    | Some eInfo' \<Rightarrow> event_snapshot eInfo' \<le> event_snapshot eInfo
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

definition sorted_partial_i :: "('a \<times> nat) list \<Rightarrow> 'a rel \<Rightarrow> bool" where
"sorted_partial_i list rel \<equiv> (\<forall>j<length list. \<forall>i<j. if fst (list!j) = fst (list!i) then snd (list!i) < snd (list!j) else (fst (list!j), fst (list!i))\<notin>rel)"





definition
"valid_event_sequence eventList snapshot hb \<equiv> 
(\<forall>(e,i)\<in>snapshot_entries snapshot.\<forall>i'<i. (e,i')\<in>set eventList ) \<and> sorted_partial_i eventList hb"


definition "previous_events hb e \<equiv> fst ` Set.filter (\<lambda>(x,y). y = e \<and> x\<noteq>e) hb"  (* or {e'.  e'\<noteq>e \<and> (e',e)\<in>hb}*)
definition "downwards_closure S E \<equiv> S \<union>  (\<Union>e\<in>S. case (events E).[e] of None \<Rightarrow> {} | Some info \<Rightarrow> snapshot_events (event_snapshot info))"
definition "parallel_closure S A hb \<equiv> Set.filter (\<lambda>x. x\<in>S \<or> (\<exists>y\<in>S. (y,x)\<notin>hb)) A"

value "parallel_closure {1,2::int} {1,2,3,4,5} ({(2,3), (2,4), (1,4), (1,1), (2,2), (3,3), (4,4), (5,5)}\<^sup>+)"

value "parallel_closure {} {1::int,2,3,4,5} ({(2,3), (1,4), (1,1), (2,2), (3,3), (4,4), (5,5)}\<^sup>+)"


export_code previous_events in Haskell


definition 
"wf_correct_execution_lists execution \<equiv> 
events execution |> fmpred (\<lambda>e eInfo. valid_event_sequence (event_executionOrder eInfo) (event_snapshot eInfo) (happensBefore execution))
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


definition 
"closed_concurrent e hb E \<equiv> \<forall>e1\<in>E. e1\<noteq>e \<and> (e1, e)\<in>hb \<longrightarrow> (\<forall>e2\<in>E.(e1,e2)\<notin>hb \<and> (e2,e1)\<notin>hb \<longrightarrow> (e2, e)\<in>hb)"

text {* Define that event e has received all effectors from its dependencies. *}
definition 
"fullSnapshot e E \<equiv> 
  case (events E).[e] of 
      None \<Rightarrow> False
    | Some info \<Rightarrow> (\<forall>(e',n)\<in>snapshot_entries (event_snapshot info). 
        case (events E).[e'] of
            None \<Rightarrow> False
          | Some info' \<Rightarrow> n \<ge> length (event_effectors info'))"

definition
"stable e E \<equiv> closed_concurrent e (happensBefore E) (fmdom' (events E))
            \<and> fullSnapshot e E  "


definition 
"wf_stablePreconditions execution pred \<equiv>
events execution |> fmpred (\<lambda>e eInfo. 
    case pred (event_operation eInfo) of 
       None \<Rightarrow> True
     | Some cond \<Rightarrow> 
        stable e execution
      \<and> cond (event_state_pre eInfo))
"

export_code closed_concurrent in Haskell
export_code wf_stablePreconditions in Haskell


definition wellFormed :: "('operation, 'operation_result, 'operation_effector, 'state) execution \<Rightarrow> 'state \<Rightarrow> ('operation, 'operation_result, 'operation_effector, 'state) generator_function \<Rightarrow> ( 'operation_effector, 'state) effector_function \<Rightarrow> ('operation \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> ('operation \<rightharpoonup> 'state \<Rightarrow> bool) \<Rightarrow> bool"
where
"wellFormed execution initS gen eff localPre pre \<equiv>
    wf_causallyConsistent execution 
  \<and> wf_correct_execution_lists execution
  \<and> wf_generator execution gen
  \<and> wf_effector execution initS eff
  \<and> wf_localPreconditions execution localPre
  \<and> wf_stablePreconditions execution pre"





end