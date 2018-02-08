theory system_model
imports fmap_functions
begin 


section {* System model *}

datatype event = D_event (event_number:int)
datatype inref = D_inref (inref_number:int)
datatype ref = D_ref (ref_number:int)
datatype antidoteKey =  D_antidoteKey int | NullKey

instantiation event :: linorder begin
definition "less_eq_event x y \<equiv> event_number x \<le> event_number y"
definition "less_event x y \<equiv> event_number x < event_number y"
instance by (standard, auto simp add: less_eq_event_def less_event_def event.expand)
end

instantiation inref :: linorder begin
definition "less_eq_inref x y \<equiv> inref_number x \<le> inref_number y"
definition "less_inref x y \<equiv> inref_number x < inref_number y"
instance by (standard, auto simp add: less_eq_inref_def less_inref_def inref.expand)
end

instantiation ref :: linorder begin
definition "less_eq_ref x y \<equiv> ref_number x \<le> ref_number y"
definition "less_ref x y \<equiv> ref_number x < ref_number y"
instance by (standard, auto simp add: less_eq_ref_def less_ref_def ref.expand)
end

instantiation antidoteKey :: linorder begin
definition "less_antidoteKey1 x y \<equiv> case x of 
  NullKey \<Rightarrow> y \<noteq> NullKey
| D_antidoteKey i \<Rightarrow> (case y of
     NullKey \<Rightarrow> False
   | D_antidoteKey j \<Rightarrow> i < j)
"
definition "less_antidoteKey x y \<equiv> less_antidoteKey1 x y"
definition "less_eq_antidoteKey x y \<equiv> x=y \<or> less_antidoteKey1 x y "
instance 
  apply standard
      apply (auto simp add: less_antidoteKey_def less_eq_antidoteKey_def less_antidoteKey1_def  split: antidoteKey.splits ref.splits inref.splits)
  done
end



instantiation prod :: (linorder,linorder) linorder begin
definition "less_prod x y \<equiv> fst x < fst y \<or> fst x = fst y \<and> snd x < snd y"
definition "less_eq_prod x y \<equiv> fst x < fst y \<or> fst x = fst y \<and> snd x \<le> snd y"
instance 
  apply standard
      apply (auto simp add: less_prod_def less_eq_prod_def)
  done
end

instantiation option :: (linorder) linorder begin
definition "less_option x y \<equiv> case x of None \<Rightarrow> y\<noteq>None | Some x' \<Rightarrow> (case y of None \<Rightarrow> False | Some y' \<Rightarrow> x' < y')"
definition "less_eq_option x y \<equiv> case x of None \<Rightarrow> True | Some x' \<Rightarrow> (case y of None \<Rightarrow> False | Some y' \<Rightarrow> x' \<le> y')"
instance 
  apply standard
      apply (auto simp add: less_option_def less_eq_option_def split: option.splits)
  done
end

definition fmap_entries :: "('k, 'v) fmap \<Rightarrow> ('k\<times>'v) set" where
"fmap_entries m \<equiv> (\<lambda>k. (k, m![k])) ` fmdom' m" 


lemma fmap_entries_forall[code_abbrev]: "fmpred P m \<longleftrightarrow> (\<forall>(k,v)\<in>fmap_entries m. P k v)"
  apply (auto simp add: fmap_entries_def)
  apply (meson fmdom'_notI fmpredD option.exhaust_sel)
  by (metis fmdom'I fmpredI option.sel)

lemma fmap_entries_exists[code_abbrev]: "(\<not>fmpred (\<lambda>k v. \<not>P k v) m) \<longleftrightarrow> (\<exists>(k,v)\<in>fmap_entries m. P k v)"
  by (subst fmap_entries_forall, auto)


definition orElse (infixr "orElse" 25) where
"x orElse y \<equiv> (case x of Some a \<Rightarrow> a | None \<Rightarrow> y)"

(* using event-IDs to model unique identifiers *)
type_synonym uid = event

datatype operation = 
    init ref inref
  | assign ref ref
  | deref ref
  | may_delete inref "ref list"
  | reset_inref inref
  | reset_ref ref
 (* TODO resolve *)

datatype operation_effector = 
    effector_inref_inuse_enable inref
  | effector_inref_rev_refs_add inref ref uid
  | effector_inref_rev_refs_rem inref ref uid
  | effector_ref_dest_keys_assign ref "inref option" uid "uid set"
    (*effector_init ref inref uid (f_dest_uids:"uid set")
  | effector_assign ref ref
  | effector_deref ref
  | effector_may_delete inref "ref list"
  | effector_reset_inref inref
  | effector_reset_ref ref
*)

datatype operation_result =
    deref_result "antidoteKey option"
  | no_result
  | may_delete_result bool

type_synonym 'a mv_register_state = "('a \<times> uid) set"
  
type_synonym 'a two_phase_set_state = "'a set \<times> 'a set"  

record ref_state =
  object_key :: "antidoteKey"
  dest_keys :: "inref option mv_register_state"

record inref_state =
  inref_object_key :: "antidoteKey"
  rev_refs :: "(ref \<times> uid) two_phase_set_state"
  inUse :: bool

record state =
  state_refs :: "(ref, ref_state) fmap"
  state_inrefs :: "(inref, inref_state) fmap"

datatype snapshot = Snapshot (snapshot_map: "(event,nat) fmap")

abbreviation "snapshot_events s \<equiv> fmdom' (snapshot_map s)"
abbreviation "snapshot_entries s \<equiv> fmap_entries (snapshot_map s)"
abbreviation "snapshot_num s e \<equiv> case (snapshot_map s).[e] of Some n \<Rightarrow> Suc n | None \<Rightarrow> 0"
definition includedIn where
"includedIn e n snapshot \<equiv> n < snapshot_num snapshot e"

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


record eventInfo =
  event_operation :: "operation"
  event_result :: operation_result
  event_effectors :: "operation_effector list"
  event_executionOrder :: "event list"
  event_state_pre :: state (* state before executing the event *)
  event_state_post :: state (* state after executing the event *)
  event_snapshot :: snapshot  (* events that happened before and how many of their effectors are included in the snapshot *)
                          
record execution =
  events :: "(event, eventInfo) fmap"
  



abbreviation "events' E \<equiv> fmap_entries (events E)"
abbreviation "eventsIds E \<equiv> fmdom' (events E)"

definition happensBeforeP :: "event \<Rightarrow> event \<Rightarrow> execution \<Rightarrow> bool" ("_ happened before _ in _" [25,25,25]25) where
"x happened before y in E \<equiv> 
   case (events E).[y] of 
     None \<Rightarrow> False 
   | Some yInfo \<Rightarrow> (
      case (events E).[x] of
       None \<Rightarrow> False 
     | Some xInfo \<Rightarrow> includedIn x (length (event_effectors xInfo)) (event_snapshot yInfo)
  ) "

definition happensBefore :: "execution \<Rightarrow> event rel"  where
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

type_synonym generator_function = "(operation \<Rightarrow> uid \<Rightarrow> state \<Rightarrow> operation_result \<times> (operation_effector list))"
type_synonym effector_function = "(operation_effector \<Rightarrow> state \<Rightarrow> state)"

definition compose_forward (infixl "|>" 25) where
"x |> f \<equiv> f x"

value "(1::int) |> op+ 1 |> op* 2"

definition "wf_causallyConsistent E \<equiv> 
\<forall>(e,eInfo)\<in>events' E. \<forall>(e',i)\<in>snapshot_entries(event_snapshot eInfo). 
  case (events E).[e'] of
      None \<Rightarrow> False
    | Some eInfo' \<Rightarrow> event_snapshot eInfo' \<le> event_snapshot eInfo
"

definition "partial_order_on2 S R \<equiv> 
fst ` R \<subseteq>  S
\<and> snd ` R \<subseteq>  S
\<and> (\<forall>x\<in>S. (x,x)\<in>R)
\<and> R\<^sup>+ \<subseteq> R
\<and> (\<forall>x\<in>S. \<forall>y\<in>S. (x,y)\<in>R \<and> (y,x)\<in>R \<longrightarrow> x = y)
"

lemma partial_order_on2_eq: "partial_order_on2 S R = partial_order_on S R"
  apply (auto simp add: partial_order_on2_def partial_order_on_def preorder_on_def refl_on_domain refl_onD antisymD)
    apply (auto simp add: refl_on_def)[1]
   apply (auto simp add: trans_def)[1]
  apply (auto simp add: antisym_def)[1]
  by (metis fst_conv image_subset_iff)


export_code wf_causallyConsistent in Haskell



definition wf_generator :: "execution \<Rightarrow> generator_function \<Rightarrow> bool" where
"wf_generator execution gen \<equiv>
events execution |> fmpred (\<lambda>e eInfo.
  gen (event_operation eInfo)  e (event_state_pre eInfo) = (event_result eInfo, event_effectors eInfo)) 
"



definition executeEffectors :: "operation_effector list \<Rightarrow> state \<Rightarrow> effector_function \<Rightarrow> state" where
"executeEffectors effectors initial eff \<equiv> foldl (\<lambda>s e. eff e s) initial effectors "

definition sorted_partial :: "'a list \<Rightarrow> 'a rel \<Rightarrow> bool" where
"sorted_partial list rel \<equiv> (\<forall>j<length list. \<forall>i<j. (list!j, list!i)\<notin>rel)"


definition
"valid_event_sequence eventList eventSet hb \<equiv> 
set eventList = eventSet \<and> distinct eventList \<and> sorted_partial eventList hb"


definition "previous_events hb e \<equiv> fst ` Set.filter (\<lambda>(x,y). y = e \<and> x\<noteq>e) hb"  (* or {e'.  e'\<noteq>e \<and> (e',e)\<in>hb}*)
definition "downwards_closure S E \<equiv> S \<union>  (\<Union>e\<in>S. case (events E).[e] of None \<Rightarrow> {} | Some info \<Rightarrow> snapshot_events (event_snapshot info))"
definition "parallel_closure S A hb \<equiv> Set.filter (\<lambda>x. x\<in>S \<or> (\<exists>y\<in>S. (y,x)\<notin>hb)) A"

value "parallel_closure {1,2::int} {1,2,3,4,5} ({(2,3), (2,4), (1,4), (1,1), (2,2), (3,3), (4,4), (5,5)}\<^sup>+)"

value "parallel_closure {} {1::int,2,3,4,5} ({(2,3), (1,4), (1,1), (2,2), (3,3), (4,4), (5,5)}\<^sup>+)"


export_code previous_events in Haskell

definition 
"wf_correct_execution_lists execution \<equiv> 
events execution |> fmpred (\<lambda>e eInfo. valid_event_sequence (event_executionOrder eInfo) (previous_events (happensBefore execution) e) (happensBefore execution))
"

export_code wf_correct_execution_lists

find_consts "('a \<Rightarrow> 'b list) => 'a list => 'b list"

definition wf_effector :: "execution \<Rightarrow> state \<Rightarrow> effector_function \<Rightarrow> bool" where
"wf_effector execution initS eff \<equiv>
events execution |> fmpred (\<lambda>e eInfo. 
  let effectors = event_executionOrder eInfo |> List.maps (\<lambda>e'. 
      case (events execution).[e'] of Some eInfo' \<Rightarrow> take (snapshot_num (event_snapshot eInfo) e') (event_effectors eInfo') | None \<Rightarrow> [])
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


definition wellFormed :: "execution \<Rightarrow> state \<Rightarrow> generator_function \<Rightarrow> effector_function \<Rightarrow> (operation \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> (operation \<rightharpoonup> state \<Rightarrow> bool) \<Rightarrow> bool"
where
"wellFormed execution initS gen eff localPre pre \<equiv>
    wf_causallyConsistent execution 
  \<and> wf_correct_execution_lists execution
  \<and> wf_generator execution gen
  \<and> wf_effector execution initS eff
  \<and> wf_localPreconditions execution localPre
  \<and> wf_stablePreconditions execution pre"



definition initialState :: state where 
"initialState \<equiv> \<lparr>
  state_refs = fmempty,
  state_inrefs = fmempty
 \<rparr>"                                              


end