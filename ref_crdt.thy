theory ref_crdt
  imports Main
   "sorted_list"
    "~~/src/HOL/Library/Finite_Map"
    "~~/src/HOL/Library/Open_State_Syntax"
    "~~/src/HOL/Library/Code_Target_Numeral"
begin

(*<*)
abbreviation lookupsyntax ("_ .[_]"[25,25]25) where
"m.[x] \<equiv> fmlookup m x"

abbreviation lookupsyntax2 ("_ ![_]"[25,25]25) where
"m![x] \<equiv> the (fmlookup m x)"

(*>*)

section {* System model *}

datatype event = D_event (event_number:int)
datatype inref = D_inref (inref_number:int)
datatype ref = D_ref (ref_number:int)
datatype antidoteKey =  D_antidoteKey int (*D_antidoteKey_ref (key_ref:ref) | D_antidoteKey_inref (key_inref:inref)*) | NullKey

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


definition run :: "state \<Rightarrow> (state \<Rightarrow> state) list \<Rightarrow> state"  where
"run start actions \<equiv> foldl (\<lambda>s f. f s) start actions"

fun two_phase_set_add where 
"two_phase_set_add (A,R) (x, uid) = (insert (x,uid) A, R)"

fun two_phase_set_remove where 
"two_phase_set_remove (A,R) (x, uid) = (A,insert (x,uid) R)"

term fmlookup
find_consts "('a, 'b) fmap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" 


definition return :: "'a \<Rightarrow> operation_effector list \<Rightarrow> ('a \<times> operation_effector list)" where
"return r l = (r,l)"

definition skip :: "operation_effector list \<Rightarrow> operation_effector list" where
"skip \<equiv> id"

definition forEach :: "'a list \<Rightarrow> ('a \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list) \<Rightarrow>operation_effector list \<Rightarrow> operation_effector list" where
"forEach list f effs \<equiv> foldl (\<lambda>es x. f x es) effs list"

text {* forEach loop with state:  *}

definition forEachS :: "'a list \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> operation_effector list \<Rightarrow> ('b \<times> operation_effector list)) \<Rightarrow>operation_effector list \<Rightarrow> operation_effector list" where
"forEachS list s f effs \<equiv> foldl (\<lambda>(s,es) x. f x s es) (s,effs) list |> snd"

definition set_forEach :: "('a::linorder) set \<Rightarrow> ('a \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list) \<Rightarrow>operation_effector list \<Rightarrow> operation_effector list" where
"set_forEach S \<equiv> forEach (sorted_list_of_set2 S)"

definition set_forEachS :: "('a::linorder) set \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> operation_effector list \<Rightarrow> ('b \<times> operation_effector list)) \<Rightarrow>operation_effector list \<Rightarrow> operation_effector list" where
"set_forEachS S \<equiv> forEachS (sorted_list_of_set2 S)"

definition inref_inuse_enable :: "inref \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list" where 
"inref_inuse_enable inref list = list@[effector_inref_inuse_enable inref]"

definition inref_rev_refs_add :: "inref \<Rightarrow> ref \<Rightarrow> uid \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list" where 
"inref_rev_refs_add inref elem uid list = list@[effector_inref_rev_refs_add inref elem uid]"

definition inref_rev_refs_remove :: "inref \<Rightarrow> ref \<Rightarrow> uid \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list" where 
"inref_rev_refs_remove inref elem uid list = list@[effector_inref_rev_refs_rem inref elem uid]"

definition ref_state :: "state \<Rightarrow> ref \<Rightarrow> ref_state" where
"ref_state state ref \<equiv> case  (state_refs state).[ref] of 
    Some s \<Rightarrow> s
  | None \<Rightarrow> \<lparr> object_key = D_antidoteKey (ref_number ref),  dest_keys = {}\<rparr>"

definition ref_get_object_key :: "state \<Rightarrow> ref \<Rightarrow> antidoteKey" where
"ref_get_object_key state ref \<equiv> object_key (ref_state state ref)" 

definition inref_state :: "state \<Rightarrow> inref \<Rightarrow> inref_state" where
"inref_state state inref \<equiv> case  (state_inrefs state).[inref] of 
    Some s \<Rightarrow> s
  | None \<Rightarrow> \<lparr> inref_object_key = D_antidoteKey (inref_number inref), rev_refs = ({},{}), inUse = False\<rparr>"

definition inref_get_object_key :: "state \<Rightarrow> inref \<Rightarrow> antidoteKey" where
"inref_get_object_key state ref \<equiv> inref_object_key (inref_state state ref)" 

definition ref_dest_keys_assign :: "ref \<Rightarrow> inref option \<Rightarrow> uid \<Rightarrow> state \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list" where 
"ref_dest_keys_assign ref key uid state list \<equiv> list@[effector_ref_dest_keys_assign ref key uid (snd` dest_keys (ref_state state ref))]"



definition s_update_inref :: "inref \<Rightarrow> (inref_state \<Rightarrow> inref_state) \<Rightarrow> state \<Rightarrow> state" where
"s_update_inref inref f S \<equiv> S\<lparr>state_inrefs := fmupd inref (f (inref_state S inref)) (state_inrefs S)\<rparr>"


definition s_update_ref :: "ref \<Rightarrow> (ref_state \<Rightarrow> ref_state) \<Rightarrow> state \<Rightarrow> state" where
"s_update_ref ref f S \<equiv> S\<lparr>state_refs := fmupd ref (f (ref_state S ref)) (state_refs S)\<rparr>"

definition mv_reg_getall :: "'a mv_register_state \<Rightarrow> 'a set" where
"mv_reg_getall s = (fst ` s)"

definition mv_reg_get1 :: "'a::linorder mv_register_state \<Rightarrow> 'a \<Rightarrow> 'a" where
"mv_reg_get1 s d \<equiv> let all = mv_reg_getall s in if all = {} then d else Max (mv_reg_getall s)"

definition mv_reg_get1' where
"mv_reg_get1' s \<equiv> mv_reg_get1 s None"

definition mv_reg_count :: "'a mv_register_state \<Rightarrow> nat" where
"mv_reg_count s = card (mv_reg_getall s)"

definition two_phase_set_get :: "'a two_phase_set_state \<Rightarrow> 'a set" where
"two_phase_set_get s \<equiv> fst s - snd s"

definition may_delete_check :: "state \<Rightarrow> inref \<Rightarrow> ref set \<Rightarrow> bool" where
"may_delete_check state inref last_refs \<equiv> 
   (*let last_keypairs :: (ref \<times> uid) set = \<Union> ((\<lambda>r. dest_keys (ref_state state r)) ` last_refs) in *)
   (fst ` two_phase_set_get (rev_refs (inref_state state inref))) = last_refs"

subsection {* Implementation *}

text {* We now present the implementation of the reference CRDT: *}

definition precondition_impl :: "operation \<rightharpoonup> state \<Rightarrow> bool" where
"precondition_impl opr \<equiv> case opr of 
    init ref inref \<Rightarrow> Some (\<lambda>state. \<not> inUse (inref_state state inref))
  | assign x y \<Rightarrow> None
  | deref ref \<Rightarrow> None
  | may_delete inref remaining \<Rightarrow> Some (\<lambda>s. True)
  | reset_inref inref \<Rightarrow> Some (\<lambda>state. may_delete_check state inref {})
  | reset_ref ref \<Rightarrow> None
"

definition localPrecondition_impl :: "operation \<Rightarrow> state \<Rightarrow> bool" where
"localPrecondition_impl opr S \<equiv> case opr of 
    init ref inref \<Rightarrow> True
  | assign x y \<Rightarrow> 
      mv_reg_count (dest_keys (ref_state S y)) = 1
    \<and> mv_reg_get1' (dest_keys (ref_state S y)) \<noteq> None 
  | deref ref \<Rightarrow> 
      mv_reg_count (dest_keys (ref_state S ref)) = 1
    \<and> mv_reg_get1' (dest_keys (ref_state S ref)) \<noteq> None
  | may_delete inref remaining \<Rightarrow> True
  | reset_inref inref \<Rightarrow> True
  | reset_ref ref \<Rightarrow> True
"

find_consts "'a set \<Rightarrow> 'a"


definition effector_impl :: "effector_function" where
"effector_impl eff S \<equiv> case eff of
    effector_inref_inuse_enable inref \<Rightarrow> 
      s_update_inref inref (\<lambda>s. s\<lparr> inUse := True\<rparr>) S
  | effector_inref_rev_refs_add inref antidoteKey uid \<Rightarrow> 
      s_update_inref inref (\<lambda>s. s\<lparr>
                rev_refs := two_phase_set_add (rev_refs s) (antidoteKey, uid ) \<rparr>) S
  | effector_inref_rev_refs_rem inref antidoteKey uid \<Rightarrow> 
      s_update_inref inref (\<lambda>s. s\<lparr>
                rev_refs := two_phase_set_remove (rev_refs s) (antidoteKey, uid ) \<rparr>) S
  | effector_ref_dest_keys_assign ref antidoteKey uid oldUids \<Rightarrow> 
      s_update_ref ref (\<lambda>s. s\<lparr>dest_keys := insert (antidoteKey,uid) (Set.filter (\<lambda>(x,u). u\<noteq>uid \<and> u\<notin>oldUids) (dest_keys s)) \<rparr>) S
"

(** broken version 
definition ref_reset_targets :: "ref \<Rightarrow> inref option \<Rightarrow> uid \<Rightarrow> state \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list" where 
"ref_reset_targets ref ignoredInref uid state  \<equiv> exec {
        let (outkeys :: (inref option\<times>uid) set) = (dest_keys (ref_state state ref));
        set_forEachS outkeys True (\<lambda>(target,uid) first_time. 
          case target of 
              None \<Rightarrow> return first_time
            | Some target' => exec {
                  (if \<not> (target = ignoredInref \<and> first_time) then exec {
                    inref_rev_refs_remove target' ref uid;
                    return first_time
                  } else if target = ignoredInref then exec {
                    return False
                  } else exec {
                    return first_time
                  })
              })
      }"
**)

definition ref_reset_targets :: "ref \<Rightarrow> uid \<Rightarrow> state \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list" where 
"ref_reset_targets ref uid state  \<equiv> exec {
        let (outkeys :: (inref option\<times>uid) set) = (dest_keys (ref_state state ref));
        set_forEach outkeys (\<lambda>(target,uid). 
          case target of 
              None \<Rightarrow> skip
            | Some target' => inref_rev_refs_remove target' ref uid
            )
      }"

definition ref_reset :: "ref \<Rightarrow> inref option \<Rightarrow> uid \<Rightarrow> state \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list" where 
"ref_reset ref ignoredInref uid state  \<equiv> exec {
        ref_dest_keys_assign ref None uid state;
        ref_reset_targets ref uid state
      }"

definition outref_update :: "ref \<Rightarrow> inref option \<Rightarrow> state \<Rightarrow> uid \<Rightarrow> operation_effector list \<Rightarrow> operation_effector list" where
"outref_update ref inref state uid \<equiv> exec {
  (* first insert into new target: *)
  (case inref of
     None \<Rightarrow> skip
   | Some inref \<Rightarrow> inref_rev_refs_add inref ref uid);
  (* then: assign source *)
  ref_dest_keys_assign ref inref uid state;
  (* then reset targets: remove from all old targets *)
  ref_reset_targets ref uid state
}"

definition generator_impl :: generator_function where
"generator_impl opr uid state \<equiv> [] |> (case opr of 
    init ref inref \<Rightarrow> exec {
        inref_inuse_enable inref;
        outref_update ref (Some inref) state uid;
        return no_result
      }
  | assign outTo outVal \<Rightarrow> exec {
        let new_key = mv_reg_get1' (dest_keys (ref_state state outVal));
        outref_update outTo new_key state uid;
        return no_result
      }
  | deref ref \<Rightarrow> exec {
        let inref = mv_reg_get1' (dest_keys (ref_state state ref));
        let key = (map_option (inref_get_object_key state) inref);
        return (deref_result key)
      }
  | may_delete inref last_refs \<Rightarrow> exec {
        return (may_delete_result (may_delete_check state inref (set last_refs)))
      }
  | reset_inref inref \<Rightarrow> exec {
        return no_result
      }
  | reset_ref ref \<Rightarrow> exec {
        outref_update ref None state uid;
        return no_result
      }
)
"



definition 
"wellFormed_impl execution \<equiv> wellFormed execution initialState generator_impl effector_impl localPrecondition_impl precondition_impl"

find_consts "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"

fun find_smaller :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "find_smaller R x [] = None"
| "find_smaller R x (y#ys) = None"


lemma find_length[simp]: "find P xs = Some x \<Longrightarrow> length (remove1 x xs) < length xs"
  by (induct xs, auto split: if_splits)

lemma find_length2[simp]: "find P xs = Some x \<Longrightarrow> Suc (length (remove1 x xs)) = length xs "
  by (induct xs, auto split: if_splits)


definition findMinimal :: "'a rel \<Rightarrow> 'a list \<Rightarrow> 'a"   where 
"findMinimal R xs \<equiv> case find (\<lambda>y. \<forall>x\<in>set xs. x=y \<or> (x,y)\<notin>R) xs of None \<Rightarrow> hd xs | Some x \<Rightarrow> x"


lemma findMinimalIn: "xs\<noteq>[] \<Longrightarrow>  findMinimal R xs \<in> set xs"
  apply (auto simp add: findMinimal_def split: option.splits)
  by (metis (no_types, lifting) find_Some_iff in_set_conv_nth)


lemma findMinimal_termination[simp]: "xs\<noteq>[] \<Longrightarrow> length (remove1 (findMinimal R xs) xs) < length xs"
  by (simp add: findMinimalIn length_remove1)

lemma findMinimal_termination2[simp]: "findMinimal R (v # va) \<noteq> v \<Longrightarrow> length (remove1 (findMinimal R (v # va)) va) < length va"
  by (metis One_nat_def Suc_pred findMinimalIn length_pos_if_in_set length_remove1 lessI list.discI set_ConsD)


fun topSort :: "'a rel \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "topSort R [] = []"
| "topSort R xs = (let m = findMinimal R xs in m#topSort R (remove1 m xs))" 

find_consts "('k, 'v) fmap"

definition "numberEffectors E e \<equiv> e |> fmlookup (events E) |> the |> event_effectors |> length"

definition execution_addStep :: "int \<Rightarrow> operation \<Rightarrow> (event,nat) fmap \<Rightarrow> execution \<Rightarrow> execution" where
"execution_addStep eId opr preEventsN E \<equiv> 
let
   e = D_event eId;
   preEvents = fmdom' preEventsN;
   (* only existing events *) 
   deps1 :: event set = Set.filter (\<lambda>e. e\<in>fmdom' (events E)) preEvents;
   (* include parallel events which need to be stable *)
   deps2 = Set.filter (\<lambda>e. e\<in>deps1 \<or> (precondition_impl (event_operation ((events E)![e])) \<noteq> None \<and> (\<exists>e'\<in>deps1. (e',e)\<in>happensBefore E ) )) (fmdom' (events E));
   (* include causal dependencies *)
   deps3 = downwards_closure deps2 E; (* TODO could be more precise; at the level of effectors instead of events*)
   (* include parallel events, if stable precondition check required *)
   deps = (if precondition_impl opr = None then deps3 else parallel_closure deps3 (fmdom' (events E)) (happensBefore E));
   snapshot = sorted_list_of_set2 deps 
                 |> map (\<lambda>e. (e, case preEventsN.[e] of 
                                  None \<Rightarrow> numberEffectors E e
                                | Some n \<Rightarrow> if precondition_impl opr \<noteq> None \<or>  (\<exists>e'\<in>deps. e\<in>snapshot_events (event_snapshot ((events E)![e']))) 
                                            then numberEffectors E e 
                                            else n
                             ))  
                 |> fmap_of_list
                 |> Snapshot ;
   precond = (precondition_impl opr orElse (\<lambda>x. True));
   execOrder = topSort (happensBefore E) (sorted_list_of_set2 deps); 
   preState :: state = executeEffectors (List.maps (\<lambda>e. event_effectors ((events E)![e])) execOrder) initialState effector_impl
in if \<not>(localPrecondition_impl opr preState \<and> precond preState) then
  E
else
  let (res,eff) = generator_impl opr e preState;
      postState :: state = executeEffectors eff preState effector_impl  
  in
  \<lparr>
    events = fmupd e \<lparr>
      event_operation = opr,
      event_result = res,
      event_effectors = eff,
      event_executionOrder = execOrder,
      event_state_pre = preState,
      event_state_post = postState,
      event_snapshot = snapshot
    \<rparr> (events E)
  \<rparr>

"

definition "emptyExecution \<equiv> \<lparr>events = fmempty\<rparr>"

record trace_event = 
  t_operation :: operation
  t_deps :: "(event,nat) fmap"

definition execution_run :: "trace_event list \<Rightarrow> execution" where
"execution_run ops \<equiv> snd (fold (\<lambda>e (n,E). (n+1, execution_addStep n (t_operation e) (t_deps e) E)) ops (0, emptyExecution))"

definition forallEvents :: "execution \<Rightarrow> (event \<Rightarrow> eventInfo \<Rightarrow> bool) \<Rightarrow> bool" where
"forallEvents E P \<equiv> events E |> fmpred P"

definition forallStates :: "execution \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bool" where
"forallStates E P \<equiv> forallEvents E (\<lambda>e eInfo. P (event_state_pre eInfo) \<and> P (event_state_post eInfo))"


subsection {* Invariants *}

(* if ref exists, inref exists *)
definition invariant1 :: "execution \<Rightarrow> bool" where
"invariant1 E \<equiv> forallStates E (\<lambda>s. state_refs s |> fmpred (\<lambda>r rState. \<forall>(k,u)\<in>dest_keys rState. case k of None \<Rightarrow> True | Some inref \<Rightarrow> 
   (case (state_inrefs s).[inref] of None \<Rightarrow> False | Some inrefState \<Rightarrow> (r,u) \<in> two_phase_set_get (rev_refs inrefState) )))"

(* once an inref is unreachable, it remains unreachable *)
definition invariant2 :: "execution \<Rightarrow> bool" where
"invariant2 E \<equiv> 
(\<forall>(e,eInfo)\<in>events' E. 
  \<forall>(inref,inrefState)\<in>fmap_entries (state_inrefs (event_state_pre eInfo)). 
 two_phase_set_get (rev_refs inrefState) = {}
   \<and> stable e E
  \<longrightarrow> (\<forall>(e', eInfo')\<in>events' E.  (e,e')\<in>happensBefore E \<longrightarrow> 
        (case (state_inrefs (event_state_post eInfo')).[inref] of
            Some inrefState' \<Rightarrow> two_phase_set_get (rev_refs inrefState') = {}
          | None \<Rightarrow> False
    )))"

(* if there is a reverse reference, then there is also a forward reference
(only true, if using transactional semantics )
 *)
definition invariant3 :: "execution \<Rightarrow> bool" where
"invariant3 E \<equiv> 
forallStates E (\<lambda>S. 
  \<forall>(inref,inrefState)\<in>fmap_entries (state_inrefs S).  
    \<forall>(r,u)\<in>two_phase_set_get (rev_refs inrefState). 
      case state_refs S.[r] of
         None \<Rightarrow> False
       | Some rstate \<Rightarrow> (Some inref,u)\<in> dest_keys rstate
)
"

(* some simple postconditions for operations*)
definition invariant4 :: "execution \<Rightarrow> bool" where
"invariant4 E \<equiv> 
\<forall>(e,eInfo)\<in>events' E. 
case event_operation eInfo of
    init x y \<Rightarrow> 
      (let S = event_state_post eInfo in
      case state_refs S.[x] of
        None \<Rightarrow> False
        | Some rstate \<Rightarrow> Some y\<in>fst`dest_keys rstate)
  | _ \<Rightarrow> True
"

export_code wf_correct_execution_lists in Haskell
export_code execution_run in Haskell




definition "transformOp I \<equiv> let (opr, deps) = I in \<lparr>t_operation = opr, t_deps = deps\<rparr>"
definition "transformOp2 I \<equiv> let (opr, deps,xx) = I in trace_event.extend \<lparr>t_operation = opr, t_deps = deps\<rparr> xx"

instantiation  fmap :: (narrowing,narrowing) narrowing begin
definition "narrowing_fmap = Quickcheck_Narrowing.apply (Quickcheck_Narrowing.cons fmap_of_list) narrowing"
instance proof qed
end

instantiation  trace_event_ext :: (narrowing) narrowing begin
definition "narrowing_trace_event_ext = Quickcheck_Narrowing.apply (Quickcheck_Narrowing.cons transformOp2) narrowing"
instance proof qed
end


definition "execution_run2 ops \<equiv> execution_run (map transformOp ops)"


definition fmap_key_list where
"fmap_key_list m \<equiv> sorted_list_of_set2 (fmdom' m)"

definition fmap_to_list where
"fmap_to_list m \<equiv> map (\<lambda>k. (k,m![k])) (fmap_key_list m)"


export_code sorted_list_of_set2 execution_run2 invariant1 invariant2 invariant3 invariant4
 init assign deref may_delete reset_inref reset_ref D_event D_inref D_ref D_antidoteKey 
integer_of_nat int_of_integer integer_of_nat nat_of_integer fmap_of_list D_event integer_of_int
events event_operation event_result event_effectors event_executionOrder event_state_pre event_state_post event_snapshot 
fmlookup fmap_key_list fmap_to_list Snapshot state_refs state_inrefs 
object_key  dest_keys inref_object_key  rev_refs  inUse
effector_inref_inuse_enable effector_inref_rev_refs_add effector_inref_rev_refs_rem effector_ref_dest_keys_assign
in Haskell  (*module_name Ref_crdt*) file "refcrdt-quickcheck/srcgen"

typedef operations = "UNIV :: (trace_event list) set"
  by force


fun cleanRef where
"cleanRef (D_ref n) = D_ref (n mod 3)"
fun cleanInef where
"cleanInef (D_inref n) = D_inref 0"


fun cleanOperations :: "trace_event list \<Rightarrow> nat \<Rightarrow> trace_event list" where
  "cleanOperations [] n = []"
| "cleanOperations (ev#evs) n = (if n > 20 then [] else
  let newOp = (case t_operation ev of
     init x y \<Rightarrow> init (cleanRef x) (cleanInef y)
  | assign x y \<Rightarrow> assign (cleanRef x) (cleanRef y) 
  | deref x \<Rightarrow> deref (cleanRef x)
  | may_delete x xs \<Rightarrow> may_delete (cleanInef x) []
  | reset_inref x \<Rightarrow> reset_inref (cleanInef x)
  | reset_ref x \<Rightarrow> reset_ref (cleanRef x)
)
  in \<lparr>t_operation=newOp, deps = fmap_of_list (map (\<lambda>x. case x of (D_event x,i) \<Rightarrow> (D_event (x mod (int n)), i)) (fmap_to_list (t_deps ev)))\<rparr>#cleanOperations evs (Suc n))"

(*
init ref inref
  | assign ref ref
  | deref ref
  | may_delete inref "ref list"
  | reset_inref inref
  | reset_ref ref
*)

(*
lemma "let E = execution_run (cleanOperations ops 0) in invariant2 E"
  quickcheck[random,size=40,timeout=1000,verbose,timeout=1000]
  oops
*)

abbreviation "r1 \<equiv> D_ref 1"
abbreviation "r2 \<equiv> D_ref 2"
abbreviation "r3 \<equiv> D_ref 3"

abbreviation "ir1 \<equiv> D_inref 1"
abbreviation "ir2 \<equiv> D_inref 2"

abbreviation "e i \<equiv> D_event i"

value "let ops = [
 (* e0 *)  (init r3 ir2, fmap_of_list []),
 (* e1 *)  (reset_ref r2, fmap_of_list [(e 0,0)]),
 (* e2 *)  (init r2 ir1, fmap_of_list [(e 0,1),(e 1,1)]),
 (* e3 *)  (assign r3 r2, fmap_of_list [(e 0,1)]),
 (* e4 *)  (reset_ref r1, fmap_of_list [(e 1,1),(e 0,1),(e 3,1)]),
 (* e5 *)  (assign r2 r3, fmap_of_list [(e 0,1)]),
 (* e6 *)  (may_delete ir1 [], fmap_of_list [(e 3,1),(e 1,0),(e 0,1)])
   ]; 
   E = execution_run (map transformOp ops) ;
   ev = e 4;
   eInfo = the (fmlookup (events E) ev);
   e' = e 6;
   eInfo' = the (fmlookup (events E) e');
  inv = (
  \<forall>(inref,inrefState)\<in>fmap_entries (state_inrefs (event_state_pre eInfo)). 
 two_phase_set_get (rev_refs inrefState) = {}
   \<and> stable ev E
  \<longrightarrow> ( (ev,e')\<in>happensBefore E \<longrightarrow> 
        (case (state_inrefs (event_state_post eInfo')).[inref] of
            Some inrefState' \<Rightarrow> two_phase_set_get (rev_refs inrefState') = {}
          | None \<Rightarrow> False
    )))
   
  in (inv, invariant2 E, E)"



end