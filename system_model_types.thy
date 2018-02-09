theory system_model_types
imports Main
begin


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

(* using event-IDs to model unique identifiers *)
type_synonym uid = event

end