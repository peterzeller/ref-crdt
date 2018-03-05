theory sugar 
imports Main
begin

subsection {* Syntactic sugar *}

text {* Here we define some helper functions, to shorten the notation in this document. *}

definition orElse (infixr "orElse" 25) where
"x orElse y \<equiv> (case x of Some a \<Rightarrow> a | None \<Rightarrow> y)"

lemma orElse_some[simp]: "(Some x orElse y) = x"
  by (simp add: orElse_def)

lemma orElse_none[simp]: "(None orElse x) = x"
  by (simp add: orElse_def)

definition compose_forward (infixl "|>" 25) where
"x |> f \<equiv> f x"

lemma "(1 |> op+ 1 |> op* 2) = (4 :: int)"
  by eval

abbreviation questionmark ("???") where
"??? \<equiv> undefined"


end