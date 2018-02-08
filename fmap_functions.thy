theory fmap_functions
  imports Main
    "~~/src/HOL/Library/Finite_Map"
begin

abbreviation lookupsyntax ("_ .[_]"[25,25]25) where
"m.[x] \<equiv> fmlookup m x"

abbreviation lookupsyntax2 ("_ ![_]"[25,25]25) where
"m![x] \<equiv> the (fmlookup m x)"



end