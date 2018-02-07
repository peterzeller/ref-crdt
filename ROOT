(*	compile with:
		isabelle build -D .
	or:
		isabelle build -D . -j 4 -o quick_and_dirty
*)
session "ref_crdt" = "HOL" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
    "sorted_list"
    "~~/src/HOL/Library/Finite_Map"
    "~~/src/HOL/Library/Open_State_Syntax"
    "~~/src/HOL/Library/Code_Target_Numeral"
    "~~/src/HOL/Library/FSet"
    "~~/src/HOL/Eisbach/Eisbach"
    "~~/src/HOL/Library/Sublist"
    "~~/src/HOL/Library/LaTeXsugar"
    "~~/src/HOL/Library/OptionalSugar"
    "~~/src/HOL/Library/Multiset"
    "~~/src/HOL/Library/Option_ord"
  theories [show_question_marks = false, names_short]
    ref_crdt
  document_files
    "root.tex"
    "mathpartir.sty"
