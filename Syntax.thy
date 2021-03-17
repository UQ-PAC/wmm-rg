theory Syntax
  imports Main
begin

chapter \<open>Syntax\<close>

text \<open>Basic While Language syntax, with parallel composition\<close>

datatype 'a com =
  Nil
  | Basic "'a"
  | Seq "'a com" "'a com" (infixr ";" 80)
  | Choice "'a com" "'a com" (infixr "\<sqinter>" 150)
  | Loop "'a com" ("_*" [100] 150)
  | Parallel "'a com" "'a com"  (infixr "||" 150)

end