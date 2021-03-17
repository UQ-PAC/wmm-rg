theory Syntax
  imports Main
begin

chapter \<open>While Language Syntax\<close>

type_synonym 'b pred = "'b set"
type_synonym 'b rpred = "'b rel"

text \<open>A While language with non-deterministic choice, iteration and parallel composition.\<close>
datatype 'a com =
  Nil
  | Basic "'a"
  | Seq "'a com" "'a com" (infixr ";;" 80)
  | Choice "'a com" "'a com" (infixr "\<sqinter>" 150)
  | Loop "'a com" ("_*" [100] 150)
  | Parallel "'a com" "'a com"  (infixr "||" 150)

text \<open>Ensure there is no parallelism within a program\<close>
fun local :: "'a com \<Rightarrow> bool"
  where 
    "local (c\<^sub>1 || c\<^sub>2) = False" |
    "local (c\<^sub>1 ;; c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |    
    "local (c\<^sub>1 \<sqinter> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |  
    "local (c*) = (local c)" |    
    "local _ = True"

end