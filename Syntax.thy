theory Syntax
  imports Main
begin

chapter \<open>While Language Syntax\<close>

type_synonym ('a,'b) inst = "'a set \<times> 'a rel \<times> 'b"

abbreviation vc :: "('a,'b) inst \<Rightarrow> 'a set"
  where "vc \<alpha> \<equiv> fst \<alpha>"

abbreviation beh :: "('a,'b) inst \<Rightarrow> 'a rel"
  where "beh \<alpha> \<equiv> fst (snd \<alpha>)"

text \<open>
A While language with non-deterministic choice, iteration and parallel composition.
Also includes special commands for environment steps, which is useful for describing
refinement properties. These have no evaluation semantics or rules however.
\<close>
datatype ('a,'b) com =
  Nil
  | Basic "('a,'b) inst"
  | Seq "('a,'b) com" "('a,'b) com" (infixr ";" 80)
  | Choice "('a,'b) com" "('a,'b) com" (infixr "\<sqinter>" 150)
  | Loop "('a,'b) com" ("_*" [100] 150)
  | Parallel "('a,'b) com" "('a,'b) com"  (infixr "||" 150)

text \<open>Ensure there is no parallelism within a program\<close>
fun local :: "('a,'b) com \<Rightarrow> bool"
  where 
    "local (c\<^sub>1 || c\<^sub>2) = False" |
    "local (c\<^sub>1 ; c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |    
    "local (c\<^sub>1 \<sqinter> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |  
    "local (c*) = (local c)" |    
    "local _ = True"

abbreviation Env
  where "Env R \<equiv> Basic (UNIV,R\<^sup>*,undefined)"

end