theory Syntax
  imports Main
begin

chapter \<open>While Language Syntax\<close>

type_synonym 'a seq = "'a list"

text \<open>
A While language with non-deterministic choice, iteration and parallel composition.
Also includes special commands for environment steps, which is useful for describing
refinement properties. These have no evaluation semantics or rules however.
\<close>
datatype ('a,'b,'c) com =
  Nil
  | Basic "'a"
  | Seq "('a,'b,'c) com" "('a,'b,'c) com" (infixr ";" 80)
  | Ord "('a,'b,'c) com" "('a,'b,'c) com" (infixr "\<cdot>" 80)
  | BigChoice "'a seq set" ("\<Sqinter> _" 150)
  | Choice "('a,'b,'c) com" "('a,'b,'c) com" (infixr "\<sqinter>" 150)
  | Loop "('a,'b,'c) com" ("_*" [100] 150)
  | Parallel "('a,'b,'c) com" "('a,'b,'c) com"  (infixr "||" 150)
  | Rel "('b \<times> 'c) rel"

text \<open>Convert a sequence to a command\<close>
fun seq2com
  where "seq2com [] = Nil" | "seq2com (\<alpha>#t) = Basic \<alpha> \<cdot> seq2com t"

text \<open>Ensure there is no parallelism within a program\<close>
fun local :: "('a,'b,'c) com \<Rightarrow> bool"
  where 
    "local (c\<^sub>1 || c\<^sub>2) = False" |
    "local (Rel r) = False" |
    "local (c\<^sub>1 ; c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |    
    "local (c\<^sub>1 \<cdot> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |    
    "local (c\<^sub>1 \<sqinter> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |  
    "local (c*) = (local c)" |    
    "local _ = True"

text \<open>Identify all operations in a program\<close>
fun basics :: "('a,'b,'c) com \<Rightarrow> 'a set"
  where
    "basics (Basic \<beta>) = {\<beta>}" |
    "basics (Seq c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Ord c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Choice c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (BigChoice S) = (\<Union>s \<in> S. set s)" |
    "basics (Parallel c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Loop c) = basics c" |
    "basics _ = {}"

abbreviation fullR
  where "fullR R \<equiv> {((g,l),(g',l)) | l g g'. (g,g') \<in> R}"

abbreviation Env
  where "Env R \<equiv> Rel (fullR (R\<^sup>*))"

end