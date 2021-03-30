theory Syntax
  imports Main
begin

chapter \<open>While Language Syntax\<close>

type_synonym ('a,'b) basic = "('a \<times> 'b set \<times> 'b rel)"
type_synonym ('a,'b) seq = "('a,'b) basic list"

abbreviation tag :: "('a,'b) basic \<Rightarrow> 'a"
  where "tag \<equiv> fst"

abbreviation vc :: "('a,'b) basic \<Rightarrow> 'b set"
  where "vc \<alpha> \<equiv> fst (snd \<alpha>)"

abbreviation beh :: "('a,'b) basic \<Rightarrow> 'b rel"
  where "beh \<alpha> \<equiv> snd (snd \<alpha>)"

text \<open>
A While language with non-deterministic choice, iteration and parallel composition.
Also includes special commands for environment steps, which is useful for describing
refinement properties. These have no evaluation semantics or rules however.
\<close>
datatype ('a,'b) com =
  Nil
  | Basic "('a,'b) basic"
  | Seq "('a,'b) com" "('a,'b) com" (infixr ";" 80)
  | Ord "('a,'b) com" "('a,'b) com" (infixr "\<cdot>" 80)
  | SeqChoice "('a,'b) seq set" ("\<Sqinter> _" 150)
  | Choice "('a,'b) com" "('a,'b) com" (infixr "\<sqinter>" 150)
  | Loop "('a,'b) com" ("_*" [100] 150)
  | Parallel "('a,'b) com" "('a,'b) com"  (infixr "||" 150)
  | Thread 'b "'b \<Rightarrow> 'b \<Rightarrow> 'b" "('a,'b) com"

text \<open>Ensure there is no parallelism within a program\<close>
fun local :: "('a,'b) com \<Rightarrow> bool"
  where 
    "local (c\<^sub>1 || c\<^sub>2) = False" |
    "local (Thread _ _ _) = False" |
    "local (c\<^sub>1 ; c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |
    "local (c\<^sub>1 \<cdot> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |        
    "local (c\<^sub>1 \<sqinter> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |  
    "local (c*) = (local c)" |    
    "local _ = True"

text \<open>Identify all operations in a program\<close>
fun basics :: "('a,'b) com \<Rightarrow> ('a,'b) basic set"
  where
    "basics (Basic \<beta>) = {\<beta>}" |
    "basics (Seq c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Ord c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Choice c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (SeqChoice S) = (\<Union>s \<in> S. set s)" |
    "basics (Parallel c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Loop c) = basics c" |
    "basics (Thread _ _ c) = basics c" |
    "basics _ = {}"

fun compare :: "(('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> bool) \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) com \<Rightarrow> bool"
  where
    "compare T Nil Nil = True" |
    "compare T (Basic \<alpha>) (Basic \<beta>) = (T \<alpha> \<beta>)" |
    "compare T (Seq c\<^sub>1 c\<^sub>2) (Seq c\<^sub>1' c\<^sub>2') = (compare T c\<^sub>1 c\<^sub>1' \<and> compare T c\<^sub>2 c\<^sub>2')" |
    "compare T (Ord c\<^sub>1 c\<^sub>2) (Ord c\<^sub>1' c\<^sub>2') = (compare T c\<^sub>1 c\<^sub>1' \<and> compare T c\<^sub>2 c\<^sub>2')" |
    "compare T (c\<^sub>1 \<sqinter> c\<^sub>2) (c\<^sub>1' \<sqinter> c\<^sub>2') = (compare T c\<^sub>1 c\<^sub>1' \<and> compare T c\<^sub>2 c\<^sub>2')" |
    "compare T (Loop c) (Loop c') = (compare T c c')" |
    "compare T (Thread s m c) (Thread s' m' c') = (compare T c c')" |
    "compare _ _ _ = False"

abbreviation Env
  where "Env R \<equiv> Basic (undefined,UNIV,R\<^sup>*)"

text \<open>Convert a sequence to a command\<close>
fun seq2com
  where "seq2com [] = Nil" | "seq2com (\<alpha>#t) = Basic \<alpha> \<cdot> seq2com t"

end