theory Syntax
  imports Main
begin

chapter \<open>While Language Syntax\<close>

(* a basic step is an action, a verification condition, and a behaviour set.  *)
(* note that iterated product types are right-associated. *)
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
  | Seq "('a,'b) com" "('a,'b) com" (infixr ";;" 80)
  | Ord "('a,'b) com" "('a,'b) com" (infixr "\<cdot>" 80)
  | SeqChoice "('a,'b) seq set" ("\<Sqinter> _" 150)
  | Choice "('a,'b) com" "('a,'b) com" (infixr "\<sqinter>" 150)
  | Loop "('a,'b) com" ("_*" [100] 150)
  | Parallel "('a,'b) com" "('a,'b) com"  (infixr "||" 150)
  | Thread "('a,'b) com"
  (* | Capture 'b "('a,'b) com" *)
  (* | CaptureAll "('a,'b) com" *)


text \<open>Ensure there is no parallelism within a program\<close>
fun local :: "('a,'b) com \<Rightarrow> bool"
  where 
    "local (c\<^sub>1 || c\<^sub>2) = False" |
    "local (Thread _) = False" |
    "local (c\<^sub>1 ;; c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |
    "local (c\<^sub>1 \<cdot> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |
    "local (c\<^sub>1 \<sqinter> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |  
    "local (c*) = (local c)" |    
    (* "local (Capture _ c) = local c" | *)
    (* "local (CaptureAll c) = local c" | *)
    "local _ = True"


class state =
  fixes merge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  (* assumes "surj (\<lambda>m. merge m s)" *)

fun capBasic :: "('a,'b :: state) basic \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a,'b) basic" where
"capBasic \<alpha> s s' = 
  (tag \<alpha>, {m. merge m s \<in> vc \<alpha>}, {(m,m'). (merge m s, merge m' s') \<in> beh \<alpha>})"

fun uncapBasic :: "'b \<Rightarrow> ('a,'b :: state) basic \<Rightarrow> ('a,'b) basic" where
"uncapBasic s \<alpha> = 
  (tag \<alpha>, {merge m s |m. m \<in> vc \<alpha>}, {(merge m s, merge m' s) |m m'. (m,m') \<in> beh \<alpha>})"

lemma "surj f \<Longrightarrow> {f a |a. f a \<in> A} = A"
by fast

lemma "(uncapBasic s (capBasic \<alpha> s s)) = \<alpha>"
apply auto
oops

text \<open>Identify all operations in a program\<close>
fun basics :: "('a,'b ) com \<Rightarrow> ('a,'b) basic set"
  where
    "basics (Basic \<beta>) = {\<beta>}" |
    "basics (Seq c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Ord c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Choice c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (SeqChoice S) = (\<Union>s \<in> S. set s)" |
    "basics (Parallel c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Loop c) = basics c" |
    "basics (Thread c) = basics c" |
    (* "basics (Capture s c) = uncapBasic s ` basics c" | *)
    (* "basics (Capture s c) = basics c" |  *)
    (* "basics (CaptureAll c) = basics c" | *)
    "basics _ = {}"

text \<open>Shorthand for an environment step\<close>
abbreviation Env :: "'b rel \<Rightarrow> ('a,'b) com"
  where "Env R \<equiv> Basic (undefined,UNIV,R\<^sup>*)"

text \<open>Convert a sequence to a command\<close>
fun seq2com :: "('a,'b) seq \<Rightarrow> ('a,'b) com"
  where "seq2com [] = Nil" | "seq2com (\<alpha>#t) = Basic \<alpha> \<cdot> seq2com t"

end