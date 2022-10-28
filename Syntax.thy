theory Syntax
  imports Main Push_State
begin

chapter \<open>While Language Syntax\<close>

(* a basic step is an action, a verification condition, and a behaviour set.  *)
(* note that iterated product types are right-associated. *)
type_synonym ('a,'b) basic = "('a \<times> 'b set \<times> 'b rel)"
type_synonym ('a,'b) eff = "('b set \<times> 'b rel)"
type_synonym ('a,'b) seq = "('a,'b) basic list"
type_synonym ('a,'b) wmm = "('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"

abbreviation tag :: "('a,'b) basic \<Rightarrow> 'a"
  where "tag \<equiv> fst"

abbreviation vc :: "('a,'b) basic \<Rightarrow> 'b set"
  where "vc \<alpha> \<equiv> fst (snd \<alpha>)"

abbreviation beh :: "('a,'b) basic \<Rightarrow> 'b rel"
  where "beh \<alpha> \<equiv> snd (snd \<alpha>)"

abbreviation pushbasic where
  "pushbasic s s' \<alpha> \<equiv> (tag \<alpha>, pushpred s (vc \<alpha>), pushrel s s' (beh \<alpha>))" 

abbreviation popbasic where
  "popbasic s s' \<alpha> \<equiv> (tag \<alpha>, poppred' s (vc \<alpha>), poprel' s s' (beh \<alpha>))"

text \<open>
A While language with non-deterministic choice, iteration and parallel composition.
Choice is intended to select from an arbitrary set of commands, however, this cannot
be expressed as an Isabelle datatype. To mimic a set, choice takes a function from
'labels' to arbitrary commands, where it may select any command in the function's range.
The state encoding is reused to express the notion of a label (but maybe this is a bad idea).
\<close>
datatype ('a,'b) com =
  Nil
  | Basic "('a,'b) basic"
  | Seq "('a,'b) com" "('a,'b) wmm" "('a,'b) com" ("_ ;\<^sub>_ _ " [90,0,90] 80)
  | Choice "'b \<Rightarrow> ('a,'b) com"                    (binder "\<Sqinter>" 10)
  | Loop "('a,'b) com" "('a,'b) wmm"              ("_*\<^sub>_" [90,90] 90)
  | Parallel "('a,'b) com" "('a,'b) com"          (infixr "||" 150)
  | Thread "('a,'b) com"
  | Capture 'b "('a,'b) com"

abbreviation univ_stack ("\<forall>\<^sub>c _" 100)
  where "univ_stack c \<equiv> \<Sqinter>s. Capture s c"

subsection \<open>Local Command\<close>

text \<open>
Identify if a command consists of only thread local constructs.
\<close>

inductive local :: "('a,'b) com \<Rightarrow> bool"
  where 
    "local Nil" |
    "local (Basic \<alpha>)" |
    "local c\<^sub>1 \<Longrightarrow> local c\<^sub>2  \<Longrightarrow> local (c\<^sub>1 ;\<^sub>r c\<^sub>2)" |
    "\<forall>s. local (f s) \<Longrightarrow> local (Choice f)" |
    "local c \<Longrightarrow> local (c*\<^sub>w)" | 
    "local c \<Longrightarrow> local (Capture k c)"

lemma local_simps [simp]:
  "local Nil = True"
  "local (Basic \<alpha>) = True"
  "local (c\<^sub>1 ;\<^sub>r c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)"
  "local (Choice f) = (\<forall>s. local (f s))"
  "local (c*\<^sub>w) = local c"
  "local (Capture k c) = local c"
  "local (c\<^sub>1 || c\<^sub>2) = False"
  "local (Thread c) = False"
  by (auto intro: local.intros elim: local.cases)

end