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

context pstate
begin

abbreviation pushbasic where
  "pushbasic s s' \<alpha> \<equiv> (tag \<alpha>, pushpred s (vc \<alpha>), pushrel s s' (beh \<alpha>))" 

abbreviation popbasic where
  "popbasic s s' \<alpha> \<equiv> (tag \<alpha>, poppred' s (vc \<alpha>), poprel' s s' (beh \<alpha>))"


abbreviation poppableBasic where
"poppableBasic s s' \<alpha> \<equiv> poppable s (vc \<alpha>) \<and> poppable_rel s s' (beh \<alpha>)"

end

text \<open>
A While language with non-deterministic choice, iteration and parallel composition.
Choice is intended to select from an arbitrary set of commands, however, this cannot
be expressed as an Isabelle datatype. To mimic a set, choice takes a function from
'labels' to arbitrary commands, where it may select any command in the function's range.
The state encoding is reused to express the notion of a label, hence the choice is over
some set of states (but maybe this is a bad idea).
\<close>




datatype ('a,'b,'c) com =
  Nil
  | Basic "('a,'b) basic"
  | Seq "('a,'b,'c) com" "('a,'b) wmm" "('a,'b,'c) com" ("_ ;\<^sub>_ _ " [90,0,90] 80)
  | Choice "nat \<Rightarrow> ('a,'b,'c) com"                    (binder "\<Sqinter>" 10)
  | Loop "('a,'b,'c) com" "('a,'b) wmm"              ("_*\<^sub>_" [90,90] 90)
  | Parallel "('a,'b,'c) com" "('a,'b,'c) com"          (infixr "||" 150)
  | Thread "('a,'b,'c) com"
  | Capture 'c "('a,'b,'c) com"
  | Interrupt "('a,'b,'c) com"                      ("\<triangle> _" 80)          (* as unary *)

abbreviation univ_stack ("\<forall>\<^sub>c _" 100)
  where "univ_stack c \<equiv> \<Sqinter>s. Capture s c"

subsection \<open>Local Command\<close>

text \<open>
Identify if a command consists of only thread local constructs.
\<close>

inductive local :: "('a,'b,'c) com \<Rightarrow> bool"
  where 
    "local Nil" |                
    "local (Basic \<alpha>)" |
    "local c\<^sub>1 \<Longrightarrow> local c\<^sub>2  \<Longrightarrow> local (c\<^sub>1 ;\<^sub>r c\<^sub>2)" |
    "\<forall>s. local (f s) \<Longrightarrow> local (Choice f)" |
    "local c \<Longrightarrow> local (c*\<^sub>w)" | 
    "local c \<Longrightarrow> local (Capture k c)" |
    "local c \<Longrightarrow> local (\<triangle>c)"

lemma local_simps [simp]:
  "local Nil = True"
  "local (Basic \<alpha>) = True"
  "local (c\<^sub>1 ;\<^sub>r c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)"
  "local (Choice f) = (\<forall>s. local (f s))"
  "local (c*\<^sub>w) = local c"
  "local (Capture k c) = local c"
  "local (\<triangle>c) = (local c)"
  "local (c\<^sub>1 || c\<^sub>2) = False"
  "local (Thread c) = False"
  by (auto intro: local.intros elim: local.cases)


(*
subsection \<open>Syntactic Basics\<close>
text \<open>
Collect basics contained within the command.
May not directly line up with those basics emitted during evaluation due to the effects
of forwarding. Consequently, probably a bad idea to use these definitions.
\<close>

inductive basic :: "('a,'b::state) com \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  where
    "basic (Basic \<beta>) ( \<beta>)" |
    "basic c\<^sub>1 \<beta> \<Longrightarrow> basic (c\<^sub>1 ;\<^sub>r c\<^sub>2) \<beta>" |
    "basic c\<^sub>2 \<beta> \<Longrightarrow> basic (c\<^sub>1 ;\<^sub>r c\<^sub>2) \<beta>" |
    "basic (f s) \<beta> \<Longrightarrow> basic (\<Sqinter>s. f s) \<beta>" |
    "basic c \<beta> \<Longrightarrow> basic (c*\<^sub>w) \<beta>" |
    "basic c \<beta> \<Longrightarrow> basic (Capture k c) ( \<beta>)" |
    "basic c\<^sub>1 \<beta> \<Longrightarrow> basic (c\<^sub>1 || c\<^sub>2) \<beta>" |
    "basic c\<^sub>2 \<beta> \<Longrightarrow> basic (c\<^sub>1 || c\<^sub>2) \<beta>" |
    "basic c \<beta> \<Longrightarrow> basic (Thread c) \<beta>"
inductive_cases basic_tuple: "basic c (a,b,d)"

definition basics :: "('a,'b::state) com \<Rightarrow> ('a,'b) basic set"
  where "basics c \<equiv> {\<beta>. basic c \<beta>}"

lemma basics_simps [simp]:
  "basics Nil = {}"
  "basics (Basic \<beta>) = {\<beta>}"
  "basics (c\<^sub>1 ;\<^sub>r c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2"
  "basics (\<Sqinter>s. f s) = \<Union>{basics (f s) | s. True}"
  "basics (c*\<^sub>w) = basics c"
  "basics (Capture k c) =  basics c"
  "basics (c\<^sub>1 || c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2"
  "basics (Thread c) = basics c" 
  apply (auto simp: basics_def elim: basic.cases  intro: basic.intros)
    done
*)


end