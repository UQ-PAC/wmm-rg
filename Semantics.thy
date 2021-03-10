theory Semantics
  imports Main
begin

chapter \<open>Semantics\<close>

section \<open>Syntax\<close> 

datatype 'a com =
  Nil
  | Basic "'a"
  | Seq "'a com" "'a com" (infixr ";" 80)
  | Choice "'a com" "'a com" (infixr "\<sqinter>" 150)
  | Loop "'a com" ("_*" [100] 150)
  | Parallel "'a com" "'a com"  (infixr "||" 150)

section \<open>Small Step Semantics with Reordering\<close> 

locale semantics =
  fixes re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100)
  and fwd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<langle>_\<rangle>" [1000,0] 1000)

context semantics
begin

text \<open>Combine forwarding and reordering into a single check\<close>
abbreviation reorder_act :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ < _ <\<^sub>a _" [100,0,100] 100)
  where "\<beta>' < \<alpha> <\<^sub>a \<beta> \<equiv> \<beta>' = \<beta>\<langle>\<alpha>\<rangle> \<and> \<alpha> \<hookleftarrow> \<beta>\<langle>\<alpha>\<rangle>"

text \<open>Recursively define reordering of an instruction earlier than a program\<close>
fun reorder_prog :: "'a \<Rightarrow> 'a com \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ < _ <\<^sub>p _" [100,0,100] 100)
  where
    "reorder_prog \<alpha>' Nil \<alpha> = (\<alpha>' = \<alpha>)" |
    "reorder_prog \<alpha>' (Basic \<beta>) \<alpha> = (\<alpha>' < \<beta> <\<^sub>a \<alpha>)" |
    "reorder_prog \<alpha>' (c\<^sub>1 ; c\<^sub>2) \<alpha> = (\<exists>\<alpha>\<^sub>n. \<alpha>' < c\<^sub>1 <\<^sub>p \<alpha>\<^sub>n \<and> \<alpha>\<^sub>n < c\<^sub>2 <\<^sub>p \<alpha>)" |
    "reorder_prog \<alpha>' (c\<^sub>1 \<sqinter> c\<^sub>2) \<alpha> = (\<alpha>' < c\<^sub>1 <\<^sub>p \<alpha> \<and> \<alpha>' < c\<^sub>2 <\<^sub>p \<alpha>)" |
    "reorder_prog \<alpha>' (Loop c) \<alpha> = (\<alpha>' = \<alpha> \<and> \<alpha> < c <\<^sub>p \<alpha>)" |
    "reorder_prog _ _ _ = False"

text \<open>Recursively define forwarding of an instruction across a program \<close>
fun fwd_prog :: "'a \<Rightarrow> 'a com \<Rightarrow> 'a"
  ("_\<llangle>_\<rrangle>" [1000,0] 1000)
  where
    "fwd_prog \<alpha> (Basic \<beta>) = \<alpha>\<langle>\<beta>\<rangle>" |
    "fwd_prog \<alpha> (c\<^sub>1 ; c\<^sub>2) = fwd_prog (fwd_prog \<alpha> c\<^sub>2) c\<^sub>1" |
    "fwd_prog \<alpha> (c\<^sub>1 \<sqinter> c\<^sub>2) = fwd_prog \<alpha> c\<^sub>1" |
    "fwd_prog \<alpha> _  = \<alpha>"


(* to remove WMM from the theory, it suffices to remove ps case in the below def *)
text \<open>Small step semantics for an instruction execution\<close>
inductive_set execute :: "('a com \<times> 'a \<times> 'a com) set"
  and execute_abv :: "'a com \<Rightarrow> 'a \<Rightarrow> 'a com \<Rightarrow> bool"
  ("_ \<mapsto>\<^sub>_ _" [71,0,71] 70)
  where
  "c \<mapsto>\<^sub>\<alpha> c' \<equiv> (c, \<alpha>, c') \<in> execute" |
  act[intro]:  "Basic \<alpha> \<mapsto>\<^sub>\<alpha> Nil" |
  pre[intro]:  "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ; c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1' ; c\<^sub>2" |
  pst[intro]:  "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1' \<Longrightarrow> \<gamma> < c\<^sub>2 <\<^sub>p \<alpha> \<Longrightarrow> c\<^sub>2 ; c\<^sub>1 \<mapsto>\<^sub>\<gamma> c\<^sub>2 ; c\<^sub>1'" |
  par1[intro]: "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1' || c\<^sub>2" |
  par2[intro]: "c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1 || c\<^sub>2'"
inductive_cases executeE[elim]: "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1'"

text \<open>Small step semantics for a silent step\<close>
inductive_set silent :: "('a com \<times> 'a com) set"
  and rw_abv :: "'a com \<Rightarrow> 'a com \<Rightarrow> bool"
  ("_ \<leadsto> _" [71,71] 70)
  where
  "c \<leadsto> c' \<equiv> (c, c') \<in> silent" |
  seq1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ; c\<^sub>2 \<leadsto> c\<^sub>1' ; c\<^sub>2" |
  seq2[intro]:  "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 ; c\<^sub>2 \<leadsto> c\<^sub>1 ; c\<^sub>2'" |
  seqE1[intro]: "Nil ; c\<^sub>1 \<leadsto> c\<^sub>1" |
  seqE2[intro]: "c\<^sub>1 ; Nil \<leadsto> c\<^sub>1" |
  left[intro]:  "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>1" |
  right[intro]: "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>2" |
  loop1[intro]: "c* \<leadsto> Nil" |
  loop2[intro]: "c* \<leadsto> c ; c*" |
  par1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1' || c\<^sub>2" |
  par2[intro]:  "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1 || c\<^sub>2'" |
  parE1[intro]: "Nil || c \<leadsto> c" |
  parE2[intro]: "c || Nil \<leadsto> c"
inductive_cases silentE[elim]: "c\<^sub>1 \<leadsto> c\<^sub>1'"

text \<open>An execution step implies the program has changed\<close>
lemma step_neq:
  assumes "c \<mapsto>\<^sub>\<alpha> c'"
  shows "c \<noteq> c'"
  using assms
  by (induct) auto

lemma [simp]:
  "c \<mapsto>\<^sub>\<alpha> c = False"
  using step_neq by auto

text \<open>Relationship between program reordering and program forwarding\<close>
lemma fwd_prog [simp]:
  assumes "\<alpha>' < c <\<^sub>p \<alpha>"
  shows "\<alpha>\<llangle>c\<rrangle> = \<alpha>'"
  using assms by (induct c arbitrary: \<alpha>' \<alpha>) auto

end

end