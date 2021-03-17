theory Semantics
  imports Reordering
begin

chapter \<open>Small Step Semantics\<close>

text \<open>
Define the small step semantics for the While language, with weak memory model behaviours.
Also introduces a notion of configuration, that couples programs and memory states,
with transitions for the program and the environment.
\<close>

type_synonym ('a,'b) config = "'a com \<times> 'b"

locale semantics = reordering +
  fixes eval :: "'a \<Rightarrow> 'b rel" 

context semantics
begin

section \<open>Program Transition Definitions\<close>

text \<open>Small step semantics for an instruction execution\<close>
text \<open>To remove reordering from the theory, it suffices to remove the out-of-order (ooo) case below\<close>
inductive_set execute :: "('a com \<times> 'a \<times> 'a com) set"
  and execute_abv :: "'a com \<Rightarrow> 'a \<Rightarrow> 'a com \<Rightarrow> bool"
  ("_ \<mapsto>\<^sub>_ _" [71,73,71] 70)
  where
  "c \<mapsto>\<^sub>\<alpha> c' \<equiv> (c, \<alpha>, c') \<in> execute" |
  act[intro]:  "Basic \<alpha> \<mapsto>\<^sub>\<alpha> Nil" |
  seq[intro]:  "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1' ;; c\<^sub>2" |
  ooo[intro]:  "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1' \<Longrightarrow> \<gamma> < c\<^sub>2 <\<^sub>c \<alpha> \<Longrightarrow> c\<^sub>2 ;; c\<^sub>1 \<mapsto>\<^sub>\<gamma> c\<^sub>2 ;; c\<^sub>1'" |
  par1[intro]: "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1' || c\<^sub>2" |
  par2[intro]: "c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1 || c\<^sub>2'"
inductive_cases executeE[elim]: "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1'"

text \<open>Small step semantics for a silent step\<close>
inductive_set silent :: "('a com \<times> 'a com) set"
  and rw_abv :: "'a com \<Rightarrow> 'a com \<Rightarrow> bool"
  ("_ \<leadsto> _" [71,71] 70)
  where
  "c \<leadsto> c' \<equiv> (c, c') \<in> silent" |
  seq1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<leadsto> c\<^sub>1' ;; c\<^sub>2" |
  seq2[intro]:  "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<leadsto> c\<^sub>1 ;; c\<^sub>2'" |
  seqE1[intro]: "Nil ;; c\<^sub>1 \<leadsto> c\<^sub>1" |
  seqE2[intro]: "c\<^sub>1 ;; Nil \<leadsto> c\<^sub>1" |
  left[intro]:  "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>1" |
  right[intro]: "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>2" |
  loop1[intro]: "c* \<leadsto> Nil" |
  loop2[intro]: "c* \<leadsto> c ;; c*" |
  par1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1' || c\<^sub>2" |
  par2[intro]:  "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1 || c\<^sub>2'" |
  parE1[intro]: "Nil || c \<leadsto> c" |
  parE2[intro]: "c || Nil \<leadsto> c"
inductive_cases silentE[elim]: "c\<^sub>1 \<leadsto> c\<^sub>1'"

text \<open>An execution step implies the program has changed\<close>
lemma execute_neq:
  assumes "c \<mapsto>\<^sub>\<alpha> c'"
  shows "c \<noteq> c'"
  using assms by (induct) auto

lemma [simp]:
  "c \<mapsto>\<^sub>\<alpha> c = False"
  using execute_neq by auto

text \<open>A silent step will not introduce parallelism\<close>
lemma local_silent:
  "c \<leadsto> c' \<Longrightarrow> local c \<Longrightarrow> local c'"
  by (induct rule: silent.induct) auto

text \<open>An execution step will not introduce parallelism\<close>
lemma local_execute:
  "c \<mapsto>\<^sub>\<alpha> c' \<Longrightarrow> local c \<Longrightarrow> local c'"
  by (induct rule: execute.induct) auto

section \<open>Transition Definitions\<close>

text \<open>These transitions are over configurations of (program,state)\<close>

text \<open>Environment Transition\<close>
abbreviation env_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -e\<rightarrow> _" [81,81] 80)
  where "s -e\<rightarrow> s' \<equiv> fst s = fst s'"

text \<open>Program Execution Transition\<close>
abbreviation exec_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -\<alpha>\<rightarrow> _" [81,81] 80)
  where "s -\<alpha>\<rightarrow> s' \<equiv> \<exists>\<alpha>. fst s \<mapsto>\<^sub>\<alpha> (fst s') \<and> (snd s,snd s') \<in> eval \<alpha>"

text \<open>Program Silent Transition\<close>
abbreviation sil_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -s\<rightarrow> _" [81,81] 80)
  where "s -s\<rightarrow> s' \<equiv> fst s \<leadsto> fst s' \<and> snd s = snd s'"

text \<open>Program Transition\<close>
abbreviation com_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -c\<rightarrow> _" [81,81] 80)
  where "s -c\<rightarrow> s' \<equiv> s -\<alpha>\<rightarrow> s' \<or> s -s\<rightarrow> s'"

text \<open>Collect of all possible transitions\<close>
inductive_set transitions :: "('a,'b) config list set"
  where 
    one[intro]: "[s] \<in> transitions" |
    env[intro]: "s -e\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    prg[intro]: "s -\<alpha>\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    sil[intro]: "s -s\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions"
inductive_cases transitionsE[elim]: "t \<in> transitions"

end

end