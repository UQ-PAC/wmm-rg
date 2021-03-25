theory Semantics
  imports Reordering Atomics
begin

chapter \<open>Small Step Semantics\<close>

text \<open>
Define the small step semantics for the While language, with weak memory model behaviours.
Also introduces a notion of configuration, that couples programs and memory states,
with transitions for the program and the environment.
\<close>

type_synonym ('a,'b,'c) config = "('a,'b,'c) com \<times> ('b \<times> 'c tree)"

locale semantics = reordering fwd re + atomic vc beh
  for vc :: "'a \<Rightarrow> ('b \<times> 'c) set"
  and beh :: "'a \<Rightarrow> ('b \<times> 'c) rel"
  and fwd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<langle>_\<rangle>" [1000,0] 1000)
  and re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100)

context semantics
begin

section \<open>Program Transition Definitions\<close>

text \<open>
Semantics that collects reordering effects.
Given c \<mapsto>[r,\<alpha>'] c', this corresponds to c \<mapsto>\<alpha><r> c', such that
r should be the program \<alpha>' has to reorder with in c to execute and 
\<alpha> should be \<alpha>' forwarded across r.\<close>
inductive lcl_execute :: "('a,'b,'c) com \<Rightarrow> ('a,'b,'c) com \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool"
  ("_ \<mapsto>[_,_] _" [71,0,0,71] 70)
  where
  act[intro]: "Basic \<alpha> \<mapsto>[Nil,\<alpha>] Nil" |
  seq[intro]: "c\<^sub>1 \<mapsto>[r,\<alpha>] c\<^sub>1' \<Longrightarrow> c\<^sub>1 ; c\<^sub>2 \<mapsto>[r,\<alpha>] c\<^sub>1' ; c\<^sub>2" |
  ord[intro]: "c\<^sub>1 \<mapsto>[r,\<alpha>] c\<^sub>1' \<Longrightarrow> c\<^sub>1 \<cdot> c\<^sub>2 \<mapsto>[r,\<alpha>] c\<^sub>1' \<cdot> c\<^sub>2" |
  ooo[intro]: "c\<^sub>1 \<mapsto>[r,\<alpha>] c\<^sub>1' \<Longrightarrow> \<alpha>' < c\<^sub>2 ; r <\<^sub>c \<alpha> \<Longrightarrow> c\<^sub>2 ; c\<^sub>1 \<mapsto>[c\<^sub>2 ; r ,\<alpha>] c\<^sub>2 ; c\<^sub>1'"
inductive_cases lcl_execute[elim]: "c \<mapsto>[r,\<alpha>'] c'"

text \<open>
Semantics that collects reordering effects.
Given c \<mapsto>[r,\<alpha>'] c', this corresponds to c \<mapsto>\<alpha><r> c', such that
r should be the program \<alpha>' has to reorder with in c to execute and 
\<alpha> should be \<alpha>' forwarded across r.\<close>
inductive glb_execute :: "('a,'b,'c) com \<Rightarrow> ('b \<times> 'c tree) rel \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool"
  ("_ \<mapsto>[_] _" [71,0,71] 70)
  where
  lcl[intro]: "c \<mapsto>[r,\<alpha>] c' \<Longrightarrow> c \<mapsto>[leaf\<^sub>r (eval \<alpha>\<llangle>r\<rrangle>)] c'" |
  par1[intro]: "c\<^sub>1 \<mapsto>[g] c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>[left\<^sub>r g] c\<^sub>1' || c\<^sub>2" |
  par2[intro]: "c\<^sub>2 \<mapsto>[g] c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>[right\<^sub>r g] c\<^sub>1 || c\<^sub>2'"
inductive_cases glb_execute[elim]: "c \<mapsto>[g] c'"

text \<open>Small step semantics for a silent step\<close>
inductive silent :: "('a,'b,'c) com \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool"
  ("_ \<leadsto> _" [71,71] 70)
  where
  seq1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ; c\<^sub>2 \<leadsto> c\<^sub>1' ; c\<^sub>2" |
  ord1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 \<cdot> c\<^sub>2 \<leadsto> c\<^sub>1' \<cdot> c\<^sub>2" |
  seq2[intro]:  "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 ; c\<^sub>2 \<leadsto> c\<^sub>1 ; c\<^sub>2'" |
  seqE1[intro]: "Nil ; c\<^sub>1 \<leadsto> c\<^sub>1" |
  seqE2[intro]: "c\<^sub>1 ; Nil \<leadsto> c\<^sub>1" |
  ordE[intro]:  "Nil \<cdot> c\<^sub>1 \<leadsto> c\<^sub>1" |
  bigc[intro]:  "s \<in> S \<Longrightarrow> (\<Sqinter> S) \<leadsto> seq2com s" |
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
lemma execute_neq:
  assumes "c \<mapsto>[r,\<alpha>'] c'"
  shows "c \<noteq> c'"
  using assms by (induct) auto

lemma [simp]:
  "c \<mapsto>[r,\<alpha>'] c = False"
  using execute_neq by blast

lemma gexecute_neq:
  assumes "c \<mapsto>[g] c'"
  shows "c \<noteq> c'"
  using assms by (induct) auto

lemma [simp]:
  "c \<mapsto>[g] c = False"
  using gexecute_neq by blast

lemma [intro]:
  "local (seq2com s)"
  by (induct s) auto

text \<open>A silent step will not introduce parallelism\<close>
lemma local_silent:
  "c \<leadsto> c' \<Longrightarrow> local c \<Longrightarrow> local c'"
  by (induct rule: silent.induct) auto

text \<open>An execution step will not introduce parallelism\<close>
lemma local_execute:
  "c \<mapsto>[r,\<alpha>'] c' \<Longrightarrow> local c \<Longrightarrow> local c'"
  by (induct rule: lcl_execute.induct) auto

section \<open>Transition Definitions\<close>

text \<open>These transitions are over configurations of (program,state)\<close>

text \<open>Environment Transition\<close>
abbreviation env_tran :: "('a,'b,'c) config \<Rightarrow> ('a,'b,'c) config \<Rightarrow> bool" ("_ -e\<rightarrow> _" [81,81] 80)
  where "s -e\<rightarrow> s' \<equiv> fst s = fst s'"

text \<open>Program Execution Transition\<close>
abbreviation exec_tran :: "('a,'b,'c) config \<Rightarrow> ('a,'b,'c) config \<Rightarrow> bool" ("_ -\<alpha>\<rightarrow> _" [81,81] 80)
  where "s -\<alpha>\<rightarrow> s' \<equiv> \<exists>g. fst s \<mapsto>[g] (fst s') \<and> (snd s,snd s') \<in> g"

text \<open>Program Silent Transition\<close>
abbreviation sil_tran :: "('a,'b,'c) config \<Rightarrow> ('a,'b,'c) config \<Rightarrow> bool" ("_ -s\<rightarrow> _" [81,81] 80)
  where "s -s\<rightarrow> s' \<equiv> fst s \<leadsto> fst s' \<and> snd s = snd s'"

text \<open>Program Transition\<close>
abbreviation com_tran :: "('a,'b,'c) config \<Rightarrow> ('a,'b,'c) config \<Rightarrow> bool" ("_ -c\<rightarrow> _" [81,81] 80)
  where "s -c\<rightarrow> s' \<equiv> s -\<alpha>\<rightarrow> s' \<or> s -s\<rightarrow> s'"

text \<open>Collect of all possible transitions\<close>
inductive_set transitions :: "('a,'b,'c) config list set"
  where 
    one[intro]: "[s] \<in> transitions" |
    env[intro]: "s -e\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    prg[intro]: "s -\<alpha>\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    sil[intro]: "s -s\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions"
inductive_cases transitionsE[elim]: "t \<in> transitions"

end

end