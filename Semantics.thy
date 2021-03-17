theory Semantics
  imports Reordering
begin

chapter \<open>Small Step Semantics\<close>

locale semantics = reordering +
  fixes eval :: "'a \<Rightarrow> 's rel" 

context semantics
begin

section \<open>Program Transition Definitions\<close>

text \<open>Small step semantics for an instruction execution\<close>
text \<open>To remove WMM from the theory, it suffices to remove the pst case below\<close>
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

section \<open>Transition Definitions\<close>

text \<open>These transitions are over configurations of (program,state)\<close>

text \<open>Environment Transition\<close>
abbreviation etran ("_ -e\<rightarrow> _" [81,81] 80)
  where "etran s s' \<equiv> (fst s) = (fst s')"

text \<open>Program Execution Transition\<close>
abbreviation ctran ("_ -\<alpha>\<rightarrow> _" [81,81] 80)
  where "ctran s s' \<equiv> (\<exists>\<alpha>. ((fst s) \<mapsto>\<^sub>\<alpha> (fst s')) \<and> (snd s,snd s') \<in> eval \<alpha>)"

text \<open>Program Silent Transition\<close>
abbreviation stran ("_ -s\<rightarrow> _" [81,81] 80)
  where "stran s s' \<equiv> (((fst s) \<leadsto> (fst s')) \<and> (snd s) = (snd s'))"

text \<open>Program Transition\<close>
abbreviation atran ("_ -c\<rightarrow> _" [81,81] 80)
  where "atran s s' \<equiv> (s -\<alpha>\<rightarrow> s' \<or> s -s\<rightarrow> s')"

text \<open>Collect of all possible transitions\<close>
inductive_set transitions
  where 
    one[intro]: "[s] \<in> transitions" |
    env[intro]: "s -e\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    prg[intro]: "s -\<alpha>\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    sil[intro]: "s -s\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions"
inductive_cases transitionsE[elim]: "t \<in> transitions"

text \<open>Ensure there is no parallelism within a program\<close>
fun local_only
  where 
    "local_only (c\<^sub>1 || c\<^sub>2) = False" |
    "local_only (c\<^sub>1 ; c\<^sub>2) = (local_only c\<^sub>1 \<and> local_only c\<^sub>2)" |    
    "local_only (c\<^sub>1 \<sqinter> c\<^sub>2) = (local_only c\<^sub>1 \<and> local_only c\<^sub>2)" |  
    "local_only (c*) = (local_only c)" |    
    "local_only _ = True"

lemma local_only_silent:
  "c \<leadsto> c' \<Longrightarrow> local_only c \<Longrightarrow> local_only c'"
  by (induct rule: silent.induct) auto

section \<open>Predicate Manipulations\<close>

text \<open>Weakest Precondition, based on evaluation of an instruction\<close>
definition wp
  where "wp a P \<equiv> {m. \<forall>m'. (m,m') \<in> eval a \<longrightarrow> m' \<in> P}"

text \<open>Specification Check, ensuring an instruction conforms to a relation\<close>
definition guar
  where "guar \<alpha> G \<equiv> eval \<alpha> \<subseteq> G"

end

text \<open>Compose two state transitions\<close>
definition comp (infixr "\<otimes>" 60)
  where "comp a b \<equiv> {(m,m'). \<exists>m''. (m,m'') \<in> a \<and> (m'',m') \<in> b}"

text \<open>Stabilisation of a predicate under an environment step\<close>
definition st
  where "st R P \<equiv> {m. \<forall>m'. (m,m') \<in> R\<^sup>* \<longrightarrow> m' \<in> P}"

end