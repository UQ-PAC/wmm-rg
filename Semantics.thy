theory Semantics
  imports Main
begin

section \<open>Semantics\<close>

text \<open>
Define the small-step semantics for a simple While language.
\<close>

subsection \<open> Syntax \<close> 

datatype 'a Stmt =
  Skip
  | Basic "'a"
  | Seq "'a Stmt" "'a Stmt" (infixr ";;" 80)
  | Choice "'a Stmt" "'a Stmt" (infixr "\<sqinter>" 150)
  | Loop "'a Stmt" ("_*" [100] 150)
  | Parallel "'a Stmt" "'a Stmt"  (infixr "||" 150)

subsection \<open> Semantics \<close>

inductive_set prog :: "('a Stmt \<times> 'a \<times> 'a Stmt) set"
  and prog_abv :: "'a Stmt \<Rightarrow> 'a \<Rightarrow> 'a Stmt \<Rightarrow> bool"
  ("_ \<mapsto>\<^sub>_ _" [11,0,0] 70)
  where
  "c \<mapsto>\<^sub>\<alpha> c' \<equiv> (c, \<alpha>, c') \<in> prog" |
  act[intro]:  "Basic \<alpha> \<mapsto>\<^sub>\<alpha> Skip" |
  seq[intro]:  "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1' ;; c\<^sub>2" |
  par1[intro]: "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1' || c\<^sub>2" |
  par2[intro]: "c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>1 || c\<^sub>2'"

fun unroll
  where "unroll 0 c = Skip" | "unroll (Suc n) c = c ;; unroll n c"

inductive_set rw :: "('a Stmt \<times> 'a Stmt) set"
  and rw_abv :: "'a Stmt \<Rightarrow> 'a Stmt \<Rightarrow> bool"
  ("_ \<leadsto> _" [11,0] 70)
  where
  "c \<leadsto> c' \<equiv> (c, c') \<in> rw" |
  seq[intro]:   "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<leadsto> c\<^sub>1' ;; c\<^sub>2" |
  seqE[intro]:  "Skip ;; c\<^sub>1 \<leadsto> c\<^sub>1" |
  left[intro]:  "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>1" |
  right[intro]: "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>2" |
  loop[intro]:  "c* \<leadsto> unroll n c" |
  par1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1' || c\<^sub>2" |
  par2[intro]:  "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1 || c\<^sub>2'" |
  parE1[intro]: "Skip || c \<leadsto> c" |
  parE2[intro]: "c || Skip \<leadsto> c"

subsection \<open>Elimination Properties\<close>

lemma prog_skipE [elim]:
  assumes "Skip \<mapsto>\<^sub>\<alpha> c"
  obtains "False"
  using assms by (blast elim: prog.cases)

lemma rw_skipE [elim]:
  assumes "Skip \<leadsto> c"
  obtains "False"
  using assms by (blast elim: rw.cases)

lemma prog_actE [elim]:
  assumes "Basic \<alpha> \<mapsto>\<^sub>\<beta> c"
  obtains "\<beta> = \<alpha>" "c = Skip"
  using assms by (blast elim: prog.cases)

lemma rw_actE [elim]:
  assumes "Basic \<alpha> \<leadsto> c"
  obtains "False"
  using assms by (blast elim: rw.cases)

lemma prog_seqE [elim]:
  assumes "c\<^sub>1 ;; c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>3"
  obtains c\<^sub>1' where "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>1'" "c\<^sub>3 = c\<^sub>1' ;; c\<^sub>2"
  using assms by (blast elim: prog.cases)

lemma rw_seqE [elim]:
  assumes "c\<^sub>1 ;; c\<^sub>2 \<leadsto> c\<^sub>3"
  obtains c\<^sub>1' where "c\<^sub>1 \<leadsto> c\<^sub>1'" "c\<^sub>3 = c\<^sub>1' ;; c\<^sub>2" | "c\<^sub>1 = Skip" "c\<^sub>2 = c\<^sub>3"
  using assms by (blast elim: rw.cases)

lemma prog_choiceE [elim]:
  assumes "c\<^sub>1 \<sqinter> c\<^sub>2 \<mapsto>\<^sub>\<alpha> c\<^sub>3"
  obtains "False"
  using assms by (blast elim: prog.cases)

lemma rw_choiceE [elim]:
  assumes "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>3"
  obtains (left) "c\<^sub>1 = c\<^sub>3" | (right) "c\<^sub>2 = c\<^sub>3"
  using assms by (blast elim: rw.cases)

lemma prog_loopE [elim]:
  assumes "c\<^sub>1* \<mapsto>\<^sub>\<beta> c\<^sub>2"
  obtains "False"
  using assms by (blast elim: prog.cases)

lemma rw_loopE [elim]:
  assumes "c\<^sub>1* \<leadsto> c\<^sub>2"
  obtains n where "c\<^sub>2 = unroll n c\<^sub>1"
  using assms by (blast elim: rw.cases)

lemma prog_parE [elim]:
  assumes "c\<^sub>1 || c\<^sub>2 \<mapsto>\<^sub>\<beta> c\<^sub>3"
  obtains (par1) c\<^sub>1' where "c\<^sub>1 \<mapsto>\<^sub>\<beta> c\<^sub>1'" "c\<^sub>3 = c\<^sub>1' || c\<^sub>2" |
          (par2) c\<^sub>2' where "c\<^sub>2 \<mapsto>\<^sub>\<beta> c\<^sub>2'" "c\<^sub>3 = c\<^sub>1 || c\<^sub>2'"
  using assms by (blast elim: prog.cases)

lemma rw_parE [elim]:
  assumes "c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>3"
  obtains (par1) c\<^sub>1' where "c\<^sub>1 \<leadsto> c\<^sub>1'" "c\<^sub>3 = c\<^sub>1' || c\<^sub>2" |
          (par2) c\<^sub>2' where "c\<^sub>2 \<leadsto> c\<^sub>2'" "c\<^sub>3 = c\<^sub>1 || c\<^sub>2'" |
          (par1E) "c\<^sub>1 = Skip" "c\<^sub>3 = c\<^sub>2" |
          (par2E) "c\<^sub>2 = Skip" "c\<^sub>3 = c\<^sub>1" 
  using assms by (blast elim: rw.cases)

end