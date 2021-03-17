theory Interference
  imports Semantics
begin

locale interference = semantics re fwd eval
  for re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100)
  and fwd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<langle>_\<rangle>" [1000,0] 1000)
  and eval :: "'a \<Rightarrow> 's rel"

context interference
begin

section \<open>Interference Definitions\<close>

text \<open>Independence of two instructions \<beta> and \<alpha> under environment R, 
      such that the early execution of \<alpha> is assumed to be possible and 
      cannot invalidate sequential reasoning\<close>
definition inter\<^sub>a
  where "inter\<^sub>a R G \<beta> \<alpha> \<equiv> R\<^sup>* \<otimes> eval \<alpha>\<langle>\<beta>\<rangle> \<otimes> R\<^sup>* \<otimes> eval \<beta> \<subseteq> R\<^sup>* \<otimes> eval \<beta> \<otimes> R\<^sup>* \<otimes> eval \<alpha> \<and> spec \<alpha>\<langle>\<beta>\<rangle> G"

text \<open>Independence of program c and instruction \<alpha> under environment R, 
      such that the early execution of \<alpha> is assumed to be possible and 
      cannot invalidate sequential reasoning\<close>
fun inter\<^sub>c
  where
    "inter\<^sub>c R G (Basic \<beta>) \<alpha> = inter\<^sub>a R G \<beta> \<alpha>" |
    "inter\<^sub>c R G (c\<^sub>1 ; c\<^sub>2) \<alpha> = (inter\<^sub>c R G c\<^sub>1 \<alpha>\<llangle>c\<^sub>2\<rrangle> \<and> inter\<^sub>c R G c\<^sub>2 \<alpha>)" |
    "inter\<^sub>c R G (c\<^sub>1 \<sqinter> c\<^sub>2) \<alpha> = (inter\<^sub>c R G c\<^sub>1 \<alpha> \<and> inter\<^sub>c R G c\<^sub>2 \<alpha>)" |
    "inter\<^sub>c R G (c*) \<alpha> = inter\<^sub>c R G c \<alpha>" |
    "inter\<^sub>c R G _ \<alpha> = True"

text \<open>Instrumented version of the semantics that collects the reordering effects\<close>
inductive_set execute_collect :: "('a com \<times> 'a \<times> 'a com \<times> 'a \<times> 'a com) set"
  and execute_collect_abv :: "'a com \<Rightarrow> 'a \<Rightarrow> 'a com \<Rightarrow> 'a \<Rightarrow> 'a com \<Rightarrow> bool"
  ("_ \<mapsto>[_,_,_] _" [71,0,0,0,71] 70)
  where
  "c \<mapsto>[\<alpha>,t,\<gamma>] c' \<equiv> (c, \<alpha>, t, \<gamma>, c') \<in> execute_collect" |
  act[intro]:  "Basic \<alpha> \<mapsto>[\<alpha>,Nil,\<alpha>] Nil" |
  pre[intro]:  "c\<^sub>1 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' \<Longrightarrow> c\<^sub>1 ; c\<^sub>2 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' ; c\<^sub>2" |
  pst[intro]:  "c\<^sub>1 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' \<Longrightarrow> \<gamma> < c\<^sub>2 <\<^sub>p \<alpha> \<Longrightarrow> c\<^sub>2 ; c\<^sub>1 \<mapsto>[\<gamma>,c\<^sub>2;c,\<alpha>'] c\<^sub>2 ; c\<^sub>1'"
inductive_cases execute_collect[elim]: "c\<^sub>1 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1'"

text \<open>Compute possible reorderings of the program using the instrumented semantics\<close>
inductive reorder_trace
  where 
    "reorder_trace [] c" |
    "c \<leadsto> c' \<Longrightarrow> reorder_trace t c' \<Longrightarrow> reorder_trace t c" |
    "c \<mapsto>[\<alpha>,r,\<alpha>'] c' \<Longrightarrow> reorder_trace t c' \<Longrightarrow> reorder_trace ((r,\<alpha>')#t) c"

text \<open>Ensure all reorderings enforce the necessary interference property\<close>
definition inter
  where "inter R G c \<equiv> \<forall>t. reorder_trace t c \<longrightarrow> (\<forall>(r,\<alpha>) \<in> set t. inter\<^sub>c R G r \<alpha>)"

text \<open>Interference is preserved across a silent step\<close>
lemma inter_silentI [intro]:
  assumes "inter R G c" "c \<leadsto> c'"
  shows "inter R G c'"
  using assms by (auto simp: inter_def intro: reorder_trace.intros)

text \<open>Interference is preserved across an execution step and prevents interference\<close>
lemma indep_stepI [intro]:
  assumes "inter R G c" "c \<mapsto>[\<alpha>,r,\<alpha>'] c'"
  shows "inter R G c' \<and> inter\<^sub>c R G r \<alpha>'"
  using assms reorder_trace.intros(1,3)
  unfolding inter_def by force

text \<open>Instrumented semantics collects valid reorderings\<close>
lemma collect_reorder:
  assumes "c \<mapsto>[\<alpha>',r,\<alpha>] c'"
  shows "\<alpha>' < r <\<^sub>p \<alpha>"
  using assms by (induct, auto)

text \<open>Convert a normal execution step into an instrumented step\<close>
lemma exec_collect:
  assumes "c \<mapsto>\<^sub>\<alpha> c'" "local_only c"
  shows "\<exists>r \<alpha>'. c \<mapsto>[\<alpha>,r,\<alpha>'] c'"
  using assms by induct auto

end

end