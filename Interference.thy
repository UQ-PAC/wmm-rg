theory Interference
  imports Semantics
begin

chapter \<open>Reordering Interference\<close>

text \<open>
Define the necessary side-conditions to ensure reordering cannot introduce interference.
First defines properties to avoid interference for the early execution of an instruction,
and then defines all possible early executions that may be observed for a program.
\<close>

locale interference = semantics

context interference
begin

section \<open>Interference Definitions\<close>

text \<open>
Independence of two instructions \<beta> and \<alpha> under environment R, 
such that the early execution of \<alpha> is assumed to be possible and 
cannot invalidate sequential reasoning.\<close>
definition inter\<^sub>\<alpha> :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "inter\<^sub>\<alpha> R G \<beta> \<alpha> \<equiv> 
          \<forall>Q. wp\<^sub>t R (wp\<^sub>\<alpha> \<beta> (wp\<^sub>t R (wp\<^sub>\<alpha> \<alpha> Q))) \<subseteq> wp\<^sub>t R (wp\<^sub>\<alpha> \<alpha>\<langle>\<beta>\<rangle> (wp\<^sub>t R (wp\<^sub>\<alpha> \<beta> Q))) \<and> 
          guar \<alpha>\<langle>\<beta>\<rangle> G"

text \<open>
Independence of program c and instruction \<alpha> under environment R,
such that the early execution of \<alpha> is assumed to be possible and 
cannot invalidate sequential reasoning.
Define by recursively iterating over the program and capturing the forwarding throughout.\<close>
fun inter\<^sub>c :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'a com \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "inter\<^sub>c R G (Basic \<beta>) \<alpha> = inter\<^sub>\<alpha> R G \<beta> \<alpha>" |
    "inter\<^sub>c R G (c\<^sub>1 ;; c\<^sub>2) \<alpha> = (inter\<^sub>c R G c\<^sub>1 \<alpha>\<llangle>c\<^sub>2\<rrangle> \<and> inter\<^sub>c R G c\<^sub>2 \<alpha>)" |
    "inter\<^sub>c R G (c\<^sub>1 \<sqinter> c\<^sub>2) \<alpha> = (inter\<^sub>c R G c\<^sub>1 \<alpha> \<and> inter\<^sub>c R G c\<^sub>2 \<alpha>)" |
    "inter\<^sub>c R G (c*) \<alpha> = inter\<^sub>c R G c \<alpha>" |
    "inter\<^sub>c R G _ \<alpha> = True"

text \<open>
Instrumented version of the semantics that collects the reordering effects.
Given c \<mapsto>[\<alpha>,r,\<alpha>'] c', this corresponds to c \<mapsto>\<alpha> c', such that
r should be the program \<alpha>' has to reorder with in c to execute and 
\<alpha> should be \<alpha>' forwarded across r.\<close>
inductive_set execute_collect :: "('a com \<times> 'a \<times> 'a com \<times> 'a \<times> 'a com) set"
  and execute_collect_abv :: "'a com \<Rightarrow> 'a \<Rightarrow> 'a com \<Rightarrow> 'a \<Rightarrow> 'a com \<Rightarrow> bool"
  ("_ \<mapsto>[_,_,_] _" [71,0,0,0,71] 70)
  where
  "c \<mapsto>[\<alpha>,t,\<gamma>] c' \<equiv> (c, \<alpha>, t, \<gamma>, c') \<in> execute_collect" |
  act[intro]:  "Basic \<alpha> \<mapsto>[\<alpha>,Nil,\<alpha>] Nil" |
  seq[intro]:  "c\<^sub>1 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' ;; c\<^sub>2" |
  ooo[intro]:  "c\<^sub>1 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' \<Longrightarrow> \<gamma> < c\<^sub>2 <\<^sub>c \<alpha> \<Longrightarrow> c\<^sub>2 ;; c\<^sub>1 \<mapsto>[\<gamma>,c\<^sub>2;;c,\<alpha>'] c\<^sub>2 ;; c\<^sub>1'"
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

section \<open>Interference Properties\<close>

text \<open>Interference check is preserved across a silent step\<close>
lemma inter_silentI [intro]:
  assumes "inter R G c" "c \<leadsto> c'"
  shows "inter R G c'"
  using assms by (auto simp: inter_def intro: reorder_trace.intros)

text \<open>Interference check is preserved across an execution step and prevents interference\<close>
lemma indep_stepI [intro]:
  assumes "inter R G c" "c \<mapsto>[\<alpha>,r,\<alpha>'] c'"
  shows "inter R G c' \<and> inter\<^sub>c R G r \<alpha>'"
  using assms reorder_trace.intros(1,3)
  unfolding inter_def by force

text \<open>Instrumented semantics collects valid reorderings\<close>
lemma collect_reorder:
  assumes "c \<mapsto>[\<alpha>',r,\<alpha>] c'"
  shows "\<alpha>' < r <\<^sub>c \<alpha>"
  using assms by (induct, auto)

text \<open>Convert a normal execution step into an instrumented step\<close>
lemma exec_collect:
  assumes "c \<mapsto>\<^sub>\<alpha> c'" "local c"
  shows "\<exists>r \<alpha>'. c \<mapsto>[\<alpha>,r,\<alpha>'] c'"
  using assms by induct auto

end

end