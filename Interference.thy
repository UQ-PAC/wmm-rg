theory Interference
  imports Semantics
begin

chapter \<open>Reordering Interference\<close>

text \<open>
Define the necessary side-conditions to ensure reordering cannot introduce interference.
First defines properties to avoid interference for the early execution of an instruction,
and then defines all possible early executions that may be observed for a program.
\<close>
                         
locale interference = semantics re fwd
  for re :: "('a,'b) inst \<Rightarrow> ('a,'b) inst \<Rightarrow> bool" (infix "\<hookleftarrow>" 100)
  and fwd :: "('a,'b) inst \<Rightarrow> ('a,'b) inst \<Rightarrow> ('a,'b) inst" ("_\<langle>_\<rangle>" [1000,0] 1000)

context interference
begin

section \<open>Interference Definitions\<close>

text \<open>
Independence of two instructions \<beta> and \<alpha> under environment R, 
such that the early execution of \<alpha> is assumed to be possible and 
cannot invalidate sequential reasoning.\<close>
definition inter\<^sub>\<alpha> :: "'a rpred \<Rightarrow> 'a rpred \<Rightarrow> ('a,'b) inst \<Rightarrow> ('a,'b) inst \<Rightarrow> bool"
  where "inter\<^sub>\<alpha> R G \<beta> \<alpha> \<equiv> 
          Env R ; Basic \<beta> ; Env R ; Basic \<alpha> \<sqsubseteq> Env R ; Basic \<alpha>\<langle>\<beta>\<rangle> ; Env R ; Basic \<beta> \<and>
          guar \<alpha>\<langle>\<beta>\<rangle> G"

text \<open>
Independence of program c and instruction \<alpha> under environment R,
such that the early execution of \<alpha> is assumed to be possible and 
cannot invalidate sequential reasoning.
Define by recursively iterating over the program and capturing the forwarding throughout.\<close>
fun inter\<^sub>c :: "'a rpred \<Rightarrow> 'a rpred \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) inst \<Rightarrow> bool"
  where
    "inter\<^sub>c R G (Basic \<beta>) \<alpha> = inter\<^sub>\<alpha> R G \<beta> \<alpha>" |
    "inter\<^sub>c R G (c\<^sub>1 ; c\<^sub>2) \<alpha> = (inter\<^sub>c R G c\<^sub>1 \<alpha>\<llangle>c\<^sub>2\<rrangle> \<and> inter\<^sub>c R G c\<^sub>2 \<alpha>)" |
    "inter\<^sub>c R G (c\<^sub>1 \<sqinter> c\<^sub>2) \<alpha> = (inter\<^sub>c R G c\<^sub>1 \<alpha> \<and> inter\<^sub>c R G c\<^sub>2 \<alpha>)" |
    "inter\<^sub>c R G (c*) \<alpha> = inter\<^sub>c R G c \<alpha>" |
    "inter\<^sub>c R G _ \<alpha> = True"

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
proof -
  have "reorder_trace [(r, \<alpha>')] c" using assms reorder_trace.intros by simp
  hence "inter\<^sub>c R G r \<alpha>'" using assms by (auto simp: inter_def)
  thus ?thesis using assms reorder_trace.intros(3)[OF assms(2)] inter_def by force
qed

end

end