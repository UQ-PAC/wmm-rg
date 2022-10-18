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
Independence of two instructions \<beta> and \<alpha> under environment R/G, 
such that the early execution of \<alpha> cannot invalidate sequential reasoning.\<close>
definition inter\<^sub>\<alpha> :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  where "inter\<^sub>\<alpha> R G \<alpha>' \<beta> \<alpha> \<equiv> \<forall>P M Q. R,G \<turnstile>\<^sub>A P {\<beta>} M \<longrightarrow> R,G \<turnstile>\<^sub>A M {\<alpha>} Q \<longrightarrow> 
                                  (\<exists>M'. R,G \<turnstile>\<^sub>A P {\<alpha>'} M' \<and> R,G \<turnstile>\<^sub>A M' {\<beta>} Q)"

text \<open>
Independence of program c and instruction \<alpha> under environment R/G and memory model w,
such that the early execution of \<alpha> cannot invalidate sequential reasoning.
Define by recursively iterating over the program and capturing the forwarding throughout.\<close>
fun inter\<^sub>c :: "('a,'b) wmm \<Rightarrow> 'b rpred \<Rightarrow> 'b rpred \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  where 
    "inter\<^sub>c w R G (Basic \<beta>) \<alpha> = (\<forall>\<alpha>'. w \<alpha>' \<beta> \<alpha> \<longrightarrow> inter\<^sub>\<alpha> R G \<alpha>' \<beta> \<alpha>)" |
    "inter\<^sub>c w R G (c\<^sub>1 ;\<^sub>_ c\<^sub>2) \<alpha> = (\<forall>\<alpha>'. \<alpha>' < c\<^sub>2 <\<^sub>w \<alpha> \<longrightarrow> (inter\<^sub>c w R G c\<^sub>1 \<alpha>' \<and> inter\<^sub>c w R G c\<^sub>2 \<alpha>))" |
    "inter\<^sub>c w R G (Nil) \<alpha> = True" | 
    "inter\<^sub>c w R G _ \<alpha> = False"

text \<open>
Independence implications of the bookkeeping data structure collected 
via the instrumented semantics.\<close>
fun inter :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> ('a,'b) bookkeeping \<Rightarrow> bool"
  where
    "inter R G ((Reorder \<alpha>' w c)#r) = (inter\<^sub>c w R G c \<alpha>' \<and> inter R G r)" | 
    "inter R G (Scope#r) = (inter (pushrelSame R) (pushrelAll G) r)" | 
    "inter R G [] = True"

text \<open>Compute possible reorderings of the program using the instrumented semantics.\<close>
inductive reorder_trace
  where 
    "reorder_trace [] c" |
    "c \<leadsto> c' \<Longrightarrow> reorder_trace t c' \<Longrightarrow> reorder_trace t c" |
    "c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> reorder_trace t c' \<Longrightarrow> reorder_trace (r#t) c"

text \<open>Ensure all reorderings enforce the necessary interference property\<close>
definition rif
  where "rif R G c \<equiv> \<forall>t. reorder_trace t c \<longrightarrow> (\<forall>r \<in> set t. inter R G r)"

section \<open>Interference Properties\<close>

text \<open>Interference check is preserved across a silent step\<close>
lemma inter_silentI [intro]:
  assumes "rif R G c" "c \<leadsto> c'"
  shows "rif R G c'"
  using assms by (auto simp: rif_def intro: reorder_trace.intros)

text \<open>Interference check is preserved across an execution step and prevents interference\<close>
lemma indep_stepI [intro]:
  assumes "rif R G c" "c \<mapsto>[\<alpha>',r] c'"
  shows "rif R G c' \<and> inter R G r"
proof -
  have "reorder_trace [r] c" using assms reorder_trace.intros by blast
  hence "inter R G r" using assms by (auto simp: rif_def)
  moreover have "rif R G c'"
    using assms by (clarsimp simp: rif_def) (force intro: reorder_trace.intros(3))
  ultimately show ?thesis by simp
qed

end

end