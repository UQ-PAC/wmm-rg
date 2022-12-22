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

(*
lemma what:
  assumes "guar\<^sub>\<alpha> \<alpha> G" "G \<subseteq> G'"
  shows "guar\<^sub>\<alpha> \<alpha> G'" using assms unfolding guar_def by auto

lemma what2:
  assumes "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "G \<subseteq> G'"
  shows "R,G' \<turnstile>\<^sub>A M {\<alpha>} Q" using assms atomic_rule_def what by blast
*)

lemma invarIQ:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "G \<subseteq> (I \<Zinj> I)" "P \<subseteq> I" "stable R I"
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} I" 
proof -
  have a0:"guar\<^sub>\<alpha> \<alpha> G" using atomic_rule_def assms(1) by blast  
  have a7:"stable R P" using atomic_rule_def assms(1) by fast
  have a3:"guar\<^sub>\<alpha> \<alpha> (I \<Zinj> I)" using a0 assms(2) guar_def by blast 
  have a1:"P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q"  using atomic_rule_def assms(1) by fast
  have a4:"P \<subseteq> {m. m \<in> (vc \<alpha>) \<and> (\<forall>m'. (m,m') \<in> (beh \<alpha>) \<longrightarrow> m' \<in> Q)}" using a1 wp_def by force
  have a5:"{(m,m'). m \<in> (vc \<alpha>) \<and> (m,m') \<in> (beh \<alpha>)} \<subseteq>(I \<Zinj> I)" using a3 guar_def by blast 
  have a6:"\<forall> m m'. m \<in> (vc \<alpha>) \<and> (m,m') \<in> (beh \<alpha>) \<longrightarrow> m \<notin> I \<or> m' \<in> I" using a5 impProd_def
    by (smt (verit, ccfv_threshold) Collect_mono_iff case_prod_conv)
  have a2:"P \<subseteq> wp\<^sub>\<alpha> \<alpha> I" using a1 a3 assms(2) wp_def a6 assms(3)
    by (smt (verit, best) Int_Collect subset_iff)
  show ?thesis using a2 a0 a7 assms(4) atomic_rule_def by auto
qed

lemma invarIP:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "G \<subseteq> (I \<Zinj> I)" "P \<subseteq> I" "stable R I"
  shows "I \<subseteq> (vc \<alpha>) \<longrightarrow> R,G \<turnstile>\<^sub>A I {\<alpha>} I"
proof -
  have a0:"guar\<^sub>\<alpha> \<alpha> G" using atomic_rule_def assms(1) by blast  
  have a7:"stable R P" using atomic_rule_def assms(1) by fast
  have a3:"guar\<^sub>\<alpha> \<alpha> (I \<Zinj> I)" using a0 assms(2) guar_def by blast 
  have a1:"P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q"  using atomic_rule_def assms(1) by fast
  have a5:"{(m,m'). m \<in> (vc \<alpha>) \<and> (m,m') \<in> (beh \<alpha>)} \<subseteq>(I \<Zinj> I)" using a3 guar_def by blast 
  have a6:"\<forall> m m'. m \<in> (vc \<alpha>) \<and> (m,m') \<in> (beh \<alpha>) \<longrightarrow> m \<notin> I \<or> m' \<in> I" using a5 impProd_def
    by (smt (verit, ccfv_threshold) Collect_mono_iff case_prod_conv)
  have a2:"P \<subseteq> wp\<^sub>\<alpha> \<alpha> I" using a1 a3 assms(2) wp_def a6 assms(3)
    by (smt (verit, best) Int_Collect subset_iff)
  have a8:"I \<subseteq> (vc \<alpha>) \<longrightarrow> I \<subseteq> wp\<^sub>\<alpha> \<alpha> I" using a1 a3 assms(2,3) guar_def a5 a6 a2 
    by (smt (verit, best) Int_Collect basic_trans_rules(31) subsetI wp_def)
  show ?thesis using a8 a0 a7 assms(4) atomic_rule_def by auto
qed


lemma interAtom:
  assumes "R,G \<turnstile>\<^sub>A P {\<beta>} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "G = (I \<Zinj> I)" "P \<subseteq> I" "stable R I" 
          "I \<subseteq> (vc \<beta>)" "I \<subseteq> (vc \<alpha>)" "I \<subseteq> Q"
  shows "\<exists> M'. R,G \<turnstile>\<^sub>A P {\<alpha>'} M' \<and> R,G \<turnstile>\<^sub>A M' {\<beta>} Q" 
proof -
  have i0:"R,G \<turnstile>\<^sub>A I {\<beta>} I" using assms(1,3,4,5,6) invarIP by fast
  have i1:"R,G \<turnstile>\<^sub>A I {\<alpha>} I" using assms(2,3,4,5,7) invarIP by blast
  have i2:"R,G \<turnstile>\<^sub>A I {\<alpha>'} I" using i1 sorry
  have i3:"guar\<^sub>\<alpha> \<alpha> G" using atomic_rule_def assms(2) by blast 
  have i4:"stable R P" using assms(1) atomic_rule_def by blast
  have i5:"guar\<^sub>\<alpha> \<alpha>' G" using atomic_rule_def i2 by blast 
  have i6:"I \<subseteq> wp\<^sub>\<alpha> \<alpha>' I" using i2 atomic_rule_def by fast
  have i7:"P \<subseteq> wp\<^sub>\<alpha> \<alpha>' I" using i6 assms(4) by fast
  have i8:"R,G \<turnstile>\<^sub>A P {\<alpha>'} I" using assms(5) i4 i5 i7 atomic_rule_def by auto
  have i9:"stable R Q" using atomic_rule_def assms(2) by blast 
  have i10:"R,G \<turnstile>\<^sub>A I {\<beta>} Q" using i0 assms(8) i9 atomic_post by blast
  show ?thesis using i8 i10 inter\<^sub>\<alpha>_def assms(1,2) by blast
qed

lemma interAtom2:
  assumes "G = (I \<Zinj> I)" "P \<subseteq> I" "stable R I" 
          "I \<subseteq> (vc \<beta>)" "I \<subseteq> (vc \<alpha>)" "I \<subseteq> Q"
  shows "inter\<^sub>A R G \<alpha>' \<beta> \<alpha>" using assms interAtom sorry




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

lemma inter_monoG:
  assumes "G \<subseteq> G'" "inter R G r"
  shows "inter R G' r" sorry

end

end