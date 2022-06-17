theory Atomics
  imports Syntax State
begin

chapter \<open>Atomic Actions\<close>

text \<open>
Describe concepts the logic must know about atomic instructions. 
\<close>

section \<open>Atomic Properties\<close>

text \<open>Weakest precondition of a basic instruction, based on the locale's 
      verification conditions and behaviours.\<close>
abbreviation wp\<^sub>\<alpha> :: "('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp\<^sub>\<alpha> \<alpha> Q \<equiv> wp (vc \<alpha>) (beh \<alpha>) Q"

text \<open>Specification check, ensuring an instruction conforms to a relation\<close>
abbreviation guar\<^sub>\<alpha> :: "('a,'b) basic \<Rightarrow> 'b rpred \<Rightarrow> bool"
  where "guar\<^sub>\<alpha> \<alpha> G \<equiv> guar (vc \<alpha>) (beh \<alpha>) G"

section \<open>Atomic Rule\<close>

text \<open>Rule for an atomic operation\<close>
definition atomic_rule :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> ('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>A _ {_} _" [65,0,0,0,65] 65)
  where "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<equiv> P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q \<and> guar\<^sub>\<alpha> \<alpha> G \<and> stable R P \<and> stable R Q"

lemma atomicI [intro]:
  assumes "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "guar\<^sub>\<alpha> \<alpha> G" "stable R P" "stable R Q"
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
using assms
by (auto simp add: atomic_rule_def)

lemma thr_atomic:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  shows "thr\<^sub>R op R,thr\<^sub>G op G \<turnstile>\<^sub>A thr\<^sub>P op l P {thr\<^sub>\<alpha> op l l' \<alpha>} thr\<^sub>P op l' Q"
using assms
unfolding atomic_rule_def thr\<^sub>\<alpha>_def 
(* by (simp add: thr_stable thr_wp thr_guar) *)
oops


subsection \<open>Derived Properties\<close>

text \<open>Re-establish an atomic judgement over a stronger stable precondition\<close>
lemma atomic_pre:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "P' \<subseteq> P" "stable R P'"
  shows "R,G \<turnstile>\<^sub>A P' {\<alpha>} Q"
  using assms unfolding atomic_rule_def by fast

text \<open>Strengthen the rely and weaken the guarantee for an atomic judgement\<close>
lemma atomic_conseqI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "R' \<subseteq> R" "G \<subseteq> G'"
  shows "R',G' \<turnstile>\<^sub>A P {\<alpha>} Q"
  using assms unfolding atomic_rule_def guar_def by blast

text \<open>Atomic judgements over the same instruction can be combined\<close>
lemma actomic_conjI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P\<^sub>1 {\<alpha>} Q\<^sub>1" "R,G  \<turnstile>\<^sub>A P\<^sub>2 {\<alpha>} Q\<^sub>2"
  shows "R,G \<turnstile>\<^sub>A P\<^sub>1 \<inter> P\<^sub>2 {\<alpha>} Q\<^sub>1 \<inter> Q\<^sub>2"
  using assms unfolding atomic_rule_def wp_def stable_def by blast

text \<open>Add an invariant across an atomic judgement\<close>
lemma atomic_invI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  assumes "stable R\<^sub>2 I" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>A P \<inter> I {\<alpha>} Q \<inter> I"
  unfolding atomic_rule_def
proof (safe, goal_cases)
  case (1 m)
  hence "{(m,m'). m \<in> P \<inter> vc \<alpha> \<and> (m,m') \<in> beh \<alpha>} \<subseteq> R\<^sub>2\<^sup>=" "m \<in> vc \<alpha>"
    "\<exists>m'. (m, m') \<in> beh \<alpha>"
    using assms(1,3) by (auto simp: wp_def guar_def atomic_rule_def)
  hence "m \<in> wp\<^sub>\<alpha> \<alpha> I" using assms(2) 1 by (auto simp: wp_def stable_def)
  moreover have "m \<in> wp\<^sub>\<alpha> \<alpha> Q" using 1 assms(1) by (auto simp: atomic_rule_def wp_def)
  ultimately show ?case by (auto simp: wp_def)
qed (insert assms, auto simp: atomic_rule_def wp_def)

text \<open>Atomic rule for a false precondition\<close>
lemma atomic_falseI [intro]:
  assumes "guar\<^sub>\<alpha> \<beta> G"
  shows "R,G \<turnstile>\<^sub>A {} {\<beta>} {}"
  using assms unfolding atomic_rule_def by auto



lemma guar\<^sub>\<alpha>_rel: "guar\<^sub>\<alpha> \<alpha> G = (Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G)"
unfolding guar_def
by fast

lemma guar_uncapE:
  "guar\<^sub>\<alpha> (uncapBasic s \<alpha>) (uncapGuar G) \<Longrightarrow> guar\<^sub>\<alpha> \<alpha> G"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc (uncapBasic s \<alpha>)) O beh (uncapBasic s \<alpha>) \<subseteq> uncapGuar G"
  hence "capGuar (Id_on (uncapPred s (vc \<alpha>))) O beh \<alpha> \<subseteq> G"
    by simp (metis capGuar_relcomp capGuar_mono cap_uncapBeh cap_uncapGuar)
  thus "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
    using capPred_in_capGuar cap_uncapPred by blast
qed

lemma guar_uncapI:
  "guar\<^sub>\<alpha> \<alpha> G \<Longrightarrow> guar\<^sub>\<alpha> (uncapBasic s \<alpha>) (uncapGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
  hence "uncapGuar (Id_on (vc \<alpha>)) O uncapGuar (beh \<alpha>) \<subseteq> uncapGuar G"
    using uncapGuar_relcomp uncapGuar_mono by blast
  (* uncap with specific 's' is always within general uncapGuar *)
  moreover have "Id_on (uncapPred s (vc \<alpha>)) \<subseteq> uncapGuar (Id_on (vc \<alpha>))"
    using uncapGuar_capPred by fastforce
  moreover have "uncapBeh s (beh \<alpha>) \<subseteq> uncapGuar (beh \<alpha>)"
    using uncapBeh_in_uncapGuar by auto
  ultimately show
    "Id_on (vc (uncapBasic s \<alpha>)) O beh (uncapBasic s \<alpha>) \<subseteq> uncapGuar G"
    by auto
qed

lemma guar_capE:
  "guar\<^sub>\<alpha> (capBasic \<beta>) (capGuar G) \<Longrightarrow> guar\<^sub>\<alpha> \<beta> G"
using guar_uncapI
by (metis cap_uncapBeh cap_uncapPred snd_conv snd_swap swap_simp uncapPred_intro uncap_capGuar)

lemma guar_capI:
  "guar\<^sub>\<alpha> \<beta> G \<Longrightarrow> guar\<^sub>\<alpha> (capBasic \<beta>) (capGuar G)"
using guar_uncapE
by (metis cap_uncapBeh cap_uncapPred fst_conv snd_conv uncapPred_intro uncap_capGuar)

lemma cap_wp_capBasic:
  "capPred (wp\<^sub>\<alpha> (uncapBasic s \<alpha>) (uncapPred s' Q)) = wp\<^sub>\<alpha> \<alpha> Q"
proof -
  have
    "capPred {m. \<forall>m'. (m, m') \<in> beh (uncapBasic s \<alpha>) \<longrightarrow> m' \<in> uncapPred s' Q}
      = {m. \<forall>m'. (m, m') \<in> beh \<alpha> \<longrightarrow> m' \<in> Q}"
      unfolding uncapPred_def uncapBeh_def capPred_def
    by auto (metis (full_types) popr_push push_intro)+
  moreover have "capPred (vc (uncapBasic s \<alpha>)) = vc \<alpha>" by force
  moreover have "capPred (Domain (beh (uncapBasic s \<alpha>))) = Domain (beh \<alpha>)" 
    unfolding capPred_def uncapBeh_def by force
  ultimately show ?thesis by (simp only: wp_rel_partial capPred_inter)
qed

end