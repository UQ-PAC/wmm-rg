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
apply (auto simp add: thr_stable thr_wp thr_guar)
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
  using assms unfolding atomic_rule_def wp'_def stable_def by blast

text \<open>Add an invariant across an atomic judgement\<close>
lemma atomic_invI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  assumes "stable R\<^sub>2 I" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>A P \<inter> I {\<alpha>} Q \<inter> I"
  unfolding atomic_rule_def
proof (safe, goal_cases)
  case (1 m)
  hence
    "m \<in> vc \<alpha>"
    "Id_on (P \<inter> vc \<alpha>) O beh \<alpha> \<subseteq> R\<^sub>2"
    using assms(1,3) by (auto simp: wp'_def guar_def atomic_rule_def)
  hence "m \<in> wp\<^sub>\<alpha> \<alpha> I" using assms(2) 1 sledgehammer    
  moreover have "m \<in> wp\<^sub>\<alpha> \<alpha> Q" using 1 assms(1) by (auto simp: atomic_rule_def wp_def)
  ultimately show ?
case by (auto simp: wp'_def)
qed (insert assms, auto simp: atomic_rule_def)

text \<open>Atomic rule for a false precondition\<close>
lemma atomic_falseI [intro]:
  assumes "guar\<^sub>\<alpha> \<beta> G"
  shows "R,G \<turnstile>\<^sub>A {} {\<beta>} {}"
  using assms unfolding atomic_rule_def by auto

fun beh_at :: "('a,'b) basic \<Rightarrow> 'b \<Rightarrow> 'b set" where
"beh_at \<alpha> \<sigma> = {\<sigma>' |\<sigma>'. (\<sigma>,\<sigma>') \<in> beh \<alpha>}"

fun G_at :: "'b rel \<Rightarrow> 'b \<Rightarrow> 'b set" where
"G_at G \<sigma> = {\<sigma>' |\<sigma>'. (\<sigma>,\<sigma>') \<in> G}"

lemma guar\<^sub>\<alpha>_alt: "guar\<^sub>\<alpha> \<alpha> G = (\<forall>\<sigma>\<in>vc \<alpha>. beh_at \<alpha> \<sigma> \<subseteq> G_at G \<sigma>)"
unfolding guar_def by auto

lemma guar\<^sub>\<alpha>_alt2: "guar\<^sub>\<alpha> \<alpha> G = ({(m,m')|m m'. m \<in> vc \<alpha>} \<inter> beh \<alpha> \<subseteq> G)"
unfolding guar_def
by fast

lemma vc_subset_uncap: "vc \<beta> \<subseteq> {push m s |m. m \<in> vc (capBasic s \<beta>)}"
by auto (metis (full_types) popr_push push_intro)

lemma beh_subset_uncap: "beh \<beta> \<subseteq> uncapGuar (beh (capBasic s \<beta>))"
by auto (metis (full_types) popr_push push_intro)

lemma guar_capB_to_guar_uncapG:
  "guar\<^sub>\<alpha> (capBasic s \<beta>) G \<Longrightarrow> guar\<^sub>\<alpha> \<beta> (uncapGuar G)"
apply (simp only: guar\<^sub>\<alpha>_alt2)
proof (intro subrelI)
  assume 1: "{(m, m') |m m'. m \<in> vc (capBasic s \<beta>)} \<inter> beh (capBasic s \<beta>) \<subseteq> G"
    (is "?V \<inter> ?B \<subseteq> G")
  hence g3: "uncapGuar ?V \<inter> uncapGuar ?B \<subseteq> uncapGuar G"
    using uncapGuar_mono[of "?V \<inter> ?B" G] uncapGuar_inter by fast
  fix x x'
  assume 2: "(x,x') \<in> {(m, m') |m m'. m \<in> vc \<beta>} \<inter> beh \<beta>"
  hence "x \<in> {push m s |m. m \<in> vc (capBasic s \<beta>)}" using vc_subset_uncap by fast
  hence g1: "(x,x') \<in> uncapGuar ?V" using 2 push_intro by fastforce
  have g2: "(x,x') \<in> uncapGuar ?B" using 2 beh_subset_uncap by fast
  thus "(x,x') \<in> uncapGuar G" using g1 g2 g3 by fast
qed

term Id_on

fun UNIV_on :: "'a set \<Rightarrow> ('a \<times> 'b) set" where
"UNIV_on A = {(a,b) |a b. a \<in> A}"

lemma "a\<in>A \<Longrightarrow> (a,b) \<in> UNIV_on A"
by simp

lemma cap_wp_capBasic:
  "capPred (wp\<^sub>\<alpha> (uncapBasic s \<alpha>) (uncapPred s' Q)) = wp\<^sub>\<alpha> \<alpha> Q"
unfolding wp_def
proof -
  have "capPred (vc (uncapBasic s \<alpha>)) = vc \<alpha>"
    using cap_uncapPred by auto
  have "vc (uncapBasic s \<alpha>) = uncapPred s (vc \<alpha>)"
    by simp
  (* is there or does there need to be a link between vc and beh? *)
  (* what does it mean when an initial state does not appear in the behaviours? *)
  have "capPred {m. \<forall>m'. (m, m') \<in> uncapBeh s (beh \<alpha>) \<longrightarrow> m' \<in> uncapPred s' Q}
    = {m. \<forall>m'. (m, m') \<in> beh \<alpha> \<longrightarrow> m' \<in> Q}"
    sorry
  show ?thesis sorry
qed



end