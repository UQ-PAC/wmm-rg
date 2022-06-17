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

fun beh_at :: "('a,'b) basic \<Rightarrow> 'b \<Rightarrow> 'b set" where
"beh_at \<alpha> \<sigma> = {\<sigma>' |\<sigma>'. (\<sigma>,\<sigma>') \<in> beh \<alpha>}"

fun G_at :: "'b rel \<Rightarrow> 'b \<Rightarrow> 'b set" where
"G_at G \<sigma> = {\<sigma>' |\<sigma>'. (\<sigma>,\<sigma>') \<in> G}"

lemma guar\<^sub>\<alpha>_alt: "guar\<^sub>\<alpha> \<alpha> G = (\<forall>\<sigma>\<in>vc \<alpha>. beh_at \<alpha> \<sigma> \<subseteq> G_at G \<sigma>)"
unfolding guar_def by auto

lemma guar\<^sub>\<alpha>_alt2: "guar\<^sub>\<alpha> \<alpha> G = ({(m,m')|m m'. m \<in> vc \<alpha>} \<inter> beh \<alpha> \<subseteq> G)"
unfolding guar_def
by fast

lemma guar\<^sub>\<alpha>_rel: "guar\<^sub>\<alpha> \<alpha> G = (Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G)"
unfolding guar_def
by fast

lemma vc_subset_uncap: "vc \<beta> \<subseteq> {push m s |m. m \<in> vc (capBasic \<beta>)}"
by auto (metis (full_types) popr_push push_intro)

lemma beh_subset_uncap: "beh \<beta> \<subseteq> uncapGuar (beh (capBasic \<beta>))"
by auto (metis (full_types) popr_push push_intro)

lemma guar_eq:
  "guar\<^sub>\<alpha> (capBasic \<alpha>) (capGuar G) = guar\<^sub>\<alpha> \<alpha> G"
unfolding guar\<^sub>\<alpha>_rel
proof -
  have "uncapGuar (Id_on (vc (capBasic \<alpha>))) = Id_on (vc \<alpha>)"
    using uncap_capGuar push_intro sorry
  moreover have "uncapGuar (beh (capBasic \<alpha>)) = beh \<alpha>"
    using uncap_capGuar by fastforce
  moreover have 
    "(Id_on (vc (capBasic \<alpha>)) O beh (capBasic \<alpha>) \<subseteq> capGuar G)
    = (uncapGuar (Id_on (vc (capBasic \<alpha>))) O uncapGuar (beh (capBasic \<alpha>)) \<subseteq> G)"
    by (metis uncapGuar_eq uncapGuar_relcomp uncap_capGuar)
  ultimately show
    "(Id_on (vc (capBasic \<alpha>)) O beh (capBasic \<alpha>) \<subseteq> capGuar G)
    = (Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G)"
    by presburger
oops

lemma guar_capI:
  assumes "guar\<^sub>\<alpha> \<alpha> G"
  shows "guar\<^sub>\<alpha> (capBasic \<alpha>) (capGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof (intro subrelI)
  have "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
    using assms unfolding guar\<^sub>\<alpha>_rel by simp
  hence subset: "capGuar (Id_on (vc \<alpha>)) O capGuar (beh \<alpha>) \<subseteq> capGuar G"
    using capGuar_relcomp capGuar_mono by blast
  fix m m'
  assume mm': "(m,m') \<in> Id_on (vc (capBasic \<alpha>)) O beh (capBasic \<alpha>)"
  hence "(m,m') \<in> capBeh (beh \<alpha>)" by auto
  hence "(m,m') \<in> capGuar (beh \<alpha>)" by auto
  moreover have "(m,m) \<in> capGuar (Id_on (vc \<alpha>))" using mm' by auto
  ultimately have 
    "(m,m') \<in> capGuar (Id_on (vc \<alpha>)) O capGuar (beh \<alpha>)" by fast
  thus "(m,m') \<in> capGuar G" using subset by fast
qed

lemma guar_uncapI:
  assumes "guar\<^sub>\<alpha> \<alpha> G"
  shows "guar\<^sub>\<alpha> (uncapBasic s \<alpha>) (uncapGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof (intro subrelI)
  have "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
    using assms unfolding guar\<^sub>\<alpha>_rel by simp
  hence subset: "uncapGuar (Id_on (vc \<alpha>)) O uncapGuar (beh \<alpha>) \<subseteq> uncapGuar G"
    using uncapGuar_relcomp uncapGuar_mono by blast
  fix m m'
  assume mm': "(m,m') \<in> Id_on (vc (uncapBasic s \<alpha>)) O beh (uncapBasic s \<alpha>)"
  hence "(m,m') \<in> uncapBeh s (beh \<alpha>)" by auto
  hence "(m,m') \<in> uncapGuar (beh \<alpha>)" by auto
  moreover have "(m,m) \<in> uncapGuar (Id_on (vc \<alpha>))" using mm' by auto
  ultimately have 
    "(m,m') \<in> uncapGuar (Id_on (vc \<alpha>)) O uncapGuar (beh \<alpha>)" by fast
  thus "(m,m') \<in> uncapGuar G" using subset by fast
qed

lemma guar_capB_to_guar_uncapG:
  "guar\<^sub>\<alpha> (capBasic \<beta>) G \<Longrightarrow> guar\<^sub>\<alpha> \<beta> (uncapGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof (intro subrelI)
  assume "Id_on (vc (capBasic \<beta>)) O beh (capBasic \<beta>) \<subseteq> G" (is "?V O ?B \<subseteq> G")
  hence subset: "uncapGuar ?V O uncapGuar ?B \<subseteq> uncapGuar G"
    using uncapGuar_relcomp uncapGuar_mono by blast
  fix m m'
  assume "(m,m') \<in> Id_on (vc \<beta>) O beh \<beta>"
  hence mm': "(m,m) \<in> Id_on (vc \<beta>)" "(m,m') \<in> beh \<beta>" by auto
  have "vc \<beta> \<subseteq> {push m s |m s. m \<in> capPred (vc \<beta>)}"
    by clarsimp (metis popl_push push_intro)    
  hence "Id_on (vc \<beta>) \<subseteq> uncapGuar (Id_on (vc (capBasic \<beta>)))"
    by force
  moreover have "uncapGuar (beh (capBasic \<beta>)) = beh \<beta>"
    using uncap_capGuar by fastforce
  ultimately show "(m,m') \<in> uncapGuar G"
    using mm' subset by fast
qed


lemma cap_wp_capBasic:
  "capPred (wp\<^sub>\<alpha> (uncapBasic s \<alpha>) (uncapPred s' Q)) = wp\<^sub>\<alpha> \<alpha> Q"
proof -
  have
    "capPred {m. \<forall>m'. (m, m') \<in> beh (uncapBasic s \<alpha>) \<longrightarrow> m' \<in> uncapPred s' Q}
      = {m. \<forall>m'. (m, m') \<in> beh \<alpha> \<longrightarrow> m' \<in> Q}"
    by auto (metis (full_types) popr_push push_intro)+
  moreover have "capPred (vc (uncapBasic s \<alpha>)) = vc \<alpha>" by force
  moreover have
    "capPred (Domain (beh (uncapBasic s \<alpha>))) = Domain (beh \<alpha>)" by force
  ultimately show ?thesis by (simp only: wp_rel_partial capPred_inter)
qed

end