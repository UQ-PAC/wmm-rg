theory Atomics
  imports Syntax
begin

chapter \<open>Atomic Actions\<close>

text \<open>
Describe concepts the logic must know about atomic instructions. 
\<close>

section \<open>Helper Definitions\<close>

type_synonym 'b pred = "'b set"
type_synonym 'b rpred = "'b rel"

text \<open>Stability of a predicate across an environment step\<close>
definition stable :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  where "stable R P \<equiv> \<forall>m m'. m \<in> P \<longrightarrow> (m,m') \<in> R \<longrightarrow> m' \<in> P"

text \<open>Weakest precondition for a precondition and postrelation\<close>
definition wp 
  where "wp pre post Q \<equiv> pre \<inter> {m. (\<forall>m'. (m,m') \<in> post \<longrightarrow> m' \<in> Q)}"

text \<open>Weakest precondition of the transitive closure of an arbitrary state relation\<close>
abbreviation wp\<^sub>t :: "'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp\<^sub>t R P \<equiv> wp (UNIV) (R\<^sup>*) P"

subsection \<open>Helper Lemmas\<close>

lemma stable_conseqI [intro]:
  assumes "stable R' P" "R \<subseteq> R'" 
  shows "stable R P"
  using assms rtrancl_mono unfolding stable_def by blast

lemma stable_conjI [intro]:
  assumes "stable R P" "stable R' P'"
  shows "stable (R \<inter> R') (P \<inter> P')"
  using assms by (auto simp: stable_def)

lemma stable_transitive:
  assumes "(m,m') \<in> R\<^sup>*" "m \<in> P" "stable R P"
  shows "m' \<in> P"
  using assms by (induct rule: rtrancl.induct) (auto simp: stable_def)

lemma stable_wp\<^sub>tI:
  "stable R P \<Longrightarrow> P \<subseteq> wp\<^sub>t R P"
  unfolding wp_def using stable_transitive by fast

section \<open>Atomic Properties\<close>

locale atomics =
  fixes behv :: "'a \<Rightarrow> 'b rel" 
  and vc :: "'a \<Rightarrow> 'b set"

context atomics
begin

text \<open>Weakest precondition of a basic instruction, based on the locale's 
      verification conditions and behaviours.\<close>
abbreviation wp\<^sub>\<alpha> :: "'a \<Rightarrow> 'b set \<Rightarrow> 'b set"
  where "wp\<^sub>\<alpha> \<alpha> Q \<equiv> wp (vc \<alpha>) (behv \<alpha>) Q"

text \<open>Weakest precondition of a program, only covering basic instructions, environment steps and 
      sequential composition as these are sufficient for the logic's checks.\<close>
fun wp\<^sub>l
  where 
    "wp\<^sub>l (Basic \<alpha>) Q = wp\<^sub>\<alpha> \<alpha> Q" |
    "wp\<^sub>l (Env r) Q = wp\<^sub>t r Q" |
    "wp\<^sub>l (Seq c\<^sub>1 c\<^sub>2) Q = wp\<^sub>l c\<^sub>1 (wp\<^sub>l c\<^sub>2 Q)" |
    "wp\<^sub>l _ Q = undefined"

text \<open>Refinement relation between two programs, in terms of their weakest precondition calculation.\<close>
definition refine (infix "\<sqsubseteq>" 60)
  where "c \<sqsubseteq> c' \<equiv> \<forall>Q. wp\<^sub>l c Q \<subseteq> wp\<^sub>l c' Q"

text \<open>Merge the verification condition and behaviour to define evaluation\<close>
definition eval :: "'a \<Rightarrow> 'b rpred"
  where "eval \<alpha> \<equiv> {(m,m'). m \<in> vc \<alpha> \<longrightarrow> (m,m') \<in> behv \<alpha>}"

text \<open>Specification check, ensuring an instruction conforms to a relation\<close>
abbreviation guar :: "'a \<Rightarrow> 'b rpred \<Rightarrow> bool"
  where "guar \<alpha> G \<equiv> behv \<alpha> \<subseteq> G"

end

section \<open>Atomic Rule\<close>

locale atomic_rules = atomics

context atomic_rules
begin

text \<open>Rule for an atomic operation\<close>
definition atomic_rule :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'a \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>A _ {_} _" [40,0,0,0,40] 40)
  where "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<equiv> P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q \<and> guar \<alpha> G \<and> stable R P \<and> stable R Q"

subsection \<open>Derived Properties\<close>

text \<open>Re-establish an atomic judgement over a stronger stable precondition\<close>
lemma atomic_pre:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "P' \<subseteq> P" "stable R P'"
  shows "R,G \<turnstile>\<^sub>A P' {\<alpha>} Q"
  using assms unfolding atomic_rule_def
  by fast

text \<open>Strengthen the rely and weaken the guarantee for an atomic judgement\<close>
lemma atomic_conseqI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "R' \<subseteq> R" "G \<subseteq> G'"
  shows "R',G' \<turnstile>\<^sub>A P {\<alpha>} Q"
  using assms unfolding atomic_rule_def
  by blast

text \<open>Atomic judgements over the same instruction can be combined\<close>
lemma actomic_conjI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P\<^sub>1 {\<alpha>} Q\<^sub>1" "R,G  \<turnstile>\<^sub>A P\<^sub>2 {\<alpha>} Q\<^sub>2"
  shows "R,G \<turnstile>\<^sub>A P\<^sub>1 \<inter> P\<^sub>2 {\<alpha>} Q\<^sub>1 \<inter> Q\<^sub>2"
  using assms unfolding atomic_rule_def wp_def stable_def wp\<^sub>l.simps
  by (intro conjI) blast+

text \<open>Add an invariant across an atomic judgement\<close>
lemma atomic_frameI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  assumes "stable R\<^sub>2 M" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>A P \<inter> M {\<alpha>} Q \<inter> M"
  unfolding atomic_rule_def
proof (safe, goal_cases)
  case (1 x)
  hence "{(m,m'). m \<in> P} \<inter> behv \<alpha> \<subseteq> R\<^sub>2" "x \<in> vc \<alpha>"
    using assms(1,3) by (auto simp: wp_def atomic_rule_def)
  hence "x \<in> wp\<^sub>l (Basic \<alpha>) M" using assms(2) 1 by (auto simp: wp_def stable_def)
  moreover have "x \<in> wp\<^sub>l (Basic \<alpha>) Q" using 1 assms(1) by (auto simp: atomic_rule_def wp_def)
  ultimately show ?case by (auto simp: wp_def)
qed (insert assms, auto simp: atomic_rule_def wp_def)

end

end