theory Atomics
  imports Syntax
begin

chapter \<open>Atomic Actions\<close>

text \<open>
Describe concepts the logic must know about atomic instructions. 
\<close>

section \<open>Helper Definitions\<close>

type_synonym ('b) pred = "('b) set"
type_synonym ('b) rpred = "('b) rel"

text \<open>Stability of a predicate across an environment step\<close>
definition stable :: "('b) rpred \<Rightarrow> ('b) pred \<Rightarrow> bool"
  where "stable R P \<equiv> \<forall>m m'. m \<in> P \<longrightarrow> (m,m') \<in> R \<longrightarrow> m' \<in> P"

text \<open>Weakest precondition for a precondition and postrelation\<close>
definition wp 
  where "wp pre post Q \<equiv> pre \<inter> {m. (\<forall>m'. (m,m') \<in> post \<longrightarrow> m' \<in> Q)}"

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
  "stable R P \<Longrightarrow> P \<subseteq> wp UNIV (R\<^sup>*) P"
  unfolding wp_def using stable_transitive by fast

lemma [intro]:
  "stable R {}"
  by (auto simp: stable_def)

section \<open>Atomic Properties\<close>

text \<open>Weakest precondition of a basic instruction, based on the locale's 
      verification conditions and behaviours.\<close>
abbreviation wp\<^sub>\<alpha> :: "('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp\<^sub>\<alpha> \<alpha> Q \<equiv> wp (vc \<alpha>) (beh \<alpha>) Q"

text \<open>Weakest precondition of a program, only covering basic instructions, environment steps and 
      sequential composition as these are sufficient for the logic's checks.\<close>
fun wp\<^sub>c :: "('a,'b) com \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where 
    "wp\<^sub>c (Basic \<alpha>) Q = wp\<^sub>\<alpha> \<alpha> Q" |
    "wp\<^sub>c (Rel r) Q = wp UNIV r Q" |
    "wp\<^sub>c (c\<^sub>1 ; c\<^sub>2) Q = wp\<^sub>c c\<^sub>1 (wp\<^sub>c c\<^sub>2 Q)" |
    "wp\<^sub>c _ Q = undefined"

text \<open>Refinement relation between two programs, in terms of their weakest precondition calculation.\<close>
definition refine :: "('a,'b) com \<Rightarrow> ('a,'b) com \<Rightarrow> bool" (infix "\<sqsubseteq>" 60)
  where "c \<sqsubseteq> c' \<equiv> \<forall>Q. wp\<^sub>c c Q \<subseteq> wp\<^sub>c c' Q"

text \<open>Merge the verification condition and behaviour to define evaluation\<close>
definition eval :: "('a,'b) basic \<Rightarrow> 'b rel"
  where "eval \<alpha> \<equiv> {(m,m'). m \<in> vc \<alpha> \<longrightarrow> (m,m') \<in> beh \<alpha>}"

text \<open>Specification check, ensuring an instruction conforms to a relation\<close>
abbreviation guar :: "('a,'b) basic \<Rightarrow> 'b rpred \<Rightarrow> bool"
  where "guar \<alpha> G \<equiv> {(m,m'). m \<in> vc \<alpha> \<and> (m,m') \<in> beh \<alpha>} \<subseteq> G\<^sup>="

section \<open>Atomic Rule\<close>

text \<open>Rule for an atomic operation\<close>
definition atomic_rule :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> ('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>A _ {_} _" [40,0,0,0,40] 40)
  where "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<equiv> P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q \<and> guar \<alpha> G \<and> stable R P \<and> stable R Q"

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
  using assms unfolding atomic_rule_def by blast

text \<open>Atomic judgements over the same instruction can be combined\<close>
lemma actomic_conjI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P\<^sub>1 {\<alpha>} Q\<^sub>1" "R,G  \<turnstile>\<^sub>A P\<^sub>2 {\<alpha>} Q\<^sub>2"
  shows "R,G \<turnstile>\<^sub>A P\<^sub>1 \<inter> P\<^sub>2 {\<alpha>} Q\<^sub>1 \<inter> Q\<^sub>2"
  using assms unfolding atomic_rule_def wp_def stable_def by fast

text \<open>Add an invariant across an atomic judgement\<close>
lemma atomic_invI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  assumes "stable R\<^sub>2 I" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>A P \<inter> I {\<alpha>} Q \<inter> I"
  unfolding atomic_rule_def
proof (safe, goal_cases)
  case (1 m)
  hence "{(m,m'). m \<in> P \<inter> vc \<alpha> \<and> (m,m') \<in> beh \<alpha>} \<subseteq> R\<^sub>2\<^sup>=" "m \<in> vc \<alpha>"
    using assms(1,3) by (auto simp: wp_def atomic_rule_def)
  hence "m \<in> wp\<^sub>\<alpha> \<alpha> I" using assms(2) 1 by (auto simp: wp_def stable_def)
  moreover have "m \<in> wp\<^sub>\<alpha> \<alpha> Q" using 1 assms(1) by (auto simp: atomic_rule_def wp_def)
  ultimately show ?case by (auto simp: wp_def)
qed (insert assms, auto simp: atomic_rule_def wp_def)

lemma atomic_falseI [intro]:
  assumes "guar \<beta> G"
  shows "R,G \<turnstile>\<^sub>A {} {\<beta>} {}"
  using assms unfolding atomic_rule_def by auto

section \<open>State Expansion\<close>

definition expand\<^sub>P
  where "expand\<^sub>P m P \<equiv> \<Union> (m ` P)"

definition expand\<^sub>G
  where "expand\<^sub>G m r G \<equiv> {(c,c'). \<exists>(b,b')\<in> G. c \<in> m b \<and> c' \<in> m b' \<and> r c c'}"

definition expand\<^sub>R
  where "expand\<^sub>R m R \<equiv> {(c,c'). \<exists>(b,b')\<in> R. c \<in> m b \<and> c' \<in> m b'}"

definition valid_expand
  where "valid_expand m r \<equiv> 
          (\<forall>b b' c. c \<in> m b' \<longrightarrow> c \<in> m b \<longrightarrow> b = b') \<and> 
          (\<forall>a b c. r a b \<longrightarrow> a \<in> m c \<longrightarrow> b \<in> m c \<longrightarrow> a = b)"

lemma expand_stable:
  assumes "stable R P" "valid_expand m r"
  shows "stable (expand\<^sub>R m R) (expand\<^sub>P m P)"
  using assms unfolding stable_def valid_expand_def expand\<^sub>P_def expand\<^sub>R_def
  by fastforce

lemma expand_wp\<^sub>\<alpha>:
  assumes "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "valid_expand m r"
  assumes \<alpha>: "vc \<alpha>' = expand\<^sub>P m (vc \<alpha>)" "beh \<alpha>' = expand\<^sub>G m r (beh \<alpha>)"
  shows "expand\<^sub>P m P \<subseteq> wp\<^sub>\<alpha> \<alpha>' (expand\<^sub>P m Q)"
  using assms(1,2) unfolding wp_def valid_expand_def expand\<^sub>P_def expand\<^sub>G_def \<alpha>
  by fastforce

lemma expand_guar:
  assumes "guar \<alpha> G" "valid_expand m r"
  assumes \<alpha>: "vc \<alpha>' = expand\<^sub>P m (vc \<alpha>)" "beh \<alpha>' = expand\<^sub>G m r (beh \<alpha>)"
  shows "guar \<alpha>' (expand\<^sub>G m r G)"
  using assms(1,2,3) unfolding valid_expand_def expand\<^sub>G_def \<alpha> expand\<^sub>P_def
  by blast

text \<open>Expand the state of an atomic judgement\<close>
lemma atomic_expandI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha> :: ('b,'a) basic} Q"
  assumes "valid_expand m r"
  assumes \<alpha>: "vc \<alpha>' = expand\<^sub>P m (vc \<alpha>)" "beh \<alpha>' = expand\<^sub>G m r (beh \<alpha>)" 
  shows "expand\<^sub>R m R,expand\<^sub>G m r G \<turnstile>\<^sub>A expand\<^sub>P m P {\<alpha>' :: ('b,'c) basic} expand\<^sub>P m Q"
  unfolding atomic_rule_def
proof (safe)
  show "stable (expand\<^sub>R m R) (expand\<^sub>P m P)" 
    using assms(1,2) expand_stable unfolding atomic_rule_def by blast
next
  show "stable (expand\<^sub>R m R) (expand\<^sub>P m Q)" 
    using assms(1,2) expand_stable unfolding atomic_rule_def by blast
next
  fix x assume "x \<in> expand\<^sub>P m P"
  thus "x \<in> wp\<^sub>\<alpha> \<alpha>' (expand\<^sub>P m Q)"
    using assms(1,2) \<alpha> expand_wp\<^sub>\<alpha> unfolding atomic_rule_def by blast
next
  fix x x' assume b: "(x, x') \<notin> expand\<^sub>G m r G" "x \<in> vc \<alpha>'" "(x, x') \<in> beh \<alpha>'"
  have "guar \<alpha>' (expand\<^sub>G m r G)"
    using assms(1,2) \<alpha> expand_guar unfolding atomic_rule_def by blast
  thus "x = x'" using b by auto
qed

end