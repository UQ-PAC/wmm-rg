theory Atomics
  imports Syntax
begin

chapter \<open>Atomic Actions\<close>

text \<open>
Describe concepts the logic must know about atomic instructions. 
\<close>

section \<open>Helper Definitions\<close>

datatype 'c tree = Leaf 'c | Branch "'c tree" "'c tree"

type_synonym ('b,'c) gpred = "('b \<times> 'c tree) set"
type_synonym ('b,'c) pred = "('b \<times> 'c) set"
type_synonym ('b,'c) rpred = "'b rel"

definition leaf :: "('b \<times> 'c) set \<Rightarrow> ('b \<times> 'c tree) set"
  where "leaf e \<equiv> {(g,Leaf l) | g l. (g,l) \<in> e}"

definition left :: "('b \<times> 'c tree) set \<Rightarrow> ('b \<times> 'c tree) set"
  where "left e \<equiv> {(g,Branch l r) | g l r. (g,l) \<in> e}"

definition right :: "('b \<times> 'c tree) set \<Rightarrow> ('b \<times> 'c tree) set"
  where "right e \<equiv> {(g,Branch l r) | g l r. (g,r) \<in> e}"

definition leaf\<^sub>r :: "('b \<times> 'c) rel \<Rightarrow> ('b \<times> 'c tree) rel"
  where "leaf\<^sub>r e \<equiv> {((g,Leaf l),(g', Leaf l')) | g g' l l'. ((g,l),(g',l')) \<in> e}"

definition left\<^sub>r :: "('b \<times> 'c tree) rel \<Rightarrow> ('b \<times> 'c tree) rel"
  where "left\<^sub>r e \<equiv> {((g,Branch l r),(g',Branch l' r)) | g g' l l' r. ((g,l),(g',l')) \<in> e}"

definition right\<^sub>r :: "('b \<times> 'c tree) rel \<Rightarrow> ('b \<times> 'c tree) rel"
  where "right\<^sub>r e \<equiv> {((g,Branch l r),(g', Branch l r')) | g g' l r r'. ((g,r),(g',r')) \<in> e}"

definition any :: "('b) set \<Rightarrow> ('b \<times> 'c tree) set"
  where "any e \<equiv> {(g,t) | t g. (g) \<in> e}"

text \<open>Stability of a predicate across an environment step\<close>
definition stable :: "('b,'c) rpred \<Rightarrow> ('b,'c) pred \<Rightarrow> bool"
  where "stable R P \<equiv> \<forall>g l g'. (g,l) \<in> P \<longrightarrow> (g,g') \<in> R \<longrightarrow> (g',l) \<in> P"

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
  assumes "(g,g') \<in> R\<^sup>*" "(g,l) \<in> P" "stable R P"
  shows "(g',l) \<in> P"
  using assms by (induct rule: rtrancl.induct) (auto simp: stable_def)

lemma stable_wp\<^sub>tI:
  "stable R P \<Longrightarrow> P \<subseteq> wp UNIV (fullR (R\<^sup>*)) P"
  unfolding wp_def using stable_transitive by fast

lemma [intro]:
  "stable R {}"
  by (auto simp: stable_def)

section \<open>Atomic Properties\<close>

locale atomic =
  fixes vc :: "'a \<Rightarrow> ('b \<times> 'c) set"
  and beh :: "'a \<Rightarrow> ('b \<times> 'c) rel"

context atomic
begin

text \<open>Weakest precondition of a basic instruction, based on the locale's 
      verification conditions and behaviours.\<close>
abbreviation wp\<^sub>\<alpha> :: "'a \<Rightarrow> ('b,'c) pred \<Rightarrow> ('b,'c) pred"
  where "wp\<^sub>\<alpha> \<alpha> Q \<equiv> wp (vc \<alpha>) (beh \<alpha>) Q"

text \<open>Weakest precondition of a program, only covering basic instructions, environment steps and 
      sequential composition as these are sufficient for the logic's checks.\<close>
fun wp\<^sub>c :: "('a,'b,'c) com \<Rightarrow> ('b,'c) pred \<Rightarrow> ('b,'c) pred"
  where 
    "wp\<^sub>c (Basic \<alpha>) Q = wp\<^sub>\<alpha> \<alpha> Q" |
    "wp\<^sub>c (Rel r) Q = wp UNIV r Q" |
    "wp\<^sub>c (c\<^sub>1 ; c\<^sub>2) Q = wp\<^sub>c c\<^sub>1 (wp\<^sub>c c\<^sub>2 Q)" |
    "wp\<^sub>c _ Q = undefined"

text \<open>Refinement relation between two programs, in terms of their weakest precondition calculation.\<close>
definition refine :: "('a,'b,'c) com \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool" (infix "\<sqsubseteq>" 60)
  where "c \<sqsubseteq> c' \<equiv> \<forall>Q. wp\<^sub>c c Q \<subseteq> wp\<^sub>c c' Q"

text \<open>Merge the verification condition and behaviour to define evaluation\<close>
definition eval :: "'a \<Rightarrow> ('b \<times> 'c) rel"
  where "eval \<alpha> \<equiv> {(m,m'). m \<in> vc \<alpha> \<longrightarrow> (m,m') \<in> beh \<alpha>}"

text \<open>Specification check, ensuring an instruction conforms to a relation\<close>
abbreviation guar :: "'a \<Rightarrow> ('b,'c) rpred \<Rightarrow> bool"
  where "guar \<alpha> G \<equiv> {(g,g'). \<exists>l l'. (g,l) \<in> vc \<alpha> \<and> ((g,l),(g',l')) \<in> beh \<alpha>} \<subseteq> G\<^sup>="

end

section \<open>Atomic Rule\<close>

locale atomic_rule = atomic

context atomic_rule
begin

text \<open>Rule for an atomic operation\<close>
definition atomic_rule :: "('b,'c) rpred \<Rightarrow> ('b,'c) rpred \<Rightarrow> ('b,'c) pred \<Rightarrow> 'a \<Rightarrow> ('b,'c) pred \<Rightarrow> bool" 
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

(*
text \<open>Add an invariant across an atomic judgement\<close>
lemma atomic_frameI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  assumes "stable R\<^sub>2 M" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>A P \<inter> M {\<alpha>} Q \<inter> M"
  unfolding atomic_rule_def
proof (safe, goal_cases)
  case (1 g l)
  hence "{(g,g'). \<exists>l l'. (g,l) \<in> P \<inter> vc \<alpha> \<and> ((g,l),(g',l')) \<in> beh \<alpha>} \<subseteq> R\<^sub>2\<^sup>=" "(g,l) \<in> vc \<alpha>"
    using assms(1,3) by (auto simp: wp_def atomic_rule_def)
  hence "(g,l) \<in> wp\<^sub>\<alpha> \<alpha> M" using assms(2) 1 by (auto simp: wp_def stable_def)
  moreover have "(g,l) \<in> wp\<^sub>\<alpha> \<alpha> Q" using 1 assms(1) by (auto simp: atomic_rule_def wp_def)
  ultimately show ?case by (auto simp: wp_def)
qed (insert assms, auto simp: atomic_rule_def wp_def)
*)

end

end