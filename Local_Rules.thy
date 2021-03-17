theory Local_Rules
  imports Syntax
begin

chapter \<open>Local Rules\<close>

text \<open>Define the rely/guarantee rules for a local program.\<close>

section \<open>Helper Definitions\<close>

text \<open>Stability of a predicate across an environment step\<close>
definition stable :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  where "stable R P \<equiv> \<forall>m m'. m \<in> P \<longrightarrow> (m,m') \<in> R \<longrightarrow> m' \<in> P"

text \<open>Weakest precondition for an arbitrary state relation\<close>
definition wp :: "'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp \<alpha> P \<equiv> {m. \<forall>m'. (m,m') \<in> \<alpha> \<longrightarrow> m' \<in> P}"

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

locale local_rules =
  fixes eval :: "'a \<Rightarrow> 'b rel" 

context local_rules
begin

section \<open>Atomic Rule\<close>

text \<open>Weakest precondition for an instruction\<close>
abbreviation wp\<^sub>\<alpha> :: "'a \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp\<^sub>\<alpha> \<alpha> P \<equiv> wp (eval \<alpha>) P"

text \<open>Specification Check, ensuring an instruction conforms to a relation\<close>
abbreviation guar :: "'a \<Rightarrow> 'b rpred \<Rightarrow> bool"
  where "guar \<alpha> G \<equiv> eval \<alpha> \<subseteq> G"

text \<open>Rule for an atomic operation\<close>
definition atomic_rule :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'a \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>A _ {_} _" [40,0,0,0,40] 40)
  where "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<equiv> P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q \<and> guar \<alpha> G \<and> stable R P \<and> stable R Q"

subsection \<open>Properties\<close>

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
  using assms unfolding atomic_rule_def  
  by (auto simp: wp_def stable_def)

text \<open>Add an invariant across an atomic judgement\<close>
lemma atomic_frameI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  assumes "stable R\<^sub>2 M" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>A P \<inter> M {\<alpha>} Q \<inter> M"
  unfolding atomic_rule_def
proof (safe, goal_cases)
  case (1 x)
  hence "{(m,m'). m \<in> P} \<inter> eval \<alpha> \<subseteq> R\<^sub>2" 
    using assms(1,3) unfolding atomic_rule_def by fast
  hence "x \<in> wp\<^sub>\<alpha> \<alpha> M" using assms(2) 1 unfolding stable_def wp_def by blast
  moreover have "x \<in> wp\<^sub>\<alpha> \<alpha> Q" using 1 assms(1) by (auto simp: atomic_rule_def wp_def)
  ultimately show ?case by (auto simp: wp_def)
qed (insert assms, auto simp: atomic_rule_def wp_def)

section \<open>Local Rules\<close>

text \<open>Rules of the logic over a thread, similar to standard Hoare-logic\<close>
inductive lrules :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'a com \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>l _ {_} _" [20,0,0,0,20] 20)
where
  nil[intro]:    "stable R P \<Longrightarrow> R,G \<turnstile>\<^sub>l P { Nil } P" |
  seq[intro]:    "R,G \<turnstile>\<^sub>l P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>1 ;; c\<^sub>2 } M" |
  choice[intro]: "R,G \<turnstile>\<^sub>l P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>1 \<sqinter> c\<^sub>2 } Q" |
  loop[intro]:   "stable R P \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c } P \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c* } P" |
  basic[intro]:  "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { Basic \<alpha> } Q" |
  conseq[intro]: "R,G \<turnstile>\<^sub>l P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> R',G' \<turnstile>\<^sub>l P' { c } Q'"

subsection \<open>Properties\<close>

text \<open>
Various elimination rules based on a judgement over a particular program structure.
These mostly deal with complexities introduced by support conseq.
\<close>

lemma nilE [elim!]:
  assumes "R,G \<turnstile>\<^sub>l P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms by (induct R G P "Nil :: 'a com" Q) blast+

lemma basicE [elim!]:
  assumes "R,G \<turnstile>\<^sub>l P {Basic \<beta>} Q"
  obtains P' Q' where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>} Q'" "Q' \<subseteq> Q"
  using assms 
proof (induct R G P "Basic \<beta>" Q)
  case (basic R G P Q)
  then show ?case by auto
next
  case (conseq R G P Q P' R' G' Q')
  then show ?case using order.trans atomic_conseqI by metis
qed

lemma seqE [elim]:
  assumes "R,G \<turnstile>\<^sub>l P {c\<^sub>1 ;; c\<^sub>2} Q"
  obtains M  where "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M" "R,G \<turnstile>\<^sub>l M {c\<^sub>2} Q"
  using assms 
  by (induct R G P "c\<^sub>1 ;; c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+

lemma choiceE [elim]:
  assumes "R,G \<turnstile>\<^sub>l P {c\<^sub>1 \<sqinter> c\<^sub>2} Q"
  obtains "R,G \<turnstile>\<^sub>l P {c\<^sub>1} Q" "R,G \<turnstile>\<^sub>l P {c\<^sub>2} Q"
  using assms by (induct R G P "c\<^sub>1 \<sqinter> c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) auto

lemma loopE [elim]:
  assumes "R,G \<turnstile>\<^sub>l P { c* } Q"
  obtains I where "P \<subseteq> I" "R,G \<turnstile>\<^sub>l I { c } I" "I \<subseteq> Q" "stable R I"
  using assms 
proof (induct R G P "c*" Q arbitrary: c)
  case (loop R G P c)
  then show ?case by blast
next
  case (conseq R G P Q P' R' G' Q')
  then show ?case using lrules.conseq stable_conseqI by (metis subset_eq)
qed

text \<open>No local judgement can be established over parallel composition\<close>
lemma local_only:
  assumes "R,G \<turnstile>\<^sub>l P { c } Q"
  shows "local c"
  using assms by induct auto

lemma parE [elim!]:
  assumes "R,G \<turnstile>\<^sub>l P { c\<^sub>1 || c\<^sub>2 } Q"
  obtains "False"
  using local_only assms by force

text \<open>Weaken the precondition of a judgement to a stable state\<close>
lemma stable_preE:
  assumes "R,G \<turnstile>\<^sub>l P {c} Q"
  obtains P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile>\<^sub>l P' {c} Q"
  using assms 
proof (induct)
  case (basic R G P \<alpha> Q)
  then show ?case using atomic_rule_def by fast
next
  case (choice R G P c\<^sub>1 Q c\<^sub>2)
  show ?case
  proof (rule choice(2), rule choice(4),  goal_cases)
    case (1 P' P'')
    have a: "stable R (P' \<inter> P'')" using 1 by auto
    have b: "P \<subseteq> P' \<inter> P''" using 1 by auto
    then show ?case using 1 choice(5)[OF b a] by blast
  qed
qed blast+

end

end