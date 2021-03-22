theory Local_Rules
  imports Atomics
begin

chapter \<open>Local Rules\<close>

text \<open>Define the rely/guarantee rules for a local program.\<close>

locale local_rules = atomic_rule

context local_rules
begin

section \<open>Base Rules\<close>

text \<open>Rules of the logic over a thread, similar to standard Hoare-logic\<close>
inductive lrules :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> ('a,'b) com \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>l _ {_} _" [20,0,0,0,20] 20)
where
  nil[intro]:    "stable R P \<Longrightarrow> R,G \<turnstile>\<^sub>l P { Nil } P" |
  seq[intro]:    "R,G \<turnstile>\<^sub>l P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>1 ; c\<^sub>2 } M" |
  choice[intro]: "R,G \<turnstile>\<^sub>l P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>1 \<sqinter> c\<^sub>2 } Q" |
  loop[intro]:   "stable R P \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c } P \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c* } P" |
  basic[intro]:  "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { Basic \<alpha> } Q" |
  conseq[intro]: "R,G \<turnstile>\<^sub>l P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> R',G' \<turnstile>\<^sub>l P' { c } Q'"

section \<open>Derived Properties\<close>

text \<open>
Various elimination rules based on a judgement over a particular program structure.
These mostly deal with complexities introduced by support conseq.
\<close>

lemma nilE [elim!]:
  assumes "R,G \<turnstile>\<^sub>l P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms by (induct R G P "Nil :: ('a,'b) com" Q) blast+

lemma basicE [elim!]:
  assumes "R,G \<turnstile>\<^sub>l P {Basic \<beta>} Q"
  obtains P' Q' where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>} Q'" "Q' \<subseteq> Q"
  using assms 
proof (induct R G P "Basic \<beta> :: ('a,'b) com" Q)
  case (basic R G P Q)
  then show ?case by auto
next
  case (conseq R G P Q P' R' G' Q')
  then show ?case using order.trans atomic_conseqI by metis
qed

lemma seqE [elim]:
  assumes "R,G \<turnstile>\<^sub>l P {c\<^sub>1 ; c\<^sub>2} Q"
  obtains M  where "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M" "R,G \<turnstile>\<^sub>l M {c\<^sub>2} Q"
  using assms 
  by (induct R G P "c\<^sub>1 ; c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+

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

text \<open>No local judgement can be established over parallel composition or env steps\<close>
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

lemma [intro]:
  "stable R {}"
  by (auto simp: stable_def)

lemma falseI:
  assumes "\<forall>\<beta> \<in> basics c. guar \<beta> G" "local c"
  shows "R,G \<turnstile>\<^sub>l {} {c} {}"
  using assms
proof (induct c)
  case (Basic x)
  then show ?case using atomic_rule_def by force
qed auto

end

end