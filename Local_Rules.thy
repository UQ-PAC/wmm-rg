theory Local_Rules
  imports Atomics
begin

chapter \<open>Local Rules\<close>

text \<open>Define the rely/guarantee rules for a local program.\<close>

section \<open>Base Rules\<close>

text \<open>Rules of the logic over a thread, similar to standard Hoare-logic\<close>
inductive lrules :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> ('a,'b) com \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>l _ {_} _" [20,0,0,0,20] 20)
where
  nil[intro]:    "stable R P \<Longrightarrow> R,G \<turnstile>\<^sub>l P { Nil } P" |
  seq[intro]:    "R,G \<turnstile>\<^sub>l P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>1 ; c\<^sub>2 } M" |
  ord[intro]:    "R,G \<turnstile>\<^sub>l P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>1 \<cdot> c\<^sub>2 } M" |
  choice[intro]: "R,G \<turnstile>\<^sub>l P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { c\<^sub>1 \<sqinter> c\<^sub>2 } Q" |
  bigchoice[intro]: "\<forall>s \<in> S. R,G \<turnstile>\<^sub>l P { seq2com s } Q \<Longrightarrow> R,G \<turnstile>\<^sub>l P { \<Sqinter> S } Q" |
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
  using assms by (induct R G P "Nil :: ('b,'a) com" Q) blast+

lemma basicE [elim!]:
  assumes "R,G \<turnstile>\<^sub>l P {Basic \<beta>} Q"
  obtains P' Q' where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>} Q'" "Q' \<subseteq> Q"
  using assms 
proof (induct R G P "Basic \<beta> :: ('b,'a) com" Q)
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

lemma ordE [elim]:
  assumes "R,G \<turnstile>\<^sub>l P {c\<^sub>1 \<cdot> c\<^sub>2} Q"
  obtains M  where "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M" "R,G \<turnstile>\<^sub>l M {c\<^sub>2} Q"
  using assms 
  by (induct R G P "c\<^sub>1 \<cdot> c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+

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
  then show ?case using lrules.conseq stable_conseqI by (metis subset_iff)
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

lemma relE [elim!]:
  assumes "R,G \<turnstile>\<^sub>l P { Rel r } Q"
  obtains "False"
  using local_only assms by force

text \<open>Weaken the precondition of a judgement to a stable state\<close>
lemma stable_pre:
  assumes "R,G \<turnstile>\<^sub>l P {c} Q"
  shows "\<exists>P'. P \<subseteq> P' \<and> stable R P' \<and> (R,G \<turnstile>\<^sub>l P' {c} Q)"
  using assms 
proof (induct)
  case (basic R G P \<alpha> Q)
  then show ?case using atomic_rule_def by fast
next
  case (choice R G P c\<^sub>1 Q c\<^sub>2)
  then obtain P\<^sub>1 where 1: "P \<subseteq> P\<^sub>1" "stable R P\<^sub>1" "R,G \<turnstile>\<^sub>l P\<^sub>1 {c\<^sub>1} Q" by auto
  then obtain P\<^sub>2 where 2: "P \<subseteq> P\<^sub>2" "stable R P\<^sub>2" "R,G \<turnstile>\<^sub>l P\<^sub>2 {c\<^sub>2} Q" using choice by auto
  have "stable R (P\<^sub>1 \<inter> P\<^sub>2)" using 1 2 by auto
  then show ?case using 1 2 by blast
next
  case (bigchoice S R G P Q)
  hence "\<exists>P\<^sub>s. \<forall>s\<in>S. P \<subseteq> P\<^sub>s s \<and> stable R (P\<^sub>s s) \<and> (R,G \<turnstile>\<^sub>l P\<^sub>s s {seq2com s} Q)"
    by metis
  then obtain P\<^sub>s where s: "\<forall>s\<in>S. P \<subseteq> P\<^sub>s s \<and> stable R (P\<^sub>s s) \<and> (R,G \<turnstile>\<^sub>l P\<^sub>s s {seq2com s} Q)"
    by blast
  hence "stable R (\<Inter>s\<in>S. P\<^sub>s s)" by (auto simp: stable_def)
  moreover have "P \<subseteq> (\<Inter>s\<in>S. P\<^sub>s s)" using s by auto
  ultimately show ?case using s bigchoice.hyps(1) by blast
next
  case (conseq R G P c Q P' R' G' Q')
  then show ?case by (meson lrules.conseq order_refl stable_conseqI subset_trans)
qed blast+

lemma stable_preE:
  assumes "R,G \<turnstile>\<^sub>l P {c} Q"
  obtains P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile>\<^sub>l P' {c} Q"
  using assms stable_pre by metis

lemma false_seqI:
  assumes "\<forall>\<beta> \<in> set s. guar \<beta> G"
  shows "R,G \<turnstile>\<^sub>l {} {seq2com s} {}"
  using assms by (induct s) auto

lemma falseI:
  assumes "\<forall>\<beta> \<in> basics c. guar \<beta> G" "local c"
  shows "R,G \<turnstile>\<^sub>l {} {c} {}"
  using assms
proof (induct c)
  case (BigChoice S)
  then show ?case by (intro bigchoice ballI false_seqI) auto
qed auto

end