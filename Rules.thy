theory Rules
  imports Interference
begin

chapter \<open>Rules\<close>

text \<open>Define the rely/guarantee rules for a concurrent program.\<close>

locale rules = interference

context rules
begin

section \<open>Global Rules\<close>

text \<open>Establish the rules of the logic, similar to standard Hoare-logic\<close>
inductive rules :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b set \<Rightarrow> ('a,'b) com \<Rightarrow> 'b set \<Rightarrow> bool" 
  ("_,_ \<turnstile> _ {_} _" [65,0,0,0,65] 65)
  where
  basic[intro]:  "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<Longrightarrow> R,G \<turnstile> P { Basic \<alpha> } Q" |
  nil[intro]:    "stable R P \<Longrightarrow> R,G \<turnstile> P { Nil } P" |
  seq[intro]:    "R,G \<turnstile> Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 ;; c\<^sub>2 } M" |
  ord[intro]:    "R,G \<turnstile> Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 \<cdot> c\<^sub>2 } M" |
  choice[intro]: "R,G \<turnstile> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 \<sqinter> c\<^sub>2 } Q" |
  seqset[intro]: "\<forall>s \<in> S. R,G \<turnstile> P { seq2com s } Q \<Longrightarrow> R,G \<turnstile> P { \<Sqinter> S } Q" |
  loop[intro]:   "stable R P \<Longrightarrow> R,G \<turnstile> P { c } P \<Longrightarrow> R,G \<turnstile> P { c* } P" |
  thread[intro]: "R,G \<turnstile> P { c } Q \<Longrightarrow> rif R G c \<Longrightarrow> R,G \<turnstile> P { Thread c } Q" |
  par[intro]:    "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                  R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (Q\<^sub>1 \<inter> Q\<^sub>2)" |
  conseq[intro]: "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                   R',G' \<turnstile> P' { c } Q'"  |
  inv[intro]:    "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' I \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> R \<inter> R',G \<turnstile> (P \<inter> I) {c} (Q \<inter> I)" (* |
  capture[intro]:
    "R,G \<turnstile> P {c} Q \<Longrightarrow> 
      {(m,m') |m m'. (merge m s, merge m' s) \<in> R},
      {(m,m') |m m'. (merge m s, merge m' s') \<in> G} 
      \<turnstile> {m |m. merge m s \<in> P} {Capture s c} {m |m. merge m s' \<in> Q}" *)
  | capall[intro]: "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R P \<Longrightarrow> R,G \<turnstile> P {CaptureAll c} P"

subsection \<open>Properties\<close>

lemma nilE [elim!]:
  assumes "R,G \<turnstile> P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms 
  by (induct R G P "Nil :: ('a,'b) com" Q) blast+

lemma basicE [elim!]:
  assumes "R,G \<turnstile> P {Basic \<beta>} Q"
  obtains P' Q' where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>} Q'" "Q' \<subseteq> Q"
  using assms 
proof (induct R G P "Basic \<beta> :: ('a,'b) com" Q arbitrary: \<beta>)
  case (basic R G P Q)
  then show ?case by auto
next
  case (conseq R G P Q P' R' G' Q')
  then show ?case using order.trans atomic_conseqI by metis
next
  case (inv R G P Q R' I)
  show ?case 
  proof (rule inv(2), goal_cases)
    case (1 P' Q')
    thus ?case using inv(3,4) inv(5)[of "P' \<inter> I" "Q' \<inter> I"] atomic_invI by blast
  qed
qed

lemma seqE [elim]:
  assumes "R,G \<turnstile> P {c\<^sub>1 ;; c\<^sub>2} Q"
  obtains M  where "R,G \<turnstile> P {c\<^sub>1} M" "R,G \<turnstile> M {c\<^sub>2} Q"
  using assms by (induct R G P "c\<^sub>1 ;; c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+ 

lemma ordE [elim]:
  assumes "R,G \<turnstile> P {c\<^sub>1 \<cdot> c\<^sub>2} Q"
  obtains M  where "R,G \<turnstile> P {c\<^sub>1} M" "R,G \<turnstile> M {c\<^sub>2} Q"
  using assms by (induct R G P "c\<^sub>1 \<cdot> c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+

text \<open>It is always possible to rephrase a judgement in terms of a stable precondition\<close>
lemma stable_preE:
  assumes "R,G \<turnstile> P {c} Q"
  shows "\<exists>P'. P \<subseteq> P' \<and> stable R P' \<and> R,G \<turnstile> P' {c} Q"
  using assms 
proof (induct ) 
  case (thread R G P c Q)
  then show ?case by (metis rules.thread)
next 
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  obtain P\<^sub>1' where 1: "P\<^sub>1 \<subseteq> P\<^sub>1'" "stable R\<^sub>1 P\<^sub>1'" "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1' {c\<^sub>1} Q\<^sub>1" using par(2) by blast
  obtain P\<^sub>2' where 2: "P\<^sub>2 \<subseteq> P\<^sub>2'" "stable R\<^sub>2 P\<^sub>2'" "R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2' {c\<^sub>2} Q\<^sub>2" using par(4) by blast
  hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1' \<inter> P\<^sub>2' {c\<^sub>1 || c\<^sub>2} Q\<^sub>1 \<inter> Q\<^sub>2" using 1 2 rules.par par(5,6) by simp
  thus ?case using 1 2 stable_conjI by blast
next
  case (basic R G P \<alpha> Q)
  then show ?case using atomic_rule_def by fast
next
  case (choice R G P c\<^sub>1 Q c\<^sub>2)
  obtain P\<^sub>1 where 1: "P \<subseteq> P\<^sub>1" "stable R P\<^sub>1" "R,G \<turnstile> P\<^sub>1 {c\<^sub>1} Q" using choice by auto
  obtain P\<^sub>2 where 2: "P \<subseteq> P\<^sub>2" "stable R P\<^sub>2" "R,G \<turnstile> P\<^sub>2 {c\<^sub>2} Q" using choice by auto
  have "stable R (P\<^sub>1 \<inter> P\<^sub>2)" using 1 2 by auto
  thus ?case using 1 2 by blast
next
  case (conseq R G P c Q P' R' G' Q')
  then show ?case by (meson order_refl rules.conseq stable_conseqI subset_trans)
next
  case (inv R G P c Q R' I)
  then obtain P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c} Q" by auto
  then show ?case using inv rules.inv by blast
next
  case (seqset S R G P Q)
  hence "\<exists>P\<^sub>s. \<forall>s\<in>S. P \<subseteq> P\<^sub>s s \<and> stable R (P\<^sub>s s) \<and> (R,G \<turnstile> P\<^sub>s s {seq2com s} Q)"
    by metis
  then obtain P\<^sub>s where s: "\<forall>s\<in>S. P \<subseteq> P\<^sub>s s \<and> stable R (P\<^sub>s s) \<and> (R,G \<turnstile> P\<^sub>s s {seq2com s} Q)"
    by blast
  hence "stable R (\<Inter>s\<in>S. P\<^sub>s s)" by (auto simp: stable_def)
  moreover have "P \<subseteq> (\<Inter>s\<in>S. P\<^sub>s s)" using s by auto
  ultimately show ?case using s seqset.hyps(1) by blast
qed blast+

lemma false_seqI [intro]:
  "\<forall>\<beta> \<in> set s. guar\<^sub>\<alpha> \<beta> G \<Longrightarrow> R,G \<turnstile> {} {seq2com s} {}"
  by (induct s) auto

(* why do we need these to satisfy the guarantee, and why do we need local c? *)
lemma falseI:
  "local c \<Longrightarrow> \<forall>\<beta> \<in> basics c. guar\<^sub>\<alpha> \<beta> G \<Longrightarrow> R,G \<turnstile> {} {c} {}"
proof (induct c)
  case (Basic x)
  thus ?case by (intro basic) (auto simp: atomic_rule_def guar_def wp_def)
next
  case (SeqChoice x)
  thus ?case by (intro ballI seqset false_seqI) auto
(* next         
  case (Capture x1 c)
  then show ?case sorry *)
qed auto

lemma seq_rot:
  "R,G \<turnstile> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile> Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 ;; c\<^sub>2 } M"
  by auto

end

end