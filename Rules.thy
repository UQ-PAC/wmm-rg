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
  inv[intro]:    "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' I \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> R \<inter> R',G \<turnstile> (P \<inter> I) {c} (Q \<inter> I)"
(*   | capture[intro]: "R,G \<turnstile> P {c} Q \<Longrightarrow> stable (capbeh k R) (capvc k P) \<Longrightarrow>
      capbeh k R,capbeh k G \<turnstile> capvc k P {Capture k c} capvc k Q" *)
  (* | capture[intro]: "R,G \<turnstile> P {c} Q \<Longrightarrow>
    thr\<^sub>R op R,thr\<^sub>G op G \<turnstile> thr\<^sub>P op l P { Capture op l l' c } thr\<^sub>P op l' Q" *)
  | capture[intro]: 
    "uncapRely R,uncapGuar G \<turnstile> uncapPred s P {c} uncapPred s' Q
     \<Longrightarrow> R,G \<turnstile> P {Capture s c} Q"
  (* | capall[intro]: "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R P \<Longrightarrow> R,G \<turnstile> P {CaptureAll c} P" *)

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

lemma captureE':
  assumes "R,G \<turnstile> P {Capture s c} Q"
  shows "\<exists>s'. uncapRely R,uncapGuar G \<turnstile> uncapPred s P {c} uncapPred s' Q"
using assms
proof (induct R G P "Capture s c" Q arbitrary: s c)
  case (conseq R G P Q P' R' G' Q')
  thus ?case by (meson pushpred_mono pushrelAll_eq pushrelSame_mono rules.conseq)
next
  case (capture R G s P c s' Q)
  thus ?case by (intro exI)
next
  case (inv R G P Q R' I)
  obtain s' where s': "pushrelSame R,pushrelAll G \<turnstile> pushpred s P {c} pushpred s' Q"
    using inv(2) by auto
  moreover have "pushrelAll G \<subseteq> pushrelAll R'"
    using inv by (intro pushrelAll_mono)
  moreover have
    "stable (pushrelAll R') (pushpredAll I)"
    using inv by (intro stable_pushrelAll)
  ultimately have 
    "pushrelSame R \<inter> pushrelAll R',pushrelAll G
      \<turnstile> pushpred s P \<inter> pushpredAll I {c} pushpred s' Q \<inter> pushpredAll I"
    by (intro rules.inv)
  hence 
    "pushrelSame R \<inter> pushrelAll R',pushrelAll G
      \<turnstile> pushpred s (P \<inter> I) {c} pushpred s' (Q \<inter> I)"
    by (simp add: pushpred_inter_pushpredAll)
  hence
    "pushrelSame (R \<inter> R'),pushrelAll G 
      \<turnstile> pushpred s (P \<inter> I) {c} pushpred s' (Q \<inter> I)"
    using pushrelSame_in_pushrelAll by auto 
  thus ?case by auto
qed

lemma captureE [elim]:
  assumes "R,G \<turnstile> P {Capture s c} Q"
  obtains s' where "uncapRely R,uncapGuar G \<turnstile> uncapPred s P {c} uncapPred s' Q"
by (rule exE[OF captureE'[OF assms]])


text \<open>In fact, we can rephrase a judgement with an explicit stabilisation.\<close>
lemma stable_preE':
  assumes "R,G \<turnstile> P {c} Q"
  shows "R,G \<turnstile> stabilise R P {c} Q"
using assms
proof (induct)
  case (basic R G P \<alpha> Q)
  thus ?case unfolding atomic_rule_def
    by (simp add: basic rules.basic stabilise_stable)
next
  case (nil R P G)
  thus ?case by (simp add: rules.nil stabilise_stable)
next
  case (loop R P G c)
  thus ?case by (simp add: rules.loop stabilise_stable)
next
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  hence "R\<^sub>1 \<inter> R\<^sub>2, G\<^sub>1 \<union> G\<^sub>2 \<turnstile> stabilise R\<^sub>1 P\<^sub>1 \<inter> stabilise R\<^sub>2 P\<^sub>2 {c\<^sub>1 || c\<^sub>2} Q\<^sub>1 \<inter> Q\<^sub>2" 
    by (intro rules.par)
  thus ?case using stabilise_inter_RP by (rule conseq; simp)
next
  case (conseq R G P c Q P' R' G' Q')
  thus ?case using stabilise_mono_RP[of R' R P' P] by blast
next
  case (inv R G P c Q R' I)
  hence "R \<inter> R',G \<turnstile> stabilise R P \<inter> I {c} Q \<inter> I" by (intro rules.inv)
  hence "R \<inter> R',G \<turnstile> stabilise R P \<inter> stabilise R' I {c} Q \<inter> I"
    using inv stabilise_stable[of R' I] by simp
  thus ?case using stabilise_inter_RP by (rule conseq; simp)
next
  case (capture R G s P c s' Q)
  thus ?case by (intro rules.capture, simp add: stabilise_pushrel)
qed auto

text \<open>It is always possible to rephrase a judgement in terms of a stable precondition\<close>
lemma stable_preE:
  assumes "R,G \<turnstile> P {c} Q"
  shows "\<exists>P'. P \<subseteq> P' \<and> stable R P' \<and> R,G \<turnstile> P' {c} Q"
using stable_preE'[OF assms] stable_stabilise stabilise_supset
by auto


lemma false_seqI [intro]:
  "\<forall>\<beta> \<in> set s. guar\<^sub>\<alpha> \<beta> G \<Longrightarrow> R,G \<turnstile> {} {seq2com s} {}"
  by (induct s) auto

lemma falseI:
  "local c \<Longrightarrow> \<forall>\<beta> \<in> basics c. guar\<^sub>\<alpha> \<beta> G \<Longrightarrow> R,G \<turnstile> {} {c} {}"
proof (induct c arbitrary: R G)
  case (Basic x)
  thus ?case by (intro basic) (auto simp: atomic_rule_def guar_def wp_def)
next
  case (SeqChoice x)
  thus ?case by (intro ballI seqset false_seqI) auto
next
  case (Seq c1 c2)
  hence "R,G \<turnstile> {} {c1} {}" "R,G \<turnstile> {} {c2} {}" by auto
  then show ?case by auto
next
  case (Ord c1 c2)
  hence "R,G \<turnstile> {} {c1} {}" "R,G \<turnstile> {} {c2} {}" by auto
  then show ?case by auto
next
  case (Capture s c)
  thus ?case by (intro capture, simp add: guar_mix)
qed (auto)



lemma seq_rot:
  "R,G \<turnstile> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile> Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 ;; c\<^sub>2 } M"
  by auto

end

end