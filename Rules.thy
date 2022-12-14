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
  basic[intro]:   "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<Longrightarrow> R,G \<turnstile> P { Basic \<alpha> } Q" |
  nil[intro]:     "stable R P \<Longrightarrow> R,G \<turnstile> P { Nil } P" |
  seq[intro]:     "R,G \<turnstile> M { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 } M \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 ;\<^sub>w c\<^sub>2 } Q" |
  choice[intro]:  "\<forall>l. R,G \<turnstile> P { S l } Q \<Longrightarrow> R,G \<turnstile> P { Choice S } Q" |
  loop[intro]:    "stable R P \<Longrightarrow> R,G \<turnstile> P { c } P \<Longrightarrow> R,G \<turnstile> P { c*\<^sub>w } P" |
  thread[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> rif R G c \<Longrightarrow> R,G \<turnstile> P { Thread c } Q" |
  par[intro]:     "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                    R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (Q\<^sub>1 \<inter> Q\<^sub>2)" |
  conseq[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                    R',G' \<turnstile> P' { c } Q'"  |
  inv[intro]:     "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' I \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> R \<inter> R',G \<turnstile> (P \<inter> I) {c} (Q \<inter> I)" | 
  capture[intro]: "capRely R,capGuar G \<turnstile> pushpred s P {c} pushpredAll Q \<Longrightarrow> 
                    R,G \<turnstile> P {Capture s c} Q" |
  interr[intro]:  "P \<subseteq> Q \<Longrightarrow> G' \<subseteq> G \<Longrightarrow> stable G' Q \<Longrightarrow> stable R Q  
                          \<Longrightarrow> R,G' \<turnstile> P {c} _ \<Longrightarrow> rif R G' c \<Longrightarrow> R,G \<turnstile> P {(\<triangle>c)} Q" 
(*   for interr the wmm should be set to sc in instantiation but this parameter
     will be set accordingly in the instantiation when \<triangle> is seq composed within ite-com *)

subsection \<open>Properties\<close>

lemma nilE [elim!]:
  assumes "R,G \<turnstile> P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms 
  by (induct R G P "Nil :: ('a,'b) com" Q) blast+

lemma nilE2:
  assumes "R,G \<turnstile> P {Nil} Q"
  shows "stabilise R P \<subseteq> Q"
  using assms 
proof (induct R G P "Nil :: ('a,'b) com" Q)
  case (nil R P G)
  then show ?case 
    by (simp add: stabilise_stable) 
next
  case (conseq R G P Q P' R' G' Q')
  then show ?case 
    by (meson dual_order.trans stabilise_mono_RP) 
next
  case (inv R G P Q R' I)
  then show ?case 
    by (metis Int_commute inf_mono order_refl stabilise_inter_RP stabilise_stable 
        subset_trans)
qed


lemma basicE [elim!]:
  assumes "R,G \<turnstile> P {Basic \<beta>} Q"
  obtains Q' where "R,G \<turnstile>\<^sub>A stabilise R P {\<beta>} Q'" "Q' \<subseteq> Q"
  using assms 
proof (induct R G P "Basic \<beta> :: ('a,'b) com" Q arbitrary: \<beta>)
  case (basic R G P \<alpha> Q)
  then show ?case using stabilise_atomic by fast
next
  case (conseq R G P Q P' R' G' Q')
  show ?case
  proof (rule conseq(2), goal_cases)
    case (1 Q')
    thus ?case using conseq
    by (meson atomic_conseqI atomic_pre dual_order.trans stabilise_mono_RP stable_stabilise)
  qed
next
  case (inv R G P Q R' I)
  show ?case 
  proof (rule inv(2), goal_cases)
    case (1 Q')
    thus ?case using inv(3,4) inv(5)[of "Q' \<inter> I"] atomic_invI
      by (smt (verit, best) Int_greatest atomic_pre dual_order.eq_iff dual_order.trans 
                            le_infE stabilise_inter_RP stabilise_stable stable_stabilise)
  qed
qed


lemma seqE [elim]:
  assumes "R,G \<turnstile> P {c\<^sub>1 ;\<^sub>w c\<^sub>2} Q"
  obtains M  where "R,G \<turnstile> P {c\<^sub>1} M" "R,G \<turnstile> M {c\<^sub>2} Q"
  using assms by (induct R G P "c\<^sub>1 ;\<^sub>w c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+  
 

lemma captureE:
  assumes "R,G \<turnstile> P {Capture s c} Q"
  shows "capRely R, capGuar G \<turnstile> capPred s P {c} pushpredAll Q"
using assms
proof (induct R G P "Capture s c" Q arbitrary: s c)
  case (conseq R G P Q P' R' G' Q')
  thus ?case using rules.conseq by force
next
  case (capture R G s P c Q)
  thus ?case by simp
next
  case (inv R G P Q R' I)
  have "pushrelSame R,pushrelAll G \<turnstile> pushpred s P {c} pushpredAll Q"
    using inv(2) by auto
  moreover have "pushrelAll G \<subseteq> pushrelAll R'"
    using inv by (intro pushrelAll_mono)
  moreover have
    "stable (pushrelAll R') (pushpredAll I)"
    using inv by (intro stable_pushrelAll)
  ultimately have 
    "pushrelSame R \<inter> pushrelAll R',pushrelAll G
      \<turnstile> pushpred s P \<inter> pushpredAll I {c} pushpredAll Q \<inter> pushpredAll I"
    by (intro rules.inv)
  hence 
    "pushrelSame R \<inter> pushrelAll R',pushrelAll G
      \<turnstile> pushpred s (P \<inter> I) {c} pushpredAll (Q \<inter> I)"
    by (simp add: pushpred_inter_pushpredAll pushpredAll_inter)
  hence
    "pushrelSame (R \<inter> R'),pushrelAll G 
      \<turnstile> pushpred s (P \<inter> I) {c} pushpredAll (Q \<inter> I)"
    using pushrelSame_in_pushrelAll by auto 
  thus ?case.
qed


lemma interrE:
  assumes "R,G \<turnstile> P {(\<triangle>c)} Q"
  obtains G' Q' where "P \<subseteq> Q" "G' \<subseteq> G" "stable G' Q" "stable R Q" 
                           "R,G' \<turnstile> P {c} Q'" "rif R G' c"  
  using assms 
proof (induct R G P "(\<triangle>c)" Q arbitrary: c)
  case (conseq R G P Q P' R' G' Q')
  show ?case 
  proof (rule conseq(2), goal_cases)
    case (1 P'' G'' Q'')
    then show ?case
      using conseq
      using rules.conseq[of "R" "G'" "P" "c" "Q'"]
                          stable_conseqI[of "R" "P"] sorry
  qed
next
  case (inv R G P Q R' I)
  show ?case 
  proof (rule inv(2), goal_cases)
    case (1 G' Q')
    then show ?case sorry
  qed
next
  case (interr G' G P R c uu)
  then show ?case sorry
qed 


text \<open>In fact, we can rephrase a judgement with an explicit stabilisation.\<close>
lemma stable_preE':
  assumes "R,G \<turnstile> P {c} Q"
  shows "R,G \<turnstile> stabilise R P {c} Q"
using assms
proof (induct)
  case (basic R G P \<alpha> Q)
  thus ?case using stabilise_atomic by (intro rules.basic, simp)
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
  case (capture R G s P c Q)
  thus ?case by (intro rules.capture, auto simp add: stabilise_pushrel)
next
  case (interr G G' P R c uu)
  thus ?case apply (simp add: rules.interr stabilise_stable) sorry
qed auto


text \<open>It is always possible to rephrase a judgement in terms of a stable precondition\<close>
lemma stable_preE:
  assumes "R,G \<turnstile> P {c} Q"
  shows "\<exists>P'. P \<subseteq> P' \<and> stable R P' \<and> R,G \<turnstile> P' {c} Q"
  using assms stabilise_supset stable_stabilise stable_preE'
  by metis

text \<open> Combining choice with capture to provide the choice over some var that is "hidden" \<close>

abbreviation univ_capture  ("\<forall>\<^sub>c _")
  where "univ_capture c \<equiv> \<Sqinter>s. Capture s c"  

(* \<forall>\<^sub>c here chooses some pushed s without knowing it, hence wp (\<Sqinter>s. Capture s c) Q 
   is the wp to reach Q for all elems which might be topmost on the mem-stack *)

text \<open>Universal quantification of top-most stack frame\<close>
lemma univ_captureI:
  assumes "\<forall>l. pushrelSame R,pushrelAll G \<turnstile> pushpred l P {c} pushpredAll Q"
  shows "R,G \<turnstile> P {univ_capture c} Q"
  using assms by (intro choice allI capture) simp



end

end