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
inductive rules :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b set \<Rightarrow> ('a,'b,'c) com \<Rightarrow> 'b set \<Rightarrow> bool" 
  ("_,_ \<turnstile> _ {_} _" [65,0,0,0,65] 65)
  where
  basic[intro]:   "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<Longrightarrow> R,G \<turnstile> P { Basic \<alpha> } Q" |
  nil[intro]:     "stable R P \<Longrightarrow> R,G \<turnstile> P { Nil } P" |
  seq[intro]:     "R,G \<turnstile> M { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 } M \<Longrightarrow> wlf w \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 ;\<^sub>w c\<^sub>2 } Q" |
  choice[intro]:  "\<forall>l. R,G \<turnstile> P { S l } Q \<Longrightarrow> R,G \<turnstile> P { Choice S } Q" |
  loop[intro]:    "stable R P \<Longrightarrow> R,G \<turnstile> P { c } P \<Longrightarrow> wlf w \<Longrightarrow> R,G \<turnstile> P { c*\<^sub>w } P" |
  thread[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> rif R c \<Longrightarrow> R,G \<turnstile> P { Thread c } Q" |
  par[intro]:     "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                    R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (Q\<^sub>1 \<inter> Q\<^sub>2)" |
  conseq[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                    R',G' \<turnstile> P' { c } Q'"  |
  inv[intro]:     "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' I \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> 
                    R \<inter> R',G \<turnstile> (P \<inter> I) {c} (Q \<inter> I)" | 
  capture[intro]: "capRely R,capGuar G \<turnstile> pushpred s P {c} pushpredAll Q \<Longrightarrow> 
                    R,G \<turnstile> P {Capture s c} Q" |
  interr[intro]:  "P \<subseteq> I \<Longrightarrow> stable R I \<Longrightarrow> stable G I \<Longrightarrow> R,G \<turnstile> P {c} _ \<Longrightarrow>
                    R,G \<turnstile> P {(\<triangle>c)} I" 
(*   for interr the wmm should be set to sc but this parameter
     will be set accordingly in the instantiation when \<triangle> is seq composed within ite-com *)

subsection \<open>Properties\<close>

lemma nilE [elim!]:
  assumes "R,G \<turnstile> P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms 
  by (induct R G P "Nil :: ('a,'b,'c) com" Q) blast+

lemma nilE2:
  assumes "R,G \<turnstile> P {Nil} Q"
  shows "stabilise R P \<subseteq> Q"
  using assms 
proof (induct R G P "Nil :: ('a,'b,'c) com" Q)
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
proof (induct R G P "Basic \<beta> :: ('a,'b,'c) com" Q arbitrary: \<beta>)
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
  obtains M  where "R,G \<turnstile> P {c\<^sub>1} M" "R,G \<turnstile> M {c\<^sub>2} Q" "wlf w"
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
  obtains I Q' G' where "P \<subseteq> I"  "stable R I"  "stable G' I" "R,G' \<turnstile> P {c} Q'" 
                      "G' \<subseteq> G" "I \<subseteq> Q" 
  using assms
proof (induct R G P "(\<triangle>c)" Q arbitrary: c)
  case (conseq R G P Q P' R' G' Q')
  show ?case 
  proof (rule conseq(2), goal_cases)
    case (1 I G'' Q'')
    then show ?case using conseq(3-7)
              rules.conseq[of "R" "G'" "P" "c" "Q'"]
              stable_conseqI[of "G'" "Q" "G''"] 
              conseq(7)[of "I""G''""Q''"] by blast 
  qed
next
  case (inv R G P Q' R' I2)
  show ?case 
  proof (rule inv(2), goal_cases)
    case (1 I3 G' Q)
    have a1:"P \<inter> I2 \<subseteq> (I3 \<inter> I2)" using 1(1) by auto
    have a2:"stable (R \<inter> R') (I3 \<inter> I2)" using  1 inv stable_conjI by blast
    have b0:"stable G I2" using inv(3,4) stable_conseqI by blast
    have b1:"stable G' I2" using b0 1(5) stable_conseqI by blast
    have a5:"stable G' (I3 \<inter> I2)" using 1(3) b1 stable_conjI by blast
    have a3:"R \<inter> R', G' \<turnstile> P \<inter> I2 {c} Q \<inter> I2" using 1 inv rules.inv by blast 
    have a0:"I3 \<inter> I2 \<subseteq> Q' \<inter> I2" using 1 inv  by auto
    then show ?case using inv 1 a0 a1 a2 a3 a5 inv(5) by blast
  qed
next
  case (interr P I R G c Q)
  then show ?case using interr(6)[of "I""G""Q"] by blast
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
  case (interr P Q R G c uu)
  have "(stabilise R P) \<subseteq> Q" using interr(1,2) by (simp add: stabilise_min)
  thus ?case using interr(2,3,5) rules.interr by blast
qed auto


text \<open>It is always possible to rephrase a judgement in terms of a stable precondition\<close>
lemma stable_preE:
  assumes "R,G \<turnstile> P {c} Q"
  shows "\<exists>P'. P \<subseteq> P' \<and> stable R P' \<and> R,G \<turnstile> P' {c} Q"
  using assms stabilise_supset stable_stabilise stable_preE'
  by metis

text \<open> to derive guar predicate from judgement \<close>

lemma wlf_trans:
  assumes "\<alpha>' < c <\<^sub>w \<alpha>" "wlf w" "guar\<^sub>\<alpha> \<alpha> G"
  shows "guar\<^sub>\<alpha> \<alpha>' G" using assms
proof (induct c arbitrary: \<alpha> \<alpha>' w)
  case Nil
  then show ?case using wlf_def reorder_com.simps(1) by auto
next
  case (Basic x)
  then show ?case using wlf_def reorder_com.simps(2) by metis
next
  case (Seq c1 w c2)
  obtain \<alpha>\<^sub>n where a0:"\<alpha>\<^sub>n < c2 <\<^sub>w \<alpha>" "\<alpha>' < c1 <\<^sub>w \<alpha>\<^sub>n"
    using Seq(3) reorder_com.simps(3) by blast
  have a1:"guar\<^sub>\<alpha> \<alpha>\<^sub>n G" using a0(1) Seq(2,4,5) by simp
  then show ?case using a1 a0(2) Seq(1,4,5) by simp
qed auto

lemma guar_com:
  assumes "c \<mapsto>[\<alpha>,r] c'" "R,G \<turnstile> P {c} Q" 
  shows "guar\<^sub>\<alpha> \<alpha> G" using assms
proof (induct arbitrary: P Q R G)
  case (act \<alpha>)
  then show ?case 
  proof -
    obtain Q' where a0:"R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>} Q'" using act basicE by auto
    then show ?thesis using atomic_rule_def by blast
  qed
next
  case (ino c\<^sub>1 \<alpha>' r c\<^sub>1' w c\<^sub>2)
  then show ?case 
  proof -
    obtain M where a0:"R,G \<turnstile> P {c\<^sub>1} M" using ino(3) seqE by auto
    then show ?thesis using ino(2) by auto
    qed
next
  case (ooo c\<^sub>1 \<alpha>' r c\<^sub>1' \<alpha>'' c\<^sub>2 w)
  then show ?case 
  proof -
    obtain M where m:"R,G \<turnstile> P {c\<^sub>2} M" "R,G \<turnstile> M {c\<^sub>1} Q" "wlf w" using ooo(4) seqE by auto
    have g1:"guar\<^sub>\<alpha> \<alpha>' G" using ooo(1) ooo(2) m(2) by auto
    then show ?thesis  using m(3) ooo(3) wlf_def wlf_trans by auto
    qed
next
  case (cap c \<alpha>' r c' s s')
  then show ?case 
  proof -
    have c0:"capRely R, pushrelAll G \<turnstile> capPred s P {c} pushpredAll Q" using captureE cap(4) by auto
    have c1:"guar\<^sub>\<alpha> \<alpha>' (pushrelAll G)" using c0 cap(2) by auto 
    then show ?thesis using guar_capE by (simp add: help3)
  qed
next
  case (inter1 c \<alpha>' r c')
  then show ?case 
  proof -
    obtain Q' where i0: "R,G \<turnstile> P {c} Q'" using interrE inter1(3)
      by (smt (verit) conseq equalityD2)
    have i1:"guar\<^sub>\<alpha> \<alpha>' G" using i0 inter1(2) by auto
    then show ?thesis using guar_sub i0 by auto
  qed
qed


end

end


