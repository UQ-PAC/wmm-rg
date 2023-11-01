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
  seq[intro]:     "R,G \<turnstile> M { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 } M \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 ;\<^sub>w c\<^sub>2 } Q" |
  choice[intro]:  "\<forall>l. R,G \<turnstile> P { S l } Q \<Longrightarrow> R,G \<turnstile> P { Choice S } Q" |
  loop[intro]:    "stable R P \<Longrightarrow> R,G \<turnstile> P { c } P \<Longrightarrow> R,G \<turnstile> P { c*\<^sub>w } P" |
  thread[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> rif R c \<Longrightarrow> R,G \<turnstile> P { Thread c } Q" |
  par[intro]:     "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                    R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (Q\<^sub>1 \<inter> Q\<^sub>2)" |
  conseq[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                    R',G' \<turnstile> P' { c } Q'"  |
  inv[intro]:     "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' I \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> 
                    R \<inter> R',G \<turnstile> (P \<inter> I) {c} (Q \<inter> I)" | 
  capture[intro]: "capRely R,capGuar G \<turnstile> capPred s P {c} capPost Q \<Longrightarrow> 
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
  obtains M  where "R,G \<turnstile> P {c\<^sub>1} M" "R,G \<turnstile> M {c\<^sub>2} Q"
  using assms by (induct R G P "c\<^sub>1 ;\<^sub>w c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+  


lemma captureE:
  assumes "R,G \<turnstile> P {Capture s c} Q"
  obtains "capRely R, capGuar G \<turnstile> capPred s P {c} capPost Q" 
using assms
proof (induct R G P "Capture s c" Q arbitrary: s c)
  case (conseq R G P Q P' R' G' Q')
  thus ?case by (meson pushpredAll_mono pushpred_mono pushrelAll_eq pushrelSame_mono rules.conseq)
next
  case (capture R G s P c Q)
  thus ?case by blast
next
  case (inv R G P Q R' I)
  show ?case
  proof (rule inv(2), goal_cases)
    case (1)
    let ?G="capGuar G" and ?R="capGuar R'" and ?I="capPost I"
    have "stable ?R ?I" using inv(3) by (rule stable_pushrelAll)
    moreover have "?G \<subseteq> ?R" using inv(4) by (rule pushrelAll_mono)      
    ultimately have "capRely R \<inter> ?R,?G \<turnstile> capPred s P \<inter> ?I {c} capPost Q \<inter> ?I" using 1(1) by blast
    thus ?case using inv(5) by force
  qed
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
  thus ?case using stabilise_pushrel by blast
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


lemma falseI:
  "local c \<Longrightarrow> R,G \<turnstile> {} {c} {}"
proof (induct c arbitrary: R G)
  case (Basic x)
  thus ?case 
  by (intro basic) (auto simp: atomic_rule_def guar_def wp_def)
next
  case (Seq c1 w c2)
  hence "R,G \<turnstile> {} {c1} {}" "R,G \<turnstile> {} {c2} {}" by (meson local_simps(3) subsetD)+
  then show ?case by auto
qed (auto)

end

end


