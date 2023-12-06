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
  thread[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> P = {} \<or> rif R c \<Longrightarrow> R,G \<turnstile> P { Thread c } Q" |
  par[intro]:     "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                    R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (Q\<^sub>1 \<inter> Q\<^sub>2)" |
  conseq[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                    R',G' \<turnstile> P' { c } Q'"  |
  inv[intro]:     "R,G \<turnstile> P {c} Q \<Longrightarrow> stable (R \<union> G) I \<Longrightarrow> guard I R,G \<turnstile> P \<inter> I {c} Q \<inter> I" |
  capture[intro]: "capRely R,capGuar G \<turnstile> capPred s P {c} capPost Q \<Longrightarrow> 
                    R,G \<turnstile> P {Capture s c} Q" |
  interr[intro]:  "P \<subseteq> I \<Longrightarrow> stable R I \<Longrightarrow> stable G I \<Longrightarrow> R,G \<turnstile> P {c} _ \<Longrightarrow>
                    R,G \<turnstile> P {\<triangle>c} I"
(*   for interr the wmm should be set to sc but this parameter
     will be set accordingly in the instantiation when \<triangle> is seq composed within ite-com *)


subsection \<open>Elimination Rules\<close>

lemma nilE [elim!]:
  assumes "R,G \<turnstile> P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms 
  by (induct R G P "Nil :: ('a,'b,'c) com" Q) blast+


lemma nilE2:
  assumes "R,G \<turnstile> P {Nil} Q"
  shows "stabilise R P \<subseteq> Q"
proof -
  obtain M where m: "stable R M" "P \<subseteq> M" "M \<subseteq> Q" using assms by auto
  hence "stabilise R M = M" by (simp add: stabilise_stable)
  moreover have "stabilise R P \<subseteq> stabilise R M" using stabilise_mono m by auto
  ultimately show ?thesis using m by auto
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
  case (inv R G P Q I)
  show ?case 
  proof (rule inv(2), goal_cases)
    case (1 Q')
    hence "guard I R,G \<turnstile>\<^sub>A stabilise R P \<inter> I {\<beta>} Q' \<inter> I" using atomic_invI inv(3) by blast
    hence "guard I R,G \<turnstile>\<^sub>A stabilise (guard I R) (P \<inter> I) {\<beta>} Q' \<inter> I"
    proof (rule atomic_pre)
      show "stabilise (guard I R) (P \<inter> I) \<subseteq> stabilise R P \<inter> I"
        using stabilise_guard inv(3) by force
    qed auto
    thus ?case using inv(4)[of "Q' \<inter> I"] 1 by blast
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
  thus ?case by (meson pushpredAll_mono pushpred_mono pushrelAll_mono pushrelSame_mono rules.conseq)
next
  case (capture R G s P c Q)
  thus ?case by blast
next
  case (inv R G P Q I)
  show ?case
  proof (rule inv(2), goal_cases)
    case (1)
    let ?G="capGuar G" and ?R="capGuar ( R)" and ?I="capPost I"
    have "stable (pushrelSame R \<union> pushrelAll G) (pushpredAll I)"
      using inv(3) stable_pushrelAll stable_pushrelSame by simp
    with 1(1) have "guard ?I (pushrelSame R),?G \<turnstile> capPred s P \<inter> ?I {c} capPost Q \<inter> ?I"
      by (rule rules.inv)
    thus ?case using inv(4) pushrel_guard by force
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
  case (inv R G P Q I)
  show ?case 
  proof (rule inv(2), goal_cases)
    case (1 J G' Q')
    have "stable (R \<union> G') I" using inv(3) 1(5) by blast
    hence "guard I R, G' \<turnstile> P \<inter> I {c} Q' \<inter> I" using 1(4) by blast
    moreover have "stable (guard I R) (J \<inter> I)" using stable_guard inv(3) 1 by blast
    moreover have "stable G' (J \<inter> I)" using inv(3) 1 by blast
    ultimately show ?case using inv(4)[where ?I2="J \<inter> I"] 1(1,5,6) by blast
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
  case (inv R G P c Q I)
  hence "guard I R,G \<turnstile> stabilise R P \<inter> I {c} Q \<inter> I" by (intro rules.inv)
  thus ?case using stabilise_guard inv by blast
next
  case (capture R G s P c Q)
  thus ?case using stabilise_pushrel by blast
next
  case (interr P Q R G c uu)
  have "(stabilise R P) \<subseteq> Q" using interr(1,2) by (simp add: stabilise_min)
  thus ?case using interr(2,3,5) rules.interr by blast
next
  case (thread R G P c Q)
  then show ?case by force
qed auto


text \<open>It is always possible to rephrase a judgement in terms of a stable precondition\<close>
lemma stable_preE:
  assumes "R,G \<turnstile> P {c} Q"
  shows "\<exists>P'. P \<subseteq> P' \<and> stable R P' \<and> R,G \<turnstile> P' {c} Q"
  using assms stabilise_supset stable_stabilise stable_preE'
  by metis


subsection \<open>Introduction Rules\<close>

lemma falseI:
  "R,G \<turnstile> {} {c} {}"
proof (induct c arbitrary: R G)
  case (Basic x)
  thus ?case 
  apply (intro basic) apply (auto simp: atomic_rule_def guar_def wp_def)
  .
next
  case (Seq c1 w c2)
  hence "R,G \<turnstile> {} {c1} {}" "R,G \<turnstile> {} {c2} {}" by (meson local_simps(3) subsetD)+
  then show ?case by auto
next
  case (Parallel c1 c2)
  show ?case using par[OF Parallel, of "{}" R "{}" R] by blast 
qed (auto)


text \<open>Example of context-sensitive rely modification\<close>
lemma procI:
  assumes "R_callee,G_callee \<turnstile> P { c } Q"
  assumes "R_caller \<subseteq> guard (stabilise (R_caller \<union> G_callee) P) R_callee"
  assumes "G_callee \<subseteq> G_caller"
  shows "R_caller,G_caller \<turnstile> P { c } Q"
proof -
  let ?R = "R_callee \<inter> R_caller"
  let ?I = "stabilise (?R \<union> G_callee) P"
  have "?R,G_callee \<turnstile> P { c } Q" using assms(1) by blast
  hence "guard ?I ?R,G_callee \<turnstile> (P \<inter> ?I) {c} (Q \<inter> ?I)" by (rule inv) simp
  thus ?thesis
  proof (rule conseq)
    show "P \<subseteq> P \<inter> ?I" by (simp add: stabilise_supset)
  next
    have "R_caller \<subseteq> guard (stabilise (R_caller \<union> G_callee) P) ?R"
      using assms(2) by (auto simp: guard_def)
    also have "... \<subseteq> guard ?I ?R" by (blast intro!: guard_mono stabilise_mono_R)
    finally show "R_caller \<subseteq> guard ?I ?R" .
  qed (insert assms(3), auto)
qed


lemma old_invI [intro]:
  assumes "R,G \<turnstile> P {c} Q" "stable R' I" "G \<subseteq> R'"
  shows "R \<inter> R',G \<turnstile> (P \<inter> I) {c} (Q \<inter> I)"
proof -
  have "R \<inter> R',G \<turnstile> P {c} Q" using assms by blast
  moreover have "stable (R \<inter> R' \<union> G) I" using assms(2,3) by blast
  ultimately have "guard I (R \<inter> R'),G \<turnstile> (P \<inter> I) {c} (Q \<inter> I)" by blast
  thus ?thesis using guard_subset conseq by blast
qed

lemma choice_if:
  assumes "R,G \<turnstile> P { c\<^sub>1 } Q"
  assumes "R,G \<turnstile> P { c\<^sub>2 } Q"
  shows "R,G \<turnstile> P { \<Sqinter>s. if C s then c\<^sub>1 else c\<^sub>2 } Q"
  using assms by - (rule choice, auto)

end

end


