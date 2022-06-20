theory Transition_Rules
  imports Rules
begin

context rules
begin

text \<open>
A series of lemmas that demonstrate the logic's rules are preserved across the semantic steps and
ensure any executed behaviours conform to the desired specification.
\<close>

section \<open>Reordering Rules\<close> 

text \<open>
  Reorder the judgements of a reorderable instruction \<alpha> and program c, given a suitable 
  interference property.
\<close>
lemma reorder_prog:
  assumes "R,G \<turnstile> P {c} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "inter\<^sub>c R G c \<alpha>"
  obtains M' P' where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>c\<rrangle>} M'" "R,G \<turnstile> M' {c} Q"
  using assms
proof (induct c arbitrary: R G P M Q \<alpha>)
  case Nil
  hence "P \<subseteq> M" by blast
  then show ?case using Nil by (auto simp: atomic_rule_def)
next
  case (Basic \<beta>)
  obtain P' N' where \<beta>: "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>} N'" "N' \<subseteq> M" using Basic by auto
  have m': "R,G \<turnstile>\<^sub>A N' {\<alpha>} Q"
    using atomic_pre[OF Basic(3)] \<beta>(2,3) Basic(3) by (auto simp: atomic_rule_def)
  obtain M' where m'': "R,G \<turnstile>\<^sub>A P' {\<alpha>\<langle>tag \<beta>\<rangle>} M'" "R,G \<turnstile>\<^sub>A M' {\<beta>} Q"
    using \<beta>(2) m'(1) Basic by (auto simp: inter\<^sub>\<alpha>_def) metis
  have "R,G \<turnstile> M' {Basic \<beta>} Q" by (rule rules.basic[OF m''(2)])
  then show ?case using Basic(1) \<beta>(1) m''(1) by auto
next
  case (Seq c\<^sub>1 c\<^sub>2)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} M" using Seq(4) by fast
  have i: "inter\<^sub>c R G c\<^sub>1 \<alpha>\<llangle>c\<^sub>2\<rrangle>" "inter\<^sub>c R G c\<^sub>2 \<alpha>" using Seq by auto
  show ?case
  proof (rule Seq(2)[OF _ m(2) Seq(5) i(2)], goal_cases outer)
    case (outer P' N')
    hence c1: "R,G \<turnstile> P {c\<^sub>1} P'" using m(1) conseq by auto
    show ?case 
    proof (rule Seq(1)[OF _ c1 outer(2) i(1)], goal_cases inner)
      case (inner P'' M'')
      then show ?case using Seq(3) outer by auto
    qed
  qed
next
  case (Ord c\<^sub>1 c\<^sub>2)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} M" using Ord(4) by fast
  have i: "inter\<^sub>c R G c\<^sub>1 \<alpha>\<llangle>c\<^sub>2\<rrangle>" "inter\<^sub>c R G c\<^sub>2 \<alpha>" using Ord by auto
  show ?case
  proof (rule Ord(2)[OF _ m(2) Ord(5) i(2)], goal_cases outer)
    case (outer P' N')
    hence c1: "R,G \<turnstile> P {c\<^sub>1} P'" using m(1) conseq by auto
    show ?case 
    proof (rule Ord(1)[OF _ c1 outer(2) i(1)], goal_cases inner)
      case (inner P'' M'')
      then show ?case using Ord(3) outer by auto
    qed
  qed
qed auto

section \<open>Transition Rules\<close>


text \<open>Judgements are preserved across thread-local execution steps\<close>
lemma lexecute_ruleI [intro]:
  assumes "R,G \<turnstile> P {c} Q" "c \<mapsto>[r,\<alpha>] c'"  "inter\<^sub>c R G r \<alpha>"
  shows "\<exists>P' M. P \<subseteq> P' \<and> R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M \<and> R,G \<turnstile> M {c'} Q"
  using assms(2,1,3)
proof (induct arbitrary: P R G Q)
  case (act \<alpha>)
  then show ?case by clarsimp (meson atomic_rule_def nil rules.conseq order_refl)
next
  case (ino c\<^sub>1 c \<alpha>' c\<^sub>1' c\<^sub>2)
  then obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} Q" by auto
  then show ?case using ino(2)[OF m(1) ino(4)] m(2) by blast
next
  case (ord c\<^sub>1 c \<alpha> c\<^sub>1' c\<^sub>2)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} Q" 
    using ord by fast
  then show ?case using ord(2)[OF m(1) ord(4)] m(2) by blast
next
  case (ooo c\<^sub>2 c \<alpha> c\<^sub>2' \<alpha>' c\<^sub>1)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} Q" using ooo(4) by blast
  have i: "inter\<^sub>c R G c\<^sub>1 (\<alpha>\<llangle>c\<rrangle>)" "inter\<^sub>c R G c \<alpha>" using ooo by auto
  obtain P' M where m': "M' \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>c\<rrangle>} M" "R,G \<turnstile> M {c\<^sub>2'} Q"
    using ooo(2)[OF m(2) i(2)] by blast
  hence m'': "R,G \<turnstile> P {c\<^sub>1} P'" using m(1) by blast
  then show ?case using reorder_prog[OF m'' m'(2)] i(1) m'(3) by simp (metis rules.seq)
next
  case (cap c s r \<alpha> c')
  then obtain P' M s' where M: 
    "uncapPred s P \<subseteq> uncapPred s P'"
    "uncapRely R,uncapGuar G \<turnstile>\<^sub>A uncapPred s P' {(uncapBasic s \<alpha>)\<llangle>uncapCom s r\<rrangle>} M"
    "uncapRely R,uncapGuar G \<turnstile> uncapPred s M {c'} uncapPred s' Q"
       sorry
  hence "R,G \<turnstile> M {Capture s c'} Q" by fast
  moreover have "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M" sorry
  ultimately show ?case using M(1)
    by (metis capPred_mono cap_uncapPred)
oops



text \<open>Judgements are preserved across silent steps\<close>
lemma rewrite_ruleI [intro]:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<leadsto> c'"
  shows "R,G \<turnstile> P {c'} Q"
  using assms
proof (induct arbitrary: c' rule: rules.induct)
  case (seq R G P c\<^sub>1 Q c\<^sub>2 M)
  thus ?case by (cases rule: silentE, auto) blast+
next
  case (ord R G P c\<^sub>1 Q c\<^sub>2 M)
  thus ?case by (cases rule: silentE, auto) blast+
next
  case (capture R G s P c s' Q)
  show ?case using capture(3)
  proof (cases "Capture s c" c' rule: silentE)
    case (19 c c' k)
    thus ?thesis using capture(2) by fast
  next
    case (20 k)
    hence "uncapRely R,uncapGuar G \<turnstile> uncapPred s P {Nil} uncapPred s' Q"
      using capture(1) by fast
    then obtain M where M:
      "stable (uncapRely R) (uncapPred s M)"
      "uncapPred s P \<subseteq> uncapPred s M"
      "uncapPred s M \<subseteq> uncapPred s' Q"
      by (metis nilE pushpred_intro)
    hence 1: "stable R M" using stable_uncap by fast
    hence 2: "P \<subseteq> M" "M \<subseteq> Q"
      using M(2,3) by (metis poppred_mono pop_pushpred)+
    have "R,G \<turnstile> M {Nil} Q" using 1 2 by auto
    thus ?thesis using 2(1) 20(2) by (simp add: conseq)
  qed auto
qed (cases rule: silentE, auto)+


text \<open>Judgements are preserved across global execution steps\<close>
lemma gexecute_ruleI [intro]:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<mapsto>[g] c'"
  shows "\<exists>M v. P \<subseteq> wp v g M \<and> guar v g G \<and> R,G \<turnstile> M {c'} Q"
  using assms
proof (induct arbitrary: g c' rule: rules.induct)
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case using par(7)
  proof cases
    case (par1 c\<^sub>1')
    obtain M\<^sub>2 where m2: "P\<^sub>2 \<subseteq> M\<^sub>2" "stable R\<^sub>2 M\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2} Q\<^sub>2" using par
      by (meson stable_preE)
    obtain M\<^sub>1 v where m1: "P\<^sub>1 \<subseteq> wp v g M\<^sub>1" "guar v g G\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1'} Q\<^sub>1" 
      using par1 par(2)[OF par1(2)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par1 m2 par by blast
    moreover have "P\<^sub>1 \<inter> P\<^sub>2 \<subseteq> wp v g (M\<^sub>1 \<inter> M\<^sub>2)" 
      using m1(1,2) m2(1,2) par.hyps(6) unfolding guar_def wp_def stable_def
      by auto blast
    ultimately show ?thesis using m1(2) unfolding guar_def by blast
  next
    case (par2 c\<^sub>2')
    obtain M\<^sub>1 where m1: "P\<^sub>1 \<subseteq> M\<^sub>1" "stable R\<^sub>1 M\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1} Q\<^sub>1" using par
      by (meson stable_preE)
    obtain M\<^sub>2 v where m2: "P\<^sub>2 \<subseteq> wp v g M\<^sub>2" "guar v g G\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2'} Q\<^sub>2" 
      using par2 par(4)[OF par2(2)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par2 m1 par by blast
    moreover have "P\<^sub>1 \<inter> P\<^sub>2 \<subseteq> wp v g (M\<^sub>1 \<inter> M\<^sub>2)" 
      using m1(1,2) m2(1,2) par.hyps(5) unfolding guar_def wp_def stable_def
      by auto blast
    ultimately show ?thesis using m2(2) unfolding guar_def by blast
  qed 
next
  case (conseq R G P c Q P' R' G' Q')
  thus ?case by (smt Un_iff guar_def rules.conseq subset_iff)
next
  case (inv R G P c Q R' M')
  then obtain M v where p: "P \<subseteq> wp v g M" "guar v g G" "R,G \<turnstile> M {c'} Q" by metis
  hence "P \<inter> M' \<subseteq> wp v g (M \<inter> M')" using inv(3,4) by (auto simp: stable_def guar_def wp_def) blast
  thus ?case using rules.inv p(2,3) inv(3,4) by blast
next
  case (thread R G P c Q)
  then obtain r \<alpha> c'' where e: "g = beh \<alpha>\<llangle>r\<rrangle>" "c \<mapsto>[r,\<alpha>] c''" "c' = Thread c''" by auto
  then obtain P' M where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M" "R,G \<turnstile> M {c''} Q" "rif R G c''"
    using thread lexecute_ruleI indep_stepI[OF thread(3) e(2)] by metis
  thus ?case using e unfolding atomic_rule_def by blast
qed auto

end

end