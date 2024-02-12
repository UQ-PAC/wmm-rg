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
  assumes "R,G \<turnstile> P {c} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "inter\<^sub>c w R c \<alpha>" "\<alpha>' < c <\<^sub>w \<alpha>" 
  obtains M' where "R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M'" "R,G \<turnstile> M' {c} Q"
  using assms
proof (induct c arbitrary: R G P M Q \<alpha> \<alpha>')
  case Nil
  hence "stabilise R P \<subseteq> M" using stable_preE'[OF Nil(2)] by blast
  then show ?case using Nil atomic_rule_def unfolding reorder_com.simps
    by (metis atomic_pre nil stable_stabilise) 
next
  case (Basic \<beta>)
  obtain N' where \<beta>: "R,G \<turnstile>\<^sub>A stabilise R P {\<beta>} N'" "N' \<subseteq> M" using Basic by auto
  have m': "R,G \<turnstile>\<^sub>A N' {\<alpha>} Q"
    using atomic_pre[OF Basic(3)] \<beta>(1,2) Basic(3) by (auto simp: atomic_rule_def)
  obtain M' where m'': "R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M'" "R,G \<turnstile>\<^sub>A M' {\<beta>} Q"
    using \<beta>(1) m'(1) Basic
    unfolding inter\<^sub>\<alpha>_def inter\<^sub>c.simps reorder_com.simps by metis
  have "R,G \<turnstile> M' {Basic \<beta>} Q" by (rule rules.basic[OF m''(2)])
  then show ?case using Basic(1) \<beta>(1) m''(1) by auto
next
  case (Seq c\<^sub>1 w' c\<^sub>2)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} M" using Seq(4) by fast 
  obtain \<alpha>'' where r: "\<alpha>'' < c\<^sub>2 <\<^sub>w \<alpha>" "\<alpha>' < c\<^sub>1 <\<^sub>w \<alpha>''" using Seq(7) by auto
  hence i: "inter\<^sub>c w R c\<^sub>1 \<alpha>''" "inter\<^sub>c w R c\<^sub>2 \<alpha>" using Seq(6) unfolding inter\<^sub>c.simps by blast+
  show ?case
  proof (rule Seq(2)[OF _ m(2) Seq(5) i(2) r(1)], goal_cases outer)
    case (outer N')
    hence c1: "R,G \<turnstile> P {c\<^sub>1} stabilise R M'" using m(1) conseq stabilise_supset[of M'] by fast
    show ?case 
    proof (rule Seq(1)[OF _ c1 outer(1) i(1) r(2)], goal_cases inner)
      case (inner M'')
      then show ?case using Seq(3) outer using Seq.prems(2) by blast
    qed
  qed
qed auto 

section \<open>Transition Rules\<close>

text \<open>Judgements are preserved across thread-local execution steps\<close>
lemma lexecute_ruleI [intro]:                
  assumes "R,G \<turnstile> P {c} Q" "c \<mapsto>[\<alpha>',r] c'" "inter R r" 
  shows "\<exists>M. R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<and> R,G \<turnstile> M {c'} Q"
  using assms(2,1,3)
proof (induct arbitrary: P R G Q)
  case (act \<alpha>)
  then show ?case by clarsimp (meson atomic_rule_def nil rules.conseq order_refl)
next
  case (ino c\<^sub>1 \<alpha>' r c\<^sub>1' w c\<^sub>2)
  then obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} Q" by auto 
  then show ?case using ino(2)[OF m(1) ino(4)] m(2) using ino.prems(1) by blast
next
  case (ooo c\<^sub>1 \<alpha>' r c\<^sub>1' \<alpha>'' c\<^sub>2 w)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>2} M'" "R,G \<turnstile> M' {c\<^sub>1} Q" using ooo(4) by (rule seqE)
  have i: "inter\<^sub>c w R c\<^sub>2 \<alpha>'" "inter R r" using ooo(5) by auto
  obtain M where m': "R,G \<turnstile>\<^sub>A stabilise R M' {\<alpha>'} M" "R,G \<turnstile> M {c\<^sub>1'} Q"
    using ooo(2)[OF m(2) i(2)] by auto
  have m'': "R,G \<turnstile> P {c\<^sub>2} stabilise R M'" using m(1) stabilise_supset[of M' R] by auto
  show ?case using reorder_prog[OF m'' m'(1)] i(1) m'(2) ooo(3) 
    by (metis (mono_tags, lifting) seq seqE)
next
  case (cap c \<alpha>' r c' s s')
  let ?R="capRely R" and ?G="capGuar G" and ?P="capPred s P" and ?Q="capPost Q"
  obtain "?R,?G \<turnstile> ?P {c} ?Q" using cap(3) by (rule captureE)
  moreover have "inter ?R r" using cap(4) by simp
  ultimately obtain M where m: "?R,?G \<turnstile>\<^sub>A stabilise ?R ?P {\<alpha>'} M" "?R,?G \<turnstile> M {c'} ?Q"
    using cap(2) by force
  have "R,G \<turnstile>\<^sub>A stabilise R P {popbasic s s' \<alpha>'} poppred' s' M" using m(1)
    apply (rule atomic_pre[OF atomic_popI])
    by (intro push_to_pop stabilise_pushrel) auto
  moreover have "R,G \<turnstile> poppred' s' M {Capture s' c'} Q" using m(2)
    by (meson capture conseq dual_order.refl push_poppred_subset)
  ultimately show ?case by blast
next
  case (inter1 c\<^sub>1 \<alpha>' r c\<^sub>2)    
  show ?case 
  proof -
    obtain I G' Q' where g:
    "P \<subseteq> I" "stable R I" "stable G' I"  "R,G' \<turnstile> P {c\<^sub>1} Q'" "G' \<subseteq> G" "I \<subseteq> Q"
      using inter1(3) by (rule interrE)
    obtain M where m: "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M" "R,G' \<turnstile> M {c\<^sub>2} Q'" 
      using  g(4) inter1.prems(2) inter1.hyps(2) by force
    have m0:"stabilise R P = {} \<or> guar\<^sub>\<alpha> \<alpha>' G'" using m(1) atomic_rule_def by metis
    have g2:"G' \<subseteq> (G' \<union> R)" by auto
    have g3:"stable (G' \<union> R) I" using g(2,3) by (meson State.stable_def Un_iff)
    have p1:"(stabilise R P) \<subseteq> (stabilise R P) \<inter> I"  using g(1,2)
      by (simp add: stabilise_min)

    have "guard I R,G' \<turnstile>\<^sub>A stabilise R P \<inter> I {\<alpha>'} M \<inter> I"
      using atomic_invI m(1) g3 by blast
    hence "R,G \<turnstile>\<^sub>A stabilise R P  \<inter> I {\<alpha>'} M \<inter> I" using guard_subset g(5) atomic_conseqI
      by auto  
    hence m3:"R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<inter> I" using p1 atomic_pre stable_stabilise
      by fast

    have m4:"R,G' \<turnstile> M \<inter> I {c\<^sub>2} Q'" using m(2) rules.conseq by blast
    have g1:"M \<inter> I \<subseteq> I" by auto
    have g2:"M \<inter> I \<subseteq> M" by auto
    have c1:"R,G' \<turnstile> M \<inter> I {c\<^sub>2} Q'" using m(2) g2 rules.conseq by blast
    have c2:"R,G' \<turnstile> M \<inter> I {\<triangle>c\<^sub>2} I" using g(1,2,3) c1 rules.interr by simp
    have c3:"R,G \<turnstile> M \<inter> I {\<triangle>c\<^sub>2} Q" using c2 g(5,6) rules.conseq by blast 
    then show ?thesis using m3 c3 by auto
  qed
qed

text \<open>Judgements are preserved across silent steps\<close>
lemma rewrite_ruleI [intro]:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<leadsto> c'"
  shows "R,G \<turnstile> P {c'} Q"
  using assms
proof (induct arbitrary: c' rule: rules.induct)
  case (seq R G M c\<^sub>2 Q P c\<^sub>1 w)
  thus ?case by (cases rule: silentE, auto) (blast)+
next
  case (capture R G s P c Q)
  show ?case using capture
  proof (cases "Capture s c" c' rule: silentE)
    case (15 k)
    hence "stabilise (capRely R) (capPred s P) \<subseteq> pushpredAll Q"
      using nilE2 capture(1) by simp
    hence "pushpred s (stabilise R P) \<subseteq> pushpredAll Q"
      using stabilise_pushrel by fast
    thus ?thesis unfolding 15
      by simp (meson conseq dual_order.refl nil stabilise_supset stable_stabilise)
  qed auto
next
  case (inv R G P c Q I)
  then show ?case by blast
qed (cases rule: silentE, auto)+

text \<open>Judgements are preserved across global execution steps\<close>

lemma gexecute_ruleI [intro]:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<mapsto>[\<alpha>] c'" "P \<noteq> {}"
  shows "\<exists>M. P \<subseteq> wp\<^sub>\<alpha> \<alpha> M \<and> guar\<^sub>\<alpha> \<alpha> G \<and> R,G \<turnstile> M {c'} Q \<and> \<alpha> \<in> obs c"
  using assms
proof (induct arbitrary: g c' rule: rules.induct)
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case using par(7)
  proof cases
    case (par1 c\<^sub>1')
    obtain M\<^sub>2 where m2: "P\<^sub>2 \<subseteq> M\<^sub>2" "stable R\<^sub>2 M\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2} Q\<^sub>2" using par
      by (meson stable_preE)
    hence "P\<^sub>1 \<noteq> {}" using par by blast
    then obtain M\<^sub>1  where m1: "P\<^sub>1 \<subseteq> wp\<^sub>\<alpha> \<alpha> M\<^sub>1" 
         "guar\<^sub>\<alpha> \<alpha> G\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1'} Q\<^sub>1" "\<alpha> \<in> obs c\<^sub>1"
      using par1 par(2)[OF par1(2)] by force
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par1 m2 par by blast
    moreover have "P\<^sub>1 \<inter> P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<alpha> (M\<^sub>1 \<inter> M\<^sub>2)" 
      using m1(1,2,3) m2(1,2) par.hyps(6) unfolding guar_def wp_def stable_def
      by auto blast
    ultimately show ?thesis using m1 unfolding guar_def obs_par by blast
  next
    case (par2 c\<^sub>2')
    obtain M\<^sub>1 where m1: "P\<^sub>1 \<subseteq> M\<^sub>1" "stable R\<^sub>1 M\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1} Q\<^sub>1" using par
      by (meson stable_preE)
    hence "P\<^sub>2 \<noteq> {}" using par by blast
    then obtain M\<^sub>2  where m2: "P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<alpha> M\<^sub>2" 
         "guar\<^sub>\<alpha> \<alpha> G\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2'} Q\<^sub>2" "\<alpha> \<in> obs c\<^sub>2"
      using par2 par(4)[OF par2(2)] by force
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par2 m1 par by blast
    moreover have "P\<^sub>1 \<inter> P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<alpha> (M\<^sub>1 \<inter> M\<^sub>2)" 
      using m1(1,2) m2(1,2,3) par.hyps(5) unfolding guar_def wp_def stable_def
      by auto blast
    ultimately show ?thesis using m2 unfolding guar_def obs_par by blast
  qed 
next
  case (conseq R G P c Q P' R' G' Q')
  hence "P \<noteq> {}" by auto
  thus ?case using conseq by (smt Un_iff guar_def rules.conseq subset_iff)
next
  case (inv R G P c Q I)
  then obtain M  where p: "P \<subseteq> wp\<^sub>\<alpha> \<alpha> M" "guar\<^sub>\<alpha> \<alpha> G" "R,G \<turnstile> M {c'} Q" "\<alpha> \<in> obs c"
    by blast
  hence "P \<inter> I \<subseteq> wp\<^sub>\<alpha> \<alpha> (M \<inter> I)" using inv(3,4) unfolding stable_def guar_def wp_def by blast
  thus ?case using rules.inv p inv(3,4) by blast
next
  case (thread R G P c Q)
  hence r: "rif R c" by auto
  obtain r  c'' where e:  "c \<mapsto>[\<alpha>,r] c''" "c' = Thread c''" "\<alpha> \<in> obs c"
    using thread gexecuteE[OF thread(4), simplified] obs_act by metis
  then obtain M where "R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>} M" "R,G \<turnstile> M {c''} Q" "rif R c''"
    using thread lexecute_ruleI[OF thread(1) e(1)] indep_stepI[OF r e(1)] by metis
  thus ?case using stabilise_supset[of P R] e thread(5) unfolding atomic_rule_def obs_thread
    using local.rules.thread by blast
qed auto

end

end
