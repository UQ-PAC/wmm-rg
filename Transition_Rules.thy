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
  assumes "R,G \<turnstile> P {c} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "inter\<^sub>c w R G c \<alpha>" "\<alpha>' < c <\<^sub>w \<alpha>" 
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
  hence i: "inter\<^sub>c w R G c\<^sub>1 \<alpha>''" "inter\<^sub>c w R G c\<^sub>2 \<alpha>" using Seq(6) unfolding inter\<^sub>c.simps by blast+
  show ?case
  proof (rule Seq(2)[OF _ m(2) Seq(5) i(2) r(1)], goal_cases outer)
    case (outer N')
    hence c1: "R,G \<turnstile> P {c\<^sub>1} stabilise R M'" using m(1) conseq stabilise_supset[of M'] by fast
    show ?case 
    proof (rule Seq(1)[OF _ c1 outer(1) i(1) r(2)], goal_cases inner)
      case (inner M'')
      then show ?case using Seq(3) outer by auto
    qed
  qed
qed auto 

section \<open>Transition Rules\<close>


lemma atomic_subG:
  assumes "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} P" "G \<subseteq> G'" 
  shows "R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} P" sorry

lemma atomic_subG2:
  assumes "R,G' \<turnstile>\<^sub>A P {\<alpha>'} Q" "guar\<^sub>\<alpha> \<alpha>' G" 
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>'} Q" 
proof -
  have r1:"P \<subseteq> wp\<^sub>\<alpha> \<alpha>' Q" using assms(1) atomic_rule_def by fast
  have r2:"stable R P" using assms(1) atomic_rule_def by fast
  have r3:"stable R Q" using assms(1) atomic_rule_def by blast
  then show ?thesis using r1 r2 r3 assms(2) by auto
qed

lemma inter_subG:
  assumes "inter R G r" "G \<subseteq> G'"
  shows "inter R G' r" sorry

lemma stabile_G:
  assumes "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M" "stable G' P" "stable R P"
  shows "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} P" sorry


lemma help_inter:
 assumes "c \<mapsto>[\<alpha>',r] c'" 
        "(\<And>P R G Q. R,G \<turnstile> P {c} Q \<Longrightarrow> inter R G r 
              \<Longrightarrow> \<exists>M. R,G \<turnstile>\<^sub>A stabilise R P { \<alpha>'} M \<and> R,G \<turnstile> M {c'} Q)" 
         "R,G \<turnstile> P {\<triangle> c} P"
         "inter R G r"
  shows "\<exists>M. R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<and> R,G \<turnstile> M {\<triangle> c'} P"
proof -
(*  obtain \<alpha>'' where a0:"(\<triangle>c) \<mapsto>[\<alpha>'',r] (\<triangle>c')" using assms(1) by (rule lexecute.inter1) *)
  obtain G' Q' where g:"G \<subseteq> G'" "stable G' P" "stable R P" "R,G' \<turnstile> P {c} Q'"
    using assms(3) by (rule interrE)  
  have i:"inter R G' r " using assms(4) g(1) inter_subG by simp
  obtain M where m: "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M" "R,G' \<turnstile> M {c'} Q'"
    using assms(2)[OF g(4) i] by auto
  have a1:"R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} P" using stabile_G[OF m(1) g(2) g(3)] by auto
  have c1:"R,G' \<turnstile> P {c'} Q'" using m a1 sorry 
  have a2:"R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} P" using m(1) atomic_subG[OF a1 g(1)] by auto
  have c2:"R,G \<turnstile> P {\<triangle>c'} P" using g(1) g(2) g(3) c1 by (rule rules.interr) 
  then show ?thesis using a2 c2 by auto
qed


text \<open>Judgements are preserved across thread-local execution steps\<close>
lemma lexecute_ruleI [intro]:                
  assumes "R,G \<turnstile> P {c} Q" "c \<mapsto>[\<alpha>',r] c'" "inter R G r" 
  shows "\<exists>M. R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<and> R,G \<turnstile> M {c'} Q"
  using assms(2,1,3)
proof (induct arbitrary: P R G Q)
  case (act \<alpha>)
  then show ?case by clarsimp (meson atomic_rule_def nil rules.conseq order_refl)
next
  case (ino c\<^sub>1 \<alpha>' r c\<^sub>1' w c\<^sub>2)
  then obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} Q" by auto 
  then show ?case using ino(2)[OF m(1) ino(4)] m(2) by blast
next
  case (ooo c\<^sub>1 \<alpha>' r c\<^sub>1' \<alpha>'' c\<^sub>2 w)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>2} M'" "R,G \<turnstile> M' {c\<^sub>1} Q" using ooo(4) by (rule seqE)
  have i: "inter\<^sub>c w R G c\<^sub>2 \<alpha>'" "inter R G r" using ooo(5) by auto
  obtain M where m': "R,G \<turnstile>\<^sub>A stabilise R M' {\<alpha>'} M" "R,G \<turnstile> M {c\<^sub>1'} Q"
    using ooo(2)[OF m(2) i(2)] by auto
  have m'': "R,G \<turnstile> P {c\<^sub>2} stabilise R M'" using m(1) stabilise_supset[of M' R] by auto
  show ?case using reorder_prog[OF m'' m'(1)] i(1) m'(2) ooo(3) by (metis rules.seq)
next
  case (cap c \<alpha>' r c' s s')
  let ?R="capRely R" and ?G="capGuar G" and ?P="capPred s P" and ?Q="pushpredAll Q"
  have "?R,?G \<turnstile> ?P {c} ?Q" using cap(4) by (rule captureE)
  moreover have "inter ?R ?G r" using cap(5) by simp
  ultimately obtain M where m: "?R,?G \<turnstile>\<^sub>A stabilise ?R ?P {\<alpha>'} M" "?R,?G \<turnstile> M {c'} ?Q"
    using cap(2) by force
  have "R,G \<turnstile>\<^sub>A stabilise R P {popbasic s s' \<alpha>'} poppred' s' M"
    using helpa[OF m(1)[simplified stabilise_pushrel]] by simp
  moreover have "R,G \<turnstile> (poppred' s' M) {Capture s' c'} Q"
    using m(2) push_poppred_subset by blast
  ultimately show ?case by blast
next
  case (inter1 c\<^sub>1 \<alpha>' r c\<^sub>2)       (* in this case we want to set Q = P *)
  show ?case using help_inter  
    using inter1.hyps(1) inter1.hyps(2) inter1.prems(1) inter1.prems(2) by auto
qed
thm silent.cases[of a b]


(*
  have p:"?R,?G \<turnstile>\<^sub>A stabilise ?R ?P {\<alpha>'} P" "?R,?G \<turnstile> P {\<triangle>c\<^sub>2} ?Q" sorry
  have a:"R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} ?P" using atomic_subG[OF p(1) g0(1)] g0(2) 
    by (metis)
  have d:"(\<triangle>c\<^sub>1) \<mapsto>[\<alpha>',r] (\<triangle>c\<^sub>2)" sorry
  have g:"stable G P" sorry
  moreover have "R,G \<turnstile> P {\<triangle> c\<^sub>2} P" using inter_subG[OF p(2) g0(1)] g0(2) 
*)
(*
  then show ?case using help_inter by (meson semantics.inter1)


  obtain G' Q' where g0:"G \<subseteq> G'" "stable G' P" "stable R P" "R,G' \<turnstile> P {c\<^sub>1} Q'"
    using inter1(3) by (rule interrE)  
  then have a0:"R,G \<turnstile> P {\<triangle> c\<^sub>1} Q" using inter1.prems(1) by simp
  then have a1:"inter R G' r" using inter1(4) g0(1) sorry  
  then have a2:"(\<triangle>c\<^sub>1) \<mapsto>[\<alpha>',r] (\<triangle>c\<^sub>2)" using inter1(1) g0 by blast
  obtain M where "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<and> R,G' \<turnstile> M {c\<^sub>2} Q" using inter1(2)[OF g0(4)] a1 
  show ?case sorry 
qed
thm silent.cases[of a b]
*)


lemma test:
  assumes "pushpred s (stabilise R P) \<subseteq> pushpredAll Q" "x \<in> stabilise R P" 
  shows "x \<in> Q"
proof -
  have "push x s \<in> pushpred s (stabilise R P)" using assms by auto
  hence "push x s \<in> pushpredAll Q" using assms by auto
  then obtain x' s' where e: "push x s = push x' s'" "x' \<in> Q" unfolding pushpredAll_def by auto
  hence "x' = x" using push_inj by auto
  thus ?thesis using e by auto
qed

text \<open>Judgements are preserved across silent steps\<close>
lemma rewrite_ruleI [intro]:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<leadsto> c'"
  shows "R,G \<turnstile> P {c'} Q"
  using assms
proof (induct arbitrary: c' rule: rules.induct)
  case (seq R G P c\<^sub>1 Q c\<^sub>2 M)
  thus ?case by (cases rule: silentE, auto) (blast)+
next
  case (capture R G s P c Q)
  show ?case using capture
  proof (cases "Capture s c" c' rule: silentE)
    case 1
    then show ?case using capture by auto
  next
    case (15 k)
    hence "capRely R,capGuar G \<turnstile> capPred s P {Nil} pushpredAll Q"
      using capture(1) by simp
    hence t: "stabilise (capRely R) (capPred s P) \<subseteq> pushpredAll Q"
      using nilE2 by simp
    have "R,G \<turnstile> stabilise R P {Nil} stabilise R P"
      by (simp add: rules.rules.nil stable_stabilise)
    moreover have "P \<subseteq> stabilise R P"
      by (simp add: stabilise_supset)
    moreover have "stabilise R P \<subseteq> Q"
      using t test unfolding stabilise_pushrel by blast
    ultimately show ?thesis using 15(2) by blast
  next
    case (16 c'' c''' k)
    then show ?thesis using capture by auto
  qed auto
qed (cases rule: silentE, auto)+


text \<open>Judgements are preserved across global execution steps\<close>
lemma gexecute_ruleI [intro]:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<mapsto>[g] c'"
  shows "\<exists>\<alpha> M. \<alpha> \<in> obs c \<and> g = beh \<alpha> \<and> P \<subseteq> wp\<^sub>\<alpha> \<alpha> M \<and> guar\<^sub>\<alpha> \<alpha>  G \<and> R,G \<turnstile> M {c'} Q"
  using assms
proof (induct arbitrary: g c' rule: rules.induct)
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case using par(7)
  proof cases
    case (par1 c\<^sub>1')
    obtain M\<^sub>2 where m2: "P\<^sub>2 \<subseteq> M\<^sub>2" "stable R\<^sub>2 M\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2} Q\<^sub>2" using par
      by (meson stable_preE)
    obtain M\<^sub>1 \<alpha> where m1: "\<alpha> \<in> obs c\<^sub>1" "g = beh \<alpha>" "P\<^sub>1 \<subseteq> wp\<^sub>\<alpha> \<alpha> M\<^sub>1" "guar\<^sub>\<alpha> \<alpha> G\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1'} Q\<^sub>1" 
      using par1 par(2)[OF par1(2)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par1 m2 par by blast
    moreover have "P\<^sub>1 \<inter> P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<alpha> (M\<^sub>1 \<inter> M\<^sub>2)" 
      using m1(3,4) m2(1,2) par.hyps(6) unfolding guar_def wp_def stable_def
      by auto blast
    ultimately show ?thesis using m1(1,2,4) unfolding guar_def obs_par by blast
  next
    case (par2 c\<^sub>2')
    obtain M\<^sub>1 where m1: "P\<^sub>1 \<subseteq> M\<^sub>1" "stable R\<^sub>1 M\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1} Q\<^sub>1" using par
      by (meson stable_preE)
    obtain M\<^sub>2 \<alpha> where m2: "\<alpha> \<in> obs c\<^sub>2" "g = beh \<alpha>" "P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<alpha> M\<^sub>2" "guar\<^sub>\<alpha> \<alpha> G\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2'} Q\<^sub>2" 
      using par2 par(4)[OF par2(2)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par2 m1 par by blast
    moreover have "P\<^sub>1 \<inter> P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<alpha> (M\<^sub>1 \<inter> M\<^sub>2)" 
      using m1(1,2) m2(3,4) par.hyps(5) unfolding guar_def wp_def stable_def 
      by auto blast
    ultimately show ?thesis using m2(1,2,4) unfolding guar_def obs_par by blast
  qed 
next
  case (conseq R G P c Q P' R' G' Q')
  thus ?case by (smt Un_iff guar_def rules.conseq subset_iff)
next
  case (inv R G P c Q R' M')
  then obtain M \<alpha> where p: "\<alpha> \<in> obs c" "g = beh \<alpha>" "P \<subseteq> wp\<^sub>\<alpha> \<alpha> M" "guar\<^sub>\<alpha> \<alpha> G" "R,G \<turnstile> M {c'} Q" by metis
  hence "P \<inter> M' \<subseteq> wp\<^sub>\<alpha> \<alpha> (M \<inter> M')" using inv(3,4) by (auto simp: stable_def guar_def wp_def) blast
  thus ?case using rules.inv p(1,2,3,4,5) inv(3,4) by blast
next
  case (thread R G P c Q)
  then obtain r \<alpha>' c'' where e: "g = beh \<alpha>'" "c \<mapsto>[\<alpha>',r] c''" "c' = Thread c''" "\<alpha>' \<in> obs c" 
    using obs_act by (auto)
  then obtain M where "R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M" "R,G \<turnstile> M {c''} Q" "rif R G c''"
    using thread lexecute_ruleI[OF thread(1) e(2)] indep_stepI[OF thread(3) e(2)] by metis
  thus ?case using stabilise_supset[of P R] e unfolding atomic_rule_def 
    by (metis (no_types, lifting) dual_order.trans obs_thread rules.rules.thread)
qed auto

end

end