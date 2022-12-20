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

(* only used if we want to show "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} P" in help_inter*)
(* version that uses "stable ?A P" *) 
lemma stable_G:
  assumes "R,G' \<turnstile>\<^sub>A P {\<alpha>'} M"  "stable (Id_on (vc \<alpha>') O (beh \<alpha>')) P" "stable R P"
  shows "R,G' \<turnstile>\<^sub>A P {\<alpha>'} P" 
proof -
  let ?A="(Id_on (vc \<alpha>') O (beh \<alpha>'))"
  have a2:"guar\<^sub>\<alpha> \<alpha>' G'" using assms(1) atomic_rule_def by blast
  have a4:"P \<subseteq> wp\<^sub>\<alpha> \<alpha>' M" using assms(1) atomic_rule_def by fast
  have s1:"stablePQ P ?A P" using assms(2) stable_rel2 stablePQ_def by fast
  have s2:"P \<subseteq> (vc \<alpha>')" using a4 wp_def by fast
  have a1:"P \<subseteq> wp\<^sub>\<alpha> \<alpha>' P" using assms(2) s1 s2 stablePQ_def wp_relcomp by metis
  then show ?thesis using a1 a2 assms(3) by auto
qed


(* version that uses "stable G' P" *)
lemma stable_G2:
  assumes "R,G' \<turnstile>\<^sub>A P {\<alpha>'} M"  "stable G' P" "stable R P"
  shows "R,G' \<turnstile>\<^sub>A P {\<alpha>'} P" 
proof -
  let ?A="(Id_on (vc \<alpha>') O (beh \<alpha>'))"
  have a2:"guar\<^sub>\<alpha> \<alpha>' G'" using assms(1) atomic_rule_def by blast
  have a3:"?A \<subseteq> G'"using a2 guar_def by blast
  have a4:"P \<subseteq> wp\<^sub>\<alpha> \<alpha>' M" using assms(1) atomic_rule_def by fast
  have s2:"P \<subseteq> (vc \<alpha>')" using a4 wp_def by fast
  have s3:"stablePQ P G' P" using assms(2) stablePQ_def stable_rel2 by fast 
  have s1:"stablePQ P ?A P" using s3 a3 stablePQ_subR by blast 
  have a1:"P \<subseteq> wp\<^sub>\<alpha> \<alpha>' P" using s2 s3 stablePQ_def s1 wp_relcomp by metis 
  then show ?thesis using a1 a2 assms(3) by auto
qed


(*
lemma stable_G2:
  assumes "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M"  "stable G' (stabilise R P)" 
  shows "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} stabilise R P"
proof -
  have a0:"stable R (stabilise R P)" using stable_stabilise by auto
  then show ?thesis using assms a0 stable_G 
    by (simp add: atomic_stab_guar)
qed
*)


lemma stable_G3:
  assumes "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M"  "stablePQ (stabilise R P) G' Q" "stable R Q"
  shows "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} Q" 
proof -
  have a0:"guar\<^sub>\<alpha> \<alpha>' G'" using assms(1) atomic_rule_def by blast
  have a00:"{(m, m'). m \<in> (vc \<alpha>') \<and> (m, m') \<in> (beh \<alpha>')} = (Id_on (vc \<alpha>') O (beh \<alpha>'))" by auto
  have a01:"(Id_on (vc \<alpha>') O (beh \<alpha>')) \<subseteq> G'" using a0 a00 guar_def by blast
  have a1:"stabilise R P \<subseteq> wp\<^sub>\<alpha> \<alpha>' M" using assms(1) atomic_rule_def by fast
  have a2:"stablePQ (stabilise R P) (Id_on (vc \<alpha>') O (beh \<alpha>')) Q" using a01 assms(2) 
      stablePQ_subR by blast
  have a6:"(Id_on (stabilise R P)) O ((Id_on (vc \<alpha>') O (beh \<alpha>'))) \<subseteq> ((stabilise R P) \<times> Q)" 
    using a2 stablePQ_def by metis
  have a5:"stabilise R P \<subseteq> (vc \<alpha>')" using assms(1) atomic_rule_def wp_def 
    by (metis (no_types, lifting) le_inf_iff)
  have a3:"(stabilise R P) \<subseteq> wp\<^sub>\<alpha> \<alpha>' Q" using a2 a6 a5 wp_relcomp stablePQ_def wp_def
    by (metis (no_types, lifting))
  have a4:"stable R (stabilise R P)" using stable_stabilise by auto
  then show ?thesis using a0 a1 a2 a3 assms(3) by auto
qed
 

lemma inter_stable:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} M" "R,G \<turnstile> M {c'} Q" "stablePQ P G Q"
  shows "stablePQ M G Q"
proof -
  let ?A="(Id_on (vc \<alpha>) O (beh \<alpha>))"
  have a0:"guar\<^sub>\<alpha> \<alpha> G" using assms(1) atomic_rule_def by blast
  have a1:"?A \<subseteq> G" using a0 guar_def by blast
  have a2:"G O G \<subseteq> G\<^sup>*" using relcompE rtrancl_def by auto
  have a1:"?A O G \<subseteq> G O G" using a1 relcomp_mono by auto
  have b0:"P \<subseteq> wp\<^sub>\<alpha> \<alpha> M" using assms(1) atomic_rule_def by fast 
  have b1:"stablePQ P ?A M" using b0 relcomp_wp stablePQ_def by fast
  
  

lemma help_inter:
 assumes "c \<mapsto>[\<alpha>',r] c'" 
        "(\<And>P R G Q. R,G \<turnstile> P {c} Q \<Longrightarrow> inter R G r 
              \<Longrightarrow> \<exists>M. R,G \<turnstile>\<^sub>A stabilise R P { \<alpha>'} M \<and> R,G \<turnstile> M {c'} Q)" 
         "R,G \<turnstile> P {(\<triangle>c)} Q"
  shows "\<exists>M. R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<and> R,G \<turnstile> M {\<triangle> c'} Q"
proof -
  obtain G' Q' where g:
        "P \<subseteq> Q"  "G' \<subseteq> G"  "stable G' Q"  "stable R Q"  "R,G' \<turnstile> P {c} Q'" "rif R G' c"  
                            "stablePQ P G' Q" "stable R P"
    using assms(3) by (rule interrE)  
  have i1:"inter R G' r"  using assms(1) g(6) interference.indep_stepI by blast
  have i2:"rif R G' c'" using assms(1) g(6) interference.indep_stepI rif_def by blast
  have p1:"P = stabilise R P" using g(8) stabilise_stable by auto
  obtain M where m: "R,G' \<turnstile>\<^sub>A P {\<alpha>'} M" "R,G' \<turnstile> M {c'} Q'" 
    using p1 assms(2)[OF g(5) i1] by auto

  obtain P'' where p: "P''=stabilise R (sp \<alpha>' P)" "R,G' \<turnstile>\<^sub>A P {\<alpha>'} P''" "P'' \<subseteq> M"
    using m(1) atomic_spI by metis

  have a2:"R,G \<turnstile>\<^sub>A P {\<alpha>'} P''" using p(2) g(1,2) by blast
  have s1:"guar\<^sub>\<alpha> \<alpha>' G'" using m(1) atomic_rule_def by blast
  have s4:"R,G' \<turnstile>\<^sub>A P {\<alpha>'} Q" using p1 m(1) g(7,4) stable_G3 by metis
  have s5:"P'' \<subseteq> Q" using p1 s4 atomic_spI(2) p by metis
  have s6:"R,G' \<turnstile> P'' {c'} Q'" using m(2) p(3) apply (rule rules.conseq) by auto
(*  have s9:"stable (Id_on (vc \<alpha>') O (beh \<alpha>')) P" sorry
  have s10: "R,G' \<turnstile>\<^sub>A P {\<alpha>'} P" using p1 m(1) s9 g(8) stable_G by metis
  have s11:"P'' \<subseteq> P" using s10 p(1,2) g(8) atomic_spI(2) stabilise_stable by blast
  have s7:"stablePQ P'' G' Q" using s11 g(7) stablePQ_subP by blast
*)
  have s7:"stablePQ P'' G' Q" sorry
  have s8:"stable R P''" using stable_stabilise p(1) by auto
  have p3:"R,G \<turnstile> P'' {\<triangle>c'} Q" using s5 g(2,3,4) s6 i2 s7 s8 by (rule rules.interr) 


  then show ?thesis using p1 a2 p3 by auto 
qed

(* All my pains go away if we assume P=Q in the rule interr *)

lemma help_inter2:
 assumes "c \<mapsto>[\<alpha>',r] c'" 
        "(\<And>P R G Q. R,G \<turnstile> P {c} Q \<Longrightarrow> inter R G r 
              \<Longrightarrow> \<exists>M. R,G \<turnstile>\<^sub>A stabilise R P { \<alpha>'} M \<and> R,G \<turnstile> M {c'} Q)" 
         "R,G \<turnstile> P {(\<triangle>c)} Q"
  shows "\<exists>M. R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<and> R,G \<turnstile> M {\<triangle> c'} Q"
proof -
  obtain G' Q' where g:
        "P = Q"  "G' \<subseteq> G"  "stable G' Q"  "stable R Q"  "R,G' \<turnstile> P {c} Q'" "rif R G' c"  
                            "stablePQ P G' Q" "stable R P"
    using assms(3) sorry 
  have i1:"inter R G' r"  using assms(1) g(6) interference.indep_stepI by blast
  have i2:"rif R G' c'" using assms(1) g(6) interference.indep_stepI rif_def by blast
  have p1:"P = stabilise R P" using g(8) stabilise_stable by auto
  obtain M where m: "R,G' \<turnstile>\<^sub>A P {\<alpha>'} M" "R,G' \<turnstile> M {c'} Q'" 
    using p1 assms(2)[OF g(5) i1] by auto

  obtain P'' where p: "P''=stabilise R (sp \<alpha>' P)" "R,G' \<turnstile>\<^sub>A P {\<alpha>'} P''" "P'' \<subseteq> M"
    using m(1) atomic_spI by metis

  have a2:"R,G \<turnstile>\<^sub>A P {\<alpha>'} P''" using p(2) g(1,2) by blast
  have s1:"guar\<^sub>\<alpha> \<alpha>' G'" using m(1) atomic_rule_def by blast
  have s4:"R,G' \<turnstile>\<^sub>A P {\<alpha>'} Q" using p1 m(1) g(7,4) stable_G3 by metis
  have s6:"R,G' \<turnstile> P'' {c'} Q'" using m(2) p(3) apply (rule rules.conseq) by auto
  have s9:"stable G' P" using g(1,3) by auto
  have s10: "R,G' \<turnstile>\<^sub>A P {\<alpha>'} P" using p1 m(1) s9 g(8) stable_G2  by metis
  have s11:"P'' \<subseteq> P" using s10 p(1,2) g(8) atomic_spI(2) stabilise_stable by blast
  have s7:"stablePQ P'' G' Q" using s11 g(7) stablePQ_subP by blast
  have s8:"stable R P''" using stable_stabilise p(1) by auto
  have s5:"P'' \<subseteq> Q" using p1 s4 atomic_spI(2) p by metis  (* this needs to be P''=Q *)
  have p3:"R,G \<turnstile> P'' {\<triangle>c'} Q" using s5 g(2,3,4) s6 i2 s7 s8 by (rule rules.interr) 

  then show ?thesis using p1 a2 p3 by auto 
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
  case (inter1 c\<^sub>1 \<alpha>' r c\<^sub>2)    
  show ?case using help_inter using inter1.hyps(1,2) inter1.prems(1,2) by auto
qed
thm silent.cases[of a b]


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

(* interesting fun facts:
  have b6:"{m. (\<exists>m'.(m,m') \<in> beh \<alpha> \<and> m' \<in> M)} \<subseteq> {m. (\<exists> m'.(m,m') \<in> beh \<alpha> \<longrightarrow> m' \<in> M)}" 
    by blast
  have b6:"{m. (\<exists>m'.(m,m') \<in> beh \<alpha> \<and> m' \<in> M)} \<supseteq> {m. (\<forall> m'.(m,m') \<in> beh \<alpha> \<and> m' \<in> M)}" 
    by blast
  have b6:"{m. (\<exists>m'.(m,m') \<in> beh \<alpha> \<longrightarrow> m' \<in> M)} \<supseteq> {m. (\<forall> m'.(m,m') \<in> beh \<alpha> \<longrightarrow> m' \<in> M)}" 
    by blast

  stable G Q \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> stable G P does not hold

  have b9:"{m. (\<forall> m'.(m,m') \<in> beh \<alpha> \<longrightarrow> m' \<in> M)} = {m. (\<forall> m'.(m,m') \<notin> beh \<alpha> \<or> m' \<in> M)}"
    by blast
  have b10:"{m. (\<forall> m'.(m,m') \<notin> beh \<alpha> \<or> m' \<in> M)} = 
              {m. (\<forall> m'.(m,m') \<notin> beh \<alpha> \<or> ((m,m') \<in> beh \<alpha> \<and> m' \<in> M))}" by blast
  have b11:"{m. (\<forall> m'.(m,m') \<notin> beh \<alpha> \<or> ((m,m') \<in> beh \<alpha> \<and> m' \<in> M))} \<supseteq>
                 {m. (\<forall> m'.(m,m') \<in> beh \<alpha> \<and> m' \<in> M)}" by blast    
  have b12:"{m. (\<forall> m'.(m,m') \<in> beh \<alpha> \<and> m' \<in> M)} \<subseteq> {m. (\<exists> m'.(m,m') \<in> beh \<alpha> \<and> m' \<in> M)}" by blast


  let ?AV="{(m,m'). m \<in> vc \<alpha> \<and> (m,m') \<in> beh \<alpha>}" and 
      ?VA="{m. m \<in> vc \<alpha>}" and 
      ?AM="{m. (\<forall> m'.(m,m') \<in> beh \<alpha> \<longrightarrow> m' \<in> M)}" and
       ?A="{m. \<exists>m'.(m,m') \<in> beh \<alpha>}"
  have b0:"P \<subseteq> ?VA" using assms(3) by (simp add: wp_def)
  have b1:"P \<subseteq> ?AM" using assms(3) by (simp add: wp_def)
  have b2:"?AV = Id_on (vc \<alpha>) O (beh \<alpha>)" by blast
  have b3:"(beh \<alpha>) O Id_on M = {(m,m'). (m,m') \<in> beh \<alpha> \<and> m' \<in> M}" by blast
  have b4:"Domain ((beh \<alpha>) O Id_on M) = {m. (\<exists>m'.(m,m') \<in> beh \<alpha> \<and> m' \<in> M)}" by blast 
  have b5:"(Id_on (vc \<alpha>) O (beh \<alpha>)) \<subseteq> G" using assms(1) guar\<^sub>\<alpha>_rel by blast
  have b6:"(Id_on Q) O G \<subseteq> (Q \<times> Q)" using assms(2) unfolding stable_def by blast
  have b7:"(Id_on Q) O (Id_on (vc \<alpha>) O (beh \<alpha>)) \<subseteq> (Q \<times> Q)" using b6 b5 by blast
  have b8:"(Id_on P) O (Id_on (vc \<alpha>) O (beh \<alpha>)) \<subseteq> (Q \<times> Q)" using b7 assms(4) by blast


*)
