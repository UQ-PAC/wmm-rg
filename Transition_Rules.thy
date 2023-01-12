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
      then show ?case using Seq(3) outer using Seq.prems(2) by blast
    qed
  qed
qed auto 

section \<open>Transition Rules\<close>

lemma atomStep_Q:
  assumes "R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>'} M"  "stablePQ (stabilise R P) G' Q" "stable R Q" 
  shows "R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>'} Q" 
proof -
  have a0:"guar\<^sub>\<alpha> \<alpha>' G'" using assms(1) atomic_rule_def by blast
  have a00:"{(m, m'). m \<in> (vc \<alpha>') \<and> (m, m') \<in> (beh \<alpha>')} = (Id_on (vc \<alpha>') O (beh \<alpha>'))" by auto
  have a01:"(Id_on (vc \<alpha>') O (beh \<alpha>')) \<subseteq> G'" using a0 a00 guar_def by blast
  have a1:"(stabilise R P) \<subseteq> wp\<^sub>\<alpha> \<alpha>' M" using assms(1) atomic_rule_def by fast
  have a2:"stablePQ  (stabilise R P) (Id_on (vc \<alpha>') O (beh \<alpha>')) Q" using a01 assms(2) 
      stablePQ_subR by blast
  have a6:"(Id_on (stabilise R P)) O ((Id_on (vc \<alpha>') O (beh \<alpha>'))) \<subseteq> ((stabilise R P) \<times> Q)" 
    using a2 stablePQ_def by metis
  have a5:"(stabilise R P) \<subseteq> (vc \<alpha>')" using assms(1) atomic_rule_def wp_def 
    by (metis (no_types, lifting) le_inf_iff)
  have a3:"(stabilise R P) \<subseteq> wp\<^sub>\<alpha> \<alpha>' Q" using a2 a6 a5 wp_relcomp stablePQ_def wp_def
    by (metis (no_types, lifting))
  have a4:"stable R (stabilise R P)" using stable_stabilise by auto
  then show ?thesis using a0 a1 a2 a3 assms(3) by auto
qed


lemma stable_PI:
  assumes "R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>} P''" "P \<subseteq> I" "G' = G \<inter> (I \<Zinj> I)" "guar\<^sub>\<alpha> \<alpha> G'" "stable R I"
  shows "stablePQ (stabilise R P) G' I"
proof -
  have a0:"stablePQ I (I \<Zinj> I) I" using stablePQ_def impProd_def 
    by (smt (verit, best) Id_onE case_prodE mem_Collect_eq mem_Sigma_iff prod.simps(1) relcompE subsetI)
  have a1:"stablePQ P (I \<Zinj> I) I" using assms(2) a0 stablePQ_subP by blast
  have b0:"(Id_on (vc \<alpha>) O beh \<alpha>) \<subseteq> G'" using assms(4) guar_def by blast
  have b1:"{m'. \<forall>m. m \<in> (P\<inter>I) \<and> (m,m') \<in> beh \<alpha>} 
         \<subseteq> {m'. \<forall> m. m \<in> I \<and> (m,m') \<in> (I \<Zinj> I)}" using assms impProd_def by force
  have b2:"(stabilise R P) \<subseteq> (vc \<alpha>)" using assms(1) atomic_rule_def wp_def 
    by (metis (no_types, lifting) le_inf_iff)
  have b3:"{m'. \<forall> m. m \<in> I \<and> (m,m') \<in> (I \<Zinj> I)} \<subseteq> I" by auto
  have b5:"stabilise R P \<subseteq> stabilise R I" using assms(2) stabilise_def by (simp add: stabilise_mono) 
  have b6:"stabilise R P \<subseteq> I" using assms(5) stabilise_stable b5 by blast
  have b7:"stablePQ (stabilise R P) (I \<Zinj> I) I" using b6 a0 stablePQ_subP by blast
  show ?thesis using assms(3) b7 stablePQ_subR by blast
qed


(*
lemma interCom:
  assumes "c \<mapsto>[\<alpha>,r] c'" "P \<subseteq> I" "G \<subseteq>(I \<Zinj> I)" "stable R I" "R,G \<turnstile> P {c} UNIV" 
  shows "inter R G r" 
  using assms
proof (induct)
  case (act \<alpha>)
  then show ?case by auto
next
  case (ino c\<^sub>1 \<alpha>' r c\<^sub>1' w c\<^sub>2)
  then show ?case 
  proof -
    have a0:"R,G \<turnstile> P {c\<^sub>1} UNIV" using assms ino rules.conseq by auto
    then show ?case
      using ino.hyps(2)   ino.prems(1) ino.prems(2) ino.prems(3) by auto
  qed
next
  case (ooo c\<^sub>1 \<alpha>' r c\<^sub>1' \<alpha>'' c\<^sub>2 w) 
  then show ?case 
  proof -
    have a0:"R,G \<turnstile> I {c\<^sub>1} UNIV" using assms ooo sorry
    have a1:"R,G \<turnstile> P {c\<^sub>1} UNIV" using assms(2) rules.conseq a0 by simp
    have a2:"inter R G r" using a1 ooo.hyps(2) ooo.prems by auto
    have a3:"inter\<^sub>c w R G c\<^sub>2 \<alpha>'" sorry
    then show ?case
      using ooo.prems ooo.hyps a3 a2 by simp
  qed
next
  case (cap c \<alpha>' r c' s s')
  then show ?case 
  proof -
    have a1:"R,G \<turnstile> P {c} UNIV" using assms sorry
    have a2:"inter R G r" using a1 cap.hyps(2) cap.prems by auto
    have a3:"inter (pushrelSame R) (pushrelAll G) r" sorry
    then show ?case
      using cap.prems cap.hyps a3 a2 by simp
  qed
qed 
*)
(*-----------------------------------------------------*)


lemma obs_seq2:
  assumes "\<alpha> \<in> obs(c2)"
  shows "\<alpha> \<in> obs(c1 ;\<^sub>w c2)" using assms obs_seq3 sorry


lemma obs_guar:
  assumes "R,G \<turnstile> P {Basic x ;\<^sub>w c\<^sub>1 } Q'" "inter\<^sub>c w R G (Basic x) \<alpha>" "c\<^sub>1 \<mapsto>[\<alpha>,r] c\<^sub>1'" 
          "\<alpha> \<in> obs(Basic x ;\<^sub>w c\<^sub>1)"
  shows "guar\<^sub>\<alpha> \<alpha> G" using assms 
proof -
  show ?thesis sorry
qed


lemma help_interAlpha:
  assumes "w \<alpha>' x \<alpha> \<longrightarrow> inter\<^sub>\<alpha> R G \<alpha>' x \<alpha>" "P \<subseteq> I" "G' = G \<inter> (I \<Zinj> I)" 
          "R,G' \<turnstile> P {Basic x ;\<^sub>w c\<^sub>1 } Q'" "inter\<^sub>c w R G (Basic x) \<alpha>" "c\<^sub>1 \<mapsto>[\<alpha>,r] c\<^sub>1'"
  shows "w \<alpha>' x \<alpha> \<longrightarrow> inter\<^sub>\<alpha> R G' \<alpha>' x \<alpha>" 
proof -
  obtain M where m:"R,G' \<turnstile> P {Basic x} M" using assms(4) seqE by metis
  have a0:"guar\<^sub>\<alpha> x G'" using m atomic_rule_def by blast
  have b1:"\<alpha> \<in> obs(Basic x ;\<^sub>w c\<^sub>1)" using assms(6) obs_act obs_seq2 by auto
  have b2:"inter\<^sub>c w R G' (Basic x) \<alpha>" using assms(3,5) sorry
  have b0:"guar\<^sub>\<alpha> \<alpha> G'" using assms(4,6) b1 b2 obs_guar by auto
  have c1:"w \<alpha>' x \<alpha> \<Longrightarrow> Basic x ;\<^sub>w c\<^sub>1 \<mapsto>[\<alpha>',(Reorder \<alpha> w (Basic x)) # r] Basic x ;\<^sub>w c\<^sub>1'" 
    using assms(6) obs_def lexecute.intros(3) by simp
  have c0:"w \<alpha>' x \<alpha> \<Longrightarrow> guar\<^sub>\<alpha> \<alpha>' G'" using assms(4) c1 guar_com by auto  

  have a1:"w \<alpha>' x \<alpha> \<Longrightarrow> inter\<^sub>\<alpha> R G \<alpha>' x \<alpha>" using assms(1) by auto
  fix P' M' Q' 
  have a2:"w \<alpha>' x \<alpha> \<Longrightarrow> R,G \<turnstile>\<^sub>A P' {x} M' \<Longrightarrow> R,G \<turnstile>\<^sub>A M' {\<alpha>} Q' \<Longrightarrow>
            (\<exists>M''. R,G \<turnstile>\<^sub>A P' {\<alpha>'} M'' \<and> R,G \<turnstile>\<^sub>A M'' {x} Q')" using a1 inter\<^sub>\<alpha>_def by auto
  have d1:"R,G \<turnstile>\<^sub>A P' {x} M \<Longrightarrow> R,G' \<turnstile>\<^sub>A P' {x} M" using atomic_subG a0 by metis
  have d2:"R,G \<turnstile>\<^sub>A M' {\<alpha>} Q' \<Longrightarrow> R,G' \<turnstile>\<^sub>A M' {\<alpha>} Q'" using atomic_subG b0 by metis
  have d3:"w \<alpha>' x \<alpha> \<Longrightarrow> R,G \<turnstile>\<^sub>A P' {\<alpha>'} M'' \<Longrightarrow> R,G' \<turnstile>\<^sub>A P' {\<alpha>'} M''" using atomic_subG c0 by metis
  have d4:"R,G \<turnstile>\<^sub>A M'' {x} Q' \<Longrightarrow> R,G' \<turnstile>\<^sub>A M'' {x} Q'" using atomic_subG a0 by metis

  have a4:"w \<alpha>' x \<alpha> \<Longrightarrow> R,G' \<turnstile>\<^sub>A P' {x} M' \<Longrightarrow> R,G' \<turnstile>\<^sub>A M' {\<alpha>} Q' \<Longrightarrow>
            (\<exists>M''. R,G' \<turnstile>\<^sub>A P' {\<alpha>'} M'' \<and> R,G' \<turnstile>\<^sub>A M'' {x} Q')" using a2 d1 d2 d3 d4 
    by (metis Int_lower1 a0 assms(3) atomic_subG atomic_supG c0) 
  have a5:"w \<alpha>' x \<alpha> \<Longrightarrow> inter\<^sub>\<alpha> R G' \<alpha>' x \<alpha>" using inter\<^sub>\<alpha>_def 
    by (smt (verit, best) Int_lower1 a0 a1 assms(3) atomic_subG atomic_supG c0)
  thus ?thesis by auto
qed



lemma help_interC:
  assumes "P \<subseteq> I" "G' = G \<inter> (I \<Zinj> I)" "R,G' \<turnstile> P {c\<^sub>2 ;\<^sub>w c\<^sub>1} Q'" "inter\<^sub>c w R G c\<^sub>2 \<alpha>" "c\<^sub>1 \<mapsto>[\<alpha>,r] c\<^sub>1'"
  shows "inter\<^sub>c w R G' c\<^sub>2 \<alpha>" 
  using assms
proof (induct c\<^sub>2 arbitrary: w \<alpha> P Q' c\<^sub>1)
  case (Basic x)
  then show ?case 
  proof -
    have b0:" (\<forall>\<alpha>'. w \<alpha>' x \<alpha> \<longrightarrow> inter\<^sub>\<alpha> R G \<alpha>' x \<alpha>)" using Basic(4) by auto
    have b1:" (\<forall>\<alpha>'. w \<alpha>' x \<alpha> \<longrightarrow> inter\<^sub>\<alpha> R G' \<alpha>' x \<alpha>)" using help_interAlpha b0 Basic by auto
    thus ?case using b1 by auto  
  qed
next
  case (Seq c1 w' c2)
  then show ?case using Seq
  proof -
    obtain M where a00:"R,G' \<turnstile> P {c1 ;\<^sub>w' c2} M" "R,G' \<turnstile> M {c\<^sub>1} Q'"  
        using Seq(5) apply (rule seqE) by auto
    obtain M' where a02:"R,G' \<turnstile> M' {c2} M" using a00(1) apply (rule seqE) by auto
    obtain c\<^sub>1 Q'' where a03:"R,G' \<turnstile> M' {c2 ;\<^sub>w c\<^sub>1} Q''" using a02 a00(2) rules.seq
      by (meson Seq.prems(3) rules.seqE)
    fix \<alpha>'
    have  a0:"\<forall> \<alpha>'. \<alpha>' < c2 <\<^sub>w \<alpha> \<longrightarrow> (inter\<^sub>c w R G c1 \<alpha>' \<and> inter\<^sub>c w R G c2 \<alpha>)" 
      using Seq(6) unfolding inter\<^sub>c.simps by auto
    have a1:"\<alpha>' < c2 <\<^sub>w \<alpha> \<Longrightarrow> inter\<^sub>c w R G c1 \<alpha>'" using a0 by blast
    have a2:"inter\<^sub>c w R G c1 \<alpha>' \<Longrightarrow> inter\<^sub>c w R G' c1 \<alpha>'" using Seq(3,4) a00 Seq.hyps(1) sorry (*by blast*)
    have a3:"\<alpha>' < c2 <\<^sub>w \<alpha> \<Longrightarrow> inter\<^sub>c w R G' c1 \<alpha>'" using a1 a2 by auto
    have b1:"\<alpha>' < c2 <\<^sub>w \<alpha> \<Longrightarrow> inter\<^sub>c w R G c2 \<alpha>" using a0 by blast
    have b2:"inter\<^sub>c w R G c2 \<alpha> \<Longrightarrow> inter\<^sub>c w R G' c2 \<alpha>" using Seq(3,4) a03 Seq.hyps(2) sorry (*by blast*)
    have b3:"\<alpha>' < c2 <\<^sub>w \<alpha> \<Longrightarrow> inter\<^sub>c w R G' c2 \<alpha>" using b1 b2 by auto
    have c1:"\<alpha>' < c2 <\<^sub>w \<alpha> \<Longrightarrow> (inter\<^sub>c w R G' c1 \<alpha>' \<and> inter\<^sub>c w R G' c2 \<alpha>)" using a3 b3 by simp
     then show ?thesis sorry
     (*  by (meson Seq.hyps(1) Seq.prems(1) a0 a00(1) assms(2) b2 inter\<^sub>c.simps(2) rules.seqE seq) *)
  qed
qed auto


lemma help_interSub:
  assumes "inter R G r" "P \<subseteq> I" "G' = G \<inter> (I \<Zinj> I)" "R,G' \<turnstile> P {c} Q'"
  shows "inter R G' r" sorry


lemma inner_inter:
  assumes "c \<mapsto>[\<alpha>',r] c'" "inter R G ( r)"  "P \<subseteq> I" "G' = G \<inter> (I \<Zinj> I)" "R,G' \<turnstile> P {c} Q'"
  shows "inter R G' (r)" 
  using assms
proof (induct arbitrary: P Q')
  case (act \<alpha>)
  then show ?case by auto
next
  case (ino c\<^sub>1 \<alpha>' r c\<^sub>1' w c\<^sub>2)
  then show ?case by auto
next
  case (ooo c\<^sub>1 \<alpha> r c\<^sub>1' \<alpha>'' c\<^sub>2 w)
  have a3:"R,G' \<turnstile> P {c\<^sub>2 ;\<^sub>w c\<^sub>1} Q'" using ooo assms(5) by auto
  have a0:"inter\<^sub>c w R G c\<^sub>2 \<alpha>" "inter R G r" using ooo by auto
  have a5:"inter\<^sub>c w R G' c\<^sub>2 \<alpha>" using help_interC a0(1) ooo by auto
  have a6:"inter R G' r" using help_interSub a0(2) ooo by auto
  thus ?case using a5 a6 by auto
next
  case (cap c \<alpha>' r c' s s')
  then show ?case apply simp
    apply (drule captureE)
    sorry
next
  case (inter1 c \<alpha>' r c')
  then show ?case by (auto elim!: interrE)
qed


lemma help_inter_try:
 assumes "c \<mapsto>[\<alpha>',r] c'" 
        "(\<And>P R G Q. R,G \<turnstile> P {c} Q \<Longrightarrow> inter R G r 
              \<Longrightarrow> \<exists>M. R,G \<turnstile>\<^sub>A stabilise R P { \<alpha>'} M \<and> R,G \<turnstile> M {c'} Q)" 
         "R,G \<turnstile> P {(\<triangle>c)} I" 
         "inter R G r"
  shows "\<exists>M. R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<and> R,G \<turnstile> M {\<triangle> c'} I"
proof -
  obtain G' Q' where g:
    "P \<subseteq> I"  
    "G' = G \<inter> (I \<Zinj> I)" 
    "stable R I"  
    "R,G' \<turnstile> P {c} Q'" 
    using assms(3) by (rule interrE) 
  have i1:"inter R G' r"  using assms(1,4) g(1,2,4) inner_inter by auto
  obtain M where m: "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M" "R,G' \<turnstile> M {c'} Q'" using assms(2)[OF g(4) i1] by auto
  obtain P'' where p: "P''=stabilise R (sp \<alpha>' (stabilise R P))" "R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>'} P''" "P'' \<subseteq> M"
    using m(1) atomic_spI by metis

  have a2:"R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} P''" using p(2) g(1,2) by blast
  have s1:"guar\<^sub>\<alpha> \<alpha>' G'" using m(1) atomic_rule_def by blast
  have s2:"stablePQ (stabilise R P) G' I" using p(2) g(1) g(2) s1 g(3) stable_PI by blast
  have s3:"R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>'} M" using m(1) by auto
  have s4:"R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>'} I" using s3 s2 g(3) atomStep_Q by blast
  have s5:"P'' \<subseteq> I" using s4 atomic_spI(2) p by metis
  have s6:"R,G' \<turnstile> P'' {c'} Q'" using m(2) p(3) apply (rule rules.conseq) by auto

  have p3:"R,G \<turnstile> P'' {\<triangle>c'} I" using s5 g(2,3) s6 by (rule rules.interr) 

  show ?thesis using a2 p3 by auto
qed

(* old version with additional prereq:
lemma help_inter:
 assumes "c \<mapsto>[\<alpha>',r] c'" 
        "(\<And>P R G Q. R,G \<turnstile> P {c} Q \<Longrightarrow> inter R G r 
              \<Longrightarrow> \<exists>M. R,G \<turnstile>\<^sub>A stabilise R P { \<alpha>'} M \<and> R,G \<turnstile> M {c'} Q)" 
         "R,G \<turnstile> P {(\<triangle>c)} I"
  shows "\<exists>M. R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M \<and> R,G \<turnstile> M {\<triangle> c'} I"
proof -
  obtain G' Q' where g:
    "P \<subseteq> I" "G' = G \<inter> (I \<Zinj> I)" "stable R I"  "R,G' \<turnstile> P {c} Q'" "rif R G' c" 
    using assms(3) by (rule interrE) 
  have i1:"inter R G' r"  using assms(1) g(5) interference.indep_stepI by blast
  have i2:"rif R G' c'" using assms(1) g(5) interference.indep_stepI rif_def by blast
  obtain M where m: "R,G' \<turnstile>\<^sub>A stabilise R P {\<alpha>'} M" "R,G' \<turnstile> M {c'} Q'" using assms(2)[OF g(4) i1] by auto
  obtain P'' where p: "P''=stabilise R (sp \<alpha>' (stabilise R P))" "R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>'} P''" "P'' \<subseteq> M"
    using m(1) atomic_spI by metis

  have a2:"R,G \<turnstile>\<^sub>A stabilise R P {\<alpha>'} P''" using p(2) g(1,2) by blast
  have s1:"guar\<^sub>\<alpha> \<alpha>' G'" using m(1) atomic_rule_def by blast
  have s2:"stablePQ (stabilise R P) G' I" using p(2) g(1) g(2) s1 g(3) stable_PI by blast
  have s3:"R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>'} M" using m(1) by auto
  have s4:"R,G' \<turnstile>\<^sub>A (stabilise R P) {\<alpha>'} I" using s3 s2 g(3) atomStep_Q by blast
  have s5:"P'' \<subseteq> I" using s4 atomic_spI(2) p by metis
  have s6:"R,G' \<turnstile> P'' {c'} Q'" using m(2) p(3) apply (rule rules.conseq) by auto

  have p3:"R,G \<turnstile> P'' {\<triangle>c'} I" using s5 g(2,3) s6 i2 by (rule rules.interr) 

  show ?thesis using a2 p3 by auto
qed
*)


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
  then show ?case using ino(2)[OF m(1) ino(4)] m(2) using ino.prems(1) by blast
next
  case (ooo c\<^sub>1 \<alpha>' r c\<^sub>1' \<alpha>'' c\<^sub>2 w)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>2} M'" "R,G \<turnstile> M' {c\<^sub>1} Q" using ooo(4) by (rule seqE)
  have i: "inter\<^sub>c w R G c\<^sub>2 \<alpha>'" "inter R G r" using ooo(5) by auto
  obtain M where m': "R,G \<turnstile>\<^sub>A stabilise R M' {\<alpha>'} M" "R,G \<turnstile> M {c\<^sub>1'} Q"
    using ooo(2)[OF m(2) i(2)] by auto
  have m'': "R,G \<turnstile> P {c\<^sub>2} stabilise R M'" using m(1) stabilise_supset[of M' R] by auto
  show ?case using reorder_prog[OF m'' m'(1)] i(1) m'(2) ooo(3) 
    by (metis (mono_tags, lifting) ooo.prems(1) seq seqE)
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
  show ?case using help_inter_try using inter1.hyps(1,2) inter1.prems(1,2) by auto
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
