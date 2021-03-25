theory Soundness
  imports Global_Rules
begin

chapter \<open>Soundness\<close>

locale soundness = global_rules 

context soundness
begin

section \<open>Helper Definitions\<close>

text \<open>Strongest postcondition across arbitrary environment steps, 
      used to compute some new intermediate states for reasoning\<close>
definition sp :: "('a,'b) basic \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "sp \<alpha> R P \<equiv> {m. \<exists>m' m''. m' \<in> P \<and> (m',m'') \<in> beh \<alpha> \<and> (m'',m) \<in> (R\<^sup>* ) }"

section \<open>Reordering Rules\<close> 

text \<open>
  Reorder the judgements of two reorderable instructions given a suitable interference property.
  The precondition P and postcondition Q are preserved.
\<close>
lemma reorder_action:
  assumes "R,G \<turnstile>\<^sub>A P {\<beta>} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "inter\<^sub>\<alpha> R G \<beta> \<alpha>"
  obtains M' where "R,G \<turnstile>\<^sub>A P {\<alpha>\<langle>tag \<beta>\<rangle>} M'" "R,G \<turnstile>\<^sub>A M' {\<beta>} Q"
proof -
  \<comment> \<open>Nominate the strongest-postcondition of \<alpha> from P as the state between \<alpha> and \<beta>\<close>
  let ?M="sp \<alpha>\<langle>tag \<beta>\<rangle> R P"

  \<comment> \<open>Establish stability for P, Q and the new intermediate state, in addition to guarantees\<close>
  have stablePQ: "stable R P" "stable R Q" "guar \<alpha> G" "guar \<beta> G"
    using assms(1,2) by (auto simp: atomic_rule_def)
  have stableM: "stable R ?M"  unfolding stable_def sp_def by force

  \<comment> \<open>Extract order independence properties\<close> 
  have ref: "Env R ; Basic \<beta> ; Env R ; Basic \<alpha> \<sqsubseteq> Env R ; Basic \<alpha>\<langle>tag \<beta>\<rangle> ; Env R ; Basic \<beta>"
    using assms(3) by (auto simp: inter\<^sub>\<alpha>_def)
  have g: "guar \<alpha>\<langle>tag \<beta>\<rangle> G" using assms(3) by (auto simp: inter\<^sub>\<alpha>_def)

  \<comment> \<open>Show transition from P to Q is independent of order\<close>
  have p: "P \<subseteq> wp\<^sub>\<alpha> \<beta> M" "M \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "M \<subseteq> wp UNIV ( (R\<^sup>* )) M" "P \<subseteq>  wp UNIV ( (R\<^sup>* )) P" "Q \<subseteq>  wp UNIV ( (R\<^sup>* )) Q"
    using assms(1,2)  unfolding atomic_rule_def by (auto intro!: stable_wp\<^sub>tI)
  hence "P \<subseteq>  wp UNIV ( (R\<^sup>* )) (wp\<^sub>\<alpha> \<beta> ( wp UNIV ( (R\<^sup>* )) (wp\<^sub>\<alpha> \<alpha> Q)))" unfolding wp_def by blast
  hence exec: "P \<subseteq>  wp UNIV ( (R\<^sup>* )) (wp\<^sub>\<alpha> \<alpha>\<langle>tag \<beta>\<rangle> ( wp UNIV ( (R\<^sup>* )) (wp\<^sub>\<alpha> \<beta> Q)))" using ref by (auto simp: refine_def)
  hence vc: "P \<subseteq> vc \<alpha>\<langle>tag \<beta>\<rangle>" by (auto simp: wp_def)

  \<comment> \<open>Establish the late judgement over \<beta>\<close>
  have "R,G \<turnstile>\<^sub>A ?M {\<beta>} Q" 
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "?M \<subseteq> wp\<^sub>\<alpha> \<beta> Q" using exec unfolding wp_def sp_def by fast
  qed (insert stablePQ stableM, auto)

  \<comment> \<open>Establish the early judgement over the new \<alpha>\<close>
  moreover have "R,G \<turnstile>\<^sub>A P {\<alpha>\<langle>tag \<beta>\<rangle>} ?M"
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "P \<subseteq> wp\<^sub>\<alpha> \<alpha>\<langle>tag \<beta>\<rangle> ?M" using vc unfolding wp_def wf_def sp_def by fast
  qed (insert stablePQ stableM g, auto)

  ultimately show ?thesis using that by blast
qed

text \<open>
  Reorder the judgements of a reorderable instruction \<alpha> and program c, given a suitable 
  interference property.
\<close>
lemma reorder_prog:
  assumes "R,G \<turnstile>\<^sub>l P {c} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "inter\<^sub>c R G c \<alpha>"
  obtains M' P' where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>c\<rrangle>} M'" "R,G \<turnstile>\<^sub>l M' {c} Q"
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
    using reorder_action[OF \<beta>(2) m'(1)] Basic by auto
  have "R,G \<turnstile>\<^sub>l M' {Basic \<beta>} Q" by (rule lrules.basic[OF m''(2)])
  then show ?case using Basic(1) \<beta>(1) m''(1) by auto
next
  case (Seq c\<^sub>1 c\<^sub>2)
  obtain M' where m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M'" "R,G \<turnstile>\<^sub>l M' {c\<^sub>2} M" using Seq(4) by fast
  have i: "inter\<^sub>c R G c\<^sub>1 \<alpha>\<llangle>c\<^sub>2\<rrangle>" "inter\<^sub>c R G c\<^sub>2 \<alpha>" using Seq by auto
  show ?case
  proof (rule Seq(2)[OF _ m(2) Seq(5) i(2)], goal_cases outer)
    case (outer P' N')
    hence c1: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} P'" using m(1) conseq by auto
    show ?case 
    proof (rule Seq(1)[OF _ c1 outer(2) i(1)], goal_cases inner)
      case (inner P'' M'')
      then show ?case using Seq(3) outer by auto
    qed
  qed
next
  case (Ord c\<^sub>1 c\<^sub>2)
  obtain M' where m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M'" "R,G \<turnstile>\<^sub>l M' {c\<^sub>2} M" using Ord(4) by fast
  have i: "inter\<^sub>c R G c\<^sub>1 \<alpha>\<llangle>c\<^sub>2\<rrangle>" "inter\<^sub>c R G c\<^sub>2 \<alpha>" using Ord by auto
  show ?case
  proof (rule Ord(2)[OF _ m(2) Ord(5) i(2)], goal_cases outer)
    case (outer P' N')
    hence c1: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} P'" using m(1) conseq by auto
    show ?case 
    proof (rule Ord(1)[OF _ c1 outer(2) i(1)], goal_cases inner)
      case (inner P'' M'')
      then show ?case using Ord(3) outer by auto
    qed
  qed
qed auto

section \<open>Transition Rules\<close>

text \<open>Local judgements are preserved across silent steps\<close>
lemma rewriteI [intro]:
  assumes "R,G \<turnstile>\<^sub>l P {c} Q"
  assumes "c \<leadsto> c'"
  shows "R,G \<turnstile>\<^sub>l P {c'} Q"
  using assms
proof (induct arbitrary: c' rule: lrules.induct)
  case (seq R G P c\<^sub>1 Q c\<^sub>2 M)
  show ?case using seq(5,1,2,3,4) by cases blast+
next
  case (ord R G P c\<^sub>1 Q c\<^sub>2 M)
  show ?case using ord(5,1,2,3,4) by cases blast+
next
  case (loop R P G c)
  thus ?case by cases blast+
qed auto

text \<open>Global judgements are preserved across silent steps\<close>
lemma g_rewriteI [intro]:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<leadsto> c'"
  shows "R,G \<turnstile> P {c'} Q"
  using assms
proof (induct arbitrary: c' rule: rules.induct)
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case using par(7,1,2,3,4,5,6) by cases blast+
qed auto

text \<open>Local judgements are preserved across reordered interference-free execution steps\<close>
lemma stepI:
  assumes "c \<mapsto>[r,\<alpha>] c'" "R,G \<turnstile>\<^sub>l P {c} Q"
  assumes "inter\<^sub>c R G r \<alpha>"
  shows "\<exists>P' M. P \<subseteq> P' \<and> (R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M) \<and> (R,G \<turnstile>\<^sub>l M {c'} Q)"
  using assms
proof (induct arbitrary: P R G Q)
  case (act \<alpha>)
  then show ?case
    apply (elim basicE)
    apply simp
    apply (meson atomic_rule_def nil lrules.conseq order_refl)
    done
next
  case (seq c\<^sub>1 c \<alpha>' c\<^sub>1' c\<^sub>2)
  obtain M' where m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M'" "R,G \<turnstile>\<^sub>l M' {c\<^sub>2} Q" using seq by fast
  then show ?case using seq(2)[OF m(1) seq(4)] m(2) by blast
next
  case (ooo c\<^sub>2 c \<alpha> c\<^sub>2' \<alpha>' c\<^sub>1)
  obtain M' where m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M'" "R,G \<turnstile>\<^sub>l M' {c\<^sub>2} Q" using ooo(4) by blast
  have i: "inter\<^sub>c R G c\<^sub>1 (\<alpha>\<llangle>c\<rrangle>)" "inter\<^sub>c R G c \<alpha>" using ooo by auto
  obtain P' M where m': "M' \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>c\<rrangle>} M" "R,G \<turnstile>\<^sub>l M {c\<^sub>2'} Q"
    using ooo(2)[OF m(2) i(2)] by blast
  hence m'': "R,G \<turnstile>\<^sub>l P {c\<^sub>1} P'" using m(1) by blast
  then show ?case using reorder_prog[OF m'' m'(2)] i(1) m'(3) by simp (metis lrules.seq)
next
  case (ord c\<^sub>1 c \<alpha> c\<^sub>1' c\<^sub>2)
  obtain M' where m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M'" "R,G \<turnstile>\<^sub>l M' {c\<^sub>2} Q" using ord by fast
  then show ?case using ord(2)[OF m(1) ord(4)] m(2) by blast
qed auto

text \<open>Global judgements are preserved across execution steps - reordering or not \<close>
lemma g_stepI:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<mapsto>[r,\<alpha>] c'"
  shows "\<exists>P' M. P \<subseteq> P' \<and> (R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M) \<and> (R,G \<turnstile> M {c'} Q)"
  using assms
proof (induct arbitrary: \<alpha> c' rule: rules.induct)
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case using par(7)
  proof cases
    case (par1 c\<^sub>1')
    obtain M\<^sub>2 where m2: "P\<^sub>2 \<subseteq> M\<^sub>2" "stable R\<^sub>2 M\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2} Q\<^sub>2" using par
      by (meson g_stable_preE)
    obtain P M\<^sub>1 where m1: "P\<^sub>1 \<subseteq> P" "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>A P { \<alpha>\<llangle>r\<rrangle> } M\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1'} Q\<^sub>1" 
      using par1 par(2)[OF par1(2)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par1 m2 par by blast
    moreover have "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>A P \<inter> M\<^sub>2 { \<alpha>\<llangle>r\<rrangle> } M\<^sub>1 \<inter> M\<^sub>2" 
      using m1(2) m2(2) par.hyps(6) by blast
    ultimately show ?thesis using m2(1) m1(1) by blast
  next
    case (par2 c\<^sub>2')
    obtain M\<^sub>1 where m1: "P\<^sub>1 \<subseteq> M\<^sub>1" "stable R\<^sub>1 M\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1} Q\<^sub>1" using par
      by (meson g_stable_preE)
    obtain P M\<^sub>2 where m2: "P\<^sub>2 \<subseteq> P" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>A P { \<alpha>\<llangle>r\<rrangle> } M\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2'} Q\<^sub>2"
      using par2 par(4)[OF par2(2)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par2 m1 par by blast
    moreover have "R\<^sub>2 \<inter> R\<^sub>1,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>A P \<inter> M\<^sub>1 { \<alpha>\<llangle>r\<rrangle> } M\<^sub>2 \<inter> M\<^sub>1" 
      using atomic_invI[OF m2(2) m1(2) par(5)] by blast
    ultimately show ?thesis using m2(1) m1(1) by (metis inf_commute inf_mono)
  qed 
 next
  case (conseq R G P c Q P' R' G' Q')
  thus ?case using rules.conseq atomic_conseqI by (smt dual_order.trans order_refl)
next
  case (frame R G P c Q R' M')
  then obtain P' M where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M" "R,G \<turnstile> M {c'} Q" by metis
  thus ?case using rules.frame atomic_invI frame(3,4) by blast
next
  case (thread R G P c Q)
  then show ?case using stepI[OF thread(3,1)] thread(2) indep_stepI[OF thread(2,3)] by auto 
qed

section \<open>Soundness\<close>

text \<open>All traces that start with a program c\<close>
fun cp :: "('a,'b) com \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where "cp c t = (t \<in> transitions \<and> fst (t ! 0) = c)"

text \<open>All traces that satisfy a precondition in their first state\<close>
fun pre :: "'b pred \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where 
    "pre P (s#t) = (snd s \<in> P)" | 
    "pre P [] = True"

text \<open>All traces that satisfy a postcondition in their final state given termination\<close>
fun post :: "'b pred \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where 
    "post Q [s] = (fst s = Nil \<longrightarrow> snd s \<in> Q)" | 
    "post Q (s#t) = post Q t" | 
    "post Q [] = True"

text \<open>All traces where program steps satisfy a guarantee\<close>
fun gurn :: "'b rpred \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where
    "gurn G (s#s'#t) = (gurn G (s'#t) \<and> (s -c\<rightarrow> s' \<longrightarrow> (snd s,snd s') \<in> G\<^sup>=))" |
    "gurn G _ = True"

text \<open>All traces where environment steps satisfy a rely\<close>
fun rely :: "'b rpred \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where
    "rely R (s#s'#t) = (rely R (s'#t) \<and> (s -e\<rightarrow> s' \<longrightarrow> (snd s, snd s') \<in> R))" |
    "rely R _ = True"

text \<open>Validity of the rely/guarantee judgements\<close>
definition validity ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45) 
  where "\<Turnstile> c SAT [P, R, G, Q] \<equiv> \<forall>t. cp c t \<and> pre P t \<and> rely R t \<longrightarrow> post Q t \<and> gurn G t"

subsection \<open>Soundness Proof\<close>

text \<open>All transitions that start with a program with a logic judgement and satisfy
      the precondition and environment rely should conform to the guarantee and
      establish the postcondition if they terminate\<close>
lemma sound_transitions:
  assumes "t \<in> transitions" "fst (t ! 0) = c" "R,G \<turnstile> P {c} Q" "pre P t" "rely R t"
  shows "post Q t \<and> gurn G t"
  using assms
proof (induct arbitrary: c P rule: transitions.induct)
  case (one s)
  thus ?case by force
next
  case (env s s' t)
  then obtain P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c} Q" by (metis g_stable_preE) 
  thus ?case using env by (auto simp: stable_def)
next
  case (prg s s' t)
  then obtain \<alpha> r where \<alpha>: "c \<mapsto>[r,\<alpha>] (fst s')" "(snd s,snd s') \<in> eval \<alpha>\<llangle>r\<rrangle>" by auto
  then obtain P' M where p: "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M" "R,G \<turnstile> M {fst s'} Q"
    using g_stepI[OF prg(5) \<alpha>(1)] by metis    
  hence "rely R (s' # t)" "pre M (s' # t)" "(snd s, snd s') \<in> G\<^sup>="
    using prg \<alpha>(2) apply (auto simp: eval_def atomic_rule_def wp_def) by fastforce+
  thus ?case using prg p(3) by auto
next
  case (sil s s' t)
  thus ?case by auto
qed

theorem sound:
  assumes "R,G \<turnstile> P { c } Q"
  shows "\<Turnstile> c SAT [P, R, G, Q]"
  using assms sound_transitions by (auto simp: validity_def)

end

end