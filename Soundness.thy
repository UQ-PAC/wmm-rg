theory Soundness
  imports Global_Rules
begin

chapter \<open>Soundness\<close>

locale soundness = global_rules

context soundness
begin

section \<open>Helper Definitions\<close>

text \<open>Weakest precondition of the transitive closure of an arbitrary state relation\<close>
abbreviation wp\<^sub>t :: "'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp\<^sub>t R P \<equiv> wp (R\<^sup>*) P"

lemma stable_wp\<^sub>tI:
  "stable R P \<Longrightarrow> P \<subseteq> wp\<^sub>t R P"
  unfolding wp_def using stable_transitive by fast

text \<open>Strongest postcondition across arbitrary environment steps, 
      used to compute some new intermediate states for reasoning\<close>
definition sp :: "'a \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "sp \<alpha> R P \<equiv> {m. \<exists>m' m''. m' \<in> P \<and> (m',m'') \<in> eval \<alpha> \<and> (m'',m) \<in> R\<^sup>* }"

text \<open>Re-establish an atomic judgement with its strongest postcondition\<close>
lemma atomic_strongest:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} sp \<alpha> R P \<and> sp \<alpha> R P \<subseteq> Q"
proof -
  have "Q \<subseteq> {m. \<forall>m'. (m,m') \<in> R\<^sup>* \<longrightarrow> m' \<in> Q}" "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" 
    using assms stable_transitive unfolding atomic_rule_def wp_def by fast+
  hence "sp \<alpha> R P \<subseteq> Q" by (auto simp: sp_def wp_def)
  moreover have "R,G \<turnstile>\<^sub>A P {\<alpha>} (sp \<alpha> R P)"
    using assms by (clarsimp simp add: atomic_rule_def wp_def stable_def sp_def) force
  ultimately show ?thesis by auto
qed

section \<open>Reordering Rules\<close> 

text \<open>
  Reorder the judgements of two reorderable instructions given a suitable interference property.
  The precondition P and postcondition Q are preserved.
\<close>
lemma reorder_action:
  assumes "R,G \<turnstile>\<^sub>A P {\<beta>} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "\<beta> \<hookleftarrow> \<alpha>\<langle>\<beta>\<rangle>" "inter\<^sub>\<alpha> R G \<beta> \<alpha>"
  obtains M' where "R,G \<turnstile>\<^sub>A P {\<alpha>\<langle>\<beta>\<rangle>} M'" "R,G \<turnstile>\<^sub>A M' {\<beta>} Q"
proof -
  \<comment> \<open>Nominate the strongest-postcondition of \<alpha> from P as the state between \<alpha> and \<beta>\<close>
  let ?M="sp \<alpha>\<langle>\<beta>\<rangle> R P"

  \<comment> \<open>Extract order independence properties\<close>
  have "R\<^sup>* O eval \<alpha>\<langle>\<beta>\<rangle> O R\<^sup>* O eval \<beta> \<subseteq> R\<^sup>* O eval \<beta> O R\<^sup>* O eval \<alpha>"
    using assms(4) by (auto simp: inter\<^sub>\<alpha>_def)
  hence env: "\<forall>Q. wp\<^sub>t R (wp\<^sub>\<alpha> \<beta> (wp\<^sub>t R (wp\<^sub>\<alpha> \<alpha> Q))) \<subseteq> wp\<^sub>t R (wp\<^sub>\<alpha> \<alpha>\<langle>\<beta>\<rangle> (wp\<^sub>t R (wp\<^sub>\<alpha> \<beta> Q)))"
    unfolding comp_def wp_def by safe blast 
  have g: "eval \<alpha>\<langle>\<beta>\<rangle> \<subseteq> G" using assms(4) by (auto simp: inter\<^sub>\<alpha>_def)

  \<comment> \<open>Establish stability for P, Q and the new intermediate state, in addition to guarantees\<close>
  have stablePQ: "stable R P" "stable R Q" "eval \<alpha> \<subseteq> G" "eval \<beta> \<subseteq> G"
    using assms(1,2) by (auto simp: atomic_rule_def)
  have stableM: "stable R ?M"  unfolding stable_def sp_def by force

  \<comment> \<open>Show transition from P to Q is independent of order\<close>
  have p: "P \<subseteq> wp\<^sub>\<alpha> \<beta> M" "M \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "M \<subseteq> wp\<^sub>t R M" "P \<subseteq> wp\<^sub>t R P" "Q \<subseteq> wp\<^sub>t R Q"
    using assms(1,2)  unfolding atomic_rule_def by (auto intro!: stable_wp\<^sub>tI)
  hence "P \<subseteq> wp\<^sub>t R (wp\<^sub>\<alpha> \<beta> (wp\<^sub>t R (wp\<^sub>\<alpha> \<alpha> Q)))" unfolding wp_def by blast
  hence exec: "P \<subseteq> wp\<^sub>t R (wp\<^sub>\<alpha> \<alpha>\<langle>\<beta>\<rangle> (wp\<^sub>t R (wp\<^sub>\<alpha> \<beta> Q)))" using env by blast

  \<comment> \<open>Establish the late judgement over \<beta>\<close>
  have "R,G \<turnstile>\<^sub>A ?M {\<beta>} Q" 
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "?M \<subseteq> wp (eval \<beta>) Q" using exec unfolding wp_def sp_def by blast
  qed (insert stablePQ stableM, simp)

  \<comment> \<open>Establish the early judgement over the new \<alpha>\<close>
  moreover have "R,G \<turnstile>\<^sub>A P {\<alpha>\<langle>\<beta>\<rangle>} ?M"
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "P \<subseteq> wp\<^sub>\<alpha> \<alpha>\<langle>\<beta>\<rangle> ?M" unfolding wp_def wf_def sp_def by blast
  qed (insert stablePQ stableM g, simp)

  ultimately show ?thesis using that by blast
qed

text \<open>
  Reorder the judgements of a reorderable instruction \<alpha> and program c, given a suitable 
  interference property.
\<close>
lemma reorder_prog:
  assumes "R,G \<turnstile>\<^sub>l P {c} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "\<alpha>' < c <\<^sub>c \<alpha>" "inter\<^sub>c R G c \<alpha>"
  obtains M' P' where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>'} M'" "R,G \<turnstile>\<^sub>l M' {c} Q"
  using assms
proof (induct c arbitrary: R G P M Q \<alpha>' \<alpha>)
  case Nil
  hence "P \<subseteq> M" by blast
  then show ?case using Nil by (auto simp: atomic_rule_def)
next
  case (Basic \<beta>)
  have \<alpha>: "\<beta> \<hookleftarrow> \<alpha>\<langle>\<beta>\<rangle>" "\<alpha>' = \<alpha>\<langle>\<beta>\<rangle>" using Basic by auto
  obtain P' N' where \<beta>: "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>} N'" "N' \<subseteq> M" using Basic by auto
  have m': "R,G \<turnstile>\<^sub>A N' {\<alpha>} Q"
    using atomic_pre[OF Basic(3)] \<beta>(2,3) Basic(3) by (auto simp: atomic_rule_def)
  obtain M' where m'': "R,G \<turnstile>\<^sub>A P' {\<alpha>\<langle>\<beta>\<rangle>} M'" "R,G \<turnstile>\<^sub>A M' {\<beta>} Q"
    using reorder_action[OF \<beta>(2) m'(1) \<alpha>(1)] Basic by auto
  have "R,G \<turnstile>\<^sub>l M' {Basic \<beta>} Q" by (rule lrules.basic[OF m''(2)])
  then show ?case using Basic(1) \<beta>(1) m''(1) \<alpha>(2) by auto
next
  case (Seq c\<^sub>1 c\<^sub>2)
  obtain \<alpha>\<^sub>n where \<alpha>: "\<alpha>' < c\<^sub>1 <\<^sub>c \<alpha>\<^sub>n" "\<alpha>\<^sub>n < c\<^sub>2 <\<^sub>c \<alpha>" using Seq by auto
  obtain M' where m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M'" "R,G \<turnstile>\<^sub>l M' {c\<^sub>2} M" using Seq(4) by fast
  have i: "inter\<^sub>c R G c\<^sub>1 \<alpha>\<^sub>n" "inter\<^sub>c R G c\<^sub>2 \<alpha>" using Seq \<alpha> by auto
  show ?case
  proof (rule Seq(2)[OF _ m(2) Seq(5) \<alpha>(2) i(2)], goal_cases outer)
    case (outer P' N')
    hence c1: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} P'" using m(1) conseq by auto
    show ?case 
    proof (rule Seq(1)[OF _ c1 outer(2) \<alpha>(1) i(1)], goal_cases inner)
      case (inner P'' M'')
      then show ?case using Seq(3) outer by auto
    qed
  qed
next
  case (Choice c\<^sub>1 c\<^sub>2)
  hence \<alpha>: "\<alpha>' < c\<^sub>1 <\<^sub>c \<alpha>" "\<alpha>' < c\<^sub>2 <\<^sub>c \<alpha>" by auto
  obtain m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M" "R,G \<turnstile>\<^sub>l P {c\<^sub>2} M" using Choice(4) by blast
  have i: "inter\<^sub>c R G c\<^sub>1 \<alpha>" "inter\<^sub>c R G c\<^sub>2 \<alpha>" using Choice by auto
  show ?case
  proof (rule Choice(2)[OF _ m(2) Choice(5) \<alpha>(2) i(2)], goal_cases outer)
    case (outer P' N')
    show ?case 
    proof (rule Choice(1)[OF _ m(1) Choice(5) \<alpha>(1) i (1)], goal_cases inner)
      case (inner P'' N'')
      hence "R,G \<turnstile>\<^sub>l (N' \<inter> N'') {c\<^sub>1} Q"
        using outer by (meson Int_lower2 subset_refl lrules.conseq)
      moreover have "R,G \<turnstile>\<^sub>l (N' \<inter> N'') {c\<^sub>2} Q" 
        using inner outer by (meson Int_lower1 subset_refl lrules.conseq)
      ultimately have "R,G \<turnstile>\<^sub>l (N' \<inter> N'') {c\<^sub>1 \<sqinter> c\<^sub>2} Q" by auto
      moreover have "P \<subseteq> P' \<inter> P''" using outer inner by auto
      ultimately show ?case using actomic_conjI[OF outer(2) inner(2)] Choice(3) by blast 
    qed
  qed
next
  case (Loop c)
  then obtain I where i: "P \<subseteq> I" "R,G \<turnstile>\<^sub>l I {c} I" "stable R I" "I \<subseteq> M" by auto
  have [simp]: "\<alpha>' = \<alpha>" using Loop by auto
  have \<alpha>: "\<alpha> < c <\<^sub>c \<alpha>" using Loop by auto
  have "R,G \<turnstile>\<^sub>A I {\<alpha>} Q" using Loop(4) i(3,4) by (meson atomic_pre)
  hence s: "R,G \<turnstile>\<^sub>A I {\<alpha>} (sp \<alpha> R I)" "sp \<alpha> R I \<subseteq> Q" using atomic_strongest by auto
  have d: "inter\<^sub>c R G c \<alpha>" using Loop by auto

  show ?case
  proof (rule Loop(1)[OF _ i(2) s(1) \<alpha> d], goal_cases outer)
    case (outer P' I')
    hence "R,G \<turnstile>\<^sub>A I {\<alpha>} I'" using i(3) by (meson atomic_pre)
    hence "sp \<alpha> R I \<subseteq> I'" using atomic_strongest by auto
    hence "R,G \<turnstile>\<^sub>l (sp \<alpha> R I) {c} (sp \<alpha> R I)" using outer(3) lrules.conseq by simp
    hence "R,G \<turnstile>\<^sub>l (sp \<alpha> R I) {c*} (sp \<alpha> R I)" using s(1) by (meson loop atomic_rule_def)
    hence "R,G \<turnstile>\<^sub>l (sp \<alpha> R I) {c*} Q" using s(2) conseq by blast
    then show ?case using Loop(2)[OF i(1)] s(1) by simp
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
  show ?case using par(7,1,2,3,4,5,6) by (cases) blast+
qed auto

text \<open>Local judgements are preserved across reordered interference-free execution steps\<close>
lemma stepI:
  assumes "c \<mapsto>[\<alpha>,r,\<alpha>'] c'" "R,G \<turnstile>\<^sub>l P {c} Q"
  assumes "inter\<^sub>c R G r \<alpha>'"
  shows "\<exists>P' M. P \<subseteq> P' \<and> (R,G \<turnstile>\<^sub>A P' {\<alpha>} M) \<and> (R,G \<turnstile>\<^sub>l M {c'} Q)"
  using assms
proof (induct arbitrary: P R G Q)
  case (act \<alpha>)
  then show ?case by (elim basicE) (meson atomic_rule_def nil lrules.conseq order_refl)
next
  case (seq c\<^sub>1 \<alpha> c \<alpha>' c\<^sub>1' c\<^sub>2)
  obtain M' where m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M'" "R,G \<turnstile>\<^sub>l M' {c\<^sub>2} Q" using seq by fast
  then show ?case using seq(2)[OF m(1) seq(4)] m(2) by blast
next
  case (ooo c\<^sub>2 \<alpha> c \<alpha>' c\<^sub>2' \<gamma> c\<^sub>1)
  obtain M' where m: "R,G \<turnstile>\<^sub>l P {c\<^sub>1} M'" "R,G \<turnstile>\<^sub>l M' {c\<^sub>2} Q" using ooo by fast
  have i: "inter\<^sub>c R G c\<^sub>1 (\<alpha>'\<llangle>c\<rrangle>)" "inter\<^sub>c R G c \<alpha>'" using ooo by auto
  obtain P' M where m': "M' \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>} M" "R,G \<turnstile>\<^sub>l M {c\<^sub>2'} Q"
    using ooo(2)[OF m(2) i(2)] by blast
  hence m'': "R,G \<turnstile>\<^sub>l P {c\<^sub>1} P'" using m(1) by blast
  have "\<alpha>'\<llangle>c\<rrangle> = \<alpha>" using ooo(1) collect_reorder by auto
  then show ?case using reorder_prog[OF m'' m'(2) ooo(3)] i(1) m'(3) by (metis lrules.seq)
qed 

text \<open>Global judgements are preserved across execution steps - reordering or not \<close>
lemma g_stepI:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<mapsto>\<^sub>\<alpha> c'"
  shows "\<exists>P' M. P \<subseteq> P' \<and> (R,G \<turnstile>\<^sub>A P' {\<alpha>} M) \<and> (R,G \<turnstile> M {c'} Q)"
  using assms
proof (induct arbitrary: \<alpha> c' rule: rules.induct)
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case using par(7)
  proof cases
    case (par1 c\<^sub>1')
    obtain M\<^sub>2 where m2: "P\<^sub>2 \<subseteq> M\<^sub>2" "stable R\<^sub>2 M\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2} Q\<^sub>2" using par
      by (meson g_stable_preE)
    obtain P M\<^sub>1 where m1: "P\<^sub>1 \<subseteq> P" "R\<^sub>1,G\<^sub>1 \<turnstile>\<^sub>A P { \<alpha> } M\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1'} Q\<^sub>1" 
      using par1 par(2)[OF par1(2)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par1 m2 par by blast
    moreover have "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>A P \<inter> M\<^sub>2 { \<alpha> } M\<^sub>1 \<inter> M\<^sub>2" 
      using m1(2) m2(2) par.hyps(6) by blast
    ultimately show ?thesis using m2(1) m1(1) by blast
  next
    case (par2 c\<^sub>2')
    obtain M\<^sub>1 where m1: "P\<^sub>1 \<subseteq> M\<^sub>1" "stable R\<^sub>1 M\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1} Q\<^sub>1" using par
      by (meson g_stable_preE)
    obtain P M\<^sub>2 where m2: "P\<^sub>2 \<subseteq> P" "R\<^sub>2,G\<^sub>2 \<turnstile>\<^sub>A P { \<alpha> } M\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2'} Q\<^sub>2"
      using par2 par(4)[OF par2(2)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> M\<^sub>1 \<inter> M\<^sub>2 {c'} Q\<^sub>1 \<inter> Q\<^sub>2" using par2 m1 par by blast
    moreover have "R\<^sub>2 \<inter> R\<^sub>1,G\<^sub>1 \<union> G\<^sub>2 \<turnstile>\<^sub>A P \<inter> M\<^sub>1 { \<alpha> } M\<^sub>2 \<inter> M\<^sub>1" 
      using atomic_frameI[OF m2(2) m1(2) par(5)] by blast
    ultimately show ?thesis using m2(1) m1(1) by (metis inf_commute inf_mono)
  qed 
next
  case (conseq R G P c Q P' R' G' Q')
  thus ?case using rules.conseq atomic_conseqI by (meson order_refl subset_trans)
next
  case (frame R G P c Q R' M')
  then obtain P' M where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>} M" "R,G \<turnstile> M {c'} Q" by metis
  thus ?case using rules.frame atomic_frameI frame(3,4) by blast
next
  case (thread R G P c Q)
  hence "local c" using local_only by auto
  then obtain r \<alpha>'' where c: "c \<mapsto>[\<alpha>,r,\<alpha>''] c'" using thread exec_collect by blast
  then show ?case 
    using stepI[OF c thread(1)] thread(2) indep_stepI[OF thread(2) c] by auto 
qed

section \<open>Soundness\<close>

text \<open>Set of all config traces that start with a program c\<close>
definition cp :: "'a com \<Rightarrow> ('a,'b) config list set"
  where "cp c \<equiv> {t. t \<in> transitions \<and> fst (t ! 0) = c}"

text \<open>Set of all config traces that satisfy a precondition in their first state\<close>
definition pre :: "'b pred \<Rightarrow> ('a,'b) config list set"
  where "pre P \<equiv> {t. snd (t!0) \<in> P}"

text \<open>Set of all config traces where environment steps satisfy a rely\<close>
definition rely :: "'b rpred \<Rightarrow> ('a,'b) config list set"
  where "rely R \<equiv> {t. (\<forall>i. Suc i < length t \<longrightarrow> t!i -e\<rightarrow> t!Suc i \<longrightarrow> (snd(t!i), snd(t!Suc i)) \<in> R)}"

text \<open>Set of all config traces where program steps satisfy a guarantee\<close>
definition gurn :: "'b rpred \<Rightarrow> ('a,'b) config list set"
  where "gurn G \<equiv> {t. (\<forall>i. Suc i < length t \<longrightarrow> t!i -c\<rightarrow> t!Suc i \<longrightarrow> (snd(t!i), snd(t!Suc i)) \<in> G\<^sup>=)}"

text \<open>Set of all config traces that satisfy a postcondition in their final state\<close>
definition post :: "'b pred \<Rightarrow> ('a,'b) config list set"
  where "post Q \<equiv> {t. fst (last t) = Nil \<longrightarrow> snd (last t) \<in> Q}"

text \<open>Validity of the rely/guarantee judgements\<close>
definition validity ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45) 
  where "\<Turnstile> c SAT [P, R, G, Q] \<equiv> cp c \<inter> pre P \<inter> rely R \<subseteq> gurn G \<inter> post Q"

subsection \<open>Properties\<close>

lemma gurn [simp]:
  "(s # s' # t \<in> gurn G) = (s' # t \<in> gurn G \<and> (s -c\<rightarrow> s' \<longrightarrow> (snd s, snd s') \<in> G\<^sup>=))"
  unfolding gurn_def using length_Suc_conv less_Suc_eq_0_disj by auto

lemma rely [simp]:
  "(s # s' # t \<in> rely R) = (s' # t \<in> rely R \<and> (s -e\<rightarrow> s' \<longrightarrow> (snd s, snd s') \<in> R))"
  unfolding rely_def using length_Suc_conv less_Suc_eq_0_disj by auto

lemma pre [simp]:
  "(s # t \<in> pre P) = (snd s \<in> P)"
  by (auto simp: pre_def)

lemma post [simp]:
  "([x] \<in> post P) = (fst x = Nil \<longrightarrow> snd x \<in> P)"
  "(s # s' # t \<in> post Q) = (s' # t \<in> post Q)"
  by (auto simp: post_def)

subsection \<open>Soundness Proof\<close>

text \<open>All transitions that start with a program with a logic judgement and satisfy
      the precondition and environment rely should conform to the guarantee and
      establish the postcondition if they terminate\<close>
lemma sound_transitions:
  assumes "t \<in> transitions" "fst (t ! 0) = c" "R,G \<turnstile> P {c} Q" "t \<in> pre P \<inter> rely R"
  shows "t \<in> gurn G \<inter> post Q"
  using assms
proof (induct arbitrary: c P rule: transitions.induct)
  case (one s)
  thus ?case using gurn_def by force
next
  case (env s s' t)
  then obtain P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c} Q" by (metis g_stable_preE) 
  thus ?case using env by (auto simp: stable_def)
next
  case (prg s s' t)
  then obtain \<alpha> where \<alpha>: "c \<mapsto>\<^sub>\<alpha> (fst s')" "(snd s,snd s') \<in> eval \<alpha>" by auto
  then obtain P' M where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>} M" "R,G \<turnstile> M {fst s'} Q"
    using g_stepI[OF prg(5) \<alpha>(1)] by metis
  thus ?case using prg \<alpha> unfolding atomic_rule_def wp_def by fastforce
next
  case (sil s s' t)
  thus ?case by auto
qed

theorem sound:
  assumes "R,G \<turnstile> P { c } Q"
  shows "\<Turnstile> c SAT [P, R, G, Q]"
  using assms sound_transitions by (auto simp: validity_def cp_def)

end

end