theory Soundness
  imports Rules
begin

chapter \<open>Soundness\<close>

locale soundness = rules 

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
  have stablePQ: "stable R P" "stable R Q" "guar\<^sub>\<alpha> \<alpha> G" "guar\<^sub>\<alpha> \<beta> G"
    using assms(1,2) by (auto simp: atomic_rule_def)
  have stableM: "stable R ?M"  unfolding stable_def sp_def by force

  \<comment> \<open>Extract order independence properties\<close> 
  have ref: "Env R ; Basic \<beta> ; Env R ; Basic \<alpha> \<sqsubseteq> Env R ; Basic \<alpha>\<langle>tag \<beta>\<rangle> ; Env R ; Basic \<beta>"
    using assms(3) by (auto simp: inter\<^sub>\<alpha>_def)
  have g: "guar\<^sub>\<alpha> \<alpha>\<langle>tag \<beta>\<rangle> G" using assms(3) by (auto simp: inter\<^sub>\<alpha>_def)

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
    using reorder_action[OF \<beta>(2) m'(1)] Basic by auto
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
qed (cases rule: silentE, auto)+

text \<open>Judgements are preserved across thread-local execution steps\<close>
lemma lexecute_ruleI [intro]:
  assumes "R,G \<turnstile> P {c} Q" "c \<mapsto>[r,\<alpha>] c'"  "inter\<^sub>c R G r \<alpha>"
  shows "\<exists>P' M. P \<subseteq> P' \<and> (R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M) \<and> R,G \<turnstile> M {c'} Q"
  using assms(2,1,3)
proof (induct arbitrary: P R G Q)
  case (act \<alpha>)
  then show ?case by clarsimp (meson atomic_rule_def nil rules.conseq order_refl)
next
  case (ino c\<^sub>1 c \<alpha>' c\<^sub>1' c\<^sub>2)
  then obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} Q" by auto
  then show ?case using ino(2)[OF m(1) ino(4)] m(2) by blast
next
  case (ooo c\<^sub>2 c \<alpha> c\<^sub>2' \<alpha>' c\<^sub>1)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} Q" using ooo(4) by blast
  have i: "inter\<^sub>c R G c\<^sub>1 (\<alpha>\<llangle>c\<rrangle>)" "inter\<^sub>c R G c \<alpha>" using ooo by auto
  obtain P' M where m': "M' \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>c\<rrangle>} M" "R,G \<turnstile> M {c\<^sub>2'} Q"
    using ooo(2)[OF m(2) i(2)] by blast
  hence m'': "R,G \<turnstile> P {c\<^sub>1} P'" using m(1) by blast
  then show ?case using reorder_prog[OF m'' m'(2)] i(1) m'(3) by simp (metis rules.seq)
next
  case (ord c\<^sub>1 c \<alpha> c\<^sub>1' c\<^sub>2)
  obtain M' where m: "R,G \<turnstile> P {c\<^sub>1} M'" "R,G \<turnstile> M' {c\<^sub>2} Q" using ord by fast
  then show ?case using ord(2)[OF m(1) ord(4)] m(2) by blast
qed

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
  hence "P \<inter> M' \<subseteq> wp v g (M \<inter> M')" using inv(3,4) unfolding stable_def guar_def wp_def apply auto by blast
  thus ?case using rules.inv p(2,3) inv(3,4) by blast
next       
  case (thread R G P c Q op l)
  show ?case using thread(4)
  proof (cases)
    case (thr r' \<alpha>' c'' l')
    hence i: "inter R G c''" "inter\<^sub>c R G r' \<alpha>'" using thread indep_stepI by auto
    then obtain P' M where p: "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>'\<llangle>r'\<rrangle>} M" "R,G \<turnstile> M {c''} Q" 
      using lexecute_ruleI[OF thread(1) thr(3)] by auto
    hence a: "P \<subseteq> wp\<^sub>\<alpha> \<alpha>'\<llangle>r'\<rrangle> M" "guar\<^sub>\<alpha> \<alpha>'\<llangle>r'\<rrangle> G" unfolding atomic_rule_def by auto
    hence "thr\<^sub>P op l P \<subseteq> wp (thr\<^sub>P op l (vc \<alpha>'\<llangle>r'\<rrangle>)) g (thr\<^sub>P op l' M)"
      unfolding wp_def thr(1) thr\<^sub>P_def by auto
    moreover have "guar (thr\<^sub>P op l (vc \<alpha>'\<llangle>r'\<rrangle>)) g (thr\<^sub>G op G)"
      using a(2) unfolding thr(1) thr\<^sub>P_def thr\<^sub>G_def guar_def by auto
    ultimately show ?thesis using p i unfolding thr(2) by blast
  qed 
(* next
  case (aux R G P c Q r')
  thus ?case sorry then obtain c'' p' \<beta> where a: "c \<mapsto>[p',\<beta>] c''" "aux\<^sub>c r' c'' = c'" "\<alpha> = aux\<^sub>\<alpha> r' \<beta>" "r = aux\<^sub>c r' p'"
    apply (elim aux_execE) by blast
  then obtain P' M where p: "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>\<llangle>p'\<rrangle>} M" "R,G \<turnstile> M {c''} Q"
    using aux(2)[OF a(1)] by blast
  have "aux\<^sub>P r' P \<subseteq> aux\<^sub>P r' P'" using p by (simp add: aux\<^sub>P_mono)
  moreover have "aux\<^sub>R r' R,aux\<^sub>G r' G \<turnstile> aux\<^sub>P r' M {c'} aux\<^sub>P r' Q" using p  a(2) by blast
  moreover have "aux\<^sub>R r' R,aux\<^sub>G r' G \<turnstile>\<^sub>A aux\<^sub>P r' P' {\<alpha>\<llangle>r\<rrangle>} aux\<^sub>P r' M"
    using p(2) unfolding a by simp blast
  ultimately show ?case by blast*)
qed auto

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
  case (env s s' t)
  then obtain P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c} Q" by (metis stable_preE) 
  thus ?case using env by (auto simp: stable_def)
next
  case (prg s s' t)
  then obtain g where \<alpha>: "c \<mapsto>[g] (fst s')" "(snd s,snd s') \<in> g" by auto
  then obtain M v where p: "P \<subseteq> wp v g M" "guar v g G" "R,G \<turnstile> M {fst s'} Q"
    using gexecute_ruleI[OF prg(5) \<alpha>(1)] by metis
  hence "rely R (s' # t)" "pre M (s' # t)" "(snd s, snd s') \<in> G\<^sup>="
    using prg \<alpha>(2) by (auto simp: atomic_rule_def wp_def guar_def)
  thus ?case using prg p(3) by auto
qed force+

theorem sound:
  assumes "R,G \<turnstile> P { c } Q"
  shows "\<Turnstile> c SAT [P, R, G, Q]"
  using assms sound_transitions by (auto simp: validity_def)

end

end