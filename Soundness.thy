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
definition sp :: "'a \<Rightarrow> ('b,'c) rpred \<Rightarrow> ('b,'c) pred \<Rightarrow> ('b,'c) pred"
  where "sp \<alpha> R P \<equiv> {m. \<exists>m' m''. m' \<in> P \<and> (m',m'') \<in> beh \<alpha> \<and> (m'',m) \<in> fullR (R\<^sup>* ) }"

text \<open>Re-establish an atomic judgement with its strongest postcondition\<close>
lemma atomic_strongest:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} sp \<alpha> R P \<and> sp \<alpha> R P \<subseteq> Q"
proof -
  have "Q \<subseteq> {m. \<forall>m'. (m,m') \<in> fullR (R\<^sup>* ) \<longrightarrow> m' \<in> Q}" "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" 
    using assms stable_transitive unfolding atomic_rule_def wp_def by fast+
  hence "sp \<alpha> R P \<subseteq> Q" apply (auto simp: sp_def wp_def) by blast
  moreover have "R,G \<turnstile>\<^sub>A P {\<alpha>} (sp \<alpha> R P)"
    using assms unfolding atomic_rule_def wp_def stable_def sp_def by fastforce
  ultimately show ?thesis by auto
qed

section \<open>Reordering Rules\<close> 

text \<open>
  Reorder the judgements of two reorderable instructions given a suitable interference property.
  The precondition P and postcondition Q are preserved.
\<close>
lemma reorder_action:
  assumes "R,G \<turnstile>\<^sub>A P {\<beta>} M" "R,G \<turnstile>\<^sub>A M {\<alpha>} Q" "inter\<^sub>\<alpha> R G \<beta> \<alpha>"
  obtains M' where "R,G \<turnstile>\<^sub>A P {\<alpha>\<langle>\<beta>\<rangle>} M'" "R,G \<turnstile>\<^sub>A M' {\<beta>} Q"
proof -
  \<comment> \<open>Nominate the strongest-postcondition of \<alpha> from P as the state between \<alpha> and \<beta>\<close>
  let ?M="sp \<alpha>\<langle>\<beta>\<rangle> R P"

  \<comment> \<open>Establish stability for P, Q and the new intermediate state, in addition to guarantees\<close>
  have stablePQ: "stable R P" "stable R Q" "guar \<alpha> G" "guar \<beta> G"
    using assms(1,2) by (auto simp: atomic_rule_def)
  have stableM: "stable R ?M"  unfolding stable_def sp_def by force

  \<comment> \<open>Extract order independence properties\<close> 
  have ref: "Env R ; Basic \<beta> ; Env R ; Basic \<alpha> \<sqsubseteq> Env R ; Basic \<alpha>\<langle>\<beta>\<rangle> ; Env R ; Basic \<beta>"
    using assms(3) by (auto simp: inter\<^sub>\<alpha>_def)
  have g: "guar \<alpha>\<langle>\<beta>\<rangle> G" using assms(3) by (auto simp: inter\<^sub>\<alpha>_def)

  \<comment> \<open>Show transition from P to Q is independent of order\<close>
  have p: "P \<subseteq> wp\<^sub>\<alpha> \<beta> M" "M \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "M \<subseteq> wp UNIV (fullR (R\<^sup>* )) M" "P \<subseteq>  wp UNIV (fullR (R\<^sup>* )) P" "Q \<subseteq>  wp UNIV (fullR (R\<^sup>* )) Q"
    using assms(1,2)  unfolding atomic_rule_def by (auto intro!: stable_wp\<^sub>tI)
  hence "P \<subseteq>  wp UNIV (fullR (R\<^sup>* )) (wp\<^sub>\<alpha> \<beta> ( wp UNIV (fullR (R\<^sup>* )) (wp\<^sub>\<alpha> \<alpha> Q)))" unfolding wp_def by force
  hence exec: "P \<subseteq>  wp UNIV (fullR (R\<^sup>* )) (wp\<^sub>\<alpha> \<alpha>\<langle>\<beta>\<rangle> ( wp UNIV (fullR (R\<^sup>* )) (wp\<^sub>\<alpha> \<beta> Q)))" using ref by (auto simp: refine_def)
  hence vc: "P \<subseteq> vc \<alpha>\<langle>\<beta>\<rangle>" by (auto simp: wp_def)

  \<comment> \<open>Establish the late judgement over \<beta>\<close>
  have "R,G \<turnstile>\<^sub>A ?M {\<beta>} Q" 
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "?M \<subseteq> wp\<^sub>\<alpha> \<beta> Q" using exec unfolding wp_def sp_def by fast
  qed (insert stablePQ stableM, auto)

  \<comment> \<open>Establish the early judgement over the new \<alpha>\<close>
  moreover have "R,G \<turnstile>\<^sub>A P {\<alpha>\<langle>\<beta>\<rangle>} ?M"
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "P \<subseteq> wp\<^sub>\<alpha> \<alpha>\<langle>\<beta>\<rangle> ?M" using vc unfolding wp_def wf_def sp_def by fast
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
  obtain M' where m'': "R,G \<turnstile>\<^sub>A P' {\<alpha>\<langle>\<beta>\<rangle>} M'" "R,G \<turnstile>\<^sub>A M' {\<beta>} Q"
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
  show ?case using par(7,1,2,3,4,5,6)
    apply cases
    apply blast
    apply blast
    apply clarsimp
    sorry
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
qed 

abbreviation fullG
  where "fullG G \<equiv> {((g,l),(g',l')). (g,g') \<in> G}"

lemma gexec_localE:
  assumes "c \<mapsto>[g] c'" "local c"
  obtains \<alpha> r where "c \<mapsto>[r,\<alpha>] c'" "g = leaf\<^sub>r (eval \<alpha>\<llangle>r\<rrangle>)"
  using assms
  by (induct) auto

text \<open>Global judgements are preserved across execution steps - reordering or not \<close>
lemma g_stepI:
  assumes "R,G \<turnstile> P {c} Q"
  assumes "c \<mapsto>[g] c'"
  shows "\<exists>M v. P \<subseteq> wp v g M \<and> ({m. fst m \<in> v} \<inter> g) \<subseteq> fullG (G\<^sup>=) \<and> (R,G \<turnstile> M {c'} Q)"
  using assms
proof (induct arbitrary: g c' rule: rules.induct)
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case using par(7)
  proof cases
    case (lcl r \<alpha>)
    then show ?thesis by auto
  next
    case (par1 g' c\<^sub>1')
    obtain M\<^sub>2 where m2: "P\<^sub>2 \<subseteq> M\<^sub>2" "stable R\<^sub>2 M\<^sub>2" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2} Q\<^sub>2" using par
      by (meson g_stable_preE)
    obtain M\<^sub>1 v where m1: "P\<^sub>1 \<subseteq> wp v g' M\<^sub>1" "({m. fst m \<in> v} \<inter> g') \<subseteq> fullG (G\<^sub>1\<^sup>=)" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1'} Q\<^sub>1"
      using par1 par(2)[OF par1(3)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> left M\<^sub>1 \<inter> right M\<^sub>2 {c'} left Q\<^sub>1 \<inter> right Q\<^sub>2" 
      using par1 m2 par by blast
    moreover have "left P\<^sub>1 \<inter> right P\<^sub>2 \<subseteq> wp (left v) g (left M\<^sub>1 \<inter> right M\<^sub>2)" 
      using par1 m2(1,2) m1(1,2) par.hyps(6)
      unfolding left_def right_def left\<^sub>r_def wp_def stable_def
      apply auto
      apply (subgoal_tac "((gb, lb), g'a, l') \<in> fullG (R\<^sub>2\<^sup>=)")
      apply (subgoal_tac "(gb, rb) \<in> M\<^sub>2")
      apply auto
      apply (subgoal_tac "((gb, lb), g'a, l') \<in> {((g, l), g', l').
           (g, g') \<in> G\<^sub>1 \<or> g = g'}")
      apply auto
      apply (subgoal_tac "((gb, lb), g'a, l') \<in> {m. fst m \<in> v} \<inter> g'")
      apply blast
      by auto
    moreover have "({m. fst m \<in> (left v)} \<inter> g) \<subseteq> fullG (G\<^sub>1\<^sup>=)" 
      using m1(2) par1 
      apply (auto simp: left\<^sub>r_def left_def)
      apply (subgoal_tac "((g, l), g'a, l') \<in> {m. fst m \<in> v} \<inter> g'")
      apply blast
      apply auto
      done
    ultimately show ?thesis by blast
  next
    case (par2 g' c\<^sub>2')
    obtain M\<^sub>1 where m1: "P\<^sub>1 \<subseteq> M\<^sub>1" "stable R\<^sub>1 M\<^sub>1" "R\<^sub>1,G\<^sub>1 \<turnstile> M\<^sub>1 {c\<^sub>1} Q\<^sub>1" using par
      by (meson g_stable_preE)
    obtain M\<^sub>2 v where m2: "P\<^sub>2 \<subseteq> wp v g' M\<^sub>2" "({m. fst m \<in> v} \<inter> g') \<subseteq> fullG (G\<^sub>2\<^sup>=)" "R\<^sub>2,G\<^sub>2 \<turnstile> M\<^sub>2 {c\<^sub>2'} Q\<^sub>2"
      using par2 par(4)[OF par2(3)] by blast
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> left M\<^sub>1 \<inter> right M\<^sub>2 {c'} left Q\<^sub>1 \<inter> right Q\<^sub>2" 
      using par2 m1 par by blast
    moreover have "left P\<^sub>1 \<inter> right P\<^sub>2 \<subseteq> wp (right v) g (left M\<^sub>1 \<inter> right M\<^sub>2)" 
      using par2 m2(1,2) m1(1,2) par.hyps(5)
      unfolding left_def right_def right\<^sub>r_def wp_def stable_def
      apply auto
      apply (subgoal_tac "((gb, rb), aa, r') \<in> fullG (R\<^sub>1\<^sup>=)")
      apply (subgoal_tac "(gb, lb) \<in> M\<^sub>1")
      apply auto
      apply (subgoal_tac "((gb, rb), aa, r') \<in> {((g, l), g', l').
           (g, g') \<in> G\<^sub>2 \<or> g = g'}")
      apply auto
      apply (subgoal_tac "((gb, rb), aa, r') \<in> {m. fst m \<in> v} \<inter> g'")
      apply blast
      by auto
    moreover have "({m. fst m \<in> (right v)} \<inter> g) \<subseteq> fullG (G\<^sub>2\<^sup>=)" 
      using m2(2) par2 
      apply (auto simp: right\<^sub>r_def right_def)
      apply (subgoal_tac "((g, r), g'a, r') \<in> {m. fst m \<in> v} \<inter> g'")
      apply blast
      apply auto
      done
    ultimately show ?thesis by blast
  qed 
next
  case (conseq R G P c Q P' R' G' Q')
  then obtain v M where m: "P \<subseteq> wp v g M" "({m. fst m \<in> v} \<inter> g) \<subseteq> fullG (G\<^sup>=)" "R,G \<turnstile> M {c'} Q" by metis
  hence "P' \<subseteq> wp v g M" "({m. fst m \<in> v} \<inter> g) \<subseteq> fullG (G'\<^sup>=)" using conseq by auto
  moreover have "R',G' \<turnstile> M {c'} Q'" using conseq m rules.conseq by auto
  ultimately show ?case by auto
(*next
  case (frame R G P c Q R' M')
  then obtain P' M where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M" "R,G \<turnstile> M {c'} Q" by metis
  thus ?case using rules.frame atomic_frameI frame(3,4) by blast *)
next
  case (thread R G P c Q)
  hence "local c" using local_only by auto
  then obtain r \<alpha> where \<alpha>: "c \<mapsto>[r,\<alpha>] c'" "g = leaf\<^sub>r (eval \<alpha>\<llangle>r\<rrangle>)" using thread gexec_localE
    by blast
  then obtain P' M where act: "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<alpha>\<llangle>r\<rrangle>} M" "R,G \<turnstile> leaf M {c'} leaf Q"
    using stepI[OF \<alpha>(1) thread(1)] indep_stepI[OF thread(2) \<alpha>(1)] by blast
  moreover have  "(({m. fst m \<in> leaf (vc \<alpha>\<llangle>r\<rrangle>)}) \<inter> g) \<subseteq> fullG (G\<^sup>=)" using \<alpha>(2) act(2) 
    apply (auto simp: atomic_rule_def leaf_def leaf\<^sub>r_def eval_def)
    by blast
  moreover have "leaf P \<subseteq> wp (leaf (vc \<alpha>\<llangle>r\<rrangle>)) g (leaf M)"
    using \<alpha>(2) act(1,2) 
    by (auto simp: atomic_rule_def leaf\<^sub>r_def eval_def wp_def leaf_def)
  ultimately show ?case by blast
qed

section \<open>Soundness\<close>

text \<open>All traces that start with a program c\<close>
fun cp :: "('a,'b,'c) com \<Rightarrow> ('a,'b,'c) config list \<Rightarrow> bool"
  where "cp c t = (t \<in> transitions \<and> fst (t ! 0) = c)"

text \<open>All traces that satisfy a precondition in their first state\<close>
fun pre :: "('b,'c) gpred \<Rightarrow> ('a,'b,'c) config list \<Rightarrow> bool"
  where 
    "pre P (s#t) = (snd s \<in> P)" | 
    "pre P [] = True"

text \<open>All traces that satisfy a postcondition in their final state given termination\<close>
fun post :: "('b,'c) gpred \<Rightarrow> ('a,'b,'c) config list \<Rightarrow> bool"
  where 
    "post Q [s] = (fst s = Nil \<longrightarrow> snd s \<in> Q)" | 
    "post Q (s#t) = post Q t" | 
    "post Q [] = True"

text \<open>All traces where program steps satisfy a guarantee\<close>
fun gurn :: "('b,'c) rpred \<Rightarrow> ('a,'b,'c) config list \<Rightarrow> bool"
  where
    "gurn G (s#s'#t) = (gurn G (s'#t) \<and> (s -c\<rightarrow> s' \<longrightarrow> (fst (snd s), fst (snd s')) \<in> G\<^sup>=))" |
    "gurn G _ = True"

text \<open>All traces where environment steps satisfy a rely\<close>
fun rely :: "('b,'c) rpred \<Rightarrow> ('a,'b,'c) config list \<Rightarrow> bool"
  where
    "rely R (s#s'#t) = (rely R (s'#t) \<and> (s -e\<rightarrow> s' \<longrightarrow> (snd s, snd s') \<in> fullR R))" |
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
  then obtain g where \<alpha>: "c \<mapsto>[g] (fst s')" "(snd s,snd s') \<in> g" by auto
  then obtain v M where p: "P \<subseteq> wp v g M" "({m. fst m \<in> v} \<inter> g) \<subseteq> fullG (G\<^sup>=)" "R,G \<turnstile> M {fst s'} Q"
    using g_stepI[OF prg(5) \<alpha>(1)] by auto
  hence "rely R (s' # t)" "pre M (s' # t)" "(fst (snd s), fst (snd s')) \<in> G\<^sup>="
    using prg \<alpha>(2)
    apply (auto simp: wp_def)
    apply (cases "snd s'", auto)
    apply (subgoal_tac "(snd s,snd s') \<in> {m. fst m \<in> v} \<inter> g")
    apply (metis (mono_tags, lifting) Ball_Collect old.prod.case prod.collapse)
    apply auto
    apply (subgoal_tac "(snd s,snd s') \<in> {m. fst m \<in> v} \<inter> g")
    apply (metis (mono_tags, lifting) Ball_Collect old.prod.case prod.collapse)
    apply auto
    done
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