theory Trace_WP
  imports Pipeline Execution
begin

chapter \<open>Trace Weakest-Precondition Reasoning\<close>

locale trace_wp = execution eval + memory_model re fwd
  for eval :: "'a \<Rightarrow> 's rel"
  and re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100) 
  and fwd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" +
  fixes aeval :: "'a \<Rightarrow> 's rel"
  assumes aeval_sound: "\<And>\<alpha>. eval \<alpha> \<subseteq> aeval \<alpha>"

context trace_wp
begin

section \<open>Basic Definitions\<close>

text \<open>Stability of a state across an environment step\<close>
definition stable
  where "stable R P \<equiv> \<forall>m m'. m \<in> P \<longrightarrow> (m,m') \<in> R \<longrightarrow> m' \<in> P"

text \<open>Complete WP, based on the evaluation of an action\<close>
definition wp
  where "wp a P \<equiv> {m. \<forall>m'. (m,m') \<in> eval a \<longrightarrow> m' \<in> P}"

text \<open>Approximate WP, based on the approximate evaluation of an action\<close>
definition awp
  where "awp a P \<equiv> {m. \<forall>m'. (m,m') \<in> aeval a \<longrightarrow> m' \<in> P}"

text \<open>Stabilisation of a predicate under an environment step\<close>
definition st
  where "st R P \<equiv> {m. \<forall>m'. (m,m') \<in> R \<longrightarrow> m' \<in> P}"

text \<open>Ensure an action conforms to its guarantee\<close>
definition guar
  where "guar \<alpha> G ctx \<equiv> {(m,m'). m \<in> ctx \<alpha>} \<inter> eval \<alpha> \<subseteq> G"

text \<open>Wellformedness, current only enforcing transitivity and reflexivity on R\<close>
definition wf
  where "wf R G ctx \<equiv> 
            (\<forall>\<alpha>. guar \<alpha> G ctx) \<and>
            (\<forall>m m' m''. (m,m') \<in> R \<longrightarrow> (m',m'') \<in> R \<longrightarrow> (m,m'') \<in> R) \<and> 
            (\<forall>m. (m,m) \<in> R)"

text \<open>Compose two state transitions\<close>
definition comp (infixr "\<otimes>" 60)
  where "comp a b \<equiv> {(m,m'). \<exists>m''. (m,m'') \<in> a \<and> (m'',m') \<in> b}"

section \<open>Trace Rules\<close>

text \<open>Rule for an atomic operation with a context\<close>
definition atomic_rule :: "'s rel \<Rightarrow> 's rel \<Rightarrow> ('a \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 'a \<Rightarrow> 's set \<Rightarrow> bool" 
  ("_,_,_ \<turnstile>\<^sub>W _ {_} _" [20, 20, 20, 20] 20)
  where "R,G,ctx \<turnstile>\<^sub>W P {\<alpha>} Q \<equiv> P \<subseteq> awp \<alpha> Q \<and> P \<subseteq> ctx \<alpha> \<and> stable R P \<and> stable R Q"

text \<open>Rules for a sequential trace of operations\<close>
inductive trace_rules :: "('s) rel \<Rightarrow> ('s) rel \<Rightarrow> ('a \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 'a list \<Rightarrow> 's set \<Rightarrow> bool"
  ("_,_,_ \<turnstile>\<^sub>t _ {_} _" [20, 20, 20, 20] 20)
where
  nil[intro]: "stable R P \<Longrightarrow> R,G,ctx \<turnstile>\<^sub>t P { [] } P" |
  con[intro]: "R,G,ctx \<turnstile>\<^sub>W P {\<alpha>} Q \<Longrightarrow> R,G,ctx \<turnstile>\<^sub>t Q { t\<^sub>2 } Q' \<Longrightarrow> R,G,ctx \<turnstile>\<^sub>t P { \<alpha> # t\<^sub>2 } Q'" | 
  rw[intro]:  "P \<subseteq> P' \<Longrightarrow> Q' \<subseteq> Q \<Longrightarrow> R,G,ctx \<turnstile>\<^sub>t P' { t\<^sub>2 } Q' \<Longrightarrow> R,G,ctx \<turnstile>\<^sub>t P { t\<^sub>2 } Q"

text \<open>Soundness for RG\<close>
inductive valid :: "'s \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 'a list \<Rightarrow> 's set \<Rightarrow> bool"
  where
  base: "\<forall>m'. (m,m') \<in> R \<longrightarrow> m' \<in> Q \<Longrightarrow> valid m R G [] Q" |
  step: "\<forall>m'. (m,m') \<in> R \<longrightarrow> (\<forall>m''. (m',m'') \<in> eval \<alpha>' \<longrightarrow> ((m',m'') \<in> G \<and> valid m'' R G t Q)) \<Longrightarrow> 
            valid m R G (\<alpha>'#t) Q"

section \<open>Derived Rules\<close>

lemma nilE [elim!]:
  assumes "R,G,ctx \<turnstile>\<^sub>t P {[]} Q"
  obtains M where "P \<subseteq> M" "M \<subseteq> Q" "stable R M" 
  using assms 
proof (induct R G ctx P "[] :: 'a list" Q)
  case (nil R P G)
  then show ?case by auto
next
  case (rw P P' Q' Q R G)
  then show ?case by force
qed

lemma conE [elim]:
  assumes "R,G,ctx \<turnstile>\<^sub>t P {\<alpha>#t} Q"
  obtains M where "R,G,ctx \<turnstile>\<^sub>t P {[\<alpha>]} M" "R,G,ctx \<turnstile>\<^sub>t M {t} Q"
  using assms 
proof (induct R G ctx P "\<alpha>#t" Q arbitrary: \<alpha> t)
  case (con R G ctx P \<alpha> Q t\<^sub>2 Q')
  have "R,G,ctx \<turnstile>\<^sub>t P {[\<alpha>]} Q" using con(1) atomic_rule_def by force
  then show ?thesis using con(2,4) by auto 
qed auto

lemma singleE [elim]:
  assumes "R,G,ctx \<turnstile>\<^sub>t P {[\<alpha>]} Q"
  obtains P' Q' where "P \<subseteq> P'" "Q' \<subseteq> Q" "R,G,ctx \<turnstile>\<^sub>W P' {\<alpha>} Q'"
  using assms 
proof (induct R G ctx P "[\<alpha>] :: 'a list" Q)
  case (con R G P Q Q')
  then show ?case by auto
next
  case (rw P P' Q' Q R G)
  then show ?case by force
qed

lemma stableP [elim]:
  assumes "R,G,ctx \<turnstile>\<^sub>t P {t} Q"
  obtains P' where "P \<subseteq> P'" "stable R P'" "R,G,ctx \<turnstile>\<^sub>t P' {t} Q"
  using assms 
proof (induct)
  case (con R G ctx P \<alpha> Q t Q')
  show ?case using atomic_rule_def con(1,2,3) con(4)[of P] by blast
qed blast+

lemma seqE [elim]:
  assumes "R,G,ctx \<turnstile>\<^sub>t P {c\<^sub>1 @ c\<^sub>2} Q"
  obtains M where "R,G,ctx \<turnstile>\<^sub>t P {c\<^sub>1} M" "R,G,ctx \<turnstile>\<^sub>t M {c\<^sub>2} Q"
  using assms
proof (induct c\<^sub>1 arbitrary: P)
  case Nil
  hence "R,G,ctx \<turnstile>\<^sub>t P {c\<^sub>2} Q" by auto
  then obtain P' where p: "P \<subseteq> P'" "stable R P'" "R,G,ctx \<turnstile>\<^sub>t P' {c\<^sub>2} Q" by blast
  hence q: "R,G,ctx \<turnstile>\<^sub>t P {[]} P'" by auto
  show ?case using Nil(1)[OF q] p(3) by auto 
next
  case (Cons a c\<^sub>1)
  then obtain M P' Q' where s: "P \<subseteq> P'" "R,G,ctx \<turnstile>\<^sub>W P' {a} Q'" "Q' \<subseteq> M" "R,G,ctx \<turnstile>\<^sub>t M { c\<^sub>1 @ c\<^sub>2 } Q" by force
  show ?case 
  proof (rule Cons(1)[OF _ s(4)], goal_cases)
    case (1 N)
    hence "R,G,ctx \<turnstile>\<^sub>t P {a # c\<^sub>1} N" using 1 s(1,2,3) rw by (meson con order_refl)
    then show ?case using Cons(2) 1(2) by simp
  qed
qed

lemma seqI [intro]:
  assumes "R,G,ctx \<turnstile>\<^sub>t P {c\<^sub>1} M" "R,G,ctx \<turnstile>\<^sub>t  M {c\<^sub>2} Q"
  shows "R,G,ctx \<turnstile>\<^sub>t P {c\<^sub>1 @ c\<^sub>2} Q"
  using assms
proof (induct c\<^sub>1 arbitrary: P)
  case Nil
  then show ?case by clarsimp blast
next
  case (Cons a c\<^sub>1)
  then obtain N P' Q' where s: "P \<subseteq> P'" "R,G,ctx \<turnstile>\<^sub>W P' {a} Q'" "Q' \<subseteq> N" "R,G,ctx \<turnstile>\<^sub>t N { c\<^sub>1 } M" by force
  hence "R,G,ctx \<turnstile>\<^sub>t Q' {c\<^sub>1 @ c\<^sub>2} Q" using Cons(1)[OF s(4)] Cons(3) by auto
  thus ?case using con[OF s(2)] s(1) by auto
qed 

section \<open>Interference Pairs\<close>

text \<open>Independence of two actions \<beta> and \<alpha> under environment R, 
      such that the early execution of \<alpha> is assumed to be possible and 
      cannot invalidate sequential reasoning\<close>
definition indep\<^sub>a
  where "indep\<^sub>a R ctx \<beta> \<alpha> \<equiv> 
          (ctx \<beta> \<inter> awp \<beta> (ctx \<alpha>) \<subseteq> ctx (fwd \<alpha> \<beta>) \<inter> awp (fwd \<alpha> \<beta>) (st R (ctx \<beta>)) \<and> 
          (aeval (fwd \<alpha> \<beta>) \<otimes> R \<otimes> aeval \<beta> \<subseteq> aeval \<beta> \<otimes> R \<otimes> aeval \<alpha>))"

text \<open>Independence of trace t and action \<alpha> under environment R, 
      such that the early execution of \<alpha> is assumed to be possible and 
      cannot invalidate sequential reasoning\<close>
fun indep\<^sub>t
  where
    "indep\<^sub>t R ctx[] \<alpha> = True" |
    "indep\<^sub>t R ctx (\<beta>#t) \<alpha> = (indep\<^sub>t R ctx t \<alpha> \<and> indep\<^sub>a R ctx \<beta> \<alpha>\<langle>t\<rangle>)"

text \<open>Independence of actions in a trace t under environment R,
      such that all partial evaluations of the pre-program that enable early
      execution are considered\<close>
fun zip
  where 
    "zip R ctx t [] = True" |
    "zip R ctx t (\<alpha>#s) = ((\<forall>c r \<alpha>'. t \<midarrow>c\<leadsto>* r \<longrightarrow> \<alpha>'\<lless>r\<lless>\<alpha> \<longrightarrow> indep\<^sub>t R ctx r \<alpha>) \<and> zip R ctx (t@[\<alpha>]) s)"

text \<open>Wrap the zip with a default empty list for the pre-program\<close>
abbreviation indep
  where "indep R ctx t \<equiv> zip R ctx [] t"

text \<open>The zip should demonstrate independence between a prefix and an action if they
      are known to be reorderable\<close>
lemma zip_focus:
  assumes "zip R ctx t (pre @ \<alpha> # post)" "\<alpha>' \<lless> t@pre \<lless> \<alpha>" 
  shows "indep\<^sub>t R ctx (t@pre) \<alpha>"
  using assms by (induct pre arbitrary: \<alpha>' t) force+

text \<open>The zip property should be preserved if an executable action is removed from the pre trace\<close>
lemma zip_remove_pre:
  "\<alpha>' \<lless> pre \<lless> \<alpha> \<Longrightarrow> zip R ctx (pre @ \<alpha> # post) s \<Longrightarrow> zip R ctx (pre @ post) s"
proof (induct s arbitrary: post)
  case Nil
  then show ?case by auto
next
  case (Cons a s)
  have "(pre @ \<alpha> # post) \<midarrow>\<alpha>,\<alpha>'\<leadsto> (pre@post)"
    using Cons(2) by (induct pre arbitrary: \<alpha>') auto
  then show ?case using Cons by auto
qed

text \<open>The zip property should be preserved if an executable action is removed from the post trace\<close>
lemma zip_remove_post:
  assumes "zip R ctx t (pre @ \<alpha> # post)" "\<alpha>' \<lless> t@pre \<lless> \<alpha>" 
  shows "zip R ctx t (pre @ post)"
  using assms
proof (induct pre arbitrary: \<alpha>' t)
  case Nil
  thus ?case using zip_remove_pre by force
next
  case (Cons a pre)
  thus ?case by force
qed

text \<open>Show soundness of the independence information\<close>
lemma indep_sound:
  assumes "indep R ctx (pre @ \<alpha> # post)" "\<alpha>' \<lless> pre \<lless> \<alpha>"
  shows "indep\<^sub>t R ctx pre \<alpha> \<and> indep R ctx (pre @ post)"
  using assms zip_focus zip_remove_post by fastforce

section \<open>Reordering Rules\<close>

text \<open>
Reorder the judgements of two re-orderable actions, shifting a commit judgement before a weak judgement.
The conditions before (P) and after (Q) both actions are preserved, regardless of order.
\<close>
lemma reorder_action:
  assumes "R,G,ctx \<turnstile>\<^sub>W P {\<beta>} M" "R,G,ctx \<turnstile>\<^sub>W M {\<alpha>} Q" "\<beta> \<hookleftarrow> fwd \<alpha> \<beta>" "indep\<^sub>a R ctx \<beta> \<alpha>" "wf R G ctx"
  obtains M' where "R,G,ctx \<turnstile>\<^sub>W P {fwd \<alpha> \<beta>} M'" "R,G,ctx \<turnstile>\<^sub>W M' {\<beta>} Q"
proof -
  \<comment> \<open>Nominate the weakest-precondition of \<beta> over Q as the state between the new \<alpha> and \<beta>\<close>
  let ?\<alpha>="fwd \<alpha> \<beta>"
  let ?M="{m. \<exists>m' m''. m' \<in> P \<and> (m',m'') \<in> aeval ?\<alpha> \<and> (m'',m) \<in> R}"

  \<comment> \<open>Extract order independence properties\<close>
  have inter: "ctx \<beta> \<inter> awp \<beta> (ctx \<alpha>) \<subseteq> ctx ?\<alpha> \<inter> awp ?\<alpha> (st R (ctx \<beta>))"
    using assms(4) unfolding indep\<^sub>a_def by blast
  have env: "\<forall>Q. awp \<beta> (st R (awp \<alpha> Q)) \<subseteq> awp ?\<alpha> (st R (awp \<beta> Q))"
    using assms(4) unfolding indep\<^sub>a_def comp_def awp_def st_def by blast

  \<comment> \<open>Extract stability for P, Q and the new intermediate state\<close>
  have stablePQ: "stable R P" "stable R Q"
    using assms(1,2) by (auto simp: atomic_rule_def)
  have stableM: "stable R ?M" 
    using assms(5) unfolding wf_def stable_def by blast

  \<comment> \<open>Show transition from P to Q is independent of order\<close>
  have "P \<subseteq> awp \<beta> M" "M \<subseteq> awp \<alpha> Q" "M \<subseteq> st R M"
    using assms(1,2) unfolding atomic_rule_def stable_def st_def awp_def by auto
  hence "P \<subseteq> awp \<beta> (st R (awp \<alpha> Q))" unfolding st_def awp_def by blast
  hence exec: "P \<subseteq> awp ?\<alpha> (st R (awp \<beta> Q))" using env by blast

  \<comment> \<open>Show the contexts for both operations hold under P\<close>
  have "P \<subseteq> ctx \<beta> \<inter> awp \<beta> (ctx \<alpha>)" using assms(1,2) unfolding atomic_rule_def awp_def by blast
  hence ctx: "P \<subseteq> ctx ?\<alpha> \<inter> awp ?\<alpha> (st R (ctx \<beta>))" using inter by blast

  \<comment> \<open>Establish the late judgement over \<beta>\<close>
  have "R,G,ctx \<turnstile>\<^sub>W ?M {\<beta>} Q" 
  proof (unfold atomic_rule_def, intro conjI)
    show "?M \<subseteq> awp \<beta> Q" using exec unfolding st_def awp_def by blast
  next
    show "?M \<subseteq> ctx \<beta>" using ctx unfolding st_def awp_def by blast
  qed (insert stablePQ stableM, simp)

  \<comment> \<open>Establish the early judgement over the new \<alpha>\<close>
  moreover have "R,G,ctx \<turnstile>\<^sub>W P {?\<alpha>} ?M"
  proof (unfold atomic_rule_def, intro conjI)
    show "P \<subseteq> awp ?\<alpha> ?M" using assms(5) unfolding awp_def wf_def by blast
  next
    show "P \<subseteq> ctx (fwd \<alpha> \<beta>)" using ctx by blast
  qed (insert stablePQ stableM, simp)

  ultimately show ?thesis using that by blast
qed

text \<open>Inductive version of the action reordering\<close>
lemma reorder_trace:
  assumes "R,G,ctx \<turnstile>\<^sub>t P {t} M" "R,G,ctx \<turnstile>\<^sub>W M {\<alpha>} Q" "\<alpha>' \<lless> t \<lless> \<alpha>" "indep\<^sub>t R ctx t \<alpha>" "wf R G ctx"
  obtains M' P' where "P \<subseteq> P'" "R,G,ctx \<turnstile>\<^sub>W P' {\<alpha>'} M'" "R,G,ctx \<turnstile>\<^sub>t M' {t} Q"
  using assms
proof (induct t arbitrary: P \<alpha>')
  case Nil
  hence "P \<subseteq> M" "R,G,ctx \<turnstile>\<^sub>W M {\<alpha>} Q" by (auto simp: atomic_rule_def)
  thus ?case using Nil by (auto simp: atomic_rule_def)
next
  case (Cons \<beta> t)
  obtain I P' where i: "P \<subseteq> P'" "R,G,ctx \<turnstile>\<^sub>W P' {\<beta>} I" "R,G,ctx \<turnstile>\<^sub>t I {t} M"
    using Cons(3) by (meson conE order_refl singleE rw)
  obtain \<alpha>'' where a: "\<beta> \<hookleftarrow> fwd \<alpha>'' \<beta>" "\<alpha>'' \<lless> t \<lless> \<alpha>" "\<alpha>' = fwd \<alpha>'' \<beta>"
    using Cons(5) by fastforce
  have r: "R,G,ctx \<turnstile>\<^sub>W M {\<alpha>} Q" using Cons(4) by auto
  have e: "indep\<^sub>a R ctx \<beta> \<alpha>''" "indep\<^sub>t R ctx t \<alpha>" using Cons(6) a(2) by auto
  show ?case
  proof (rule Cons(1)[OF _ i(3) r a(2) e(2) assms(5)], goal_cases)
    case (1 Q M')
    hence "R,G,ctx \<turnstile>\<^sub>W I {\<alpha>''} M'" using i(2) by (auto simp: atomic_rule_def)
    then obtain J where "R,G,ctx \<turnstile>\<^sub>W P' {fwd \<alpha>'' \<beta>} J" "R,G,ctx \<turnstile>\<^sub>W J {\<beta>} M'"
      using reorder_action[OF i(2) _ a(1)] e(1) assms(5) by blast
    thus ?case using Cons(2) i(1,3) 1(3) a(3) by blast
  qed
qed

section \<open>Soundness\<close>

text \<open>Given a valid judgement over a sequential trace, show any pipelined version is valid\<close>
lemma trace_to_commits:
  "t' \<in> \<lbrakk>t\<rbrakk> \<Longrightarrow> wf R G ctx \<Longrightarrow> indep R ctx t \<Longrightarrow> R,G,ctx \<turnstile>\<^sub>t P { t } Q \<Longrightarrow> m \<in> P \<Longrightarrow> valid m R G t' Q"
proof (clarsimp simp add: pipelined_def, induct t t' "[] :: 'a list" arbitrary: P Q m rule: commit_trace.induct)
  case ct_nil
  then obtain M where s: "stable R M" "P \<subseteq> M" "M \<subseteq> Q" by fast
  hence "m \<in> M" "M \<subseteq> Q" using ct_nil by auto
  thus ?case using s(1) by (auto simp: stable_def intro: valid.base)
next
  case (ct_act t \<alpha> \<alpha>' ct t')
  show ?case using ct_act(1)
  proof (cases rule: commit_actionE)
    case (1 pre post)
    text \<open>Split the original trace into pre; \<alpha>; post\<close>
    hence "R,G,ctx \<turnstile>\<^sub>t P {pre @ [\<alpha>] @ post} Q" using ct_act(6) by auto
    then obtain M N where split: "R,G,ctx \<turnstile>\<^sub>t P {pre} M" "R,G,ctx \<turnstile>\<^sub>W M {\<alpha>} N" "R,G,ctx \<turnstile>\<^sub>t N {post} Q"
      by (elim seqE singleE) auto
    have inter: "indep\<^sub>t R ctx pre \<alpha>" "indep R ctx ct"
      using ct_act(5) 1(3) indep_sound
      unfolding 1(1,2) by auto
    text \<open>Show we can preserve the properties of interest executing \<alpha> first\<close>
    obtain P' B where reorder: "P \<subseteq> P'" "R,G,ctx \<turnstile>\<^sub>W P' {\<alpha>'} B" "R,G,ctx \<turnstile>\<^sub>t B {pre} N"
      using reorder_trace[OF split(1) split(2) 1(3)] ct_act(4) inter(1) by simp metis
    text \<open>Use the inductive property to maintain validity across pre; post\<close>
    have ind: "\<forall>m \<in> B. valid m R G t' Q"
      using ct_act(3)[OF ct_act(4) inter(2)] 1(2) seqI[OF reorder(3) split(3)] by force

    text \<open>Extract the useful properties for the executed action\<close>
    have props: "P' \<subseteq> wp \<alpha>' B \<inter> ctx \<alpha>'" "stable R P'"
      using reorder(1,2) aeval_sound unfolding atomic_rule_def
      by (auto simp: wp_def awp_def) blast 

    have "m \<in> P'" using ct_act(7) reorder(1) by auto
    thus ?thesis
    proof (intro allI impI conjI step, goal_cases)
      case (1 m' m'')
      thus ?case using props stable_def ct_act(4) unfolding wf_def guar_def by fast
    next
      case (2 m' m'')
      thus ?case using ind props stable_def wp_def by fast
    qed
  qed
qed

end

end