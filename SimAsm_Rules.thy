theory SimAsm_Rules
  imports SimAsm
begin

section \<open>Wellformedness\<close>

definition glb
  where "glb m \<equiv> \<lparr> st = (\<lambda>v. st m (Glb v)), \<dots> = more m \<rparr>"

definition rg
  where "rg m \<equiv> \<lambda>v. st m (Reg v)"

definition stabilize
  where "stabilize R P \<equiv> {m. \<forall>m'. (glb m,glb m') \<in> R \<longrightarrow> rg m = rg m' \<longrightarrow> m' \<in> P}"

definition reflexive
  where "reflexive R \<equiv> \<forall>m. (m,m) \<in> R"

definition transitive
  where "transitive R \<equiv> \<forall>m m' m''. (m,m') \<in> R \<longrightarrow> (m',m'') \<in> R \<longrightarrow> (m,m'') \<in> R"

definition assert
  where "assert b \<equiv> {m. b}"

text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step\<^sub>t :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) trel"
  where "step\<^sub>t R \<equiv> {(m,m'). (glb m, glb m') \<in> R \<and> rg m = rg m'}"

text \<open>Lift a relational predicate\<close>
definition step :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) trel"
  where "step R \<equiv> {(m,m'). (glb m, glb m') \<in> R}"

text \<open>Define stability in terms of a relational predicate that preserves the thread state\<close>
abbreviation stable\<^sub>t
  where "stable\<^sub>t R P \<equiv> stable (step\<^sub>t R) P"

text \<open>Couple all wellformedness conditions into a single definition\<close>
abbreviation wellformed :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'a) grel \<Rightarrow> bool"
  where "wellformed R G \<equiv> reflexive R \<and> transitive R \<and> reflexive G" 

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G"
  shows "stable\<^sub>t R (stabilize R Q)"
  unfolding stable_def step\<^sub>t_def
proof (clarsimp)
  fix m m'
  assume a: "m \<in> stabilize R Q" "(glb m, glb m') \<in> R" "rg m = rg m'"
  have "\<forall>g''. (glb m',g'') \<in> R \<longrightarrow> (glb m,g'') \<in> R"
    using assms a(2) unfolding transitive_def by blast
  thus "m' \<in> stabilize R Q" using a(1,3) by (auto simp: stabilize_def)
qed

text \<open>The conjunction of two stable predicates is stable\<close>
lemma stable\<^sub>t_conj [intro]:
  assumes "stable\<^sub>t R P" "stable\<^sub>t R Q"
  shows "stable\<^sub>t R (P \<inter> Q)"
  using assms by (auto simp: stable_def)

text \<open>Elimination rule to ignore the stabilization process\<close>
lemma stabilizeE:
  assumes "m \<in> stabilize R P"
  assumes "reflexive R"
  obtains "m \<in> P"
proof -
  have "\<forall>g. (glb m, glb g) \<in> R \<longrightarrow> rg m = rg g \<longrightarrow> g \<in> P" "(glb m, glb m) \<in>  R"
    using assms by (auto simp: reflexive_def stabilize_def)
  thus ?thesis using that by auto
qed

text \<open>Stabilization preserves entailment\<close>
lemma stabilize_entail :
  assumes "m \<in> stabilize R P" 
  assumes "reflexive R"
  assumes "P \<subseteq> Q"
  shows "m \<in> stabilize R Q"
  using assms by (auto simp: stabilize_def)

section \<open>Predicate Transformations\<close>

text \<open>Transform a predicate based on an sub-operation\<close>
fun wp\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) trans" 
  where 
    "wp\<^sub>i (assign r e) Q = {m. (m (r :=\<^sub>s ev m e)) \<in> Q}" |
    "wp\<^sub>i (cmp b) Q =  {m. ev\<^sub>B m b \<longrightarrow> m \<in> Q}" | 
    "wp\<^sub>i _ Q = Q"

text \<open>Transform a predicate based on an auxiliary state update\<close>
fun wp\<^sub>a :: "('v,'g,'r,'a) auxfn \<Rightarrow> ('v,'g,'r,'a) trans"
  where "wp\<^sub>a a Q = {m. m(aux: a) \<in> Q}"

text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) trans"
  where
    "wp R Skip Q = Q" |
    "wp R (Op v a f) Q = stabilize R (v \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = stabilize R (wp\<^sub>i (cmp b) (wp R c\<^sub>1 Q) \<inter> wp\<^sub>i (ncmp b) (wp R c\<^sub>2 Q))" |
    "wp R (While b I c) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp\<^sub>i (cmp b) (wp R c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" |
    "wp R (DoWhile I c b) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp R c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"

text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "('v,'g,'r,'a) trans \<Rightarrow> ('v,'g,'r,'a) rtrans"
  where "wp\<^sub>r f G \<equiv> {(m,m'). m' \<in> f {m'. (m,m') \<in> G}}"

subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar
  where "guar f G \<equiv> {m. (m,m) \<in> (wp\<^sub>r f G)}"

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c Skip G = True" |
    "guar\<^sub>c (Op v a f) G = (v \<subseteq> guar (wp\<^sub>i a o wp\<^sub>a f) (step G))" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If _ c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While _ _ c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c (DoWhile _ c _) G = (guar\<^sub>c c G)"

section \<open>Locale Interpretation\<close>

text \<open>Convert the language into the abstract language expected by the underlying logic\<close> 
fun lift\<^sub>c :: "('v,'g,'r,'a) lang \<Rightarrow> (('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) com"
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Op v a f) = Basic (\<lfloor>v,a,f\<rfloor>)" |
    "lift\<^sub>c (lang.Seq c\<^sub>1 c\<^sub>2) = (com.Seq (lift\<^sub>c c\<^sub>1) (lift\<^sub>c c\<^sub>2))" |
    "lift\<^sub>c (If b c\<^sub>1 c\<^sub>2) = (Choice 
      (com.Seq (Basic (\<lfloor>cmp b\<rfloor>)) (lift\<^sub>c c\<^sub>1)) (com.Seq (Basic (\<lfloor>ncmp b\<rfloor>)) (lift\<^sub>c c\<^sub>2)))" |
    "lift\<^sub>c (While b I c) = (com.Seq ((com.Seq (Basic (\<lfloor>cmp b\<rfloor>)) (lift\<^sub>c c))*) (Basic (\<lfloor>ncmp b\<rfloor>)))" | 
    "lift\<^sub>c (DoWhile I c b) = (lift\<^sub>c c ;; Basic (\<lfloor>cmp b\<rfloor>))* ;; lift\<^sub>c c ;; Basic (\<lfloor>ncmp b\<rfloor>)" 

text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

text \<open>Correctness of the guarantee check\<close>
lemma com_guar:
  "wellformed R G \<Longrightarrow> guar\<^sub>c c G \<Longrightarrow> \<forall>\<beta>\<in>basics (lift\<^sub>c c). guar\<^sub>\<alpha> \<beta> (step G)"
proof (induct c) 
  case (Op v p)
  then show ?case by (cases p) (auto simp: liftg_def guar_def wp\<^sub>r_def)
qed (auto simp: guar_def reflexive_def liftl_def step_def)

interpretation rules fwd\<^sub>s re\<^sub>a by (unfold_locales) (auto)

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
  where "rules_abv \<equiv> rules"

abbreviation lifted_abv ("_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,20] 20)
  where "lifted_abv R G P c Q \<equiv> step\<^sub>t R,step G \<turnstile> P {lift\<^sub>c c} Q"

abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0] 45) 
  where "validity_abv c P R G Q \<equiv> validity (lift\<^sub>c c) P (step\<^sub>t R) (step G) Q"

text \<open>An ordering property on contexts\<close>
definition context_order 
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv> 
    (stable\<^sub>t R Q \<and> wellformed R G) \<longrightarrow> ((P \<subseteq> Q) \<and> stable\<^sub>t R P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness\<close>
definition valid 
  ("_,_ \<turnstile>\<^sub>w _ {_} _" [100,0,0,0,100] 60)
  where "valid R G P c Q \<equiv>  
    (wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c c G) \<longrightarrow> (stable\<^sub>t R P \<and> (R,G \<turnstile>\<^sub>s P {c} Q))"

section \<open>Soundness\<close>

text \<open>Basic Rule for operations with vc\<close>
lemma basic_wp\<^sub>i_1:
  assumes "P \<subseteq> stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q))" "wellformed R G" "stable\<^sub>t R Q" 
  assumes "c \<subseteq> guar (wp\<^sub>i \<alpha> o wp\<^sub>a f) (step G)"
  shows "step\<^sub>t R,step G \<turnstile> P {Basic (\<lfloor>c, \<alpha>, f\<rfloor>)} Q"
proof -
  have "step\<^sub>t R,step G \<turnstile>\<^sub>A stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q)) {\<lfloor>c, \<alpha>, f\<rfloor>} Q"
    using assms by (cases \<alpha>) (auto simp: atomic_rule_def guar_def wp_def step_def 
                                         wp\<^sub>r_def o_def liftg_def elim!: stabilizeE)
  thus ?thesis using assms by (intro conseq[OF basic]) (auto)
qed

text \<open>Basic Rule for operations\<close>
lemma basic_wp\<^sub>i_2:
  assumes "P \<subseteq> stabilize R (wp\<^sub>i \<alpha> Q)" "wellformed R G" "stable\<^sub>t R Q"
  assumes "\<forall>m. m \<in> guar (wp\<^sub>i \<alpha>) (step G)"
  shows "step\<^sub>t R,step G \<turnstile> P {Basic (\<lfloor>\<alpha>\<rfloor>)} Q"
proof -
  have "step\<^sub>t R,step G \<turnstile>\<^sub>A stabilize R (wp\<^sub>i \<alpha> Q) {\<lfloor>\<alpha>\<rfloor>} Q"
    using assms by (cases \<alpha>) (auto simp: atomic_rule_def guar_def wp_def step_def 
                                         wp\<^sub>r_def o_def liftl_def elim!: stabilizeE)
  thus ?thesis using assms by (intro conseq[OF basic]) (auto simp:)
qed

text \<open>A rule for cmp operations, used for If/While\<close>
lemma cmp_sound [intro!]:
  assumes "wellformed R G" "stable\<^sub>t R Q"
  assumes "P \<subseteq> stabilize R (wp\<^sub>i (cmp b) Q)"
  shows "step\<^sub>t R,step G \<turnstile> P {Basic (\<lfloor>cmp b\<rfloor>)} Q"
  using assms by (intro basic_wp\<^sub>i_2) (auto simp: step_def reflexive_def wp\<^sub>r_def)

subsection \<open>State Ordering\<close>

text \<open>Properties of the state ordering. Essentially entailment with preservation of stability\<close>

text \<open>The ordering is reflexive\<close>
lemma refl_ord:
  "R,G \<turnstile>\<^sub>w P \<ge> P"
  unfolding context_order_def by (auto simp: )

text \<open>It is possible to strengthen the RHS\<close>
lemma assert_ord:
  "R,G \<turnstile>\<^sub>w P \<inter> assert A \<ge> P"
  by (cases A) (auto simp: context_order_def assert_def) 

text \<open>Stabilize Ordering\<close>
lemma stabilize_ord [intro]:
  assumes "P \<subseteq> Q" 
  shows "R,G \<turnstile>\<^sub>w stabilize R P \<ge> Q"
  using assms stabilizeE unfolding context_order_def 
  by blast

subsection \<open>Rules\<close>

text \<open>If Rule\<close>
lemma if_wp:
  "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w stabilize R (wp\<^sub>i (cmp b) P\<^sub>1 \<inter> wp\<^sub>i (ncmp b) P\<^sub>2) {If b c\<^sub>1 c\<^sub>2} Q"
  unfolding valid_def apply clarsimp apply (intro conjI rules.choice rules.seq, auto )
  apply (rule stabilize_entail, auto)+
  done

text \<open>While Rule\<close>
lemma while_wp:
  assumes "R,G \<turnstile>\<^sub>w P {c} stabilize R J" (is "R,G \<turnstile>\<^sub>w P {c} ?I")
  assumes "J \<subseteq>  (wp\<^sub>i (cmp b) P \<inter> wp\<^sub>i (ncmp b) Q)"
  shows "R,G \<turnstile>\<^sub>w ?I {While b J c} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI rules.choice rules.seq)
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (While b J c) (G)"
  thus "step\<^sub>t R,step G \<turnstile> ?I {(Basic (\<lfloor>cmp b\<rfloor>) ;; lift\<^sub>c c)*} ?I"
    using assms 
    apply (intro rules.loop rules.seq, unfold valid_def)
    apply force
    apply force
    apply (auto simp:)
    apply (rule stabilize_entail, auto)+
    done
qed (insert assms, auto, rule stabilize_entail)

text \<open>Do While Rule\<close>
lemma do_wp:
  assumes "R,G \<turnstile>\<^sub>w stabilize R J {c} stabilize R (wp\<^sub>i (cmp b) (stabilize R J) \<inter> (wp\<^sub>i (ncmp b) Q))" (is "R,G \<turnstile>\<^sub>w ?I {c} ?Q")
  shows "R,G \<turnstile>\<^sub>w stabilize R J {DoWhile J c b} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI rules.choice rules.seq)
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (DoWhile J c b) (G)"
  thus "step\<^sub>t R,step G \<turnstile> ?I {lift\<^sub>c c} ?Q" 
    using assms by (auto simp: valid_def) 
next
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (DoWhile J c b) (G)"
  thus "step\<^sub>t R,step G \<turnstile> ?I {(lift\<^sub>c c ;; Basic (\<lfloor>cmp b\<rfloor>))*} ?I"
    using assms 
    apply (intro rules.loop rules.seq)
    defer 1
    apply auto[1]
    apply (auto)[1]
    apply (auto)
    unfolding valid_def
    by (simp add: rules.intros(8) stabilize_entail stabilize_stable subsetI)
qed (insert assms, auto, rule stabilize_entail, auto)

text \<open>False Rule\<close>
lemma false_wp:
  assumes "P = {}"
  shows "R,G \<turnstile>\<^sub>w P {c} Q"
  using assms unfolding valid_def
  by (intro conjI impI com_guar rules.conseq[OF falseI, where ?G="step G"]) (auto)

text \<open>Rewrite Rule\<close>
lemma rewrite_wp:
  "R,G \<turnstile>\<^sub>w P {c} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w M \<ge> P \<Longrightarrow> R,G \<turnstile>\<^sub>w M {c} Q"
  by (auto simp: valid_def context_order_def)

text \<open>Assert Rule\<close>
lemma assert_wp:
  assumes "A \<Longrightarrow> R,G \<turnstile>\<^sub>w P {c} Q"
  shows "R,G \<turnstile>\<^sub>w (P \<inter> assert A) {c} Q"
proof (cases A)
  case True
  then show ?thesis using assms by (intro rewrite_wp[OF _ assert_ord], simp)
next
  case False
  then show ?thesis by (intro false_wp, auto simp: assert_def)
qed 

text \<open>Com Rule\<close>
theorem com_wp:
  shows "R,G \<turnstile>\<^sub>w wp R c Q {c} Q" 
proof (induct c arbitrary: Q)
  case Skip
  then show ?case by (auto simp: valid_def)
next
  case (Op x1 x2)
  then show ?case unfolding valid_def lift\<^sub>c.simps 
    by (intro conjI impI basic_wp\<^sub>i_1) auto
next
  case (Seq c1 c2)
  then show ?case by (auto simp: valid_def)
next
  case (If x1 c1 c2)
  then show ?case unfolding wp.simps by (blast intro: if_wp)
next
  case (While x1 x2 c)
  then show ?case unfolding wp.simps by (intro assert_wp impI while_wp) (auto)
next
  case (DoWhile I c b)
  thus ?case unfolding wp.simps by (intro assert_wp do_wp; rule rewrite_wp) auto
qed

subsection \<open>High-Level Theorem\<close>

text \<open>Soundness lemma for WP reasoning\<close>
theorem armv8_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" 
  assumes st: "stable\<^sub>t R Q" 
  assumes g: "guar\<^sub>c c G"
  assumes P: "P \<subseteq> wp R c Q"
  shows "\<Turnstile> c SAT [P, R, G, Q]"
proof -
  have "R,G \<turnstile>\<^sub>s wp R c Q {c} Q" using wf st g com_wp unfolding valid_def by blast
  hence "R,G \<turnstile>\<^sub>s P {c} Q" by (rule rules.conseq) (insert P, auto simp: )
  thus ?thesis by (intro sound thread) auto
qed

end