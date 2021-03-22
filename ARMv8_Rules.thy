theory ARMv8_Rules
  imports Refine ARMv8 
begin

named_theorems pred_defs
definition conj  (infixr "\<and>\<^sub>p" 35)
  where "conj l r \<equiv> \<lambda>m. (l m) \<and> (r m)"
definition entail (infix "\<turnstile>\<^sub>p" 25)
  where "entail P Q \<equiv> \<forall>m. P m \<longrightarrow> Q m"
definition assert
  where "assert b \<equiv> \<lambda>m. b"
declare assert_def [pred_defs]
declare entail_def [pred_defs]
declare conj_def [pred_defs]
definition stabilize 
  where "stabilize R P \<equiv> \<lambda>m. \<forall>m'. R m m' \<longrightarrow> P m'"
definition reflexive 
  where "reflexive R \<equiv> \<forall>m . R m  m"
definition transitive 
  where "transitive R \<equiv> \<forall>m m' m''. R m m' \<longrightarrow> R m' m'' \<longrightarrow> R m m''"

section \<open>Predicate Transformations\<close>

text \<open>Transform a predicate based on an instruction\<close>
fun wp\<^sub>i :: "('v,'r,'g) inst \<Rightarrow> ('v,'r,'g) pred \<Rightarrow> ('v,'r,'g) pred" 
  where 
    "wp\<^sub>i (Store x r) Q = (\<lambda>m. Q (m (x :=\<^sub>1 rg r m)))" | 
    "wp\<^sub>i (Load r x) Q = (\<lambda>m. Q (m (r :=\<^sub>2 ld x m)))" | 
    "wp\<^sub>i (Op r\<^sub>t f r\<^sub>1 r\<^sub>2) Q = (\<lambda>m. Q (m (r\<^sub>t :=\<^sub>2 f (rg r\<^sub>1 m) (rg r\<^sub>2 m))))" |
    "wp\<^sub>i (Cond f r) Q = (\<lambda>m. (f (rg r m)) \<longrightarrow> Q m)" | 
    "wp\<^sub>i _ Q = Q"

fun wp\<^sub>s  :: "('v,'r,'g) ispec \<Rightarrow> ('v,'r,'g) pred \<Rightarrow> ('v,'r,'g) pred"
  where
    "wp\<^sub>s (p,\<alpha>) Q = (p \<and>\<^sub>p wp\<^sub>i \<alpha> Q)"

text \<open>The WP predicate transformer given a rely R and guarantee G\<close>
fun wp :: "('v,'r,'g) rpred \<Rightarrow> ('v,'r,'g) rpred \<Rightarrow> ('v,'r,'g) lang \<Rightarrow> ('v,'r,'g) pred \<Rightarrow> ('v,'r,'g) pred"
  where
    "wp R G Skip Q = Q" |
    "wp R G (Inst \<alpha>) Q = stabilize R (wp\<^sub>s \<alpha> Q)" |
    "wp R G (Seq c\<^sub>1 c\<^sub>2) Q = wp R G c\<^sub>1 (wp R G c\<^sub>2 Q)" |
    "wp R G (If f r c\<^sub>1 c\<^sub>2) Q = stabilize R (wp\<^sub>i (Cond f r) (wp R G c\<^sub>1 Q) \<and>\<^sub>p 
                                           wp\<^sub>i (NCond f r) (wp R G c\<^sub>2 Q))" |
    "wp R G (While f r I c) Q = (stabilize R I \<and>\<^sub>p
                                (assert (I \<turnstile>\<^sub>p (wp\<^sub>i (Cond f r) (wp R G c (stabilize R I))) \<and>\<^sub>p 
                                              wp\<^sub>i (NCond f r) Q)))"

text \<open>Convert a state predicate into the shallow-embedding\<close>
definition state
  where "state P \<equiv> {(m). P m}"

text \<open>Convert a state relation into the shallow-embedding\<close>
definition step
  where "step P \<equiv> {((m),(m')). P m m'}"

section \<open>Wellformedness\<close>

text \<open>Couple all wellformedness conditions into a single definition\<close>
definition wellformed :: "('v,'r,'g) rpred \<Rightarrow> ('v,'r,'g) rpred \<Rightarrow> ('v,'r,'g) pred \<Rightarrow> bool"
  where "wellformed R G Q \<equiv> 
    stable (step R) (state Q)  \<and> reflexive R \<and> transitive R \<and> reflexive G" 

lemma G_refl [intro]:
  assumes wf: "wellformed R G Q"
  shows "G m m" 
  using wf unfolding wellformed_def reflexive_def by blast

text \<open>Establish wellformedness of a false predicate\<close>
lemma wf_false:
  "\<forall>m. \<not> P m \<Longrightarrow> wellformed R G Q \<Longrightarrow> wellformed R G P"
  unfolding wellformed_def stable_def by (auto simp: state_def)

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G P"
  shows "stable (step R) (state (stabilize R Q))"
  unfolding stable_def state_def step_def
proof (clarsimp)
  fix m m'
  assume a: "(stabilize R Q) m" "R m m'"
  have "\<forall>m''. R m' m'' \<longrightarrow> R m m''"
    using assms a(2) unfolding wellformed_def transitive_def by blast
  thus "(stabilize R Q) m'" using a(1) by (auto simp: stabilize_def)
qed

text \<open>Stabilization preserves wellformedness\<close>
lemma stabilize_wellformed [intro]:
  assumes "wellformed R G P"
  shows "wellformed R G (stabilize R Q)" (is "wellformed R G ?P")
proof -
  have "stable (step R) (state ?P)" 
    using stabilize_stable assms by blast
  thus ?thesis using assms unfolding wellformed_def by blast
qed

text \<open>WP preserves wellformedness\<close>
lemma wellformed_actI [intro]:
  assumes "wellformed R G Q"
  shows "wellformed R G (wp R G (Inst \<alpha>) Q)"
  using assms wellformed_def by auto

text \<open>Elimination rule to ignore the stabilization process\<close>
lemma stabilizeE:
  assumes "stabilize R P m"
  assumes "wellformed R G Q"
  obtains "P m"
  using assms unfolding wellformed_def reflexive_def stabilize_def by blast

section \<open>Program Wellformedness\<close>

text \<open>We require all instructions in a program to conform to the guarantee\<close>

text \<open>Compute the verification condition necessary for an instruction to conform to a guarantee G\<close>
definition guar\<^sub>i :: "('v,'r,'g) inst \<Rightarrow> ('v,'r,'g) rpred \<Rightarrow> ('v,'r,'g) pred"
  where "guar\<^sub>i i G \<equiv> \<lambda>m. \<forall>m'. (m,m') \<in> beh\<^sub>i i \<longrightarrow> (G m m' \<or> m = m')"

fun guar\<^sub>s :: "('v,'r,'g) ispec \<Rightarrow> ('v,'r,'g) rpred \<Rightarrow> bool"
  where "guar\<^sub>s (p,\<alpha>) G = (p \<turnstile>\<^sub>p guar\<^sub>i \<alpha> G)"

text \<open>Ensure all operations have preconditions strong enough to discharge their guarantee\<close>
fun guar\<^sub>c
  where
    "guar\<^sub>c (Inst \<alpha>) G = guar\<^sub>s \<alpha> G" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If f v c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While f v I c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c _ _ = True"

section \<open>Soundness\<close>

subsection \<open>Interpretation of General Logic\<close>

fun act_ref :: "('v,'r,'g) ispec \<Rightarrow> ('v,'r,'g) ispec \<Rightarrow> bool" 
  where "act_ref (p,\<alpha>) (q,\<beta>) = (\<alpha> = \<beta> \<and> (p \<turnstile>\<^sub>p q))"

interpretation refine vc\<^sub>s beh\<^sub>s fwd\<^sub>s re\<^sub>s act_ref
  by (unfold_locales) (auto simp: pred_defs)

abbreviation lrules_abv ("_,_ \<turnstile>\<^sub>l _ {_} _" [20,0,0,0,20] 20)
  where "lrules_abv \<equiv> lrules"

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
  where "rules_abv \<equiv> rules"

abbreviation lifted_abv ("_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,20] 20)
  where "lifted_abv R G P c Q \<equiv> step R,step G \<turnstile>\<^sub>l state P {lift\<^sub>c c} state Q"

abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45) 
  where "validity_abv c P R G Q \<equiv> validity (lift\<^sub>c c) (state P) (step R) (step G) (state Q)"

text \<open>An ordering property on contexts\<close>
definition context_order 
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv> wellformed R G Q \<longrightarrow> ((P \<turnstile>\<^sub>p Q) \<and> wellformed R G P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness\<close>
definition valid 
  ("_,_ \<turnstile>\<^sub>w _ {_} _" [100,0,0,100] 60)
  where "valid R G P c Q \<equiv> (guar\<^sub>c c G \<and> wellformed R G Q) \<longrightarrow> ((R,G \<turnstile>\<^sub>s P {c} Q) \<and> wellformed R G P)"

subsection \<open>Instruction Soundness\<close>

text \<open>WP correctly transforms the state for an instruction\<close>
lemma wp_sound [intro]:
  assumes wf: "wellformed R G Q" 
  shows "state (stabilize R (wp\<^sub>s \<alpha> Q)) \<subseteq> wp\<^sub>\<alpha> \<alpha> (state Q)"
  using wf by (cases \<alpha>, rename_tac p i, case_tac i) 
              (auto simp add: state_def wp_def pred_defs elim!: stabilizeE)

text \<open>The guar check is correct\<close>
lemma guar_correct [simp]:
  "guar \<alpha> (step G) = guar\<^sub>c (Inst \<alpha>) G"
  by (cases \<alpha>) (auto simp: guar\<^sub>i_def pred_defs step_def)

text \<open>WP soundly computes an instructions weakest precondition\<close>
lemma inst_sound [intro]:
  assumes "wellformed R G Q" "guar\<^sub>c (Inst \<alpha>) G"
  shows "R,G \<turnstile>\<^sub>s wp R G (Inst \<alpha>) Q {Inst \<alpha>} Q"
proof (clarsimp, rule lrules.basic, simp add: atomic_rule_def, intro conjI)
  show "state (stabilize R (wp\<^sub>s \<alpha> Q)) \<subseteq> wp\<^sub>\<alpha> \<alpha> (state Q)" 
    using assms(1) wp_sound by blast
qed (insert assms, auto simp: wellformed_def)

text \<open>Bundle the inst rule with a precondition rewrite\<close>
lemma inst_conseq [intro]:
  assumes "wellformed R G Q" "guar\<^sub>c (Inst \<alpha>) G"
  assumes "P \<turnstile>\<^sub>p wp R G (Inst \<alpha>) Q"
  shows "step R,step G \<turnstile>\<^sub>l state P {Basic \<alpha>} state Q"
  using inst_sound[OF assms(1,2)] apply simp
proof (rule lrules.conseq)
  show "state P \<subseteq> state (wp R G (Inst \<alpha>) Q)"
    using assms(3) by (auto simp: entail_def state_def)
qed auto

subsection \<open>Base Introduction Rules\<close>

text \<open>Reflexive Ordering\<close>
lemma reflOrd [intro]:
  "R,G \<turnstile>\<^sub>w P \<ge> P"
  unfolding context_order_def by (auto simp: pred_defs)

text \<open>Assert Ordering\<close>
lemma assertOrd:
  "R,G \<turnstile>\<^sub>w P \<and>\<^sub>p assert A \<ge> P"
  by (cases A) (auto simp: context_order_def pred_defs intro: wf_false) 

text \<open>Stabilize Ordering\<close>
lemma stabilizeOrd:
  assumes "P \<turnstile>\<^sub>p Q" 
  shows "R,G \<turnstile>\<^sub>w stabilize R P \<ge> Q"
  using assms stabilizeE unfolding context_order_def entail_def
  by blast

text \<open>Skip Rule\<close>
lemma skipWP:
  "R,G \<turnstile>\<^sub>w Q {Skip} Q"
  by (auto simp: context_order_def valid_def wellformed_def)

text \<open>Instruction Rule\<close>
lemma instWP:
  "R,G \<turnstile>\<^sub>w wp R G (Inst \<alpha>) Q {Inst \<alpha>} Q"
  unfolding valid_def using inst_sound[of R G Q \<alpha>] by auto
 
text \<open>Sequential Rule\<close>
lemma seqWP:
  "R,G \<turnstile>\<^sub>w P {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w M {c\<^sub>2} P \<Longrightarrow> R,G \<turnstile>\<^sub>w M {Seq c\<^sub>2 c\<^sub>1} Q"
  unfolding valid_def by auto

lemma guar_cond [simp]:
  "guar\<^sub>i (Cond f r) G = (\<lambda>m. True)"
  by (auto simp add: pred_defs guar\<^sub>i_def)

lemma [simp]:
  "(P \<turnstile>\<^sub>p P) = True"
  by (auto simp add: pred_defs guar\<^sub>i_def)

text \<open>Stabilization preserves entailment\<close>
lemma stabilize_entail [intro]:
  assumes "P \<turnstile>\<^sub>p Q"
  shows "stabilize R P \<turnstile>\<^sub>p stabilize R Q"
  using assms by (clarsimp simp add: entail_def stabilize_def)

text \<open>If Rule\<close>
lemma ifWP:
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q"
  shows "R,G \<turnstile>\<^sub>w stabilize R (wp\<^sub>i (Cond f r) P\<^sub>1 \<and>\<^sub>p wp\<^sub>i (NCond f r) P\<^sub>2) {If f r c\<^sub>1 c\<^sub>2} Q"
  using assms 
  apply (clarsimp simp add: valid_def)
  apply (intro impI conjI lrules.choice lrules.seq stabilize_wellformed; assumption?)
  by (intro inst_conseq; simp; intro stabilize_entail; simp add: pred_defs)+

text \<open>While Rule\<close>
lemma whileWP:
  assumes "I \<turnstile>\<^sub>p wp\<^sub>i (Cond f r) P \<and>\<^sub>p wp\<^sub>i (NCond f r) Q"
  assumes "R,G \<turnstile>\<^sub>w P {c} stabilize R I" (is "R,G \<turnstile>\<^sub>w P {c} ?I")
  shows "R,G \<turnstile>\<^sub>w ?I {While f r I c} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI lrules.choice lrules.seq stabilize_wellformed; assumption?)
  assume "guar\<^sub>c (While f r I c) G \<and> wellformed R G Q"
  thus "step R,step G \<turnstile>\<^sub>l (state ?I) {Basic (VC\<^sub>T (NCond f r))} state Q"
    using assms(1) 
    by (intro inst_conseq; simp; intro stabilize_entail; simp add: pred_defs)
next
  assume "guar\<^sub>c (While f r I c) G \<and> wellformed R G Q"
  hence "guar\<^sub>c c G" "wellformed R G ?I" by auto
  thus "step R,step G \<turnstile>\<^sub>l state ?I {(Basic (VC\<^sub>T (Cond f r)) ; lift\<^sub>c c)*} state ?I"
    using assms
    apply (intro lrules.loop lrules.seq stabilize_stable; simp add: valid_def)
    defer 1
    by blast (intro inst_conseq; simp; intro stabilize_entail; simp add: pred_defs)
qed auto

lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

lemma guar_all:
  "guar\<^sub>c c G \<Longrightarrow> \<forall>\<beta>\<in>basics (lift\<^sub>c c). guar \<beta> (step G)"
  by (induct c) auto

text \<open>False Rule\<close>
lemma falseWP:
  assumes "P \<turnstile>\<^sub>p (\<lambda>m. False)"
  shows "R,G \<turnstile>\<^sub>w P {c} Q"
  using assms unfolding valid_def
  apply (intro conjI impI guar_all lrules.conseq[OF falseI, where ?G="step G"])
  by (auto simp: entail_def state_def intro: wf_false)

text \<open>Precondition Rewrite Rule\<close>
lemma rewriteWP:
  "R,G \<turnstile>\<^sub>w P {c} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w M \<ge> P \<Longrightarrow> R,G \<turnstile>\<^sub>w M {c} Q"
proof (clarsimp simp add: valid_def context_order_def)
  assume a: "M \<turnstile>\<^sub>p P"
  assume "R,G \<turnstile>\<^sub>s P {c} Q "
  thus "R,G \<turnstile>\<^sub>s M {c} Q" by (rule lrules.conseq) (insert a, auto simp: entail_def state_def)
qed

text \<open>Assert Rule\<close>

lemma assertWP:
  assumes "A \<longrightarrow> R,G \<turnstile>\<^sub>w P {c} Q"
  shows "R,G \<turnstile>\<^sub>w (P \<and>\<^sub>p assert A) {c} Q"
proof (cases A)
  case True
  then show ?thesis using assms by (intro rewriteWP[OF _ assertOrd], simp)
next
  case False
  then show ?thesis by (intro falseWP, auto simp: pred_defs)
qed 

subsection \<open>Rewrite Introduction Rules\<close>

text \<open>Skip Rewrite Rule\<close>
lemma skipRW:
  assumes "R,G \<turnstile>\<^sub>w P \<ge> Q" 
  shows "R,G \<turnstile>\<^sub>w P {Skip} Q"
  using rewriteWP[OF skipWP assms] .

text \<open>Act Rewrite Rule\<close>
lemma actRW:
  assumes "R,G \<turnstile>\<^sub>w P \<ge> wp R G (Inst \<alpha>) Q"
  shows "R,G \<turnstile>\<^sub>w P {Inst \<alpha>} Q"
  using rewriteWP[OF instWP assms] .

text \<open>If Rewrite Rule\<close>
lemma ifRW:
  assumes "R,G \<turnstile>\<^sub>w P \<ge> stabilize R (wp\<^sub>i (Cond f r) P\<^sub>1 \<and>\<^sub>p wp\<^sub>i (NCond f r) P\<^sub>2)"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q"
  shows "R,G \<turnstile>\<^sub>w P {If f r c\<^sub>1 c\<^sub>2} Q"
  using rewriteWP[OF ifWP[OF assms(2,3)] assms(1)] . 

text \<open>While Rewrite Rule\<close>
lemma whileRW:
  assumes order: "R,G \<turnstile>\<^sub>w N \<ge> stabilize R I"
  assumes recur: "R,G \<turnstile>\<^sub>w P {c} stabilize R I"
  assumes side: "I \<turnstile>\<^sub>p wp\<^sub>i (Cond f r) P \<and>\<^sub>p wp\<^sub>i (NCond f r) Q"
  shows "R,G \<turnstile>\<^sub>w N {While f r I c} Q"
  using rewriteWP[OF whileWP[OF side recur] order] .

subsection \<open>Soundness\<close>

lemma wp_valid:
  shows "R,G \<turnstile>\<^sub>w wp R G c Q {c} Q" 
proof (induct c arbitrary: Q)
  case Skip
  thus ?case using skipWP by auto
next
  case (Inst \<beta>)
  thus ?case using instWP by blast
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case using seqWP unfolding wp.simps by blast
next
  case (If f r c\<^sub>1 c\<^sub>2)
  thus ?case using ifWP unfolding wp.simps by metis
next
  case (While f r I c)
  thus ?case unfolding wp.simps
    by (intro assertWP impI whileRW) (auto simp add: pred_defs)
qed

text \<open>Soundness lemma for WP reasoning over ARMv8 with verification conditions\<close>
theorem armv8_wp_sound_vc:
  assumes wf: "transitive R" "reflexive R" "reflexive G" 
  assumes st: "stable (step R) (state Q)" 
  assumes g: "guar\<^sub>c c G"
  assumes P: "P \<turnstile>\<^sub>p wp R G c Q"
  assumes i: "inter (step R) (step G) (lift\<^sub>c c)" (* Rephrase this in terms of the ARMv8 analysis *)
  shows "\<Turnstile> c SAT [P, R, G, Q]"
proof -
  have "wellformed R G Q" using wf st by (auto simp: wellformed_def)
  hence "R,G \<turnstile>\<^sub>s wp R G c Q {c} Q" using g wp_valid unfolding valid_def by blast
  hence "R,G \<turnstile>\<^sub>s P {c} Q" by (rule lrules.conseq) (insert P, auto simp: state_def entail_def)
  thus ?thesis using i by (intro sound thread) auto
qed

text \<open>Refine via the elimination of verification conditions\<close>
fun no_vc
  where 
    "no_vc Skip = Skip" |
    "no_vc (Inst (p,\<alpha>)) = Inst (\<lambda>m. True,\<alpha>)" |
    "no_vc (Seq c\<^sub>1 c\<^sub>2) = Seq (no_vc c\<^sub>1) (no_vc c\<^sub>2)" |
    "no_vc (If f r c\<^sub>1 c\<^sub>2) = If f r (no_vc c\<^sub>1) (no_vc c\<^sub>2)" |
    "no_vc (While f r I c) = While f r I (no_vc c)"

text \<open>Prove elimination of verification conditions is a valid refinement\<close>
lemma no_vc_ref:
  "lang_ref (lift\<^sub>c c) (lift\<^sub>c (no_vc c))"
proof (induct c)
  case (Inst x)
  then show ?case by (cases x) (auto simp: pred_defs)
qed auto

text \<open>Soundness lemma for WP reasoning over ARMv8\<close>
theorem armv8_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" 
  assumes st: "stable (step R) (state Q)" 
  assumes g: "guar\<^sub>c c G"
  assumes P: "P \<turnstile>\<^sub>p wp R G c Q"
  assumes i: "inter (step R) (step G) (lift\<^sub>c c)" (* Rephrase this in terms of the ARMv8 analysis *)
  shows "\<Turnstile> (no_vc c) SAT [P, R, G, Q]"
proof -
  have "wellformed R G Q" using wf st by (auto simp: wellformed_def)
  hence "R,G \<turnstile>\<^sub>s wp R G c Q {c} Q" using g wp_valid unfolding valid_def by blast
  hence "R,G \<turnstile>\<^sub>s P {c} Q" by (rule lrules.conseq) (insert P, auto simp: state_def entail_def)
  thus ?thesis using i no_vc_ref by (intro refine_sound thread) auto
qed

end