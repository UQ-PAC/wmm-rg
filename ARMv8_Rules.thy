theory ARMv8_Rules
  imports Soundness ARMv8
begin

section \<open>Predicate Transformations\<close>

definition stabilize 
  where "stabilize R P \<equiv> \<lambda>(g,l). \<forall>g'. R g g' \<longrightarrow> P (g',l)"

text \<open>Transform a predicate based on an instruction\<close>
fun wp\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) pred \<Rightarrow> ('v,'r) pred" 
  where 
    "wp\<^sub>i (load addr val) Q = (\<lambda>m. ld m addr = val \<longrightarrow> Q m)" | 
    "wp\<^sub>i (store addr r) Q = (\<lambda>m. Q (m (addr :=\<^sub>1 rg m r)))" | 
    "wp\<^sub>i (op r f rs) Q = (\<lambda>m. Q (m (r :=\<^sub>2 f (map (rg m) rs))))" |
    "wp\<^sub>i (test f rs) Q = (\<lambda>m. f (map (rg m) rs) \<longrightarrow> Q m)" | 
    "wp\<^sub>i _ Q = Q"

text \<open>The WP predicate transformer given a rely R and guarantee G\<close>
fun wp :: "('v,'r) rpred \<Rightarrow> ('v,'r) rpred \<Rightarrow> ('v,'r) lang \<Rightarrow> ('v,'r) pred \<Rightarrow> ('v,'r) pred"
  where
    "wp R G Skip Q = Q" |
    "wp R G (Load v r\<^sub>a r) Q = stabilize R (v \<and>\<^sub>p (\<lambda>m. Q (m (r :=\<^sub>2 ld m (rg m r\<^sub>a)))))" |
    "wp R G (Store v r\<^sub>a r) Q = stabilize R (v \<and>\<^sub>p (\<lambda>m. Q (m (rg m r\<^sub>a :=\<^sub>1 rg m r))))" |
    "wp R G (Op r f rs) Q = wp\<^sub>i (op r f rs) Q" |
    "wp R G (Seq c\<^sub>1 c\<^sub>2) Q = wp R G c\<^sub>1 (wp R G c\<^sub>2 Q)" |
    "wp R G (If f r c\<^sub>1 c\<^sub>2) Q = (wp\<^sub>i (test f r) (wp R G c\<^sub>1 Q) \<and>\<^sub>p wp\<^sub>i (ntest f r) (wp R G c\<^sub>2 Q))" |
    "wp R G (While f r I c) Q = (stabilize R I \<and>\<^sub>p
                                (assert (I \<turnstile>\<^sub>p (wp\<^sub>i (test f r) (wp R G c (stabilize R I))) \<and>\<^sub>p 
                                              wp\<^sub>i (ntest f r) Q)))"

text \<open>Convert a state predicate into the shallow-embedding\<close>
abbreviation state
  where "state P \<equiv> Collect P"

text \<open>Convert a state relation into the shallow-embedding\<close>
definition step\<^sub>R :: "('v,'r) rpred \<Rightarrow> ('v,'r) state rel"
  where "step\<^sub>R P \<equiv> {((g,l),(g',l')). P g g' \<and> l = l'}"

definition step\<^sub>G :: "('v,'r) rpred \<Rightarrow> ('v,'r) state rel"
  where "step\<^sub>G P \<equiv> {((g,l),(g',l')). P g g'}"

section \<open>Wellformedness\<close>

text \<open>Couple all wellformedness conditions into a single definition\<close>
definition wellformed :: "('v,'r) rpred \<Rightarrow> ('v,'r) rpred \<Rightarrow> ('v,'r) pred \<Rightarrow> bool"
  where "wellformed R G Q \<equiv> 
    stable (step\<^sub>R R) (state Q) \<and> reflexive R \<and> transitive R \<and> reflexive G" 

text \<open>Establish wellformedness of a false predicate\<close>
lemma wf_false:
  "\<forall>m. \<not> P m \<Longrightarrow> wellformed R G Q \<Longrightarrow> wellformed R G P"
  unfolding wellformed_def stable_def by (auto)

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G P"
  shows "stable (step\<^sub>R R) (state (stabilize R Q))"
  unfolding stable_def step\<^sub>R_def
proof (clarsimp)
  fix g l g'
  assume a: "(stabilize R Q) (g,l)" "R g g'"
  have "\<forall>g''. R g' g'' \<longrightarrow> R g g''"
    using assms a(2) unfolding wellformed_def transitive_def by blast
  thus "(stabilize R Q) (g',l)" using a(1) by (auto simp: stabilize_def)
qed

text \<open>Stabilization preserves wellformedness\<close>
lemma stabilize_wellformed [intro]:
  assumes "wellformed R G P"
  shows "wellformed R G (stabilize R Q)" (is "wellformed R G ?P")
proof -
  have "stable (step\<^sub>R R) (state ?P)" 
    using stabilize_stable assms by blast
  thus ?thesis using assms unfolding wellformed_def by blast
qed

text \<open>Elimination rule to ignore the stabilization process\<close>
lemma stabilizeE:
  assumes "stabilize R P m"
  assumes "wellformed R G Q"
  obtains "P m"
  using assms unfolding wellformed_def reflexive_def stabilize_def by blast

section \<open>Program Wellformedness\<close>

(*
text \<open>We require all instructions in a program to conform to the guarantee\<close>

text \<open>Compute the verification condition necessary for an instruction to conform to a guarantee G\<close>
definition guar\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) rpred \<Rightarrow> ('v,'r) pred"
  where "guar\<^sub>i i G \<equiv> \<lambda>m. \<forall>m'. (m,m') \<in> beh\<^sub>i i \<longrightarrow> (G (fst m) (fst m') \<or> m = m')"

fun guar\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) rpred \<Rightarrow> bool"
  where "guar\<^sub>s (p,ts,\<alpha>) G = (p \<and>\<^sub>p ts \<turnstile>\<^sub>p guar\<^sub>i \<alpha> G)"
*)

text \<open>Ensure all operations have preconditions strong enough to discharge their guarantee\<close>
fun guar\<^sub>c
  where
    "guar\<^sub>c (Store v r\<^sub>a r) G = (\<forall>m. v m \<longrightarrow> G (fst m) ((fst m)(rg m r\<^sub>a := rg m r)))" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If f v c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While f v I c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c _ _ = True"

section \<open>Soundness\<close>

text \<open>Convert the While language into the com language expected by the underlying logic\<close> 
fun lift\<^sub>c :: "('v,'r) lang \<Rightarrow> (('v,'r) inst,('v,'r) state) com"
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Op r f rs) = Basic (\<lfloor>op r f rs\<rfloor>)" |
    "lift\<^sub>c (Load c r\<^sub>a r) = \<Sqinter> {[\<lfloor>eq r\<^sub>a v\<^sub>a\<rfloor>, \<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,load v\<^sub>a v\<rfloor>, \<lfloor>assign r v\<rfloor>] |v v\<^sub>a. True}" |
    "lift\<^sub>c (Store c r\<^sub>a r) = \<Sqinter> {[\<lfloor>eq r\<^sub>a v\<^sub>a\<rfloor>, \<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,store v\<^sub>a r\<rfloor>] |v\<^sub>a. True}" |
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) = (lift\<^sub>c c\<^sub>1 ; lift\<^sub>c c\<^sub>2)" |
    "lift\<^sub>c (If f r c\<^sub>1 c\<^sub>2) = (Choice (com.Seq (Basic (\<lfloor>test f r\<rfloor>)) (lift\<^sub>c c\<^sub>1)) 
                                    (com.Seq (Basic (\<lfloor>ntest f r\<rfloor>)) (lift\<^sub>c c\<^sub>2)))" |
    "lift\<^sub>c (While f r I c) = (com.Seq ((com.Seq (Basic (\<lfloor>test f r\<rfloor>)) (lift\<^sub>c c))*) 
                                      (Basic (\<lfloor>ntest f r\<rfloor>)))"

subsection \<open>Interpretation of General Logic\<close>

(*
fun act_ref :: "('v,'r) ispec \<Rightarrow> ('v,'r) ispec \<Rightarrow> bool" 
  where "act_ref (p,\<alpha>) (q,\<beta>) = (\<alpha> = \<beta> \<and> (p \<turnstile>\<^sub>p q))"

fun re\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) ispec \<Rightarrow> bool" 
  where "re\<^sub>s (_,\<alpha>) (_,\<beta>) = re\<^sub>i \<alpha> \<beta>" 
*)

interpretation rules fwd\<^sub>s re\<^sub>i
  by (unfold_locales) (auto simp: pred_defs)

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
  where "rules_abv \<equiv> rules"

abbreviation lifted_abv ("_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,20] 20)
  where "lifted_abv R G P c Q \<equiv> step\<^sub>R R,step\<^sub>G G \<turnstile> state P {lift\<^sub>c c} state Q"

abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45) 
  where "validity_abv c P R G Q \<equiv> validity (lift\<^sub>c c) (state P) (step\<^sub>R R) (step\<^sub>G G) (state Q)"

text \<open>An ordering property on contexts\<close>
definition context_order 
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv> wellformed R G Q \<longrightarrow> ((P \<turnstile>\<^sub>p Q) \<and> wellformed R G P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness\<close>
definition valid 
  ("_,_ \<turnstile>\<^sub>w _ {_} _" [100,0,0,100] 60)
  where "valid R G P c Q \<equiv> (guar\<^sub>c c G \<and> wellformed R G Q) \<longrightarrow> ((R,G \<turnstile>\<^sub>s P {c} Q) \<and> wellformed R G P)"

subsection \<open>Instruction Soundness\<close>

lemma load_sound:
  assumes "wellformed R G Q"
  shows "R,G \<turnstile>\<^sub>s wp R G (Load c r\<^sub>a r) Q {Load c r\<^sub>a r} Q"
proof (clarsimp simp del: beh\<^sub>i.simps, rule rules.seqset, clarsimp simp del: beh\<^sub>i.simps, intro rules.ord rules.basic)
  show "step\<^sub>R R,step\<^sub>G G \<turnstile> state Q {Nil} state Q" using assms by (auto simp: wellformed_def)
next
  fix v
  show "step\<^sub>R R,step\<^sub>G G \<turnstile>\<^sub>A (state (wp\<^sub>i (assign r v) Q)) {\<lfloor>assign r v\<rfloor>} state Q"
    unfolding atomic_rule_def
    apply (intro conjI)    
       apply (clarsimp simp add: wp_def)
    using assms 
    apply (clarsimp simp add: step\<^sub>G_def pair_upd2_def wellformed_def reflexive_def guar_def)
    using assms
    apply (clarsimp simp add: step\<^sub>G_def pair_upd2_def wellformed_def stable_def step\<^sub>R_def)
    apply (metis (full_types) snd_conv)
    using assms
    apply (clarsimp simp add: step\<^sub>G_def pair_upd2_def wellformed_def stable_def step\<^sub>R_def)
    done
next
  fix v v\<^sub>a
  show "step\<^sub>R R,step\<^sub>G G \<turnstile>\<^sub>A 
          (state (stabilize R ((\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c \<and>\<^sub>p wp\<^sub>i (load v\<^sub>a v) (wp\<^sub>i (assign r v) Q)))) 
          {\<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c, load v\<^sub>a v\<rfloor>} state (wp\<^sub>i (assign r v) Q)"
    unfolding atomic_rule_def
    apply (intro conjI)
    using assms
    apply (auto simp: wp_def pred_defs guar_def elim!: stabilizeE)
    apply (clarsimp simp add: step\<^sub>G_def pair_upd2_def wellformed_def reflexive_def stable_def step\<^sub>R_def)
    apply (clarsimp simp add: step\<^sub>G_def pair_upd2_def wellformed_def reflexive_def stable_def step\<^sub>R_def)
    apply (metis (full_types) snd_conv)
    done
next
  fix v v\<^sub>a
  show "step\<^sub>R R,step\<^sub>G G \<turnstile>\<^sub>A 
        (state
          (stabilize R
            (c \<and>\<^sub>p (\<lambda>m. Q (m(r :=\<^sub>2 ld m (rg m r\<^sub>a)))))))
        {\<lfloor>eq r\<^sub>a v\<^sub>a\<rfloor>}
        (state (stabilize R ((\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c \<and>\<^sub>p wp\<^sub>i (load v\<^sub>a v) (wp\<^sub>i (assign r v) Q))))"
    unfolding atomic_rule_def
    apply (intro conjI)
    using assms
    apply (auto simp: guar_def step\<^sub>G_def wp_def pred_defs)
    apply (auto simp: stabilize_def)
    apply (auto simp: wellformed_def reflexive_def)
    done
qed

lemma store_sound:
  assumes "wellformed R G Q" "guar\<^sub>c (Store c r\<^sub>a r) G"
  shows "R,G \<turnstile>\<^sub>s wp R G (Store c r\<^sub>a r) Q {Store c r\<^sub>a r} Q"
proof (clarsimp simp del: beh\<^sub>i.simps, rule rules.seqset, clarsimp simp del: beh\<^sub>i.simps, intro rules.ord rules.basic)
  show "step\<^sub>R R,step\<^sub>G G \<turnstile> state Q {Nil} state Q" using assms by (auto simp: wellformed_def)
next
  fix v\<^sub>a
  show "step\<^sub>R R,step\<^sub>G G \<turnstile>\<^sub>A 
          (state (stabilize R (((\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c) \<and>\<^sub>p wp\<^sub>i (store v\<^sub>a r) Q)))
          {\<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,store v\<^sub>a r\<rfloor>} state Q"
    unfolding atomic_rule_def
    apply (intro conjI)    
    using assms
    apply (auto simp: wp_def pred_defs step\<^sub>G_def pair_upd1_def guar_def elim!: stabilizeE split: if_splits)
    apply (subgoal_tac "(a(b r\<^sub>a := b r)) = (\<lambda>x. if x = b r\<^sub>a then rg (a, b) r else ld (a, b) x)")
    apply force
    apply auto[1]
    by (auto simp: wellformed_def)
next
  fix v\<^sub>a
  show "step\<^sub>R R,step\<^sub>G G \<turnstile>\<^sub>A 
        state (stabilize R (c \<and>\<^sub>p (\<lambda>m. Q (m (rg m r\<^sub>a :=\<^sub>1 rg m r)))))
        {\<lfloor>eq r\<^sub>a v\<^sub>a\<rfloor>}
        (state (stabilize R (((\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c) \<and>\<^sub>p wp\<^sub>i (store v\<^sub>a r) Q)))"
    unfolding atomic_rule_def
    apply (intro conjI)
    using assms
    apply (auto simp: guar_def wp_def pred_defs)
    by (auto simp: stabilize_def step\<^sub>G_def wellformed_def reflexive_def)
qed    

lemma op_sound:
  assumes "wellformed R G Q"
  shows "R,G \<turnstile>\<^sub>s wp R G (Op r f rs) Q {Op r f rs} Q"
  apply (clarsimp, rule rules.basic, simp add: atomic_rule_def, intro conjI)
  using assms
  apply (auto simp: wp_def pred_defs step\<^sub>G_def guar_def pair_upd2_def wellformed_def reflexive_def)
  apply (auto simp: stable_def step\<^sub>R_def)
  by (metis snd_conv)


(*
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
*)

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

(*
text \<open>Instruction Rule\<close>
lemma instWP:
  "R,G \<turnstile>\<^sub>w wp R G (Inst \<alpha>) Q {Inst \<alpha>} Q"
  unfolding valid_def using inst_sound[of R G Q \<alpha>] by auto
 *)

text \<open>Sequential Rule\<close>
lemma seqWP:
  "R,G \<turnstile>\<^sub>w P {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w M {c\<^sub>2} P \<Longrightarrow> R,G \<turnstile>\<^sub>w M {Seq c\<^sub>2 c\<^sub>1} Q"
  unfolding valid_def by auto

(*
lemma guar_cond [simp]:
  "guar\<^sub>i (Cond f r) G = (\<lambda>m. True)"
  by (auto simp add: pred_defs guar\<^sub>i_def)
*)

lemma [simp]:
  "(P \<turnstile>\<^sub>p P) = True"
  by (auto simp add: pred_defs)

lemma [simp]:
  "(PTrue \<and>\<^sub>p PTrue) = PTrue"
  by (auto simp: pred_defs)

text \<open>Stabilization preserves entailment\<close>
lemma stabilize_entail [intro]:
  assumes "P \<turnstile>\<^sub>p Q"
  shows "stabilize R P \<turnstile>\<^sub>p stabilize R Q"
  using assms by (clarsimp simp add: entail_def stabilize_def)

lemma stabilize_entail' [intro]:
  assumes "wellformed R G Z"
  assumes "P \<turnstile>\<^sub>p Q"
  shows "stabilize R P \<turnstile>\<^sub>p Q"
  using assms
  by (clarsimp simp add: entail_def stabilize_def wellformed_def stable_def step\<^sub>R_def reflexive_def)

lemma test_sound:
  assumes "wellformed R G Q"
  assumes "P \<turnstile>\<^sub>p wp\<^sub>i (test f rs) Q"
  shows "step\<^sub>R R,step\<^sub>G G \<turnstile> state P {Basic (\<lfloor>test f rs\<rfloor>)} state Q"
  apply (rule rules.conseq[of "step\<^sub>R R" "step\<^sub>G G" "state (wp\<^sub>i (test f rs) Q)" _ "state Q"])
  apply (rule rules.basic)
  unfolding atomic_rule_def
  apply (intro conjI)
  apply (clarsimp simp: wp_def)
  using assms apply (clarsimp simp: guar_def wellformed_def reflexive_def step\<^sub>G_def)
  using assms apply (auto simp: wellformed_def step\<^sub>R_def stable_def)[2]
  using assms(2) apply (clarsimp simp: pred_defs)[1]
  by auto

text \<open>If Rule\<close>
lemma ifWP:
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q"
  shows "R,G \<turnstile>\<^sub>w (wp\<^sub>i (test f r) P\<^sub>1 \<and>\<^sub>p wp\<^sub>i (ntest f r) P\<^sub>2) {If f r c\<^sub>1 c\<^sub>2} Q"
  using assms
  unfolding valid_def
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro impI conjI rules.choice rules.seq stabilize_wellformed; assumption?)
  apply (rule test_sound; simp)
  apply (simp add: pred_defs)
  apply (rule test_sound; simp)
  apply (simp add: pred_defs)
  unfolding wellformed_def
  apply simp
  by (auto simp: stable_def step\<^sub>R_def pred_defs)

text \<open>While Rule\<close>
lemma whileWP:
  assumes "I \<turnstile>\<^sub>p wp\<^sub>i (test f r) P \<and>\<^sub>p wp\<^sub>i (ntest f r) Q"
  assumes "R,G \<turnstile>\<^sub>w P {c} stabilize R I" (is "R,G \<turnstile>\<^sub>w P {c} ?I")
  shows "R,G \<turnstile>\<^sub>w ?I {While f r I c} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI rules.choice rules.seq stabilize_wellformed; assumption?)
  assume "guar\<^sub>c (While f r I c) G \<and> wellformed R G Q"
  thus "step\<^sub>R R,step\<^sub>G G \<turnstile> (state ?I) {Basic (\<lfloor>ntest f r\<rfloor>)} state Q"
    using assms(1) by (intro test_sound; simp; intro stabilize_entail'; simp add: pred_defs)
next
  assume "guar\<^sub>c (While f r I c) G \<and> wellformed R G Q"
  hence "guar\<^sub>c c G" "wellformed R G ?I" by auto
  thus "step\<^sub>R R,step\<^sub>G G \<turnstile> state ?I {(Basic (\<lfloor>test f r\<rfloor>) ; lift\<^sub>c c)*} state ?I"
    using assms
    apply (intro rules.loop rules.seq stabilize_stable; unfold valid_def)
    apply blast
    defer 1
    apply blast
    apply (intro test_sound; simp; intro stabilize_entail'; simp add: pred_defs)
    done
qed auto

lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

lemma guar_all:
  "wellformed R G Q \<Longrightarrow> guar\<^sub>c c G \<Longrightarrow> \<forall>\<beta>\<in>basics (lift\<^sub>c c). guar\<^sub>\<alpha> \<beta> (step\<^sub>G G)"
  apply (induct c) 
  apply (auto simp: guar_def step\<^sub>G_def pair_upd1_def pair_upd2_def pred_defs wellformed_def reflexive_def)
  apply (subgoal_tac "G ab (ab(ba x2 := ba x3))")
  apply (subgoal_tac "(ab(ba x2 := ba x3)) = (\<lambda>x. if x = ba x2 then rg (ab, ba) x3 else ld (ab,ba) x)")
  apply simp
  apply auto
  done

text \<open>False Rule\<close>
lemma falseWP:
  assumes "P \<turnstile>\<^sub>p (\<lambda>m. False)"
  shows "R,G \<turnstile>\<^sub>w P {c} Q"
  using assms unfolding valid_def
  apply (intro conjI impI guar_all rules.conseq[OF falseI, where ?G="step\<^sub>G G"])
  by (auto simp: entail_def intro: wf_false)

text \<open>Precondition Rewrite Rule\<close>
lemma rewriteWP:
  "R,G \<turnstile>\<^sub>w P {c} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w M \<ge> P \<Longrightarrow> R,G \<turnstile>\<^sub>w M {c} Q"
proof (clarsimp simp add: valid_def context_order_def)
  assume a: "M \<turnstile>\<^sub>p P"
  assume "R,G \<turnstile>\<^sub>s P {c} Q "
  thus "R,G \<turnstile>\<^sub>s M {c} Q" by (rule rules.conseq) (insert a, auto simp: entail_def)
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

(*
text \<open>Act Rewrite Rule\<close>
lemma actRW:
  assumes "R,G \<turnstile>\<^sub>w P \<ge> wp R G (Inst \<alpha>) Q"
  shows "R,G \<turnstile>\<^sub>w P {Inst \<alpha>} Q"
  using rewriteWP[OF instWP assms] .
*)

text \<open>If Rewrite Rule\<close>
lemma ifRW:
  assumes "R,G \<turnstile>\<^sub>w P \<ge> (wp\<^sub>i (test f r) P\<^sub>1 \<and>\<^sub>p wp\<^sub>i (ntest f r) P\<^sub>2)"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q"
  shows "R,G \<turnstile>\<^sub>w P {If f r c\<^sub>1 c\<^sub>2} Q"
  using rewriteWP[OF ifWP[OF assms(2,3)] assms(1)] . 

text \<open>While Rewrite Rule\<close>
lemma whileRW:
  assumes order: "R,G \<turnstile>\<^sub>w N \<ge> stabilize R I"
  assumes recur: "R,G \<turnstile>\<^sub>w P {c} stabilize R I"
  assumes side: "I \<turnstile>\<^sub>p wp\<^sub>i (test f r) P \<and>\<^sub>p wp\<^sub>i (ntest f r) Q"
  shows "R,G \<turnstile>\<^sub>w N {While f r I c} Q"
  using rewriteWP[OF whileWP[OF side recur] order] .

subsection \<open>Soundness\<close>

lemma wellformed_op:
  assumes "wellformed R G Q"
  shows "wellformed R G (ARMv8_Rules.wp R G (Op x1 x2 x3) Q)"
  using assms unfolding wellformed_def
  apply (auto simp: stable_def step\<^sub>R_def pair_upd2_def)
  by (metis snd_conv) 

lemma wp_valid:
  shows "R,G \<turnstile>\<^sub>w wp R G c Q {c} Q" 
proof (induct c arbitrary: Q)
  case Skip
  thus ?case using skipWP by auto
next
  case (Load)
  thus ?case using load_sound by (auto simp: valid_def) 
next
  case (Store)
  thus ?case using store_sound by (auto simp: valid_def) 
next
  case (Op)
  thus ?case using op_sound wellformed_op unfolding valid_def by metis
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case using seqWP unfolding wp.simps by blast
next
  case (If f r c\<^sub>1 c\<^sub>2)
  thus ?case using ifWP unfolding wp.simps by blast
next
  case (While f r I c)
  thus ?case unfolding wp.simps
    by (intro assertWP impI whileRW) (auto simp add: pred_defs)
qed

text \<open>Soundness lemma for WP reasoning over ARMv8\<close>
theorem armv8_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" 
  assumes st: "stable (step\<^sub>R R) (state Q)" 
  assumes g: "guar\<^sub>c c G"
  assumes P: "P \<turnstile>\<^sub>p wp R G c Q"
  assumes i: "inter (step\<^sub>R R) (step\<^sub>G G) (lift\<^sub>c c)" (* Rephrase this in terms of the ARMv8 analysis *)
  shows "\<Turnstile> c SAT [P, R, G, Q]"
proof -
  have "wellformed R G Q" using wf st by (auto simp: wellformed_def)
  hence "R,G \<turnstile>\<^sub>s wp R G c Q {c} Q" using g wp_valid unfolding valid_def by blast
  hence "R,G \<turnstile>\<^sub>s P {c} Q" by (rule rules.conseq) (insert P, auto simp: entail_def)
  thus ?thesis using i by (intro sound thread) auto
qed

end