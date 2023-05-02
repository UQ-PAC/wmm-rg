theory SimAsm_Rules
  imports SimAsm_WP
begin


instantiation state_rec_ext :: (type,type,type) pstate
begin

definition "push_state_rec_ext \<equiv> \<lambda>(l :: ('a, 'b, 'c) state_rec_scheme) (r :: ('a, 'b, 'c) state_rec_scheme). l"

instance (* Need to move some things around at the abstract level to get this through *)
  apply standard
  sorry
end


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
    using assms apply (cases \<alpha>) 
                by (auto simp: atomic_rule_def guar_def wp_def step_def 
                                         wp\<^sub>r_def liftg_def o_def  elim!: stabilizeE) 
  thus ?thesis using assms by (intro conseq[OF basic]) (auto)
qed

text \<open>Basic Rule for operations without vc\<close>
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
  "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q' \<Longrightarrow> R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q' \<Longrightarrow> R,G \<turnstile>\<^sub>w Q' {c\<^sub>3} Q \<Longrightarrow> 
            R,G \<turnstile>\<^sub>w stabilize R (wp\<^sub>s (If b c\<^sub>1 c\<^sub>2 c\<^sub>3) Q) \<inter> 
                    stabilize R (wp\<^sub>i (cmp b) P\<^sub>1 \<inter> wp\<^sub>i (ncmp b) P\<^sub>2) {If b c\<^sub>1 c\<^sub>2 c\<^sub>3} Q"
  unfolding valid_def apply clarsimp 
  apply (intro conjI)
  prefer 2
   apply (intro rules.choice)
   apply (intro allI)
   apply (simp split: if_splits)
   apply (intro conjI impI)
  using cmp_sound rules.rules.seq rules.rules.interr stabilize_entail subsetI 
  sorry
(*            R,G \<turnstile>\<^sub>w stabilize R (wp\<^sub>s c\<^sub>2 (wp\<^sub>s c\<^sub>3 Q) \<inter> wp\<^sub>s c\<^sub>1 (wp\<^sub>s c\<^sub>3 Q)) \<inter>  *)
(*    apply (simp add: cmp_sound rules.rules.seq stabilize_entail subsetI)+  
  by blast 
*)

(*
lemma if_wp:
  "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w stabilize R (wp\<^sub>i (cmp b) P\<^sub>1 \<inter> wp\<^sub>i (ncmp b) P\<^sub>2) {If b c\<^sub>1 c\<^sub>2} Q"
  unfolding valid_def apply clarsimp apply (intro conjI rules.choice rules.seq, auto )
  apply (rule stabilize_entail, auto)+
  done
*)


text \<open>While Rule\<close>
lemma while_wp:
  assumes "R,G \<turnstile>\<^sub>w P {c} stabilize R J" (is "R,G \<turnstile>\<^sub>w P {c} ?I")
  assumes "J \<subseteq>  (wp\<^sub>i (cmp b) P \<inter> wp\<^sub>i (ncmp b) Q)"
  shows "R,G \<turnstile>\<^sub>w ?I {While b J c} Q"
  unfolding valid_def lift\<^sub>c.simps
  sorry
(*
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
*)

text \<open>Do While Rule\<close>
lemma do_wp:
  assumes "R,G \<turnstile>\<^sub>w stabilize R J {c} stabilize R (wp\<^sub>i (cmp b) (stabilize R J) \<inter> (wp\<^sub>i (ncmp b) Q))" (is "R,G \<turnstile>\<^sub>w ?I {c} ?Q")
  shows "R,G \<turnstile>\<^sub>w stabilize R J {DoWhile J c b} Q"
  unfolding valid_def lift\<^sub>c.simps
  sorry
(*
proof (intro impI conjI rules.choice rules.seq)
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (DoWhile J c b) (G)"
  thus "step\<^sub>t R,step G \<turnstile> ?I {lift\<^sub>c c} ?Q" 
    using assms by (auto simp: valid_def) 
next
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (DoWhile J c b) (G)"
  thus "step\<^sub>t R,step G \<turnstile> ?I {(lift\<^sub>c c ;; Basic (\<lfloor>cmp b\<rfloor>))*} ?I"
    using assms
    apply (intro rules.loop rules.seq)
    prefer 2
    apply auto[1]
    apply blast
    unfolding valid_def
    apply (simp add: rules.intros(8) stabilize_entail stabilize_stable subsetI)
    apply (subgoal_tac "stable\<^sub>t R
     (stabilize R
       ({m. ((st_ev\<^sub>B m b) \<longrightarrow> (m \<in> (stabilize R J)))} \<inter>
        {m. ((\<not> (st_ev\<^sub>B m b)) \<longrightarrow> (m \<in> Q))}))")
    apply clarsimp
    apply (rule rules.conseq)
    apply blast
    apply blast
    apply blast
    apply blast
    defer 1
    apply blast
    using stabilize_entail by auto
qed (insert assms, auto, rule stabilize_entail, auto)
*)


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
  shows "validity_abv c P R G Q"
(*  shows "\<Turnstile> c SAT [P, R, G, Q]"  *)
proof -
  have "R,G \<turnstile>\<^sub>s wp R c Q {c} Q" using wf st g com_wp unfolding valid_def by blast
  hence "R,G \<turnstile>\<^sub>s P {c} Q" by (rule rules.conseq) (insert P, auto simp: )
  thus ?thesis by (intro sound thread) auto
qed

end