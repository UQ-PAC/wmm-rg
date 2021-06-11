theory ARMv8_Rules    
  imports "../Soundness" ARMv8 "HOL-Eisbach.Eisbach"
begin

section \<open>Wellformedness\<close>

text \<open>
Abstract theory is in terms of sets of states, where as the WP reasoning uses functions.
This lifting converts to the abstract.
\<close>
abbreviation lift_encoding ("\<langle>_\<rangle>" 1000) 
  where "lift_encoding \<equiv> Collect"

text \<open>Lift an invariant to a relation\<close>
definition inv :: "(('v,'a) gstate \<Rightarrow> bool) \<Rightarrow> ('v,'a) grel"
  where "inv I \<equiv> \<lambda>(m,m'). I m \<longrightarrow> I m'"

text \<open>Convert a global predicate into a thread local predicate by ignoring the local state\<close>
definition all\<^sub>t :: "(('v,'a) gstate \<Rightarrow> bool) \<Rightarrow> ('v,'r,'a) pred"
  where "all\<^sub>t I \<equiv> \<lambda>m. I (glb m)"

text \<open>Lift a relational predicate with no constraint on thread state\<close>
definition step :: "('v,'a) grel \<Rightarrow> ('v,'r,'a) trel"
  where "step R \<equiv> \<lambda>(m,m'). R (glb m, glb m')"

text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step\<^sub>t :: "('v,'a) grel \<Rightarrow> ('v,'r,'a) trel"
  where "step\<^sub>t R \<equiv> \<lambda>(m,m'). R (glb m, glb m') \<and> rg m = rg m'"

text \<open>Define stability in terms of a relational predicate that preserves the thread state\<close>
abbreviation stable\<^sub>t
  where "stable\<^sub>t R P \<equiv> stable \<langle>step\<^sub>t R\<rangle> \<langle>P\<rangle>"

text \<open>Couple all wellformedness conditions into a single definition\<close>
abbreviation wellformed :: "('v,'a) grel \<Rightarrow> ('v,'a) grel \<Rightarrow> bool"
  where "wellformed R G \<equiv> reflexive R \<and> transitive R \<and> reflexive G" 

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G"
  shows "stable\<^sub>t R (stabilize R Q)"
  unfolding stable_def step\<^sub>t_def
proof (clarsimp)
  fix m m'
  assume a: "stabilize R Q m" "R (glb m, glb m')" "rg m = rg m'"
  have "\<forall>g''. R (glb m',g'') \<longrightarrow> R (glb m,g'')"
    using assms a(2) unfolding transitive_def by blast
  thus "stabilize R Q m'" using a(1,3) by (auto simp: stabilize_def set_glb_def)
qed

text \<open>The conjunction of two stable predicates is stable\<close>
lemma stable\<^sub>t_conj [intro]:
  assumes "stable\<^sub>t R P" "stable\<^sub>t R Q"
  shows "stable\<^sub>t R (P \<and>\<^sub>p Q)"
  using assms by (auto simp: stable_def pred_defs)

text \<open>Elimination rule to ignore the stabilization process\<close>
lemma stabilizeE:
  assumes "stabilize R P m"
  assumes "wellformed R G"
  obtains "P m"
proof -
  have "\<forall>g. R (glb m, g) \<longrightarrow> P (set_glb m g)" "R (glb m, glb m)"
    using assms by (auto simp: reflexive_def stabilize_def)
  thus ?thesis using that by auto
qed

text \<open>Stabilization preserves entailment\<close>
lemma stabilize_entail [intro!]:
  assumes "wellformed R G"
  assumes "P \<turnstile>\<^sub>p Q"
  shows "stabilize R P \<turnstile>\<^sub>p Q"
  using assms by (auto simp: pred_defs stabilize_def)

section \<open>Predicate Transformations\<close>

named_theorems wp_defs

text \<open>Transform a predicate based on an sub-operation\<close>
fun wp\<^sub>i :: "('v,'r) subop \<Rightarrow> ('v,'r,'a) trans" 
  where 
    "wp\<^sub>i (load v e) Q = (\<lambda>m. st m v = ev (rg m) e \<longrightarrow> Q m)" | 
    "wp\<^sub>i (store v e) Q = (\<lambda>m. Q (m(v :=\<^sub>s ev (rg m) e)))" | 
    "wp\<^sub>i (op r e) Q = (\<lambda>m. Q (m (r :=\<^sub>r ev (rg m) e)))" |
    "wp\<^sub>i (cmp b) Q = (\<lambda>m. ev\<^sub>B (rg m) b \<longrightarrow> Q m)" | 
    "wp\<^sub>i (cas\<^sub>T v e\<^sub>1 e\<^sub>2) Q = (\<lambda>m. st m v = ev (rg m) e\<^sub>1 \<longrightarrow> Q (m(v :=\<^sub>s ev (rg m) e\<^sub>2)))" | 
    "wp\<^sub>i (cas\<^sub>F v e\<^sub>1 e\<^sub>2) Q = (\<lambda>m. st m v \<noteq> ev (rg m) e\<^sub>1 \<longrightarrow> Q m)" | 
    "wp\<^sub>i _ Q = Q"

text \<open>Transform a predicate based on an auxiliary state update\<close>
fun wp\<^sub>a :: "('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) trans"
  where "wp\<^sub>a a Q = (\<lambda>m. Q (m(aux: a)))"

datatype ('v,'r,'a) insts =
  ld "('v,'r,'a) pred" "('v,'r) exp" 'r "('v,'r,'a) auxfn"
  | sr "('v,'r,'a) pred" "('v,'r) exp" 'r "('v,'r,'a) auxfn"
  | ir 'r "('v,'r) exp" 
  | cm "('v,'r) bexp"
  | ncm "('v,'r) bexp"
  | env "('v,'a) grel"

fun wpre :: "('v,'r,'a) insts \<Rightarrow> ('v,'r,'a) trans"
  where
    "wpre (ld v r\<^sub>a r a) Q = ((\<lambda>m. v m \<and> Q (m (r :=\<^sub>r st m (ev (rg m) r\<^sub>a), aux: a))))" |
    "wpre (sr v r\<^sub>a r a) Q = ( (\<lambda>m. v m \<and> Q (m (ev (rg m) r\<^sub>a :=\<^sub>s rg m r, aux: a))))" |
    "wpre (ir r e) Q = wp\<^sub>i (op r e) Q" |
    "wpre (cm b) Q = wp\<^sub>i (cmp b) Q" |
    "wpre (ncm b) Q = wp\<^sub>i (ncmp b) Q" |
    "wpre (env R) Q = stabilize R Q"

text \<open>Transform a predicate based on a successful CAS instruction\<close>
definition wp_CAS\<^sub>T :: "'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) trans"
  where "wp_CAS\<^sub>T r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q \<equiv> 
    \<lambda>m. st m (rg m r\<^sub>a) = rg m r\<^sub>1 \<longrightarrow> Q (m(rg m r\<^sub>a :=\<^sub>s rg m r\<^sub>2, r :=\<^sub>r T, aux: a))"
declare wp_CAS\<^sub>T_def [wp_defs]

text \<open>Transform a predicate based on a failed CAS instruction\<close>
definition wp_CAS\<^sub>F :: "'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) trans"
  where "wp_CAS\<^sub>F r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q \<equiv> 
    \<lambda>m. st m (rg m r\<^sub>a) \<noteq> rg m r\<^sub>1 \<longrightarrow> Q (m(r :=\<^sub>r F, aux: a))"
declare wp_CAS\<^sub>F_def [wp_defs]

text \<open>Transform a predicate based on a CAS instruction\<close>
definition wp_CAS :: "'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) trans"
  where "wp_CAS r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q \<equiv> wp_CAS\<^sub>T r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q \<and>\<^sub>p wp_CAS\<^sub>F r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q"
declare wp_CAS_def [wp_defs]

text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "('v,'a) grel \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> ('v,'r,'a) trans"
  where
    "wp R Skip Q = Q" |
    "wp R Fence Q = Q" |
    "wp R (Load v r\<^sub>a r a) Q = stabilize R (wpre (ld v r\<^sub>a r a) Q)" |
    "wp R (Store v r\<^sub>a r a) Q = stabilize R (wpre (sr v r\<^sub>a r a) Q)" |
    "wp R (Op r e) Q = wpre (ir r e) Q" |
    "wp R (Test p) Q = stabilize R (p \<longrightarrow>\<^sub>p Q)" |
    "wp R (Assert p) Q = (stabilize R p \<and>\<^sub>p Q)" |
    "wp R (CAS v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) Q = stabilize R (v \<and>\<^sub>p wp_CAS r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q)" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = (wpre (cm b) (wp R c\<^sub>1 Q) \<and>\<^sub>p wpre (ncm b) (wp R c\<^sub>2 Q))" |
    "wp R (While b I c) Q = 
      (stabilize R I \<and>\<^sub>p assert (I \<turnstile>\<^sub>p wp\<^sub>i (cmp b) (wp R c (stabilize R I)) \<and>\<^sub>p wp\<^sub>i (ncmp b) Q))" |
    "wp R (DoWhile I c b) Q = 
      (stabilize R I \<and>\<^sub>p assert (I \<turnstile>\<^sub>p wp R c (wp\<^sub>i (cmp b) (stabilize R I) \<and>\<^sub>p wp\<^sub>i (ncmp b) Q)))"

text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "('v,'r,'a) trans \<Rightarrow> ('v,'r,'a) rtrans"
  where "wp\<^sub>r f G \<equiv> \<lambda>(m,m'). f (\<lambda>m'. G (m,m')) m'"
declare wp\<^sub>r_def [wp_defs]

text \<open>Conditions under which a relational predicate is reflexive\<close>
definition refl :: "('v,'r,'a) trel \<Rightarrow> ('v,'r,'a) pred"
  where "refl G \<equiv> \<lambda>m. G (m,m)"
declare refl_def [wp_defs]

subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar
  where "guar f G \<equiv> refl (wp\<^sub>r f G)"

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c (Load v r\<^sub>a r a) G = (v \<turnstile>\<^sub>p guar (wpre (ld True\<^sub>p r\<^sub>a r a)) (step G))" |
    "guar\<^sub>c (Store v r\<^sub>a r a) G = (v \<turnstile>\<^sub>p guar (wpre (sr True\<^sub>p r\<^sub>a r a)) (step G))" |
    "guar\<^sub>c (CAS v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) G = (v \<turnstile>\<^sub>p guar (wp_CAS r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) (step G))" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If b c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While b I c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c (DoWhile I c b) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c _ _ = True"

section \<open>Locale Interpretation\<close>

text \<open>Convert the ARMv8 language into the abstract language expected by the underlying logic\<close> 
fun lift\<^sub>c :: "('v,'r,'a) com_armv8 \<Rightarrow> (('v,'r,'a) auxop, ('v,'r,'a) tstate) com"
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c Fence = Basic (\<lfloor>fence\<rfloor>)" |
    "lift\<^sub>c (Op r e) = Basic (\<lfloor>op r e\<rfloor>)" |
    "lift\<^sub>c (Load c r\<^sub>a r a) = \<Sqinter> {[
      \<lfloor>eq ( r\<^sub>a) (Val v\<^sub>a)\<rfloor>, 
      \<lfloor>(\<lambda>m. ev (rg m) r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,load v\<^sub>a (Val v), (\<lambda>m. a (m(r :=\<^sub>r v)))\<rfloor>, 
      \<lfloor>op r (Glb v v\<^sub>a)\<rfloor>] |v v\<^sub>a. True}" |
    "lift\<^sub>c (Store c r\<^sub>a r a) = \<Sqinter> {[
      \<lfloor>eq ( r\<^sub>a) (Val v\<^sub>a)\<rfloor>, 
      \<lfloor>(\<lambda>m. ev (rg m) r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,store v\<^sub>a (Reg r), a\<rfloor>] |v\<^sub>a. True}" |
    "lift\<^sub>c (CAS c r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) = (Choice
      (\<Sqinter> {[
        \<lfloor>eq (Reg r\<^sub>a) (Val v\<^sub>a)\<rfloor>, 
        \<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,cas\<^sub>T v\<^sub>a (Reg r\<^sub>1) (Reg r\<^sub>2),(\<lambda>m. a (m(r :=\<^sub>r T)))\<rfloor>, 
        \<lfloor>op r (Glb T v\<^sub>a)\<rfloor>] |v\<^sub>a. True})
      (\<Sqinter> {[
        \<lfloor>eq (Reg r\<^sub>a) (Val v\<^sub>a)\<rfloor>, 
        \<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,cas\<^sub>F v\<^sub>a (Reg r\<^sub>1) (Reg r\<^sub>2),(\<lambda>m. a (m(r :=\<^sub>r F)))\<rfloor>, 
        \<lfloor>op r (Glb F v\<^sub>a)\<rfloor>] |v\<^sub>a. True}))" |
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) = (lift\<^sub>c c\<^sub>1 ;; lift\<^sub>c c\<^sub>2)" |
    "lift\<^sub>c (If b c\<^sub>1 c\<^sub>2) = (Choice 
      (com.Seq (Basic (\<lfloor>cmp b\<rfloor>)) (lift\<^sub>c c\<^sub>1)) 
      (com.Seq (Basic (\<lfloor>ncmp b\<rfloor>)) (lift\<^sub>c c\<^sub>2)))" |
    "lift\<^sub>c (While b I c) = (com.Seq 
      ((com.Seq (Basic (\<lfloor>cmp b\<rfloor>)) (lift\<^sub>c c))*) (Basic (\<lfloor>ncmp b\<rfloor>)))" |
    "lift\<^sub>c (DoWhile I c b) = (com.Seq 
      ((com.Seq (lift\<^sub>c c) (Basic (\<lfloor>cmp b\<rfloor>)))*) (com.Seq (lift\<^sub>c c) (Basic (\<lfloor>ncmp b\<rfloor>))))" |
    "lift\<^sub>c (Test p) = Basic ((nop,tstate_rec.more), UNIV, {(m,m'). m = m' \<and> p m})" |
    "lift\<^sub>c (Assert p) = Basic ((nop,tstate_rec.more), Collect p, Id)"

interpretation rules fwd\<^sub>s re\<^sub>a
  by (unfold_locales) (auto simp: pred_defs)

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
  where "rules_abv \<equiv> rules"

abbreviation lifted_abv ("_,_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,0,20] 20)
  where "lifted_abv R G I P c Q \<equiv> \<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p P\<rangle> {lift\<^sub>c c} \<langle>all\<^sub>t I \<and>\<^sub>p Q\<rangle>"

abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _, _]" [60,0,0,0,0] 45) 
  where "validity_abv c P R G Q I \<equiv> validity (lift\<^sub>c c) \<langle>all\<^sub>t I \<and>\<^sub>p P\<rangle> \<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle> \<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<langle>all\<^sub>t I \<and>\<^sub>p Q\<rangle>"

text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

text \<open>Correctness of the guarantee check\<close>
lemma com_guar:
  "wellformed R G \<Longrightarrow> guar\<^sub>c c G \<Longrightarrow> \<forall>\<beta>\<in>basics (lift\<^sub>c c). guar\<^sub>\<alpha> \<beta> \<langle>step G\<rangle>"
  by (induct c) (auto simp: guar_def step_def reflexive_def wp_defs pred_defs liftl_def liftg_def)

text \<open>An ordering property on contexts\<close>
definition context_order 
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv> 
    (stable\<^sub>t R Q \<and> wellformed R G) \<longrightarrow> ((P \<turnstile>\<^sub>p Q) \<and> stable\<^sub>t R P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness\<close>
definition valid :: "('v,'a) grel \<Rightarrow> ('v,'a) grel \<Rightarrow> ('v,'a) gpred \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> bool"
  ("_,_,_ \<turnstile>\<^sub>w _ {_} _" [100,0,0,0,0,100] 60)
  where "valid R G I P c Q \<equiv>  
    (wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c c (inv I \<and>\<^sub>p G)) \<longrightarrow> (stable\<^sub>t R P \<and> (R,G,I \<turnstile>\<^sub>s P {c} Q))"

section \<open>Soundness\<close>

subsection \<open>Sub-operations\<close>

lemma stable\<^sub>t_local_op [intro!]:
  "stable\<^sub>t R Q \<Longrightarrow> stable\<^sub>t R (\<lambda>m. Q (m\<lparr>rg := f (rg m)\<rparr>))"
  by (auto simp add: stable_def step\<^sub>t_def)

lemma stable\<^sub>t_local_cmp [intro!]:
  "stable\<^sub>t R Q \<Longrightarrow> stable\<^sub>t R (\<lambda>m. f (rg m) \<longrightarrow> Q m)"
  by (auto simp add: stable_def step\<^sub>t_def)

lemma stable\<^sub>t_local_assign [intro!]:
  "stable\<^sub>t R Q \<Longrightarrow> stable\<^sub>t R (\<lambda>m. Q (m(r :=\<^sub>r f (rg m))))"
  unfolding rg_upd_def by auto

fun local_op
  where
    "local_op (load _ _) = False" |
    "local_op (store _ _) = False" |
    "local_op (cas\<^sub>T _ _ _) = False" |
    "local_op (cas\<^sub>F _ _ _) = False" |
    "local_op _ = True"

lemma [intro]:
  "(inv I) (m,m)"
  by (auto simp: inv_def)

lemma [intro!]:
  "stable\<^sub>t R Q \<Longrightarrow> stable\<^sub>t ((\<lambda>(m, m'). I m \<longrightarrow> I m') \<and>\<^sub>p R) (\<lambda>m. I (glb m) \<and> Q m)"
  by (auto simp: stable_def step\<^sub>t_def inv_def)

lemma [intro!]:
  "stable\<^sub>t R Q \<Longrightarrow> stable\<^sub>t (inv I \<and>\<^sub>p R) (all\<^sub>t I \<and>\<^sub>p Q)"
  by (auto simp: stable_def step\<^sub>t_def inv_def all\<^sub>t_def)

lemma [intro!]:
  "reflexive G \<Longrightarrow> reflexive (inv I \<and>\<^sub>p G)"
  by (auto simp: reflexive_def inv_def)

text \<open>Basic Rule for global operations\<close>
lemma basic_wp\<^sub>i_global:
  assumes "P \<turnstile>\<^sub>p stabilize R (c \<and>\<^sub>p wp\<^sub>i \<alpha> (wp\<^sub>a a Q))" "wellformed R G" "stable\<^sub>t R Q" 
  assumes "c \<turnstile>\<^sub>p guar (wp\<^sub>i \<alpha> o wp\<^sub>a a) (step (inv I \<and>\<^sub>p G))"
  shows "\<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p P\<rangle> {Basic (\<lfloor>c, \<alpha>, a\<rfloor>)} \<langle>all\<^sub>t I \<and>\<^sub>p Q\<rangle>"
proof -
  have "\<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile>\<^sub>A \<langle>all\<^sub>t I \<and>\<^sub>p stabilize R (c \<and>\<^sub>p wp\<^sub>i \<alpha> (wp\<^sub>a a Q))\<rangle> {\<lfloor>c, \<alpha>, a\<rfloor>} \<langle>all\<^sub>t I \<and>\<^sub>p Q\<rangle>"
    using assms by (cases \<alpha>) (auto simp: atomic_rule_def guar_def wp_def rg_upd_def 
                                         step_def aux_upd_def pred_defs 
                                         refl_def wp\<^sub>r_def o_def liftg_def all\<^sub>t_def inv_def
                                   elim!: stabilizeE)
  thus ?thesis using assms by (intro conseq[OF basic]) (auto simp: pred_defs)
qed

text \<open>Basic Rule for local operations\<close>
lemma basic_wp\<^sub>i_local:
  assumes "P \<turnstile>\<^sub>p wp\<^sub>i \<alpha> Q" "wellformed R G" "stable\<^sub>t R Q" "local_op \<alpha>" 
  shows "\<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p P\<rangle> {Basic (\<lfloor>\<alpha>\<rfloor>)} \<langle>all\<^sub>t I \<and>\<^sub>p Q\<rangle>"
proof -
  have "\<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile>\<^sub>A  \<langle>all\<^sub>t I \<and>\<^sub>p wp\<^sub>i \<alpha> Q\<rangle> {\<lfloor>\<alpha>\<rfloor>} \<langle>all\<^sub>t I \<and>\<^sub>p Q\<rangle>"
    using assms by (cases \<alpha>) (auto simp: atomic_rule_def guar_def wp_def rg_upd_def 
                                         step_def aux_upd_def pred_defs liftl_def all\<^sub>t_def inv_def
                                         elim!: stabilizeE)
  thus ?thesis using assms by (intro conseq[OF basic]) (auto simp: pred_defs)
qed

text \<open>Automation to assist with Load/Store/CAS\<close>
lemma stabilize_cmp:
  "P \<turnstile>\<^sub>p wp\<^sub>i (cmp b) Q \<Longrightarrow> stabilize R P \<turnstile>\<^sub>p wp\<^sub>i (cmp b) (stabilize R Q)"
  by (auto simp: pred_defs stabilize_def set_glb_def)

method expand_seq =
  (clarsimp, intro rules.choice rules.seqset; (clarsimp, intro rules.ord, (auto)[1]))

method basic_wp\<^sub>i = 
  ((rule basic_wp\<^sub>i_local | rule basic_wp\<^sub>i_global), 
   (rule stabilize_cmp | blast); 
   auto simp: wp_defs pred_defs step_def aux_upd_def)

text \<open>A rule for cmp operations, used for If/While/DoWhile\<close>
lemma cmp_sound [intro!]:
  assumes "wellformed R G" "stable\<^sub>t R Q"
  assumes "P \<turnstile>\<^sub>p wp\<^sub>i (cmp b) Q"
  shows "\<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p P\<rangle> {Basic (\<lfloor>cmp b\<rfloor>)} \<langle>all\<^sub>t I \<and>\<^sub>p Q\<rangle>"
  using assms by (intro basic_wp\<^sub>i_local) auto

subsection \<open>State Ordering\<close>

text \<open>Properties of the state ordering. Essentially entailment with preservation of stability\<close>

text \<open>The ordering is reflexive\<close>
lemma refl_ord:
  "R,G \<turnstile>\<^sub>w P \<ge> P"
  unfolding context_order_def by (auto simp: pred_defs)

text \<open>It is possible to strengthen the RHS\<close>
lemma assert_ord:
  "R,G \<turnstile>\<^sub>w P \<and>\<^sub>p assert A \<ge> P"
  by (cases A) (auto simp: pred_defs context_order_def assert_def) 

text \<open>Stabilize Ordering\<close>
lemma stabilize_ord [intro]:
  assumes "P \<turnstile>\<^sub>p Q" 
  shows "R,G \<turnstile>\<^sub>w stabilize R P \<ge> Q"
  using assms stabilizeE unfolding context_order_def 
  by blast

subsection \<open>Rules\<close>

text \<open>If Rule\<close>
lemma if_wp:
  "R,G,I \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q \<Longrightarrow> R,G,I \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q \<Longrightarrow> R,G,I \<turnstile>\<^sub>w wp\<^sub>i (cmp b) P\<^sub>1 \<and>\<^sub>p wp\<^sub>i (ncmp b) P\<^sub>2 {If b c\<^sub>1 c\<^sub>2} Q"
  unfolding valid_def by clarsimp (intro conjI rules.choice rules.seq, auto simp add: pred_defs)

text \<open>While Rule\<close>
lemma while_wp:
  assumes "R,G,I \<turnstile>\<^sub>w P {c} stabilize R J" (is "R,G,I \<turnstile>\<^sub>w P {c} ?I")
  assumes "J \<turnstile>\<^sub>p wp\<^sub>i (cmp b) P \<and>\<^sub>p wp\<^sub>i (ncmp b) Q"
  shows "R,G,I \<turnstile>\<^sub>w ?I {While b J c} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI rules.choice rules.seq)
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (While b J c) (inv I \<and>\<^sub>p G)"
  thus "\<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p ?I\<rangle> {(Basic (\<lfloor>cmp b\<rfloor>) ;; lift\<^sub>c c)*} \<langle>all\<^sub>t I \<and>\<^sub>p ?I\<rangle>"
    using assms 
    apply (intro rules.loop rules.seq, unfold valid_def)
    apply force
    apply force
    by (auto simp: pred_defs elim!: stabilizeE)
qed (insert assms, auto simp add: pred_defs elim!: stabilizeE)

text \<open>Do While Rule\<close>
lemma do_wp:
  assumes "R,G,I \<turnstile>\<^sub>w stabilize R J {c} (wp\<^sub>i (cmp b) (stabilize R J) \<and>\<^sub>p wp\<^sub>i (ncmp b) Q)" (is "R,G,I \<turnstile>\<^sub>w ?I {c} ?Q")
  shows "R,G,I \<turnstile>\<^sub>w stabilize R J {DoWhile J c b} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI rules.choice rules.seq)
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (DoWhile J c b) (inv I \<and>\<^sub>p G)"
  thus "\<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p ?I\<rangle> {lift\<^sub>c c} \<langle>all\<^sub>t I \<and>\<^sub>p ?Q\<rangle>" 
    using assms by (auto simp: valid_def) 
next
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (DoWhile J c b) (inv I \<and>\<^sub>p G)"
  thus "\<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p ?I\<rangle> {(lift\<^sub>c c ;; Basic (\<lfloor>cmp b\<rfloor>))*} \<langle>all\<^sub>t I \<and>\<^sub>p ?I\<rangle>"
    using assms 
    apply (intro rules.loop seq_rot)
    apply (auto simp: valid_def)[2]
    by (auto simp: pred_defs)
qed (insert assms, auto simp add: pred_defs)

text \<open>False Rule\<close>
lemma false_wp:
  assumes "P \<turnstile>\<^sub>p (\<lambda>m. False)"
  shows "R,G,I \<turnstile>\<^sub>w P {c} Q"
  using assms unfolding valid_def
  by (intro conjI impI com_guar rules.conseq[OF falseI, where ?G="\<langle>step (inv I \<and>\<^sub>p G)\<rangle>"]) (auto simp: pred_defs)

text \<open>Rewrite Rule\<close>
lemma rewrite_wp:
  "R,G,I \<turnstile>\<^sub>w P {c} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w M \<ge> P \<Longrightarrow> R,G,I \<turnstile>\<^sub>w M {c} Q"
  by (auto simp: pred_defs valid_def context_order_def)

text \<open>Assert Rule\<close>
lemma assert_wp:
  assumes "A \<Longrightarrow> R,G,I \<turnstile>\<^sub>w P {c} Q"
  shows "R,G,I \<turnstile>\<^sub>w (P \<and>\<^sub>p assert A) {c} Q"
proof (cases A)
  case True
  then show ?thesis using assms by (intro rewrite_wp[OF _ assert_ord], simp)
next
  case False
  then show ?thesis by (intro false_wp, auto simp: assert_def)
qed 

text \<open>Com Rule\<close>
theorem com_wp:
  shows "R,G,I \<turnstile>\<^sub>w wp R c Q {c} Q" 
proof (induct c arbitrary: Q)
  case Fence
  thus ?case unfolding valid_def lift\<^sub>c.simps by (intro conjI impI basic_wp\<^sub>i_local) auto
next
  case (Op r e)
  thus ?case unfolding valid_def lift\<^sub>c.simps 
    by (intro conjI impI basic_wp\<^sub>i_local) (auto simp: rg_upd_def)
next
  case (Test p)
  thus ?case unfolding valid_def lift\<^sub>c.simps
    by (intro conjI impI rules.basic)
       (auto simp: atomic_rule_def wp_def pred_defs guar_def step_def elim!: stabilizeE)
next
  case (Assert p)
  thus ?case unfolding valid_def lift\<^sub>c.simps
    by (intro conjI impI rules.basic)
       (auto simp: atomic_rule_def wp_def pred_defs guar_def step_def elim!: stabilizeE)
next
  case (Load c r\<^sub>a r a)
  thus ?case unfolding valid_def by (intro conjI impI, force) (expand_seq, basic_wp\<^sub>i+)
next
  case (Store c r\<^sub>a r a)
  thus ?case unfolding valid_def by (intro conjI impI, force) (expand_seq, basic_wp\<^sub>i+)
next
  case (CAS c r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a)
  thus ?case unfolding valid_def by (intro conjI impI, force) (expand_seq, basic_wp\<^sub>i+)
next
  case (If b c\<^sub>1 c\<^sub>2)
  thus ?case unfolding wp.simps wpre.simps by (blast intro: if_wp)
next
  case (While b I c)
  thus ?case unfolding wp.simps by (intro assert_wp impI while_wp) (auto simp: pred_defs)
next
  case (DoWhile I c b)
  thus ?case unfolding wp.simps by (intro assert_wp do_wp; rule rewrite_wp) auto
qed (auto simp: valid_def)

subsection \<open>High-Level Theorem\<close>

text \<open>Soundness lemma for WP reasoning over ARMv8\<close>
theorem armv8_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" 
  assumes st: "stable\<^sub>t R Q" 
  assumes g: "guar\<^sub>c c (inv I \<and>\<^sub>p G)"
  assumes P: "P \<turnstile>\<^sub>p wp R c Q"
  shows "\<Turnstile> c SAT [P, R, G, Q, I]"
proof -
  have "R,G,I \<turnstile>\<^sub>s wp R c Q {c} Q" using wf st g com_wp unfolding valid_def by blast
  hence "R,G,I \<turnstile>\<^sub>s P {c} Q" by (rule rules.conseq) (insert P, auto simp: pred_defs)
  thus ?thesis by (intro sound thread) auto
qed

end