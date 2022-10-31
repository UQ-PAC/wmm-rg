theory ARMv8_Rules    
  imports "../Security" ARMv8 "HOL-Eisbach.Eisbach"
begin

section \<open>Wellformedness\<close>

definition stabilize
  where "stabilize R P \<equiv> {m. \<forall>m'. (glb m,glb m') \<in> R \<longrightarrow> rg m = rg m' \<longrightarrow> m' \<in> P}"

definition reflexive
  where "reflexive R \<equiv> \<forall>m. (m,m) \<in> R"

definition transitive
  where "transitive R \<equiv> \<forall>m m' m''. (m,m') \<in> R \<longrightarrow> (m',m'') \<in> R \<longrightarrow> (m,m'') \<in> R"

definition assert
  where "assert b \<equiv> {m. b}"

text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step\<^sub>t :: "('v,'a) grel \<Rightarrow> ('v,'r,'a) trel"
  where "step\<^sub>t R \<equiv> {(m,m'). (glb m, glb m') \<in> R \<and> rg m = rg m'}"

text \<open>Lift a relational predicate\<close>
definition step :: "('v,'a) grel \<Rightarrow> ('v,'r,'a) trel"
  where "step R \<equiv> {(m,m'). (glb m, glb m') \<in> R}"

text \<open>Define stability in terms of a relational predicate that preserves the thread state\<close>
abbreviation stable\<^sub>t
  where "stable\<^sub>t R P \<equiv> stable (step\<^sub>t R) P"

text \<open>Lift an invariant to a relation\<close>
definition inv :: "(('v,'a) gstate set) \<Rightarrow> ('v,'a) grel"
  where "inv I \<equiv> {(m,m'). m \<in> I \<longrightarrow> m' \<in> I}"

text \<open>Convert a global predicate into a thread local predicate by ignoring the local state\<close>
definition all\<^sub>t :: "(('v,'a) gstate set) \<Rightarrow> ('v,'r,'a) pred"
  where "all\<^sub>t I \<equiv> {m. (glb m) \<in> I}"

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

text \<open>Transform a predicate based on a sub-operation\<close>  (*pred transformer Q \<longrightarrow>  wp c Q *)
fun wp\<^sub>i :: "('v,'r) subop \<Rightarrow> ('v,'r,'a) trans" 
  where 
    "wp\<^sub>i (load v e) Q = {m. st m (Glb v) = ev\<^sub>E (rg m) e \<longrightarrow> m \<in> Q}" | 
    "wp\<^sub>i (cstore b v e) Q = {m. ev\<^sub>B (rg m) b \<longrightarrow> (m(Glb v :=\<^sub>s ev\<^sub>E (rg m) e)) \<in> Q}" | 
    "wp\<^sub>i (op r e) Q = {m. m(Reg r :=\<^sub>s ev\<^sub>E (rg m) e) \<in> Q}" |
    "wp\<^sub>i (cmp b) Q = {m. ev\<^sub>B (rg m) b \<longrightarrow> m \<in> Q}" | 
    "wp\<^sub>i (cas\<^sub>T v e\<^sub>1 e\<^sub>2) Q = {m. st m (Glb v) = ev\<^sub>E (rg m) e\<^sub>1 \<longrightarrow> m(Glb v :=\<^sub>s ev\<^sub>E (rg m) e\<^sub>2) \<in> Q}" | 
    "wp\<^sub>i (cas\<^sub>F v e\<^sub>1) Q = {m. st m (Glb v) \<noteq> ev\<^sub>E (rg m) e\<^sub>1 \<longrightarrow> m \<in> Q}" | 
    "wp\<^sub>i _ Q = Q"

(* m(Glb v :=\<^sub>s ev\<^sub>E (rg m) e) is syntax for updating the state:
      m \<lparr> st := ((st m) (Glb v := ev\<^sub>E (rg m) e)) \<rparr>  -- see ARMv8_State.thy
*)

text \<open>Transform a predicate based on an auxiliary state update\<close>
fun wp\<^sub>a :: "('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) trans"
  where "wp\<^sub>a a Q = {m. (m(aux: a)) \<in> Q}"            
  (* m(aux: a) is the syntax for updating the more in m to a:
                         m\<lparr>state_rec.more := a m\<rparr>           *)


(* Instructions are syntactic and don't refer to state, used in wpre and wp *) 
datatype ('v,'r,'a) insts =
  ld "('v,'r,'a) pred" "('v,'r) exp" 'r "('v,'r,'a) auxfn"
  | sr "('v,'r,'a) pred" "('v,'r) bexp" "('v,'r) exp" 'r "('v,'r,'a) auxfn"
  | ir 'r "('v,'r) exp" 
  | cm "('v,'r) bexp"
  | ncm "('v,'r) bexp"
  | env "('v,'a) grel"                                         (* env step *)
  | cs "('v,'r,'a) pred" 'r 'r 'r 'r 'v 'v "('v,'r,'a) auxfn"  (* cas inst *)

text \<open>Transform a predicate based on a successful CAS instruction\<close>
abbreviation wp_CAS\<^sub>T :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) trans"
  where "wp_CAS\<^sub>T v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q \<equiv> 
    {m. m \<in> v \<and> (st m (Glb (rg m r\<^sub>a)) = st m (Reg r\<^sub>1) \<longrightarrow> (m(Glb (rg m r\<^sub>a) :=\<^sub>s rg m r\<^sub>2, Reg r :=\<^sub>s T, aux: a)) \<in> Q)}"

text \<open>Transform a predicate based on a failed CAS instruction\<close>
abbreviation wp_CAS\<^sub>F :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) trans"
  where "wp_CAS\<^sub>F v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q \<equiv> 
    {m. m \<in> v \<and> (st m (Glb (rg m r\<^sub>a)) \<noteq> st m (Reg r\<^sub>1) \<longrightarrow> (m(Reg r :=\<^sub>s F, aux: a)) \<in> Q)}"

fun wpre :: "('v,'r,'a) insts \<Rightarrow> ('v,'r,'a) trans"
  where
    "wpre (ld v r\<^sub>a r a) Q = {m. m \<in> v \<and> (m (Reg r :=\<^sub>s st m (Glb (ev\<^sub>E (rg m) r\<^sub>a)), aux: a)) \<in> Q}" |
    "wpre (sr v b r\<^sub>a r a) Q = {m. m \<in> v \<and> (ev\<^sub>B (rg m) b \<longrightarrow> (m (Glb (ev\<^sub>E (rg m) r\<^sub>a) :=\<^sub>s rg m r, aux: a)) \<in> Q)}" |
    "wpre (ir r e) Q = wp\<^sub>i (op r e) Q" |
    "wpre (cm b) Q = wp\<^sub>i (cmp b) Q" |
    "wpre (ncm b) Q = wp\<^sub>i (ncmp b) Q" |
    "wpre (env R) Q = stabilize R Q" |
    "wpre (cs v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) Q = wp_CAS\<^sub>T v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q \<inter> wp_CAS\<^sub>F v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a Q"
 
text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "('v,'a) grel \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> ('v,'r,'a) trans"
  where
    "wp R Skip Q = Q" |
    "wp R Fence Q = Q" |
    "wp R (Load v d r\<^sub>a r a) Q = stabilize R (wpre (ld (v \<inter> {m. ev\<^sub>E (rg m) r\<^sub>a \<in> d}) r\<^sub>a r a) Q)" |
    "wp R (Store v d r\<^sub>a r a) Q = stabilize R (wpre (sr  (v \<inter> {m. ev\<^sub>E (rg m) r\<^sub>a \<in> d}) True\<^sub>B r\<^sub>a r a) Q)" |
    "wp R (Op r e) Q = wpre (ir r e) Q" |
    "wp R (CAS v d r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) Q = stabilize R (wpre (cs (v \<inter> {m. rg m r\<^sub>a \<in> d}) r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) Q)" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = (wpre (cm b) (wp R c\<^sub>1 Q) \<inter> wpre (ncm b) (wp R c\<^sub>2 Q))"

text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "('v,'r,'a) trans \<Rightarrow> ('v,'r,'a) rtrans"
  where "wp\<^sub>r f G \<equiv> {(m,m'). m' \<in> f {m'. (m,m') \<in> G}}"

subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar
  where "guar f G \<equiv> {m. (m,m) \<in> (wp\<^sub>r f G)}"

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c (Load v d r\<^sub>a r a) G = (v \<inter> {m. ev\<^sub>E (rg m) r\<^sub>a \<in> d} \<subseteq> guar (wpre (ld UNIV r\<^sub>a r a)) (step G))" |
    "guar\<^sub>c (Store v d r\<^sub>a r a) G = (v \<inter> {m. ev\<^sub>E (rg m) r\<^sub>a \<in> d} \<subseteq> guar (wpre (sr UNIV True\<^sub>B r\<^sub>a r a)) (step G))" |
    "guar\<^sub>c (CAS v d r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) G = (v \<inter> {m. (rg m) r\<^sub>a \<in> d} \<subseteq> guar (wpre (cs UNIV r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a)) (step G))" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If b c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c _ _ = True"

section \<open>Locale Interpretation\<close>

text \<open>Convert the ARMv8 language into the abstract language expected by the underlying logic\<close> 

fun lift\<^sub>c :: "(('v,'r,'a) auxop, ('v,'r,'a) state) wmm \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> (('v,'r,'a) auxop, ('v,'r,'a) state) com"
  where
    "lift\<^sub>c w Skip = com.Nil" |
    "lift\<^sub>c w Fence = Basic (\<lfloor>fence\<rfloor>)" |
    "lift\<^sub>c w (Op r e) = Basic (\<lfloor>op r e\<rfloor>)" |
    "lift\<^sub>c w (Seq c\<^sub>1 c\<^sub>2) = (lift\<^sub>c c\<^sub>1);\<^sub>w (lift\<^sub>c c\<^sub>2)"  
(*  #1 and#2 are temp registers which are captured/hidden through \<forall>\<^sub>c operator; the command
     to be captured is a sequence of subops which can potentially reorder: guard; upd; upd *)
(*    "lift\<^sub>c (Load c d r\<^sub>a r a) = \<forall>\<^sub>c ([#1 = r\<^sub>a] ;\<^sub>w #2 := glb(#1) ;\<^sub>w r := #2 )" | 
    "lift\<^sub>c (Store c d r\<^sub>a r a) = \<Sqinter> {[
      \<lfloor>eq r\<^sub>a (Val v\<^sub>a)\<rfloor>, 
      \<lfloor>{m. ev\<^sub>E (rg m) r\<^sub>a = v\<^sub>a} \<inter> c,cstore True\<^sub>B v\<^sub>a (Var r), a\<rfloor>] |v\<^sub>a. v\<^sub>a \<in> d}" |
    "lift\<^sub>c (CAS c d r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) = (Choice
      (\<Sqinter> {[
        \<lfloor>eq (Var r\<^sub>a) (Val v\<^sub>a)\<rfloor>, 
        \<lfloor>{m. rg m r\<^sub>a = v\<^sub>a} \<inter> c,cas\<^sub>T v\<^sub>a (Var r\<^sub>1) (Var r\<^sub>2),(\<lambda>m. a (m(Reg r :=\<^sub>s T)))\<rfloor>, 
        \<lfloor>op r (Val T)\<rfloor>] |v\<^sub>a. v\<^sub>a \<in> d})
      (\<Sqinter> {[
        \<lfloor>eq (Var r\<^sub>a) (Val v\<^sub>a)\<rfloor>, 
        \<lfloor>{m. rg m r\<^sub>a = v\<^sub>a} \<inter> c,cas\<^sub>F v\<^sub>a (Var r\<^sub>1),(\<lambda>m. a (m(Reg r :=\<^sub>s F)))\<rfloor>, 
        \<lfloor>op r (Val F)\<rfloor>] |v\<^sub>a. v\<^sub>a \<in> d}))" |
    "lift\<^sub>c (If b c\<^sub>1 c\<^sub>2) = (Choice 
      (com.Seq (Basic (\<lfloor>cmp b\<rfloor>)) (lift\<^sub>c c\<^sub>1)) 
      (com.Seq (Basic (\<lfloor>ncmp b\<rfloor>)) (lift\<^sub>c c\<^sub>2)))" *)
*)

(* these two dummy parameters used in the interpretation of rules 
    and help to instantiate the types of auxop and state for ARMv8 *)

abbreviation "someAuxOp ::('v,'r,'a) auxop  \<equiv> undefined"
abbreviation "someState :: ('v,'r,'a) state \<equiv> undefined" 

interpretation rules "someAuxOp" "someState" by (unfold_locales) 

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
  where "rules_abv \<equiv> rules"

abbreviation lifted_abv ("_,_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,0,20] 20)
  where "lifted_abv R G I P c Q \<equiv> step\<^sub>t (inv I \<inter> R),step (inv I \<inter> G) \<turnstile> all\<^sub>t I \<inter> P {lift\<^sub>c c} all\<^sub>t I \<inter> Q"

abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _, _]" [60,0,0,0,0] 45) 
  where "validity_abv c P R G Q I \<equiv> validity (lift\<^sub>c c) (all\<^sub>t I \<inter> P) (step\<^sub>t (inv I \<inter> R)) (step (inv I \<inter> G)) (all\<^sub>t I \<inter> Q)"

text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

text \<open>Correctness of the guarantee check\<close>
lemma com_guar:
  "wellformed R G \<Longrightarrow> guar\<^sub>c c G \<Longrightarrow> \<forall>\<beta>\<in>basics (lift\<^sub>c c). guar\<^sub>\<alpha> \<beta> (step G)"
  by (induct c) (auto simp: guar_def step_def reflexive_def wp\<^sub>r_def liftl_def liftg_def)
 
text \<open>An ordering property on contexts\<close>
definition context_order 
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv> 
    (stable\<^sub>t R Q \<and> wellformed R G) \<longrightarrow> ((P \<subseteq> Q) \<and> stable\<^sub>t R P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness\<close>
definition valid :: "('v,'a) grel \<Rightarrow> ('v,'a) grel \<Rightarrow> ('v,'a) gpred \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> bool"
  ("_,_,_ \<turnstile>\<^sub>w _ {_} _" [100,0,0,0,0,100] 60)
  where "valid R G I P c Q \<equiv>  
    (wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c c (inv I \<inter> G)) \<longrightarrow> (stable\<^sub>t R P \<and> (R,G,I \<turnstile>\<^sub>s P {c} Q))"

section \<open>Soundness\<close>

subsection \<open>Sub-operations\<close>

lemma stable\<^sub>t_local_op [intro!]:
  assumes "stable\<^sub>t R Q" 
  shows "stable\<^sub>t R {m. (m(Reg r :=\<^sub>s f (rg m))) \<in> Q}"
  using assms by (auto simp: stable_def step\<^sub>t_def)

lemma stable\<^sub>t_local_cmp [intro!]:
  "stable\<^sub>t R Q \<Longrightarrow> stable\<^sub>t R {m. f (rg m) \<longrightarrow> m \<in> Q}"
  by (auto simp add: stable_def step\<^sub>t_def)

fun local_op
  where
    "local_op (load _ _) = False" |
    "local_op (cstore _ _ _) = False" |
    "local_op (cas\<^sub>T _ _ _) = False" |
    "local_op (cas\<^sub>F _ _) = False" |
    "local_op _ = True"

lemma [intro]:
  "(m,m) \<in> inv I"
  by (auto simp: inv_def)

lemma [intro!]:
  "stable\<^sub>t R Q \<Longrightarrow> stable\<^sub>t ({(m, m'). m \<in> I \<longrightarrow> m' \<in> I} \<inter> R) ({m. glb m \<in> I} \<inter> Q)"
  by (auto simp: stable_def step\<^sub>t_def inv_def)

lemma [intro!]:
  "stable\<^sub>t R Q \<Longrightarrow> stable\<^sub>t (inv I \<inter> R) (all\<^sub>t I \<inter> Q)"
  by (auto simp: stable_def step\<^sub>t_def inv_def all\<^sub>t_def)

lemma [intro!]:
  "reflexive G \<Longrightarrow> reflexive (inv I \<inter> G)"
  by (auto simp: reflexive_def inv_def)

text \<open>Basic Rule for global operations\<close>
lemma basic_wp\<^sub>i_global:
  assumes "P \<subseteq> stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a a Q))" "wellformed R G" "stable\<^sub>t R Q" 
  assumes "c \<subseteq> guar (wp\<^sub>i \<alpha> o wp\<^sub>a a) (step (inv I \<inter> G))"
  shows "step\<^sub>t (inv I \<inter> R),step (inv I \<inter> G) \<turnstile> all\<^sub>t I \<inter> P {Basic (\<lfloor>c, \<alpha>, a\<rfloor>)} all\<^sub>t I \<inter> Q"
proof -
  have "step\<^sub>t (inv I \<inter> R),step (inv I \<inter> G) \<turnstile>\<^sub>A all\<^sub>t I \<inter> stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a a Q)) {\<lfloor>c, \<alpha>, a\<rfloor>} all\<^sub>t I \<inter> Q"
    using assms by (cases \<alpha>) (auto simp: atomic_rule_def guar_def wp_def 
                                         step_def wp\<^sub>r_def o_def liftg_def all\<^sub>t_def inv_def
                                   elim!: stabilizeE)
  thus ?thesis using assms by (intro conseq[OF basic]) (auto)
qed

text \<open>Basic Rule for local operations\<close>
lemma basic_wp\<^sub>i_local:
  assumes "P \<subseteq> wp\<^sub>i \<alpha> Q" "wellformed R G" "stable\<^sub>t R Q" "local_op \<alpha>" 
  shows "step\<^sub>t (inv I \<inter> R),step (inv I \<inter> G) \<turnstile> all\<^sub>t I \<inter> P {Basic (\<lfloor>\<alpha>\<rfloor>)} all\<^sub>t I \<inter> Q"
proof -
  have "step\<^sub>t (inv I \<inter> R),step (inv I \<inter> G) \<turnstile>\<^sub>A  all\<^sub>t I \<inter> wp\<^sub>i \<alpha> Q {\<lfloor>\<alpha>\<rfloor>} all\<^sub>t I \<inter> Q"
    using assms by (cases \<alpha>) (auto simp: atomic_rule_def guar_def wp_def reflexive_def
                                         step_def liftl_def all\<^sub>t_def inv_def
                                         elim!: stabilizeE)
  thus ?thesis using assms by (intro conseq[OF basic]) (auto)
qed

text \<open>Automation to assist with Load/Store/CAS\<close>
lemma stabilize_cmp:
  "P \<subseteq> wp\<^sub>i (cmp b) Q \<Longrightarrow> stabilize R P \<subseteq> wp\<^sub>i (cmp b) (stabilize R Q)"
  by (auto simp: stabilize_def)

method expand_seq =
  (clarsimp, intro rules.choice rules.seqset; (clarsimp, intro rules.ord, (auto)[1]))

method basic_wp\<^sub>i = 
  ((rule basic_wp\<^sub>i_local | rule basic_wp\<^sub>i_global), 
   (rule stabilize_cmp | rule subset_refl); 
   auto simp: wp\<^sub>r_def step_def)

text \<open>A rule for cmp operations, used for If/While/DoWhile\<close>
lemma cmp_sound [intro!]:
  assumes "wellformed R G" "stable\<^sub>t R Q"
  assumes "P \<subseteq> wp\<^sub>i (cmp b) Q"
  shows "step\<^sub>t (inv I \<inter> R),step (inv I \<inter> G) \<turnstile> all\<^sub>t I \<inter> P {Basic (\<lfloor>cmp b\<rfloor>)} all\<^sub>t I \<inter> Q"
  using assms by (intro basic_wp\<^sub>i_local) auto

subsection \<open>State Ordering\<close>

text \<open>Properties of the state ordering. Essentially entailment with preservation of stability\<close>

text \<open>The ordering is reflexive\<close>
lemma refl_ord:
  "R,G \<turnstile>\<^sub>w P \<ge> P"
  unfolding context_order_def by auto

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
  "R,G,I \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q \<Longrightarrow> R,G,I \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q \<Longrightarrow> R,G,I \<turnstile>\<^sub>w wp\<^sub>i (cmp b) P\<^sub>1 \<inter> wp\<^sub>i (ncmp b) P\<^sub>2 {If b c\<^sub>1 c\<^sub>2} Q"
  unfolding valid_def by clarsimp (intro conjI rules.choice rules.seq, auto)

text \<open>False Rule\<close>
lemma false_wp:
  assumes "P \<subseteq> {}"
  shows "R,G,I \<turnstile>\<^sub>w P {c} Q"
  using assms unfolding valid_def
  by (intro conjI impI com_guar rules.conseq[OF falseI, where ?G="step (inv I \<inter> G)"]) (auto)

text \<open>Rewrite Rule\<close>
lemma rewrite_wp:
  "R,G,I \<turnstile>\<^sub>w P {c} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w M \<ge> P \<Longrightarrow> R,G,I \<turnstile>\<^sub>w M {c} Q"
  by (auto simp: valid_def context_order_def)

text \<open>Assert Rule\<close>
lemma assert_wp:
  assumes "A \<Longrightarrow> R,G,I \<turnstile>\<^sub>w P {c} Q"
  shows "R,G,I \<turnstile>\<^sub>w (P \<inter> assert A) {c} Q"
proof (cases A)
  case True
  then show ?thesis using assms by (intro rewrite_wp[OF _ assert_ord], simp)
next
  case False
  then show ?thesis by (intro false_wp, auto simp: assert_def)
qed 

lemma [simp]:
  "m(aux: \<lambda>m. f (m(x :=\<^sub>s e)), x :=\<^sub>s e) = m(x :=\<^sub>s e, aux: f)"
  by (auto simp: aux_upd_def st_upd_def)

text \<open>Com Rule\<close>
theorem com_wp:
  shows "R,G,I \<turnstile>\<^sub>w wp R c Q {c} Q" 
proof (induct c arbitrary: Q)
  case Fence
  thus ?case unfolding valid_def lift\<^sub>c.simps by (intro conjI impI basic_wp\<^sub>i_local) auto
next
  case (Op r e)
  thus ?case unfolding valid_def lift\<^sub>c.simps 
    by (intro conjI impI basic_wp\<^sub>i_local) (auto)
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
qed (auto simp: valid_def)

subsection \<open>High-Level Theorem\<close>

text \<open>Soundness lemma for WP reasoning over ARMv8\<close>
theorem armv8_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" 
  assumes st: "stable\<^sub>t R Q" 
  assumes g: "guar\<^sub>c c (inv I \<inter> G)"
  assumes P: "P \<subseteq> wp R c Q"
  shows "\<Turnstile> c SAT [P, R, G, Q, I]"
proof -
  have "R,G,I \<turnstile>\<^sub>s wp R c Q {c} Q" using wf st g com_wp unfolding valid_def by blast
  hence "R,G,I \<turnstile>\<^sub>s P {c} Q" by (rule rules.conseq) (insert P, auto)
  thus ?thesis by (intro sound thread) auto
qed

end