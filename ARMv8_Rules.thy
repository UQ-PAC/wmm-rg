theory ARMv8_Rules
  imports Soundness ARMv8
begin

section \<open>Predicate Transformations\<close>

definition glb :: "('v,'r,'a) tstate_scheme \<Rightarrow> ('v,'a) gstate_scheme"
  where "glb m \<equiv> \<lparr> st = st m, \<dots> = more m \<rparr>"

definition set_glb :: "('v,'r,'a) tstate_scheme \<Rightarrow> ('v,'a) gstate_scheme \<Rightarrow> ('v,'r,'a) tstate_scheme"
  where "set_glb m g \<equiv> \<lparr> st = st g, rg = rg m, \<dots> = gstate.more g \<rparr>"

definition stabilize :: "('v,'a) rpred \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred"
  where "stabilize R P \<equiv> \<lambda>m. \<forall>g. R (glb m,g) \<longrightarrow> P (set_glb m g)"

definition aux_upd
  where "aux_upd a \<equiv> \<lambda>m. m\<lparr>tstate.more := a m\<rparr>"

text \<open>Transform a predicate based on an instruction\<close>
fun wp\<^sub>i :: "('v,'r,'a) inst \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred" 
  where 
    "wp\<^sub>i (load v e a) Q = (\<lambda>m. st m v = ev (rg m) e \<longrightarrow> Q (aux_upd a m))" | 
    "wp\<^sub>i (store v e a) Q = (\<lambda>m. Q (aux_upd a (m(v :=\<^sub>s ev (rg m) e))))" | 
    "wp\<^sub>i (op r e) Q = (\<lambda>m. Q (m (r :=\<^sub>r ev (rg m) e)))" |
    "wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) Q = (\<lambda>m. f (ev (rg m) e\<^sub>1) (ev (rg m) e\<^sub>2) \<longrightarrow> Q m)" | 
    "wp\<^sub>i (cas\<^sub>T v e\<^sub>1 e\<^sub>2 a) Q = (\<lambda>m. st m v = ev (rg m) e\<^sub>1 \<longrightarrow> Q (aux_upd a (m(v :=\<^sub>s ev (rg m) e\<^sub>2))))" | 
    "wp\<^sub>i (cas\<^sub>F v e\<^sub>1 e\<^sub>2 a) Q = (\<lambda>m. st m v \<noteq> ev (rg m) e\<^sub>1 \<longrightarrow> Q (aux_upd a m))" | 
    "wp\<^sub>i _ Q = Q"

fun guar\<^sub>i
  where
    "guar\<^sub>i (load v e a) G = (\<lambda>m. st m v = ev (rg m) e \<longrightarrow> G (glb m,glb (aux_upd a m)))" |
    "guar\<^sub>i (store v e a) G = (\<lambda>m. G (glb m,glb (aux_upd a (m(v :=\<^sub>s ev (rg m) e)))))" |
    "guar\<^sub>i (cas\<^sub>T v e\<^sub>1 e\<^sub>2 a) G = 
      (\<lambda>m. st m v = ev (rg m) e\<^sub>1 \<longrightarrow> G (glb m,glb (aux_upd a (m(v :=\<^sub>s ev (rg m) e\<^sub>2)))))" | 
    "guar\<^sub>i (cas\<^sub>F v e\<^sub>1 e\<^sub>2 a) G = 
      (\<lambda>m. st m v \<noteq> ev (rg m) e\<^sub>1 \<longrightarrow> G (glb m,glb (aux_upd a m)))" | 
    "guar\<^sub>i _ _ = (\<lambda>m. True)"

definition step\<^sub>R :: "('v,'a) rpred \<Rightarrow> ('v,'r,'a) tstate_scheme rel"
  where "step\<^sub>R R \<equiv> {(m,m'). R (glb m, glb m') \<and> rg m = rg m'}"

definition step :: "('v,'a) rpred \<Rightarrow> ('v,'r,'a) tstate_scheme rel"
  where "step R \<equiv> {(m,m'). R (glb m, glb m')}"

text \<open>The WP predicate transformer given a rely R and guarantee G\<close>
fun wp :: "('v,'a) rpred \<Rightarrow> ('v,'a) rpred \<Rightarrow> ('v,'r,'a) lang \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred"
  where
    "wp R G Skip Q = Q" |
    "wp R G Fence Q = Q" |
    "wp R G (Load v r\<^sub>a r a) Q = stabilize R (v \<and>\<^sub>p (\<lambda>m. Q (aux_upd a (m (r :=\<^sub>r st m (rg m r\<^sub>a))))))" |
    "wp R G (Store v r\<^sub>a r a) Q = stabilize R (v \<and>\<^sub>p (\<lambda>m. Q (aux_upd a (m (rg m r\<^sub>a :=\<^sub>s rg m r)))))" |
    "wp R G (Op r e) Q = wp\<^sub>i (op r e) Q" |
    "wp R G (Test p) Q = stabilize R (p \<longrightarrow>\<^sub>p Q)" |
    "wp R G (Assert p) Q = (stabilize R p \<and>\<^sub>p Q)" |
    "wp R G (CAS v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) Q = 
      stabilize R (
        v \<and>\<^sub>p 
        (\<lambda>m. st m (rg m r\<^sub>a) = rg m r\<^sub>1 \<longrightarrow> Q (aux_upd a (m(rg m r\<^sub>a :=\<^sub>s rg m r\<^sub>2, r :=\<^sub>r T)))) \<and>\<^sub>p 
        (\<lambda>m. st m (rg m r\<^sub>a) \<noteq> rg m r\<^sub>1 \<longrightarrow> Q (aux_upd a (m(r :=\<^sub>r F)))))" |
    "wp R G (Seq c\<^sub>1 c\<^sub>2) Q = wp R G c\<^sub>1 (wp R G c\<^sub>2 Q)" |
    "wp R G (If e\<^sub>1 f e\<^sub>2 c\<^sub>1 c\<^sub>2) Q = (
      wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) (wp R G c\<^sub>1 Q) \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) (wp R G c\<^sub>2 Q))" |
    "wp R G (While e\<^sub>1 f e\<^sub>2 I c) Q = 
      (stabilize R I \<and>\<^sub>p assert (
        I \<turnstile>\<^sub>p wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) (wp R G c (stabilize R I)) \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) Q))" |
    "wp R G (DoWhile I c e\<^sub>1 f e\<^sub>2) Q = 
      (stabilize R I \<and>\<^sub>p assert (
        I \<turnstile>\<^sub>p wp R G c (wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) (stabilize R I) \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) Q)))"

section \<open>Wellformedness\<close>

text \<open>Couple all wellformedness conditions into a single definition\<close>
definition wellformed :: "('v,'a) rpred \<Rightarrow> ('v,'a) rpred \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> bool"
  where "wellformed R G Q \<equiv> 
    stable (step\<^sub>R R) (Collect Q) \<and> reflexive R \<and> transitive R \<and> reflexive G" 

text \<open>Establish wellformedness of a false predicate\<close>
lemma wf_false:
  "\<forall>m. \<not> P m \<Longrightarrow> wellformed R G Q \<Longrightarrow> wellformed R G P"
  unfolding wellformed_def stable_def by (auto)

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G P"
  shows "stable (step\<^sub>R R) (Collect (stabilize R Q))"
  unfolding stable_def step\<^sub>R_def
proof (clarsimp)
  fix m m'
  assume a: "stabilize R Q m" "R (glb m, glb m')" "rg m = rg m'"
  have "\<forall>g''. R (glb m',g'') \<longrightarrow> R (glb m,g'')"
    using assms a(2) unfolding wellformed_def transitive_def by blast
  thus "stabilize R Q m'" using a(1,3) by (auto simp: stabilize_def set_glb_def)
qed

text \<open>Stabilization preserves wellformedness\<close>
lemma stabilize_wellformed [intro]:
  assumes "wellformed R G P"
  shows "wellformed R G (stabilize R Q)" (is "wellformed R G ?P")
proof -
  have "stable (step\<^sub>R R) (Collect ?P)" 
    using stabilize_stable assms by blast
  thus ?thesis using assms unfolding wellformed_def by blast
qed

lemma stable_conj [intro]:
  assumes "stable R (Collect P)" "stable R (Collect Q)"
  shows "stable R (Collect (P \<and>\<^sub>p Q))"
  using assms by (auto simp: stable_def pred_defs)

lemma wellformed_conjI [intro]:
  assumes "wellformed R G P" "wellformed R G Q"
  shows "wellformed R G (P \<and>\<^sub>p Q)"
  using assms by (auto simp: wellformed_def)

lemma [simp]:
  "set_glb m (glb m) = m"
  by (auto simp: set_glb_def glb_def)

text \<open>Elimination rule to ignore the stabilization process\<close>
lemma stabilizeE:
  assumes "stabilize R P m"
  assumes "wellformed R G Q"
  obtains "P m"
  using assms unfolding wellformed_def reflexive_def stabilize_def sorry

section \<open>Program Wellformedness\<close>

text \<open>Ensure all operations have preconditions strong enough to discharge their guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c (Load v r\<^sub>a r a) G = 
      (\<forall>m. v m \<longrightarrow> G (glb m,glb (m\<lparr>tstate.more := a (m(r :=\<^sub>r st m (rg m r\<^sub>a)))\<rparr>)))" |
    "guar\<^sub>c (Store v r\<^sub>a r a) G = 
      (\<forall>m. v m \<longrightarrow> G (glb m,glb (aux_upd a (m(rg m r\<^sub>a :=\<^sub>s rg m r)))))" |
    "guar\<^sub>c (CAS v r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) G = 
      ((\<forall>m. v m \<and> st m (rg m r\<^sub>a) = rg m r\<^sub>1 \<longrightarrow> G (glb m,glb (aux_upd a (m(rg m r\<^sub>a :=\<^sub>s rg m r\<^sub>2, r :=\<^sub>r T))))) \<and>
      (\<forall>m. v m \<and> st m (rg m r\<^sub>a) \<noteq> rg m r\<^sub>1 \<longrightarrow> G (glb m,glb (aux_upd a (m(r :=\<^sub>r F))))))" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If e\<^sub>1 f e\<^sub>2 c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While e\<^sub>1 f e\<^sub>2 I c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c (DoWhile I c e\<^sub>1 f e\<^sub>2) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c _ _ = True"

section \<open>Soundness\<close>

text \<open>Convert the While language into the com language expected by the underlying logic\<close> 
fun lift\<^sub>c :: "('v,'r,'a) lang \<Rightarrow> (('v,'r,'a) inst, ('v,'r,'a) tstate_scheme) com"
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c Fence = Basic (\<lfloor>fence\<rfloor>)" |
    "lift\<^sub>c (Op r e) = Basic (\<lfloor>op r e\<rfloor>)" |
    "lift\<^sub>c (Load c r\<^sub>a r a) = 
      \<Sqinter> {[
        \<lfloor>eq r\<^sub>a v\<^sub>a\<rfloor>, \<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,load v\<^sub>a (Val v) (\<lambda>m. a (m(r :=\<^sub>r v)))\<rfloor>, \<lfloor>op r (Glb v v\<^sub>a)\<rfloor>] 
          |v v\<^sub>a. True}" |
    "lift\<^sub>c (Store c r\<^sub>a r a) = \<Sqinter> {[\<lfloor>eq r\<^sub>a v\<^sub>a\<rfloor>, \<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,store v\<^sub>a (Reg r) a\<rfloor>] |v\<^sub>a. True}" |
    "lift\<^sub>c (CAS c r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) = (Choice
      (\<Sqinter> {[\<lfloor>eq r\<^sub>a v\<^sub>a\<rfloor>, \<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,cas\<^sub>T v\<^sub>a (Reg r\<^sub>1) (Reg r\<^sub>2) (\<lambda>m. a (m(r :=\<^sub>r T)))\<rfloor>, \<lfloor>op r (Glb T v\<^sub>a)\<rfloor>] |v\<^sub>a. True})
      (\<Sqinter> {[\<lfloor>eq r\<^sub>a v\<^sub>a\<rfloor>, \<lfloor>(\<lambda>m. rg m r\<^sub>a = v\<^sub>a) \<and>\<^sub>p c,cas\<^sub>F v\<^sub>a (Reg r\<^sub>1) (Reg r\<^sub>2) (\<lambda>m. a (m(r :=\<^sub>r F)))\<rfloor>, \<lfloor>op r (Glb F v\<^sub>a)\<rfloor>] |v\<^sub>a. True}))" |
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) = (lift\<^sub>c c\<^sub>1 ;; lift\<^sub>c c\<^sub>2)" |
    "lift\<^sub>c (If e\<^sub>1 f e\<^sub>2 c\<^sub>1 c\<^sub>2) = (Choice (com.Seq (Basic (\<lfloor>cmp e\<^sub>1 f e\<^sub>2\<rfloor>)) (lift\<^sub>c c\<^sub>1)) 
                                    (com.Seq (Basic (\<lfloor>ncmp e\<^sub>1 f e\<^sub>2\<rfloor>)) (lift\<^sub>c c\<^sub>2)))" |
    "lift\<^sub>c (While e\<^sub>1 f e\<^sub>2 I c) = (com.Seq ((com.Seq (Basic (\<lfloor>cmp e\<^sub>1 f e\<^sub>2\<rfloor>)) (lift\<^sub>c c))*) 
                                      (Basic (\<lfloor>ncmp e\<^sub>1 f e\<^sub>2\<rfloor>)))" |
    "lift\<^sub>c (DoWhile I c e\<^sub>1 f e\<^sub>2) = (com.Seq ((com.Seq (lift\<^sub>c c) (Basic (\<lfloor>cmp e\<^sub>1 f e\<^sub>2\<rfloor>)))*) (com.Seq (lift\<^sub>c c) (Basic (\<lfloor>ncmp e\<^sub>1 f e\<^sub>2\<rfloor>))))" |
    "lift\<^sub>c (Test p) = Basic (nop, UNIV, {(m,m'). m = m' \<and> p m})" |
    "lift\<^sub>c (Assert p) = Basic (nop, Collect p, Id)"

subsection \<open>Interpretation of General Logic\<close>

interpretation rules fwd\<^sub>s re\<^sub>i
  by (unfold_locales) (auto simp: pred_defs)

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
  where "rules_abv \<equiv> rules"

abbreviation lifted_abv ("_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,20] 20)
  where "lifted_abv R G P c Q \<equiv> step\<^sub>R R,step G \<turnstile> Collect P {lift\<^sub>c c} Collect Q"

abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45) 
  where "validity_abv c P R G Q \<equiv> validity (lift\<^sub>c c) (Collect P) (step\<^sub>R R) (step G) (Collect Q)"

text \<open>An ordering property on contexts\<close>
definition context_order 
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv> wellformed R G Q \<longrightarrow> ((P \<turnstile>\<^sub>p Q) \<and> wellformed R G P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness\<close>
definition valid 
  ("_,_ \<turnstile>\<^sub>w _ {_} _" [100,0,0,100] 60)
  where "valid R G P c Q \<equiv> (guar\<^sub>c c G \<and> wellformed R G Q) \<longrightarrow> ((R,G \<turnstile>\<^sub>s P {c} Q) \<and> wellformed R G P)"

subsection \<open>Instruction Soundness\<close>

lemma [simp]:
  "glb (m\<lparr>rg := e\<rparr>) = glb m"
  unfolding glb_def by auto

lemma [intro]:
  "reflexive G \<Longrightarrow> G (m,m)"
  by (auto simp: reflexive_def)

lemma [intro!]:
  "stable (step\<^sub>R R) (Collect Q) \<Longrightarrow> stable (step\<^sub>R R) {m. Q (m\<lparr>rg := f (rg m)\<rparr>)}"
  by (auto simp add: wellformed_def stable_def step\<^sub>R_def)

lemma [intro!]:
  "stable (step\<^sub>R R) (Collect Q) \<Longrightarrow> stable (step\<^sub>R R) {m. f (rg m) \<longrightarrow> Q m}"
  by (auto simp add: wellformed_def stable_def step\<^sub>R_def)

fun stab\<^sub>i
  where
    "stab\<^sub>i R (load _ _ _) Q = stabilize R Q" |
    "stab\<^sub>i R (store _ _ _) Q = stabilize R Q" |
    "stab\<^sub>i R (cas\<^sub>T _ _ _ _) Q = stabilize R Q" |
    "stab\<^sub>i R (cas\<^sub>F _ _ _ _) Q = stabilize R Q" |
    "stab\<^sub>i _ _ Q = Q"

lemma test[intro!]:
  "wellformed R G Q \<Longrightarrow> wellformed R G (stab\<^sub>i R a (wp\<^sub>i a Q))"
  by (cases a) (auto simp add: wellformed_def rg_upd_def)
  
lemma atomic_wp\<^sub>i:
  assumes "wellformed R G Q" "c \<turnstile>\<^sub>p guar\<^sub>i a G"
  shows "step\<^sub>R R,step G \<turnstile>\<^sub>A Collect (stabilize R (c \<and>\<^sub>p wp\<^sub>i a Q)) {\<lfloor>c, a\<rfloor>} Collect Q"
  using assms by (cases a) (auto simp: atomic_rule_def guar_def wp_def rg_upd_def 
                                       wellformed_def step_def aux_upd_def pred_defs 
                                 elim!: stabilizeE)

lemma atomic_wp\<^sub>i':
  assumes "wellformed R G Q" "(\<lambda>m. True) \<turnstile>\<^sub>p guar\<^sub>i a G"
  shows "step\<^sub>R R,step G \<turnstile>\<^sub>A Collect (stab\<^sub>i R a (wp\<^sub>i a Q)) {\<lfloor>a\<rfloor>} Collect Q"
  using assms by (cases a) (auto simp: atomic_rule_def guar_def wp_def rg_upd_def 
                                       wellformed_def step_def aux_upd_def pred_defs 
                                 elim!: stabilizeE)

lemma atomic_wp\<^sub>i_rw:
  assumes "wellformed R G Q" "c \<turnstile>\<^sub>p guar\<^sub>i a G" "stable (step\<^sub>R R) (Collect P)" "P \<turnstile>\<^sub>p c \<and>\<^sub>p wp\<^sub>i a Q"
  shows "step\<^sub>R R,step G \<turnstile>\<^sub>A Collect P {\<lfloor>c, a\<rfloor>} Collect Q"
  using assms by (cases a) (auto simp: atomic_rule_def guar_def wp_def rg_upd_def 
                                       wellformed_def step_def aux_upd_def pred_defs 
                                 elim!: stabilizeE)

lemma atomic_wp\<^sub>i_rw':
  assumes "wellformed R G Q" "(\<lambda>m. True) \<turnstile>\<^sub>p guar\<^sub>i a G" "stable (step\<^sub>R R) (Collect P)" "P \<turnstile>\<^sub>p wp\<^sub>i a Q"
  shows "step\<^sub>R R,step G \<turnstile>\<^sub>A Collect P {\<lfloor>a\<rfloor>} Collect Q"
  using assms by (cases a) (auto simp: atomic_rule_def guar_def wp_def rg_upd_def 
                                       wellformed_def step_def aux_upd_def pred_defs 
                                 elim!: stabilizeE)

(*
lemma atomic_op [intro]:
  "wellformed R G Q \<Longrightarrow> step\<^sub>R R,step G \<turnstile>\<^sub>A Collect (wp\<^sub>i R (op r e) Q) {\<lfloor>op r e\<rfloor>} Collect Q"
  by (auto simp: atomic_rule_def guar_def wp_def rg_upd_def wellformed_def step_def)

lemma atomic_cmp [intro]:
  "wellformed R G Q \<Longrightarrow> step\<^sub>R R,step G \<turnstile>\<^sub>A Collect (wp\<^sub>i R (cmp e\<^sub>1 f e\<^sub>2) Q) {\<lfloor>cmp e\<^sub>1 f e\<^sub>2\<rfloor>} Collect Q"
  by (auto simp: atomic_rule_def guar_def wp_def wellformed_def step_def)

lemma atomic_load [intro]:
  assumes "wellformed R G Q" "guar\<^sub>c (Load c r\<^sub>a r a) G"
  shows "step\<^sub>R R,step G \<turnstile>\<^sub>A Collect (stabilize R (c \<and>\<^sub>p wp\<^sub>i (load v\<^sub>a e a) Q)) {\<lfloor>c, load v\<^sub>a e a\<rfloor>} Collect Q"
  using assms by (auto simp: atomic_rule_def wp_def pred_defs guar_def step_def wellformed_def elim!: stabilizeE)
*)

lemma nil [intro]:
  assumes "wellformed R G Q"
  shows "step\<^sub>R R,step G \<turnstile> Collect Q {Nil} Collect Q" 
  using assms by (auto simp: wellformed_def)

lemma [simp]:
  "rg (set_glb m g) r\<^sub>a = rg m r\<^sub>a"
  by (auto simp: set_glb_def)

lemma [simp]:
  "set_glb (set_glb m g) g' = set_glb m g'"
  by (auto simp: set_glb_def)

lemma [simp]:
  "set_glb (m\<lparr>tstate.more := a\<rparr>) g = set_glb m g"
    by (auto simp: set_glb_def)

lemma [simp]:
  "st (set_glb m g) = st g"
  by (auto simp: set_glb_def)

lemma [simp]:
  "m(r :=\<^sub>r e)\<lparr>tstate.more := a\<rparr> = (m\<lparr>tstate.more := a\<rparr>)(r :=\<^sub>r e)"
  by (auto simp: rg_upd_def)

lemma ord_rotate:
  "R,G \<turnstile> Q {c\<^sub>2} M \<Longrightarrow> R,G \<turnstile> P {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile> P {c\<^sub>1 \<cdot> c\<^sub>2} M"
  by auto

lemma load_sound:
  assumes "wellformed R G Q" "guar\<^sub>c (Load c r\<^sub>a r a) G"
  shows "R,G \<turnstile>\<^sub>s wp R G (Load c r\<^sub>a r a) Q {Load c r\<^sub>a r a} Q"
  using assms
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro rules.seqset)
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro ord_rotate rules.basic)
  apply (rule nil, simp)
  apply (rule atomic_wp\<^sub>i')
  apply (auto simp add: pred_defs)[2]
  apply (rule atomic_wp\<^sub>i)
  apply blast
  apply (auto simp add: pred_defs aux_upd_def rg_upd_def)[1]
  apply (rule atomic_wp\<^sub>i_rw')
  apply auto
  apply (auto simp: stabilize_def aux_upd_def pred_defs)
  done

lemma store_sound:
  assumes "wellformed R G Q" "guar\<^sub>c (Store c r\<^sub>a r a) G"
  shows "R,G \<turnstile>\<^sub>s wp R G (Store c r\<^sub>a r a) Q {Store c r\<^sub>a r a} Q"
  using assms
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro rules.seqset)
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro ord_rotate rules.basic)
  apply (rule nil, simp)
  apply (rule atomic_wp\<^sub>i)
  apply (auto simp add: pred_defs aux_upd_def rg_upd_def)[2]
  apply (rule atomic_wp\<^sub>i_rw')
  apply auto
  apply (auto simp: stabilize_def aux_upd_def pred_defs)
  done

lemma [simp]:
  "glb (m(r :=\<^sub>r T)) = glb m"
  by (auto simp: glb_def rg_upd_def)

lemma cas_sound:
  assumes "wellformed R G Q" "guar\<^sub>c (CAS c r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) G"
  shows "R,G \<turnstile>\<^sub>s wp R G (CAS c r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a) Q {CAS c r\<^sub>a r\<^sub>1 r\<^sub>2 r T F a} Q"
  using assms
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro rules.choice rules.seqset)
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro ord_rotate rules.basic)
  apply (rule nil, simp)
  apply (rule atomic_wp\<^sub>i'; auto simp add: pred_defs)
  apply (rule atomic_wp\<^sub>i)
  apply blast
  apply (auto simp add: pred_defs aux_upd_def)[1]
  apply (rule atomic_wp\<^sub>i_rw')
  apply auto[3]
  apply (auto simp: stabilize_def aux_upd_def pred_defs)[1]
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro ord_rotate rules.basic)
  apply (rule nil, simp)
  apply (rule atomic_wp\<^sub>i'; auto simp add: pred_defs)
  apply (rule atomic_wp\<^sub>i)
  apply blast
  apply (auto simp add: pred_defs aux_upd_def)[1]
  apply (rule atomic_wp\<^sub>i_rw')
  apply auto[3]  
  apply (auto simp: stabilize_def aux_upd_def pred_defs)[1]
  done

lemma op_sound:
  assumes "wellformed R G Q"
  shows "R,G \<turnstile>\<^sub>s wp R G (Op r e) Q {Op r e} Q"
  using assms
  apply (clarsimp simp del: wp.simps beh\<^sub>i.simps)
  apply (rule rules.basic)
  apply (rule atomic_wp\<^sub>i_rw')
  apply (auto simp: pred_defs)
  by (auto simp: wellformed_def rg_upd_def)

lemma fence_sound:
  assumes "wellformed R G Q"
  shows "R,G \<turnstile>\<^sub>s wp R G (Fence) Q {Fence} Q"
  apply (clarsimp, rule rules.basic, simp add: atomic_rule_def, intro conjI)
  using assms
  by (auto simp: wp_def pred_defs step_def guar_def wellformed_def reflexive_def)

lemma test_sound:
  assumes "wellformed R G Q"
  shows "R,G \<turnstile>\<^sub>s wp R G (Test p) Q {Test p} Q"
  apply (clarsimp, rule rules.basic, simp add: atomic_rule_def, intro conjI)
  using assms
  apply (auto simp: wp_def pred_defs elim!: stabilizeE)
  by (auto simp: step_def guar_def wellformed_def reflexive_def)

lemma assert_sound:
  assumes "wellformed R G Q"
  shows "R,G \<turnstile>\<^sub>s wp R G (Assert p) Q {Assert p} Q"
  apply (clarsimp, rule rules.basic, simp add: atomic_rule_def, intro conjI)
  using assms
  apply (auto simp: wp_def pred_defs elim!: stabilizeE)[1]
  using assms
  apply (auto simp: step_def guar_def wellformed_def reflexive_def)
  using assms by blast

subsection \<open>Base Introduction Rules\<close>

text \<open>Reflexive Ordering\<close>
lemma ord_refl [intro]:
  "R,G \<turnstile>\<^sub>w P \<ge> P"
  unfolding context_order_def by (auto simp: pred_defs)

text \<open>Assert Ordering\<close>
lemma ord_assert:
  "R,G \<turnstile>\<^sub>w P \<and>\<^sub>p assert A \<ge> P"
  by (cases A) (auto simp: context_order_def pred_defs intro: wf_false) 

text \<open>Stabilize Ordering\<close>
lemma ord_stabilize:
  assumes "P \<turnstile>\<^sub>p Q" 
  shows "R,G \<turnstile>\<^sub>w stabilize R P \<ge> Q"
  using assms stabilizeE unfolding context_order_def entail_def
  by blast

text \<open>Skip Rule\<close>
lemma skip_wp:
  "R,G \<turnstile>\<^sub>w Q {Skip} Q"
  by (auto simp: context_order_def valid_def wellformed_def)

text \<open>Sequential Rule\<close>
lemma seq_wp:
  "R,G \<turnstile>\<^sub>w P {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w M {c\<^sub>2} P \<Longrightarrow> R,G \<turnstile>\<^sub>w M {Seq c\<^sub>2 c\<^sub>1} Q"
  unfolding valid_def by auto

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

lemma cmp_sound:
  assumes "wellformed R G Q"
  assumes "P \<turnstile>\<^sub>p wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) Q"
  shows "step\<^sub>R R,step G \<turnstile> Collect P {Basic (\<lfloor>cmp e\<^sub>1 f e\<^sub>2\<rfloor>)} Collect Q"
  apply (rule rules.conseq[of "step\<^sub>R R" "step G" "Collect (wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) Q)" _ "Collect Q"])
  apply (rule rules.basic)
  unfolding atomic_rule_def
  apply (intro conjI)
  apply (clarsimp simp: wp_def)
  using assms apply (clarsimp simp: guar_def wellformed_def reflexive_def step_def)
  using assms apply (auto simp: wellformed_def step\<^sub>R_def stable_def)[2]
  using assms(2) apply (clarsimp simp: pred_defs)[1]
  by auto
  
text \<open>If Rule\<close>
lemma ifWP:
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q"
  shows "R,G \<turnstile>\<^sub>w (wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) P\<^sub>1 \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) P\<^sub>2) {If e\<^sub>1 f e\<^sub>2 c\<^sub>1 c\<^sub>2} Q"
  using assms
  unfolding valid_def
  apply (clarsimp simp del: beh\<^sub>i.simps)
  apply (intro impI conjI rules.choice rules.seq stabilize_wellformed; assumption?)
  apply (rule cmp_sound; simp)
  apply (simp add: pred_defs)
  apply (rule cmp_sound; simp)
  apply (simp add: pred_defs)
  unfolding wellformed_def
  apply simp
  by (auto simp: stable_def step\<^sub>R_def pred_defs)

text \<open>While Rule\<close>
lemma whileWP:
  assumes "I \<turnstile>\<^sub>p wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) P \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) Q"
  assumes "R,G \<turnstile>\<^sub>w P {c} stabilize R I" (is "R,G \<turnstile>\<^sub>w P {c} ?I")
  shows "R,G \<turnstile>\<^sub>w ?I {While e\<^sub>1 f e\<^sub>2 I c} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI rules.choice rules.seq stabilize_wellformed; assumption?)
  assume "guar\<^sub>c (While e\<^sub>1 f e\<^sub>2 I c) G \<and> wellformed R G Q"
  thus "step\<^sub>R R,step G \<turnstile> (Collect ?I) {Basic (\<lfloor>ncmp e\<^sub>1 f e\<^sub>2\<rfloor>)} Collect Q"
    using assms(1) by (intro cmp_sound; simp; intro stabilize_entail'; simp add: pred_defs)
next
  assume "guar\<^sub>c (While e\<^sub>1 f e\<^sub>2 I c) G \<and> wellformed R G Q"
  hence "guar\<^sub>c c G" "wellformed R G ?I" by auto
  thus "step\<^sub>R R,step G \<turnstile> Collect ?I {(Basic (\<lfloor>cmp e\<^sub>1 f e\<^sub>2\<rfloor>) ;; lift\<^sub>c c)*} Collect ?I"
    using assms
    apply (intro rules.loop rules.seq stabilize_stable; unfold valid_def)
    apply blast
    defer 1
    apply blast
    apply (intro cmp_sound; simp; intro stabilize_entail'; simp add: pred_defs)
    done
qed auto

lemma doWhileWP:
  assumes "R,G \<turnstile>\<^sub>w stabilize R I {c} (wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) (stabilize R I) \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) Q)" (is "R,G \<turnstile>\<^sub>w ?I {c} ?Q")
  shows "R,G \<turnstile>\<^sub>w stabilize R I {DoWhile I c e\<^sub>1 f e\<^sub>2} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI rules.choice rules.seq stabilize_wellformed; assumption?)
  assume "guar\<^sub>c (DoWhile I c e\<^sub>1 f e\<^sub>2) G \<and> wellformed R G Q"
  thus "step\<^sub>R R,step G \<turnstile> Collect ?Q {Basic (\<lfloor>ncmp e\<^sub>1 f e\<^sub>2\<rfloor>)} Collect Q"
    by (intro cmp_sound; simp add: pred_defs)
next
  assume "guar\<^sub>c (DoWhile I c e\<^sub>1 f e\<^sub>2) G \<and> wellformed R G Q"
  hence "guar\<^sub>c c G \<and> wellformed R G ?Q" sorry
  thus "step\<^sub>R R,step G \<turnstile> Collect ?I {lift\<^sub>c c} Collect ?Q"
    using assms(1) unfolding valid_def by simp 
next
  assume wf: "guar\<^sub>c (DoWhile I c e\<^sub>1 f e\<^sub>2) G \<and> wellformed R G Q"
  hence "wellformed R G ?I \<and> wellformed R G ?Q \<and> guar\<^sub>c c G" sorry
  thus "step\<^sub>R R,step G \<turnstile> Collect ?I {(lift\<^sub>c c ;; Basic (\<lfloor>cmp e\<^sub>1 f e\<^sub>2\<rfloor>))*} Collect ?I"
    using assms
    apply (intro rules.loop rules.seq stabilize_stable; unfold valid_def)
    apply blast
    apply blast
    by (intro cmp_sound; simp add: pred_defs)
qed auto

lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

lemma guar_all:
  "wellformed R G Q \<Longrightarrow> guar\<^sub>c c G \<Longrightarrow> \<forall>\<beta>\<in>basics (lift\<^sub>c c). guar\<^sub>\<alpha> \<beta> (step G)"
  sorry (*apply (induct c) 
  apply (auto simp: guar_def step_def pred_defs wellformed_def reflexive_def)
  apply (subgoal_tac "G (ab, ab(ba x2 := ba x3))")
  apply (subgoal_tac "(ab(ba x2 := ba x3)) = (\<lambda>x. if x = ba x2 then rg (ab, ba) x3 else ld (ab,ba) x)")
  apply simp
  apply auto
  apply (subgoal_tac " G (ab, ab(ba x2 := ba x4))")
  apply (subgoal_tac "(ab(ba x2 := ba x4)) = (\<lambda>x. if x = ba x2 then rg (ab, ba) x4 else ld (ab,ba) x)")
  apply simp
  apply auto
  done *)

text \<open>False Rule\<close>
lemma falseWP:
  assumes "P \<turnstile>\<^sub>p (\<lambda>m. False)"
  shows "R,G \<turnstile>\<^sub>w P {c} Q"
  using assms unfolding valid_def
  apply (intro conjI impI guar_all rules.conseq[OF falseI, where ?G="step G"])
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
  then show ?thesis using assms by (intro rewriteWP[OF _ ord_assert], simp)
next
  case False
  then show ?thesis by (intro falseWP, auto simp: pred_defs)
qed 

subsection \<open>Rewrite Introduction Rules\<close>

text \<open>Skip Rewrite Rule\<close>
lemma skipRW:
  assumes "R,G \<turnstile>\<^sub>w P \<ge> Q" 
  shows "R,G \<turnstile>\<^sub>w P {Skip} Q"
  using rewriteWP[OF skip_wp assms] .

text \<open>If Rewrite Rule\<close>
lemma ifRW:
  assumes "R,G \<turnstile>\<^sub>w P \<ge> (wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) P\<^sub>1 \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) P\<^sub>2)"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q"
  shows "R,G \<turnstile>\<^sub>w P {If e\<^sub>1 f e\<^sub>2 c\<^sub>1 c\<^sub>2} Q"
  using rewriteWP[OF ifWP[OF assms(2,3)] assms(1)] . 

text \<open>While Rewrite Rule\<close>
lemma whileRW:
  assumes order: "R,G \<turnstile>\<^sub>w N \<ge> stabilize R I"
  assumes recur: "R,G \<turnstile>\<^sub>w P {c} stabilize R I"
  assumes side: "I \<turnstile>\<^sub>p wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) P \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) Q"
  shows "R,G \<turnstile>\<^sub>w N {While e\<^sub>1 f e\<^sub>2 I c} Q"
  using rewriteWP[OF whileWP[OF side recur] order] .

text \<open>Do While Rewrite Rule\<close>
lemma doWhileRW:
  assumes order: "R,G \<turnstile>\<^sub>w P \<ge> stabilize R I"
  assumes recur: "R,G \<turnstile>\<^sub>w stabilize R I {c} (wp\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) (stabilize R I) \<and>\<^sub>p wp\<^sub>i (ncmp e\<^sub>1 f e\<^sub>2) Q)"
  shows "R,G \<turnstile>\<^sub>w P {DoWhile I c e\<^sub>1 f e\<^sub>2} Q"
  using rewriteWP[OF doWhileWP[OF recur] order] .

subsection \<open>Soundness\<close>

lemma wellformed_assert [intro]:
  assumes "wellformed R G Q"
  shows "wellformed R G (assert p)"
  using assms by (auto simp: wellformed_def assert_def stable_def)

lemma wellformed_wp [intro]:
  assumes "wellformed R G Q"
  shows "wellformed R G (ARMv8_Rules.wp R G c Q)"
  sorry (*
  using assms by (induct c arbitrary: Q) fastforce+
*)

lemma wp_valid:
  shows "R,G \<turnstile>\<^sub>w wp R G c Q {c} Q" 
proof (induct c arbitrary: Q)
  case Skip
  thus ?case using skip_wp by auto
next
  case Fence
  thus ?case using fence_sound by (auto simp: valid_def)
next
  case (Load)
  thus ?case using load_sound by (auto simp: valid_def) 
next
  case (Store)
  thus ?case using store_sound by (auto simp: valid_def) 
next
  case (Op)
  thus ?case using op_sound by (auto simp: valid_def)
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case using seq_wp unfolding wp.simps by blast
next
  case (If f r c\<^sub>1 c\<^sub>2)
  thus ?case using ifWP unfolding wp.simps by blast
next
  case (While f r I c)
  thus ?case unfolding wp.simps
    by (intro assertWP impI whileRW) (auto simp add: pred_defs)
next
  case (DoWhile I c e\<^sub>1 f e\<^sub>2)
  thus ?case unfolding wp.simps
    by (intro assertWP impI doWhileRW ord_refl; rule rewriteWP) (blast intro: ord_stabilize)+
next
  case (Test p)
  thus ?case using test_sound by (auto simp: valid_def)
next
  case (Assert p)
  thus ?case using assert_sound by (auto simp: valid_def)
next
  case (CAS)
  thus ?case using cas_sound by (auto simp: valid_def)
qed

text \<open>Soundness lemma for WP reasoning over ARMv8\<close>
theorem armv8_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" 
  assumes st: "stable (step\<^sub>R R) (Collect Q)" 
  assumes g: "guar\<^sub>c c G"
  assumes P: "P \<turnstile>\<^sub>p wp R G c Q"
  assumes i: "inter (step\<^sub>R R) (step G) (lift\<^sub>c c)" (* Rephrase this in terms of the ARMv8 analysis *)
  shows "\<Turnstile> c SAT [P, R, G, Q]"
proof -
  have "wellformed R G Q" using wf st by (auto simp: wellformed_def)
  hence "R,G \<turnstile>\<^sub>s wp R G c Q {c} Q" using g wp_valid unfolding valid_def by blast
  hence "R,G \<turnstile>\<^sub>s P {c} Q" by (rule rules.conseq) (insert P, auto simp: entail_def)
  thus ?thesis using i by (intro sound thread) auto
qed

end