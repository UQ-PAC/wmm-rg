theory ARMv8_Inter
  imports ARMv8_Rules
begin

text \<open>
This theory file describes the abstract interference pairs analysis
and includes a soundness proof.
\<close>

abbreviation inst
  where "inst a \<equiv> fst (fst a)"

text \<open>The abstract language features used by liftc\<close>
fun sim :: "('a,'b) com \<Rightarrow> bool"
  where 
    "sim (c\<^sub>1 || c\<^sub>2) = False" |
    "sim (Thread _) = False" |
    "sim (c*) = False" |   
    "sim (c\<^sub>1 \<cdot> c\<^sub>2) = (sim c\<^sub>1 \<and> sim c\<^sub>2)" |
    "sim (c\<^sub>1 ;; c\<^sub>2) = (sim c\<^sub>1 \<and> sim c\<^sub>2)" |
    "sim (c\<^sub>1 \<sqinter> c\<^sub>2) = (sim c\<^sub>1 \<and> sim c\<^sub>2)" |  
    "sim _ = True"

definition wfbasic :: "('v,'r,'a) subbasic \<Rightarrow> bool"
  where "wfbasic \<beta> \<equiv> beh \<beta> = beh\<^sub>a (tag \<beta>) \<and> (case inst \<beta> of cfence \<Rightarrow> vc \<beta> = UNIV \<and> beh \<beta> = beh\<^sub>i cfence | _ \<Rightarrow> True)"

definition wfcom
  where "wfcom c \<equiv> \<forall>\<beta> \<in> basics c. wfbasic \<beta>"

text \<open>The language is always thread-local\<close>
lemma sim_lift [intro]:
  "sim (lift\<^sub>c c)"
  by (induct c) auto

lemma sim_seq2com [intro]:
  "sim (seq2com s)"
  by (induct s) auto

lemma sim_silent:
  "c \<leadsto> c' \<Longrightarrow> sim c \<Longrightarrow> sim c'"
  by (induct rule: silent.induct) auto

lemma sim_execute:
  "lexecute c r \<alpha> c' \<Longrightarrow> sim c \<Longrightarrow> sim c'"
  by (induct rule: lexecute.induct) auto

lemma sim_prefix:
  "lexecute c r \<alpha> c' \<Longrightarrow> sim c \<Longrightarrow> sim r"
  by (induct rule: lexecute.induct, auto)

lemma aux_exec [intro!]:
  assumes "(m\<^sub>1,m\<^sub>2) \<in> P"
  shows "(m\<^sub>1,m\<^sub>2(aux: f)) \<in> P O {(m, m'). m' = m(aux: f)}"
  using assms by blast

lemma [simp]:
  "P O {(m, m'). m' = m} = P"
  by auto

lemma wfcomI [intro]:
  "wfcom (lift\<^sub>c c)"
  by (induct c) (auto simp: wfcom_def wfbasic_def liftg_def liftl_def)

lemma [simp]:
  "wfcom (c\<^sub>1 ;; c\<^sub>2) = (wfcom c\<^sub>1 \<and> wfcom c\<^sub>2)"
  by (auto simp: wfcom_def)

lemma [simp]:
  "wfcom (Ord c\<^sub>1 c\<^sub>2) = (wfcom c\<^sub>1 \<and> wfcom c\<^sub>2)"
  by (auto simp: wfcom_def)

lemma wfcom_silent:
  "c \<leadsto> c' \<Longrightarrow> wfcom c \<Longrightarrow> wfcom c'"
  using basics_silent by (auto simp: wfcom_def)

lemma wfcom_exec:
  "lexecute c r \<alpha> c' \<Longrightarrow> wfcom c \<Longrightarrow> wfcom c'"
  using basics_exec unfolding wfcom_def by blast

lemma wfcom_exec_prefix:
  "lexecute c r \<alpha> c' \<Longrightarrow> wfcom c \<Longrightarrow> wfcom r \<and> wfbasic \<alpha>"
  using basics_exec_prefix unfolding wfcom_def by blast

lemma opbasicE:
  obtains (op) x e f v b where  "(basic ) = ((op x e,f), v, b)" |
          (cmp) g f v b where "(basic ) = ((cmp g,f), v, b)" |
          (fence) f v b where "(basic ) = ((fence,f), v, b)" |
          (cfence) f v b where "(basic ) = ((cfence,f), v, b)" |
          (stfence) f v b where "(basic ) = ((stfence,f), v, b)" |
          (load) x e f v b where "(basic ) = ((load x e,f), v, b)" |
          (store) b x e f v h where "(basic ) = ((cstore b x e,f), v, h)" |
          (cas\<^sub>T) x e1 e2 f v b where "(basic ) = ((cas\<^sub>T x e1 e2,f), v, b)" |
          (cas\<^sub>F) x e1 f v b where "(basic ) = ((cas\<^sub>F x e1,f), v, b)" |
          (nop) f v b where "(basic ) = ((nop,f), v, b)" 
  by (cases basic, case_tac a, case_tac aa; clarsimp)

lemma fwd_wfbasic:
  assumes "reorder_com \<alpha>' r \<alpha>" "wfbasic \<alpha>" 
  shows "wfbasic \<alpha>'"
  using assms
proof (induct \<alpha>' r \<alpha> rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  then show ?case by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def wfbasic_def)
qed auto

lemma fwdE:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  obtains (no_fwd) "inst \<alpha>' = inst \<alpha>" "snd (tag \<alpha>') = snd (tag \<alpha>)" "vc \<alpha>' = vc \<alpha>" "wr (inst \<beta>) \<inter> rd (inst \<alpha>) = {}" |
          (fwd) x where "wr (inst \<beta>) = {x}" "x \<in> rd (inst \<alpha>)" "rd (inst \<beta>) - {x} \<subseteq> locals"
proof (cases "wr (inst \<beta>) \<inter> rd (inst \<alpha>) = {}")
  case True
  then show ?thesis using no_fwd assms    
    by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)
next
  case False
  then show ?thesis using fwd assms 
    by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)
qed

fun exp
  where 
    "exp (subop.op x e) = e" | 
    "exp (subop.cstore b x e) = e" | 
    "exp (subop.cas\<^sub>T x e\<^sub>1 e\<^sub>2) = e\<^sub>2" | 
    "exp _ = undefined"

section \<open>Definitions\<close>

text \<open>
A data point, extends an instruction with reordering information.
Forms the basis of the analysis, as each instruction generates a point that is maintained
across all instructions earlier to it in program-order.
Collects the transitive dependencies of said instruction along with all instructions
it may reorder with.
Moreover, it collects those variables that may be redefined between the two (esc) two
handle forwarding manipulations.
\<close>
record ('v,'r,'a) point =
  op :: "('v,'r,'a) subbasic"
  wrs :: "('v,'r) var set"
  rds :: "('v,'r) var set"
  bar :: "('v,'r) subop set"
  esc :: "('v,'r) var set"
  pairs :: "(('v,'r,'a) subbasic \<times> ('v,'r) var set) set"

type_synonym ('v,'r,'a) points = "('v,'r,'a) point set"

subsection \<open>Tests\<close>

text \<open>Test if a set contains a global variable\<close>
definition hasGlobal :: "('g,'r) var set \<Rightarrow> bool"
  where "hasGlobal S \<equiv> \<exists>e. Glb e \<in> S"


text \<open>Test if a point is dependent on an operation, implying ordering of their execution\<close>
fun ord :: "('v,'r) subop \<Rightarrow> ('v,'r,'a) point \<Rightarrow> bool"
  where
    "ord fence _ = True" |
    "ord nop p = (fence \<in> bar p)" |
    "ord stfence p = (fence \<in> bar p \<or> hasGlobal (wrs p))" |
    "ord cfence p = (fence \<in> bar p \<or> hasGlobal (rds p))" |
    "ord (cmp b) p = (fence \<in> bar p \<or> cfence \<in> bar p \<or> hasGlobal (wrs p) \<or> wrs p \<inter> rd (cmp b) \<noteq> {})" |
    "ord (cstore b a e) p = (fence \<in> bar p \<or> stfence \<in> bar p \<or> Glb a \<in> wrs p)" |
    "ord (subop.op r e) p = (fence \<in> bar p \<or> Reg r \<in> wrs p)" |
    "ord (load a e) p = (fence \<in> bar p \<or> Glb a \<in> wrs p \<or> Glb a \<in> rds p)" |
    "ord (cas\<^sub>T a e\<^sub>1 e\<^sub>2) p = (fence \<in> bar p \<or> stfence \<in> bar p \<or> Glb a \<in> wrs p)" |
    "ord (cas\<^sub>F a e\<^sub>1) p = (fence \<in> bar p \<or> Glb a \<in> wrs p \<or> Glb a \<in> rds p)"

subsection \<open>Point Manipulations\<close>

text \<open>Strengthen a point based on a strictly earlier instruction\<close>
definition stren :: "('v,'r,'a) subbasic \<Rightarrow> ('v,'r,'a) point \<Rightarrow> ('v,'r,'a) point"
  where
    "stren a p = p\<lparr> wrs := wrs p \<union> wr (inst a), 
                    rds := rds p - (wr (inst a) \<inter> locals) \<union> rd (inst a), 
                    bar := bar p \<union> barriers (inst a) \<rparr>"

text \<open>Weaken a point based on a reorderable instruction\<close>
definition wken :: "('v,'r,'a) subbasic \<Rightarrow> ('v,'r,'a) point \<Rightarrow> ('v,'r,'a) point"
  where
    "wken \<alpha> p = p\<lparr> rds := rds p - wr (inst \<alpha>) \<union> 
                            (if wr (inst \<alpha>) \<inter> rds p \<noteq> {} then Reg ` deps\<^sub>E (exp (inst \<alpha>)) else {}), 
                   esc := esc p \<union> wr (inst \<alpha>),
                   pairs := pairs p \<union> (case inst \<alpha> of cfence \<Rightarrow> {} | _ \<Rightarrow> {(\<alpha>, esc p)}) \<rparr>"

text \<open>Convert an instruction into a point\<close>
abbreviation gen :: "('v,'r,'a) subbasic \<Rightarrow> ('v,'r,'a) point"
  where "gen a \<equiv> \<lparr> op = a, wrs = wr (inst a), 
                   rds = rd (inst a), bar = barriers (inst a), 
                   esc = {}, pairs = {} \<rparr>"

text \<open>Process a new instruction against one point\<close>
definition proc1 :: "('v,'r,'a) subbasic \<Rightarrow> (_,_,_) point \<Rightarrow> (_,_,_) points"
  where "proc1 \<alpha> p \<equiv> if ord (inst \<alpha>) p then {stren \<alpha> p} else {stren \<alpha> p, wken \<alpha> p}"

text \<open>Process a new instruction against a set of points\<close>
definition rif\<^sub>i :: "('v,'r,'a) subbasic \<Rightarrow> (_,_,_) points \<Rightarrow> (_,_,_) points"
  where "rif\<^sub>i a P \<equiv> { gen a } \<union> \<Union> (proc1 a ` P)"

text \<open>Process a sequence\<close>
fun rifseq
  where
    "rifseq [] P = P" | 
    "rifseq (a#t) P = rif\<^sub>i a (rifseq t P)"

text \<open>Process a full program, lifted to low-level choice and loop structures\<close>
fun rif :: "(('v,'r,'a) auxop, ('v,'r,'a) state) com \<Rightarrow> (_,_,_) points \<Rightarrow> (_,_,_) points"
  where 
    "rif (Basic a) P = rif\<^sub>i a P" |
    "rif (Choice c\<^sub>1 c\<^sub>2) P = (rif c\<^sub>1 P \<union> rif c\<^sub>2 P)" |
    "rif (SeqChoice s) P = (if s = {} then P else \<Union>((\<lambda>a. rifseq a P) ` s))" |
    "rif (c\<^sub>1 ;; c\<^sub>2) P = rif c\<^sub>1 (rif c\<^sub>2 P)" |
    "rif (Ord c\<^sub>1 c\<^sub>2) P = rif c\<^sub>1 (rif c\<^sub>2 P)" |
    "rif _ P = P"

subsection \<open>Interference Check\<close>

definition escape
  where "escape V \<alpha> \<equiv> { ((\<beta>,snd (tag \<alpha>)),vc \<alpha>,beh\<^sub>a (\<beta>,snd (tag \<alpha>))) | \<beta>. \<beta> \<in> forall V (inst \<alpha>) }"

definition chk
  where
    "chk \<beta> \<alpha> R G \<equiv> \<forall>\<alpha>'. wfbasic \<beta> \<longrightarrow> reorder_inst \<alpha>' \<beta> \<alpha> \<longrightarrow> guar\<^sub>\<alpha> (fwd\<^sub>s \<alpha> (tag \<beta>)) (step G) \<and> 
                   (\<forall>Q. stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R (wp\<^sub>\<alpha> \<alpha> (stabilize R Q)))) \<subseteq>
                        stabilize R (wp\<^sub>\<alpha> \<alpha>' (stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R Q)))))"

definition chke
  where
    "chke \<beta> \<alpha> R G \<equiv> \<forall>\<alpha> \<in> escape (snd \<beta>) \<alpha>. chk (fst \<beta>) \<alpha> R G"

definition checks
  where "checks P R G \<equiv> \<forall>p \<in> P. \<forall>\<beta> \<in> pairs p. chke \<beta> (op p) R G"

section \<open>Soundness\<close>

subsection \<open>Mono Properties\<close>

text \<open>A series of mono properties to help in reasoning about least-fixed-point\<close>

lemma mono_rif\<^sub>i:
  "mono (rif\<^sub>i a)"
  apply (rule monoI)
  unfolding rif\<^sub>i_def by blast

lemma mono_rifseq:
  "mono (rifseq a)"
proof (induct a)
  case Nil
  then show ?case by (rule monoI) simp 
next
  case (Cons a1 a2)
  then show ?case by simp (meson monoE monoI mono_rif\<^sub>i)
qed  

lemma mono_rif:
  "mono (rif c)"
proof (induct c)
  case (Seq c1 c2)
  then show ?case by (simp add: mono_def)
next
  case (Choice c1 c2)
  then show ?case
    by (smt Un_mono mono_def rif.simps(2))
next
  case (SeqChoice x)
  then show ?case using mono_rifseq by (simp add: mono_def, intro allI impI SUP_mono') auto
next
  case (Ord c1 c2)
  then show ?case by (simp add: mono_def)
qed (simp add: monoI mono_rif\<^sub>i)+

lemma mono_union_rif:
  "mono (\<lambda>Y. P \<union> rif c Y)"
  by (smt Un_mono monoD monoI mono_rif sup.idem sup.order_iff)

lemma lfp_const:
  "x \<in> P \<longrightarrow> x \<in> lfp (\<lambda>Y. P \<union> f Y)"
  by (meson Un_subset_iff basic_trans_rules(31) lfp_greatest)

subsection \<open>Helper Properties\<close>

text \<open>A series of helper properties, generally useful simplifications\<close>

lemma op_proc1 [simp]:
  "\<forall>q \<in> proc1 x p. op q = op p"
  by (auto simp: stren_def wken_def proc1_def)

lemma pairs_proc1:
  "\<forall>q \<in> proc1 x p. pairs q \<supseteq> pairs p"
  unfolding proc1_def stren_def wken_def by clarsimp

lemma proc1_non_nil [intro]:
  "proc1 x p \<noteq> {}"
  unfolding proc1_def stren_def wken_def by clarsimp

lemma [intro]:
  "stren \<alpha> q \<in> proc1 \<alpha> q"
  unfolding proc1_def by auto

subsection \<open>Pairwise Check Properties\<close>

text \<open>Properties of the pairwise interference check\<close>

lemma stabilize':
  "transitive R \<Longrightarrow> stable\<^sub>t R P \<Longrightarrow> P \<subseteq> stabilize R P"
  unfolding stabilize_def transitive_def stable_def step\<^sub>t_def
  by auto

lemma stabilize'':
  "reflexive R \<Longrightarrow> stable\<^sub>t R Q \<Longrightarrow> stabilize R Q = Q"
  unfolding stabilize_def reflexive_def stable_def step\<^sub>t_def
  by auto

text \<open>Pairwise check implies the abstract interference freedom property\<close>
lemma chk_sound:       
  "wellformed R G \<Longrightarrow> chk \<beta> \<alpha> R G \<Longrightarrow> wfbasic \<beta> \<Longrightarrow> reorder_inst \<alpha>' \<beta> \<alpha> \<Longrightarrow> inter\<^sub>\<alpha> (step\<^sub>t R) (step G) \<beta> \<alpha>"
proof (clarsimp simp: inter\<^sub>\<alpha>_def, goal_cases)
  case (1 P M Q)
  \<comment> \<open>Nominate the strongest-postcondition of \<alpha> from P as the state between \<alpha> and \<beta>\<close>  
  let ?M="{m. \<exists>m' m''. m' \<in> P \<and> (m',m'') \<in> beh (fwd\<^sub>s \<alpha> (tag \<beta>)) \<and> (m'',m) \<in> step\<^sub>t R}"
  let ?a="fwd\<^sub>s \<alpha> (tag \<beta>)"

  \<comment> \<open>Establish stability for P, Q and the new intermediate state, in addition to guarantees\<close>
  have stablePQ: "stable\<^sub>t R P" "stable\<^sub>t R Q" "guar\<^sub>\<alpha> \<alpha> (step G)" "guar\<^sub>\<alpha> \<beta> (step G)"
    using 1 by (auto simp: atomic_rule_def)
  have stableM: "stable\<^sub>t R ?M" using 1 unfolding stable_def transitive_def step\<^sub>t_def by force

  \<comment> \<open>Extract order independence properties\<close> 
  have ref: "\<forall>Q. stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R (wp\<^sub>\<alpha> \<alpha> (stabilize R Q)))) \<subseteq>
                 stabilize R (wp\<^sub>\<alpha> ?a (stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R Q))))"
    using 1 by (auto simp: chk_def)
  have g: "guar\<^sub>\<alpha> ((fwd\<^sub>s \<alpha> (tag \<beta>))) (step G)" using 1 by (auto simp: chk_def)

  \<comment> \<open>Show transition from P to Q is independent of order\<close>
  have p: "P \<subseteq> wp\<^sub>\<alpha> \<beta> M" "M \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "M \<subseteq> stabilize R M" "P \<subseteq> stabilize R P" "Q \<subseteq> stabilize R Q"
    using 1 stabilize' unfolding atomic_rule_def by (auto)
  hence "P \<subseteq> stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R (wp\<^sub>\<alpha> \<alpha> (stabilize R Q))))" 
    unfolding wp_def stabilize_def by blast
  hence exec: "P \<subseteq> stabilize R (wp\<^sub>\<alpha> ?a (stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R Q))))" 
    using ref by (auto simp: )
  hence exec': "P \<subseteq> stabilize R (wp\<^sub>\<alpha> ?a (stabilize R (wp\<^sub>\<alpha> \<beta> (Q))))" 
    using stabilize'' stablePQ(2) 1 by force
  hence vc: "P \<subseteq> vc ?a" using 1 by (auto simp: reflexive_def stabilize_def wp_def)

  \<comment> \<open>Establish the late judgement over \<beta>\<close>
  have "step\<^sub>t R,step G \<turnstile>\<^sub>A ?M {\<beta>} Q" 
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "?M \<subseteq> wp\<^sub>\<alpha> \<beta> Q" using exec' 1 
      unfolding wp_def stabilize_def step\<^sub>t_def reflexive_def transitive_def
      apply auto
      by fast
  qed (insert stablePQ stableM, auto)

  \<comment> \<open>Establish the early judgement over the new \<alpha>\<close>
  moreover have "step\<^sub>t R,step G \<turnstile>\<^sub>A P {?a} ?M"
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "P \<subseteq> wp\<^sub>\<alpha> ?a ?M" using vc 1 unfolding wp_def reflexive_def step\<^sub>t_def by auto
  qed (insert stablePQ stableM g, auto)

  ultimately show ?case by blast
qed



fun exec
  where 
    "exec m (subop.op x e) = (m (Reg x :=\<^sub>s ev\<^sub>E (rg m) e))" | 
    "exec m (subop.cstore b x e) = (m (Glb x :=\<^sub>s ev\<^sub>E (rg m) e))" | 
    "exec m (subop.cas\<^sub>T x e\<^sub>1 e\<^sub>2) = (m (Glb x :=\<^sub>s ev\<^sub>E (rg m) e\<^sub>2))" | 
    "exec m _ = m"

lemma beh_fwd\<^sub>i [simp]:
  "beh\<^sub>i (fwd\<^sub>i \<alpha> \<beta>) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) | m m\<^sub>1. (exec m\<^sub>1 \<beta>,m) \<in> beh\<^sub>i \<alpha>}"
  apply (cases \<beta>; auto)
  apply (cases \<alpha>; clarsimp split: if_splits)
  apply (cases \<alpha>; clarsimp split: if_splits)
  apply (cases \<alpha>; clarsimp split: if_splits)
  apply (cases \<alpha>; clarsimp split: if_splits)
  apply (cases \<alpha>; clarsimp split: if_splits)
  apply (cases \<alpha>; clarsimp split: if_splits)+
  done

lemma [simp]:
  "upd (dom (\<lambda>y. if x = y then Some c else M y)) (the \<circ> (\<lambda>y. if x = y then Some c else M y)) m = 
  (upd (dom M) (the o M) m)(x :=\<^sub>s c)"
  apply (auto simp: upd_def st_upd_def intro!: state_rec.equality)
  by force

lemma escE:
  assumes "\<beta> \<in> escape V \<alpha>"
  obtains M where "V = dom M" "vc \<beta> = vc \<alpha>" "beh \<beta> = beh\<^sub>a (smap (inst \<alpha>) M,snd (tag \<alpha>))" "snd (tag \<beta>) = snd (tag \<alpha>)" "inst \<beta> = smap (inst \<alpha>) M" 
  using assms unfolding escape_def forall_def by auto   

lemma ev_upd_exec [simp]:
  "wfbasic \<gamma> \<Longrightarrow> (m,m') \<in> beh \<gamma> \<Longrightarrow> ev\<^sub>E (rg (upd V f (exec m (inst \<gamma>)))) e = ev\<^sub>E (rg (upd V f m')) e"
  apply (rule deps_ev\<^sub>E)
  apply simp
  apply (cases \<gamma> rule: opbasicE) 
  by (auto simp: wfbasic_def)

lemma vc_fwd\<^sub>s[simp]:
  "vc (fwd\<^sub>s \<alpha> \<beta>) = vc \<alpha>"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma beh_fwd\<^sub>s [simp]:
  "beh (fwd\<^sub>s \<alpha> \<beta>) = ( beh\<^sub>a (fwd\<^sub>i (inst \<alpha>) (fst \<beta>), (snd (tag \<alpha>))) )"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: wfbasic_def Let_def split: if_splits)

lemma [simp]:
  "wr \<beta> = {x} \<Longrightarrow> inst (fwd\<^sub>s \<alpha> (\<beta>, f)) = (subst\<^sub>i (inst \<alpha>) x (exp \<beta>))"
  by (cases \<beta>; cases \<alpha>) auto

lemma aux_fwd\<^sub>s [simp]:
  "snd (tag (fwd\<^sub>s \<alpha> \<beta>)) = snd (tag \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma [simp]:
  "wr (inst (fwd\<^sub>s \<alpha> ( \<beta>))) = wr (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma escape_guar:
  assumes "wr \<beta> = {x}" 
  assumes "\<forall>\<alpha>' \<in> escape (insert x V) \<alpha>. guar\<^sub>\<alpha> (fwd\<^sub>s \<alpha>' \<gamma>) (step G)"
  shows "\<forall>\<alpha>' \<in> escape V (fwd\<^sub>s \<alpha> (\<beta>,f)). guar\<^sub>\<alpha> (fwd\<^sub>s \<alpha>' \<gamma>) (step G)"
  unfolding guar_def
proof (auto split: subop.splits elim!: escE, goal_cases)
  case (1 M m\<^sub>1 m\<^sub>2)
  let ?m = "exec m\<^sub>1 (fst \<gamma>)"
  let ?M = "\<lambda>y. (if x = y then Some (ev\<^sub>E (rg (upd (dom M) (the \<circ> M) ?m)) (exp \<beta>)) else M y)"
  let ?i = "smap (inst \<alpha>) ?M"
  let ?\<alpha> = "((?i, snd (tag \<alpha>)), vc \<alpha>, beh\<^sub>a (?i, snd (tag \<alpha>)))"

  have "insert x V = dom ?M" using 1 by auto
  hence "?\<alpha> \<in> escape (insert x V) \<alpha>" unfolding escape_def by auto
  moreover have "m\<^sub>1 \<in> vc (fwd\<^sub>s ?\<alpha> \<gamma>)" using 1 by auto
  moreover have "(m\<^sub>1, (upd (wr (inst \<alpha>)) (st m\<^sub>2) m\<^sub>1)(aux: snd (tag \<alpha>))) \<in> beh (fwd\<^sub>s ?\<alpha> \<gamma>)"
    using 1 assms(1,2)
    apply (clarsimp, intro exI conjI)
      prefer 2
    by simp+

  ultimately show ?case using assms unfolding guar_def by blast
qed

lemma escape_wp:
  assumes "wfbasic \<gamma>" "wr \<beta> = {x}"
  assumes "\<forall>\<alpha>' \<in> escape (insert x V) \<alpha>. stabilize R (wp\<^sub>\<alpha> \<gamma> (stabilize R (wp\<^sub>\<alpha> \<alpha>' (stabilize R Q)))) \<subseteq>
                                      stabilize R (wp\<^sub>\<alpha> (fwd\<^sub>s \<alpha>' (tag \<gamma>)) (stabilize R (wp\<^sub>\<alpha> \<gamma> (stabilize R Q))))"
  shows "\<forall> \<alpha>' \<in> escape V (fwd\<^sub>s \<alpha> (\<beta>,f)). 
    \<forall>\<alpha>''. reorder_inst \<alpha>'' \<gamma> \<alpha>' \<longrightarrow> stabilize R (wp\<^sub>\<alpha> \<gamma> (stabilize R (wp\<^sub>\<alpha> \<alpha>' (stabilize R Q)))) \<subseteq>
                              stabilize R (wp\<^sub>\<alpha> (fwd\<^sub>s \<alpha>' (tag \<gamma>)) (stabilize R (wp\<^sub>\<alpha> \<gamma> (stabilize R Q))))" 
proof (intro allI impI ballI subsetI, elim escE, goal_cases)
  case (1 \<alpha>' \<alpha>'' m M)
  let ?m = "exec m (inst \<gamma>)"
  let ?M = "\<lambda>y. (if x = y then Some (ev\<^sub>E (rg (upd (dom M) (the \<circ> M) ?m)) (exp \<beta>)) else M y)"
  let ?i = "smap (inst \<alpha>) ?M"
  let ?\<alpha> = "((?i, snd (tag \<alpha>)), vc \<alpha>, beh\<^sub>a (?i, snd (tag \<alpha>)))"

  have "insert x V = dom ?M" using 1 by auto
  hence esc: "?\<alpha> \<in> escape (insert x V) \<alpha>" unfolding escape_def by auto

  have e: "\<forall>m'. rg m = rg m' \<longrightarrow> 
      ev\<^sub>E (rg (upd (dom M) (the \<circ> M) (exec m (inst \<gamma>)))) (exp \<beta>) =
      ev\<^sub>E (rg (upd (dom M) (the \<circ> M) (exec m' (inst \<gamma>)))) (exp \<beta>)"
    by (intro allI impI ballI deps_ev\<^sub>E) (cases "inst \<gamma>"; simp)

  have "m \<in> stabilize R (wp\<^sub>\<alpha> \<gamma> (stabilize R (wp\<^sub>\<alpha> ?\<alpha> (stabilize R Q))))"
    using 1 assms(2)
    unfolding stabilize_def wp_def
    apply auto
    apply (rename_tac m\<^sub>1 m\<^sub>2 m\<^sub>4 m\<^sub>3 m\<^sub>5)
    apply (subgoal_tac "ev\<^sub>E (rg (upd (dom M) (the \<circ> M) ?m)) (exp \<beta>) = ev\<^sub>E (rg (upd (dom M) (the \<circ> M) m\<^sub>3)) (exp \<beta>)")
    apply fastforce
    apply (subgoal_tac "ev\<^sub>E (rg (upd (dom M) (the \<circ> M) m\<^sub>2)) (exp \<beta>) = ev\<^sub>E (rg (upd (dom M) (the \<circ> M) m\<^sub>3)) (exp \<beta>)")
    apply (subgoal_tac "ev\<^sub>E (rg (upd (dom M) (the \<circ> M) (exec m\<^sub>1 (inst \<gamma>)))) (exp \<beta>) = ev\<^sub>E (rg (upd (dom M) (the \<circ> M) m\<^sub>2)) (exp \<beta>)")
    using e assms(1) apply force
    using assms(1) apply auto[1]
    by (rule deps_ev\<^sub>E) (auto)

  hence "m \<in> stabilize R (wp\<^sub>\<alpha> (fwd\<^sub>s ?\<alpha> (tag \<gamma>)) (stabilize R (wp\<^sub>\<alpha> \<gamma> (stabilize R Q))))"
    using assms(3) 1 esc by blast
  thus ?case using 1(4,5,6,7) assms(2)
    unfolding stabilize_def wp_def 
    apply auto
     apply (clarsimp simp add: e)
    apply fastforce
    apply (clarsimp simp add: e)
    by fastforce
qed

lemma [simp]:
  "wr (subst\<^sub>g \<alpha> x22 x23) = wr \<alpha>"
  by (cases \<alpha>; auto)

lemma substg_rd [simp]:
  "rd (subst\<^sub>g \<alpha> x e) = rd \<alpha> - {Glb x} \<union> (if Glb x \<in> rd \<alpha> then Reg ` deps\<^sub>E e else {})"
  by (cases \<alpha>; auto)

lemma substr_rd [simp]:
  "rd (subst\<^sub>r \<alpha> x e) = rd \<alpha> - {Reg x} \<union> (if Reg x \<in> rd \<alpha> then Reg ` deps\<^sub>E e else {})"
  by (cases \<alpha>; auto)

lemma substr_wr [simp]:
  "wr (subst\<^sub>r \<alpha> x e) = wr \<alpha>"
  by (cases \<alpha>; auto)

lemma [simp]:
  "barriers \<alpha> = {fence} \<Longrightarrow> \<alpha> = fence"
  "barriers \<alpha> = {stfence} \<Longrightarrow> \<alpha> = stfence"
  "barriers \<alpha> = {cfence} \<Longrightarrow> \<alpha> = cfence"
  by (cases \<alpha>; auto)+

lemma reorder_imp:
  assumes "re\<^sub>i \<beta> \<alpha>"
  assumes "barriers \<alpha> = barriers \<alpha>'"
  assumes "wr \<alpha> = wr \<alpha>'"
  assumes "rd \<alpha>' \<subseteq> rd \<alpha>"
  shows "re\<^sub>i \<beta> \<alpha>'"
  using assms
  apply (cases \<beta>; clarsimp)
  by (intro conjI; clarsimp; blast)+

lemma fwd_barriers [simp]:
  "barriers (fwd\<^sub>i \<alpha> \<beta>) = barriers \<alpha>"
  by (cases \<alpha>; cases \<beta>; auto)

lemma escape_barriers [simp]:
  "\<forall>\<alpha> \<in> escape V \<beta>. barriers (inst \<alpha>) = barriers (inst \<beta>)"
  unfolding escape_def by auto

lemma [simp]:
  "inst (fwd\<^sub>s \<alpha> \<beta>) = fwd\<^sub>i (inst \<alpha>) (fst \<beta>)"
  by (cases \<beta>; cases \<alpha>; auto)

lemma fwd_wr [simp]:
  "wr (fwd\<^sub>i \<alpha> \<beta>) = wr \<alpha>"
  by (cases \<alpha>; cases \<beta>; auto)

lemma escape_wr [simp]:
  "\<forall>\<alpha> \<in> escape V \<beta>. wr (inst \<alpha>) = wr (inst \<beta>)"
  unfolding escape_def by auto

lemma fwd_rd [simp]:
  "rd (fwd\<^sub>i \<alpha> \<beta>) = (if wr \<beta> \<inter> rd \<alpha> \<noteq> {} then rd \<alpha> - wr \<beta> \<union>  Reg ` deps\<^sub>E (exp \<beta>) else rd \<alpha>)"
  by (cases \<alpha>; cases \<beta>; auto)

lemma escape_rd [simp]:
  "\<forall>\<alpha> \<in> escape V \<beta>. rd (inst \<alpha>) = rd (inst \<beta>) - V"
  unfolding escape_def by auto

lemma escape_reorder:
  assumes "\<alpha>' \<in> escape V (fwd\<^sub>s \<alpha> \<beta>)" "reorder_inst \<alpha>'' \<gamma> \<alpha>'"
  shows "\<forall>\<alpha>'\<in>escape (wr (fst \<beta>) \<union> V) \<alpha>. \<exists>\<alpha>''. reorder_inst \<alpha>'' \<gamma> \<alpha>'"
  using assms
proof (intro ballI, goal_cases)
  case (1 \<alpha>'')
  hence a: "re\<^sub>i (inst \<gamma>) (fwd\<^sub>i (inst \<alpha>') (inst \<gamma>))"
    by (cases \<gamma>, cases \<alpha>', clarsimp)
  hence "re\<^sub>i (inst \<gamma>) (fwd\<^sub>i (inst \<alpha>'') (inst \<gamma>))"
    apply (rule reorder_imp) 
    using 1 by auto
  then show ?case by (cases \<gamma>, cases \<alpha>'', clarsimp)
qed

lemma escape_check:
  assumes "wr \<beta> = {x}"
  assumes "\<forall>\<alpha>' \<in> escape (wr \<beta> \<union> V) \<alpha>. chk \<gamma> \<alpha>' R G"
  shows "\<forall>\<alpha>' \<in> escape V (fwd\<^sub>s \<alpha> (\<beta>,f)). chk \<gamma> \<alpha>' R G"
  unfolding chk_def
proof (intro ballI allI impI conjI, goal_cases)
  case (1 \<alpha>' \<alpha>'')
  hence "\<forall>\<alpha>' \<in> escape (wr \<beta> \<union> V) \<alpha>. guar\<^sub>\<alpha> (fwd\<^sub>s \<alpha>' (tag \<gamma>)) (step G)"
    using assms(2) escape_reorder[OF 1(1)] by (auto simp: chk_def)
  then show ?case using escape_guar[OF assms(1), of V \<alpha> "tag \<gamma>"] 1 unfolding assms(1) by simp
next
  case (2 \<alpha>' \<alpha>'' Q)
  hence "\<forall>\<alpha>' \<in> escape (wr \<beta> \<union> V) \<alpha>. stabilize R (wp\<^sub>\<alpha> \<gamma> (stabilize R (wp\<^sub>\<alpha> \<alpha>' (stabilize R Q)))) \<subseteq>
      stabilize R (wp\<^sub>\<alpha> (fwd\<^sub>s \<alpha>' (tag \<gamma>)) (stabilize R (wp\<^sub>\<alpha> \<gamma> (stabilize R Q))))"
    using assms(2) escape_reorder[OF 2(1)] by (auto simp: chk_def)
  then show ?case using escape_wp[OF 2(2) assms(1), of V] 2 assms unfolding assms(1) by simp
qed

text \<open>
Given two reorderable instructions, escaping the writes of the earlier instruction
implies a check over the forwarded variant.
\<close>
lemma chke_sound:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>" "wfbasic \<beta>" "wfbasic \<alpha>"
  assumes "chke (\<gamma>, wr (inst \<beta>) \<union> V) \<alpha> R G" 
  shows "chke (\<gamma>, V) \<alpha>' R G"
  unfolding chke_def
proof (intro ballI allI impI, simp)
  fix \<alpha>'' assume e: "\<alpha>'' \<in> escape V \<alpha>'"
  show "chk \<gamma> \<alpha>'' R G" using assms(1)
  proof (cases rule: fwdE)
    case no_fwd
    hence "forall V (inst \<alpha>') = forall (wr (inst \<beta>) \<union> V) (inst \<alpha>)"
      by (cases "inst \<beta>") fastforce+
    hence "escape V \<alpha>' = escape (wr (inst \<beta>) \<union> V) \<alpha>"
      using no_fwd unfolding escape_def by simp
    thus ?thesis using e assms(4) unfolding chke_def by auto
  next
    case (fwd x)
    thus ?thesis using fwd escape_check[of "inst \<beta>" x V \<alpha>] e assms(1,4) 
      unfolding chke_def by (cases "tag \<beta>") simp
  qed
qed

text \<open>Escape check with an empty escape set implies a full check\<close>
lemma chke_nil_esc:
  assumes "chke (\<beta>, {}) \<alpha> R G" "wfbasic \<alpha>"
  shows "chk \<beta> \<alpha> R G"
proof -
  have "\<alpha> \<in> escape {} \<alpha>" using assms(2) by (cases \<alpha>; auto simp: wfbasic_def escape_def) 
  thus "chk \<beta> \<alpha> R G" using assms by (auto simp:  chke_def)
qed

text \<open>\<close>
lemma inter_cfence:
  assumes "inst \<beta> = cfence" "wfbasic \<beta>" "wfbasic \<alpha>" "reorder_inst \<alpha>' \<beta> \<alpha>" "wellformed R G"
  shows "inter\<^sub>\<alpha> (step\<^sub>t R) (step G) \<beta> \<alpha>"
proof (clarsimp simp: inter\<^sub>\<alpha>_def, goal_cases)
  case (1 P M Q)
  \<comment> \<open>Nominate the strongest-postcondition of \<alpha> from P as the state between \<alpha> and \<beta>\<close>  
  let ?M="{m. \<exists>m' m''. m' \<in> P \<and> (m',m'') \<in> beh (fwd\<^sub>s \<alpha> (tag \<beta>)) \<and> (m'',m) \<in> step\<^sub>t R}"
  let ?a="fwd\<^sub>s \<alpha> (tag \<beta>)"

  \<comment> \<open>Establish stability for P, Q and the new intermediate state, in addition to guarantees\<close>
  have stablePQ: "stable\<^sub>t R P" "stable\<^sub>t R Q" "guar\<^sub>\<alpha> \<alpha> (step G)" "guar\<^sub>\<alpha> \<beta> (step G)"
    using 1 by (auto simp: atomic_rule_def)
  have stableM: "stable\<^sub>t R ?M" using 1 assms unfolding stable_def transitive_def step\<^sub>t_def by force

  have \<beta>: "beh \<beta> = {(m,m'). m = m'}" "vc \<beta> = UNIV"
    using assms(1,2) unfolding wfbasic_def by auto
  have [simp]: "fwd\<^sub>s \<alpha> (tag \<beta>) = \<alpha>"
    using assms(1,3) 
    by (cases \<alpha> rule: opbasicE; cases "tag \<beta>"; clarsimp simp: wfbasic_def)

  \<comment> \<open>Show transition from P to Q is independent of order\<close>
  have p: "P \<subseteq> wp\<^sub>\<alpha> \<beta> M" "M \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "M \<subseteq> stabilize R M" "P \<subseteq> stabilize R P" "Q \<subseteq> stabilize R Q"
    using 1 assms stabilize' unfolding atomic_rule_def by (auto)
  hence "P \<subseteq> stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R (wp\<^sub>\<alpha> \<alpha> (stabilize R Q))))" 
    unfolding wp_def stabilize_def by blast

  \<comment> \<open>Establish the late judgement over \<beta>\<close>
  have "step\<^sub>t R,step G \<turnstile>\<^sub>A Q {\<beta>} Q"
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "Q \<subseteq> wp\<^sub>\<alpha> \<beta> Q" by (auto simp: wp_def \<beta>)
  qed (insert stablePQ stableM, auto)

  \<comment> \<open>Establish the early judgement over the new \<alpha>\<close>
  moreover have "step\<^sub>t R,step G \<turnstile>\<^sub>A P {?a} Q"
  proof (unfold atomic_rule_def, intro conjI Int_greatest)
    show "P \<subseteq> wp\<^sub>\<alpha> ?a Q" using p by (auto simp: wp_def \<beta>)
  qed (insert stablePQ stableM, auto)

  ultimately show ?case by blast
qed  

subsection \<open>Silent rif Checks\<close>

lemma [simp]:
  "rif (seq2com s) P = rifseq s P"
  by (induct s, auto)

text \<open>Trivial proof showing rif is preserved across silent steps\<close>
lemma silent_rif_checks:
  assumes "c \<leadsto> c'" "sim c"
  shows "rif c' P \<subseteq> rif c P"
  using assms
proof (induct arbitrary: P)
  case (seq2 c\<^sub>2 c\<^sub>2' c\<^sub>1)
  then show ?case by (simp add: monoD mono_rif)
qed auto

subsection \<open>Execution rif Checks\<close>

text \<open>The ord test shouldn't establish dependencies between reorderable operations\<close>
lemma ord_sound [intro]:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  shows "\<not> ord (inst \<beta>) (gen \<alpha>)"
  using assms 
  apply (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE) 
  apply (clarsimp simp: hasGlobal_def)+
  done

text \<open>
Show that the checks produced by an instruction \<alpha> with a prefix r are sufficient
to establish the desired abstract rif properties.
\<close>

text \<open>
Relate two points such that their reordering constraints are the same,
but the checks of one implies the checks of the other, including all future checks.
\<close>
definition point_ord (infix "\<prec>" 60)
  where "point_ord p q \<equiv>  
            wrs p = wrs q \<and> rds p = rds q \<and> (bar p = bar q) \<and> 
            (\<forall>R G (\<alpha> :: ('v,'r,'a) subbasic) V. 
              chke (\<alpha>, esc p \<union> V) (op p) R G \<longrightarrow> chke (\<alpha>, esc q \<union> V) (op q) R G) \<and>
            (\<forall>R G. (\<forall>\<beta> \<in> pairs p. chke \<beta> (op p) R G) \<longrightarrow> (\<forall>\<beta> \<in> pairs q. chke \<beta> (op q) R G))"

text \<open>
Extend this point relation over two sets of points, such that for all points in the RHS,
one exists in the LHS that establishes the relation.
\<close>
definition points_ord (infix "\<prec>\<prec>" 60)
  where "points_ord P Q \<equiv> \<forall>q \<in> Q. \<exists>p \<in> P. p \<prec> q"

text \<open>The point relation is reflexive\<close>
lemma point_ord_refl [intro]:
  "p \<prec> p" 
  by (auto simp: point_ord_def)

text \<open>The point relation is preserved across stren\<close>
lemma point_ord_stren [intro]:
  "p \<prec> q \<Longrightarrow> stren \<alpha> p \<prec> stren \<alpha> q"
  by (auto simp: point_ord_def stren_def)

text \<open>The point relation is preserved across wken\<close>
lemma point_ord_wken [intro]:
  "p \<prec> q \<Longrightarrow> wken \<alpha> p \<prec> wken \<alpha> q"
  unfolding point_ord_def wken_def
  apply (auto simp: Un_assoc sup_assoc split: subop.splits)
  by (cases \<alpha>; case_tac a; metis sup_bot_right)+

text \<open>The point relation ensures equivalent ordering constraints\<close>
lemma point_ord [simp]:
  "p \<prec> q \<Longrightarrow> ord \<alpha> p = ord \<alpha> q"
  by (cases \<alpha>) (clarsimp simp: point_ord_def)+

text \<open>Based on the above, proc1 preserves the point relation\<close>
lemma point_ord_proc1 [intro]:
  "p \<prec> q \<Longrightarrow> proc1 \<alpha> p \<prec>\<prec> proc1 \<alpha> q"
  unfolding points_ord_def proc1_def by auto

text \<open>Based on the above, proci preserves the point relation\<close>
lemma points_ord_rif\<^sub>i [intro]:
  "P \<prec>\<prec> Q \<Longrightarrow> rif\<^sub>i \<alpha> P \<prec>\<prec> rif\<^sub>i \<alpha> Q"
  using point_ord_proc1 unfolding rif\<^sub>i_def points_ord_def by fast

lemma points_ord_rifseq [intro]:
  "P \<prec>\<prec> Q \<Longrightarrow> rifseq a P \<prec>\<prec> rifseq a Q"
  by (induct a, auto)

lemma points_ord_union [intro]:
  "P \<prec>\<prec> Q \<Longrightarrow> P' \<prec>\<prec> Q' \<Longrightarrow> P \<union> P' \<prec>\<prec> Q \<union> Q'"
  by (auto simp: points_ord_def)

text \<open>Finally, rif preserves the point relation\<close>
lemma points_ord_rif [intro]:
  "P \<prec>\<prec> Q \<Longrightarrow> rif c P \<prec>\<prec> rif c Q"
proof (induct c arbitrary: P Q)
  case (SeqChoice x)
  then show ?case using points_ord_rifseq[OF SeqChoice] 
    by (auto simp: points_ord_def) blast
qed auto

lemma [simp]:
  "wr (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = wr (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)

lemma [simp]:
  "barriers (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = barriers (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)

lemma [simp]:
  "rd (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = 
    (if wr (inst \<beta>) \<inter> rd (inst \<alpha>) \<noteq> {} then rd (inst \<alpha>) - wr (inst \<beta>) \<union>  Reg ` deps\<^sub>E (exp (inst \<beta>)) 
    else rd (inst \<alpha>))"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto)

text \<open>Establish the point relation between \<alpha> weakened by \<beta> and one generated from \<alpha>' directly\<close>
lemma point_ord_fwd:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>" "wfbasic \<beta>" "wfbasic \<alpha>"
  shows "wken \<beta> (gen \<alpha>) \<prec> gen \<alpha>'"
  using assms apply (auto simp: point_ord_def wken_def)
  by (insert chke_sound, blast)+

text \<open>Checks against the LHS of a points relation imply checks against the RHS\<close>
lemma points_ord_checks [intro]:
  "checks P R G \<Longrightarrow> P \<prec>\<prec> Q \<Longrightarrow> checks Q R G"
  unfolding checks_def points_ord_def point_ord_def by metis

lemma rifseq_checks_postfix [intro]:
  assumes "checks (rifseq a P) R G"
  shows "checks P R G"
  using assms
proof (induct a arbitrary: P)
  case Nil
  then show ?case by auto
next
  case (Cons a1 a2)
  hence "checks (rifseq a2 P) R G" unfolding checks_def
  proof (intro ballI)
    fix p \<beta> assume a: "p \<in> rifseq a2 P" "\<beta> \<in> pairs p"
    hence "\<exists>q \<in> proc1 a1 p. \<beta> \<in> pairs q" using pairs_proc1 proc1_non_nil by blast
    thus "chke \<beta> (op p) R G"
      using Cons a by (auto simp: checks_def rif_def rif\<^sub>i_def)
  qed
  thus ?case using Cons by auto
qed

text \<open>rif checks on sequential composition should imply rif checks of just the postfix\<close>
lemma rif_checks_postfix [intro]:
  assumes "checks (rif (c ;; r) P) R G"
  shows "checks (rif r P) R G"
  using assms
proof (induct c arbitrary: r P)
  case (Basic x)
  show ?case unfolding checks_def
  proof (intro ballI)
    fix p \<beta> assume a: "p \<in> rif r P" "\<beta> \<in> pairs p"
    hence "\<exists>q \<in> proc1 x p. \<beta> \<in> pairs q" using pairs_proc1 proc1_non_nil by blast
    thus "chke \<beta> (op p) R G"
      using Basic a by (auto simp: checks_def rif_def rif\<^sub>i_def)
  qed
next
  case (Loop c)
  thus ?case by (simp add: lfp_const checks_def) 
next
  case (SeqChoice x)
  then show ?case using rifseq_checks_postfix
    unfolding checks_def by (simp split: if_splits) fastforce
qed (unfold checks_def rif.simps; blast)+

text \<open>rif checks on sequential composition should imply rif checks of just the prefix\<close>
lemma rif_checks_prefix [intro]:
  assumes "checks (rif (c ;; r) P) R G"
  shows "checks (rif c {}) R G"
  using assms
proof -
  have "rif c {} \<subseteq> rif c (rif r P)" by (simp add: monoD mono_rif)
  thus ?thesis using assms unfolding checks_def by auto
qed

text \<open>
rif checks on sequential composition due to an action that can reorder with the postfix
correspond to the checks that would be seen if the postfix wasn't present and forwarding
was captured fully.
\<close>
lemma rif_checks_fwd:
  assumes "reorder_com \<alpha>' c\<^sub>2 \<alpha>" "wfcom c\<^sub>2" "wfbasic \<alpha>" "sim c\<^sub>2"
  assumes "checks (rif (c\<^sub>1 ;; c\<^sub>2 ;; Basic \<alpha>) {}) R G" 
  shows "checks (rif (c\<^sub>1 ;; Basic \<alpha>') {}) R G"
  using assms
proof (induct \<alpha>' c\<^sub>2 \<alpha> arbitrary: c\<^sub>1 rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  text \<open>Remove the checks on gen \<beta>\<close>
  hence "checks (rif c\<^sub>1 ({gen \<beta>} \<union> proc1 \<beta> (gen \<alpha>))) R G"
    by (auto simp: rif\<^sub>i_def)
  hence c: "checks (rif c\<^sub>1 (proc1 \<beta> (gen \<alpha>))) R G"
    unfolding checks_def using mono_Un mono_rif by blast
  text \<open>Show the point relation between \<alpha> and \<alpha>'\<close>
  have r: "reorder_inst \<alpha>' \<beta> \<alpha>" using 2 by auto
  have "proc1 \<beta> (gen \<alpha>) \<prec>\<prec> {gen \<alpha>'}" 
    using point_ord_fwd[OF r] ord_sound[OF r] 2(2,3) 
    unfolding points_ord_def proc1_def wfcom_def by auto
  text \<open>Use properties of the point relation to establish checks on c1 and \<alpha>'\<close>
  hence "rif c\<^sub>1 (proc1 \<beta> (gen \<alpha>)) \<prec>\<prec> rif c\<^sub>1 {gen \<alpha>'}" by auto
  hence "checks (rif c\<^sub>1 {gen \<alpha>'}) R G" using c by blast
  then show ?case by (auto simp: rif\<^sub>i_def)
next
  case (3 \<alpha>' c\<^sub>1' c\<^sub>2 \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "reorder_com \<alpha>' c\<^sub>1' \<alpha>''" "reorder_com \<alpha>'' c\<^sub>2 \<alpha>" by auto
  hence "checks (rif (c\<^sub>1 ;; c\<^sub>1' ;; Basic \<alpha>'') {}) R G" 
    using 3(2)[of _ "c\<^sub>1 ;; c\<^sub>1'"] 3(4,5,6,7) by (auto simp: wfcom_def)
  moreover have "wfbasic \<alpha>''" using 3 \<alpha> fwd_wfbasic by blast
  ultimately show ?case using \<alpha> 3 by auto
next
  case (4 \<alpha>' c\<^sub>1' c\<^sub>2 \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "reorder_com \<alpha>' c\<^sub>1' \<alpha>''" "reorder_com \<alpha>'' c\<^sub>2 \<alpha>" by auto
  hence "checks (rif (c\<^sub>1 ;; c\<^sub>1' ;; Basic \<alpha>'') {}) R G" 
    using 4(2)[of _ "c\<^sub>1 ;; c\<^sub>1'"] 4(4,5,6,7) by (auto simp: wfcom_def)
  moreover have "wfbasic \<alpha>''" using 4 \<alpha> fwd_wfbasic by blast
  ultimately show ?case using \<alpha> 4 by auto
qed auto 

text \<open>Convert an execution step to a reordering\<close>
lemma exec_to_reorder:
  assumes "lexecute c r \<alpha> c'"
  shows "\<exists>\<alpha>'. reorder_com \<alpha>' r \<alpha>"
  using assms
  by (induct, unfold reorder_com.simps(1); blast)

text \<open>Phrase the desired property for induction over a reordering\<close>
lemma exec_checks_induct:
  assumes "wellformed R G" "wfcom r" "wfbasic \<alpha>" "sim r"
  assumes "reorder_com \<alpha>' r \<alpha>"
  assumes "checks (rif (r ;; Basic \<alpha>) {}) R G"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct \<alpha>' r \<alpha> rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  hence r: "reorder_inst \<alpha>' \<beta> \<alpha>" "wfbasic \<beta>" by (auto simp: wfcom_def)
  text \<open>Given the two instructions can reorder, they mustn't be considered ordered\<close>
  hence "\<not> ord (inst \<beta>) (gen \<alpha>)" using ord_sound[of \<alpha>' \<alpha> \<beta>] by auto
  text \<open>Obtain the point generated for \<alpha>\<close>
  then obtain p where "p \<in> rif\<^sub>i \<beta> (rif\<^sub>i \<alpha> {})" "op p = \<alpha>" "(\<beta>,{}) \<in> pairs p \<or> inst \<beta> = cfence"
    unfolding rif\<^sub>i_def proc1_def stren_def wken_def
    apply (clarsimp split: if_splits subop.splits)
    by (cases "inst \<beta>"; fastforce)
  text \<open>Extract the check between \<beta> and \<alpha> and show it establishes inter\<close>
  hence "chke (\<beta>,{}) \<alpha> R G \<or> inst \<beta> = cfence" using 2(6) by (auto simp: checks_def)
  thus ?case using chk_sound chke_nil_esc 2(1,3) r inter_cfence  unfolding inter\<^sub>c.simps by blast
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "reorder_com \<alpha>' c\<^sub>1 \<alpha>''" "reorder_com \<alpha>'' c\<^sub>2 \<alpha>" by auto
  hence w:  "wfbasic \<alpha>''" using 3(4,5) fwd_wfbasic by blast
  hence "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>2 \<alpha>" using 3 rif_checks_postfix by fastforce
  moreover have "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>1 \<alpha>''" 
    using \<alpha> 3(1)[OF 3(3) _ w _ \<alpha>(1)] 3(4,6,8)
    using  rif_checks_fwd[OF \<alpha>(2) _ 3(5), of c\<^sub>1]  by simp
  ultimately show ?case using \<alpha> by auto
next
  case (4 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "reorder_com \<alpha>' c\<^sub>1 \<alpha>''" "reorder_com \<alpha>'' c\<^sub>2 \<alpha>" by auto
  hence w:  "wfbasic \<alpha>''" using 4(4,5) fwd_wfbasic by blast
  hence "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>2 \<alpha>" using 4 rif_checks_postfix by fastforce
  moreover have "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>1 \<alpha>''" 
    using \<alpha> 4(1)[OF 4(3) _ w _ \<alpha>(1)] 4(4,6,8)
    using  rif_checks_fwd[OF \<alpha>(2) _ 4(5), of c\<^sub>1]  by simp
  ultimately show ?case using \<alpha> by auto
qed auto 

text \<open>rif should perform checks on any instruction that can reorder before some prefix\<close>
lemma exec_rif_checks:
  assumes "wellformed R G" "wfcom r" "wfbasic \<alpha>" "sim r"
  assumes "lexecute c r \<alpha> c'"
  assumes "checks (rif (r ;; Basic \<alpha>) {}) R G"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms exec_to_reorder exec_checks_induct by blast

subsection \<open>Remaining rif Checks\<close>

text \<open>
It is necessary to show that the early execution of an instruction does not result in
a remaining program for which rif no longer holds. 
We demonstrate this by relating two versions of the analysis, one where the executed
instruction has been considered and one where it is not.
We then demonstrate that checks against the version with the instruction present imply
those where it is not.
\<close>

text \<open>
Compare two points ignoring the implications of some instruction \<alpha>,
such that the checks of the LHS are implied by those of the RHS and the
reordering constraints of the LHS are stronger than the RHS ignoring \<alpha>.
\<close>
definition point_ign :: "('v,'r,'a) point \<Rightarrow> (_,_,_) subbasic \<Rightarrow> (_,_,_) point \<Rightarrow> bool" 
  ("_ \<sim>\<^sub>_ _" [0,100,0] 60)
  where "point_ign p \<alpha> q \<equiv> 
     wrs p \<subseteq> wrs q \<union> wr (inst \<alpha>) \<and> 
     rds p \<subseteq> rds q \<union> (wrs q - locals) \<union> rd (inst \<alpha>) \<and> 
     (bar p \<subseteq> bar q \<union> (if hasGlobal (wrs q) then {cfence} else {}) \<union> barriers (inst \<alpha>)) \<and>
     (op p = op q) \<and>
     (esc p = esc q) \<and>
     (pairs p \<supseteq> pairs q)"

lemma [intro]:
  "p \<sim>\<^sub>\<alpha> p"
  by (auto simp: point_ign_def)

text \<open>
Extend the point comparison over two sets of points, such that there exists a point in
the RHS for all in the LHS.
\<close>
definition points_ign :: "('v,'r,'a) points \<Rightarrow> (_,_,_) subbasic \<Rightarrow> (_,_,_) points \<Rightarrow> bool"
  ("_ \<approx>\<^sub>_ _" [0,100,0] 60)
  where "points_ign P \<alpha> Q \<equiv> \<forall>q \<in> Q. \<exists>p \<in> P. (p \<sim>\<^sub>\<alpha> q)"

text \<open>
Given an instruction that the ignored operation can reorder before, q should have
stronger reordering constraints than p.
\<close>
lemma point_ign_ord:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>" "inst \<beta> \<noteq> cfence"
  assumes "p \<sim>\<^sub>\<alpha> q"
  shows "ord (inst \<beta>) p \<longrightarrow> ord (inst \<beta>) q"
proof (cases \<beta> rule: opbasicE)
  case (op x e f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
      clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (cmp g f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
      clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (fence f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
    clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (cfence f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
    clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (stfence f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
    clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (load x e f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
    clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (store x e f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
    clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (cas\<^sub>T x e1 e2 f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
    clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (cas\<^sub>F x e1 f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
    clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
next
  case (nop f v b)
  then show ?thesis by (insert assms, cases \<alpha> rule: opbasicE; 
    clarsimp simp: point_ign_def hasGlobal_def split: if_splits; blast)
qed

text \<open>
The point_ign relation is preserved across updates due to an instruction that the
ignored instruction can reorder before.
\<close>
lemma point_ign_pres:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>" "p \<sim>\<^sub>\<alpha> q" "q' \<in> proc1 \<beta> q"
  shows "\<exists>p'\<in>proc1 \<beta> p. (p' \<sim>\<^sub>\<alpha>' q')"
proof (cases "q' = stren \<beta> q")
  case True
  moreover have "stren \<beta> p \<sim>\<^sub>\<alpha>' (stren \<beta> q)" 
    using assms(1,2) by (auto simp: stren_def point_ign_def hasGlobal_def split: if_splits)
  ultimately show ?thesis by blast
next
  case False
  text \<open>Must have weakened due to out-of-order otherwise\<close>
  hence q: "q' = wken \<beta> q" "\<not> ord (inst \<beta>) q" 
    using assms(3) unfolding proc1_def by (auto split: if_splits)
  text \<open>Therefore, \<beta> can't have a global write in common with q\<close>
  hence wr: "(wr (inst \<beta>) - locals) \<inter> wrs q = {}"
    by (cases "inst \<beta>"; auto split: var.splits)

  show ?thesis
  proof (cases "inst \<beta> = cfence")
    case True
    hence "fence \<notin> barriers (inst \<alpha>) \<and> rd (inst \<alpha>) \<subseteq> locals"
      using assms(1) by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE) auto
    hence "ord (inst \<beta>) p \<Longrightarrow> (stren \<beta> p) \<sim>\<^sub>\<alpha>' (wken \<beta> q)"
      using assms(1,2) q(2) by (auto simp: hasGlobal_def True stren_def wken_def point_ign_def)
    moreover have "\<not>ord (inst \<beta>) p \<Longrightarrow> wken \<beta> p \<sim>\<^sub>\<alpha>' (wken \<beta> q)"
      using assms(1,2) q(2) by (auto simp: True wken_def point_ign_def)
    ultimately show ?thesis using q(1) unfolding proc1_def by auto
  next
    case False
    text \<open>Also, \<beta> can't be ordered with p due to q's stronger constraints\<close>
    hence "\<not> ord (inst \<beta>) p" using q point_ign_ord assms(1,2) by blast
    text \<open>Therefore, \<beta> must weaken p as well\<close>
    hence "wken \<beta> p \<in> proc1 \<beta> p" unfolding proc1_def by auto
    text \<open>wken preserves the relation\<close>
    moreover have "wken \<beta> p \<sim>\<^sub>\<alpha>' (wken \<beta> q)"
      using assms(1,2) wr unfolding wken_def point_ign_def
      apply (intro conjI)
      apply (clarsimp; blast)+
      by (auto split: subop.splits)
    ultimately show ?thesis using q(1) by blast
  qed
qed

text \<open>
It is possible to establish the points_ign relation between P and a version of P
updated using the ignored instruction.
\<close>
lemma points_ignI [intro]:
  shows "rif (Basic \<alpha>) P \<approx>\<^sub>\<alpha> P"
proof (simp add: points_ign_def rif\<^sub>i_def, intro ballI disjI2)
  fix q assume "q \<in> P"
  moreover have "stren \<alpha> q \<sim>\<^sub>\<alpha> q" by (auto simp: stren_def point_ign_def)
  ultimately show "\<exists>y\<in>P. \<exists>p\<in>proc1 \<alpha> y. (p \<sim>\<^sub>\<alpha> q)" by auto
qed

text \<open>
It is also possible to preserve the points_ign relation across a program that
the ignored instruction can reorder before.
\<close>
lemma points_ign_presI [intro]:
  assumes "reorder_com \<beta> r \<alpha>" "sim r"
  assumes "P \<approx>\<^sub>\<alpha> Q"
  shows "rif r P \<approx>\<^sub>\<beta> (rif r Q)"
  using assms
proof (induct \<beta> r \<alpha> arbitrary: P Q rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  then show ?case using point_ign_pres by (simp add: rif\<^sub>i_def points_ign_def) blast
qed auto

text \<open>
Checks against the RHS of the points_ign relation implies checks against the LHS.
\<close>
lemma points_ign_check:
  assumes "P \<approx>\<^sub>\<alpha> Q"
  assumes "checks P R G"
  shows "checks Q R G"
proof (simp add: checks_def, intro ballI)
  fix q \<beta> assume q: "q \<in> Q" "\<beta> \<in> pairs q"
  then obtain p where p: "p \<in> P" "p \<sim>\<^sub>\<alpha> q" using assms(1) by (auto simp: points_ign_def)
  hence "\<beta> \<in> pairs p" "op p = op q" using q by (auto simp: point_ign_def)
  thus "chke \<beta> (op q) R G" using p(1) assms(2) by (auto simp: checks_def)
qed

text \<open>
These properties allow us to show that rif checks for (r ;; \<alpha>) imply the rif checks for 
just r given \<alpha> can execute before r. 
\<close>
theorem remaining_rif_checks:
  assumes "lexecute c r \<alpha> c'" "sim r"
  assumes "checks (rif (r ;; Basic \<alpha>) P) R G"
  shows "checks (rif r P) R G"
proof -
  obtain \<alpha>' where "reorder_com \<alpha>' r \<alpha>" using assms(1) exec_to_reorder by metis
  moreover have "rif (Basic \<alpha>) P \<approx>\<^sub>\<alpha> P" by blast
  ultimately have i: "rif r (rif (Basic \<alpha>) P) \<approx>\<^sub>\<alpha>' (rif r P)"
    using points_ign_presI assms(2) by fastforce
  thus ?thesis using assms(3) points_ign_check by simp blast
qed

subsection \<open>Soundness\<close>

text \<open>
Show that the rif analysis can be rephrased in terms of the prefix r and instruction \<alpha>
encountered when executing a program step.
\<close>
lemma rif_lexecute:
  assumes "lexecute c r \<alpha> c'" 
  shows "\<exists>c\<^sub>2. rif c P = rif ((r ;; Basic \<alpha>) ;; c\<^sub>2) P \<and> rif c' P = rif (r ;; c\<^sub>2) P"
  using assms
proof (induct arbitrary: P)
  case (act \<alpha>)
  have a: "rif\<^sub>i \<alpha> P = rif\<^sub>i \<alpha> (rif Nil P)" "P = rif Nil P" by auto
  show ?case apply auto using a by blast
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then obtain c where 
    "rif (c\<^sub>1 ;; c\<^sub>2) P = rif ((r ;; Basic \<alpha>) ;; c ;; c\<^sub>2) P" 
    "rif (c\<^sub>1' ;; c\<^sub>2) P = rif (r ;; c ;; c\<^sub>2) P"
    by force
  then show ?case by blast
next
  case (ooo c\<^sub>1 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>2)
  then obtain c where "rif c\<^sub>1 P = rif ((r ;; Basic \<alpha>) ;; c) P" "rif c\<^sub>1' P = rif (r ;; c) P" 
    by force
  then show ?case by auto
next
  case (ord c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then obtain c where 
    "rif (c\<^sub>1 \<cdot> c\<^sub>2) P = rif ((r ;; Basic \<alpha>) ;; c ;; c\<^sub>2) P" 
    "rif (c\<^sub>1' \<cdot> c\<^sub>2) P = rif (r ;; c ;; c\<^sub>2) P"
    by force
  then show ?case by blast
qed 

text \<open>
Soundness statement suitable for induction over the reordering trace property.
Reordering trace consists of steps of rewrites and program steps, which we verify separately.
\<close>
lemma rif_sound_induct:
  assumes "reorder_trace t c" "sim c" "wfcom c"
  assumes "wellformed R G" "checks (rif c {}) R G"
  shows "\<forall>(r,\<alpha>) \<in> set t. inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct)
  case (1 c)
  then show ?case by auto
next
  case (2 c c' t)
  thus ?case using silent_rif_checks sim_silent wfcom_silent 
    unfolding checks_def by fast
next
  case (3 c r \<alpha> c' t)
  text \<open>Re-phrase rif in terms of r and \<alpha>\<close>
  then obtain c\<^sub>2 where c2[simp]: 
      "rif c {} = rif ((r ;; Basic \<alpha>) ;; c\<^sub>2) {}" "rif c' {} = rif (r ;; c\<^sub>2) {}"
    using rif_lexecute by metis
  have s: "sim r" using 3 sim_prefix by blast
  text \<open>rif checks between r and \<alpha> must have been carried out\<close>
  have a: "wfcom r \<and> wfbasic \<alpha>" using 3 wfcom_exec_prefix by metis
  hence "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
    using s 3 exec_rif_checks unfolding c2
    using rif_checks_prefix by (metis rif.simps(4))
  text \<open>rif checks on the remaining program must have been carried out\<close>
  moreover have "\<forall>a\<in>set t. case a of (a, b) \<Rightarrow> inter\<^sub>c (step\<^sub>t R) (step G) a b"
    using 3 by (simp add: remaining_rif_checks[OF _ s] wfcom_exec sim_execute)
  ultimately show ?case by simp
qed

text \<open>Simplify the soundness property\<close>
theorem rif_lift_sound:
  assumes "checks (rif c {}) R G" "sim c" "wellformed R G" "wfcom c"
  shows "ARMv8_Rules.rif (step\<^sub>t R) (step G) c"
  using assms rif_sound_induct unfolding rif_def by blast

theorem rif_sound:
  assumes "checks (rif (lift\<^sub>c c) {}) R G" "wellformed R G"
  shows "ARMv8_Rules.rif (step\<^sub>t R) (step G) (lift\<^sub>c c)"
  using assms by (intro rif_lift_sound) auto

abbreviation rif_checks
  where "rif_checks c R G \<equiv> checks (rif (lift\<^sub>c c) {}) R G"

end