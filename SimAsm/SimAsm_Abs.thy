theory SimAsm_Abs
  imports "HOL-Library.FSet" SimAsm_WP "HOL-Library.While_Combinator" "HOL-Eisbach.Eisbach"
begin

text \<open>
This theory file describes the abstract interference pairs analysis
and includes a soundness proof.
\<close>

section \<open>Definitions\<close>

text \<open>A data point, extends an instruction with reordering information\<close>
record ('v,'g,'r,'a) point =
  op :: "('v,'g,'r,'a) opbasic"
  wrs :: "('g,'r) var set"
  rds :: "('g,'r) var set"
  bar :: bool
  esc :: "('g,'r) var set"
  pairs :: "(('v,'g,'r,'a) opbasic \<times> ('g,'r) var set) set"

type_synonym ('v,'g,'r,'a) points = "('v,'g,'r,'a) point set"

abbreviation inst
  where "inst a \<equiv> fst (tag a)"

fun fences
  where "fences full_fence = True" | "fences _ = False"

definition hasGlobal
  where "hasGlobal S \<equiv> \<exists>e. Glb e \<in> S"

text \<open>Conditions under which a point is ordered after an instruction\<close>
fun ord
  where
    "ord nop p = (bar p)" |
    "ord (cmp b) p = (bar p \<or> hasGlobal (wrs p) \<or> hasGlobal (deps\<^sub>B b \<inter> rds p))" |
    "ord (assign v e) p = 
      (bar p \<or> 
        hasGlobal (deps e \<inter> (rds p \<union> wrs p)) \<or> 
        (case v of Glb g \<Rightarrow> Glb g \<in> wrs p | _ \<Rightarrow> False) \<or> 
        (hasGlobal (deps e) \<and> v \<in> rds p))" |
    "ord full_fence _ = True"

text \<open>Strengthen a point based on a strictly earlier instruction\<close>
definition stren :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "stren a p = p\<lparr> wrs := wrs p \<union> wr (inst a), 
                    rds := rds p - (wr (inst a) \<inter> locals) \<union> rd (inst a), 
                    bar := bar p \<or> fences (inst a) \<rparr>"

text \<open>Weaken a point based on a reorderable instruction\<close>
definition wken :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "wken \<alpha> p = p\<lparr> rds := rds p - wr (inst \<alpha>) \<union> 
                            (if wr (inst \<alpha>) \<inter> rds p \<noteq> {} then rd (inst \<alpha>) else {}), 
                   esc := esc p \<union> wr (inst \<alpha>),
                   pairs := pairs p \<union> {(\<alpha>, esc p)} \<rparr>"

text \<open>Convert an instruction into a point\<close>
definition gen :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "gen a = \<lparr> op = a, wrs = wr (inst a), rds = rd (inst a), bar = fences (inst a), esc = {}, pairs = {} \<rparr>"

text \<open>Process a new instruction against one point\<close>
definition proc1 :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> ('v,'g,'r,'a) point set"
  where
    "proc1 \<alpha> p \<equiv> if ord (inst \<alpha>) p then {stren \<alpha> p} else {stren \<alpha> p, wken \<alpha> p}"

text \<open>Process a new instruction against a set of points\<close>
definition proc\<^sub>i :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point set \<Rightarrow> ('v,'g,'r,'a) point set"
  where 
    "proc\<^sub>i a P \<equiv> \<Union> (proc1 a ` P)"

text \<open>Process a full program, but don't introduce new actions. Used only for reasoning\<close>
fun proc :: "(('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) com \<Rightarrow> ('v,'g,'r,'a) point set \<Rightarrow> ('v,'g,'r,'a) point set"
  where 
    "proc (Basic a) P = proc\<^sub>i a P" |
    "proc (Choice c\<^sub>1 c\<^sub>2) P = (proc c\<^sub>1 P \<union> proc c\<^sub>2 P)" |
    "proc (Loop c) P = lfp (\<lambda>Y. (P \<union> proc c Y))" |
    "proc (c\<^sub>1 ;; c\<^sub>2) P = proc c\<^sub>1 (proc c\<^sub>2 P)" |
    "proc _ P = P"

text \<open>Process a new instruction against a set of points\<close>
definition rif\<^sub>i :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point set \<Rightarrow> ('v,'g,'r,'a) point set"
  where 
    "rif\<^sub>i a P \<equiv> { gen a } \<union> proc\<^sub>i a P"

text \<open>Process a full program\<close>
fun rif :: "(('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) com \<Rightarrow> ('v,'g,'r,'a) point set \<Rightarrow> ('v,'g,'r,'a) point set"
  where 
    "rif (Basic a) P = rif\<^sub>i a P" |
    "rif (Choice c\<^sub>1 c\<^sub>2) P = (rif c\<^sub>1 P \<union> rif c\<^sub>2 P)" |
    "rif (Loop c) P = lfp (\<lambda>Y. (P \<union> rif c Y))" |
    "rif (c\<^sub>1 ;; c\<^sub>2) P = rif c\<^sub>1 (rif c\<^sub>2 P)" |
    "rif _ P = P"

text \<open>Interference Check\<close>
fun sp 
  where 
    "sp P \<alpha> R = {m. \<exists>m' m''. m' \<in> P \<and> m' \<in> vc \<alpha> \<and> (m',m'') \<in> beh \<alpha> \<and> (m'',m) \<in> step\<^sub>t R}"

definition upd
  where "upd m V I \<equiv> m\<lparr>st := \<lambda>x. if x \<in> dom V - I then the (V x) else st m x\<rparr>"
 
definition esc_beh
  where "esc_beh V \<alpha> = {(m,m'). \<exists>n. (upd m V {}, n) \<in> beh \<alpha> \<and> m' = upd n V (wr (inst \<alpha>))}"

definition esc_vc
  where "esc_vc V \<alpha> = {m. upd m V {} \<in> vc \<alpha>}"

definition esc_all
  where "esc_all V \<alpha> \<equiv> {(tag \<alpha>, esc_vc M \<alpha>, esc_beh M \<alpha>) | M. dom M = V}"

fun fwd
  where "fwd \<alpha> (assign x e) = 
      (tag \<alpha>, vc \<alpha>, {(m,m'). \<exists>n. (m(x :=\<^sub>s ev m e),n) \<in> beh \<alpha> \<and> 
                 m' = n(x :=\<^sub>s if x \<in> wr (inst \<alpha>) then st n x else st m x)})" |
    "fwd b _ = b"

definition chk
  where
    "chk \<beta> \<alpha> R G \<equiv> guar\<^sub>\<alpha> (fwd \<alpha> (inst \<beta>)) (step G) \<and> 
                   (\<forall>Q. stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R (wp\<^sub>\<alpha> \<alpha> (stabilize R Q)))) \<subseteq>
                        stabilize R (wp\<^sub>\<alpha> (fwd \<alpha> (inst \<beta>)) (stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R Q)))))"

definition chke
  where
    "chke \<beta> \<alpha> R G \<equiv> \<forall>\<alpha> \<in> esc_all (snd \<beta>) \<alpha>. chk (fst \<beta>) \<alpha> R G"

definition checks
  where "checks P R G \<equiv> \<forall>p \<in> P. \<forall>\<beta> \<in> pairs p. chke \<beta> (op p) R G"

definition rif_checks
  where "rif_checks c R G \<equiv> checks (rif c {}) R G"

section \<open>Soundness\<close>

subsection \<open>Mono Properties\<close>
lemma mono_proc\<^sub>i:
  "mono (proc\<^sub>i a)"
  apply (rule monoI) unfolding proc\<^sub>i_def by blast

lemma mono_rif\<^sub>i:
  "mono (rif\<^sub>i a)"
  by (smt Un_mono monoI mono_Un mono_proc\<^sub>i rif\<^sub>i_def subset_Un_eq subset_refl sup.bounded_iff)

lemma mono_proc:
  "mono (proc c)"
proof (induct c)
  case (Seq c1 c2)
  then show ?case by (simp add: mono_def)
next
  case (Choice c1 c2)
  then show ?case
    by (smt Un_mono mono_def proc.simps(2))
next
  case (Loop c)
  then show ?case 
    by (smt Un_iff lfp_mono monoI subset_eq proc.simps(3))
qed (simp add: monoI mono_proc\<^sub>i)+

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
  case (Loop c)
  then show ?case 
    by (smt Un_iff lfp_mono monoI subset_eq rif.simps(3))
qed (simp add: monoI mono_rif\<^sub>i)+

lemma lfp_const [intro]:
  "x \<in> P \<longrightarrow> x \<in> lfp (\<lambda>Y. P \<union> f Y)"
  by (meson Un_subset_iff basic_trans_rules(31) lfp_greatest)

lemma lfp_fn [intro]:
  "mono f \<Longrightarrow> x \<in> f (lfp (\<lambda>Y. Q \<union> f Y)) \<Longrightarrow> x \<in> lfp (\<lambda>Y. Q \<union> f Y)" 
proof -
  assume a1: "x \<in> f (lfp (\<lambda>Y. Q \<union> f Y))"
  assume a2: "mono f"
  have f3: "\<forall>A. mono ((\<union>) (A::'a set))"
    by (meson Un_mono monoI subset_refl)
  then have "x \<in> lfp (\<lambda>A. f (Q \<union> A))"
    using a2 a1 by (simp add: lfp_rolling)
  then show ?thesis
    using f3 a2 lfp_rolling by blast
qed

lemma mono_union_rif:
  "mono (\<lambda>Y. (P \<union> rif c Y))"
  by (smt Un_mono monoD monoI mono_rif sup.idem sup.order_iff)

(*
subsection \<open>Union Properties\<close>

lemma [simp]:
  "proc r (P \<union> Q) = proc r P \<union> proc r Q"
proof (induct r arbitrary: P Q)
  case (Loop r)
  have p: "lfp (\<lambda>Y. P \<union> Q \<union> proc r Y) \<supseteq> lfp (\<lambda>Y. P \<union> proc r Y)"
    apply (rule lfp_mono)
    by auto
  have q: "lfp (\<lambda>Y. P \<union> Q \<union> proc r Y) \<supseteq> lfp (\<lambda>Y. Q \<union> proc r Y)"
    apply (rule lfp_mono)
    by auto
  hence a: "lfp (\<lambda>Y. P \<union> Q \<union> proc r Y) \<supseteq> lfp (\<lambda>Y. Q \<union> proc r Y) \<union> lfp (\<lambda>Y. P \<union> proc r Y)" (is "?L \<supseteq> ?R")
    using p by auto
  hence lr: "?L \<inter> ?R = ?R" by blast
  have "lfp (\<lambda>Y. Q \<union> proc r Y) \<union> lfp (\<lambda>Y. P \<union> proc r Y) \<supseteq> lfp (\<lambda>Y. P \<union> Q \<union> proc r Y)"
    apply (rule lfp_induct)
    unfolding lr Loop
    apply auto
    apply (smt Loop.hyps Un_mono monoI subset_Un_eq sup.idem)
    using lfp_const apply fast
     using lfp_const apply fast
     using lfp_fn mono_proc apply fast
     using lfp_fn mono_proc apply fast
    done
  then show ?case unfolding proc.simps using a by blast
qed (auto simp: proc\<^sub>i_def)

lemma [simp]:
  "rif r (P \<union> Q) = rif r P \<union> rif r Q"
proof (induct r arbitrary: P Q)
  case (Loop r)
  have p: "lfp (\<lambda>Y. P \<union> Q \<union> rif r Y) \<supseteq> lfp (\<lambda>Y. P \<union> rif r Y)"
    apply (rule lfp_mono)
    by auto
  have q: "lfp (\<lambda>Y. P \<union> Q \<union> rif r Y) \<supseteq> lfp (\<lambda>Y. Q \<union> rif r Y)"
    apply (rule lfp_mono)
    by auto
  hence a: "lfp (\<lambda>Y. P \<union> Q \<union> rif r Y) \<supseteq> lfp (\<lambda>Y. Q \<union> rif r Y) \<union> lfp (\<lambda>Y. P \<union> rif r Y)" (is "?L \<supseteq> ?R")
    using p by auto
  hence lr: "?L \<inter> ?R = ?R" by blast
  have "lfp (\<lambda>Y. Q \<union> rif r Y) \<union> lfp (\<lambda>Y. P \<union> rif r Y) \<supseteq> lfp (\<lambda>Y. P \<union> Q \<union> rif r Y)"
    apply (rule lfp_induct)
    unfolding lr Loop
    apply auto
    apply (smt Loop.hyps Un_mono monoI subset_Un_eq sup.idem)
    using lfp_const apply fast
    using lfp_const apply fast
     using lfp_fn mono_rif apply fast
     using lfp_fn mono_rif apply fast
    done
  then show ?case unfolding rif.simps using a by blast
qed (auto simp: rif\<^sub>i_def proc\<^sub>i_def)

lemma rif_split:
  "rif r P = proc r P \<union> rif r {}"
proof (induct r arbitrary: P)
  case (Seq r1 r2)
  show ?case 
    using Seq(2)[of P] Seq(1)[of "rif r2 P"] Seq(1)[of "rif r2 {}"]
    apply simp by blast
next
  case (Choice r1 r2)
  then show ?case unfolding rif.simps proc.simps by blast
next
  case (Loop r)
  have p: "lfp (\<lambda>Y. P \<union> rif r Y) \<supseteq> lfp (\<lambda>Y. P \<union> proc r Y)" (is "?L \<supseteq> ?R1")
    apply (rule lfp_mono)
    using Loop by blast
  have q: "lfp (\<lambda>Y. P \<union> rif r Y) \<supseteq> lfp (\<lambda>Y. {} \<union> rif r Y)" (is "?L \<supseteq> ?R2")
    apply (rule lfp_mono)
    by auto
  hence a: "?L \<supseteq> ?R1 \<union> ?R2" (is "?L \<supseteq> ?R") using p by auto
  hence lr: "?L \<inter> ?R = ?R" by blast
  have "?R \<supseteq> ?L"
    apply (rule lfp_induct)
    unfolding lr
    apply (simp add: mono_union_rif)
    apply auto
    using lfp_const apply fast
    defer 1
    using lfp_unfold mono_rif apply blast
    unfolding Loop[of "lfp (\<lambda>Y. P \<union> proc r Y)"]
    apply auto
     using lfp_fn mono_proc apply fast
    by (metis Loop.hyps UnCI lfp_unfold mono_rif)
  then show ?case unfolding rif.simps proc.simps using a by blast
qed (auto simp: proc\<^sub>i_def rif\<^sub>i_def)
*)

subsection \<open>Helper Properties\<close>

lemma op_proc1[simp]:
  "\<forall>q \<in> proc1 x p. op q = op p"
  by (auto simp: stren_def wken_def proc1_def)

lemma pairs_proc1:
  "\<forall>q \<in> proc1 x p. pairs q \<supseteq> pairs p"
  unfolding proc1_def stren_def wken_def by clarsimp

lemma proc1_non_nil [intro]:
  "proc1 x p \<noteq> {}"
  unfolding proc1_def stren_def wken_def by clarsimp

lemma gen_pairs [simp]:
  "pairs (gen \<alpha>) = {}"
  by (auto simp: gen_def)

lemma gen_op [simp]:
  "op (gen \<alpha>) = \<alpha>"
  by (auto simp: gen_def)

lemma [simp]:
  "deps (subst e x e') = deps e - {x} \<union> (if x \<in> deps e then deps e' else {})"
  by (induct e; auto simp: if_splits)

lemma [simp]:
  "deps\<^sub>B (subst\<^sub>B e x e') = deps\<^sub>B e - {x} \<union> (if x \<in> deps\<^sub>B e then deps e' else {})"
  by (induct e; auto simp: if_splits)

lemma [simp]:
  "wr (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = wr (inst \<alpha>)"
  by (cases \<alpha>; cases \<beta>; case_tac a; case_tac aa; case_tac ab; case_tac ac; auto)

lemma [simp]:
  "fences (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = fences (inst \<alpha>)"
  by (cases \<alpha>; cases \<beta>; case_tac a; case_tac aa; case_tac ab; case_tac ac; auto)

lemma [simp]:
  "rd (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = (if wr (inst \<beta>) \<inter> rd (inst \<alpha>) \<noteq> {} then rd (inst \<alpha>) - wr (inst \<beta>) \<union> rd (inst \<beta>) else rd (inst \<alpha>))"
  by (cases \<alpha>; cases \<beta>; case_tac a; case_tac aa; case_tac ab; case_tac ac; auto)

lemma ord_sound:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  shows "\<not> ord (inst \<beta>) (gen \<alpha>)"
  using assms 
  apply (cases \<beta> ; cases \<alpha> ; case_tac a ; case_tac aa; case_tac ab; case_tac ac)
  by (auto simp: gen_def hasGlobal_def split: var.splits)

subsection \<open>Pairwise Check Properties\<close>

lemma stabilize':
  "transitive R \<Longrightarrow> stable\<^sub>t R P \<Longrightarrow> P \<subseteq> stabilize R P"
  unfolding stabilize_def transitive_def stable_def step\<^sub>t_def
  by auto

lemma stabilize'':
  "reflexive R \<Longrightarrow> stable\<^sub>t R Q \<Longrightarrow> stabilize R Q = Q"
  unfolding stabilize_def reflexive_def stable_def step\<^sub>t_def
  by auto

lemma chk_sound:
  "wellformed R G \<Longrightarrow> chk \<beta> \<alpha> R G \<Longrightarrow> inter\<^sub>\<alpha> (step\<^sub>t R) (step G) \<beta> \<alpha>"
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

lemma chke_sound2:
  "re\<^sub>a (tag \<beta>) (tag (fwd\<^sub>s \<alpha> (tag \<beta>))) \<Longrightarrow> chke (\<gamma>, wr (inst \<beta>) \<union> V) \<alpha> R G \<Longrightarrow> chke (\<gamma>, V) (fwd\<^sub>s \<alpha> (tag \<beta>)) R G"
  sorry

lemma [simp]:
  "upd m Map.empty I = m"
  by (auto simp: upd_def)

lemma chke_sound:
  assumes "chke (\<beta>, {}) \<alpha> R G" 
  shows "chk \<beta> \<alpha> R G"
proof -
  have "\<alpha> \<in> esc_all {} \<alpha>" by (auto simp: esc_all_def esc_vc_def esc_beh_def)
  thus "chk \<beta> \<alpha> R G" using assms by (auto simp: chk_def chke_def)
qed

subsection \<open>Silent rif Checks\<close>

text \<open>Trivial proof showing rif is preserved across silent steps\<close>
lemma silent_rif_checks:
  assumes "c \<leadsto> c'" "local c"
  shows "rif c' P \<subseteq> rif c P"
  using assms
proof (induct arbitrary: P)
  case (seq2 c\<^sub>2 c\<^sub>2' c\<^sub>1)
  then show ?case by (simp add: monoD mono_rif)
next
  case (loop1 c)
  then show ?case unfolding rif.simps
    using def_lfp_unfold[OF _ mono_union_rif] by blast
next
  case (loop2 c)
  then show ?case unfolding rif.simps
    using def_lfp_unfold[OF _ mono_union_rif] by blast
qed auto

subsection \<open>Execution rif Checks\<close>

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
            (\<forall>R G (\<alpha> :: ('v,'g,'r,'a) opbasic) V. 
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
  by (auto simp: Un_assoc) (case_tac \<alpha>; case_tac a; metis boolean_algebra_cancel.sup0)+

text \<open>The point relation ensures equivalent ordering constraints\<close>
lemma point_ord [simp]:
  "p \<prec> q \<Longrightarrow> ord \<alpha> p = ord \<alpha> q"
  by (cases \<alpha>) (auto simp: point_ord_def hasGlobal_def split: var.splits)

text \<open>Based on the above, proc1 preserves the point relation\<close>
lemma point_ord_proc1 [intro]:
  "p \<prec> q \<Longrightarrow> proc1 \<alpha> p \<prec>\<prec> proc1 \<alpha> q"
  unfolding points_ord_def proc1_def by auto

text \<open>Based on the above, proci preserves the point relation\<close>
lemma points_ord_proc\<^sub>i [intro]:
  "P \<prec>\<prec> Q \<Longrightarrow> proc\<^sub>i \<alpha> P \<prec>\<prec> proc\<^sub>i \<alpha> Q"
  using point_ord_proc1 unfolding proc\<^sub>i_def points_ord_def by fast

lemma points_ord_union [intro]:
  "P \<prec>\<prec> Q \<Longrightarrow> P' \<prec>\<prec> Q' \<Longrightarrow> P \<union> P' \<prec>\<prec> Q \<union> Q'"
  by (auto simp: points_ord_def)

text \<open>Finally, rif preserves the point relation\<close>
lemma points_ord_rif [intro]:
  "P \<prec>\<prec> Q \<Longrightarrow> rif c P \<prec>\<prec> rif c Q"
proof (induct c arbitrary: P Q)
  case (Basic x)
  hence "proc\<^sub>i x P \<prec>\<prec> proc\<^sub>i x Q" by blast
  then show ?case by (auto simp: rif\<^sub>i_def points_ord_def)
next
  case (Choice c1 c2)
  then show ?case by (auto simp: points_ord_def) fast+
next
  case (Loop c)
  show ?case using Loop(2) unfolding rif.simps
  proof (induct rule: lfp_ordinal_induct)
    case mono
    then show ?case by (simp add: mono_union_rif)
  next
    case (step S)
    hence "rif c (lfp (\<lambda>Y. P \<union> rif c Y)) \<prec>\<prec> rif c S" using Loop(1) by blast
    then show ?case using step(3) by (subst lfp_unfold[OF mono_union_rif]) auto
  next
    case (union M)
    then show ?case by (auto simp: points_ord_def)
  qed
qed auto

text \<open>Establish the point relation between \<alpha> weakened by \<beta> and one generated from \<alpha>' directly\<close>
lemma point_ord_fwd:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  shows "wken \<beta> (gen \<alpha>) \<prec> gen \<alpha>'"
  using assms by (auto simp: point_ord_def gen_def wken_def) (insert chke_sound2, blast)+

text \<open>Checks against the LHS of a points relation imply checks against the RHS\<close>
lemma points_ord_checks [intro]:
  "checks P R G \<Longrightarrow> P \<prec>\<prec> Q \<Longrightarrow> checks Q R G"
  unfolding checks_def points_ord_def point_ord_def by metis

text \<open>rif checks on sequential composition should imply rif checks of just the postfix\<close>
lemma rif_checks_postfix [intro]:
  assumes "checks (SimAsm_Abs.rif (c ;; r) P) R G"
  shows "checks (SimAsm_Abs.rif r P) R G"
  using assms
proof (induct c arbitrary: r P)
  case (Basic x)
  show ?case unfolding checks_def
  proof (intro ballI)
    fix p \<beta> assume a: "p \<in> rif r P" "\<beta> \<in> pairs p"
    hence "\<exists>q \<in> proc1 x p. \<beta> \<in> pairs q" using pairs_proc1 proc1_non_nil by blast
    thus "chke \<beta> (op p) R G"
      using Basic a by (auto simp: checks_def rif_def rif\<^sub>i_def proc\<^sub>i_def)
  qed
next
  case (Loop c)
  thus ?case by (simp add: SimAsm_Abs.lfp_const checks_def) 
qed (unfold checks_def rif.simps; blast)+

lemma [simp]:
  "rif\<^sub>i x {} = {gen x}"
  sorry

lemma rif_checks_prefix [intro]:
  assumes "checks (SimAsm_Abs.rif (c ;; r) P) R G"
  shows "checks (SimAsm_Abs.rif c {}) R G"
  using assms
  sorry (*
proof (induct r arbitrary: P)
  case Nil
  then show ?case by (auto simp: checks_def)
next
  case (Basic x)
  then show ?case by (auto simp: checks_def)
next
  case (Seq c1 c2)
  then show ?case sorry
next
  case (Choice c1 c2)
  then show ?case sorry
next
case (Loop c)
then show ?case sorry
next
  case (Parallel c1 c2)
  then show ?case sorry
next
  case (Thread c)
  then show ?case sorry
qed
  case (Basic x)
  show ?case unfolding checks_def
  proof (intro ballI)
    fix p \<beta> assume a: "p \<in> rif r P" "\<beta> \<in> pairs p"
    hence "\<exists>q \<in> proc1 x p. \<beta> \<in> pairs q" using pairs_proc1 proc1_non_nil by blast
    thus "chke \<beta> (op p) R G"
      using Basic a by (auto simp: checks_def rif_def rif\<^sub>i_def proc\<^sub>i_def)
  qed
next
  case (Loop c)
  thus ?case by (simp add: SimAsm_Abs.lfp_const checks_def) 
qed (unfold checks_def rif.simps; blast)+
*)

text \<open>
rif checks on sequential composition due to an action that can reorder with the postfix
correspond to the checks that would be seen if the postfix wasn't present and forwarding
was captured fully.
\<close>
lemma rif_checks_fwd:
  assumes "reorder_com \<alpha>' c\<^sub>2 \<alpha>"
  assumes "checks (rif (c\<^sub>1 ;; c\<^sub>2 ;; Basic \<alpha>) {}) R G" 
  shows "checks (rif (c\<^sub>1 ;; Basic \<alpha>') {}) R G"
  using assms
proof (induct \<alpha>' c\<^sub>2 \<alpha> arbitrary: c\<^sub>1 rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  text \<open>Remove the checks on gen \<beta>\<close>
  hence "checks (rif c\<^sub>1 ({gen \<beta>} \<union> proc1 \<beta> (gen \<alpha>))) R G"
    by (auto simp: rif\<^sub>i_def proc\<^sub>i_def)
  hence c: "checks (rif c\<^sub>1 (proc1 \<beta> (gen \<alpha>))) R G"
    unfolding checks_def using mono_Un mono_rif by blast
  text \<open>Show the point relation between \<alpha> and \<alpha>'\<close>
  have r: "reorder_inst \<alpha>' \<beta> \<alpha>" using 2 by auto
  have "proc1 \<beta> (gen \<alpha>) \<prec>\<prec> {gen \<alpha>'}" 
    using point_ord_fwd[OF r] ord_sound[OF r] unfolding points_ord_def proc1_def by auto
  text \<open>Use properties of the point relation to establish checks on c1 and \<alpha>'\<close>
  hence "rif c\<^sub>1 (proc1 \<beta> (gen \<alpha>)) \<prec>\<prec> rif c\<^sub>1 {gen \<alpha>'}" by auto
  hence "checks (rif c\<^sub>1 {gen \<alpha>'}) R G" using c by blast
  then show ?case by (auto simp: rif\<^sub>i_def proc\<^sub>i_def)
next
  case (3 \<alpha>' c\<^sub>1' c\<^sub>2 \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "reorder_com \<alpha>' c\<^sub>1' \<alpha>''" "reorder_com \<alpha>'' c\<^sub>2 \<alpha>" by auto
  hence "checks (rif (c\<^sub>1 ;; c\<^sub>1' ;; Basic \<alpha>'') {}) R G" using 3(2)[of _ "c\<^sub>1 ;; c\<^sub>1'"] 3(4) by auto
  thus ?case using \<alpha> 3 by auto
qed auto

text \<open>Convert an execution step to a reordering\<close>
lemma exec_to_reorder:
  assumes "lexecute c r \<alpha> c'"
  shows "\<exists>\<alpha>'. reorder_com \<alpha>' r \<alpha>"
  using assms
  by (induct, unfold reorder_com.simps(1); blast)

text \<open>Phrase the desired property for induction over a reordering\<close>
lemma exec_checks_induct:
  assumes "wellformed R G"
  assumes "reorder_com \<alpha>' r \<alpha>"
  assumes "checks (rif (r ;; Basic \<alpha>) {}) R G"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct \<alpha>' r \<alpha> rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  text \<open>Given the two instructions can reorder, they mustn't be considered ordered\<close>
  hence "\<not> ord (inst \<beta>) (gen \<alpha>)" using ord_sound[of \<alpha>' \<alpha> \<beta>] by auto
  text \<open>Obtain the point generated for \<alpha>\<close>
  then obtain p where "p \<in> rif\<^sub>i \<beta> (rif\<^sub>i \<alpha> {})" "op p = \<alpha>" "(\<beta>,{}) \<in> pairs p"
    unfolding rif\<^sub>i_def proc\<^sub>i_def  proc1_def gen_def stren_def wken_def
    by (clarsimp split: if_splits) fastforce
  text \<open>Extract the check between \<beta> and \<alpha> and show it establishes inter\<close>
  hence "chke (\<beta>,{}) \<alpha> R G" using 2(3) by (auto simp: checks_def)
  then show ?case using chk_sound chke_sound 2(1) unfolding inter\<^sub>c.simps by blast
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "reorder_com \<alpha>' c\<^sub>1 \<alpha>''" "reorder_com \<alpha>'' c\<^sub>2 \<alpha>" by auto
  have "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>2 \<alpha>" using 3 rif_checks_postfix by fastforce
  moreover have "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>1 \<alpha>''" using \<alpha> 3 rif_checks_fwd by simp blast
  ultimately show ?case using \<alpha> by auto
qed auto

text \<open>rif should perform checks on any instruction that can reorder before some prefix\<close>
lemma exec_rif_checks:
  assumes "wellformed R G"
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
definition point_ign :: "('v,'g,'r,'a) point \<Rightarrow> (_,_,_,_) opbasic \<Rightarrow> (_,_,_,_) point \<Rightarrow> bool" 
  ("_ \<sim>\<^sub>_ _" [0,100,0] 60)
  where "point_ign p \<alpha> q \<equiv> 
     wrs p \<subseteq> wrs q \<union> wr (inst \<alpha>) \<and> 
     rds p \<subseteq> rds q \<union> (wrs q - locals) \<union> rd (inst \<alpha>) \<and> 
     (bar p = bar q \<or> fences (inst \<alpha>)) \<and>
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
definition points_ign :: "('v,'g,'r,'a) points \<Rightarrow> (_,_,_,_) opbasic \<Rightarrow> (_,_,_,_) points \<Rightarrow> bool"
  ("_ \<approx>\<^sub>_ _" [0,100,0] 60)
  where "points_ign P \<alpha> Q \<equiv> \<forall>q \<in> Q. \<exists>p \<in> P. (p \<sim>\<^sub>\<alpha> q)"

text \<open>
Given an instruction that the ignored operation can reorder before, q should have
stronger reordering constraints than p.
\<close>
lemma point_ign_ord:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  assumes "p \<sim>\<^sub>\<alpha> q"
  shows "ord (inst \<beta>) p \<longrightarrow> ord (inst \<beta>) q"
  using assms 
  apply (cases \<alpha>; cases \<beta>; case_tac a; case_tac aa; case_tac ab; case_tac ac; clarsimp)
  by (auto simp: point_ign_def hasGlobal_def split: var.splits if_splits)

text \<open>
The point_ign relation is preserved across updates due to an instruction that the
ignored instruction can reorder before.
\<close>
lemma point_ign_pres:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>" "p \<sim>\<^sub>\<alpha> q" "q' \<in> proc1 \<beta> q"
  shows "\<exists>p'\<in>proc1 \<beta> p. (p' \<sim>\<^sub>\<alpha>' q')"
proof (cases "q' = stren \<beta> q")
  case True
  text \<open>Always strengthen\<close>
  moreover have "stren \<beta> p \<in> proc1 \<beta> p" unfolding proc1_def by auto
  text \<open>stren preserves the relation\<close>
  moreover have "stren \<beta> p \<sim>\<^sub>\<alpha>' (stren \<beta> q)" using assms(1,2) by (auto simp: stren_def point_ign_def)
  ultimately show ?thesis by blast
next
  case False
  text \<open>Must have weakened due to out-of-order otherwise\<close>
  hence q: "q' = wken \<beta> q" "\<not> ord (inst \<beta>) q" 
    using assms(3) unfolding proc1_def by (auto split: if_splits)
  text \<open>Therefore, \<beta> can't have a global write in common with q\<close>
  hence wr: "(wr (inst \<beta>) - locals) \<inter> wrs q = {}"
    by (cases "inst \<beta>"; auto split: var.splits)
  text \<open>Also, \<beta> can't be ordered with p due to q's stronger constraints\<close>
  have "\<not> ord (inst \<beta>) p" using q point_ign_ord assms(1,2) by blast
  text \<open>Therefore, \<beta> must weaken p as well\<close>
  hence "wken \<beta> p \<in> proc1 \<beta> p" unfolding proc1_def by auto
  text \<open>wken preserves the relation\<close>
  moreover have "wken \<beta> p \<sim>\<^sub>\<alpha>' (wken \<beta> q)"
    using assms(1,2) wr unfolding wken_def point_ign_def
    by clarsimp (intro conjI impI; blast)
  ultimately show ?thesis using q(1) by blast
qed

text \<open>
It is possible to establish the points_ign relation between P and a version of P
updated using the ignored instruction.
\<close>
lemma points_ignI [intro]:
  shows "rif (Basic \<alpha>) P \<approx>\<^sub>\<alpha> P"
proof (simp add: points_ign_def rif\<^sub>i_def, intro ballI disjI2)
  fix q assume "q \<in> P"
  hence "stren \<alpha> q \<in> proc\<^sub>i \<alpha> P" unfolding proc\<^sub>i_def proc1_def by auto
  moreover have "stren \<alpha> q \<sim>\<^sub>\<alpha> q" by (auto simp: stren_def point_ign_def)
  ultimately show "\<exists>p\<in>proc\<^sub>i \<alpha> P. (p \<sim>\<^sub>\<alpha> q)" by auto
qed

text \<open>
It is also possible to preserve the points_ign relation across a program that
the ignored instruction can reorder before.
\<close>
lemma points_ign_presI [intro]:
  assumes "reorder_com \<beta> r \<alpha>"
  assumes "P \<approx>\<^sub>\<alpha> Q"
  shows "rif r P \<approx>\<^sub>\<beta> (rif r Q)"
  using assms
proof (induct \<beta> r \<alpha> arbitrary: P Q rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  then show ?case using point_ign_pres by (simp add: rif\<^sub>i_def proc\<^sub>i_def points_ign_def) blast
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
  assumes "lexecute c r \<alpha> c'"
  assumes "checks (rif (r ;; Basic \<alpha>) P) R G"
  shows "checks (rif r P) R G"
proof -
  obtain \<alpha>' where "reorder_com \<alpha>' r \<alpha>" using assms(1) exec_to_reorder by metis
  moreover have "rif (Basic \<alpha>) P \<approx>\<^sub>\<alpha> P" by blast
  ultimately have i: "rif r (rif (Basic \<alpha>) P) \<approx>\<^sub>\<alpha>' (rif r P)"
    using points_ign_presI by fastforce
  thus ?thesis using assms(2) points_ign_check by simp blast
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
qed

text \<open>
Soundness statement suitable for induction over the reordering trace property.
Reordering trace consists of steps of rewrites and program steps, which we verify separately.
\<close>
lemma rif_sound_induct:
  assumes "reorder_trace t c" "local c"
  assumes "wellformed R G" "checks (rif c {}) R G"
  shows "\<forall>(r,\<alpha>) \<in> set t. inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct)
  case (1 c)
  then show ?case by auto
next
  case (2 c c' t)
  thus ?case using silent_rif_checks local_silent unfolding checks_def by fast
next
  case (3 c r \<alpha> c' t)
  text \<open>Re-phrase rif in terms of r and \<alpha>\<close>
  then obtain c\<^sub>2 where c2[simp]: "rif c {} = rif ((r ;; Basic \<alpha>) ;; c\<^sub>2) {}" "rif c' {} = rif (r ;; c\<^sub>2) {}"
    using rif_lexecute by metis
  text \<open>rif checks between r and \<alpha> must have been carried out\<close>
  have "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
    using 3 exec_rif_checks unfolding c2
    using rif_checks_prefix by (metis rif.simps(4))
  text \<open>rif checks on the remaining program must have been carried out\<close>
  moreover have "\<forall>a\<in>set t. case a of (a, b) \<Rightarrow> inter\<^sub>c (step\<^sub>t R) (step G) a b"
    using 3 by (simp add: local_execute remaining_rif_checks)
  ultimately show ?case by simp
qed

text \<open>Simplify the soundness property\<close>
theorem rif_sound:
  assumes "checks (rif c {}) R G" "local c" "wellformed R G"
  shows "SimAsm_WP.rif (step\<^sub>t R) (step G) c"
  using assms rif_sound_induct unfolding rif_def by blast

end