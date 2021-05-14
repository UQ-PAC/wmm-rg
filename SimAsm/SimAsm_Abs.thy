theory SimAsm_Abs
  imports "HOL-Library.FSet" SimAsm_WP "HOL-Library.While_Combinator" "HOL-Eisbach.Eisbach"
begin

text \<open>A data point, extends an instruction with reordering information\<close>
record ('v,'g,'r,'a) point =
  op :: "('v,'g,'r,'a) opbasic"
  wrs :: "('g,'r) var set"
  rds :: "('g,'r) var set"
  bar :: bool
  orig :: "('g,'r) var set"
  pairs :: "(('v,'g,'r,'a) opbasic \<times> ('g,'r) var set) set"

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
fun stren :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "stren a p = p\<lparr> wrs := wrs p \<union> wr (inst a), 
                    rds := rds p \<union> rd (inst a), 
                    bar := bar p \<or> fences (inst a) \<rparr>"

text \<open>Weaken a point based on a reorderable instruction\<close>
fun wken :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "wken \<alpha> p = p\<lparr> rds := rds p - wr (inst \<alpha>) \<union> 
                            (if wr (inst \<alpha>) \<inter> rds p \<noteq> {} then rd (inst \<alpha>) else {}), 
                   orig := orig p - wr (inst \<alpha>),
                   pairs := pairs p \<union> {(\<alpha>, orig p)} \<rparr>"

text \<open>Convert an instruction into a point\<close>
definition gen :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "gen a = \<lparr> op = a, wrs = wr (inst a), rds = rd (inst a), bar = fences (inst a), orig = rd (inst a), pairs = {} \<rparr>"

text \<open>Process a new instruction against one point\<close>
definition proc1 :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "proc1 \<alpha> p \<equiv> if ord (inst \<alpha>) p then stren \<alpha> p else wken \<alpha> p"

text \<open>Process a new instruction against a set of points\<close>
definition proc\<^sub>i :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point set \<Rightarrow> ('v,'g,'r,'a) point set"
  where 
    "proc\<^sub>i a P \<equiv> proc1 a ` P"

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

fun escape
  where 
    "escape v (Var x) = (if x \<in> v then {Var x} else Val ` UNIV)" |
    "escape v (Val y) = {Val y}" |
    "escape v (Exp f l) = {Exp f l' | l'. l' \<in> listset (map (escape v) l)}"

fun escape\<^sub>B
  where 
    "escape\<^sub>B v (Neg x) = escape\<^sub>B v x" |
    "escape\<^sub>B v (Exp\<^sub>B f l) = {Exp\<^sub>B f l' | l'. l' \<in> listset (map (escape v) l)}"

fun escape\<^sub>\<alpha>
  where
    "escape\<^sub>\<alpha> v (assign x e) = {assign x e' | e'. e' \<in> escape v e}" |
    "escape\<^sub>\<alpha> v (cmp e) = {cmp e' | e'. e' \<in> escape\<^sub>B v e}" |
    "escape\<^sub>\<alpha> v a = {a}"

fun escape\<^sub>i
  where
    "escape\<^sub>i v ((\<alpha>,f),c,_) = {((\<alpha>',f), c, beh\<^sub>a (\<alpha>',f)) | \<alpha>'. \<alpha>' \<in> escape\<^sub>\<alpha> v \<alpha>}"

definition chk
  where
    "chk \<beta> \<alpha> R G \<equiv> guar\<^sub>\<alpha> (fwd\<^sub>s \<alpha> (tag \<beta>)) (step G) \<and> 
                   (\<forall>Q. stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R (wp\<^sub>\<alpha> \<alpha> (stabilize R Q)))) \<subseteq>
                        stabilize R (wp\<^sub>\<alpha> (fwd\<^sub>s \<alpha> (tag \<beta>)) (stabilize R (wp\<^sub>\<alpha> \<beta> (stabilize R Q)))))"

definition chke
  where
    "chke \<beta> \<alpha> R G \<equiv> \<forall>\<alpha> \<in> escape\<^sub>i (snd \<beta>) \<alpha>. chk (fst \<beta>) \<alpha> R G"

definition checks 
  where "checks P R G \<equiv> \<forall>p \<in> P. \<forall>\<beta> \<in> pairs p. chke \<beta> (op p) R G"

definition rif_checks
  where "rif_checks c R G \<equiv> checks (rif c {}) R G"

section \<open>Soundness\<close>

subsection \<open>Mono Properties\<close>
lemma mono_proc\<^sub>i:
  "mono (proc\<^sub>i a)"
  by (smt Un_mono image_Un monoI order_refl sup.orderE sup_ge2 proc\<^sub>i_def)

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

subsection \<open>Correctness\<close>

lemma upd_rw:
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

lemma op_proc1[simp]:
  "op (proc1 x p) = op p"
  by (auto simp: proc1_def)

lemma pairs_proc1:
  "pairs (proc1 x p) \<supseteq> pairs p"
  by (auto simp: proc1_def)

lemma checks_rif_seq:
  assumes "checks (SimAsm_Abs.rif (c ;; r) P) R G"
  shows "checks (SimAsm_Abs.rif r P) R G"
  using assms
proof (induct c arbitrary: r P)
  case (Basic x)
  show ?case unfolding checks_def
  proof (intro ballI)
    fix p \<beta> assume a: "p \<in> rif r P" "\<beta> \<in> pairs p"
    hence "\<beta> \<in> pairs (proc1 x p)" using pairs_proc1 by blast
    thus "chke \<beta> (op p) R G"
      using Basic a by (auto simp: checks_def rif_def rif\<^sub>i_def proc\<^sub>i_def)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  then show ?case unfolding rif.simps by blast
next
  case (Loop c)
  then show ?case unfolding checks_def rif.simps
    by (simp add: SimAsm_Abs.lfp_const) 
next
  case (Choice c\<^sub>1 c\<^sub>2)
  then show ?case unfolding checks_def rif.simps by blast
qed (unfold rif.simps)

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

lemma ord_sound:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  shows "\<not> ord (inst \<beta>) (gen \<alpha>)"
  using assms 
  apply (cases \<beta> ; cases \<alpha> ; case_tac a ; case_tac aa; case_tac ab; case_tac ac)
  by (auto simp: gen_def hasGlobal_def split: var.splits)

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

lemma chk_cong:
  assumes "fwd\<^sub>s \<alpha> (tag \<beta>) = fwd\<^sub>s \<alpha>' (tag \<beta>')"
  assumes "beh \<alpha> = beh \<alpha>'" "vc \<alpha> = vc \<alpha>'" "beh \<beta> = beh \<beta>'" "vc \<beta> = vc \<beta>'"
  shows "chk \<beta> \<alpha> R G = chk \<beta>' \<alpha>' R G"
  using assms unfolding chk_def
  by auto

lemma chke_sound:
  assumes "chke (\<beta>, v) \<alpha> R G" shows "chk \<beta> \<alpha> R G"
proof -
  have "\<forall>\<alpha> \<in> escape\<^sub>i v \<alpha>. chk \<beta> \<alpha> R G" using assms unfolding chke_def by auto

  hence "\<forall>\<alpha> \<in> escape\<^sub>i v \<alpha>. guar\<^sub>\<alpha> (fwd\<^sub>s \<alpha> (tag \<beta>)) (step G)"
    unfolding chk_def by auto
  hence "guar\<^sub>\<alpha> (fwd\<^sub>s \<alpha> (tag \<beta>)) (step G)"
    unfolding guar_def
    apply (cases \<alpha>; cases "tag \<beta>")
    apply auto
    apply (case_tac aa; auto)
    sorry

  show "chk \<beta> \<alpha> R G"
    unfolding chk_def sorry
qed

definition point_ord (infix "\<prec>" 60)
  where "point_ord p q \<equiv> wrs p \<subseteq> wrs q \<and> rds p \<subseteq> rds q \<and> op p = op q \<and> pairs p \<supseteq> pairs q"

definition points_ord (infix "\<prec>\<prec>" 60)
  where "points_ord P Q \<equiv> \<forall>q \<in> Q. \<exists>p \<in> P. p \<prec> q"

lemma checks_points_ord [intro]:
  "checks P R G \<Longrightarrow> P \<prec>\<prec> Q \<Longrightarrow> checks Q R G"
  unfolding checks_def points_ord_def point_ord_def
  by fastforce
  
lemma rif_preserve_ord:
  assumes "P \<prec>\<prec> Q"
  shows "rif c P \<prec>\<prec> rif c Q"
  using assms
proof (induct c arbitrary: P Q)
  case (Basic x)
  then show ?case apply (auto simp: proc\<^sub>i_def rif\<^sub>i_def) sorry
next
  case (Choice c1 c2)
  then show ?case apply (auto simp: points_ord_def) by fast+
next
  case (Loop c)
  then show ?case
    apply (auto simp: points_ord_def)
    sorry
qed auto

lemma
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  shows "wken \<beta> (gen \<alpha>) \<prec> gen \<alpha>'"
  using assms 
  apply (cases \<beta> ; cases \<alpha> ; case_tac a ; case_tac aa; case_tac ab; case_tac ac)
  apply (auto simp: gen_def hasGlobal_def  split: var.splits)
  unfolding point_ord_def
  apply clarsimp
  defer 1
  defer 1
  defer 1
  defer 1
  apply clarsimp
  sorry

lemma checks_fwd:
  assumes "reorder_com \<alpha>' c\<^sub>2 \<alpha>"
  assumes "checks (rif (c\<^sub>1 ;; c\<^sub>2 ;; Basic \<alpha>) {}) R G" 
  shows "checks (rif (c\<^sub>1 ;; Basic \<alpha>') {}) R G"
  using assms
proof (induct \<alpha>' c\<^sub>2 \<alpha> arbitrary: c\<^sub>1 rule: reorder_com.induct)
  case (1 \<alpha>' \<alpha>)
  then show ?case using checks_rif_seq[of c\<^sub>2 "Basic \<alpha>"] by auto
next
  case (2 \<alpha>' \<beta> \<alpha>)
  hence "checks (rif c\<^sub>1 ({gen \<beta>} \<union> {proc1 \<beta> (gen \<alpha>)})) R G"
    by (auto simp: rif\<^sub>i_def proc\<^sub>i_def)
  hence c: "checks (rif c\<^sub>1 ({proc1 \<beta> (gen \<alpha>)})) R G"
    unfolding checks_def using mono_Un mono_rif by blast

  have "proc1 \<beta> (gen \<alpha>) \<prec> gen \<alpha>'"
    sorry
  hence "{proc1 \<beta> (gen \<alpha>)} \<prec>\<prec> {gen \<alpha>'}"
    by (auto simp: points_ord_def)
  hence "rif c\<^sub>1 {proc1 \<beta> (gen \<alpha>)} \<prec>\<prec> rif c\<^sub>1 {gen \<alpha>'}"
    using rif_preserve_ord by auto
  hence "checks (rif c\<^sub>1 {gen \<alpha>'}) R G" using c by blast
  then show ?case by (auto simp: rif\<^sub>i_def proc\<^sub>i_def)
next
  case (3 \<alpha>' c\<^sub>1' c\<^sub>2 \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "reorder_com \<alpha>' c\<^sub>1' \<alpha>''" "reorder_com \<alpha>'' c\<^sub>2 \<alpha>" by auto
  hence "checks (SimAsm_Abs.rif (c\<^sub>1 ;; c\<^sub>1' ;; Basic \<alpha>'') {}) R G"
    using 3(2)[of \<alpha>'' "c\<^sub>1 ;; c\<^sub>1'"] 3(4) by auto
  thus ?case using \<alpha> 3(1)[of \<alpha>'' "c\<^sub>1"] by auto
qed auto

lemma upd_exec:
  assumes "wellformed R G"
  assumes "reorder_com \<alpha>' c\<^sub>1 \<alpha>"
  assumes "checks (rif (c\<^sub>1 ;; Basic \<alpha>) {}) R G"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>1 \<alpha>"
  using assms
proof (induct \<alpha>' c\<^sub>1 " \<alpha> " rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  hence "\<not> ord (inst \<beta>) (gen \<alpha>)" using ord_sound[of \<alpha>' \<alpha> \<beta>] by auto
  then obtain p v where "p \<in> rif\<^sub>i \<beta> (rif\<^sub>i \<alpha> {})" "op p = \<alpha>" "(\<beta>,v) \<in> pairs p"
    apply (auto simp: rif\<^sub>i_def proc\<^sub>i_def  proc1_def gen_def split: if_splits)
    by fastforce
  hence "chke (\<beta>,v) \<alpha> R G" using 2(3) by (auto simp: checks_def) 
  then show ?case using chk_sound chke_sound 2(1) unfolding inter\<^sub>c.simps by blast
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "reorder_com \<alpha>' c\<^sub>1 \<alpha>''" "reorder_com \<alpha>'' c\<^sub>2 \<alpha>" by auto
  hence c2: "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>2 \<alpha>" using 3 checks_rif_seq[of c\<^sub>1 "(c\<^sub>2 ;; Basic \<alpha>)"] by auto
  have "checks (SimAsm_Abs.rif (c\<^sub>1 ;; Basic \<alpha>'') {}) R G"
    using \<alpha> checks_fwd 3(5) by fastforce
  hence "inter\<^sub>c (step\<^sub>t R) (step G) c\<^sub>1 \<alpha>''" using 3(1)[OF 3(3) \<alpha>(1)] by blast
  then show ?case using c2 \<alpha> by auto
qed auto

lemma upd_exec_rest:
  assumes "lexecute c r \<alpha> c'"
  assumes "checks (rif (r ;; Basic \<alpha>) P) R G"
  shows "checks (rif r P) R G"
  sorry

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

lemma exec_to_reorder:
  assumes "lexecute c r \<alpha> c'"
  shows "\<exists>\<alpha>'. reorder_com \<alpha>' r \<alpha>"
  using assms
  by (induct, unfold reorder_com.simps(1); blast)

lemma rif_sound_helper:
  assumes "reorder_trace t c" "local c"
  assumes "wellformed R G" "checks (rif c {}) R G"
  shows "\<forall>(r,\<alpha>) \<in> set t. inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct)
  case (1 c)
  then show ?case by auto
next
  case (2 c c' t)
  thus ?case using upd_rw local_silent unfolding checks_def by fast
next
  case (3 c r \<alpha> c' t)
  then obtain c\<^sub>2 where c2: "rif c {} = rif ((r ;; Basic \<alpha>) ;; c\<^sub>2) {}" "rif c' {} = rif (r ;; c\<^sub>2) {}"
    using rif_lexecute by metis
  obtain \<alpha>' where "reorder_com \<alpha>' r \<alpha>"
    using 3(1) exec_to_reorder by blast
  hence "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
    apply (rule upd_exec[OF 3(5)])
    using 3(6) unfolding c2(1)
    by (metis UnCI checks_def rif.simps(4) rif_split)
  moreover have "\<forall>a\<in>set t. case a of (a, b) \<Rightarrow> inter\<^sub>c (step\<^sub>t R) (step G) a b"
    using 3 upd_exec_rest unfolding c2 by (metis rif.simps(4) local_execute)
  ultimately show ?case by simp
qed

theorem rif_sound:
  assumes "checks (rif c {}) R G" "local c" "wellformed R G"
  shows "SimAsm_WP.rif (step\<^sub>t R) (step G) c"
  using assms rif_sound_helper unfolding rif_def by blast

end