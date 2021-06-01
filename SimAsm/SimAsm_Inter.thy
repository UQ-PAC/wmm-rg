theory SimAsm_Inter
  imports "HOL-Library.FSet" "SimAsm_Abs" "HOL-Library.While_Combinator" "HOL-Eisbach.Eisbach"
begin

text \<open>A data point, extends an instruction with reordering information\<close>
record ('g,'r) point =
  id :: nat
  wrs :: "('g,'r) var fset"
  rds :: "('g,'r) var fset"
  bar :: bool
  esc :: "('g,'r) var fset"
  pairs :: "(nat \<times> ('g,'r) var fset) fset"

type_synonym ('v,'g,'r,'a) enumi = "('v,'g,'r,'a) pred \<times> ('v,'g,'r) op \<times> ('v,'g,'r,'a) auxfn"
type_synonym ('v,'g,'r,'a) enuml = "('v,'g,'r,'a) enumi list"

definition hasGlobal\<^sub>e
  where "hasGlobal\<^sub>e S \<equiv> \<exists>e. Glb e |\<in>| S"

fun hasGlobalL
  where "hasGlobalL (Glb x#a) = True" | 
        "hasGlobalL [] = False" |
        "hasGlobalL (b#a) = hasGlobalL a"

lemma [intro]: "finite (deps a)" by (induct a, auto)
lemma [intro]: "finite (deps\<^sub>B a)" by (induct a, auto)
lemma [intro]: "finite (wr a)" by (induct a, auto)
lemma [intro]: "finite (rd a)" by (induct a, auto)

text \<open>Substitute a variable for an expression\<close>
fun subst :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) exp"
  where
    "subst (Var r) r' e = (if r = r' then e else Var r)" |
    "subst (Exp f rs) r e = (Exp f (map (\<lambda>x. subst x r e) rs))" |
    "subst e _ _ = e"

text \<open>The syntactic dependencies of an expression\<close>
fun ldeps :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var list"
  where 
    "ldeps (Var r) = [r]" |
    "ldeps (Exp _ rs) = List.bind rs ldeps" |
    "ldeps _ = []"

fun ldeps\<^sub>B :: "('v,'g,'r) bexp \<Rightarrow> ('g,'r) var list"
  where 
    "ldeps\<^sub>B (Neg e) = ldeps\<^sub>B e" |
    "ldeps\<^sub>B (Exp\<^sub>B _ rs) = List.bind rs ldeps"

definition fdeps 
  where "fdeps a = fset_of_list (ldeps a)"

definition fdeps\<^sub>B
  where "fdeps\<^sub>B a = fset_of_list (ldeps\<^sub>B a)"

text \<open>Variables written by an operation\<close>
fun fwr :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var fset"
  where 
    "fwr (assign y _) = {|y|}" |
    "fwr _ = {||}"

text \<open>Variables read by an operation\<close>
fun frd :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var fset"
  where
    "frd (assign _ e) = fdeps e" |
    "frd (cmp b) = fdeps\<^sub>B b" |
    "frd _ = {||}"

text \<open>Conditions under which a point is ordered after an instruction\<close>
fun ord\<^sub>e
  where
    "ord\<^sub>e nop p = (bar p)" |
    "ord\<^sub>e (cmp b) p = (bar p \<or> hasGlobal\<^sub>e (wrs p) \<or> hasGlobal\<^sub>e (fdeps\<^sub>B b |\<inter>| rds p))" |
    "ord\<^sub>e (assign v e) p = 
      (bar p \<or> 
        hasGlobal\<^sub>e (fdeps e |\<inter>| (rds p |\<union>| wrs p)) \<or> 
        (case v of Glb g \<Rightarrow> Glb g |\<in>| wrs p | _ \<Rightarrow> False) \<or> 
        (hasGlobal\<^sub>e (fdeps e) \<and> v |\<in>| rds p))" |
    "ord\<^sub>e full_fence _ = True"

text \<open>Strengthen a point based on a strictly earlier instruction\<close>
fun stren :: "('v,'g,'r) op \<Rightarrow> ('g,'r) point \<Rightarrow> ('g,'r) point"
  where
    "stren a p = p\<lparr> wrs := wrs p |\<union>| fwr a, 
                    rds := rds p |\<union>| frd a, 
                    bar := bar p \<or> fences a \<rparr>"

text \<open>Weaken a point based on a reorderable instruction\<close>
fun wken :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('g,'r) point \<Rightarrow> ('g,'r) point"
  where
    "wken n \<alpha> p = p\<lparr> rds := rds p - fwr \<alpha> |\<union>| 
                            (if fwr \<alpha> |\<inter>| rds p \<noteq> {||} then frd \<alpha> else {||}), 
                     esc := esc p |\<union>| fwr \<alpha>,
                     pairs := pairs p |\<union>| {|(n, esc p)|} \<rparr>"

text \<open>Convert an instruction into a point\<close>
definition gen :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('g,'r) point"
  where
    "gen n a = \<lparr> id = n, wrs = fwr a, rds = frd a, bar = fences a, esc = {||}, pairs = {||} \<rparr>"

text \<open>Process a new instruction against one point\<close>
definition proc1 :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('g,'r) point \<Rightarrow> ('g,'r) point"
  where
    "proc1 n \<alpha> p \<equiv> if ord\<^sub>e \<alpha> p then stren \<alpha> p else wken n \<alpha> p"

text \<open>Process a new instruction against a set of points\<close>
definition proc\<^sub>i :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('g,'r) point set \<Rightarrow> ('g,'r) point set"
  where 
    "proc\<^sub>i n a P \<equiv> proc1 n a ` P"

fun enum :: "('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> (nat, nat) com \<times> ('v,'g,'r,'a) enuml"
  where
    "enum Skip l = (com.Nil,l)" |
    "enum (Op v a f) l = (Basic (length l,{},{}),l@[(v,a,f)])" |
    "enum (Seq c\<^sub>1 c\<^sub>2) l = 
      (case enum c\<^sub>2 l of (n\<^sub>2,l) \<Rightarrow> (case enum c\<^sub>1 l of (n\<^sub>1,l) \<Rightarrow> (com.Seq n\<^sub>1 n\<^sub>2,l)))" |
    "enum (If b c\<^sub>1 c\<^sub>2) l = 
      (case enum c\<^sub>2 l of (n\<^sub>2,l) \<Rightarrow> case enum c\<^sub>1 l of (n\<^sub>1,l) \<Rightarrow> 
        (Choice (com.Seq (Basic (length l,{},{})) n\<^sub>1) (com.Seq (Basic (length l,{},{})) n\<^sub>2),
          l@[({},cmp b,state_rec.more)]))" |
    "enum (While b I c) l = 
      (case enum c l of (n,l) \<Rightarrow> 
        (com.Seq ((com.Seq (Basic (length l,{},{})) n)*) (Basic (length l,{},{}))),
          l@[({},cmp b,state_rec.more)])" |
    "enum (DoWhile I c b) l = 
      (case enum c l of (n,l) \<Rightarrow> 
        ((n ;; Basic (length l,{},{}))* ;; n ;; Basic (length l,{},{}), 
          l@[({},cmp b,state_rec.more)]))" 

text \<open>Process a new instruction against a set of points\<close>
definition rif\<^sub>i :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('g,'r) point set \<Rightarrow> ('g,'r) point set"
  where 
    "rif\<^sub>i n a P \<equiv> { gen n a } \<union> proc\<^sub>i n a P"

text \<open>Process a full program\<close>
fun rif :: "(nat, nat) com \<Rightarrow> ('v,'g,'r) op list \<Rightarrow> ('g,'r) point set \<Rightarrow> ('g,'r) point set"
  where 
    "rif (Basic a) l P = (rif\<^sub>i (tag a) (l ! (tag a)) P)" |
    "rif (Choice c\<^sub>1 c\<^sub>2) l P = (rif c\<^sub>1 l P \<union> rif c\<^sub>2 l P)" |
    "rif (Loop c) l P = lfp (\<lambda>Y. (P \<union> rif c l Y))" |
    "rif (c\<^sub>1 ;; c\<^sub>2) l P = rif c\<^sub>1 l (rif c\<^sub>2 l P)" |
    "rif _ _ P = P"
declare rif.simps(3)[simp del]

subsection \<open>Refinement\<close>

fun expand :: "(nat, nat) com \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> (('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) com"
  where
    "expand Nil l = Nil" |
    "expand (Basic a) l = (case l ! tag a of (v,\<alpha>,f) \<Rightarrow> Basic (\<lfloor>v,\<alpha>,f\<rfloor>))" |
    "expand (com.Seq c\<^sub>1 c\<^sub>2) l = com.Seq (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Choice c\<^sub>1 c\<^sub>2) l = Choice (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Loop c\<^sub>1) l = Loop (expand c\<^sub>1 l)" |
    "expand (Parallel c\<^sub>1 c\<^sub>2) l = Parallel (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Thread c\<^sub>1) l = Thread (expand c\<^sub>1 l)"

fun expand_op 
  where "expand_op (v,\<alpha>,f) = \<lfloor>v,\<alpha>,f\<rfloor>"

fun expand_pairs :: "(nat \<times> ('g,'r) var fset) fset \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> (('v,'g,'r,'a) opbasic \<times> ('g,'r) var set) set"
  where
    "expand_pairs p l = {(expand_op (l ! i), fset s) | i s. (i,s) \<in> fset p}"

fun expand_point :: "('g,'r) point \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> ('v,'g,'r,'a) SimAsm_Abs.point"
  where
    "expand_point p l = \<lparr> op = expand_op (l ! id p), 
                          wrs = fset (wrs p), 
                          rds = fset (rds p), 
                          bar = bar p, 
                          esc = fset (esc p),
                          pairs = expand_pairs (pairs p) l \<rparr>"

fun expand_points
  where "expand_points P l = (\<lambda>s. expand_point s l) ` P"

lemma [simp]:
  "inst (\<lfloor>x1,x2,x3\<rfloor>) = x2"
  by (auto simp: liftg_def)
  
lemma [simp]:
  "fset (fwr a) = wr a"
  sorry

lemma [simp]:
  "fset (frd a) = rd a"
  sorry

lemma [simp]:
  "((map (\<lambda>a. fst (snd a)) l' @ [x2]) ! length l') = x2"
  sorry

lemma
  assumes "enum c l' = (r,l)"
  shows "SimAsm_Abs.rif (lift\<^sub>c c) (expand_points P l) = expand_points (rif r (map (fst o snd) l) P) l"
  using assms
proof (induct c arbitrary: P l l' r)
  case Skip
  then show ?case by simp
next
  case (Op x1 x2 x3)
  hence [simp]: "r = Basic (length l', {}, {})" "l = l' @ [(x1, x2, x3)]" by auto
  then show ?case 
    apply (simp add: rif\<^sub>i_def gen_def SimAsm_Abs.rif\<^sub>i_def SimAsm_Abs.gen_def SimAsm_Abs.proc\<^sub>i_def) sorry
next
  case (Seq c1 c2)
  show ?case
    unfolding lift\<^sub>c.simps SimAsm_Abs.rif.simps
    apply simp sorry
next
  case (If x1 c1 c2)
  then show ?case sorry
next
  case (While x1 x2 c)
  then show ?case sorry
next
  case (DoWhile x1 c x3)
  then show ?case sorry
qed


(*
text \<open>Interference Check\<close>
fun sp 
  where 
    "sp P (v,i,a) R = {m. \<exists>m' m''. m' \<in> P \<and> (m',m'') \<in> beh\<^sub>i i \<and> (m''(aux: a),m) \<in> step\<^sub>t R}"
 
definition chk 
  where
    "chk a b R = (\<forall>P. stable\<^sub>t R P \<longrightarrow> sp (sp P a R) b R  \<subseteq> sp (sp P b R) a R)"

definition checks 
  where "checks l P R \<equiv> \<forall>p \<in> P. \<forall>i. i |\<in>| pairs p \<longrightarrow> chk (l ! i) (l ! id p) R"

definition rif_full
  where "rif_full c \<equiv> case enum c [] of (n,l) \<Rightarrow> (rif n (map (fst o snd) l) {},l)"

definition rif_checks
  where "rif_checks c R \<equiv> case rif_full c of (n,l) \<Rightarrow> checks l n R"

section \<open>Soundness\<close>

lemma mono_proc\<^sub>i:
  "mono (proc\<^sub>i n a)"
  by (smt Un_mono image_Un monoI order_refl sup.orderE sup_ge2 proc\<^sub>i_def)

lemma mono_rif\<^sub>i:
  "mono (rif\<^sub>i n a)"
  by (smt Un_mono monoI mono_Un mono_proc\<^sub>i rif\<^sub>i_def subset_Un_eq subset_refl sup.bounded_iff)

lemma mono_proc:
  "mono (proc c l)"
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
  "mono (rif c l)"
proof (induct c)
  case (Basic x)
  then show ?case by (cases "tag x < length l") (auto simp add: monoI mono_rif\<^sub>i)
next
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
  "mono (\<lambda>Y. (P \<union> rif c l Y))"
  by (smt Un_mono monoD monoI mono_rif sup.idem sup.order_iff)

lemma [simp]:
  "proc r l (P \<union> Q) = proc r l P \<union> proc r l Q"
proof (induct r arbitrary: P Q)
  case (Loop r)
  have p: "lfp (\<lambda>Y. P \<union> Q \<union> proc r l Y) \<supseteq> lfp (\<lambda>Y. P \<union> proc r l Y)"
    apply (rule lfp_mono)
    by auto
  have q: "lfp (\<lambda>Y. P \<union> Q \<union> proc r l Y) \<supseteq> lfp (\<lambda>Y. Q \<union> proc r l Y)"
    apply (rule lfp_mono)
    by auto
  hence a: "lfp (\<lambda>Y. P \<union> Q \<union> proc r l Y) \<supseteq> lfp (\<lambda>Y. Q \<union> proc r l Y) \<union> lfp (\<lambda>Y. P \<union> proc r l Y)" (is "?L \<supseteq> ?R")
    using p by auto
  hence lr: "?L \<inter> ?R = ?R" by blast
  have "lfp (\<lambda>Y. Q \<union> proc r l Y) \<union> lfp (\<lambda>Y. P \<union> proc r l Y) \<supseteq> lfp (\<lambda>Y. P \<union> Q \<union> proc r l Y)"
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
  "rif r l (P \<union> Q) = rif r l P \<union> rif r l Q"
proof (induct r arbitrary: P Q)
  case (Loop r)
  have p: "lfp (\<lambda>Y. P \<union> Q \<union> rif r l Y) \<supseteq> lfp (\<lambda>Y. P \<union> rif r l Y)"
    apply (rule lfp_mono)
    by auto
  have q: "lfp (\<lambda>Y. P \<union> Q \<union> rif r l Y) \<supseteq> lfp (\<lambda>Y. Q \<union> rif r l Y)"
    apply (rule lfp_mono)
    by auto
  hence a: "lfp (\<lambda>Y. P \<union> Q \<union> rif r l Y) \<supseteq> lfp (\<lambda>Y. Q \<union> rif r l Y) \<union> lfp (\<lambda>Y. P \<union> rif r l Y)" (is "?L \<supseteq> ?R")
    using p by auto
  hence lr: "?L \<inter> ?R = ?R" by blast
  have "lfp (\<lambda>Y. Q \<union> rif r l Y) \<union> lfp (\<lambda>Y. P \<union> rif r l Y) \<supseteq> lfp (\<lambda>Y. P \<union> Q \<union> rif r l Y)"
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
  "rif r l P = proc r l P \<union> rif r l {}"
proof (induct r arbitrary: P)
  case (Seq r1 r2)
  show ?case 
    using Seq(2)[of P] Seq(1)[of "rif r2 l P"] Seq(1)[of "rif r2 l {}"]
    apply simp by blast
next
  case (Choice r1 r2)
  then show ?case unfolding rif.simps proc.simps by blast
next
  case (Loop r)
  have p: "lfp (\<lambda>Y. P \<union> rif r l Y) \<supseteq> lfp (\<lambda>Y. P \<union> proc r l Y)" (is "?L \<supseteq> ?R1")
    apply (rule lfp_mono)
    using Loop by blast
  have q: "lfp (\<lambda>Y. P \<union> rif r l Y) \<supseteq> lfp (\<lambda>Y. {} \<union> rif r l Y)" (is "?L \<supseteq> ?R2")
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
    unfolding Loop[of "lfp (\<lambda>Y. P \<union> proc r l Y)"]
    apply auto
     using lfp_fn mono_proc apply fast
    by (metis Loop.hyps UnCI lfp_unfold mono_rif)
  then show ?case unfolding rif.simps proc.simps using a by blast
qed (auto simp: proc\<^sub>i_def rif\<^sub>i_def)

(*
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

lemma rif\<^sub>i_I:
  assumes "p \<in> P"
  shows "ord (inst \<alpha>) p \<longrightarrow> stren \<alpha> p \<in> rif\<^sub>i \<alpha> P"
        "\<not>ord (inst \<alpha>) p \<longrightarrow> (wken \<alpha> p)\<lparr>inv := inv p \<and> chk \<alpha> (op p)\<rparr> \<in> rif\<^sub>i \<alpha> P"
  using assms unfolding proc\<^sub>i_def proc1_def rif\<^sub>i_def by auto

lemma rif\<^sub>i_preserve_inv [intro]:
  assumes "\<forall> x \<in> rif\<^sub>i \<alpha> P. point.inv x" 
  shows "\<forall>p \<in> P. inv p"
proof (clarsimp)
  fix x assume a: "x \<in> P"
  show "point.inv x" 
  proof (cases "ord (inst \<alpha>) x")
    case True
    hence "stren \<alpha> x \<in> rif\<^sub>i \<alpha> P" using rif\<^sub>i_I[OF a, of \<alpha>] by simp
    then show ?thesis using assms by auto
  next
    case False
    hence "(wken \<alpha> x)\<lparr>inv := inv x \<and> chk R \<alpha> (op x)\<rparr> \<in> rif\<^sub>i \<alpha> P"
      using rif\<^sub>i_I[OF a, of \<alpha>] by simp
    then show ?thesis using assms by auto
  qed
qed 

lemma rif_preserve_inv [intro]:
  assumes "\<forall>p \<in> rif c P. inv p"
  shows "\<forall>p \<in> P. inv p"
  using assms
proof (induct c arbitrary: P)
  case (Basic x)
  then show ?case using rif\<^sub>i_preserve_inv by fastforce
next
  case (Seq c1 c2)
  then show ?case unfolding rif.simps by blast
next
  case (Choice c1 c2)
  then show ?case unfolding rif.simps by blast
next
  case (Loop c)
  then show ?case unfolding rif.simps 
    using lfp_unfold mono_union_rif by blast 
qed (unfold rif.simps, blast)


lemma point_cmp_refl [intro]:
  "point_cmp a a"
  by (auto simp: point_cmp_def)

lemma [simp]:
  "deps (subst e r e') = deps e - {r} \<union> (if r \<in> deps e then deps e' else {})"
  sorry

lemma [simp]:
  "deps\<^sub>B (subst\<^sub>B e r e') = deps\<^sub>B e - {r} \<union> (if r \<in> deps\<^sub>B e then deps e' else {})"
  sorry

lemma ord_sound:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  shows "\<not>ord (inst \<beta>) (gen \<alpha>)"
  using assms
  apply (cases \<alpha>; cases \<beta>; clarsimp; case_tac a; case_tac aa)
  by (auto simp: gen_def)

lemma ord_cmp:
  assumes "\<not>ord \<beta> p'" "p \<prec> p'"
  shows "\<not>ord \<beta> p"
  using assms by (cases \<beta>, auto simp: point_cmp_def)

lemma
  assumes "reorder_com \<alpha>' (Basic \<beta>) \<alpha>" "p \<prec> gen \<alpha>"
  shows "\<not> ord (inst \<beta>) p"
  apply (rule ord_cmp)
  apply (rule ord_sound)
  using assms by auto

(*
lemma upd_reorder_com:
  assumes "reorder_com \<alpha>' c \<alpha>" "p \<in> P" "p \<prec> gen \<alpha>" "op p = \<alpha>"
  shows "\<exists>p'. p' \<in> rif c P \<and> op p' = \<alpha>' \<and> p' \<prec> gen \<alpha>'"
  using assms
proof (induct \<alpha>' c \<alpha> rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  hence [simp]: "op p = \<alpha>" by auto
  have "\<not> ord (inst \<beta>) p" sorry

  hence "(wken \<beta> p)\<lparr>inv := inv p \<and> chk R \<beta> (op p)\<rparr> \<in> proc \<beta> P"
    using proc_I 2 by blast

  moreover have "(wken \<beta> p)\<lparr>inv := inv p \<and> chk R \<beta> (op p)\<rparr> \<prec> gen \<alpha>'"
    using 2(1,4) unfolding point_cmp_def gen_def
    apply auto
    apply (cases \<alpha>'; cases \<beta>; case_tac a; case_tac aa; case_tac ab; case_tac ac; simp split: if_splits)
    
    sorry

  moreover have "op ((wken \<beta> p)\<lparr>inv := inv p \<and> chk R \<beta> (op p)\<rparr>) = \<alpha>'" using 2 by auto

  ultimately show ?case by auto
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then show ?case
    apply simp
    sorry
qed auto


lemma execute_act:
  assumes "lexecute c r \<alpha> c'"
  shows "\<exists>p. p \<in> rif c P \<and> op p = (fwd_com \<alpha> r) \<and> point_cmp p (gen (fwd_com \<alpha> r))"
  using assms
proof (induct arbitrary: P)
  case (act \<alpha>)
  have "gen \<alpha> \<in> proc \<alpha> P" by (auto simp: proc_def)
  then show ?case by (auto simp: gen_def)
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case by simp
next
  case (ooo c\<^sub>1 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>2)
  obtain p where p: "p \<in> rif c\<^sub>1 P" "op p = (fwd_com \<alpha> r)" "point_cmp p (gen (fwd_com \<alpha> r))"
    using ooo by blast
  have r: "reorder_com \<alpha>' (c\<^sub>2) (fwd_com \<alpha> r)" using ooo by auto
  then show ?case using p(2) upd_reorder_com[OF r p(1,3), of R] by auto
qed

(*
lemma upd_po:
  assumes "reorder_com \<alpha>' c \<alpha>" "p \<in> P" "point_cmp p (gen \<alpha>)" "\<alpha> = op p" "\<forall>a \<in> rif c P. point.inv a"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) c \<alpha>"
  using assms
proof (induct \<alpha>' c \<alpha> arbitrary: P rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  hence "\<not> ord (inst \<beta>) p" sorry (* correctness of ordering analysis *)
  hence "(wken (inst \<beta>) p)\<lparr>inv := inv p \<and> chk R \<beta> p\<rparr> \<in> rif \<beta> P"
    using 2(2) unfolding upd\<^sub>a_def upd2.simps upd\<^sub>i.simps by auto
  hence "chk R \<beta> p" using 2 by auto
  then show ?case
    apply simp
    sorry (* correctness of chk *)
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then show ?case sorry
qed auto
*)

lemma upd_exec':
  assumes "lexecute c r \<alpha> c'"
  assumes "\<forall>p \<in> rif c P. inv p"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct arbitrary: P)
  case (act \<alpha>)
  then show ?case by auto
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case by auto
next
  case (ooo c\<^sub>1 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>2)
  then obtain p where p: "p \<in> rif c\<^sub>1 P" "op p = fwd_com \<alpha> r" "point_cmp p (gen (fwd_com \<alpha> r))"
    using execute_act by blast
  have r: "reorder_com \<alpha>' (c\<^sub>2) (fwd_com \<alpha> r)" using ooo by auto
  have f: "fwd_com \<alpha> r =  (op p) " using p by auto
  have "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>" using ooo rif_preserve_inv by force
  thus ?case using upd_po[OF r p(1,3) f] ooo(4) by auto
qed

lemma upd\<^sub>aE:
  assumes "x \<in> proc \<alpha> P"
  obtains (ord) p where "ord (inst \<alpha>) p" "x = stren \<alpha> p" "p \<in> P" |
          (ooo) p where "\<not> ord (inst \<alpha>) p" "x = (wken \<alpha> p)\<lparr>inv := inv p \<and> chk R \<alpha> (op p)\<rparr>" "p \<in> P" |
          (gen) "x = gen \<alpha>"
proof -
  have "x = gen \<alpha> \<or> x \<in> proc1 R \<alpha> ` P" using assms by (auto simp: proc_def)
  thus ?thesis
  proof (elim disjE)
    assume "x = gen \<alpha>"
    thus ?thesis using gen by auto
  next
    assume "x \<in> proc1 R \<alpha> ` P"
    then obtain p where p: "p \<in> P" "x = proc1 R \<alpha> p" by blast
    thus ?thesis
    proof (cases "ord (inst \<alpha>) p")
      case True
      thus ?thesis using p ord by (auto simp: proc1_def)
    next
      case False
      thus ?thesis using p ooo by (auto simp: proc1_def)
    qed
  qed
qed*)

(*
This isn't quite right, as this relation won't be preserved across
earlier actions.

*)

definition set_ord (infix "\<lhd>" 60)
  where "set_ord P' P \<equiv> \<forall>p' \<in> P'. \<exists>p \<in> P. p' \<prec> p"

definition ignore_deps ("_ \<prec>_,_,_\<prec> _" 60)
  where "ignore_deps P \<alpha> r R P' \<equiv> rif r P \<lhd> rif r (rif\<^sub>i \<alpha> P')"

lemma ignore_deps_pres:
  assumes "reorder_inst \<alpha>' \<beta> (fwd_com \<alpha> r)"
  shows "P \<prec>\<alpha>,r,R\<prec> Q \<Longrightarrow> rif\<^sub>i \<beta> P \<prec>\<alpha>,Basic \<beta>;;r,R\<prec> rif\<^sub>i \<beta> Q"
  unfolding ignore_deps_def proc\<^sub>i_def set_ord_def rif\<^sub>i_def by auto

lemma rif_transitive:
  assumes "reorder_com \<alpha>' r' (fwd_com \<alpha> r)"
  shows "P \<prec>\<alpha>,r,R\<prec> Q \<Longrightarrow> rif r' P \<prec>\<alpha>,r';;r,R\<prec> rif r' Q"
  using assms
proof (induct r' arbitrary: r \<alpha>' \<alpha> P Q)
  case Nil
  then show ?case by (auto simp: ignore_deps_def)
next
  case (Basic \<beta>)
  thus ?case using ignore_deps_pres apply simp sorry
next
  case (Seq r\<^sub>1 r\<^sub>2)
  obtain \<alpha>'' where r: "reorder_com \<alpha>'' r\<^sub>2 (fwd_com \<alpha> r)" "reorder_com \<alpha>' r\<^sub>1 (fwd_com \<alpha> (r\<^sub>2 ;; r))"
    using Seq by auto
  have s: "SimAsm_Inter.rif r\<^sub>2 P \<prec>\<alpha>,r\<^sub>2 ;; r,R\<prec> SimAsm_Inter.rif r\<^sub>2 Q"
    using Seq(2)[OF Seq(3) r(1)] by auto
  show ?case using Seq(1)[OF s r(2)] 
    unfolding ignore_deps_def by auto
qed auto

lemma rif_lexecute:
  assumes "lexecute c r \<alpha> c'"
  shows "\<exists>c\<^sub>2. rif c P = rif ((r ;; Basic \<alpha>) ;; c\<^sub>2) P \<and> rif c' P = rif (r ;; c\<^sub>2) P"
using assms
proof (induct arbitrary: P)
  case (act \<alpha>)
  have a: "rif\<^sub>i \<alpha> P = rif\<^sub>i \<alpha> (SimAsm_Inter.rif Nil P)" "P = rif Nil P" by auto
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

theorem rif_sound_helper:
  assumes "reorder_trace t c" "local c"
  assumes "\<forall>p \<in> rif c P. inv p"
  shows "\<forall>(r,\<alpha>) \<in> set t. inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct)
  case (1 c)
  then show ?case by auto
next
  case (2 c c' t)
  then show ?case using upd_rw[OF 2(1)] local_silent by blast
next
  case (3 c r \<alpha> c' t)
  obtain c\<^sub>2 where "rif c P = rif ((r ;; Basic \<alpha>) ;; c\<^sub>2) P" "rif c' P = rif (r ;; c\<^sub>2) P"
    using rif_lexecute 3 by metis
  then show ?case using  local_execute[OF 3(1,4)] by auto
qed
*)

fun expand :: "(nat, nat) com \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> (('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) com"
  where
    "expand Nil l = Nil" |
    "expand (Basic a) l = (case l ! tag a of (v,\<alpha>,f) \<Rightarrow> Basic (\<lfloor>v,\<alpha>,f\<rfloor>))" |
    "expand (com.Seq c\<^sub>1 c\<^sub>2) l = com.Seq (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Choice c\<^sub>1 c\<^sub>2) l = Choice (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Loop c\<^sub>1) l = Loop (expand c\<^sub>1 l)" |
    "expand (Parallel c\<^sub>1 c\<^sub>2) l = Parallel (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Thread c\<^sub>1) l = Thread (expand c\<^sub>1 l)"

lemma expand_seqE [elim!]:
  assumes "expand n l = c\<^sub>1 ;; c\<^sub>2"
  obtains n\<^sub>1 n\<^sub>2 where "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = n\<^sub>1 ;; n\<^sub>2"
  using assms by (cases "(n,l)" rule: expand.cases) (auto split: prod.splits)

lemma expand_seqE' [elim!]:
  assumes "c\<^sub>1 ;; c\<^sub>2  = expand n l"
  obtains n\<^sub>1 n\<^sub>2 where "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = n\<^sub>1 ;; n\<^sub>2"
  using assms by (cases "(n,l)" rule: expand.cases) (auto split: prod.splits)

lemma expand_nilE [elim!]:
  assumes "expand n l = com.Nil"
  obtains "n = com.Nil"
  using assms by (cases "(n,l)" rule: expand.cases) (auto split: prod.splits)

lemma expand_nilE' [elim!]:
  assumes "com.Nil = expand n l"
  obtains "n = com.Nil"
  using assms by (cases "(n,l)" rule: expand.cases) (auto split: prod.splits)

lemma expand_choiceE [elim!]:
  assumes "expand n l = Choice c\<^sub>1 c\<^sub>2"
  obtains n\<^sub>1 n\<^sub>2 where "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = Choice n\<^sub>1 n\<^sub>2"
  using assms by (cases "(n,l)" rule: expand.cases) (auto split: prod.splits)

lemma expand_choiceE' [elim!]:
  assumes "Choice c\<^sub>1 c\<^sub>2 = expand n l"
  obtains n\<^sub>1 n\<^sub>2 where "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = Choice n\<^sub>1 n\<^sub>2"
  using assms by (cases "(n,l)" rule: expand.cases) (auto split: prod.splits)

lemma expand_loopE' [elim!]:
  assumes "Loop c\<^sub>1 = expand n l"
  obtains n\<^sub>1 where "expand n\<^sub>1 l = c\<^sub>1" "n = Loop n\<^sub>1"
  using assms by (cases "(n,l)" rule: expand.cases) (auto split: prod.splits)

lemma expand_basicE' [elim!]:
  assumes "Basic b = expand n l"
  obtains a v \<alpha> f where " l ! tag a = (v,\<alpha>,f)" "n = Basic a" "b = (\<lfloor>v,\<alpha>,f\<rfloor>)"
  using assms by (cases "(n,l)" rule: expand.cases) (auto split: prod.splits)

lemma rif_sound_sil:
  assumes "c \<leadsto> c'" "local c" "c = expand n l"
  obtains n' where "rif n (map (fst o snd) l) P \<supseteq> rif n' (map (fst o snd) l) P" "expand n' l = c'"
  using assms
proof (induct arbitrary: n P)
  case (seq1 c\<^sub>1 c\<^sub>1' c\<^sub>2)
  then obtain n\<^sub>1 n\<^sub>2 where n: "local c\<^sub>1" "c\<^sub>1 = expand n\<^sub>1 l" "expand n\<^sub>2 l = c\<^sub>2" "n = n\<^sub>1 ;; n\<^sub>2" by auto
  show ?case 
    apply (rule seq1(2)[OF _ n(1,2)])
    apply (rule seq1(3)[of "n' ;; n\<^sub>2" for n'])
    using n(3,4) by auto
next
  case (seq2 c\<^sub>2 c\<^sub>2' c\<^sub>1)
  then obtain n\<^sub>1 n\<^sub>2 where n: "local c\<^sub>2" "c\<^sub>2 = expand n\<^sub>2 l" "c\<^sub>1 = expand n\<^sub>1 l" "n = n\<^sub>1 ;; n\<^sub>2" by auto
  show ?case
    apply (rule seq2(2)[OF _ n(1,2)])
    apply (rule seq2(3)[of "n\<^sub>1 ;; n'" for n'])
    using n apply auto 
    using mono_rif[of n\<^sub>1 "map (\<lambda>a. fst (snd a)) l"] apply (drule monoD)
    by auto
next
  case (seqE1 c\<^sub>1)
  then obtain n\<^sub>1 where n:  "c\<^sub>1 = expand n\<^sub>1 l" "n = Nil ;; n\<^sub>1" by auto
  then show ?case using seqE1(1)[of n\<^sub>1] by auto
next
  case (seqE2 c\<^sub>1)
  then obtain n\<^sub>1 where n: "c\<^sub>1 = expand n\<^sub>1 l" "n = n\<^sub>1 ;; Nil" by auto
  then show ?case using seqE2(1)[of n\<^sub>1] by auto
next
  case (left c\<^sub>1 c\<^sub>2)
  then obtain n\<^sub>1 n\<^sub>2 where n: "local c\<^sub>1" "c\<^sub>1 = expand n\<^sub>1 l" "expand n\<^sub>2 l = c\<^sub>2" "n = Choice n\<^sub>1 n\<^sub>2" by auto
  then show ?case using left(1)[of n\<^sub>1] by auto
next
  case (right c\<^sub>1 c\<^sub>2)
  then obtain n\<^sub>1 n\<^sub>2 where n: "local c\<^sub>1" "c\<^sub>1 = expand n\<^sub>1 l" "expand n\<^sub>2 l = c\<^sub>2" "n = Choice n\<^sub>1 n\<^sub>2" by auto
  then show ?case using right(1)[of n\<^sub>2] by auto
next
  case (loop1 c)
  then obtain n\<^sub>1 where n: "n = Loop n\<^sub>1" by auto
  thus ?case using loop1(1)[of "Nil"] lfp_unfold mono_union_rif by (auto simp: rif.simps(3))
next
  case (loop2 c)
  then obtain n\<^sub>1 where n: "expand n\<^sub>1 l = c" "n = Loop n\<^sub>1" by auto
  then show ?case using loop2(1)[of "n\<^sub>1 ;; n"] apply auto unfolding rif.simps
    using lfp_fn[OF mono_rif] by blast
qed (unfold local.simps; simp)+

lemma rif_sound_exec:
  assumes "lexecute c r \<alpha> c'" "local c" "c = expand n l"
  obtains n' where "rif n (map (fst o snd) l) P \<supseteq> rif n' (map (fst o snd) l) P" "expand n' l = c'"
  using assms
proof (induct arbitrary: n P)
  case (act \<alpha>)
  then show ?case sorry
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case sorry
next
  case (ooo c\<^sub>1 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>2)
  then show ?case sorry
qed

lemma rif_lexecute:
  assumes "lexecute c r \<alpha> c'" "expand n l = c" 
  obtains c\<^sub>2 n' where "rif n (map (fst o snd) l) P = rif n' (map (fst o snd) l) P" "expand n' l = ((r ;; Basic \<alpha>) ;; c\<^sub>2)"
using assms
proof (induct arbitrary: P n)
  case (act \<alpha>)
  show ?case using act(1)[of "(Nil ;; n) ;; Nil" Nil] act(2) by auto
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  obtain n\<^sub>1 n\<^sub>2 where n: "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = n\<^sub>1 ;; n\<^sub>2" using ino(4) by auto
  show ?case
  proof (rule ino(2)[OF _ n(1), of "rif n\<^sub>2 (map (fst \<circ> snd) l) P"], goal_cases)
    case (1 n' c\<^sub>2')
    then obtain n\<^sub>1' n\<^sub>2' where "expand n\<^sub>1' l = r ;; Basic \<alpha>" "expand n\<^sub>2' l = c\<^sub>2'" "n' = n\<^sub>1' ;; n\<^sub>2'"
      by force
    thus ?case 
      using 1(1) n(2) ino(3)[of "n\<^sub>1' ;; (n\<^sub>2' ;; n\<^sub>2)" "c\<^sub>2' ;; c\<^sub>2"] 
      by (auto simp: n(3) o_def) 
  qed
next
  case (ooo c\<^sub>2 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>1)
  then obtain n\<^sub>1 n\<^sub>2 where n: "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = n\<^sub>1 ;; n\<^sub>2" by auto
  show ?case
  proof (rule ooo(2)[OF _ n(2), of P], goal_cases)
    case (1 n' c\<^sub>2')
    then obtain n\<^sub>1' n\<^sub>2' where n': "expand n\<^sub>1' l = r ;; Basic \<alpha>" "expand n\<^sub>2' l = c\<^sub>2'" "n' = n\<^sub>1' ;; n\<^sub>2'"
      by force
    then obtain n\<^sub>1'' n\<^sub>2'' where n'': "expand n\<^sub>1'' l = r" "expand n\<^sub>2'' l = Basic \<alpha>" "n\<^sub>1' = n\<^sub>1'' ;; n\<^sub>2''"
      by force
    then show ?case
      using 1(1) n(1,2) n'(1,2) ooo(4)[of "((n\<^sub>1 ;; n\<^sub>1'') ;; n\<^sub>2'') ;; n\<^sub>2'" c\<^sub>2']
      by (auto simp: n(3) n'(3))
  qed
qed

lemma rif_lexecute':
  assumes "lexecute c r \<alpha> c'" "expand n l = c" 
  obtains c\<^sub>2 n' n'' n''' where 
    "rif n (map (fst o snd) l) P = rif n' (map (fst o snd) l) P" 
    "expand n' l = ((r ;; Basic \<alpha>) ;; c\<^sub>2)"
    "expand n'' l = c'"
    "expand n''' l = (r ;; c\<^sub>2)"
    "rif n'' (map (fst o snd) l) P = rif n''' (map (fst o snd) l) P" 
using assms
proof (induct arbitrary: P n)
  case (act \<alpha>)
  show ?case using act(1)[of "(Nil ;; n) ;; Nil" Nil Nil "Nil ;; Nil"] act(2) by auto
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  obtain n\<^sub>1 n\<^sub>2 where n: "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = n\<^sub>1 ;; n\<^sub>2" using ino(4) by auto
  show ?case
  proof (rule ino(2)[OF _ n(1), of "rif n\<^sub>2 (map (fst \<circ> snd) l) P"], goal_cases)
    case (1 n' c\<^sub>2' n'' n''')
    then obtain n\<^sub>1' n\<^sub>2' where n': "expand n\<^sub>1' l = r ;; Basic \<alpha>" "expand n\<^sub>2' l = c\<^sub>2'" "n' = n\<^sub>1' ;; n\<^sub>2'"
      by force
    then obtain n\<^sub>1'' n\<^sub>2'' where n'': "expand n\<^sub>1'' l = r" "expand n\<^sub>2'' l = Basic \<alpha>" "n\<^sub>1' = n\<^sub>1'' ;; n\<^sub>2''"
      by force
    thus ?case 
      using n' 1(1,3,4,5) n(2) ino(3)[of "n\<^sub>1' ;; (n\<^sub>2' ;; n\<^sub>2)" "c\<^sub>2' ;; c\<^sub>2" "n'' ;; n\<^sub>2" "n\<^sub>1'' ;; n\<^sub>2' ;; n\<^sub>2"] 
      by (auto simp: n(3) o_def) 
  qed
next
  case (ooo c\<^sub>2 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>1)
  then obtain n\<^sub>1 n\<^sub>2 where n: "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = n\<^sub>1 ;; n\<^sub>2" by auto
  show ?case
  proof (rule ooo(2)[OF _ n(2), of P], goal_cases)
    case (1 n' c\<^sub>2')
    then obtain n\<^sub>1' n\<^sub>2' where n': "expand n\<^sub>1' l = r ;; Basic \<alpha>" "expand n\<^sub>2' l = c\<^sub>2'" "n' = n\<^sub>1' ;; n\<^sub>2'"
      by force
    then obtain n\<^sub>1'' n\<^sub>2'' where n'': "expand n\<^sub>1'' l = r" "expand n\<^sub>2'' l = Basic \<alpha>" "n\<^sub>1' = n\<^sub>1'' ;; n\<^sub>2''"
      by force
    then show ?case
      using 1(1) n(1,2) n'(1,2) ooo(4)[of "((n\<^sub>1 ;; n\<^sub>1'') ;; n\<^sub>2'') ;; n\<^sub>2'" c\<^sub>2']
      by (auto simp: n(3) n'(3))
  qed
qed

lemma upd_exec':
  assumes "lexecute c r \<alpha> c'" "expand n l = c"
  assumes "checks l (rif n (map (fst o snd) l) P) R"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct arbitrary: n P)
  case (act \<alpha>)
  then show ?case by auto
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case by auto
next
  case (ooo c\<^sub>2 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>1)
  then obtain n\<^sub>1 n\<^sub>2 where n: "expand n\<^sub>1 l = c\<^sub>1" "expand n\<^sub>2 l = c\<^sub>2" "n = n\<^sub>1 ;; n\<^sub>2" by auto
  hence "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>" using ooo(5) ooo(2)[OF n(2), of P]
    unfolding n(3)
    sorry
  then show ?case sorry

  then obtain p where p: "p \<in> rif c\<^sub>1 P" "op p = fwd_com \<alpha> r" "point_cmp p (gen (fwd_com \<alpha> r))"
    using execute_act by blast
  have r: "reorder_com \<alpha>' (c\<^sub>2) (fwd_com \<alpha> r)" using ooo by auto
  have f: "fwd_com \<alpha> r =  (op p) " using p by auto
  have "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>" using ooo rif_preserve_inv by force
  thus ?case using upd_po[OF r p(1,3) f] ooo(4) by auto
qed  

lemma [simp]:
  "tag (\<lfloor>v,\<alpha>,f\<rfloor>) = (\<alpha>,f)"
  by (auto simp: liftg_def)

lemma
  assumes "reorder_com \<alpha>' r \<alpha>"
  assumes "r = expand n l" "\<forall>a \<in> basics n. tag a < length l" 
  assumes "Basic \<alpha> = expand (Basic a) l" "tag a < length l"
  assumes "checks l (rif (n ;; Basic a)  (map (fst o snd) l) P) R"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct arbitrary: n a rule: reorder_com.induct )
  case (2 \<alpha>' \<beta> \<alpha>)
  then show ?case
    apply (auto split: prod.splits)
    sorry
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then show ?case sorry
qed (unfold reorder_com.simps, auto)

theorem rif_sound:
  assumes "reorder_trace t c" "local c"
  assumes "expand n l = c"
  assumes "checks l (rif n (map (fst o snd) l) {}) R"
  shows "\<forall>(r,\<alpha>) \<in> set t. inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct arbitrary: n)
  case (1 c)
  then show ?case by auto
next
  case (2 c c' t)
  then obtain n' where "rif n (map (fst o snd) l) {} \<supseteq> rif n' (map (fst o snd) l) {}" "expand n' l = c'"
    using rif_sound_sil by metis
  moreover have "local c'" using 2 local_silent by auto
  ultimately show ?case using 2 unfolding checks_def by blast
next
  case (3 c r \<alpha> c' t)
  then obtain c\<^sub>2 n' where 
      "rif n (map (fst o snd) l) {} = rif n' (map (fst o snd) l) {}" 
      "expand n' l = ((r ;; Basic \<alpha>) ;; c\<^sub>2)"
    using rif_lexecute by metis

  then show ?case sorry
qed
*)

end