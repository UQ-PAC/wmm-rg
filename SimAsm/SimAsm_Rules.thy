theory SimAsm_Rules
  imports SimAsm_WP SimAsm_Semantics "../Soundness" "HOL-Eisbach.Eisbach"
begin

subsection \<open>Conversion between tstack and varmap.\<close>

definition vm_of_ts :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) varmap'"
  where "vm_of_ts s \<equiv> \<lparr> varmap_st = tlookup s, \<dots> = taux s\<rparr>"

(*
definition ts_of_vm :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) tstack"
  where "ts_of_vm \<equiv> inv vm_of_ts"
*)

lemma ts_of_vm_exists: "\<exists>ts. vm_of_ts ts = vm"
proof
  let ?s = "[\<lparr> frame_st = Some \<circ> varmap_st vm, frame_cap = UNIV, \<dots> = Some (varmap_rec.more vm) \<rparr>]"
  have "Is_tstack ?s" by (simp add: Is_tstack_def)
  thus "vm_of_ts (Abs_tstack ?s) = vm" unfolding vm_of_ts_def
    by (simp add: tlookup.rep_eq taux.rep_eq Abs_tstack_inverse fun_eq_iff)
qed

lemma vm_of_ts_tauxupd [simp]:
  "vm_of_ts (tauxupd y f) = (vm_of_ts y)\<lparr> varmap_rec.more := f y \<rparr>"
  unfolding vm_of_ts_def by auto

lemma vm_of_ts_tupdate [simp]:
  "vm_of_ts (tupdate y x e) = (vm_of_ts y)\<lparr> varmap_st := (varmap_st (vm_of_ts y))(x := e) \<rparr>"
  unfolding vm_of_ts_def by auto

lemma vm_of_ts_varmap [simp]:
  "varmap_st (vm_of_ts x) = tlookup x"
  unfolding vm_of_ts_def by auto

lemma vm_of_ts_tpush_empty [simp]:
  "vm_of_ts (tstack_push m (emptyFrame w)) = vm_of_ts m"
  by (auto simp: vm_of_ts_def emptyFrame_def)


(*
lemma ts_of_vm_inverse: "vm_of_ts (ts_of_vm vm) = vm"
proof -
  have a: "ts_of_vm vm = (SOME ts. vm_of_ts ts = vm)"
    by (simp add: inv_def ts_of_vm.abs_eq)
  have "varmap_st vm = tlookup (ts_of_vm vm)"
    using a ts_of_vm_exists
    by (metis (mono_tags, lifting) varmap_rec.select_convs(1) verit_sko_ex' vm_of_ts.transfer)
  moreover have "varmap_rec.more vm = taux (ts_of_vm vm)"
    using a ts_of_vm_exists
    by (metis (mono_tags, lifting) varmap_rec.select_convs(2) verit_sko_ex' vm_of_ts.transfer)
  ultimately show ?thesis unfolding vm_of_ts_def by simp
qed*)

lift_definition ts_pred_of_vm_pred :: "('r,'v,'a) varmap' pred \<Rightarrow> ('r,'v,'a) tstack pred" is
  "\<lambda>v. vm_of_ts -` v".

lift_definition vm_pred_of_ts_pred :: "('r,'v,'a) tstack pred \<Rightarrow> ('r,'v,'a) varmap' pred" is
  "\<lambda>S. vm_of_ts ` S".

lift_definition vm_rel_of_ts_rel :: "('r,'v,'a) tstack rel \<Rightarrow> ('r,'v,'a) varmap' rel" is
  "\<lambda>x. {(vm_of_ts s,vm_of_ts s') | s s'. (s,s') \<in> x}".

lift_definition ts_rel_of_vm_rel :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel" is
  "\<lambda>x. {(s,s') | s s'. (vm_of_ts s,vm_of_ts s') \<in> x}".

(*
fun vm_lang_of_ts_lang :: "('r,'v,('r,'v,'a)tstack,'a) lang \<Rightarrow> ('r, 'v, ('r, 'v, 'a) varmap', 'a) lang" where
  "vm_lang_of_ts_lang (Skip) = Skip " |
  "vm_lang_of_ts_lang (Op pred op auxfn) = Op (vm_of_ts ` pred) op (auxfn \<circ> ts_of_vm)" |
  "vm_lang_of_ts_lang (lang.Seq a b) = lang.Seq (vm_lang_of_ts_lang a) (vm_lang_of_ts_lang b) " |
  "vm_lang_of_ts_lang (If c t f) = If c (vm_lang_of_ts_lang t) (vm_lang_of_ts_lang f)" |
  "vm_lang_of_ts_lang (While b Imix Ispec c) = While b (vm_of_ts ` Imix) (vm_of_ts ` Ispec) (vm_lang_of_ts_lang c) " |
  "vm_lang_of_ts_lang (DoWhile Imix Ispec c b) = DoWhile (vm_of_ts ` Imix) (vm_of_ts ` Ispec) (vm_lang_of_ts_lang c) b "
*)

subsection \<open>Correspondence from spec_state to tstack.\<close>

definition tstack_base :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) varmap'" where
  "tstack_base stack \<equiv> \<lparr> varmap_st = tbase_st stack, \<dots> = tbase_aux stack \<rparr>"

text \<open>
With these definitions, we define functions to convert from spec_state's
sequential and speculative components into tstack predicates.

In particular, spec_pred_of_lvm_pred implements labelled variable names
by mapping these to the appropriate parts of the tstack structure.
\<close>

lift_definition seq_pred_of_vm_pred :: "('r,'v,'a) varmap' pred \<Rightarrow> ('r,'v,'a) tstack pred" is
  "\<lambda>P. {ts \<in> ts_pred_of_vm_pred P. ts_is_seq ts}".

text \<open>
Obtains a sequential relation from a varmap relation. That is, the
global (tstack base) state is related by the given R and
the speculative (tstack upper) state is identity.
\<close>

lift_definition seq_rel_of_vm_rel :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel" is
  "\<lambda>R. {(ts,ts') \<in> ts_rel_of_vm_rel R. tstack_upper ts = tstack_upper ts'}".

locale simasm_rules =
  semantics_spec
    where st = "tlookup :: ('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v"
    and st_upd = tupdate
    and aux = taux
    and aux_upd = tauxupd
  + rules
    where exists_act = "undefined :: ('r,'v,'a) auxopSt"
    and push = "tstack_push :: ('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a option) frame_scheme \<Rightarrow> ('r,'v,'a) tstack"
  + wp_spec
    where rg = rg
    and glb = glb
  for rg :: "('r,'v,'a) varmap' \<Rightarrow> 'local \<Rightarrow> 'v"
  and glb :: "('r,'v,'a) varmap' \<Rightarrow> 'global \<Rightarrow> 'v"

context simasm_rules
begin

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [65,0,0,0,65] 65)
  where "rules_abv R G P c Q \<equiv> rules R G P c Q"

text \<open>
Combine the base frame and the varmap projection into a labelled varmap, along with an invariant
constraining the state to be speculative and fixing the captured variable set.\<close>
lift_definition spec_pred_of_lvm_pred :: "('r,'v,'a) lvarmap' pred \<Rightarrow> 'r set \<Rightarrow> ('r,'v,'a) tstack pred" is
  "\<lambda>P w. {ts | ts. mk_lvarmap (tstack_base ts) (vm_of_ts ts) \<in> P \<and> ts_is_spec ts \<and> w = capped ts}".

text \<open>Constrain the base frame of a stack with a relation\<close>
definition base_rel :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel"
  where "base_rel R \<equiv> {(ts,ts'). (tstack_base ts,tstack_base ts') \<in> R}"

text \<open>Constrain the base frame of a stack with a relation and constrain all subsequent frames with id\<close>
definition base_rel_frame_id :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel"
  where "base_rel_frame_id R \<equiv> {(ts,ts') \<in> base_rel R. tstack_upper ts = tstack_upper ts'}"

definition id_on
  where "id_on w \<equiv> {(m,m'). (\<forall>v \<in> w. varmap_st m v = varmap_st m' v) \<and> varmap_rec.more m = varmap_rec.more m'}"

text \<open>
Constrain the base frame of a stack with a relation and constrain the number of subsequent frames,
but not their contents. Additionally, allow any behaviour in the event that there are not the
expected number of frames.
\<close>
definition base_rel_frame_sz :: "('r,'v,'a) varmap' rel \<Rightarrow> nat \<Rightarrow> 'r set \<Rightarrow> ('r,'v,'a) tstack rel"
  where "base_rel_frame_sz R n w \<equiv> {(ts,ts'). ((ts,ts') \<in> base_rel (R \<inter> id_on w) \<or> tstack_len ts \<noteq> n) \<and> tstack_len ts = tstack_len ts'}"

definition base_rel_frame1 :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel"
  where "base_rel_frame1 R \<equiv> {(ts,ts'). ((ts,ts') \<in> base_rel R \<or> tstack_len ts \<noteq> 1) \<and> tstack_len ts = tstack_len ts'}"

(*
  Guarantee: varmap of one frame down is in G with w fixed
    or just the G itself

*)

definition fixed ::  "('r,'v,'a) varmap' rel \<Rightarrow> 'r set \<Rightarrow> ('r,'v,'a) varmap' rel"
  where "fixed G w \<equiv> {(m, m'\<lparr> varmap_st := \<lambda>v. if v \<in> w then varmap_st m v else varmap_st m' v \<rparr>) | m m'. (m,m') \<in> G}"



definition base_rel_guar :: "('r,'v,'a) varmap' rel \<Rightarrow> 'r set \<Rightarrow> ('r,'v,'a) tstack rel"
  where "base_rel_guar G w \<equiv> {(ts,ts'). (ts,ts') \<in> base_rel G} \<inter> {(ts,ts'). tstack_len ts = tstack_len ts'}"


fun ts_lang_of_vm_lang :: "('r,'v,('r,'v,'a)varmap',('r,'v,'a) lvarmap','a) lang \<Rightarrow> 'r set \<Rightarrow> ('r, 'v, ('r,'v,'a) tstack,('r,'v,'a) tstack, 'a) lang" where
  "ts_lang_of_vm_lang (Skip) w = Skip " |
  "ts_lang_of_vm_lang (Op pred op auxfn) w = Op (ts_pred_of_vm_pred pred) op (auxfn \<circ> vm_of_ts)" |
  "ts_lang_of_vm_lang (SimAsm.lang.Seq a b) w = SimAsm.lang.Seq (ts_lang_of_vm_lang a w) (ts_lang_of_vm_lang b w) " |
  "ts_lang_of_vm_lang (If c t f) w = If c (ts_lang_of_vm_lang t w) (ts_lang_of_vm_lang f w)" |
  "ts_lang_of_vm_lang (While b Imix Ispec c) w = While b (ts_pred_of_vm_pred Imix) (spec_pred_of_lvm_pred Ispec w) (ts_lang_of_vm_lang c w) " |
  "ts_lang_of_vm_lang (DoWhile Imix Ispec c b) w = DoWhile (ts_pred_of_vm_pred Imix) (spec_pred_of_lvm_pred Ispec w) (ts_lang_of_vm_lang c w) b "





text \<open>
The judgement over the sequential program behaviour, structured with:
  \<^item> A state that has no speculation frames
  \<^item> A rely that constrains the base frame, will not modify the stack structure, and enforces id on each frame's contents
  \<^item> A guarantee that preserves stack structure and constrains the base frame, but will
    do anything if there is a speculative frame.
\<close>
abbreviation seq_rule ("_,_ \<turnstile>\<^sub>; _ {_,_,_} _" [20,0,0,0,0,0,20] 20)
  where "seq_rule R G P c r w Q \<equiv>
          (base_rel_frame_id (step\<^sub>t R)), (base_rel_guar (step G) w) \<turnstile>
            (seq_pred_of_vm_pred P) {lift\<^sub>c (ts_lang_of_vm_lang c w) r w} (seq_pred_of_vm_pred Q)"

text \<open>
The judgement over the speculative program behaviour, structured with:
  \<^item> A state with at least one speculative frame
  \<^item> Predicates that constrain the base frame (globally labelled) and the stack projection (unlabelled)
  \<^item> A rely that constrains the base frame, will not modify the stack structure, and enforces id on each frame's contents
  \<^item> A guarantee that preserves stack structure and constrains the base frame, but will
    do anything if there is an incorrect number of speculative frames.
\<close>
abbreviation spec_rule ("_,_ \<turnstile>\<^sub>s _ {_,_,_} _" [20,0,0,0,0,0,20] 20)
  where "spec_rule R G P c r w Q \<equiv>
          (base_rel_frame_id (step\<^sub>t R)), (base_rel_guar G w) \<turnstile>
            (spec_pred_of_lvm_pred P w) {lift\<^sub>c (ts_lang_of_vm_lang c w) r w} (spec_pred_of_lvm_pred Q w)"

text \<open>Combine the above into a single rule\<close>
abbreviation lifted_abv ("_,_,_ \<turnstile> _ {_,_,_} _" [20,0,0,0,0,0,0,20] 20)
  where "lifted_abv R G G' P c r w Q \<equiv> (seq_rule R G [P]\<^sub>; c r w [Q]\<^sub>; \<and> spec_rule R G' [P]\<^sub>s c r w [Q]\<^sub>s)"

text \<open>Define validity in terms of the sequential rule\<close>
abbreviation validity_abv ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0] 45)
  where "validity_abv c P R G Q \<equiv>
    validity (lift\<^sub>c (ts_lang_of_vm_lang c (wr\<^sub>l c)) com.Nil (wr\<^sub>l c)) (seq_pred_of_vm_pred P)
      (base_rel_frame_id (step\<^sub>t R)) (base_rel_guar (step G) (wr\<^sub>l c)) (seq_pred_of_vm_pred Q)"

(*
text \<open>An ordering property on contexts\<close>
definition context_order
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv>
    (stable\<^sub>t R Q \<and> wellformed R G) \<longrightarrow> ((P \<subseteq> Q) \<and> stable\<^sub>t R P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness,
        i.e., wellformedness (of R and G) and guarantee check of c become assumptions for the soundness proof \<close>
definition valid
  ("_,_ \<turnstile>\<^sub>w _ {_,_,_} _" [100,0,0,0,0,0,100] 60)
  where "valid R G P c r w Q \<equiv>
     (wellformed R G \<and> stable\<^sub>t R [Q]\<^sub>; \<and> stable\<^sub>L R [Q]\<^sub>s \<and> guar\<^sub>c c G \<and>
      (\<exists>Q'. (seq_rel_of_vm_rel (step\<^sub>t R)), UNIV \<turnstile> (spec_pred_of_lvm_pred [Q]\<^sub>s) {r} Q'))
        \<longrightarrow> (stable\<^sub>t R [P]\<^sub>; \<and> stable\<^sub>L R [P]\<^sub>s \<and> (R,G \<turnstile>\<^sub>s P {c,r,w} Q))"

*)

subsection \<open>@{type tstack} Projection Lemmas\<close>

lemma vm_of_ts_more_upd [simp]:
  "vm_of_ts y\<lparr>varmap_rec.more := taux y\<rparr> = vm_of_ts y"
  by (auto simp: vm_of_ts_def)

lemma vm_of_ts_in_ts_pred_of_vm_pred[simp]:
  "(x \<in> ts_pred_of_vm_pred P) = (vm_of_ts x \<in> P)"
  unfolding ts_pred_of_vm_pred_def by simp

lemma vm_of_ts_in_seq_pred_of_vm_pred[simp]:
  "(x \<in> seq_pred_of_vm_pred P) = (vm_of_ts x \<in> P \<and> ts_is_seq x)"
  unfolding seq_pred_of_vm_pred_def by simp

lemma vm_of_ts_in_spec_pred_of_vm_pred[simp]:
  "(x \<in> spec_pred_of_lvm_pred P w) = (mk_lvarmap (tstack_base x) (vm_of_ts x) \<in> P \<and> ts_is_spec x \<and> w = capped x)"
  by (auto simp: spec_pred_of_lvm_pred_def)

lemma seq_ts_mono:
  assumes "P \<subseteq> Q"
  shows "seq_pred_of_vm_pred P \<subseteq> ts_pred_of_vm_pred Q"
  using assms by auto

lemma seq_mono:
  assumes "P \<subseteq> Q"
  shows "seq_pred_of_vm_pred P \<subseteq> seq_pred_of_vm_pred Q"
  using assms by auto

lemma spec_mono:
  assumes "P \<subseteq> Q"
  shows "spec_pred_of_lvm_pred P w \<subseteq> spec_pred_of_lvm_pred Q w"
  using assms by (auto simp: ul_lift_pred_def vm_of_ts_def)

lemma spec_ts_mono:
  assumes "P \<subseteq> Q\<^sup>L"
  shows "spec_pred_of_lvm_pred P w \<subseteq> ts_pred_of_vm_pred Q"
  using assms by (auto simp: ul_lift_pred_def vm_of_ts_def)

subsection \<open>@{term tstack_base} Lemmas\<close>

lemma tstack_base_auxupd_id [simp]:
  "tstack_base (tauxupd y f) = (if tstack_len y = 1 then (tstack_base y)\<lparr> varmap_rec.more := f y \<rparr> else tstack_base y)"
  unfolding tstack_base_def by auto

lemma tstack_base_vm_of_ts [simp]:
  "tstack_len y = 1 \<Longrightarrow> tstack_base y = vm_of_ts y"
  unfolding tstack_base_def vm_of_ts_def by auto

lemma tstack_base_tupdate [simp]:
  "tstack_base (tupdate y x e) = (if tcaptured y x then tstack_base y
                                  else (tstack_base y)\<lparr> varmap_st := (varmap_st (tstack_base y))(x := e) \<rparr>)"
  unfolding tstack_base_def by auto

lemma tstack_base_tpush [simp]:
  "tstack_base (tstack_push m s) = tstack_base m"
  unfolding tstack_base_def by simp

subsection \<open>Relational @{type tstack} Projection Lemmas\<close>

lemma stable\<^sub>L [intro]:
  assumes "stable\<^sub>L R P"
  shows "stable (base_rel_frame_id (step\<^sub>t R)) (spec_pred_of_lvm_pred P w)"
  sorry (* Problem 1: Stability in the speculative context doesn't make sense *)

lemma stable_ts [intro]:
  "stable R P \<Longrightarrow> stable (base_rel_frame_id R) (seq_pred_of_vm_pred P)"
  apply (auto simp: stable_def base_rel_frame_id_def base_rel_def )
  apply (metis One_nat_def tstack_base_vm_of_ts tstack_upper_len_eq)
  apply (metis tstack_upper_len_eq)
  done

lemma base_rel_frame_szI1:
  assumes "tstack_len a = 1 \<Longrightarrow> (tstack_base a, tstack_base b) \<in> G" "tstack_len a = tstack_len b"
  shows "(a,b) \<in> base_rel_frame1 G"
  using assms unfolding base_rel_frame1_def base_rel_def
  by auto

lemma base_rel_frame_szI:
  assumes "tstack_len a = n \<Longrightarrow> (tstack_base a, tstack_base b) \<in> G \<inter> id_on w" "tstack_len a = tstack_len b"
  shows "(a,b) \<in> base_rel_frame_sz G n w"
  using assms unfolding base_rel_frame_sz_def base_rel_def
  by auto

lemma base_rel_guarI:
  assumes "(tstack_base a, tstack_base b) \<in> G"
  assumes "tstack_len a = tstack_len b"
  shows "(a,b) \<in> base_rel_guar G n"
  using assms unfolding base_rel_guar_def base_rel_def
  by auto

lemma [elim!]:
  assumes "(tstack_push m s, tstack_push ma sa) \<in> base_rel G"
  obtains "(m, ma) \<in> base_rel G"
  using assms unfolding base_rel_def by auto

lemma [intro]:
  assumes "tstack_upper m = tstack_upper m'"
  shows "tstack_upper (tstack_push m s) = tstack_upper (tstack_push m' s)"
  using assms unfolding tstack_upper_def by transfer auto

lemma [simp]:
  "tstack_len m = 1 \<Longrightarrow> tstack_upper m = []"
  unfolding tstack_upper_def by transfer (case_tac m; simp)

lemma compat_example:
  assumes "G \<subseteq> R"
  shows "base_rel_frame1 G \<subseteq> guard {t. tstack_len t = 1} (base_rel_frame_id R)"
  using assms by (auto simp: base_rel_frame1_def base_rel_frame_id_def base_rel_def guard_def)

subsection \<open>@{term st_beh\<^sub>i} Invariants\<close>

lemma st_beh\<^sub>i_tstack_len [simp]:
  assumes "(x, y) \<in> st_beh\<^sub>i op"
  shows "tstack_len x = tstack_len y"
  using assms by (cases op; auto)

lemma st_beh\<^sub>i_capped [simp]:
  assumes "(x, y) \<in> st_beh\<^sub>i op"
  shows "capped x = capped y"
  using assms by (cases op; auto)

subsection \<open>Atomic Judgements\<close>

text \<open>A method to force equivalence over two large state computations, useful when the rewrite engine gives up\<close>
method force_eq =
  (match conclusion in "x \<in> Q" for x Q \<Rightarrow>
     \<open>match premises in A: "y \<in> Q" for y \<Rightarrow>
      \<open>rule subst[of _ _ "\<lambda>m. m \<in> Q", OF _ A]\<close>\<close>) |
  (match conclusion in "(x :: ('x, 'y, 'z) varmap_rec_scheme) = y" for x y \<Rightarrow>
     \<open>rule varmap_rec.equality; simp?\<close>) |
  (match conclusion in "(x :: 'x \<Rightarrow> 'y) = y" for x y \<Rightarrow>
     \<open>(clarsimp simp: fun_eq_iff split: label.splits)\<close>) |
  (match conclusion in "f (a :: ('r, 'v, 'a) varmap_rec_scheme) = f b" for f a b \<Rightarrow>
    \<open>rule arg_cong[where ?f=f]\<close>)

lemma [simp]:                  
  "tstack_len x = Suc 0 \<Longrightarrow> tcaptured x v = False"
  proof (transfer, goal_cases)
    case (1 x v)
    thus ?case by (cases x) (auto simp: captured_def)
  qed
  

lemma atomic_seq:
  assumes r: "wellformed R G"
  assumes g: "(v \<subseteq> guar (wp\<^sub>i op o wp\<^sub>a f) (step G))"
  assumes s: "stable (step\<^sub>t R) Q"
  shows "R,G \<turnstile>\<^sub>; stabilize R (v \<inter> wp\<^sub>i op (wp\<^sub>a f Q)) {Op v op f,r,w} Q"
  unfolding ts_lang_of_vm_lang.simps lift\<^sub>c.simps
proof (intro basic atomicI, goal_cases st gu spre spost)
  case st
  let ?lhs = "seq_pred_of_vm_pred (stabilize R (v \<inter> wp\<^sub>i op (wp\<^sub>a f Q)))"
  have vc: "?lhs \<subseteq> vc (lift\<^sub>b (ts_pred_of_vm_pred v) op (f \<circ> vm_of_ts))"
    using r by (cases op) (auto elim: stabilizeE intro!: seq_ts_mono simp: liftg_def)
  have wp: "?lhs \<subseteq> {m. \<forall>m'. (m, m') \<in> beh (lift\<^sub>b (ts_pred_of_vm_pred v) op (f \<circ> vm_of_ts)) \<longrightarrow>
                      vm_of_ts m' \<in> Q \<and> ts_is_seq m'}"
    using r by (cases op) (auto elim!: stabilizeE simp: liftg_def wp\<^sub>a.simps)
  show ?case using vc wp by (auto simp: State.wp_def)
next
  case gu
  thus ?case using g r apply (cases op)
        apply (auto intro!: base_rel_guarI simp: wp\<^sub>a.simps guar_def wp\<^sub>r_def liftg_def split: if_splits)
       apply force
    apply force
     apply force

    sorry
next
  case spre
  thus ?case using r by blast
next
  case spost
  thus ?case using s by blast
qed

lemma atomic_spec:
  assumes r: "reflexive R" "transitive R" "reflexive G"
  assumes s: "stable\<^sub>L R Q"
  assumes w: "wr op \<subseteq> w" "lk op \<inter> w = {}"
  shows "R,G \<turnstile>\<^sub>s (stabilize\<^sub>L R (v\<^sup>L \<inter> wp\<^sub>i\<^sub>s op (wp\<^sub>a (f \<circ> ul_restrict) Q))) {Op v op f,r,w} Q"
  unfolding ts_lang_of_vm_lang.simps lift\<^sub>c.simps
proof (intro basic impI allI conjI atomicI, goal_cases st gu spre spost)
  case st
  let ?lhs = "spec_pred_of_lvm_pred (stabilize\<^sub>L R (v\<^sup>L \<inter> wp\<^sub>i\<^sub>s op (wp\<^sub>a (f \<circ> ul_restrict) Q))) w"
  have vc: "?lhs \<subseteq> vc (lift\<^sub>b (ts_pred_of_vm_pred v) op (f \<circ> vm_of_ts))"
    using r w by (cases op) (auto elim: stabilize\<^sub>LE intro!: spec_ts_mono simp: liftg_def)
  have wp: "?lhs \<subseteq> {m. \<forall>m'. (m, m') \<in> beh (lift\<^sub>b (ts_pred_of_vm_pred v) op (f \<circ> vm_of_ts)) \<longrightarrow>
                mk_lvarmap (tstack_base m') (vm_of_ts m') \<in> Q \<and> ts_is_spec m' \<and> w = capped m'}"
    using r w by (cases op; auto elim!: stabilize\<^sub>LE simp: wp\<^sub>a.simps liftg_def) force_eq+
  show ?case using vc inv wp by (auto simp: State.wp_def)
next
  case gu
  then show ?case using r w apply (cases op)
        apply  (auto intro!:  base_rel_guarI simp: wp\<^sub>a.simps guar_def liftg_def wp\<^sub>r_def)

    sorry (* Problem 2: Need a guarantee / vc combo that works for leak *)
next
  case spre
  thus ?case using r by blast
next
  case spost
  then show ?case using s by blast
qed

lemma cmp_seq:
  assumes r: "wellformed R anything" "reflexive G"
  assumes s: "stable\<^sub>t R Q"
  shows "base_rel_frame_id (step\<^sub>t R),base_rel_guar G w \<turnstile>
          seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (cmp b) Q)) {Basic (liftl (cmp b))} seq_pred_of_vm_pred Q"
  unfolding ts_lang_of_vm_lang.simps lift\<^sub>c.simps liftl_def
proof (intro basic conjI atomicI, goal_cases st gu  spre spost )
  case st
  thus ?case using r by (auto simp: State.wp_def elim!: stabilizeE)
next
  case gu
  thus ?case using r by (auto intro!: base_rel_guarI  simp: guar_def reflexive_def step_def)
next
  case spre
  thus ?case using r by blast
next
  case spost
  thus ?case using s by blast
qed

lemma cmp_spec:
  assumes r: "wellformed R anything" "reflexive G'"
  assumes s: "stable\<^sub>L R Q"
  assumes d: "d > 1"
  shows "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile>
          spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) Q)) w {Basic (liftl (cmp b))} spec_pred_of_lvm_pred Q w"
  unfolding ts_lang_of_vm_lang.simps lift\<^sub>c.simps liftl_def
proof (intro basic conjI atomicI, goal_cases st gu  spre spost )
  case st
  thus ?case using r by (auto simp: wp_def State.wp_def elim!: stabilize\<^sub>LE)
next
  case gu
  thus ?case using r d by (auto intro!: base_rel_guarI  simp: guar_def reflexive_def step_def id_on_def)
next
  case spre
  thus ?case using r by blast
next
  case spost
  thus ?case using s by blast
qed


lemma basic_wp:
  assumes r: "wellformed R G" "reflexive G'"
  assumes g: "(v \<subseteq> guar (wp\<^sub>i op o wp\<^sub>a f) (step G))"
  assumes s: "stable (step\<^sub>t R) [Q]\<^sub>;" "stable\<^sub>L R [Q]\<^sub>s"
  assumes w: "wr op \<subseteq> s" "lk op \<inter> s = {}"

  shows "R,G,G' \<turnstile> (wp R (Op v op f) Q) {Op v op f,r,s} Q"
proof ((intro conjI; simp), goal_cases seq spec)
  case seq
  then show ?case using atomic_seq[OF r(1) g s(1)] by (cases Q, simp)
next
  case spec
  then show ?case using atomic_spec[OF _ _ _ s(2) w] r
    by (cases Q, simp)
qed

subsection \<open>Frame Reasoning\<close>

lemma base_rel_frame_sz_pushE:
  assumes "(tstack_push m s, b) \<in> base_rel_frame_sz G (Suc (Suc 0)) w"
  obtains m' s' where "b = tstack_push m' s'" "(m,m') \<in> base_rel_frame_sz G 1 w"
  using assms
proof -
  have "tstack_len (tstack_push m s) = tstack_len b" using assms by (auto simp: base_rel_frame_sz_def)
  hence "tstack_len b \<noteq> 1" by auto
  then obtain m' s where b: "b = tstack_push m' s" using is_spec_push by blast
  hence "(m,m') \<in> base_rel_frame_sz G 1 w"
    using assms unfolding base_rel_frame_sz_def base_rel_def guard_def by auto
  thus ?thesis using b that by auto
qed


lemma base_rel_guarE:
  assumes "(tstack_push m s, b) \<in> base_rel_guar G w"
  obtains m' s' where "b = tstack_push m' s'" "(m,m') \<in> base_rel_guar G n"
  using assms
proof -
  have "tstack_len (tstack_push m s) = tstack_len b" using assms by (auto simp: base_rel_guar_def)
  hence "tstack_len b \<noteq> 1" by auto
  then obtain m' s where b: "b = tstack_push m' s" using is_spec_push by blast
  hence "(m,m') \<in> base_rel_guar G n" using assms unfolding base_rel_guar_def base_rel_def by auto
  thus ?thesis using b that by auto
qed


lemma mem_restrict:
  assumes "P \<subseteq> P'\<^sup>U"
  assumes "m \<in> P"
  shows "mk_lvarmap m m \<in> P'"
proof -
  obtain x where x: "\<forall>v. varmap_st x (Gl v) = varmap_st x (Ul v)" "x \<in> P'"
                 "m = \<lparr>varmap_st = \<lambda>v. varmap_st x (Ul v), \<dots> = varmap_rec.more x\<rparr>"
    using assms by (auto simp: restrict_pred_def image_def)
  have "x = mk_lvarmap m m"
    by (auto intro: varmap_rec.equality simp: x fun_eq_iff split: label.splits)
  thus ?thesis using x by auto
qed

text \<open>
Lower a speculative judgement across the introduction of an empty frame.
\<close>
lemma spec_to_seq:
  assumes "base_rel_frame_id R, base_rel_guar G w \<turnstile>
            (spec_pred_of_lvm_pred P' w) {r} (spec_pred_of_lvm_pred Q w)"
  assumes "P \<subseteq> P'\<^sup>U"
  shows "pushrelSame (base_rel_frame_id R),pushrelAll (base_rel_guar G w') \<turnstile>
          pushpred (emptyFrame w) (seq_pred_of_vm_pred P) {r} pushpredAll UNIV"
  using assms(1)
proof (rule conseq, goal_cases pre rely guar post)
  case pre
  have "\<forall>m. vm_of_ts m \<in> P \<longrightarrow> capped m \<subseteq> w" sorry (* Problem 3: not sure what to do about these sets *)
  then show ?case unfolding pushpred_def using mem_restrict[OF assms(2)] by force
next
  case rely
  then show ?case unfolding pushrelSame_def base_rel_frame_id_def base_rel_def by auto
next
  case guar
  show ?case by (auto simp: pushrelAll_def elim!: base_rel_guarE) fast
next
  case post
  then show ?case by (auto intro: is_spec_push simp: pushpredAll_def mk_lvarmap_def)
qed

lemma spec_to_spec:
  assumes "base_rel_frame_id R, base_rel_guar G w \<turnstile>
            (spec_pred_of_lvm_pred P' w) {r} (spec_pred_of_lvm_pred Q w)"
  assumes "P \<subseteq> P'"
  shows "pushrelSame (base_rel_frame_id R),pushrelAll (base_rel_guar G w) \<turnstile>
          pushpred (emptyFrame w) (spec_pred_of_lvm_pred P w) {r} pushpredAll UNIV"
  using assms(1)
proof (rule conseq, goal_cases pre rely guar post)
  case pre
  then show ?case unfolding pushpred_def using assms(2) by auto
next
  case rely
  then show ?case unfolding pushrelSame_def base_rel_frame_id_def base_rel_def by auto
next
  case guar
  show ?case apply (auto simp: pushrelAll_def elim!: base_rel_guarE) by fastforce
next
  case post
  then show ?case by (auto intro: is_spec_push simp: pushpredAll_def mk_lvarmap_def)
qed


lemma stable_conseqI' [intro]:
  assumes "stable R' P" "Id_on P O R \<subseteq> R'"
  shows "stable R P"
  using assms rtrancl_mono unfolding stable_def by blast

lemma spec_judgement:
  assumes spec: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile> spec_pred_of_lvm_pred P' w {r} spec_pred_of_lvm_pred Q' w"
  assumes wf: "G' \<subseteq> step G \<inter> step\<^sub>t R"
  assumes pred: "P \<subseteq> Q" "P \<subseteq> P'\<^sup>U"
  assumes st: "stable\<^sub>t R Q"

  shows "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> seq_pred_of_vm_pred P {\<triangle> Capture (emptyFrame w) r} seq_pred_of_vm_pred Q"
proof -
  text \<open>Speculative behaviour is stronger than the concrete guarantee\<close>
  have u: "base_rel_guar G' w \<subseteq> base_rel_guar (step G) w"
    using wf by (auto simp: base_rel_guar_def base_rel_def)

  text \<open>Speculative behaviour is stronger than the concrete rely, given initial state is not speculative\<close>
  have m: "\<And>P. Id_on (seq_pred_of_vm_pred P) O base_rel_guar G' w \<subseteq> base_rel_frame_id (step\<^sub>t R)"
    using wf by (auto simp: base_rel_guar_def base_rel_def base_rel_frame_id_def)

  have st: "stable (base_rel_frame_id (step\<^sub>t R)) (seq_pred_of_vm_pred Q)"
    using st by blast

  have "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile>
      seq_pred_of_vm_pred P {\<triangle> Capture (emptyFrame w) r} seq_pred_of_vm_pred Q"
  proof (rule interr)
    show "seq_pred_of_vm_pred P \<subseteq> seq_pred_of_vm_pred Q" using pred spec_mono by force
  next
    show "stable (base_rel_frame_id (step\<^sub>t R)) (seq_pred_of_vm_pred Q)" using st by blast
  next
    show "stable (base_rel_guar G' w) (seq_pred_of_vm_pred Q)" using st m
      by (rule stable_conseqI')
  next
    show "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile>
            seq_pred_of_vm_pred P {Capture (emptyFrame w) r} UNIV"
      using spec pred(2) by (rule capture[OF spec_to_seq])
  qed

  thus ?thesis using u by blast
qed

lemma spec_judgement':
  assumes spec: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile> spec_pred_of_lvm_pred P' w {r} spec_pred_of_lvm_pred Q' w"
  assumes wf: "G' \<subseteq> step G \<inter> step\<^sub>t R"
  assumes pred: "P \<subseteq> Q" "P \<subseteq> P'"
  assumes st: "stable\<^sub>L R Q"

  shows "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile> spec_pred_of_lvm_pred P w {\<triangle> Capture (emptyFrame w) r} spec_pred_of_lvm_pred Q w"
proof -
  text \<open>Speculative behaviour is stronger than the concrete guarantee\<close>
  have u: "base_rel_guar G' w \<subseteq> base_rel_guar (step G) w"
    using wf by (auto simp: base_rel_guar_def base_rel_def)

  text \<open>Speculative behaviour is stronger than the concrete rely, given initial state is not speculative\<close>
  have m: "\<And>P. Id_on (spec_pred_of_lvm_pred P w) O base_rel_guar G' w \<subseteq> base_rel_frame_id (step\<^sub>t R)"
    using wf apply (auto simp: base_rel_guar_def base_rel_def base_rel_frame_id_def)
    sorry

  have st: "stable (base_rel_frame_id (step\<^sub>t R)) (spec_pred_of_lvm_pred Q w)"
    using st by blast

  have "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile>
      spec_pred_of_lvm_pred P w {\<triangle> Capture (emptyFrame w) r} spec_pred_of_lvm_pred Q w"
  proof (rule interr)
    show "spec_pred_of_lvm_pred P w \<subseteq> spec_pred_of_lvm_pred Q w" using pred spec_mono by force
  next
    show "stable (base_rel_frame_id (step\<^sub>t R)) (spec_pred_of_lvm_pred Q w)" using st by blast
  next
    show "stable (base_rel_guar G' w) (spec_pred_of_lvm_pred Q w)" using st m by blast
  next
    show "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile>
            spec_pred_of_lvm_pred P w {Capture (emptyFrame w) r} UNIV"
      using spec pred(2) by (rule capture[OF spec_to_spec])
  qed

  thus ?thesis using u by auto
qed

(*

definition stabilize\<^sub>s where
  "stabilize\<^sub>s R P \<equiv> {m. \<forall>m'. (glb (gl_restrict m),glb m') \<in> R \<longrightarrow> rg (gl_restrict m) = rg m' \<longrightarrow> m' \<in> [P]\<^sub>;}"



section \<open>Soundness\<close>


lemma h2:
  assumes "(s,s') \<in> beh\<^sub>a auxop"
  shows "tstack_len s = tstack_len s'"
  sorry

lemma h1:
  assumes "P \<subseteq>\<^sub>s (stabilize\<^sub>L R (c\<^sup>L \<inter> wp\<^sub>i\<^sub>s \<alpha> (wp\<^sub>a (f \<circ> gl_restrict) [Q]\<^sub>s)),
                                stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f [Q]\<^sub>;)))"
          "wellformed R G" "stable\<^sub>t R [Q]\<^sub>;"
  assumes "vm_of_ts x \<in> [P]\<^sub>;"
  shows "x \<in> State.wp {s. vm_of_ts s \<in> c \<and> ts_is_seq s} {(s, s'). (s, s') \<in> st_beh\<^sub>i \<alpha> O {(t, t'). t' = tauxupd t (f \<circ> vm_of_ts)} \<and> ts_is_seq s \<and> ts_is_seq s'} (seq_pred_of_vm_pred [Q]\<^sub>;)"
sorry


lemma conseq_s:
  assumes "R,G \<turnstile>\<^sub>s P {op} Q"
  assumes "P' \<subseteq>\<^sub>s P"
  shows "R,G \<turnstile>\<^sub>s P' {op} Q"
  using assms seq_pred_of_vm_pred_subset
  apply auto
  apply (rule conseq)
  apply simp_all
  apply (intro spec_pred_of_lvm_pred_subset seq_pred_of_vm_pred_subset)
  by auto

(*
lemma h3:
  "ts_is_seq x \<Longrightarrow> vm_of_ts x \<in> wp\<^sub>a f Q \<Longrightarrow> tauxupd x (f \<circ> vm_of_ts) \<in> seq_pred_of_vm_pred Q"
  unfolding seq_pred_of_vm_pred_def
  by (simp add: vm_of_ts_auxupd wp.wp\<^sub>a.simps ts_is_seq_def, insert tauxupd_len[of x], simp)

lemma basic_wp\<^sub>i_1_assign:
  fixes xa x11 x12 f
  defines "rhs \<equiv> (tauxupd (tupdate xa x11 (ev\<^sub>E (tlookup xa) x12)) (f \<circ> vm_of_ts))"
  assumes "vm_of_ts xa\<lparr>varmap_st := (varmap_st (vm_of_ts xa))(x11 := ev\<^sub>E (varmap_st (vm_of_ts xa)) x12)\<rparr> \<in> wp\<^sub>a f Qseq"
  assumes "ts_is_seq xa"
  shows
    "rhs \<in> seq_pred_of_vm_pred Qseq"
    "ts_is_seq rhs"
proof -
  show "rhs \<in> seq_pred_of_vm_pred Qseq"
    unfolding rhs_def
    using assms(2) unfolding wp\<^sub>a.simps seq_pred_of_vm_pred_def
    apply auto
    apply (metis varmap_rec.select_convs(1) vm_of_ts.abs_eq vm_of_ts_bothupd)
    by (metis assms(3) tauxupd_len ts_is_seq_def tupdate_len)
  show "ts_is_seq rhs"
    unfolding rhs_def using assms(3) unfolding ts_is_seq_def using tupdate_len tauxupd_len by metis
qed *)

lemma basic_wp\<^sub>i_1_assign_spec:
  assumes "\<alpha> = assign x11 x12"
  assumes "ts_is_spec x"
  assumes "x \<in> spec_pred_of_lvm_pred (wp\<^sub>i\<^sub>s \<alpha> (wp\<^sub>a (f \<circ> gl_restrict) Qspec))"
  shows "tauxupd (tupdate x x11 (ev\<^sub>E (tlookup x) x12)) (f \<circ> vm_of_ts) \<in> spec_pred_of_lvm_pred Qspec" (is "?ts \<in> \<dots>")
    "ts_is_spec (tauxupd (tupdate x x11 (ev\<^sub>E (tlookup x) x12)) (f \<circ> vm_of_ts))"
using assms
unfolding spec_pred_of_lvm_pred_def
proof (clarsimp simp add: id_def, goal_cases)
  (* DELETED *)
qed

 *)


(*

text \<open>Basic Rule for operations with vc c\<close>
lemma basic_wp\<^sub>i_1:
  assumes "P \<subseteq>\<^sub>s (stabilize\<^sub>L R (c\<^sup>L \<inter> wp\<^sub>i\<^sub>s \<alpha> (wp\<^sub>a (f \<circ> gl_restrict) [Q]\<^sub>s)),
                 stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f [Q]\<^sub>;)))"
          "wellformed R G" "stable\<^sub>t R [Q]\<^sub>;"
  assumes "c \<subseteq> guar (wp\<^sub>i \<alpha> o wp\<^sub>a f) (step G)"
  shows "R,G \<turnstile>\<^sub>s P {Op (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)} Q"
proof -
  (* DELETED *)
qed

text \<open>Basic Rule for operations without vc\<close>
lemma basic_wp\<^sub>i_2:
  assumes "P \<subseteq>\<^sub>s (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s \<alpha>[Q]\<^sub>s), stabilize R (wp\<^sub>i \<alpha> [Q]\<^sub>;))"
          "wellformed R G" "stable\<^sub>t R [Q]\<^sub>;"
  assumes "\<forall>m. m \<in> guar (wp\<^sub>i \<alpha>) (step G)"
  shows "R,G \<turnstile>\<^sub>s P {Op UNIV \<alpha> taux} Q"
  sorry (*
proof -
  have x: "vm_of_ts x \<in> wp\<^sub>i \<alpha> Q" if "x \<in> ts_pred_of_vm_pred (stabilize R (wp\<^sub>i \<alpha> Q))" for x
    using assms(1,2) stabilizeE using that vm_of_ts_in_ts_pred_of_vm_pred by blast
  have 1: "ts_rel_of_vm_rel (step\<^sub>t R),ts_rel_of_vm_rel(step G) \<turnstile>\<^sub>A ts_pred_of_vm_pred(stabilize R (wp\<^sub>i \<alpha> Q)) {(liftg UNIV \<alpha> taux)} ts_pred_of_vm_pred Q"
  proof (rule atomicI, goal_cases)
    case 1
    have "x \<in> wp\<^sub>\<alpha> (liftg UNIV \<alpha> taux) (ts_pred_of_vm_pred Q)" if "x \<in> ts_pred_of_vm_pred (stabilize R (wp\<^sub>i \<alpha> Q))" for x
    using x[of x, OF that] vm_of_ts_wp_liftg[where ?c = UNIV and ?f = varmap_rec.more]
    unfolding liftg_def wp_def by simp
    thus ?case by auto
  next
    case 2
    hence univ: "UNIV \<subseteq> local.guar (wp\<^sub>i \<alpha> \<circ> wp\<^sub>a varmap_rec.more) (step G)" using assms(4) by auto
    have "guar\<^sub>\<alpha> (liftg (ts_pred_of_vm_pred UNIV) \<alpha> taux) (ts_rel_of_vm_rel (step G))"
    using guar_of_liftg[where ?c = UNIV and ?f = varmap_rec.more, OF univ]
    unfolding taux_def comp_def by auto
    then show ?case by simp
  next
    case 3
    then show ?case using assms(2) by auto
  next
    case 4
    then show ?case using assms(3) by auto
  qed
  then have "R,G \<turnstile>\<^sub>s stabilize R (wp\<^sub>i \<alpha> Q) {Op UNIV \<alpha> taux} Q"
    by simp (rule rules.basic)
  thus ?thesis using assms(1) conseq
  by (simp add: ts_pred_of_vm_pred.rep_eq vimage_mono)
qed
  oops *)

lemma lift_wp:
  assumes "P \<subseteq> wp\<^sub>\<alpha> (c,vm_pred_of_ts_pred V,vm_rel_of_ts_rel (beh\<^sub>a R)) Q"
  shows "seq_pred_of_vm_pred P \<subseteq> wp\<^sub>\<alpha> (c,V,beh\<^sub>a R) (seq_pred_of_vm_pred Q)"
  using assms unfolding seq_pred_of_vm_pred_def wp_def vm_pred_of_ts_pred_def vm_rel_of_ts_rel_def
  apply auto
  sorry

text \<open>A rule for cmp operations, used for If/While\<close>
lemma cmp_sound [intro!]:
  assumes "wellformed R G" "stable\<^sub>t R [Q]\<^sub>;"
  assumes "P \<subseteq>\<^sub>s (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [Q]\<^sub>s), stabilize R (wp\<^sub>i (cmp b) [Q]\<^sub>;))" (is "P \<subseteq>\<^sub>s ?P")
  shows "R,G \<turnstile>\<^sub>s P {Op UNIV (cmp b) varmap_rec.more} Q"
proof -
  have "R,G \<turnstile>\<^sub>s ?P {Op UNIV (cmp b) varmap_rec.more} Q"
  proof (intro conjI, goal_cases seq spec)
    case seq

    then show ?case
      apply (simp add: liftg_def del: beh\<^sub>a.simps)
      apply (rule basic)
      apply (rule atomicI)
      apply (rule lift_wp)

      apply auto

      apply (auto simp: wp_def liftg_def guar_def)[2]

    sorry
next
  case spec
  then show ?case sorry
qed


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
  "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q \<Longrightarrow>
  R,G \<turnstile>\<^sub>w stabilize R ((wp\<^sub>s (vm_lang_of_ts_lang (If b c\<^sub>1 c\<^sub>2)) (Q\<^sup>G))\<^sup>U) {If b c\<^sub>1 c\<^sub>2} UNIV \<Longrightarrow>
  P \<subseteq> (wp\<^sub>i (cmp b) P\<^sub>1 \<inter> wp\<^sub>i (ncmp b) P\<^sub>2) \<Longrightarrow>
            R,G \<turnstile>\<^sub>w stabilize R P {If b c\<^sub>1 c\<^sub>2} Q"
  unfolding valid_def
sorry

text \<open>While Rule\<close>
lemma while_wp:
  assumes "R,G \<turnstile>\<^sub>w P {c} stabilize R J" (is "R,G \<turnstile>\<^sub>w P {c} ?I")
  assumes "J \<subseteq> (wp\<^sub>i (cmp b) P \<inter> wp\<^sub>i (ncmp b) Q)"
  shows "R,G \<turnstile>\<^sub>w ?I {While b Imix Ispec c} Q"
  unfolding valid_def lift\<^sub>c.simps
proof (intro impI conjI rules.choice rules.seq)
  assume "wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (While b Imix Ispec c) (G)"
  thus "step\<^sub>t R,step G \<turnstile> ?I {(Seqw (Basic (liftl (cmp b))) (lift\<^sub>c c))*} ?I"
    using assms
    apply (intro rules.loop rules.seq, unfold valid_def)
    apply force
     apply force
    apply (rule cmp_sound)
      apply blast
     apply (auto simp:)
    using stabilize_entail by blast
qed (insert assms, auto, rule stabilize_entail)


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
  assumes "P = ({}, {})"
  shows "R,G \<turnstile>\<^sub>w P {c} Q"
  using assms unfolding valid_def
  by (intro conjI impI rules.conseq[OF falseI, where ?G="step G"]) (auto)


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


*)
section \<open>kait lemmas\<close>

lemma y: "stabilize R Q \<subseteq> (stabilize\<^sub>L R Qs)[y\<phi> sub y]" if Q: "Q \<subseteq> Qs[y\<phi> sub y]" "reflexive R" "transitive R" for Q Qs R
proof (standard; goal_cases)
  case (1 x) (* x is stabilized non-spec state *)
  note stabilized = 1
  have xQ: "x \<in> Q" using "local.1" that stabilizeE by blast
  have xQs: "x \<in> Qs[y\<phi> sub y]" using xQ that by auto
  (* argue that x \<in> Qs[y\<phi> sub y] and also that its stability translates to stability\<^sub>L.*)
  then show ?case unfolding restrict_pred_def2
  apply simp
  apply standard
  proof (goal_cases)
    let ?s2 = "x\<^sup>G\<^sup>L"

    case 1
    then show "x = \<lparr>varmap_st = \<lambda>v. varmap_st ?s2 (Gl v), \<dots> = varmap_rec.more ?s2\<rparr> \<and>
      (\<forall>v. varmap_st ?s2 (Gl v) = varmap_st ?s2 (Ul v))"
    by (intro conjI) (auto simp  add: glul_lift_pred_def)
  next
    case 2
    note varmap_eta = varmap_rec.surjective[symmetric]
    from 2 show "x\<^sup>G\<^sup>L \<in> stabilize\<^sub>L R Qs"
    unfolding glul_lift_pred_def
    unfolding stabilize\<^sub>L_def
    apply simp
    apply (intro allI impI)
    proof goal_cases
    case (1 m') (* m' is spec state after environment step *)
      have x_m': "x = ul_restrict m'" by (simp add: "local.1"(4))
      have x_m'2: "varmap_st x v = varmap_st m' (Ul v)" for v using x_m' by simp

      have in_Q: "m' \<in> Q" if "(glb x, glb m') \<in> R" "rg x = rg m'" for m'
        using stabilized that unfolding stabilize_def by simp

      have ul: "ul_restrict m' \<in> Q" using x_m' stabilized stabilizeE xQ by simp
      have gl: "gl_restrict m' \<in> Q" using 1 in_Q by auto
      have "x\<^sup>G\<^sup>L \<in> Qs" unfolding glul_lift_pred_def using 2 by (metis lvarmap_eqI unlabel.simps varmap_rec.select_convs)

      have "x\<^sup>G\<^sup>L = m'"
      proof (rule lvarmap_rgglb_eqI, goal_cases rg_gl rg_ul glb_gl glb_ul more)
        case rg_gl
        then show ?case by (metis "local.1"(3) gl_restrict.simps gl_restrict_of_glul varmap_rec.surjective)
      next
        case rg_ul
        then show ?case by (metis ul_restrict_of_glul x_m')
      next
        case glb_gl
        then show ?case unfolding glul_lift_pred_def
          apply simp using 1 unfolding varmap_eta gl_restrict.simps[symmetric] ul_restrict.simps[symmetric]
            using gl rgglb_injective that unfolding transitive_def sorry (* we cannot really say anything about the true values of global registers *)
      next
        case glb_ul then show ?case using ul_restrict_of_glul x_m' by (simp add: glul_lift_pred_def)
      next
        case more then show ?case by (simp add: "local.1"(4) glul_lift_pred_def)
      qed
      then show ?case using \<open>x\<^sup>G\<^sup>L \<in> Qs\<close> gl using 1 unfolding varmap_eta gl_restrict.simps[symmetric] ul_restrict.simps[symmetric] by simp
    qed
  qed
qed

lemma z: "a \<in> wp\<^sub>i x2 Q \<Longrightarrow> a \<in> (wp\<^sub>i\<^sub>s x2 Qs)[y\<phi> sub y]" if "Q \<subseteq> Qs[y\<phi> sub y]" for x2 Q Qs a
unfolding restrict_pred_def2
proof (simp, standard)
  define a' where "a' \<equiv> a\<^sup>G\<^sup>L"
  assume assm: "a \<in> wp\<^sub>i x2 Q" 
  show "a = \<lparr>varmap_st = \<lambda>v. varmap_st a' (Gl v), \<dots> = varmap_rec.more a'\<rparr> \<and> (\<forall>v. varmap_st a' (Gl v) = varmap_st a' (Ul v))"
    unfolding a'_def glul_lift_pred_def by auto
  hence a: "a = \<lparr>varmap_st = \<lambda>v. varmap_st a' (Gl v), \<dots> = varmap_rec.more a'\<rparr>" by auto

  (* note assm2 = that *)
  (* obtain s2  *)
    (* where "s2\<in>Qs" "a = \<lparr>varmap_st = \<lambda>v. varmap_st s2 (Gl v), \<dots> = varmap_rec.more s2\<rparr>" "(\<And>v. varmap_st s2 (Gl v) = varmap_st s2 (Ul v))" *)
  (* using assm assm2 apply auto sledgehammer *)

  show "a\<^sup>G\<^sup>L \<in> wp\<^sub>i\<^sub>s x2 Qs"
  proof (cases x2)
    have q[simp]: "Gl (unlabel (Ul x)) = Gl x" for x by simp
    have w[simp]: "varmap_st \<lparr>varmap_st = f, \<dots> = varmap_rec.more a\<rparr> x = f x" for x f by simp
    have e[simp]: "unlabel (Gl x) = x" for x by simp

    case (assign x11 x12)
    thm restrict_pred_def2
    then show ?thesis sorry
  next
    case (cmp x2)
    then show ?thesis   
    using that unfolding restrict_pred_def2 glul_lift_pred_def
    by (simp add: comp_def, metis (mono_tags, lifting) CollectD assm glul_eq_restrict glul_lift_pred_def in_mono that wp\<^sub>i.simps(2))
  next
    case (leak x31 x32)
    then show ?thesis 
    using that unfolding restrict_pred_def2 glul_lift_pred_def using assm
    apply (simp) unfolding a apply simp using a'_def unfolding comp_def fun_upd_def apply simp
    by (smt (verit) a glul_lift_pred_def in_mono lvarmap_eqI mem_Collect_eq ul_restrict_of_glul unlabel.simps(1) unlabel.simps(2) varmap_rec.select_convs(1) varmap_rec.select_convs(2) varmap_st_of_glul)
  next
    case full_fence
    then show ?thesis using that unfolding restrict_pred_def2 glul_lift_pred_def by simp
  next
    case nop
    then show ?thesis using that unfolding restrict_pred_def2 glul_lift_pred_def using assm
    by (metis glul_eq_restrict glul_lift_pred_def subset_iff that wp\<^sub>i.simps(5) wp\<^sub>i\<^sub>s.simps(5))
  qed
qed 

lemma [simp]: "varmap_st a\<^sup>G\<^sup>L (Ul v) = varmap_st a v" for a v
  unfolding glul_lift_pred_def by auto

lemma [simp]: "varmap_rec.more a\<^sup>G\<^sup>L = varmap_rec.more a" for a
  unfolding glul_lift_pred_def by auto

lemma z2: "a \<in> wp\<^sub>a x3 Q \<Longrightarrow> a \<in> (wp\<^sub>a (x3 \<circ> ul_restrict) Qs)[y\<phi> sub y]" if "Q \<subseteq> Qs[y\<phi> sub y]" for a x3 Q Qs
unfolding comp_def apply auto unfolding wp\<^sub>a.simps restrict_pred_def image_def apply auto
proof
  let ?x6 = "a\<^sup>G\<^sup>L"
  note a2 = varmap_rec.surjective[symmetric]
  assume a: "a\<lparr>varmap_rec.more := x3 a\<rparr> \<in> Q"
  then show
    "(\<forall>v. varmap_st ?x6 (Gl v) = varmap_st ?x6 (Ul v)) \<and>
      ?x6\<lparr>varmap_rec.more := x3 \<lparr>varmap_st = \<lambda>v. varmap_st ?x6 (Ul v), \<dots> = varmap_rec.more ?x6\<rparr>\<rparr> \<in> Qs \<and>
      a = \<lparr>varmap_st = \<lambda>v. varmap_st ?x6 (Ul v), \<dots> = varmap_rec.more ?x6\<rparr>"
  proof (intro conjI allI, goal_cases)
    case (1 v)
    then show ?case by (simp add: varmap_st_of_glul)
  next
    case 2
    note xxx[simp] = a2[of a]
    note aasd = that
    let ?a' = "a\<lparr>varmap_rec.more := x3 a\<rparr>"
    have s2: "\<exists>s2\<in>Qs. ?a' = \<lparr>varmap_st = \<lambda>v. varmap_st s2 (Gl v), \<dots> = varmap_rec.more s2\<rparr> \<and>
                  (\<forall>v. varmap_st s2 (Gl v) = varmap_st s2 (Ul v))"
      using that unfolding glul_lift_pred_def restrict_pred_def2 apply simp using a by blast
    then show ?case apply clarsimp unfolding glul_lift_pred_def apply simp
    apply (subgoal_tac "\<lparr>varmap_st = \<lambda>v. varmap_st a (unlabel v), \<dots> = x3 a\<rparr> = s2")
    apply simp
    apply (intro varmap_rec.equality ext allI)
    apply (case_tac x)
    apply simp_all
    using varmap_rec.ext_inject varmap_rec.update_convs(2) xxx
    by metis+
  next
    case 3
    then show ?case by (metis ul_restrict.simps ul_restrict_of_glul)
  qed
qed


lemma QUESTION: "[wp R c\<^sub>2 Q]\<^sub>; \<subseteq> [wp R c\<^sub>2 Q]\<^sub>s[y\<phi> sub y]" if "[Q]\<^sub>; \<subseteq> [Q]\<^sub>s[y\<phi> sub y]" "reflexive R" "transitive R" for Q c\<^sub>2 R
using that
proof (induct c\<^sub>2 arbitrary: Q)
  case (Op x1 x2 x3)
  then show ?case apply simp apply (intro y)
  using restrict_pred_distrib restrict_of_ul[of x1] z[of _ _ _ x2] z2[of "[Q]\<^sub>;" "[Q]\<^sub>s" _ x3] by (blast, auto)
next
  case (If x1 c1 c2)
  then show ?case apply (simp add: prod.case_eq_if) apply (intro y)
    apply auto by (meson If.hyps in_mono)+
next
  case (While x1 x2 x3 c)
  then show ?case using y that stabilize_entail subset_iff by (simp add: le_infI1)
next
  case (DoWhile x1 x2 c x4)
  then show ?case using y that stabilize_entail subset_iff by (simp add: le_infI1)
qed simp_all

lemma wp_stable [intro]: "stable\<^sub>t R [Q]\<^sub>; \<Longrightarrow> reflexive R \<Longrightarrow> transitive R \<Longrightarrow> stable\<^sub>t R [wp R c Q]\<^sub>;"
using stabilize_stable
proof (induct c arbitrary: Q)
  case (If x1 c1 c2)
  thus ?case by (clarsimp simp add: prod.case_eq_if)
qed auto

lemma wp_stable\<^sub>L [intro]: "stable\<^sub>L R [Q]\<^sub>s \<Longrightarrow> reflexive R \<Longrightarrow> transitive R \<Longrightarrow> stable\<^sub>L R [wp R c Q]\<^sub>s"
using stabilize_stable
proof (induct c arbitrary: R Q)
  case (If x1 c1 c2)
  thus ?case by (clarsimp simp add: prod.case_eq_if) blast
qed (all\<open>clarsimp?; blast\<close>)

lemma basic_cmpI[intro]:
  assumes P:  "P \<subseteq> Q"
  assumes G:  "reflexive G"
  assumes st: "stable R P"
              "stable R Q"
  shows "R,G \<turnstile>\<^sub>A P {liftl (cmp b)} Q"
apply (rule atomicI)
  unfolding liftl_def State.wp_def using P apply fastforce
  unfolding guar_def using G apply (clarsimp simp add: reflexive_def; fail)
  using st apply simp_all
done

lemma [simp]:
  "(a \<union> b) \<inter> w = (a \<inter> w \<union> b \<inter> w)"
  by auto

method simp1 = (simp; fail)

section \<open>com_wp\<close>
(* lemma spec_part_simp [simp]: "fst x = [x]\<^sub>s" for x :: "('r,'v,'a) spec_state" by (cases x) auto   *)
(* lemma seq_part_simp [simp]: "snd x = [x]\<^sub>;" for x :: "('r,'v,'a) spec_state" by (cases x) auto *)

text \<open>Com Rule\<close>
theorem com_wp:
  (* Q captures the speculative implications of r *)
  assumes s: "(base_rel_frame_id (step\<^sub>t R)), (base_rel_guar G' w) \<turnstile> (spec_pred_of_lvm_pred [Q]\<^sub>s w) {r} (spec_pred_of_lvm_pred Q' w)"
  (* Q is stable *)
  assumes st: "stable\<^sub>t R [Q]\<^sub>;" "stable\<^sub>L R [Q]\<^sub>s"
  (* VCs are strong enough to establish guarantee *)
  assumes g: "guar\<^sub>c c G" "wr\<^sub>l c \<subseteq> w" "lk\<^sub>l c \<inter> w = {}"

  (* Standard properties of R G *)
  assumes wf: "wellformed R G" "reflexive G'" "G' \<subseteq> step\<^sub>t R \<inter> step G"

  (* sequential postcondition entails speculative postcondition *)
  assumes Q: "[Q]\<^sub>; \<subseteq> [Q]\<^sub>s[y\<phi> sub y]"

  shows "(R,G,G' \<turnstile> wp R c Q {c,r,w} Q) \<and> (stable\<^sub>t R [wp R c Q]\<^sub>; \<and> stable\<^sub>L R [wp R c Q]\<^sub>s)"
  using s st g Q
proof (induct c arbitrary: Q' Q r w)
  case Skip
  then show ?case by (auto)
next
  case (Op x1 x2 x3)
  thus ?case using wf by (intro conjI basic_wp) auto
next
  case (Seq c\<^sub>1 c\<^sub>2)
  hence c2: "R,G,G' \<turnstile> wp R c\<^sub>2 Q {c\<^sub>2,r,w} Q" "stable\<^sub>t R [wp R c\<^sub>2 Q]\<^sub>;" "stable\<^sub>L R [wp R c\<^sub>2 Q]\<^sub>s" by simp+
  have wpQ: "[wp R c\<^sub>2 Q]\<^sub>; \<subseteq> [wp R c\<^sub>2 Q]\<^sub>s[y\<phi> sub y]" using QUESTION Seq.prems(7) local.wf(1) by auto (* TODO: Q entailment is perserved by wp transformer *)
  have "(R,G,G' \<turnstile> wp R c\<^sub>1 (wp R c\<^sub>2 Q) {c\<^sub>1,lift\<^sub>c (ts_lang_of_vm_lang c\<^sub>2 w) r w,w} (wp R c\<^sub>2 Q))
          \<and> (stable\<^sub>t R [wp R c\<^sub>1 (wp R c\<^sub>2 Q)]\<^sub>; \<and> stable\<^sub>L R [wp R c\<^sub>1 (wp R c\<^sub>2 Q)]\<^sub>s)"
    using Seq(1)[OF _ c2(2,3)] c2(1) Seq(6,7,8,9) wpQ by auto
  then show ?case using c2 by auto
next
  case (If b c\<^sub>1 c\<^sub>2)
  hence c1: "R,G,G' \<turnstile> wp R c\<^sub>1 Q {c\<^sub>1,r,w} Q" by simp
  hence c2: "R,G,G' \<turnstile> wp R c\<^sub>2 Q {c\<^sub>2,r,w} Q" using If by simp
  have st: "stable\<^sub>t R [local.wp R c\<^sub>1 Q]\<^sub>;" "stable\<^sub>t R [local.wp R c\<^sub>2 Q]\<^sub>;"
           "stable\<^sub>L R [local.wp R c\<^sub>1 Q]\<^sub>s" "stable\<^sub>L R [local.wp R c\<^sub>2 Q]\<^sub>s"
    using If by auto
  have GG': "base_rel_guar G' w \<subseteq> base_rel_guar (step G) w"
    using wf base_rel_def base_rel_guar_def by auto

  have b1: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w 
            \<turnstile> seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (cmp b) [wp R c\<^sub>1 Q]\<^sub>;)) {Basic (liftl (cmp b))} seq_pred_of_vm_pred [wp R c\<^sub>1 Q]\<^sub>;" 
  using cmp_seq st If wf by blast
  have b1s: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w 
            \<turnstile> spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [local.wp R c\<^sub>1 Q]\<^sub>s)) w {Basic (liftl (cmp b))} spec_pred_of_lvm_pred [local.wp R c\<^sub>1 Q]\<^sub>s w" 
  using cmp_spec st If wf by blast

  have b2: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w 
            \<turnstile> seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (ncmp b) [wp R c\<^sub>2 Q]\<^sub>;)) {Basic (liftl (ncmp b))} seq_pred_of_vm_pred [wp R c\<^sub>2 Q]\<^sub>;" 
  using cmp_seq st If wf by blast
  have b2s: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w 
            \<turnstile> spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [local.wp R c\<^sub>2 Q]\<^sub>s)) w {Basic (liftl (ncmp b))} spec_pred_of_lvm_pred [local.wp R c\<^sub>2 Q]\<^sub>s w" 
  using cmp_spec st If wf by blast

  note prod.case_eq_if[simp]

  have wp_subset_wps: "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>; \<subseteq> [local.wp R c\<^sub>2 Q]\<^sub>s[y\<phi> sub y]" "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>; \<subseteq> [local.wp R c\<^sub>1 Q]\<^sub>s[y\<phi> sub y]"
  apply (all\<open>standard; simp; erule stabilizeE\<close>)
  apply (all\<open>simp add: local.wf(1)\<close>)
  using QUESTION If.prems(7) local.wf(1) by (meson in_mono)+

  have wps_subset_wps: "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>s \<subseteq> [local.wp R c\<^sub>2 Q]\<^sub>s" "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>s \<subseteq> [local.wp R c\<^sub>1 Q]\<^sub>s"
  using stabilize\<^sub>LE local.wf(1) by auto

  have wp_subset_wpi: "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>; \<subseteq> stabilize R (wp\<^sub>i (cmp b) [wp R c\<^sub>1 Q]\<^sub>;)" "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>; \<subseteq> stabilize R (wp\<^sub>i (ncmp b) [wp R c\<^sub>2 Q]\<^sub>;)"
  by (auto simp add: stabilize_def)

  have wp_subset_wpis: "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>s \<subseteq> stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [wp R c\<^sub>1 Q]\<^sub>s)" "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>s \<subseteq> stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [wp R c\<^sub>2 Q]\<^sub>s)"
  by (auto simp add: stabilize\<^sub>L_def)

  have wp: "[wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>; \<subseteq> wp\<^sub>i (cmp b) [wp R c\<^sub>1 Q]\<^sub>;"
  using local.wf(1) stabilize_smaller subset_trans wp_subset_wpi(1) by auto

  show ?case
  apply (simp, intro conjI)
  subgoal "not speculating before If"
  apply (rule choice_if)
    apply (simp, intro choice_if seq)
      using c1 apply fast
      using b1 apply simp1
      apply (rule spec_judgement)
        apply (rule seq)
          using If.prems apply simp1
          using c2 apply fast
        using wf apply simp1
        using wp_subset_wpi apply simp1
        using wp_subset_wps apply simp1
        using wf apply fast
      using c1 apply fast
      apply (rule conseq[OF b1])
        using stabilize_def apply fastforce
        apply auto[3]
    apply (simp, intro choice_if seq)
      using c2 apply fast
      using b2 apply simp1
      apply (rule spec_judgement)
        apply (rule seq)
          using If.prems apply simp1
          using c1 apply fast
        using wf apply simp1
        using wp_subset_wpi apply simp1
        using wp_subset_wps apply simp1
        using wf apply fast
      using c2 apply fast
      apply (rule conseq[OF b2])
        using stabilize_def apply fastforce
        apply auto[3]   
  by -
  subgoal "already speculating before If"
  apply (rule choice_if)
    apply (simp, intro choice_if seq)
      using c1 apply fast
      using b1s apply simp1
      apply (rule spec_judgement')
        apply (rule seq)
          using If.prems apply simp1
          using c2 apply fast
        using wf apply fast
        using wp_subset_wpis apply simp1
        using wps_subset_wps apply simp1
        using wf apply fast
      using c1 apply fast
      apply (rule conseq[OF b1s])
        using stabilize\<^sub>L_def apply fastforce
        apply auto[3]
    apply (simp, intro choice_if seq)
      using c2 apply fast
      using b2s apply simp1
      apply (rule spec_judgement')
        apply (rule seq)
          using If.prems apply simp1
          using c1 apply fast
        using wf apply fast
        using wp_subset_wpis apply simp1
        using wps_subset_wps apply simp1
        using wf apply fast
      using c2 apply fast
      apply (rule conseq[OF b2s])
        using stabilize\<^sub>L_def apply fastforce
        apply auto[3]   
  by -
  subgoal using wf st by auto
  subgoal using wf st by auto
  done
next
  case (While b Inv Inv\<^sub>s c)
  let ?case_While = ?case

  have reflexive: "reflexive R" using wf by simp
  have arg_commute: "(A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> A \<Longrightarrow> C)" for A B C by simp
    
  have assert_nonempty:
    "(assert a) \<noteq> {} \<Longrightarrow> a"
    "(assert a) \<inter> b \<noteq> {} \<Longrightarrow> a"
    "b \<inter> (assert a) \<noteq> {} \<Longrightarrow> a"
    "x \<in> assert (a) \<Longrightarrow> a"
    for a b x using assert_def by (force, force, force, (auto simp add: assert_def, meson empty_iff))

  have FST3: "A \<and> B \<and> C \<Longrightarrow> A" for A B C by simp
  have FST2: "A \<and> B \<Longrightarrow> A" for A B by simp
  have SND2: "A \<and> B \<Longrightarrow> B" for A B by simp

  note hyps_seq = FST2[OF FST3[OF While.hyps]]
  note hyps_spec = SND2[OF FST3[OF While.hyps]]

  show ?case
  proof (cases "[wp R (While b Inv Inv\<^sub>s c) Q]\<^sub>; = {}")
    case True
    then show ?thesis
    apply (intro conjI)
      using True falseI apply simp apply (rule conseq[where ?P="{}" and ?Q="{}"]) 
        apply simp1
        apply force
        apply force
        apply force
        apply force
      defer
      apply force
      using While.prems(3) local.wf(1) apply blast
      apply auto      
      apply (intro loop choice_if seq)
      sorry (* do we need to add assertions to speculative case too? *)
  next
    case False
    note nonempty = False
  
    have asserts: "Inv\<^sub>s \<subseteq> [Q]\<^sub>s" "Inv \<subseteq> (wp\<^sub>i (ncmp b) [Q]\<^sub>;)" "Inv\<^sub>s \<subseteq> [(wp R c (Inv\<^sub>s, Inv))]\<^sub>s" "Inv \<subseteq> wp\<^sub>i (cmp b) [(wp R c (Inv\<^sub>s, (stabilize R Inv)))]\<^sub>;"
    using nonempty
    apply (all\<open>simp only: wp.simps snd_def case_prod_conv\<close>)
    apply (all\<open>simp only: snd_def[symmetric]\<close>)
    apply (all\<open>drule stabilize_nonempty[OF reflexive]\<close>)
    using assert_nonempty(1) by force+
  
    have Inv_QUESTION: "Inv \<subseteq> Inv\<^sub>s[y\<phi> sub y]"
    sorry (* possibly new assert in wp *)
  
    (* have st_Inv1: "stable\<^sub>t R Inv" "stable\<^sub>L R Inv\<^sub>s" *)
    (* sorry (* possibly assert stable Inv and stable Invs *) *)
  
    (* hence st_Inv2: "stable (base_rel_frame_id (step\<^sub>t R)) (spec_pred_of_lvm_pred Inv\<^sub>s w)" *)
    (* by auto *)
  
    (* note st_Inv = st_Inv1 st_Inv2 *)
  
    (* have stabilize_Inv: "stabilize R Inv = Inv" "stabilize\<^sub>L R Inv\<^sub>s = Inv\<^sub>s" *)
    (* using st_Inv wf by simp_all *)
  
    have c: "R,G,G' \<turnstile> wp R c Q {c,r,w} Q" using While by simp
    have st: "stable\<^sub>t R [local.wp R c Q]\<^sub>;" "stable\<^sub>L R [local.wp R c Q]\<^sub>s"
      using While by auto
    have GG': "base_rel_guar G' w \<subseteq> base_rel_guar (step G) w"
      using wf base_rel_def base_rel_guar_def by auto
  
    have wp_ncmp_Q: "base_rel_frame_id(step\<^sub>t R),base_rel_guar (step G) w
                     \<turnstile> seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (ncmp b) [Q]\<^sub>;)) {Basic (liftl (ncmp b))} seq_pred_of_vm_pred [Q]\<^sub>;"
    using While.prems wf
    proof (intro cmp_seq)
    qed auto
  
    have Inv_ncmp_Q: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w
                      \<turnstile> seq_pred_of_vm_pred (stabilize R Inv) {Basic (liftl (ncmp b))} seq_pred_of_vm_pred [Q]\<^sub>;"
    using asserts(2) wf stabilize_def
    proof (intro conseq[OF wp_ncmp_Q])
    qed (all\<open>clarsimp; blast\<close>)
  
    have wp_ncmp_Qs: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w
                      \<turnstile> spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [Q]\<^sub>s)) w {Basic (liftl (ncmp b))} spec_pred_of_lvm_pred [Q]\<^sub>s w"
    using While wf by (intro cmp_spec) auto
  
    have Invs_ncmp_Qs: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w
                        \<turnstile> spec_pred_of_lvm_pred (stabilize\<^sub>L R Inv\<^sub>s) w {Basic (liftl (ncmp b))} spec_pred_of_lvm_pred [Q]\<^sub>s w"
    apply (rule conseq[OF wp_ncmp_Qs])
      apply (rule spec_mono)
        apply (standard, rule stabilize\<^sub>L_entail[where ?P=Inv\<^sub>s])
          apply (simp add: local.wf(1); fail)
          using wf apply fast
          using asserts apply force
    by simp_all
  
    thm s
    have s': "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w 
              \<turnstile> spec_pred_of_lvm_pred [(stabilize\<^sub>L R Inv\<^sub>s, stabilize R Inv)]\<^sub>s w {r} spec_pred_of_lvm_pred Q' w"
    using While.prems(1) asserts(1) conseq spec_mono
    by (simp, meson local.wf(1) stabilize\<^sub>LE subset_eq)
  
    (* have Invs_r: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile> spec_pred_of_lvm_pred Inv\<^sub>s w {r} spec_pred_of_lvm_pred [Q]\<^sub>s w" *)
  
    have Invs_c_Invs: "R,G' \<turnstile>\<^sub>s (stabilize\<^sub>L R Inv\<^sub>s) {c,r,w} (stabilize\<^sub>L R Inv\<^sub>s)"
    using wf While.prems \<open>Inv \<subseteq> Inv\<^sub>s[y\<phi> sub y]\<close> asserts(3)
    thm hyps_spec
    apply (intro conseq[OF hyps_spec[OF s']])
    apply ((auto)[1]; fail)
    apply ((auto)[1]; fail)
apply ((auto)[1]; fail)
apply ((auto)[1]; fail)
apply ((auto)[1]; fail)
defer
defer
apply ((auto)[1]; fail)
apply ((auto)[1]; fail)
apply ((auto)[1]; fail)
apply (simp add: y)
apply (rule spec_mono)
apply standard
apply (rule stabilize\<^sub>LE)
apply simp1
using wf apply simp1
using asserts(3)
sorry
  
    have wpcInv_c_Inv: "R,G \<turnstile>\<^sub>; [wp R c (Inv\<^sub>s,Inv)]\<^sub>; {c,r,w} [(Inv\<^sub>s,Inv)]\<^sub>;"
    using s' st_Inv While Inv_QUESTION
    proof (intro hyps_seq)
    qed auto
  
    have Inv_b_wpcInv: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w
          \<turnstile> seq_pred_of_vm_pred Inv {Basic (liftl (cmp b))} seq_pred_of_vm_pred [local.wp R c (Inv\<^sub>s, Inv)]\<^sub>;"
    apply (intro basic atomicI)
      using asserts(4) stabilize_Inv unfolding liftl_def State.wp_def apply force
      using wf base_rel_guarI unfolding reflexive_def guar_def apply clarsimp apply blast
      using st_Inv apply fast
      using st_Inv wp_stable wf apply (simp add: stable_ts; fail)
    done
  
    have Invs_b_Invs: "base_rel_frame_id(step\<^sub>t R),base_rel_guar G' w
          \<turnstile> spec_pred_of_lvm_pred Inv\<^sub>s w {Basic (liftl (cmp b))} spec_pred_of_lvm_pred Inv\<^sub>s w"
    using wf st_Inv
    proof (intro basic basic_cmpI)
    qed (auto simp add: base_rel_guarI reflexive_def)
  
    have Inv_Iterc_Inv: "base_rel_frame_id(step\<^sub>t R),base_rel_guar G' w
                          \<turnstile> spec_pred_of_lvm_pred Inv\<^sub>s w {Iterw (lift\<^sub>c (ts_lang_of_vm_lang c w) r w)} spec_pred_of_lvm_pred Inv\<^sub>s w"
    apply (rule loop) using st_Inv Invs_c_Invs by auto
  
    have Inv_IterSpec_Inv: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w
                            \<turnstile> seq_pred_of_vm_pred Inv {Iterw(\<Sqinter>s. if s = 0 then (\<triangle> Capture (emptyFrame w) r) \<cdot> Seqw (Basic (liftl (cmp b)))(lift\<^sub>c (ts_lang_of_vm_lang c w) r w)else Seqw (Basic (liftl (cmp b)))(lift\<^sub>c (ts_lang_of_vm_lang c w) r w))} seq_pred_of_vm_pred Inv"
    apply (rule loop)
      using st_Inv apply fast
      apply (rule choice_if)
        apply (rule seq)
          apply (rule seq)
            using wpcInv_c_Inv apply force
            using Inv_b_wpcInv apply blast
          apply (rule spec_judgement)
            using s' apply fast
            using wf apply fast
            apply (simp; fail)
            using Inv_QUESTION apply (simp; fail)
            using st_Inv apply fast
        apply (rule seq)
          using wpcInv_c_Inv apply force
          using Inv_b_wpcInv apply fast
    done
  
    show ?thesis
    apply (simp del: wp.simps)
    apply (intro conjI)
      subgoal
      apply (intro seq choice_if)
        using Inv_ncmp_Q apply simp
        apply (rule spec_judgement)
          apply (intro seq)
            using s' apply simp1
            using Inv_Iterc_Inv apply simp1
            using Invs_c_Invs apply simp1
          using wf apply simp1
          using subset_refl apply fast
          using Inv_QUESTION apply simp1
          using st_Inv apply simp1
        using Inv_ncmp_Q apply simp1
        apply (rule conseq[OF Inv_IterSpec_Inv])
          using local.wf(1) st_Inv(1) stabilize_entail apply fastforce
          apply simp_all[3]
      by -
      subgoal
      apply (intro seq choice_if)
        using Invs_ncmp_Qs apply simp1
        apply (rule spec_judgement')
          apply (intro seq)
            using s' apply simp1
            apply (rule loop)
              using st_Inv apply simp1
              using Invs_c_Invs apply simp1
            using Invs_c_Invs apply simp1
          using wf apply fast
          using stabilize_Inv apply fast
          using stabilize_Inv apply fast
          using st_Inv apply simp1
        using Invs_ncmp_Qs apply simp1
        apply (simp add: stable_stabilize\<^sub>L_id[OF reflexive st_Inv(2)], rule loop)
          using st_Inv apply simp1
          apply (rule choice_if)
            apply (rule seq, rule seq)
              using Invs_c_Invs apply simp1
              using Invs_b_Invs apply simp1
              apply (rule spec_judgement')
                using s' apply simp1
                using wf apply fast
                using subset_refl apply fast
                using subset_refl apply fast
                using st_Inv apply simp1
              apply (rule seq)
                using Invs_c_Invs apply simp1
                using Invs_b_Invs apply simp1
      by -
      subgoal using wf by auto
      subgoal using wf by auto
    done
  qed
next
  case (DoWhile x1 x2 c x4)
  then show ?case sorry
qed

thm lang.induct

subsection \<open>High-Level Theorem\<close>

text \<open>Soundness lemma for WP reasoning\<close>
theorem simAsm_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" "reflexive G'" "G' \<subseteq> step\<^sub>t R \<inter> step G"
  assumes st: "stable\<^sub>t R [Q]\<^sub>;" "stable\<^sub>L R [Q]\<^sub>s"
  assumes g: "guar\<^sub>c c G"
  assumes P: "P \<subseteq>\<^sub>s wp R c Q"
  assumes l: "lk\<^sub>l c \<inter> wr\<^sub>l c = {}"
  assumes Q: "[Q]\<^sub>; \<subseteq> [Q]\<^sub>s[y\<phi> sub y]"
  shows "\<Turnstile> c SAT [[P]\<^sub>;, R, G, [Q]\<^sub>;]"
proof -
  have "\<forall>d>1. base_rel_frame_id (step\<^sub>t R),base_rel_frame_sz (step G) d (wr\<^sub>l c) \<turnstile>
          spec_pred_of_lvm_pred [Q]\<^sub>s (wr\<^sub>l c) {com.Nil} spec_pred_of_lvm_pred [Q]\<^sub>s (wr\<^sub>l c)"
    using st(2) by auto
  hence "R,G,G' \<turnstile> wp R c Q {c,Nil,wr\<^sub>l c} Q"
    using com_wp st wf g l Q by blast
  hence "R,G \<turnstile>\<^sub>; [wp R c Q]\<^sub>; {c,Nil,wr\<^sub>l c} [Q]\<^sub>;"
    by blast
  hence "R,G \<turnstile>\<^sub>; [P]\<^sub>; {c,Nil,wr\<^sub>l c} [Q]\<^sub>;"
    using P by (meson equalityD2 rules.conseq seq_mono)
  thus ?thesis using sound by blast
qed

end (* of context wp *)




end
