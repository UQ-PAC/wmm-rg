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
  sorry

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
  show ?case apply (auto simp: pushrelAll_def elim!: base_rel_guarE) sorry
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


(*
lemma vm_of_ts_wp:
  assumes "vm_of_ts x \<in> c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q)"
  shows "x \<in> State.wp (ts_pred_of_vm_pred c) (st_beh\<^sub>i \<alpha> O {(t, t'). t' = tauxupd t (f \<circ> vm_of_ts)}) (ts_pred_of_vm_pred Q)"
proof -
  have x[intro]: "vm_of_ts x \<in> c" "vm_of_ts x \<in> wp\<^sub>i \<alpha> (wp\<^sub>a f Q)" using assms by auto
  note wp_def[simp] ts_pred_of_vm_pred_def[simp]

  show ?thesis using x
  proof (cases \<alpha>)
    case (assign v val)
    then show ?thesis
    using x vm_of_ts_bothupd[where ?s=x and ?v=v]
    by (auto simp add: vm_of_ts_auxupd vm_of_ts.rep_eq)
  next
    case (cmp x2)
    then show ?thesis  
    using x
    by (auto simp add: vm_of_ts_auxupd, simp add: vm_of_ts.rep_eq)
  next
    case (leak v val)
    then show ?thesis 
    using x vm_of_ts_bothupd[where ?s=x and ?v=v]
    by (auto simp add: vm_of_ts_auxupd vm_of_ts.rep_eq)
  qed (simp_all add: vm_of_ts_auxupd)
qed *)

lemma wp_of_liftg:
  "\<And>x. reflexive R \<Longrightarrow> vm_of_ts x \<in> stabilize R ((vm_of_ts ` c)\<^sup>L \<inter> wp\<^sub>i\<^sub>s \<alpha> {t. t\<lparr>varmap_rec.more := f (ts_of_vm t)\<rparr> \<in> (Q\<^sup>G)\<^sup>U}\<^sup>L)\<^sup>U \<Longrightarrow> x \<in> wp\<^sub>\<alpha> (liftg c \<alpha> f) (ts_pred_of_vm_pred Q)" 
unfolding liftg_def apply simp
proof goal_cases
  case (1 x)
  have "vm_of_ts x \<in> ((vm_of_ts ` c)\<^sup>L \<inter> wp\<^sub>i\<^sub>s \<alpha> {t. t\<lparr>varmap_rec.more := f (ts_of_vm t)\<rparr> \<in> (Q\<^sup>G)\<^sup>U}\<^sup>L)\<^sup>U"
    using "local.1"(1) "local.1"(2) wp.stabilizeE sorry
  then show ?case unfolding wp_def stabilize_def sorry
qed

lemma vm_of_ts_wp_liftg:
  "\<And>x. vm_of_ts x \<in> c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q) \<Longrightarrow> x \<in> wp\<^sub>\<alpha> (liftg (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)) (ts_pred_of_vm_pred Q)" 
unfolding liftg_def 
by (simp add: ts_pred_of_vm_pred.transfer vm_of_ts_wp)

(*
lemma guar_of_liftg:
  assumes "c \<subseteq> local.guar (wp\<^sub>i \<alpha> \<circ> wp\<^sub>a f) (step G)"
  shows "guar\<^sub>\<alpha> (liftg (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)) (ts_rel_of_vm_rel (step G))"
using assms 
unfolding liftg_def guar_def ts_pred_of_vm_pred_def ts_rel_of_vm_rel_def
proof (clarsimp, goal_cases)
  case (1 x y)
  hence x: "vm_of_ts x \<in> wp\<^sub>i \<alpha> {ta. (vm_of_ts x, ta\<lparr>varmap_rec.more := f ta\<rparr>) \<in> step G}"
    unfolding wp\<^sub>r_def by auto
  then show ?case using 1
  proof (cases \<alpha>)
    case (assign v val)
    then show ?thesis using x 1 vm_of_ts_bothupd[where ?s=x and ?v=v]
    by (simp add: vm_of_ts.rep_eq)    
  next
    case (cmp _)
    then show ?thesis using x 1 vm_of_ts_auxupd[of f x]
    by (clarsimp simp add: vm_of_ts.rep_eq)
  next
    case (leak v val)
    then show ?thesis using x 1 vm_of_ts_bothupd[where ?s=x and ?v=v] 
    by (simp add: vm_of_ts.rep_eq)
  qed (auto simp add: vm_of_ts_auxupd)
qed *)

lemma guar_of_liftg':
  assumes "c \<subseteq> guar (wp\<^sub>i \<alpha> \<circ> wp\<^sub>a f) (step G)" 
  shows "State.guar {s. vm_of_ts s \<in> c \<and> ts_is_seq s} {(s, s'). (s, s') \<in> st_beh\<^sub>i \<alpha> O {(t, t'). t' = tauxupd t (f \<circ> vm_of_ts)} \<and> ts_is_seq s \<and> ts_is_seq s'} (seq_rel_of_vm_rel (step G))"
proof (cases \<alpha>)
  case (assign x11 x12)
  then show ?thesis apply simp unfolding liftg_def seq_rel_of_vm_rel_def ts_pred_of_vm_pred_def guar_def apply auto
    unfolding ts_rel_of_vm_rel_def
     apply auto using assms
     sorry
next
  case (cmp x2)
  then show ?thesis sorry
next
  case (leak x31 x32)
  then show ?thesis sorry
next
  case full_fence
  then show ?thesis sorry
next
  case nop
  then show ?thesis sorry
qed

lemma stable_ts_rel_from_stablet [elim]: 
  assumes "stable\<^sub>t R P"
  shows "State.stable (ts_rel_of_vm_rel (step\<^sub>t R)) (ts_pred_of_vm_pred (P))"
using assms 
unfolding stable_def stabilize_def ts_pred_of_vm_pred_def ts_rel_of_vm_rel_def step\<^sub>t_def transitive_def
by auto

lemma stable_seq_from_stable_ts:
  assumes "State.stable (ts_rel_of_vm_rel (step\<^sub>t R)) (ts_pred_of_vm_pred Q)"
  shows "State.stable (seq_rel_of_vm_rel (step\<^sub>t R)) (seq_pred_of_vm_pred Q)"
using assms
unfolding stable_def seq_pred_of_vm_pred_def seq_rel_of_vm_rel_def
using ts_upper_of_seq 
by clarsimp fastforce

lemma stable_seq_rel_from_stablet [intro]:
  assumes "stable\<^sub>t R Q"
  shows "State.stable (seq_rel_of_vm_rel (step\<^sub>t R)) (seq_pred_of_vm_pred Q)"
using assms stable_seq_from_stable_ts stable_ts_rel_from_stablet by auto


(* lemma stept_stept [simp]: "step\<^sub>t (step\<^sub>t G) = step\<^sub>t G"  *)
(* unfolding step\<^sub>t_def by simp *)

(* lemma step_step [simp]: "step (step G) = step G"  *)
(* unfolding step_def by simp *)

lemma tauxupd_more [simp]: "{(t, t'). t' = tauxupd t (varmap_rec.more \<circ> vm_of_ts)} = Id" 
unfolding tauxupd_def auxupd_def vm_of_ts_def 
by (auto simp add: Rep_tstackI(1) Rep_tstack_inverse)

lemma wp\<^sub>a_more [simp]: "wp\<^sub>a varmap_rec.more = id" 
by standard (simp add: wp.wp\<^sub>a.simps)

lemma [simp]: "(\<lambda>s. frame.more (last (Rep_tstack s))) = (\<lambda>s. varmap_rec.more (vm_of_ts s))" 
proof
  show "\<And>s. frame.more (last (Rep_tstack s)) = varmap_rec.more (vm_of_ts s)"
  unfolding vm_of_ts_def by auto
qed

lemma [simp]: "ts_pred_of_vm_pred UNIV = UNIV"
unfolding ts_pred_of_vm_pred_def by simp

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
  case (1 v)
  let ?v_ = "v\<lparr>varmap_st := (varmap_st v)(Ul x11 := ev\<^sub>E (varmap_st v) (map\<^sub>E Ul id id x12))\<rparr>"
  let ?v = "?v_\<lparr>varmap_rec.more := f (gl_restrict ?v_)\<rparr>"

  have tlookup: "tlookup x va = varmap_st v (Ul va)" for va
    using 1(4) unfolding tlookup_def vm_of_ts_def by auto

  have ev: "ev\<^sub>E (tlookup x) xa = (ev\<^sub>E (varmap_st v) \<circ> map\<^sub>E Ul id id) xa" for xa
  by (induct xa, simp_all add: tlookup id_def comp_def) (metis (mono_tags, lifting) map_eq_conv)

  have "ev\<^sub>E (\<lambda>va. varmap_st v (Ul va)) x12 = ev\<^sub>E (tlookup x) x12"
    using tlookup by presburger

  have notnone: "frame_st (last (Rep_tstack (tauxupd (tupdate x x11 (ev\<^sub>E (tlookup x) x12)) (\<lambda>x. f (vm_of_ts x))))) va \<noteq> None" for va
    by blast

    
  show ?case
  proof (standard, intro conjI)
    show "?v \<in> Qspec" using 1(2) by (cases x12) (auto simp add: id_def wp\<^sub>a.simps)
    show "ts_is_spec (tauxupd (tupdate x x11 (ev\<^sub>E (tlookup x) x12)) (f \<circ> vm_of_ts))" using 1(2,3) by clarify (metis tauxupd_len ts_is_seq_def tupdate_len)
    show "vm_of_ts ?ts = \<lparr>varmap_st = \<lambda>va. varmap_st (?v) (Ul va), \<dots> = varmap_rec.more (?v)\<rparr>" unfolding vm_of_ts_def apply auto apply standard apply (case_tac "va = x11") apply auto apply (cases x12) apply auto using 1(4)
    apply (simp add: vm_of_ts.abs_eq) apply (subgoal_tac "ev\<^sub>E (tlookup x) = (ev\<^sub>E (varmap_st v) \<circ> map\<^sub>E Ul id id)") apply auto apply standard  
    using ev apply blast 
    apply (simp add: tlookup)  apply (rule arg_cong[where ?f=f]) apply auto apply standard apply (case_tac "x11 = xa") apply auto using 1(4) unfolding vm_of_ts_def apply auto 
    sorry (* we need properties constraining the acceptable auxfns (i.e. they are minimally state-dependent). or, we need to ignore them. *)
    show "tstack_base ?ts = \<lparr>varmap_st = \<lambda>va. varmap_st (?v) (Gl va), \<dots> = varmap_rec.more (?v)\<rparr>" unfolding tstack_base_def apply auto apply standard unfolding comp_def using notnone sorry
  qed
next
  case 2
  show ?case using assms(2) tauxupd_len tupdate_len ts_is_seq_def by metis
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
  let ?P = "(stabilize\<^sub>L R (c\<^sup>L \<inter> wp\<^sub>i\<^sub>s \<alpha> (wp\<^sub>a (f \<circ> gl_restrict) [Q]\<^sub>s)), 
                 stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f [Q]\<^sub>;)))"
  have "R,G \<turnstile>\<^sub>s ?P {Op (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)} Q"
  proof (standard, goal_cases nonspec spec)
    case nonspec
    obtain a v b where ba: "Basic (a, v, b) = nonspec (lift\<^sub>c (Op (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)) com.Nil {})" 
      by (simp add: liftg_def)
    have a: "a = (\<alpha>, (f \<circ> vm_of_ts))" using ba by (simp add: liftg_def)
    have v: "v = {x \<in> (ts_pred_of_vm_pred c). ts_is_seq x}" using ba by (simp add: liftg_def)
    have b: "b = beh\<^sub>a (\<alpha>, f \<circ> vm_of_ts)" using ba by (simp add: liftg_def)
    have refl: "reflexive R" using assms(2) by simp
    have stabilizeE': "x \<in> X" if "x \<in> stabilize R X" for x X using refl stabilizeE that by auto
    show ?case unfolding b ba[symmetric] apply (intro basic) unfolding atomic_rule_def a v b
    proof (simp only: seq_part.simps, intro conjI impI, goal_cases)
      case 1
      then show ?case
      proof standard
        fix x
        assume x: "x \<in> seq_pred_of_vm_pred (stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f [Q]\<^sub>;)))"
        hence lhs: "x \<in> seq_pred_of_vm_pred (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f [Q]\<^sub>;))" 
          using stabilizeE' seq_pred_of_vm_pred_subset by blast
        have x1: "vm_of_ts x \<in> c" "ts_is_seq x"
          using lhs unfolding seq_pred_of_vm_pred_def by (simp, simp)
        have x2: "vm_of_ts x \<in> wp\<^sub>i \<alpha> (wp\<^sub>a f [Q]\<^sub>;)" 
          using lhs unfolding seq_pred_of_vm_pred_def by simp
        note xx = x1 x2
        thus rhs: "x \<in> wp\<^sub>\<alpha> ((\<alpha>, f \<circ> vm_of_ts), {x \<in> ts_pred_of_vm_pred c. ts_is_seq x}, beh\<^sub>a (\<alpha>, f \<circ> vm_of_ts)) (seq_pred_of_vm_pred [Q]\<^sub>;)"
        proof (cases \<alpha>)
          case (assign x11 x12)
          thus ?thesis unfolding wp_def apply (auto simp add: xx) apply (rule basic_wp\<^sub>i_1_assign)
          using assign xx by auto
        next
          case (cmp x2)
          thus ?thesis unfolding wp_def apply (auto simp add: xx) using xx unfolding cmp 
          apply auto
          apply (simp add: vm_of_ts.abs_eq)
          using h3 by auto
        next
          case (leak x31 x32)
          thus ?thesis unfolding wp_def apply (auto simp add: xx) apply (rule basic_wp\<^sub>i_1_assign)
          using leak xx by auto
        next
          case full_fence
          thus ?thesis unfolding wp_def apply (auto simp add: xx) 
          using h3 x2 xx(2) by auto
        next
          case nop
          then show ?thesis unfolding nop 
            apply auto unfolding wp_def apply (auto simp add: xx)
            using x2 unfolding nop by (auto simp add: h3 xx(2))
        qed
      qed
    next
      case 2
      then show ?case apply (clarsimp, intro conjI) using stabilizeE' unfolding seq_pred_of_vm_pred_def by auto 
    next
      case 3
      have q: "seq_pred_of_vm_pred ((c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f [Q]\<^sub>;))) \<subseteq>  {x \<in> ts_pred_of_vm_pred c. ts_is_seq x}" 
        apply (clarsimp, intro conjI) using stabilizeE' unfolding seq_pred_of_vm_pred_def by auto
      then show ?case unfolding seq_rel_of_vm_rel_def seq_pred_of_vm_pred_def apply auto 
      proof goal_cases
        case 1
        have l: "\<And>x. ts_is_seq x \<Longrightarrow>  butlast (Rep_tstack x) = []" unfolding ts_is_seq_def tstack_len_def
          by (simp add: butlast_conv_take)
        have c: "c \<subseteq> local.guar (wp\<^sub>i \<alpha> \<circ> wp\<^sub>a f) (step G)" using assms by simp
        hence vm_of_ts_c: "\<And>x. vm_of_ts x \<in> c \<Longrightarrow> vm_of_ts x  \<in> (local.guar (wp\<^sub>i \<alpha> \<circ> wp\<^sub>a f) (step G))" by auto
        show ?case unfolding guar_def apply auto defer unfolding ts_is_seq_def tstack_upper_def using tstack_len_of_st_beh  apply simp
        apply (metis One_nat_def l tauxupd_len ts_is_seq_def)
        using q
        proof goal_cases
          case (1 x y)
            note c2 = vm_of_ts_c[OF 1(1)]
            have "(vm_of_ts x, vm_of_ts (tauxupd y (f \<circ> vm_of_ts))) \<in> ((step G))" using vm_of_ts_c[OF 1(1)] unfolding wp\<^sub>r_def apply auto
            proof (cases \<alpha>)
              case (assign x11 x12)
              have y: "tupdate x x11 (ev\<^sub>E (tlookup x) x12) = y" using 1(3) unfolding assign by auto
              show ?thesis using c2 unfolding wp\<^sub>r_def unfolding wp\<^sub>a.simps y apply (auto simp add: assign) by (metis varmap_rec.select_convs(1) vm_of_ts.abs_eq vm_of_ts_bothupd y) 
            next
              case (cmp x2)
              then show ?thesis using c2 1(3) unfolding wp\<^sub>r_def cmp apply (auto) apply (simp add: vm_of_ts.abs_eq) by (simp add: vm_of_ts_auxupd wp.wp\<^sub>a.simps)
            next
              case (leak x31 x32)
              then show ?thesis using c2 1(3) unfolding wp\<^sub>r_def leak wp\<^sub>a.simps apply auto by (metis varmap_rec.select_convs(1) vm_of_ts.abs_eq vm_of_ts_bothupd) 
            next
              case full_fence
              then show ?thesis using c2 1(3) unfolding wp\<^sub>r_def full_fence wp\<^sub>a.simps apply auto by (simp add: vm_of_ts_auxupd)
            next
              case nop
              then show ?thesis using c2 1(3) unfolding wp\<^sub>r_def nop wp\<^sub>a.simps apply simp by (simp add: vm_of_ts_auxupd)
            qed
          then show ?case using ts_rel_of_vm_rel_from_vm_of_ts by auto
        qed
      qed 
    next
      case 4
      then show ?case using assms by auto
    next
      case 5
      then show ?case using assms stable_ts_rel_from_stablet[OF assms(3)] by auto
    qed
  next
    case spec
    show ?case
    unfolding liftg_def
    proof (simp, intro basic, simp only: atomic_rule_def, intro conjI impI subsetI, goal_cases)
      case (1 x)
      thm assms
      have x: "x \<in> spec_pred_of_lvm_pred ((c\<^sup>L \<inter> wp\<^sub>i\<^sub>s \<alpha> (wp\<^sub>a (f \<circ> gl_restrict) [Q]\<^sub>s)))" using 1 assms(2) by auto
      have x_in_c: "x \<in> spec_pred_of_lvm_pred c\<^sup>L" using  x spec_pred_of_lvm_pred_subset by blast
      have x_in_wp: "x \<in> spec_pred_of_lvm_pred (wp\<^sub>i\<^sub>s \<alpha> (wp\<^sub>a (f \<circ> gl_restrict) [Q]\<^sub>s))" using  x spec_pred_of_lvm_pred_subset by blast
      have vm_x_in_c: "vm_of_ts x \<in> c" using x_in_c unfolding ul_lift_pred_def spec_pred_of_lvm_pred_def by auto
      have "x \<in> vc (liftg (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts))" using assms(4) x_in_c vm_x_in_c by (simp add: liftg_def)

      then show ?case apply (cases \<alpha>) apply auto unfolding wp_def apply auto unfolding liftg_def apply auto using   x_in_wp  apply auto unfolding wp\<^sub>a.simps apply auto sorry
    next
      case (2 x)
      then show ?case sorry
    next
      case 3
      then show ?case sorry
    next
      case 4
      then show ?case sorry
    next
      case 5
      then show ?case sorry
      qed
  qed                 
  thus ?thesis using conseq_s assms(1) by blast
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

  lemma y: "stabilize R Q \<subseteq> (stabilize\<^sub>L R Qs)[y\<phi> sub y]" if Q: "Q \<subseteq> Qs[y\<phi> sub y]" "reflexive R" for Q Qs R
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
              using gl sorry
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
  apply (induct x2 arbitrary: Q Qs a)
  unfolding image_def
  apply simp_all
  unfolding restrict_pred_def2 apply auto 
  sorry

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


  lemma QUESTION: "[wp R c\<^sub>2 Q]\<^sub>; \<subseteq> [wp R c\<^sub>2 Q]\<^sub>s[y\<phi> sub y]" if "[Q]\<^sub>; \<subseteq> [Q]\<^sub>s[y\<phi> sub y]" "reflexive R" for Q c\<^sub>2 R
  using that
  proof (induct c\<^sub>2 arbitrary: Q)
    case (Op x1 x2 x3)
    then show ?case apply simp apply (intro y)
    using restrict_pred_distrib restrict_of_ul[of x1] z[of _ _ _ x2] z2[of "[Q]\<^sub>;" "[Q]\<^sub>s" _ x3] by blast
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
  have wpQ: "[wp R c\<^sub>2 Q]\<^sub>; \<subseteq> [wp R c\<^sub>2 Q]\<^sub>s[y\<phi> sub y]" sorry (* TODO: Q entailment is perserved by wp transformer *)
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

  show ?case
  apply (clarsimp, intro choice_if conjI; (simp; intro choice_if)?)
  proof (goal_cases leftspec1 left1 rightspec1 right1 leftspec2 left2 rightspec2 right2 st1 st2)
    case leftspec1
    have c: "R,G \<turnstile>\<^sub>; [wp R c\<^sub>1 Q]\<^sub>; {c\<^sub>1,r,w} [Q]\<^sub>;" using c1 by auto
    have b: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
      seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (cmp b) [wp R c\<^sub>1 Q]\<^sub>;)) 
        {Basic (liftl (cmp b))} 
          seq_pred_of_vm_pred [wp R c\<^sub>1 Q]\<^sub>;" (is "?R,?G \<turnstile> ?P { ?b } ?Q")
      using cmp_seq st If wf by blast

    have s: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
      seq_pred_of_vm_pred 
        [(stabilize\<^sub>L R ([local.wp R c\<^sub>1 Q]\<^sub>s \<inter> [local.wp R c\<^sub>2 Q]\<^sub>s),
                   stabilize R
                    ({s. ev\<^sub>B (varmap_st s) b \<longrightarrow>
                         s \<in> [local.wp R c\<^sub>1 Q]\<^sub>; \<and> s \<in> [local.wp R c\<^sub>2 Q]\<^sub>s[y\<phi> sub y]} \<inter>
                     {s. \<not> ev\<^sub>B (varmap_st s) b \<longrightarrow>
                         s \<in> [local.wp R c\<^sub>2 Q]\<^sub>; \<and>
                         s \<in> [local.wp R c\<^sub>1
                                Q]\<^sub>s[y\<phi> sub y]}))]\<^sub>;
            {\<triangle> Capture (emptyFrame w) (Seqw (lift\<^sub>c (ts_lang_of_vm_lang c\<^sub>2 w) r w) r)} ?P"
      apply (rule spec_judgement)
          apply (rule seq)
      using If apply fastforce
      using c2 apply fastforce
      using wf apply fastforce
      using wf stabilize_entail apply (clarsimp simp add: Collect_mono_iff le_infI1 stabilize_def; fail)
      apply clarsimp[1] using QUESTION wf stabilize_smaller If.prems(7) apply blast
      (* this goal wants x in [wp c2 Q]s to hold in both cases b and \<not>b. we hypothesise that this
         is possible if the sequential predicate entails the speculative predicate. *)
      using wf by fast

    show ?case using c b s seq
    unfolding prod.case_eq_if by meson
    
  next
    case left1
    have c: "R,G \<turnstile>\<^sub>; [wp R c\<^sub>1 Q]\<^sub>; {c\<^sub>1,r,w} [Q]\<^sub>;" using c1 by auto
    have b: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
      seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (cmp b) [wp R c\<^sub>1 Q]\<^sub>;)) 
        {Basic (liftl (cmp b))} 
          seq_pred_of_vm_pred [wp R c\<^sub>1 Q]\<^sub>;" (is "?R,?G \<turnstile> ?P { ?b } ?Q")
      using cmp_seq st wf by blast
    have b': "?R,?G \<turnstile> seq_pred_of_vm_pred [wp R (If b c\<^sub>1 c\<^sub>2) Q]\<^sub>; {?b} ?Q" using b
      apply (rule conseq) apply (clarsimp simp add: prod.case_eq_if wp.stabilize_def wp_axioms)
      by simp_all
    show ?case using seq c b' by simp
  next
    case rightspec1
    have c: "R,G \<turnstile>\<^sub>; [wp R c\<^sub>2 Q]\<^sub>; {c\<^sub>2,r,w} [Q]\<^sub>;" (is "_,_ \<turnstile>\<^sub>; ?wp {_,_,_} _") using c1 c2 by auto
    have b: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
      seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (ncmp b) ?wp)) 
        {Basic (liftl (ncmp b))} 
          seq_pred_of_vm_pred ?wp" (is "?R,?G \<turnstile> ?P { ?b } ?Q")
      using cmp_seq st If wf by blast

    have s: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
      seq_pred_of_vm_pred 
        [(stabilize\<^sub>L R ([local.wp R c\<^sub>1 Q]\<^sub>s \<inter> [local.wp R c\<^sub>2 Q]\<^sub>s),
                   stabilize R
                    ({s. ev\<^sub>B (varmap_st s) b \<longrightarrow>
                         s \<in> [local.wp R c\<^sub>1 Q]\<^sub>; \<and> s \<in> [local.wp R c\<^sub>2 Q]\<^sub>s[y\<phi> sub y]} \<inter>
                     {s. \<not> ev\<^sub>B (varmap_st s) b \<longrightarrow>
                         s \<in> [local.wp R c\<^sub>2 Q]\<^sub>; \<and>
                         s \<in> [local.wp R c\<^sub>1
                                Q]\<^sub>s[y\<phi> sub y]}))]\<^sub>;
            {\<triangle> Capture (emptyFrame w) (Seqw (lift\<^sub>c (ts_lang_of_vm_lang c\<^sub>1 w) r w) r)} ?P"
      apply (rule spec_judgement)
          apply (rule seq)
      using If apply fastforce
      using c1 c2 apply fastforce
      using wf apply fastforce
      using wf stabilize_entail apply (clarsimp simp add: Collect_mono_iff le_infI1)
      apply (rule stabilize_entail)
        using wf stabilize_entail apply (fast,fast)
      apply (simp add: subset_iff)
      apply (simp, standard, erule stabilizeE)
        using wf apply simp
        apply clarsimp apply (meson QUESTION If.prems(7) in_mono local.wf(1))
      using wf by auto

    show ?case 
    apply (simp add: prod.case_eq_if, intro seq)
      using c apply simp
      using b apply simp
      using s apply simp
    done
  next
    case right1
    then show ?case
    apply (simp add: prod.case_eq_if, intro seq)
      using c1 c2 apply fast
      apply (rule conseq[OF cmp_seq[where ?w=w and ?b="Neg b" and ?Q="[wp R c\<^sub>2 Q]\<^sub>;"]])
      using wf st stabilize_def GG' by auto 
  next
    case leftspec2
    then show ?case 
    proof (simp add: prod.case_eq_if, intro seq; (rule spec_judgement', rule seq)?)
      show "R,G' \<turnstile>\<^sub>s [wp R c\<^sub>1 Q]\<^sub>s {c\<^sub>1,r,w} [Q]\<^sub>s" using c1 by simp
      show "base_rel_frame_id(step\<^sub>t R),base_rel_guar G' w 
                  \<turnstile> spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [wp R c\<^sub>1 Q]\<^sub>s)) w
                    {Basic (liftl (cmp b))} 
                    spec_pred_of_lvm_pred [local.wp R c\<^sub>1 Q]\<^sub>s w"
                    using cmp_spec[of R] wf st by blast
      show "(base_rel_frame_id (step\<^sub>t R)), (base_rel_guar G' w) \<turnstile> (spec_pred_of_lvm_pred [Q]\<^sub>s w) {r} (spec_pred_of_lvm_pred Q' w)"
        using s wf If.prems(1) by linarith
      show "R,G' \<turnstile>\<^sub>s [wp R c\<^sub>2 Q]\<^sub>s  {c\<^sub>2,r,w} [Q]\<^sub>s" using c2 by simp
      show "G' \<subseteq> step G \<inter> step\<^sub>t R" using wf(3) by simp
      show "stabilize\<^sub>L R ([local.wp R c\<^sub>1 Q]\<^sub>s \<inter> [local.wp R c\<^sub>2 Q]\<^sub>s) \<subseteq> stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [local.wp R c\<^sub>1 Q]\<^sub>s)" using stabilize\<^sub>L_def by auto
      show "stabilize\<^sub>L R ([local.wp R c\<^sub>1 Q]\<^sub>s \<inter> [local.wp R c\<^sub>2 Q]\<^sub>s) \<subseteq> [local.wp R c\<^sub>2 Q]\<^sub>s" using local.wf(1) stabilize\<^sub>LE by auto
      show "stable\<^sub>L R (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [local.wp R c\<^sub>1 Q]\<^sub>s))" using local.wf(1) by blast
    qed 
  next
    case left2
    then show ?case
    apply (simp add: prod.case_eq_if, intro seq)
      using c1 c2 apply fast
      apply (rule conseq[OF cmp_spec[where ?Q="[wp R c\<^sub>1 Q]\<^sub>s" and ?w=w]])
      using wf st stabilize\<^sub>L_def by auto
  next
    case rightspec2
    then show ?case 
    proof (simp add: prod.case_eq_if, intro seq; (rule spec_judgement', rule seq)?)
      show "R,G' \<turnstile>\<^sub>s [wp R c\<^sub>1 Q]\<^sub>s  {c\<^sub>1,r,w} [Q]\<^sub>s" using c2 c1 by simp
      show "R,G' \<turnstile>\<^sub>s [wp R c\<^sub>2 Q]\<^sub>s {c\<^sub>2,r,w} [Q]\<^sub>s" using c1 c2 by simp
      show "base_rel_frame_id(step\<^sub>t R),base_rel_guar G' w 
                  \<turnstile> spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [wp R c\<^sub>2 Q]\<^sub>s)) w
                    {Basic (liftl (ncmp b))} 
                    spec_pred_of_lvm_pred [local.wp R c\<^sub>2 Q]\<^sub>s w"
                    using cmp_spec[where ?R=R and ?b="Neg b" and ?w=w] wf st by blast
      show "(base_rel_frame_id (step\<^sub>t R)), (base_rel_guar G' w) \<turnstile> (spec_pred_of_lvm_pred [Q]\<^sub>s w) {r} (spec_pred_of_lvm_pred Q' w)"
        using s wf If.prems(1) by linarith
      show "G' \<subseteq> step G \<inter> step\<^sub>t R" using wf(3) by simp
      show "stabilize\<^sub>L R ([local.wp R c\<^sub>1 Q]\<^sub>s \<inter> [local.wp R c\<^sub>2 Q]\<^sub>s) \<subseteq> stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [local.wp R c\<^sub>2 Q]\<^sub>s)" using stabilize\<^sub>L_def by auto
      show "stabilize\<^sub>L R ([local.wp R c\<^sub>1 Q]\<^sub>s \<inter> [local.wp R c\<^sub>2 Q]\<^sub>s) \<subseteq> [local.wp R c\<^sub>1 Q]\<^sub>s" using local.wf(1) stabilize\<^sub>LE by auto
      show "stable\<^sub>L R (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [local.wp R c\<^sub>2 Q]\<^sub>s))" using local.wf(1) by blast
    qed 
  next
    case right2
    then show ?case
    apply (simp add: prod.case_eq_if, intro seq)
      using c1 c2 apply fast
      apply (rule conseq[OF cmp_spec[where ?Q="[wp R c\<^sub>2 Q]\<^sub>s" and ?w=w]])
      using wf st stabilize\<^sub>L_def by auto
  next
    case st1
    then show ?case apply (simp add: prod.case_eq_if) using wf by auto 
  next
    case st2
    then show ?case apply (simp add: prod.case_eq_if) using wf by auto 
  qed
next
  case (While b Inv Inv\<^sub>s c)
  let ?case_While = ?case
  have nonempty: "[wp R (While b Inv Inv\<^sub>s c) Q]\<^sub>; \<noteq> {}" (* "[wp R (While b Inv Inv\<^sub>s c) Q]\<^sub>s \<noteq> {}" *)
  sorry (* DEFINITELY NOT THE CASE but we will use cases to separate empty and nonempty *)
  have reflexive: "reflexive R" using wf by simp

  have arg_commute: "(A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> A \<Longrightarrow> C)" for A B C by simp

  have assert_nonempty: 
    "(assert a) \<noteq> {} \<Longrightarrow> a" 
    "(assert a) \<inter> b \<noteq> {} \<Longrightarrow> a" 
    "b \<inter> (assert a) \<noteq> {} \<Longrightarrow> a" 
    "x \<in> assert (a) \<Longrightarrow> a"
    for a b x using assert_def by (force, force, force, (auto simp add: assert_def, meson empty_iff))

  have asserts: "Inv\<^sub>s \<subseteq> [Q]\<^sub>s" "Inv \<subseteq> (wp\<^sub>i (ncmp b) [Q]\<^sub>;)" "Inv\<^sub>s \<subseteq> [(wp R c (Inv\<^sub>s, Inv))]\<^sub>s" "Inv \<subseteq> wp\<^sub>i (cmp b) [(wp R c (Inv\<^sub>s, (stabilize R Inv)))]\<^sub>;"
  using nonempty
  apply (all\<open>simp only: wp.simps snd_def case_prod_conv\<close>)
  apply (all\<open>simp only: snd_def[symmetric]\<close>)
  apply (all\<open>drule stabilize_nonempty[OF reflexive]\<close>)
  using assert_nonempty(1) by force+

  have Inv_QUESTION: "Inv \<subseteq> Inv\<^sub>s[y\<phi> sub y]" 
  sorry (* possibly new assert in wp *)

  have st_Inv: 
    "stable\<^sub>t R Inv" "stable\<^sub>L R Inv\<^sub>s" 
    "stable (base_rel_frame_id (step\<^sub>t R)) (spec_pred_of_lvm_pred Inv\<^sub>s w)"
  sorry (* possibly assert stable Inv and stable Invs *)

  have c: "R,G,G' \<turnstile> wp R c Q {c,r,w} Q" using While by simp
  have st: "stable\<^sub>t R [local.wp R c Q]\<^sub>;" "stable\<^sub>L R [local.wp R c Q]\<^sub>s" 
    using While by auto
  have GG': "base_rel_guar G' w \<subseteq> base_rel_guar (step G) w" 
    using wf base_rel_def base_rel_guar_def by auto

  have Inv_ncmp_Q: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> seq_pred_of_vm_pred Inv {Basic (liftl (ncmp b))} seq_pred_of_vm_pred [Q]\<^sub>;"
  proof -
    have 1: "base_rel_frame_id(step\<^sub>t R),base_rel_guar (step G) w 
          \<turnstile> seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (ncmp b) [Q]\<^sub>;)) {Basic (liftl (ncmp b))} seq_pred_of_vm_pred [Q]\<^sub>;"
    apply (rule cmp_seq) using While.prems wf by auto

    show ?thesis
    apply (rule conseq[where ?Q="seq_pred_of_vm_pred [Q]\<^sub>;"])
    using 1 apply simp
    using asserts(2) apply simp
    apply (intro seq_mono)
    using st_Inv(1) apply auto[1] thm stabilize_entail
    apply (rule stabilize_entail[where ?P=Inv])
      using reflexive apply (solves\<open>simp\<close>)
      using reflexive apply (solves\<open>simp\<close>)
      using asserts(2) apply (solves\<open>simp\<close>)
    by simp_all
  qed

  have Invs_ncmp_Qs: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w 
                      \<turnstile> spec_pred_of_lvm_pred Inv\<^sub>s w {Basic (liftl (ncmp b))} spec_pred_of_lvm_pred [Q]\<^sub>s w"
  proof -
    have 1: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w 
             \<turnstile> spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [Q]\<^sub>s)) w {Basic (liftl (ncmp b))} spec_pred_of_lvm_pred [Q]\<^sub>s w"
    apply (rule cmp_spec) using While wf by auto

    show ?thesis 
    apply (rule conseq[OF 1]) 
      apply (rule spec_mono)
        apply (standard, rule stabilize\<^sub>L_entail[where ?P=Inv\<^sub>s])
          using st_Inv apply (simp add: local.wf(1); fail)
          using wf apply fast
          using asserts apply force
    by simp_all
  qed

  have Invs_r: "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile> spec_pred_of_lvm_pred Inv\<^sub>s w {r} spec_pred_of_lvm_pred [Q]\<^sub>s w"
  sorry

  have s': "base_rel_frame_id (step\<^sub>t R),base_rel_guar G' w \<turnstile> spec_pred_of_lvm_pred [(Inv\<^sub>s, Inv)]\<^sub>s w {r} spec_pred_of_lvm_pred Q' w"
  sorry

  have Invs_c_Invs: "R,G' \<turnstile>\<^sub>s Inv\<^sub>s {c,r,w} Inv\<^sub>s"
  using While.hyps asserts(3)
  proof -
    have "(R,G,G' \<turnstile> local.wp R c (Inv\<^sub>s, Inv) {c,r,w} (Inv\<^sub>s,Inv)) \<and> stable\<^sub>t R [local.wp R c (Inv\<^sub>s, Inv)]\<^sub>; \<and> stable\<^sub>L R [local.wp R c (Inv\<^sub>s, Inv)]\<^sub>s"
    apply (rule While.hyps)
      using s' apply simp
      defer defer
      using While.prems apply auto[3]
      apply (simp add: \<open>Inv \<subseteq> Inv\<^sub>s[y\<phi> sub y]\<close>)
      using st_Inv by simp+
    thus ?thesis by (meson asserts(3) conseq exI_realizer spec_mono subset_refl)
  qed

  have FST3: "A \<and> B \<and> C \<Longrightarrow> A" for A B C by simp
  have FST2: "A \<and> B \<Longrightarrow> A" for A B by simp
  have SND2: "A \<and> B \<Longrightarrow> B" for A B by simp

  have wpcInv_c_Inv: "R,G \<turnstile>\<^sub>; [wp R c (Inv\<^sub>s,Inv)]\<^sub>; {c,r,w} [(Inv\<^sub>s,Inv)]\<^sub>;"
  apply (rule FST2[OF FST3[OF While.hyps]])
    using s' apply fast
    using st_Inv apply simp
    using st_Inv apply simp
    using While Inv_QUESTION apply simp_all
  done

  have Inv_b_wpcInv: "base_rel_frame_id (step\<^sub>t R),base_rel_guar (step G) w
        \<turnstile> seq_pred_of_vm_pred Inv {Basic (liftl (cmp b))} seq_pred_of_vm_pred [local.wp R c (Inv\<^sub>s, Inv)]\<^sub>;"
  sorry

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

  show ?case
  apply (simp del: wp.simps)
  apply (intro conjI)
    subgoal 
    apply (intro seq choice_if)
      using Inv_ncmp_Q apply simp
      apply (rule spec_judgement)
        apply (intro seq)
          using Invs_r apply simp
          using Inv_Iterc_Inv apply simp
          using Invs_c_Invs apply simp
        using wf apply simp
        using subset_refl apply fast
        using Inv_QUESTION apply simp
        using st_Inv apply simp
      using Inv_ncmp_Q apply simp
      apply (rule conseq[OF Inv_IterSpec_Inv])
        using local.wf(1) st_Inv(1) stabilize_entail apply fastforce
        apply simp_all[3]
    by -
    subgoal
    apply (intro seq choice_if)
      using Invs_ncmp_Qs apply simp1
      apply (rule spec_judgement')
        subgoal sorry
        subgoal sorry
        subgoal sorry
        subgoal sorry
        subgoal sorry
      using Invs_ncmp_Qs apply simp1
      apply (simp add: stable_stabilize\<^sub>L_id[OF reflexive st_Inv(2)], rule loop) 
        using st_Inv apply simp1
        apply (rule choice_if)
          apply (rule seq, rule seq)
            using Invs_c_Invs apply simp1
            subgoal sorry
            subgoal sorry
          subgoal sorry
    by -
    subgoal using wf by auto 
    subgoal using wf by auto
  done      
    
  thm While
  thm loop
  thm spec_judgement' seq While.prems(1) c
  find_theorems Choice name: "if"
  find_theorems Capture name: "spec"
next
  case (DoWhile x1 x2 c x4)
  then show ?case sorry
qed


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
