theory SimAsm_Rules
  imports SimAsm_WP SimAsm_Semantics "../Soundness" "HOL-Eisbach.Eisbach"
begin

subsection \<open>Conversion between tstack and varmap.\<close>

definition vm_of_ts :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) varmap'" 
  where "vm_of_ts s \<equiv> \<lparr> varmap_st = tlookup s, \<dots> = taux s\<rparr>"

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
  
lift_definition ts_pred_of_vm_pred :: "('r,'v,'a) varmap' pred \<Rightarrow> ('r,'v,'a) tstack pred" is
  "\<lambda>v. vm_of_ts -` v".

lift_definition vm_pred_of_ts_pred :: "('r,'v,'a) tstack pred \<Rightarrow> ('r,'v,'a) varmap' pred" is
  "\<lambda>S. vm_of_ts ` S".

lift_definition vm_rel_of_ts_rel :: "('r,'v,'a) tstack rel \<Rightarrow> ('r,'v,'a) varmap' rel" is 
  "\<lambda>x. {(vm_of_ts s,vm_of_ts s') | s s'. (s,s') \<in> x}".

lift_definition ts_rel_of_vm_rel :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel" is 
  "\<lambda>x. {(s,s') | s s'. (vm_of_ts s,vm_of_ts s') \<in> x}".

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
  "\<lambda>P w. {ts | ts. mk_lvarmap (tstack_base ts) (vm_of_ts ts) \<in> P \<and> ts_is_spec ts \<and> w = topcapped ts \<and> w = capped ts}".

lift_definition spec_pred_of_lvm_pred2 :: "('r,'v,'a) lvarmap' pred \<Rightarrow> ('r,'v,'a) tstack pred" is
  "\<lambda>P. {ts | ts. mk_lvarmap (tstack_base ts) (vm_of_ts ts) \<in> P \<and> ts_is_spec ts}".

fun op_vc
  where
    "op_vc (leak v e) pred = {ts. mk_lvarmap (tstack_base ts) (vm_of_ts ts) \<in> pred}" |
    "op_vc op pred = {ts. ts_is_seq ts \<longrightarrow> mk_lvarmap (tstack_base ts) (vm_of_ts ts) \<in> pred}"

fun ts_lang_of_vm_lang :: "('r,'v,('r,'v,'a)varmap',('r,'v,'a)lvarmap','a) lang \<Rightarrow> ('r, 'v, ('r, 'v, 'a) tstack,('r, 'v, 'a) tstack, 'a) lang" where
  "ts_lang_of_vm_lang (Skip) = Skip " |
  "ts_lang_of_vm_lang (Op pred op auxfn) = Op (op_vc op pred) op (auxfn \<circ> vm_of_ts)" |
  "ts_lang_of_vm_lang (SimAsm.lang.Seq a b) = SimAsm.lang.Seq (ts_lang_of_vm_lang a) (ts_lang_of_vm_lang b) " |
  "ts_lang_of_vm_lang (If c t f) = If c (ts_lang_of_vm_lang t) (ts_lang_of_vm_lang f)" |
  "ts_lang_of_vm_lang (While b Imix Ispec c) = While b (ts_pred_of_vm_pred Imix) (spec_pred_of_lvm_pred2 Ispec) (ts_lang_of_vm_lang c) " |
  "ts_lang_of_vm_lang (DoWhile Imix Ispec c b) = DoWhile (ts_pred_of_vm_pred Imix) (spec_pred_of_lvm_pred2 Ispec) (ts_lang_of_vm_lang c) b "

text \<open>Constrain the base frame of a stack with a relation\<close>
definition base_rel :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel"
  where "base_rel R \<equiv> {(ts,ts'). (tstack_base ts,tstack_base ts') \<in> R}"

text \<open>Constrain the base frame of a stack with a relation and all subsequent frames with id\<close>
definition base_rel_rely :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel"
  where "base_rel_rely R \<equiv> {(ts,ts') \<in> base_rel R. tstack_upper ts = tstack_upper ts'}"

definition id_on
  where "id_on w G \<equiv> { (ts,\<lparr>varmap_st = \<lambda>v. if v \<in> w then varmap_st ts v else varmap_st ts' v, 
                            \<dots> = varmap_rec.more ts\<rparr>) | ts ts'. (ts,ts') \<in> G }"

text \<open>
Constrain the base frame of a stack with a relation, all intermediate frames with id, 
but only ensure the topmost frame retains its capture set\<close>
definition base_rel_guar :: "('r,'v,'a) varmap' rel \<Rightarrow> 'r set \<Rightarrow> ('r,'v,'a) tstack rel"
  where "base_rel_guar G w \<equiv> {(ts,ts') \<in> base_rel G. ts_is_seq ts \<and> ts_is_seq ts'} \<union>
                              {(ts,ts') \<in> base_rel (id_on w G). ts_is_spec ts \<and>
                                                    tstack_mid ts = tstack_mid ts' \<and> 
                                                    topcapped ts = topcapped ts' \<and>
                                                    tstack_len ts = tstack_len ts' }"

text \<open>
The judgement over the sequential program behaviour, structured with:
  \<^item> A state that has no speculation frames
  \<^item> A rely that constrains the base frame, will not modify the stack structure, and enforces id on each frame's contents
  \<^item> A guarantee that preserves stack structure and constrains the base frame, but will
    do anything if there is a speculative frame.
\<close>
abbreviation seq_rule ("_,_ \<turnstile>\<^sub>; _ {_,_,_} _" [20,0,0,0,0,0,20] 20)
  where "seq_rule R G P c r w Q \<equiv> 
          (base_rel_rely (step\<^sub>t R)), (base_rel_guar (step G) w) \<turnstile> 
            (seq_pred_of_vm_pred P) {lift\<^sub>c (ts_lang_of_vm_lang c) r w} (seq_pred_of_vm_pred Q)"

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
          (base_rel_rely (step\<^sub>t R)), (base_rel_guar (step G) w) \<turnstile> 
            (spec_pred_of_lvm_pred P w) {lift\<^sub>c (ts_lang_of_vm_lang c) r w} (spec_pred_of_lvm_pred Q w)"

text \<open>Combine the above into a single rule\<close>
abbreviation lifted_abv ("_,_ \<turnstile> _ {_,_,_} _" [20,0,0,0,0,0,20] 20)
  where "lifted_abv R G P c r w Q \<equiv> (seq_rule R G [P]\<^sub>; c r w [Q]\<^sub>; \<and> spec_rule R G [P]\<^sub>s c r w [Q]\<^sub>s)"

text \<open>Define validity in terms of the sequential rule\<close>
abbreviation validity_abv ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0] 45) 
  where "validity_abv c P R G Q \<equiv> 
    validity (lift\<^sub>c (ts_lang_of_vm_lang c) com.Nil (wr\<^sub>l c)) (seq_pred_of_vm_pred P) 
      (base_rel_rely (step\<^sub>t R)) (base_rel_guar (step G) (wr\<^sub>l c)) (seq_pred_of_vm_pred Q)" 

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
  "(x \<in> spec_pred_of_lvm_pred P w) = (mk_lvarmap (tstack_base x) (vm_of_ts x) \<in> P \<and> ts_is_spec x \<and> w = capped x \<and> w = topcapped x)"
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

lemma  butlast_captured:
"Is_tstack m \<Longrightarrow>
       Is_tstack m' \<Longrightarrow>
       butlast m = butlast m' \<Longrightarrow>
       Collect (captured m) = Collect (captured m')"
proof (induct arbitrary: m' rule: Is_tstack_induct)
  case (Base x)
  then show ?case by (cases m'; auto split: if_splits simp: captured_def)
next
  case (Frame x xs)
  then show ?case by (cases m'; auto split: if_splits simp: captured_def)
qed

lemma  butlast_topcap:
  "Is_tstack m \<Longrightarrow>
       Is_tstack m' \<Longrightarrow>
       butlast m = butlast m' \<Longrightarrow>
       Collect (topcap m) = Collect (topcap m')"
  by (auto split: if_splits list.splits simp: topcap_def)

lemma tstack_upper_captured_eq:
  "tstack_upper m = tstack_upper m' \<Longrightarrow> capped m = capped m'"
  unfolding tstack_upper_def apply transfer using butlast_captured by auto

lemma tstack_upper_topcapped_eq:
  "tstack_upper m = tstack_upper m' \<Longrightarrow> topcapped m = topcapped m'"
  unfolding tstack_upper_def apply transfer using butlast_topcap by auto


lemma stable\<^sub>L [intro]:
  assumes "stable\<^sub>L R P"
  shows "stable (base_rel_rely (step\<^sub>t R)) (spec_pred_of_lvm_pred P w)"
  using assms
  unfolding stable_def stable\<^sub>L_def spec_pred_of_lvm_pred_def base_rel_rely_def
  apply clarsimp
  apply (intro conjI)
     prefer 2
  apply (metis tstack_upper_len_eq)
  prefer 3
  using tstack_upper_captured_eq 
    apply blast
  prefer 2
  using tstack_upper_topcapped_eq apply blast

  apply (subgoal_tac "(glb \<lparr>varmap_st = \<lambda>v. varmap_st (mk_lvarmap (tstack_base m) (vm_of_ts m)) (Gl v),
                         \<dots> = fst (varmap_rec.more (mk_lvarmap (tstack_base m) (vm_of_ts m)))\<rparr>,
                  glb \<lparr>varmap_st = \<lambda>v. varmap_st (mk_lvarmap (tstack_base m') (vm_of_ts m')) (Gl v),
                         \<dots> = fst (varmap_rec.more (mk_lvarmap (tstack_base m') (vm_of_ts m')))\<rparr>)
                 \<in> R \<and>
                 rg \<lparr>varmap_st = \<lambda>v. varmap_st (mk_lvarmap (tstack_base m) (vm_of_ts m)) (Gl v),
                       \<dots> = fst (varmap_rec.more (mk_lvarmap (tstack_base m) (vm_of_ts m)))\<rparr> =
                 rg \<lparr>varmap_st = \<lambda>v. varmap_st (mk_lvarmap (tstack_base m') (vm_of_ts m')) (Gl v),
                       \<dots> = fst (varmap_rec.more (mk_lvarmap (tstack_base m') (vm_of_ts m')))\<rparr> \<and>
                 (\<lambda>v. varmap_st (mk_lvarmap (tstack_base m) (vm_of_ts m)) (Ul v)) = (\<lambda>v. varmap_st (mk_lvarmap (tstack_base m') (vm_of_ts m')) (Ul v)) \<and>
                 snd (varmap_rec.more (mk_lvarmap (tstack_base m) (vm_of_ts m))) = snd (varmap_rec.more (mk_lvarmap (tstack_base m') (vm_of_ts m')))")
   apply blast
  apply (intro conjI)
  apply (auto simp: base_rel_def step\<^sub>t_def)[1]
  apply (metis varmap_rec.surjective)
  apply (auto simp: base_rel_def step\<^sub>t_def)[1]
  apply (metis varmap_rec.surjective)



  sorry (* Problem 1: Stability in the speculative context doesn't make sense *)

lemma stable_ts [intro]: 
  "stable R P \<Longrightarrow> stable (base_rel_rely R) (seq_pred_of_vm_pred P)"
  apply (auto simp: stable_def base_rel_rely_def base_rel_def )
  apply (metis One_nat_def tstack_base_vm_of_ts tstack_upper_len_eq)
  apply (metis tstack_upper_len_eq)
  done

lemma base_rel_guarI:
  assumes "ts_is_seq a \<Longrightarrow> ts_is_seq b \<Longrightarrow> (tstack_base a, tstack_base b) \<in> G"
  assumes "ts_is_spec a \<Longrightarrow> (tstack_base a, tstack_base b) \<in> id_on w G"
  assumes "topcapped a = topcapped b"
  assumes "tstack_mid a = tstack_mid b"
  assumes "tstack_len a = tstack_len b"
  shows "(a,b) \<in> base_rel_guar G w"
  using assms unfolding base_rel_guar_def base_rel_def
  by fastforce

lemma [elim!]:
  assumes "(tstack_push m s, tstack_push ma sa) \<in> base_rel G"
  obtains "(m, ma) \<in> base_rel G"
  using assms unfolding base_rel_def by auto

(* MOVE *)
lemma [intro]:
  assumes "tstack_upper m = tstack_upper m'"
  shows "tstack_upper (tstack_push m s) = tstack_upper (tstack_push m' s)"
  using assms unfolding tstack_upper_def by transfer auto

lemma [simp]:
  "tstack_len m = 1 \<Longrightarrow> tstack_upper m = []"
  unfolding tstack_upper_def by transfer (case_tac m; simp)


lemma [simp]:
  "tstack_len x = Suc 0 \<Longrightarrow> tcaptured x v = False"
  by transfer (case_tac x; auto simp: captured_def)

lemma [intro]:
  "ttopcap x x11 \<Longrightarrow> tcaptured x x11"
  by transfer (case_tac x; auto simp: captured_def topcap_def split: list.splits)

lemma [simp]:
  "ttopcap (tauxupd x f) = ttopcap x"
  apply transfer
  unfolding topcap_def auxupd_def
  by (auto split: list.splits simp: fun_eq_iff)

lemma [simp]:
  "ttopcap (tupdate x  y e) = ttopcap x"
  apply transfer
  unfolding topcap_def auxupd_def
  by (auto split: list.splits simp: fun_eq_iff)

lemma upper_mid:
  "tstack_upper a = tstack_upper b \<Longrightarrow>
           tstack_mid a = tstack_mid b"
  by (auto simp: tstack_upper_def tstack_mid_def split: list.splits if_splits)

lemma tstack_mid_tauxupd [simp]:
  "tstack_mid (tauxupd x f) = tstack_mid x"
  unfolding tstack_mid_def
  by transfer (auto simp: fun_eq_iff auxupd_def split: list.splits)

lemma tstack_mid_tupdate_base[simp]:
  "tstack_len x = Suc 0 \<Longrightarrow> tstack_mid (tupdate x y e) = tstack_mid x"
  unfolding tstack_mid_def
  by transfer (auto split: list.splits)

lemma stack_mid_update_nocap:
  "Is_tstack (x21 # x22) \<Longrightarrow>
       \<not> captured (x21 # x22) y \<Longrightarrow>
       butlast (update x22 y e) = butlast x22"
proof (induct "x21 # x22" arbitrary: x21 x22 rule: Is_tstack_induct)
  case (Base x)
  then show ?case by auto
next
  case (Frame x xs)
  then show ?case by (cases xs; auto simp: captured_def)
qed

lemma tstack_mid_tupdate_nocap[simp]:
  "\<not>tcaptured x y \<Longrightarrow> tstack_mid (tupdate x y e) = tstack_mid x"
  unfolding tstack_mid_def
  apply transfer 
  apply (auto split: list.splits)
  using stack_mid_update_nocap by force

lemma tstack_mid_tupdate_topcap[simp]:
  "ttopcap x y \<Longrightarrow> tstack_mid (tupdate x y e) = tstack_mid x"
  unfolding tstack_mid_def
  by transfer (auto split: list.splits simp: topcap_def)


lemma [simp]:
  "tstack_mid (tstack_push m s) = tstack_upper m"
  unfolding tstack_mid_def tstack_upper_def
  apply transfer
  apply (auto split: list.splits)
  done

lemma [simp]:
  "ttopcap (tstack_push m (emptyFrame w)) x = (x \<in> w)"
  by transfer
   (auto simp: topcap_def split: list.splits)

lemma [elim!]:
  assumes "[] = tstack_upper b"
  obtains "tstack_len b = 1"
  using assms unfolding tstack_upper_def apply (transfer)
  apply (case_tac b; auto split: if_splits)
  done

(* MOVE *)

lemma compat_example:
  assumes "G \<subseteq> R"
  shows "base_rel_guar G w \<subseteq> guard {t. tstack_len t = 1} (base_rel_rely R)"
  using assms by (auto simp: base_rel_guar_def base_rel_rely_def base_rel_def guard_def)

lemma base_rel:
  assumes "id_on w G \<subseteq> G"
  shows "base_rel_rely (id_on w G) \<subseteq> base_rel_guar G w"
  using assms
  apply (auto simp: base_rel_rely_def base_rel_guar_def)
               apply (simp add: base_rel_def subsetD)
  using upper_mid apply blast
  using tstack_upper_topcapped_eq apply force
  using tstack_upper_topcapped_eq apply force
  using tstack_upper_len_eq apply blast
    using upper_mid apply blast
  using tstack_upper_topcapped_eq apply force
  using tstack_upper_topcapped_eq apply force
  using tstack_upper_len_eq apply blast
    using upper_mid apply blast
  using tstack_upper_topcapped_eq apply force
  using tstack_upper_topcapped_eq apply force
  using tstack_upper_len_eq apply blast
  done

subsection \<open>@{term st_beh\<^sub>i} Invariants\<close>

lemma st_beh\<^sub>i_tstack_len [simp]:
  assumes "(x, y) \<in> st_beh\<^sub>i op"
  shows "tstack_len x = tstack_len y"
  using assms by (cases op; auto)

lemma st_beh\<^sub>i_capped [simp]:
  assumes "(x, y) \<in> st_beh\<^sub>i op"
  shows "capped x = capped y"
  using assms by (cases op; auto)

lemma st_beh\<^sub>i_ttopcap [simp]:
  "(x, y) \<in> beh (lift\<^sub>b v op f) \<Longrightarrow> ttopcap x = ttopcap y"
  by (cases op; auto simp: liftg_def)

lemma id_on_refl :
  assumes "(x,x) \<in> R"
  shows "(x,x) \<in> (id_on w R)"
  using assms unfolding id_on_def 
  apply auto
  apply (rule exI)
  apply (intro conjI)
  prefer 2
   apply blast
  apply auto
  done

subsection \<open>Atomic Judgements\<close>

text \<open>A method to force equivalence over two large state computations, useful when the rewrite engine gives up\<close>
method force_eq =
  (rule refl) |
  (match conclusion in "x \<in> Q" for x Q \<Rightarrow>
     \<open>match premises in A: "y \<in> Q" for y \<Rightarrow> 
      \<open>rule subst[of _ _ "\<lambda>m. m \<in> Q", OF _ A]\<close>\<close>) |
     (match conclusion in "(x :: ('x, 'y) prod) = y" for x y \<Rightarrow> 
     \<open>rule prod_eqI; simp?\<close>) |
  (match conclusion in "(x :: ('x, 'y, 'z) varmap_rec_scheme) = y" for x y \<Rightarrow> 
     \<open>rule varmap_rec.equality; simp?\<close>) |
  (match conclusion in "(x :: 'x \<Rightarrow> 'y) = y" for x y \<Rightarrow> 
     \<open>(clarsimp simp: fun_eq_iff split: label.splits)\<close>) |
  (match conclusion in "f (a :: ('r, 'v, 'a) varmap_rec_scheme) = f b" for f a b \<Rightarrow>
    \<open>rule arg_cong[where ?f=f]\<close>)

lemma atomic_seq:
  assumes r: "wellformed R G"
  assumes g: "v\<^sup>U \<subseteq> guar (wp\<^sub>i op o wp\<^sub>a f) (step G)"
  assumes g': "v \<subseteq> guar (wp\<^sub>i\<^sub>s op) (gl_lift_rel (step G))"
  assumes s: "stable (step\<^sub>t R) Q"
  assumes w: "wr op \<subseteq> w" "lk op \<inter> w = {}"
  shows "R,G \<turnstile>\<^sub>; stabilize R (v\<^sup>U \<inter> wp\<^sub>i op (wp\<^sub>a f Q)) {Op v op f,r,w} Q"
  unfolding ts_lang_of_vm_lang.simps lift\<^sub>c.simps
proof (intro basic atomicI, goal_cases st gu spre spost)
  case st
  let ?lhs = "seq_pred_of_vm_pred (stabilize R (v\<^sup>U \<inter> wp\<^sub>i op (wp\<^sub>a f Q)))"
  have vc: "?lhs \<subseteq> vc (lift\<^sub>b (op_vc op v) op (f \<circ> vm_of_ts))"
    using r by (cases op) (auto elim: stabilizeE intro!: seq_ts_mono simp: liftg_def u_lvarmap)
  have wp: "?lhs \<subseteq> {m. \<forall>m'. (m, m') \<in> beh (lift\<^sub>b (op_vc op v) op (f \<circ> vm_of_ts)) \<longrightarrow> 
                      vm_of_ts m' \<in> Q \<and> ts_is_seq m'}"
    using r by (cases op) (auto elim!: stabilizeE simp: liftg_def wp\<^sub>a.simps)
  show ?case using vc wp by (auto simp: wp_def)
next
  case gu
  thus ?case using g r w 
    apply (cases op) 
    apply (auto intro!: base_rel_guarI id_on_refl 
                  simp: wp\<^sub>a.simps guar_def wp\<^sub>r_def liftg_def u_lvarmap 
                 split: if_splits)

    (* leak argument under spec - difficult automatic discovery of witness *)
    apply (subgoal_tac "(
      \<lparr>varmap_st = varmap_st (tstack_base x), \<dots> = varmap_rec.more (tstack_base x)\<rparr>,
      \<lparr>varmap_st = \<lambda>v. if v = x31 then ev\<^sub>E (varmap_st (mk_lvarmap (tstack_base x) (vm_of_ts x)) \<circ> Ul) x32
                        else varmap_st (mk_lvarmap (tstack_base x) (vm_of_ts x)) (Gl v),
                    \<dots> = varmap_rec.more (tstack_base x)\<rparr>)
                \<in> (step G)")
    apply (simp add: id_on_def)
    apply (intro exI conjI)
    prefer 2
    apply force_eq+
    using g' by (auto simp: gl_lift_rel_def guar_def wp\<^sub>r_def)
next
  case spre
  thus ?case using r by blast
next
  case spost
  thus ?case using s by blast
qed

lemma atomic_spec:
  assumes r: "wellformed R G"
  assumes g: "v\<^sup>U \<subseteq> guar (wp\<^sub>i op o wp\<^sub>a f) (step G)"
  assumes g': "v \<subseteq> guar (wp\<^sub>i\<^sub>s op) (gl_lift_rel (step G))"
  assumes s: "stable\<^sub>L R Q"
  assumes w: "wr op \<subseteq> w" "lk op \<inter> w = {}"
  shows "R,G \<turnstile>\<^sub>s (stabilize\<^sub>L R (v \<inter> wp\<^sub>i\<^sub>s op (wp\<^sub>i\<^sub>a f Q))) {Op v op f,r,w} Q"
  unfolding ts_lang_of_vm_lang.simps lift\<^sub>c.simps
proof (intro basic impI allI conjI atomicI, goal_cases st gu spre spost)
  case st
  let ?lhs = "spec_pred_of_lvm_pred (stabilize\<^sub>L R (v \<inter> wp\<^sub>i\<^sub>s op (wp\<^sub>i\<^sub>a f Q))) w"
  have vc: "?lhs \<subseteq> vc (lift\<^sub>b (op_vc op v) op (f \<circ> vm_of_ts))"
    using r w by (cases op) (auto elim: stabilize\<^sub>LE intro!: spec_ts_mono simp: liftg_def)
  have wp: "?lhs \<subseteq> {m. \<forall>m'. (m, m') \<in> beh (lift\<^sub>b (op_vc op v) op (f \<circ> vm_of_ts)) \<longrightarrow>
                mk_lvarmap (tstack_base m') (vm_of_ts m') \<in> Q \<and> ts_is_spec m' \<and> capped m = capped m' \<and> topcapped m = topcapped m'}"
    using r w by (cases op; auto elim!: stabilize\<^sub>LE simp: wp\<^sub>a.simps liftg_def) force_eq+
  show ?case using vc inv wp by (auto simp: wp_def)
next
  case gu
  thus ?case using g r w 
    apply (cases op) 
    apply (auto intro!: base_rel_guarI id_on_refl 
                  simp: wp\<^sub>a.simps guar_def wp\<^sub>r_def liftg_def u_lvarmap 
                 split: if_splits)

    (* leak argument under spec - difficult automatic discovery of witness *)
    apply (subgoal_tac "(
      \<lparr>varmap_st = varmap_st (tstack_base x), \<dots> = varmap_rec.more (tstack_base x)\<rparr>,
      \<lparr>varmap_st = \<lambda>v. if v = x31 then ev\<^sub>E (varmap_st (mk_lvarmap (tstack_base x) (vm_of_ts x)) \<circ> Ul) x32
                        else varmap_st (mk_lvarmap (tstack_base x) (vm_of_ts x)) (Gl v),
                    \<dots> = varmap_rec.more (tstack_base x)\<rparr>)
                \<in> (step G)")
    apply (simp add: id_on_def)
    apply (intro exI conjI)
    prefer 2
    apply force_eq+
    using g' by (auto simp: gl_lift_rel_def guar_def wp\<^sub>r_def)
next
  case spre
  thus ?case using r by blast
next
  case spost
  then show ?case using s by blast
qed

lemma cmp_seq:
  assumes r: "wellformed R G"
  assumes s: "stable\<^sub>t R Q"
  shows "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
          seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (cmp b) Q)) {Basic (liftl (cmp b))} seq_pred_of_vm_pred Q"
  unfolding ts_lang_of_vm_lang.simps lift\<^sub>c.simps liftl_def
proof (intro basic conjI atomicI, goal_cases st gu  spre spost )
  case st
  thus ?case using r by (auto simp: wp_def elim!: stabilizeE)
next
  case gu
  thus ?case using r by (auto intro!: base_rel_guarI id_on_refl  simp: guar_def reflexive_def step_def)
next
  case spre
  thus ?case using r by blast
next
  case spost
  thus ?case using s by blast
qed

lemma cmp_spec:
  assumes r: "wellformed R G"
  assumes s: "stable\<^sub>L R Q"
  shows "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
          spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) Q)) w {Basic (liftl (cmp b))} spec_pred_of_lvm_pred Q w"
  unfolding ts_lang_of_vm_lang.simps lift\<^sub>c.simps liftl_def
proof (intro basic conjI atomicI, goal_cases st gu  spre spost )
  case st
  thus ?case using r by (auto simp: wp_def elim!: stabilize\<^sub>LE)
next
  case gu
  thus ?case using r by (auto intro!: base_rel_guarI id_on_refl  simp: guar_def reflexive_def step_def )
next
  case spre
  thus ?case using r by blast
next
  case spost
  thus ?case using s by blast
qed


lemma basic_wp:
  assumes r: "wellformed R G" 
  assumes g: "v\<^sup>U \<subseteq> guar (wp\<^sub>i op o wp\<^sub>a f) (step G)"
  assumes g': "v \<subseteq> guar (wp\<^sub>i\<^sub>s op) (gl_lift_rel (step G))"
  assumes s: "stable (step\<^sub>t R) [Q]\<^sub>;" "stable\<^sub>L R [Q]\<^sub>s"
  assumes w: "wr op \<subseteq> w" "lk op \<inter> w = {}"
  shows "R,G \<turnstile> (wp R (Op v op f) Q) {Op v op f,r,w} Q"
proof ((intro conjI; simp), goal_cases seq spec)
  case seq
  then show ?case using atomic_seq[OF r(1) g g' s(1) w] 
    by (cases Q, simp)
next
  case spec
  then show ?case using atomic_spec[OF r g g' s(2) w] 
    by (cases Q, simp)
qed

subsection \<open>Frame Reasoning\<close>

lemma base_rel_guarE:
  assumes "(tstack_push m s, b) \<in> base_rel_guar G w"
  obtains m' s' where "b = tstack_push m' s'" "(m,m') \<in> base_rel_rely (id_on w G)"
  using assms 
proof -
  have "tstack_len (tstack_push m s) = tstack_len b" using assms base_rel_guar_def 
    by auto
  hence "tstack_len b \<noteq> 1" by auto
  then obtain m' s where b: "b = tstack_push m' s" using is_spec_push by blast
  hence "(m,m') \<in> base_rel_rely (id_on w G)" using assms 
    unfolding base_rel_guar_def base_rel_rely_def base_rel_def 
    by auto
  thus ?thesis using b that by auto
qed 

lemma mem_restrict:
  assumes "P \<subseteq> P'\<^sup>U"
  assumes "m \<in> P"
  shows "mk_lvarmap m m \<in> P'"
proof -
  obtain x where x: 
      "\<forall>v. varmap_st x (Gl v) = varmap_st x (Ul v)" "x \<in> P'"
      "fst (varmap_rec.more x) = snd (varmap_rec.more x)"
      "m = \<lparr>varmap_st = \<lambda>v. varmap_st x (Ul v), \<dots> = fst (varmap_rec.more x)\<rparr>"
    using assms by (auto simp: restrict_pred_def image_def)
  have "x = mk_lvarmap m m" 
    apply (auto intro: varmap_rec.equality simp: x fun_eq_iff split: label.splits) 
    apply force_eq+
    using x(1) apply blast
    apply (cases "varmap_rec.more x"; auto)
    using x(3) by simp
  thus ?thesis using x by auto
qed

text \<open>
Lower a speculative judgement across the introduction of an empty frame.
\<close>
lemma spec_to_seq:
  assumes "base_rel_rely R, base_rel_guar G w \<turnstile> 
            (spec_pred_of_lvm_pred P' w) {r} (spec_pred_of_lvm_pred Q w)"
  assumes "P \<subseteq> P'\<^sup>U"
  shows "pushrelSame (base_rel_rely R),pushrelAll (base_rel_rely (id_on w G)) \<turnstile> 
          pushpred (emptyFrame w) (seq_pred_of_vm_pred P) {r} pushpredAll UNIV"
  using assms(1)
proof (rule conseq, goal_cases pre rely guar post)
  case pre
  then show ?case unfolding pushpred_def using mem_restrict[OF assms(2)] by auto
next
  case rely
  then show ?case unfolding pushrelSame_def base_rel_rely_def base_rel_def by auto
next
  case guar
  show ?case by (auto simp: pushrelAll_def elim!: base_rel_guarE) fast
next
  case post
  then show ?case by (auto intro: is_spec_push simp: pushpredAll_def mk_lvarmap_def)
qed 

lemma spec_to_spec:
  assumes "base_rel_rely R, base_rel_guar G w \<turnstile> 
            (spec_pred_of_lvm_pred P' w) {r} (spec_pred_of_lvm_pred Q w)"
  assumes "P \<subseteq> P'"
  shows "pushrelSame (base_rel_rely R),pushrelAll (base_rel_rely (id_on w G)) \<turnstile> 
          pushpred (emptyFrame w) (spec_pred_of_lvm_pred P w) {r} pushpredAll UNIV"
  using assms(1)
proof (rule conseq, goal_cases pre rely guar post)
  case pre
  then show ?case unfolding pushpred_def using assms(2) by auto
next
  case rely
  then show ?case unfolding pushrelSame_def base_rel_rely_def base_rel_def by auto
next
  case guar
  show ?case by (auto simp: pushrelAll_def elim!: base_rel_guarE) fast
next
  case post
  then show ?case by (auto intro: is_spec_push simp: pushpredAll_def mk_lvarmap_def)
qed 

lemma stable_conseqI' [intro]:
  assumes "stable R' P" "Id_on P O R \<subseteq> R'"
  shows "stable R P"
  using assms rtrancl_mono unfolding stable_def by blast

lemma spec_judgement:
  assumes spec: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> spec_pred_of_lvm_pred P' w {r} spec_pred_of_lvm_pred Q' w"
  assumes wf: "id_on w (step G) \<subseteq> step\<^sub>t R" (is "?G \<subseteq> ?R") "id_on w (step G) \<subseteq> step G"

  assumes pred: "P \<subseteq> Q" "P \<subseteq> P'\<^sup>U"
  assumes st: "stable\<^sub>t R Q"

  shows "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> seq_pred_of_vm_pred P {\<triangle> Capture (emptyFrame w) r} seq_pred_of_vm_pred Q"
proof -

  text \<open>Speculative behaviour is stronger than the concrete rely, given initial state is not speculative\<close>
  have m: "base_rel_rely ?G \<subseteq> base_rel_rely ?R" 
    using wf by (auto simp: base_rel_guar_def base_rel_def base_rel_rely_def)

  have st: "stable (base_rel_rely (step\<^sub>t R)) (seq_pred_of_vm_pred Q)"
    using st by blast

  have "base_rel_rely (step\<^sub>t R),base_rel_rely ?G \<turnstile> 
      seq_pred_of_vm_pred P {\<triangle> Capture (emptyFrame w) r} seq_pred_of_vm_pred Q"
  proof (rule interr)
    show "seq_pred_of_vm_pred P \<subseteq> seq_pred_of_vm_pred Q" using pred spec_mono by force
  next
    show "stable (base_rel_rely (step\<^sub>t R)) (seq_pred_of_vm_pred Q)" using st by blast
  next
    show "stable (base_rel_rely ?G) (seq_pred_of_vm_pred Q)" using st m by blast
  next
    show "base_rel_rely (step\<^sub>t R),base_rel_rely ?G \<turnstile> 
            seq_pred_of_vm_pred P {Capture (emptyFrame w) r} UNIV" 
      using spec pred(2) by (rule capture[OF spec_to_seq])
  qed

  hence "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
      seq_pred_of_vm_pred P {\<triangle> Capture (emptyFrame w) r} seq_pred_of_vm_pred Q"
    apply (rule conseq)
       apply blast+
    using wf(2)
    apply (rule base_rel)
    apply blast
    done

  thus ?thesis by blast
qed

lemma spec_judgement':
  assumes spec: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> spec_pred_of_lvm_pred P' w {r} spec_pred_of_lvm_pred Q' w"
  assumes wf: "id_on w (step G) \<subseteq> step\<^sub>t R" (is "?G \<subseteq> ?R") "id_on w (step G) \<subseteq> step G"
  assumes pred: "P \<subseteq> Q" "P \<subseteq> P'"
  assumes st: "stable\<^sub>L R Q"

  shows "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> spec_pred_of_lvm_pred P w {\<triangle> Capture (emptyFrame w) r} spec_pred_of_lvm_pred Q w"
proof -
  text \<open>Speculative behaviour is stronger than the concrete rely, given initial state is not speculative\<close>
  have m: "base_rel_rely ?G \<subseteq> base_rel_rely ?R" 
    using wf by (auto simp: base_rel_guar_def base_rel_def base_rel_rely_def)

  have st: "stable (base_rel_rely (step\<^sub>t R)) (spec_pred_of_lvm_pred Q w)"
    using st by blast

  have "base_rel_rely (step\<^sub>t R),base_rel_rely ?G \<turnstile> 
      spec_pred_of_lvm_pred P w {\<triangle> Capture (emptyFrame w) r} spec_pred_of_lvm_pred Q w"
  proof (rule interr)
    show "spec_pred_of_lvm_pred P w \<subseteq> spec_pred_of_lvm_pred Q w" using pred spec_mono by force
  next
    show "stable (base_rel_rely (step\<^sub>t R)) (spec_pred_of_lvm_pred Q w)" using st by blast
  next
    show "stable (base_rel_rely ?G) (spec_pred_of_lvm_pred Q w)" using st m by blast
  next
    show "base_rel_rely (step\<^sub>t R),base_rel_rely ?G \<turnstile> 
            spec_pred_of_lvm_pred P w {Capture (emptyFrame w) r} UNIV" 
      using spec pred(2) by (rule capture[OF spec_to_spec])
  qed

  hence "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
      spec_pred_of_lvm_pred P w {\<triangle> Capture (emptyFrame w) r} spec_pred_of_lvm_pred Q w"
    apply (rule conseq)
       apply blast+
    using wf(2)
    apply (rule base_rel)
    apply blast
    done

  thus ?thesis by auto
qed

lemma [simp]:
  "(a \<union> b) \<inter> w = (a \<inter> w \<union> b \<inter> w)"
  by auto

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guarl
  where 
    "guarl w Skip G = True" |
    "guarl w (Op v a f) G = (v\<^sup>U \<subseteq> guar (wp\<^sub>i a o wp\<^sub>a f) (step G) \<and> 
                             v \<subseteq> guar (wp\<^sub>i\<^sub>s a) (gl_lift_rel (step G)))" |
    "guarl w (SimAsm.lang.Seq c\<^sub>1 c\<^sub>2) G = (guarl w c\<^sub>1 G \<and> guarl w c\<^sub>2 G)" |
    "guarl w (If _ c\<^sub>1 c\<^sub>2) G = (guarl w c\<^sub>1 G \<and> guarl w c\<^sub>2 G)" |
    "guarl w (While _ _ _ c) G = (guarl w c G)" |
    "guarl w (DoWhile _ _ c _) G = (guarl w c G)"

lemma loop_post:
  assumes "R,G \<turnstile> I { c } I"
  assumes "stable R I"
  assumes "P \<subseteq> I"
  shows "R,G \<turnstile> P { Iterw c } I"
  using assms by auto

lemma loop_pre:
  assumes "R,G \<turnstile> I { c } I"
  assumes "stable R I"
  assumes "I \<subseteq> Q"
  shows "R,G \<turnstile> I { Iterw c } Q"
  using assms by auto

lemma [simp]: "seq_pred_of_vm_pred {} = {}" 
  by (auto simp: seq_pred_of_vm_pred_def)

lemma [simp]: "spec_pred_of_lvm_pred {} w = {}" 
  by (auto simp: spec_pred_of_lvm_pred_def)

lemma [simp]: "stable\<^sub>L R {}"
  by (auto simp: stable\<^sub>L_def)

text \<open>Com Rule\<close>
theorem com_wp:
  (* Q captures the speculative implications of r *)
  assumes s: "(base_rel_rely (step\<^sub>t R)), (base_rel_guar (step G) w) \<turnstile> (spec_pred_of_lvm_pred [Q]\<^sub>s w) {r} (spec_pred_of_lvm_pred Q' w)"
  (* Q is stable *)
  assumes st: "stable\<^sub>t R [Q]\<^sub>;" "stable\<^sub>L R [Q]\<^sub>s"
  (* VCs are strong enough to establish guarantee *)
  assumes g: "guarl w c G" "wr\<^sub>l c \<subseteq> w" "lk\<^sub>l c \<inter> w = {}"
  (* Standard properties of R G *)
  assumes wf: "wellformed R G" "id_on w (step G) \<subseteq> step\<^sub>t R \<inter> step G"

  shows "(R,G \<turnstile> wp R c Q {c,r,w} Q) \<and> (stable\<^sub>t R [wp R c Q]\<^sub>; \<and> stable\<^sub>L R [wp R c Q]\<^sub>s)"
  using s st g wf(2)
proof (induct c arbitrary: Q' Q r w)
  case Skip
  then show ?case by (auto)
next
  case (Op x1 x2 x3)
  thus ?case using wf(1) 
    using basic_wp[OF wf(1) _ _ Op(2,3) Op(5)[simplified] Op(6)[simplified]] 
    by auto
next
  case (Seq c\<^sub>1 c\<^sub>2)
  hence c2: "R,G \<turnstile> wp R c\<^sub>2 Q {c\<^sub>2,r,w} Q" "stable\<^sub>t R [wp R c\<^sub>2 Q]\<^sub>;" "stable\<^sub>L R [wp R c\<^sub>2 Q]\<^sub>s" by simp+
  have "(R,G \<turnstile> wp R c\<^sub>1 (wp R c\<^sub>2 Q) {c\<^sub>1,lift\<^sub>c (ts_lang_of_vm_lang c\<^sub>2) r w,w} (wp R c\<^sub>2 Q))
          \<and> (stable\<^sub>t R [wp R c\<^sub>1 (wp R c\<^sub>2 Q)]\<^sub>; \<and> stable\<^sub>L R [wp R c\<^sub>1 (wp R c\<^sub>2 Q)]\<^sub>s)"
    using Seq(1)[OF _ c2(2,3)] c2(1) Seq(6,7,8,9) by auto
  then show ?case using c2 by auto
next
  case (If b c\<^sub>1 c\<^sub>2)
  hence c1: "R,G \<turnstile> wp R c\<^sub>1 Q {c\<^sub>1,r,w} Q" by simp
  hence c2: "R,G \<turnstile> wp R c\<^sub>2 Q {c\<^sub>2,r,w} Q" using If by simp
  have st: "stable\<^sub>t R [local.wp R c\<^sub>1 Q]\<^sub>;" "stable\<^sub>t R [local.wp R c\<^sub>2 Q]\<^sub>;"  
           "stable\<^sub>L R [local.wp R c\<^sub>1 Q]\<^sub>s" "stable\<^sub>L R [local.wp R c\<^sub>2 Q]\<^sub>s"
    using If by auto

  have stl: "stable\<^sub>L R ([local.wp R c\<^sub>2 Q]\<^sub>s \<inter> [local.wp R c\<^sub>1 Q]\<^sub>s)" 
    using st(3) st(4) stable\<^sub>L_def by auto

  show ?case
  proof (clarsimp, intro choice_if conjI, goal_cases left right spec1 spec2 st2 st3)
    case left
    have c: "R,G \<turnstile>\<^sub>; [wp R c\<^sub>1 Q]\<^sub>; {c\<^sub>1,r,w} [Q]\<^sub>;" using c1 by auto
    have b: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
      seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (cmp b) [wp R c\<^sub>1 Q]\<^sub>;)) 
        {Basic (liftl (cmp b))} 
          seq_pred_of_vm_pred [wp R c\<^sub>1 Q]\<^sub>;" (is "?R,?G \<turnstile> ?P { ?b } ?Q")
      using cmp_seq st If wf by blast

    have s: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
      seq_pred_of_vm_pred 
        (stabilize R ([local.wp R c\<^sub>2 Q]\<^sub>s \<inter> [local.wp R c\<^sub>1 Q]\<^sub>s)\<^sup>U \<inter> stabilize R
          ({s. ev\<^sub>B (varmap_st s) b \<longrightarrow> s \<in> [local.wp R c\<^sub>1 Q]\<^sub>;} \<inter> {s. \<not> ev\<^sub>B (varmap_st s) b \<longrightarrow> s \<in> [local.wp R c\<^sub>2 Q]\<^sub>;})) 
            {\<triangle> Capture (emptyFrame w) (Seqw (lift\<^sub>c (ts_lang_of_vm_lang c\<^sub>2) r w) r)} ?P"
      apply (rule spec_judgement)
          apply (rule seq)
      using If apply fastforce
      using c2 apply fastforce
      using If apply fastforce
      using If apply fastforce
      using wf stabilize_entail apply fastforce
      using wf stabilize_entail apply (meson inf.cobounded1 stabilizeE subsetD subsetI ul_restrict_mono)
      using wf by blast

    show ?case using c b s by (intro seq) (simp; blast)
  next
    case right
    have c: "R,G \<turnstile>\<^sub>; [wp R c\<^sub>2 Q]\<^sub>; {c\<^sub>2,r,w} [Q]\<^sub>;" using c2 by auto
    have b: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
      seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (ncmp b) [wp R c\<^sub>2 Q]\<^sub>;)) 
        {Basic (liftl (ncmp b))} 
          seq_pred_of_vm_pred [wp R c\<^sub>2 Q]\<^sub>;" (is "?R,?G \<turnstile> ?P { ?b } ?Q")
      using cmp_seq st If wf by blast

    have s: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
      seq_pred_of_vm_pred 
        (stabilize R ([local.wp R c\<^sub>2 Q]\<^sub>s \<inter> [local.wp R c\<^sub>1 Q]\<^sub>s)\<^sup>U \<inter> stabilize R
          ({s. ev\<^sub>B (varmap_st s) b \<longrightarrow> s \<in> [local.wp R c\<^sub>1 Q]\<^sub>;} \<inter> {s. \<not> ev\<^sub>B (varmap_st s) b \<longrightarrow> s \<in> [local.wp R c\<^sub>2 Q]\<^sub>;})) 
            {\<triangle> Capture (emptyFrame w) (Seqw (lift\<^sub>c (ts_lang_of_vm_lang c\<^sub>1) r w) r)} ?P"
      apply (rule spec_judgement)
          apply (rule seq)
      using If apply fastforce
      using c1 apply fastforce
      using If apply fastforce
      using If apply fastforce
      using wf stabilize_entail apply fastforce
      using wf stabilize_entail apply (meson inf.cobounded1 inf.cobounded2 stabilizeE subsetD subsetI ul_restrict_mono)
      using wf by blast

    show ?case using c b s by (intro seq) (simp; blast)
  next
    case spec1
    have c: "R,G \<turnstile>\<^sub>s [wp R c\<^sub>1 Q]\<^sub>s {c\<^sub>1,r,w} [Q]\<^sub>s" using c1 by auto
    have b: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
      spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [wp R c\<^sub>1 Q]\<^sub>s)) w
        {Basic (liftl (cmp b))} 
          spec_pred_of_lvm_pred [wp R c\<^sub>1 Q]\<^sub>s w" (is "?R,?G \<turnstile> ?P { ?b } ?Q")
      using cmp_spec st If wf by blast

    have s: "?R,?G \<turnstile> spec_pred_of_lvm_pred
                     ([local.wp R c\<^sub>2 Q]\<^sub>s \<inter> [local.wp R c\<^sub>1 Q]\<^sub>s)
                     w {\<triangle> Capture (emptyFrame w)
                            (Seqw
                              (lift\<^sub>c (ts_lang_of_vm_lang c\<^sub>2) r w)
                              r)} ?P"
        apply (rule spec_judgement')
          apply (rule seq)
      using If apply fastforce
      using c2 apply fastforce
      using If apply fastforce
      using If apply fastforce
      using stl stabilize\<^sub>L_entail[OF _ stl] wf(1) 
      apply (metis (no_types, lifting) CollectI IntD2 subsetI wp\<^sub>i\<^sub>s.simps(2))
      apply simp
      using local.wf(1) by blast

    show ?case using c b s by (intro seq) (simp; blast)
  next
    case spec2
    have c: "R,G \<turnstile>\<^sub>s [wp R c\<^sub>2 Q]\<^sub>s {c\<^sub>2,r,w} [Q]\<^sub>s" using c2 by auto
    have b: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
      spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [wp R c\<^sub>2 Q]\<^sub>s)) w
        {Basic (liftl (ncmp b))} 
          spec_pred_of_lvm_pred [wp R c\<^sub>2 Q]\<^sub>s w" (is "?R,?G \<turnstile> ?P { ?b } ?Q")
      using cmp_spec st If wf by blast

    have s: "?R,?G \<turnstile> spec_pred_of_lvm_pred
                     ([local.wp R c\<^sub>2 Q]\<^sub>s \<inter> [local.wp R c\<^sub>1 Q]\<^sub>s)
                     w {\<triangle> Capture (emptyFrame w)
                            (Seqw
                              (lift\<^sub>c (ts_lang_of_vm_lang c\<^sub>1) r w)
                              r)} ?P"
        apply (rule spec_judgement')
          apply (rule seq)
      using If apply fastforce
      using c1 apply fastforce
      using If apply fastforce
      using If apply fastforce
      using stl stabilize\<^sub>L_entail[OF _ stl] wf(1) 
      apply (metis (no_types, lifting) CollectI IntD1 subsetI wp\<^sub>i\<^sub>s.simps(2))
      apply simp
      using local.wf(1) by blast

    show ?case using c b s by (intro seq) (simp; blast)
  next
    case st2
    thus ?case using local.wf(1) by blast 
  next
    case st3
    thus ?case using stl by auto 
  qed
next
  case (While b I Is c)
  have "stable\<^sub>L R {}" by (auto simp: stable\<^sub>L_def)
  hence s: "stable\<^sub>t R [local.wp R (While b I Is c) Q]\<^sub>;" 
           "stable\<^sub>L R [local.wp R (While b I Is c) Q]\<^sub>s"
    using local.wf(1) by (auto simp: assert\<^sub>s_def)
  let ?a = "(I \<subseteq> [Q]\<^sub>s\<^sup>U \<inter> wp\<^sub>i (cmp b) [(wp R c (stabilize\<^sub>L R Is, stabilize R I))]\<^sub>;) \<and>
            (I \<subseteq> (stabilize\<^sub>L R Is)\<^sup>U \<inter> wp\<^sub>i (ncmp b) [Q]\<^sub>;) \<and> 
            (Is \<subseteq> [Q]\<^sub>s \<inter> [(wp R c (stabilize\<^sub>L R Is, stabilize R I))]\<^sub>s)"

  show ?case 
  proof (cases ?a)
    case True 
    text \<open>Loop invariant assertions hold\<close>
    let ?I = "(stabilize\<^sub>L R Is, stabilize R I)"
    have st: "stable\<^sub>t R [?I]\<^sub>;" "stable\<^sub>L R [?I]\<^sub>s" using local.wf(1) by auto 

    text \<open>Normal judgment over r in terms of the postcondition Q\<close>
    have rq: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
              spec_pred_of_lvm_pred [Q]\<^sub>s w {r} spec_pred_of_lvm_pred Q' w"
      using While(2) by simp

    text \<open>Strengthen precondition on speculative judgement over r to the invariant\<close>
    have "stabilize\<^sub>L R Is \<subseteq> [Q]\<^sub>s" using True 
      by (meson Int_lower1 local.wf(1) stabilize\<^sub>LE subsetI subset_trans)
    hence r: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile>
              spec_pred_of_lvm_pred [?I]\<^sub>s w {r} spec_pred_of_lvm_pred Q' w"
      using rq by (simp add: conseq spec_mono)

    text \<open>Get the inductive hypothesis, establishing judgements over c\<close>
    have "(R,G \<turnstile> local.wp R c ?I {c,r,w} ?I) \<and> stable\<^sub>t R [local.wp R c ?I]\<^sub>; \<and> stable\<^sub>L R [local.wp R c ?I]\<^sub>s"
      apply (rule While(1)) using While st r by auto
    hence hyp: "seq_rule R G [local.wp R c ?I]\<^sub>; c r w [?I]\<^sub>;" "spec_rule R G [local.wp R c ?I]\<^sub>s c r w [?I]\<^sub>s" 
               "stable\<^sub>t R [local.wp R c ?I]\<^sub>;" "stable\<^sub>L R [local.wp R c ?I]\<^sub>s"
      by auto

    text \<open>Speculative execution of c in an invariant context\<close>
    have cspec: "R,G \<turnstile>\<^sub>s [?I]\<^sub>s {c,r,w} [?I]\<^sub>s"
      apply (rule conseq[OF hyp(2)], rule spec_mono, auto)
      using True by (metis Int_iff inf.absorb_iff2 local.wf(1) stabilize\<^sub>LE) 

    text \<open>Sequential judgment over the exit condition\<close>
    have ncmp: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
                  seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (ncmp b) [Q]\<^sub>;)) {Basic (liftl (ncmp b))} 
                    seq_pred_of_vm_pred [Q]\<^sub>;" (is "?R,?G \<turnstile> seq_pred_of_vm_pred ?P { ?c } ?Q")
      using wf cmp_seq[OF wf(1)] While by blast

    text \<open>Speculative execution of additional loop iterations\<close>
    have loopspec: "?R,?G \<turnstile> seq_pred_of_vm_pred (?P \<inter> [?I]\<^sub>s\<^sup>U) {
                      \<triangle> Capture (emptyFrame w)
                        (Seqw (lift\<^sub>c (ts_lang_of_vm_lang c) r w)
                          (Seqw
                            (Iterw
                              (lift\<^sub>c (ts_lang_of_vm_lang c) r w)) r))} seq_pred_of_vm_pred ?P"
      apply (intro spec_judgement seq loop_post)
      apply (rule r, rule cspec)
      using st(2) apply fastforce
      apply (rule subset_refl, rule cspec)
      using While apply fastforce
      using While apply fastforce
      using While apply fastforce
      using While apply fastforce
      using wf by blast

    text \<open>Sequential judgment over the failed exit condition\<close>
    have cmp: "?R,?G \<turnstile> seq_pred_of_vm_pred (stabilize R (wp\<^sub>i (cmp b) [local.wp R c ?I]\<^sub>;)) {
                Basic (liftl (cmp b))} seq_pred_of_vm_pred [local.wp R c ?I]\<^sub>;"
      using wf cmp_seq[OF wf(1)] While hyp(3) by blast

    text \<open>Execution of real loop iterations\<close>
    have cseq: "?R,?G \<turnstile> seq_pred_of_vm_pred [?I]\<^sub>; {
        Iterw ((\<triangle> Capture (emptyFrame w) r) \<cdot>
          Seqw (Basic (liftl (cmp b)))
            (lift\<^sub>c (ts_lang_of_vm_lang c) r
              w))} seq_pred_of_vm_pred  (?P \<inter> [?I]\<^sub>s\<^sup>U)"
      apply (intro loop_pre seq)
      apply (rule hyp(1), rule cmp, rule spec_judgement, rule rq)
      using While apply fastforce
      using While apply fastforce
      using True wf apply (simp add: stabilize_entail subsetI)
      using True wf apply (simp, meson stabilizeE subset_iff)
      using wf apply blast
      using st(1) apply fastforce
      using True wf stabilizeE stabilize_entail by fastforce

    text \<open>Speculative judgment over the exit condition\<close>
    have ncmps: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) w \<turnstile> 
                  spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (ncmp b) [Q]\<^sub>s)) w {Basic (liftl (ncmp b))} 
                    spec_pred_of_lvm_pred [Q]\<^sub>s w" (is "?R,?G \<turnstile> spec_pred_of_lvm_pred ?P w { ?c } ?Q")
      using wf cmp_spec[OF wf(1)] While by blast

    text \<open>Speculative execution of additional loop iterations\<close>
    have loopspecs: "?R,?G \<turnstile> spec_pred_of_lvm_pred (?P \<inter> [?I]\<^sub>s) w {
                      \<triangle> Capture (emptyFrame w)
                        (Seqw (lift\<^sub>c (ts_lang_of_vm_lang c) r w)
                          (Seqw
                            (Iterw
                              (lift\<^sub>c (ts_lang_of_vm_lang c) r w)) r))} spec_pred_of_lvm_pred ?P w"
      apply (intro spec_judgement' seq loop_post)
      apply (rule r, rule cspec)
      using st(2) apply fastforce
      apply (rule subset_refl, rule cspec)
      using While apply fastforce
      using While apply fastforce
      using While apply fastforce
      using While apply fastforce
      using wf by blast

    text \<open>Speculative judgment over the failed exit condition\<close>
    have cmps: "?R,?G \<turnstile> spec_pred_of_lvm_pred (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [local.wp R c ?I]\<^sub>s)) w {
                Basic (liftl (cmp b))} spec_pred_of_lvm_pred [local.wp R c ?I]\<^sub>s w"
      using wf cmp_spec[OF wf(1)] While hyp(4) by blast

    text \<open>Execution of speculative loop iterations\<close>
    have cseqs: "?R,?G \<turnstile> spec_pred_of_lvm_pred [?I]\<^sub>s w {
        Iterw ((\<triangle> Capture (emptyFrame w) r) \<cdot>
          Seqw (Basic (liftl (cmp b)))
            (lift\<^sub>c (ts_lang_of_vm_lang c) r
              w))} spec_pred_of_lvm_pred (?P \<inter> [?I]\<^sub>s) w"
      apply (intro loop_pre seq)
      apply (rule hyp(2), rule cmps, rule spec_judgement', rule r)
      using While apply fastforce
      using While apply fastforce
      using True wf stabilize\<^sub>L_def apply force
      apply simp
      using wf apply blast
      using st(2) apply fastforce
      using True stabilize\<^sub>L_def by force

    show ?thesis
      using s apply auto

       apply (intro seq)
         apply (rule ncmp)
        apply (rule loopspec)
      apply (rule conseq)
           apply (rule cseq)
          apply (rule seq_mono)
          apply auto[1]
         apply (simp add: stabilize_def)
        apply auto[3]

       apply (intro seq)
         apply (rule ncmps)
        apply (rule loopspecs)
      apply (rule conseq)
           apply (rule cseqs)
          apply (rule spec_mono)
          apply auto
      done
  next
    case False (* Loop invariant assertions don't hold *)
    hence "local.wp R (While b I Is c) Q = ({},{})" by (auto simp: assert\<^sub>s_def)
    hence "R,G \<turnstile> local.wp R (While b I Is c) Q {While b I Is c,r,w} Q"
      by (simp del: wp.simps) (meson conseq empty_subsetI falseI subset_refl)
    then show ?thesis using s by blast
  qed
next
  case (DoWhile x1 x2 c x4)
  then show ?case by auto (meson conseq empty_subsetI falseI subset_refl)+
qed


subsection \<open>High-Level Theorem\<close>

text \<open>Soundness lemma for WP reasoning\<close>
theorem simAsm_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" "id_on  (wr\<^sub>l c) (step G) \<subseteq> step\<^sub>t R \<inter> step G"
  assumes st: "stable\<^sub>t R [Q]\<^sub>;" "stable\<^sub>L R [Q]\<^sub>s"
  assumes g: "guarl (wr\<^sub>l c) c G"
  assumes P: "P \<subseteq>\<^sub>s wp R c Q"
  assumes l: "lk\<^sub>l c \<inter> wr\<^sub>l c = {}"
  shows "\<Turnstile> c SAT [[P]\<^sub>;, R, G, [Q]\<^sub>;]"
proof -
  have "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) (wr\<^sub>l c) \<turnstile> 
          spec_pred_of_lvm_pred [Q]\<^sub>s (wr\<^sub>l c) {com.Nil} spec_pred_of_lvm_pred [Q]\<^sub>s (wr\<^sub>l c)"
    using st(2) by auto
  hence "R,G \<turnstile> wp R c Q {c,Nil,wr\<^sub>l c} Q" 
    using com_wp[OF _ st g _ l] wf by simp
  hence "R,G \<turnstile>\<^sub>; [wp R c Q]\<^sub>; {c,Nil,wr\<^sub>l c} [Q]\<^sub>;" 
    by blast
  hence "R,G \<turnstile>\<^sub>; [P]\<^sub>; {c,Nil,wr\<^sub>l c} [Q]\<^sub>;" 
    using P by (meson equalityD2 rules.conseq seq_mono)
  thus ?thesis using sound by blast
qed

end (* of context wp *)

end
