theory SimAsm_Rules
  imports SimAsm_WP SimAsm_Semantics "../Soundness"
begin

subsection \<open>Conversion between tstack and varmap.\<close>

lift_definition vm_of_ts :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) varmap'" 
  is "\<lambda>s. \<lparr> varmap_st = tlookup s, \<dots> = frame.more (last (Rep_tstack s))\<rparr>".

lift_definition ts_of_vm :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) tstack" 
  is "inv vm_of_ts".

lemma ts_of_vm_exists: "\<exists>ts. vm_of_ts ts = vm"
proof
  let ?s = "[\<lparr> frame_st = Some \<circ> varmap_st vm, frame_cap = UNIV, \<dots> = varmap_rec.more vm \<rparr>]"
  let ?ts = "Abs_tstack ?s"
  have "Is_tstack ?s" by (simp add: Is_tstack_def)
  hence 1: "RepAbs_tstack ?s = ?s" by simp
  show "vm_of_ts ?ts = vm" 
    unfolding vm_of_ts_def tlookup_def 
    apply (simp add: 1) 
    unfolding lookup.simps by simp
    qed
  
lemma ts_of_vm_inverse: "vm_of_ts (ts_of_vm vm) = vm"
proof -
  have a: "ts_of_vm vm = (SOME ts. vm_of_ts ts = vm)" 
    by (simp add: inv_def ts_of_vm.abs_eq)
  have "varmap_st vm = tlookup (ts_of_vm vm)" 
    using a ts_of_vm_exists
    by (metis (mono_tags, lifting) varmap_rec.select_convs(1) verit_sko_ex' vm_of_ts.transfer)  
  moreover have "varmap_rec.more vm = frame.more (last (Rep_tstack (ts_of_vm vm)))"
    using a ts_of_vm_exists
    by (metis (mono_tags, lifting) varmap_rec.select_convs(2) verit_sko_ex' vm_of_ts.transfer)    
  ultimately show ?thesis unfolding vm_of_ts_def by simp
qed
  
lift_definition ts_pred_of_vm_pred :: "('r,'v,'a) varmap' pred \<Rightarrow> ('r,'v,'a) tstack pred" is
  "\<lambda>v. vm_of_ts -` v".

lift_definition vm_rel_of_ts_rel :: "('r,'v,'a) tstack rel \<Rightarrow> ('r,'v,'a) varmap' rel" is 
  "\<lambda>x. {(vm_of_ts s,vm_of_ts s') | s s'. (s,s') \<in> x}".

lift_definition ts_rel_of_vm_rel :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel" is 
  "\<lambda>x. {(s,s') | s s'. (vm_of_ts s,vm_of_ts s') \<in> x}".
  
fun ts_lang_of_vm_lang :: "('r,'v,('r,'v,'a)varmap','a) lang \<Rightarrow> ('r, 'v, ('r, 'v, 'a) tstack, 'a) lang" where
  "ts_lang_of_vm_lang (Skip) = Skip " |
  "ts_lang_of_vm_lang (Op pred op auxfn) = Op (ts_pred_of_vm_pred pred) op (auxfn)" |
  "ts_lang_of_vm_lang (SimAsm.lang.Seq a b) = SimAsm.lang.Seq (ts_lang_of_vm_lang a) (ts_lang_of_vm_lang b) " |
  "ts_lang_of_vm_lang (If c t f) = If c (ts_lang_of_vm_lang t) (ts_lang_of_vm_lang f)" |
  "ts_lang_of_vm_lang (While b Imix Ispec c) = While b (ts_pred_of_vm_pred Imix) (ts_pred_of_vm_pred Ispec) (ts_lang_of_vm_lang c) " |
  "ts_lang_of_vm_lang (DoWhile Imix Ispec c b) = DoWhile (ts_pred_of_vm_pred Imix) (ts_pred_of_vm_pred Ispec) (ts_lang_of_vm_lang c) b "

fun vm_lang_of_ts_lang :: "('r,'v,('r,'v,'a)tstack,'a) lang \<Rightarrow> ('r, 'v, ('r, 'v, 'a) varmap', 'a) lang" where
  "vm_lang_of_ts_lang (Skip) = Skip " |
  "vm_lang_of_ts_lang (Op pred op auxfn) = Op (vm_of_ts ` pred) op (auxfn)" |
  "vm_lang_of_ts_lang (lang.Seq a b) = lang.Seq (vm_lang_of_ts_lang a) (vm_lang_of_ts_lang b) " |
  "vm_lang_of_ts_lang (If c t f) = If c (vm_lang_of_ts_lang t) (vm_lang_of_ts_lang f)" |
  "vm_lang_of_ts_lang (While b Imix Ispec c) = While b (vm_of_ts ` Imix) (vm_of_ts ` Ispec) (vm_lang_of_ts_lang c) " |
  "vm_lang_of_ts_lang (DoWhile Imix Ispec c b) = DoWhile (vm_of_ts ` Imix) (vm_of_ts ` Ispec) (vm_lang_of_ts_lang c) b "

definition ts_non_caches :: "('r,'v,'a) tstack \<Rightarrow> 'r set" where
  "ts_non_caches ts \<equiv> \<Union>(frame_cap ` set (butlast (Rep_tstack ts)))"

abbreviation ts_caches :: "('r,'v,'a) tstack \<Rightarrow> 'r set" where
  "ts_caches ts \<equiv> UNIV - ts_non_caches ts"

subsection \<open>Correspondence from spec_state to tstack.\<close>

definition tstack_base :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) varmap'" where
  "tstack_base stack \<equiv> 
    \<lparr> varmap_st = the \<circ> frame_st (last (Rep_tstack stack)), \<dots> = taux stack \<rparr>"

lemma tupdate_non_caches[simp]: 
  assumes "v \<in> ts_non_caches ts"
  shows "tstack_base (tupdate ts v x) = tstack_base ts"
using assms
unfolding ts_non_caches_def tstack_base_def tupdate_def comp_def 
proof (simp add: taux.abs_eq, standard, induct ts rule: tstack_induct)
  case (Base frame)
  then show ?case by auto
next
  case (Frame hd tl)
  hence "Is_tstack (hd # tl)" by blast
  with Frame show ?case by (auto simp add: Is_tstackE(1) Is_tstack_update)
qed



text \<open>
The number of frames within the tstack naturally tells us whether that state
is speculative or sequential.
\<close>

definition ts_is_seq where 
  "ts_is_seq ts \<equiv> tstack_len ts = 1"

abbreviation ts_is_spec where 
  "ts_is_spec ts \<equiv> \<not>ts_is_seq ts"


definition ts_seq where
  "ts_seq = {ts. ts_is_seq ts}"
definition ts_spec where
  "ts_spec = {ts. ts_is_spec ts}"

lemma ts_upper_of_seq [elim]: \<open>ts_is_seq m \<Longrightarrow> (tstack_upper m = [])\<close>
unfolding ts_is_seq_def tstack_upper_def tstack_len_def 
by (simp_all only: id_def) (simp_all add: butlast_conv_take Rep_tstackI(1) le_Suc_eq)

lemma ts_is_seq_of_ts_upper [intro]: \<open>(tstack_upper m = []) \<Longrightarrow> ts_is_seq m\<close>
unfolding ts_is_seq_def tstack_upper_def tstack_len_def 
by (simp_all only: id_def) (simp_all add: butlast_conv_take Rep_tstackI(1) le_Suc_eq)



text \<open>
With these definitions, we define functions to convert from spec_state's
sequential and speculative components into tstack predicates.
 
In particular, spec_pred_of_lvm_pred implements labelled variable names
by mapping these to the appropriate parts of the tstack structure.
\<close>

lift_definition seq_pred_of_vm_pred :: "('r,'v,'a) varmap' pred \<Rightarrow> ('r,'v,'a) tstack pred" is
  "\<lambda>P. {ts \<in> ts_pred_of_vm_pred P. ts_is_seq ts}".

lift_definition spec_pred_of_lvm_pred :: "('r,'v,'a) lvarmap' pred \<Rightarrow> ('r,'v,'a) tstack pred" is
  "\<lambda>P. {ts | ts v. 
        v \<in> P \<and>
        ts_is_spec ts \<and>
        vm_of_ts ts = ul_restrict v \<and>
        tstack_base ts = gl_restrict v}".
(* flattening all frames of the tstack should result in the unlabelled part. *)
(* viewing only the base frame should be equal to the globally labelled part. *)        

text \<open>
Obtains a sequential relation from a varmap relation. That is, the
global (tstack base) state is related by the given R and
the speculative (tstack upper) state is identity.
\<close>

lift_definition seq_rel_of_vm_rel :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel" is
  "\<lambda>R. {(ts,ts') \<in> ts_rel_of_vm_rel R. tstack_upper ts = tstack_upper ts'}".

fun nonspec :: "(('r,'v,'a) auxopSt, ('r,'v,'a) tstack, 'frame) com \<Rightarrow> (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, 'frame) com" where
"nonspec (Basic (auxop, v, b)) = Basic (auxop,{s \<in> v. ts_is_seq s},b)" |
"nonspec x = x"                                                                                           
(* note: additionally, we need the behaviours 'b' to not introduce speculation (i.e. not introduce additional frames).
          we prove that this is the case for all of the behaviours which can result from beh\<^sub>a in lemma h2 below (temporary name).  *)

locale simasm_rules = 
  semantics_spec 
    where st = "tlookup :: ('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v"
    and st_upd = tupdate
    and aux = taux
    and aux_upd = tauxupd
  + rules 
    where exists_act = "undefined :: ('r,'v,'a) auxopSt"
    and push = "tstack_push :: ('r,'v,'a) tstack \<Rightarrow> ('r,'v) frame \<Rightarrow> ('r,'v,'a) tstack"
  + wp_spec
    where rg = rg
    and glb = glb
  for rg :: "('r,'v,'a) varmap' \<Rightarrow> 'local \<Rightarrow> 'v"
  and glb :: "('r,'v,'a) varmap' \<Rightarrow> 'global \<Rightarrow> 'v"

context simasm_rules
begin
  
definition stabilize\<^sub>s where 
  "stabilize\<^sub>s R P \<equiv> {m. \<forall>m'. (glb (gl_restrict m),glb m') \<in> R \<longrightarrow> rg (gl_restrict m) = rg m' \<longrightarrow> m' \<in> [P]\<^sub>;}"

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [65,0,0,0,65] 65)
  where "rules_abv R G P c Q \<equiv> rules R G P c Q"

abbreviation lifted_abv ("_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,20] 20)
  where "lifted_abv R G P c Q \<equiv> 
      (seq_rel_of_vm_rel (step\<^sub>t R)), (seq_rel_of_vm_rel (step G)) 
        \<turnstile> (seq_pred_of_vm_pred [P]\<^sub>;) {nonspec (lift\<^sub>c c com.Nil {})} (seq_pred_of_vm_pred [Q]\<^sub>;)
      \<and> (seq_rel_of_vm_rel (step\<^sub>t R)), UNIV 
        \<turnstile> (spec_pred_of_lvm_pred [P]\<^sub>s) {lift\<^sub>c c com.Nil {}} (spec_pred_of_lvm_pred [Q]\<^sub>s)" 


abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0] 45) 
 where "validity_abv c P R G Q \<equiv> validity (lift\<^sub>c c com.Nil {}) P (ts_rel_of_vm_rel (step\<^sub>t R)) (ts_rel_of_vm_rel (step G)) Q" 

text \<open>An ordering property on contexts\<close>
definition context_order 
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv> 
    (stable\<^sub>t R Q \<and> wellformed R G) \<longrightarrow> ((P \<subseteq> Q) \<and> stable\<^sub>t R P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness,
        i.e., wellformedness (of R and G) and guarantee check of c become assumptions for the soundness proof \<close>
definition valid 
  ("_,_ \<turnstile>\<^sub>w _ {_} _" [100,0,0,0,100] 60)
  where "valid R G P c Q \<equiv>  
     (wellformed R G \<and> stable\<^sub>t R [Q]\<^sub>; \<and> guar\<^sub>c (vm_lang_of_ts_lang c) G) 
     \<longrightarrow> (stable\<^sub>t R [P]\<^sub>; \<and> (R,G \<turnstile>\<^sub>s P {c} Q))" 


(* lemma vm_of_ts_auxupd:  *)
  (* "(vm_of_ts x)\<lparr>varmap_rec.more := f (vm_of_ts x)\<rparr> = vm_of_ts (tauxupd x (f \<circ> vm_of_ts))" *)
(* proof - *)
  (* have Is_tstack: "Is_tstack (auxupd (Rep_tstack x) (\<lambda>tstack. f (vm_of_ts (Abs_tstack tstack))))" *)
    (* by auto *)
  (* have f: "f (vm_of_ts x) = frame.more (last (Rep_tstack (tauxupd x (f \<circ> vm_of_ts))))" *)
    (* unfolding tauxupd_def  *)
    (* by (auto simp add: Is_tstack, simp add: auxupd_def Rep_tstack_inverse) *)
  
  (* show ?thesis *)
  (* using f unfolding vm_of_ts_def by auto *)
(* qed *)

lemma vm_of_ts_upd: 
  "(vm_of_ts s)\<lparr>varmap_st := (varmap_st (vm_of_ts s))(v := x)\<rparr> = vm_of_ts (tupdate s v x)"
unfolding vm_of_ts_def tlookup_def tupdate_def  
using lookup_update2[of "Rep_tstack s" v x] by auto

(* lemma vm_of_ts_bothupd: *)
  (* "(vm_of_ts s) *)
    (* \<lparr>varmap_st := (varmap_st (vm_of_ts s))(v := x), *)
     (* varmap_rec.more := f ((vm_of_ts s)\<lparr>varmap_st := (varmap_st (vm_of_ts s))(v := x)\<rparr>)\<rparr> *)
   (* = vm_of_ts (tauxupd (tupdate s v x) (f \<circ> vm_of_ts))" *)
(* using vm_of_ts_auxupd[where ?x = "tupdate s v x"] vm_of_ts_upd[of s] *)
(* by simp *)
  
lemma tauxupd_in_ts_pred:
  assumes "x \<in> ts_pred_of_vm_pred {t. t\<lparr>varmap_rec.more := f t\<rparr> \<in> Q}" 
  shows "tauxupd x (f \<circ> vm_of_ts) \<in> ts_pred_of_vm_pred Q"
proof -
  have "\<exists>t \<in> {t. t\<lparr>varmap_rec.more := f t\<rparr> \<in> Q}. vm_of_ts x = t" using assms ts_of_vm_exists
    by (simp add: ts_pred_of_vm_pred.rep_eq) 
  hence Q: "(vm_of_ts x) \<lparr> varmap_rec.more := f (vm_of_ts x) \<rparr> \<in> Q" by simp
  show ?thesis using vm_of_ts_auxupd[where ?x = x] Q by (simp add: ts_pred_of_vm_pred.abs_eq)
qed

lemma ts_pred_of_vm_pred_Inter [simp]: 
  "ts_pred_of_vm_pred (P \<inter> Q) = ts_pred_of_vm_pred P \<inter> ts_pred_of_vm_pred Q"
unfolding ts_pred_of_vm_pred_def by simp

lemma ts_rel_of_vm_rel_from_vm_of_ts:
assumes "(vm_of_ts x, vm_of_ts y) \<in> Rel"
shows "(x, y) \<in> ts_rel_of_vm_rel Rel"
by (simp add: assms ts_rel_of_vm_rel.rep_eq)


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
qed

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
qed

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

lemma stable_seq_rel_from_stablet [elim]:
  assumes "stable\<^sub>t R Q"
  shows "State.stable (seq_rel_of_vm_rel (step\<^sub>t R)) (seq_pred_of_vm_pred Q)"
using assms stable_seq_from_stable_ts stable_ts_rel_from_stablet by auto


lemma vm_of_ts_in_ts_pred_of_vm_pred[simp]: "(x \<in> ts_pred_of_vm_pred P) = (vm_of_ts x \<in> P)"
unfolding ts_pred_of_vm_pred_def by simp

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

lemma nonspec:
  assumes "seq_rel_of_vm_rel (step\<^sub>t R),seq_rel_of_vm_rel (step G) \<turnstile> seq_pred_of_vm_pred [P]\<^sub>; {Basic ((\<alpha>, f \<circ> vm_of_ts), ts_pred_of_vm_pred c, beh\<^sub>a (\<alpha>, f \<circ> vm_of_ts))} seq_pred_of_vm_pred [Q]\<^sub>;"
  shows "seq_rel_of_vm_rel (step\<^sub>t R),seq_rel_of_vm_rel (step G) \<turnstile> seq_pred_of_vm_pred [P]\<^sub>; {nonspec (Basic ((\<alpha>, f \<circ> vm_of_ts), ts_pred_of_vm_pred c, beh\<^sub>a (\<alpha>, f \<circ> vm_of_ts)))} seq_pred_of_vm_pred [Q]\<^sub>;"
  sorry   

lemma seq_pred_of_vm_pred_subset:
  assumes "P' \<subseteq> P"
  shows "seq_pred_of_vm_pred P' \<subseteq> seq_pred_of_vm_pred P"
  unfolding seq_pred_of_vm_pred_def 
  using assms
  by auto

lemma spec_pred_of_lvm_pred_subset:
  assumes "P' \<subseteq> P"
  shows "spec_pred_of_lvm_pred P' \<subseteq> spec_pred_of_lvm_pred P"
  unfolding spec_pred_of_lvm_pred_def 
  using assms
  by auto

lemma stabilize\<^sub>LE [elim]:
  assumes "m \<in> spec_pred_of_lvm_pred (stabilize\<^sub>L R P)"
  assumes "reflexive R"
  obtains "m \<in> spec_pred_of_lvm_pred P"
using assms
unfolding spec_pred_of_lvm_pred_def
using stabilizeE reflexive_def stabilize\<^sub>L_def 
by fastforce

  
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
qed

lemma basic_wp\<^sub>i_1_assign_spec:
  assumes "\<alpha> = assign x11 x12"
  assumes "ts_is_spec x"
  assumes "x \<in> spec_pred_of_lvm_pred (wp\<^sub>i\<^sub>s \<alpha> (wp\<^sub>a (\<lambda>f'. f (f' \<circ> Gl)) Qspec))"
  assumes "x11 \<in> ts_non_caches x"
  shows "tauxupd (tupdate x x11 (ev\<^sub>E (tlookup x) x12)) (f) \<in> spec_pred_of_lvm_pred Qspec" (is "?ts \<in> \<dots>")
    "ts_is_spec (tauxupd (tupdate x x11 (ev\<^sub>E (tlookup x) x12)) (f))"
using assms
unfolding spec_pred_of_lvm_pred_def
proof (clarsimp simp add: id_def, goal_cases)
  case (1 v)
  let ?v_ = "v\<lparr>varmap_st := (varmap_st v)(Ul x11 := ev\<^sub>E (varmap_st v) (map\<^sub>E Ul id id x12))\<rparr>"
  let ?v = "?v_\<lparr>varmap_rec.more := f (varmap_st ?v_ \<circ> Gl) (varmap_rec.more ?v_)\<rparr>"

  have tlookup [simp]: "varmap_st v (Ul va) = tlookup x va" for va
    using 1(5) unfolding tlookup_def vm_of_ts_def by auto

  have ev: "ev\<^sub>E (tlookup x) xa = (ev\<^sub>E (varmap_st v) \<circ> map\<^sub>E Ul id id) xa" for xa
  by (induct xa, simp_all add: id_def comp_def) (metis (mono_tags, lifting) map_eq_conv)

  have "ev\<^sub>E (\<lambda>va. varmap_st v (Ul va)) x12 = ev\<^sub>E (tlookup x) x12"
    using tlookup by presburger

  (* have notnone: "frame_st (last (Rep_tstack (tauxupd (tupdate x x11 (ev\<^sub>E (tlookup x) x12)) (\<lambda>x. f (vm_of_ts x))))) va \<noteq> None" for va *)
    (* by blast *)

  have ev_map [simp]:  "ev\<^sub>E (varmap_st v) (map\<^sub>E Ul id id x12) = ev\<^sub>E (tlookup x) x12"
    using ev by auto  
    
  have "tstack_base (tupdate x x11 x12) = tstack_base x" for x12
  using assms by simp 

  (* have "\<And>va. varmap_st (tstack_base (tupdate x x11 x12)) va = varmap_st v (Gl va)" for x11 x12 *)
  (* using 1(4) apply auto apply standard unfolding comp_def apply (rule arg_cong[where ?f=the])  *)

  show ?case
  proof (standard, intro conjI)
    show "?v \<in> Qspec" using 1(4) by (cases x12) (auto simp add: id_def wp\<^sub>a.simps)
    show "ts_is_spec (tauxupd (tupdate x x11 (ev\<^sub>E (tlookup x) x12)) (f))" using 1(2,3) by clarify (metis tauxupd_len ts_is_seq_def tupdate_len)
    show "vm_of_ts ?ts = \<lparr>varmap_st = \<lambda>va. varmap_st (?v) (Ul va), \<dots> = varmap_rec.more (?v)\<rparr>"
    unfolding vm_of_ts_def
    apply auto using 1
    sorry (* we need properties constraining the acceptable auxfns (i.e. they are minimally state-dependent). or, we need to ignore them. *)
    show "tstack_base ?ts = \<lparr>varmap_st = \<lambda>va. varmap_st (?v) (Gl va), \<dots> = varmap_rec.more (?v)\<rparr>" 
    proof (induct x rule: tstack_induct)
      case (Base x)
      then show ?case sorry
    next
      case (Frame x xs)
      then show ?case apply auto sledgehammer
    qed
  qed
next
  case 2
  show ?case using assms(2) tauxupd_len tupdate_len ts_is_seq_def by metis
qed

find_theorems name: arg_cong

lemma tstack_len_of_st_beh:
assumes "(x, y) \<in> st_beh\<^sub>i \<alpha>"
shows "tstack_len x = tstack_len y"
using assms
by (cases \<alpha>) (auto simp add: tupdate_len)

lemma stable_of_stabilize_ts [intro]:
  assumes "wellformed R G"
  shows "State.stable (seq_rel_of_vm_rel (step\<^sub>t R)) (seq_pred_of_vm_pred (stabilize R P))"
unfolding stable_def 
proof (intro allI impI, goal_cases)
  case (1 m m')
  have "tstack_upper m = []" "tstack_upper m' = []"
    using 1(1,2) unfolding seq_pred_of_vm_pred_def seq_rel_of_vm_rel_def by (simp_all add: ts_upper_of_seq)
    thus ?case
      using 1 stabilize_stable[OF assms] unfolding seq_pred_of_vm_pred_def seq_rel_of_vm_rel_def
      by clarsimp (meson State.stable_def stable_ts_rel_from_stablet ts_is_seq_of_ts_upper vm_of_ts_in_ts_pred_of_vm_pred)
qed

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

      then show ?case apply (cases \<alpha>) apply auto unfolding wp_def apply auto unfolding liftg_def apply auto using   x_in_wp  apply auto unfolding wp\<^sub>a.simps apply auto 
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
  oops

text \<open>A rule for cmp operations, used for If/While\<close>
lemma cmp_sound [intro!]:
  assumes "wellformed R G" "stable\<^sub>t R [Q]\<^sub>;"
  assumes "P \<subseteq>\<^sub>s (stabilize\<^sub>L R (wp\<^sub>i\<^sub>s (cmp b) [Q]\<^sub>s), stabilize R (wp\<^sub>i (cmp b) [Q]\<^sub>;))"
  shows "R,G \<turnstile>\<^sub>s P {Op UNIV (cmp b) taux} Q"
  using assms 
  by (intro basic_wp\<^sub>i_2) (auto simp: step_def reflexive_def wp\<^sub>r_def)  

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

(*
lemma if_wp:
  "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w stabilize R (wp\<^sub>i (cmp b) P\<^sub>1 \<inter> wp\<^sub>i (ncmp b) P\<^sub>2) {If b c\<^sub>1 c\<^sub>2} Q"
  unfolding valid_def apply clarsimp apply (intro conjI rules.choice rules.seq, auto )
  apply (rule stabilize_entail, auto)+
  done
*)


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

text \<open>Com Rule\<close>
theorem com_wp:
  shows "R,G \<turnstile>\<^sub>w wp R c Q {c} Q" 
proof (induct c arbitrary: Q)
  case Skip
  then show ?case by (auto simp: valid_def)
next
  case (Op x1 x2)
  then show ?case unfolding valid_def lift\<^sub>c.simps 
    by (intro conjI impI basic_wp\<^sub>i_1) auto
next
  case (Seq c1 c2)
  then show ?case by (auto simp: valid_def)
next
  case (If x1 c1 c2)
  then show ?case unfolding wp.simps by (blast intro: if_wp)
next
  case (While x1 x2 c)
  then show ?case unfolding wp.simps by (intro assert_wp impI while_wp) (auto)
next
  case (DoWhile I c b)
  thus ?case unfolding wp.simps by (intro assert_wp do_wp; rule rewrite_wp) auto
qed

subsection \<open>High-Level Theorem\<close>

text \<open>Soundness lemma for WP reasoning\<close>
theorem simAsm_wp_sound:
  assumes wf: "transitive R" "reflexive R" "reflexive G" 
  assumes st: "stable\<^sub>t R Q" 
  assumes g: "guar\<^sub>c c G"
  assumes P: "P \<subseteq> wp R c Q"
  shows "\<Turnstile> c SAT [P, R, G, Q]"
proof -
  have "R,G \<turnstile>\<^sub>s wp R c Q {c} Q" using wf st g com_wp unfolding valid_def by blast
  hence "R,G \<turnstile>\<^sub>s P {c} Q" by (rule rules.conseq) (insert P, auto simp: )
  thus ?thesis by (intro sound thread) auto
qed

end (* of context wp *)

end
