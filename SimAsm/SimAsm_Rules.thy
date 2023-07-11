theory SimAsm_Rules
  imports SimAsm_WP SimAsm_Semantics "../Soundness"
  begin

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
  
lift_definition ts_rel_of_vm_rel :: "('r,'v,'a) varmap' rel \<Rightarrow> ('r,'v,'a) tstack rel" is 
  "\<lambda>x. {(s,s') | s s'. (vm_of_ts s, vm_of_ts s') \<in> x}".
  
fun ts_lang_of_vm_lang :: "('r,'v,('r,'v,'a)varmap','a) lang \<Rightarrow> ('r, 'v, ('r, 'v, 'a) tstack, 'a) lang" where
  "ts_lang_of_vm_lang (Skip) = Skip " |
  "ts_lang_of_vm_lang (Op pred op auxfn) = Op (ts_pred_of_vm_pred pred) op (auxfn \<circ> vm_of_ts)" |
  "ts_lang_of_vm_lang (SimAsm.lang.Seq a b) = SimAsm.lang.Seq (ts_lang_of_vm_lang a) (ts_lang_of_vm_lang b) " |
  "ts_lang_of_vm_lang (If c t f) = If c (ts_lang_of_vm_lang t) (ts_lang_of_vm_lang f)" |
  "ts_lang_of_vm_lang (While b Imix Ispec c) = While b (ts_pred_of_vm_pred Imix) (ts_pred_of_vm_pred Ispec) (ts_lang_of_vm_lang c) " |
  "ts_lang_of_vm_lang (DoWhile Imix Ispec c b) = DoWhile (ts_pred_of_vm_pred Imix) (ts_pred_of_vm_pred Ispec) (ts_lang_of_vm_lang c) b "

fun vm_lang_of_ts_lang :: "('r,'v,('r,'v,'a)tstack,'a) lang \<Rightarrow> ('r, 'v, ('r, 'v, 'a) varmap', 'a) lang" where
  "vm_lang_of_ts_lang (Skip) = Skip " |
  "vm_lang_of_ts_lang (Op pred op auxfn) = Op (vm_of_ts ` pred) op (auxfn \<circ> ts_of_vm)" |
  "vm_lang_of_ts_lang (lang.Seq a b) = lang.Seq (vm_lang_of_ts_lang a) (vm_lang_of_ts_lang b) " |
  "vm_lang_of_ts_lang (If c t f) = If c (vm_lang_of_ts_lang t) (vm_lang_of_ts_lang f)" |
  "vm_lang_of_ts_lang (While b Imix Ispec c) = While b (vm_of_ts ` Imix) (vm_of_ts ` Ispec) (vm_lang_of_ts_lang c) " |
  "vm_lang_of_ts_lang (DoWhile Imix Ispec c b) = DoWhile (vm_of_ts ` Imix) (vm_of_ts ` Ispec) (vm_lang_of_ts_lang c) b "

  
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
  for rg :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) varmap'"
  and glb :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) varmap'"

context simasm_rules
begin

abbreviation rules_abv ("_,_ \<turnstile> _ {_} _" [65,0,0,0,65] 65)
  where "rules_abv R G P c Q \<equiv> rules R G P c Q"

abbreviation lifted_abv ("_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,20] 20)
  where "lifted_abv R G P c Q \<equiv> 
      (ts_rel_of_vm_rel (step\<^sub>t R)), (ts_rel_of_vm_rel (step G)) \<turnstile> (ts_pred_of_vm_pred P) {(lift\<^sub>c c com.Nil {})} (ts_pred_of_vm_pred Q)" 

abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0] 45) 
 where "validity_abv c P R G Q \<equiv> validity (lift\<^sub>c c com.Nil {}) P (ts_rel_of_vm_rel (step\<^sub>t R)) (ts_rel_of_vm_rel (step G)) Q" 

text \<open>An ordering property on contexts\<close>
definition context_order 
  ("_,_ \<turnstile>\<^sub>w _ \<ge> _" [100,0,0,100] 60)
  where "context_order R G P Q \<equiv> 
    (stable\<^sub>t R Q \<and> wellformed R G) \<longrightarrow> ((P \<subseteq> Q) \<and> stable\<^sub>t R P)"

text \<open>The validity property we intend to show, abstracts over the preservation of wellformedness\<close>
definition valid 
  ("_,_ \<turnstile>\<^sub>w _ {_} _" [100,0,0,0,100] 60)
  where "valid R G P c Q \<equiv>  
     (wellformed R G \<and> stable\<^sub>t R Q \<and> guar\<^sub>c (vm_lang_of_ts_lang c) G) \<longrightarrow> (stable\<^sub>t R P \<and> (R,G \<turnstile>\<^sub>s P {c} Q))" 


lemma vm_of_ts_auxupd: 
  "(vm_of_ts x)\<lparr>varmap_rec.more := f (vm_of_ts x)\<rparr> = vm_of_ts (tauxupd x (f \<circ> vm_of_ts))"
proof -
  have Is_tstack: "Is_tstack (auxupd (Rep_tstack x) (\<lambda>tstack. f (vm_of_ts (Abs_tstack tstack))))"
    by auto
  have f: "f (vm_of_ts x) = frame.more (last (Rep_tstack (tauxupd x (f \<circ> vm_of_ts))))"
    unfolding tauxupd_def 
    by (auto simp add: Is_tstack, simp add: auxupd_def Rep_tstack_inverse)
  
  show ?thesis
  using f unfolding vm_of_ts_def by auto
qed

lemma vm_of_ts_upd: 
  "(vm_of_ts s)\<lparr>varmap_st := (varmap_st (vm_of_ts s))(v := x)\<rparr> = vm_of_ts (tupdate s v x)"
unfolding vm_of_ts_def tlookup_def tupdate_def  
using lookup_update2[of "Rep_tstack s" v x] by auto

lemma vm_of_ts_bothupd:
  "(vm_of_ts s)
    \<lparr>varmap_st := (varmap_st (vm_of_ts s))(v := x),
     varmap_rec.more := f ((vm_of_ts s)\<lparr>varmap_st := (varmap_st (vm_of_ts s))(v := x)\<rparr>)\<rparr>
   = vm_of_ts (tauxupd (tupdate s v x) (f \<circ> vm_of_ts))"
using vm_of_ts_auxupd[where ?x = "tupdate s v x"] vm_of_ts_upd[of s]
by simp
  
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
    using "local.1"(1) "local.1"(2) wp.stabilizeE by blast
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
  assumes "c \<subseteq> ts_pred_of_vm_pred (local.guar (wp\<^sub>i \<alpha> \<circ> wp\<^sub>a (f \<circ> ts_of_vm)) (step G))" 
  shows "guar\<^sub>\<alpha> (liftg c \<alpha> f) (ts_rel_of_vm_rel (step G))"
using assms
unfolding liftg_def guar_def ts_pred_of_vm_pred_def ts_rel_of_vm_rel_def
proof (clarsimp; goal_cases)
  case (1 x y)
  hence x: "vm_of_ts x \<in> wp\<^sub>i \<alpha> {ta. (vm_of_ts x, ta\<lparr>varmap_rec.more := f (ts_of_vm ta)\<rparr>) \<in> step G}" sorry
  hence x2: "vm_of_ts x \<in> guar (wp\<^sub>i \<alpha> \<circ> wp\<^sub>a (f \<circ> ts_of_vm)) (step G)" unfolding wp\<^sub>r_def by simp
  then show ?case 
  proof (cases \<alpha>)
    case (assign v x')
    show ?thesis using   x2 unfolding assign wp\<^sub>r_def apply simp 
    using 1(3)   unfolding comp_def unfolding assign apply simp using vm_of_ts_bothupd[where ?s=x and ?v=v and ?f="f \<circ> ts_of_vm"] sorry
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
    then show ?thesis using 1 unfolding nop wp\<^sub>r_def apply auto using x vm_of_ts_auxupd[where ?x=x] sorry
  qed
qed

lemma stable_ts_rel_of_vm_rel[intro]: 
  assumes "stable\<^sub>t R P"
  shows "State.stable (ts_rel_of_vm_rel (step\<^sub>t R)) (ts_pred_of_vm_pred (P))"
using assms 
unfolding stable_def stabilize_def ts_pred_of_vm_pred_def ts_rel_of_vm_rel_def step\<^sub>t_def transitive_def
by auto

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
proof
  show "\<And>x. wp\<^sub>a varmap_rec.more x = id x" by simp
qed

lemma [simp]: "(\<lambda>s. frame.more (last (Rep_tstack s))) = (\<lambda>s. varmap_rec.more (vm_of_ts s))" 
proof
  show "\<And>s. frame.more (last (Rep_tstack s)) = varmap_rec.more (vm_of_ts s)"
  unfolding vm_of_ts_def by auto
qed

lemma [simp]: "ts_pred_of_vm_pred UNIV = UNIV"
unfolding ts_pred_of_vm_pred_def by simp

section \<open>Soundness\<close>

text \<open>Basic Rule for operations with vc\<close>
lemma basic_wp\<^sub>i_1:
  assumes "P \<subseteq> stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q))" "wellformed R G" "stable\<^sub>t R Q" 
  assumes "c \<subseteq> guar (wp\<^sub>i \<alpha> o wp\<^sub>a f) (step G)"           
  shows "R,G \<turnstile>\<^sub>s P {Op (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)} Q"
proof -
  have x: "vm_of_ts x \<in> c" "vm_of_ts x \<in> wp\<^sub>i \<alpha> (wp\<^sub>a f Q)"
  if "x \<in> ts_pred_of_vm_pred (stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q)))" for x 
  unfolding ts_pred_of_vm_pred_def
  by (metis Int_iff assms(2) that stabilizeE vm_of_ts_in_ts_pred_of_vm_pred)+
  
  have 1: "ts_rel_of_vm_rel (step\<^sub>t R),ts_rel_of_vm_rel(step G) \<turnstile>\<^sub>A ts_pred_of_vm_pred(stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q))) {(liftg (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts))} ts_pred_of_vm_pred Q"
  proof (rule atomicI, goal_cases)
    case 1
    then show ?case using 1 x vm_of_ts_wp_liftg by auto
  next
    case 2
    then show ?case using assms(4) using guar_of_liftg by blast
  next
    case 3
    then show ?case using stable_ts_rel_of_vm_rel assms by blast
  next
    case 4
    then show ?case using stable_ts_rel_of_vm_rel assms by blast
  qed
  (* have 2: "step\<^sub>t (step\<^sub>t G) = step\<^sub>t G" for G unfolding step\<^sub>t_def by auto *)
  (* have 3: "step (step G) = step G" for G unfolding step_def by auto *)
  have "R,G \<turnstile>\<^sub>s (stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q))) {Op (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)} Q"
    using 1 by (simp only: lift\<^sub>c.simps) (rule rules.basic)
  thus ?thesis apply (rule rules.conseq) using assms(1) by auto
qed

text \<open>Basic Rule for operations without vc\<close>
lemma basic_wp\<^sub>i_2:
  assumes "P \<subseteq> stabilize R (wp\<^sub>i \<alpha> Q)" "wellformed R G" "stable\<^sub>t R Q"
  assumes "\<forall>m. m \<in> guar (wp\<^sub>i \<alpha>) (step G)"
  shows "R, G \<turnstile>\<^sub>s P {Op UNIV \<alpha> taux} Q"
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

text \<open>A rule for cmp operations, used for If/While\<close>
lemma cmp_sound [intro!]:
  assumes "wellformed R G" "stable\<^sub>t R Q"
  assumes "P \<subseteq> stabilize R (wp\<^sub>i (cmp b) Q)"
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

lemma "R,G \<turnstile>\<^sub>w stabilize R ((wp\<^sub>s (vm_lang_of_ts_lang c) (Q\<^sup>G))\<^sup>U) {c} Q"
unfolding valid_def
apply (intro impI conjI; elim conjE)
proof (goal_cases)
  case 1
  then show ?case by auto
next
  case 2
  then show ?case
  proof (induct c arbitrary: R G)
    case Skip
    have s: "ts_pred_of_vm_pred (stabilize R (Q\<^sup>G)\<^sup>U) \<subseteq> ts_pred_of_vm_pred Q" unfolding ts_pred_of_vm_pred_def restrict_pred_def gl_lift_pred_def apply auto
      by (metis (no_types, lifting) Skip.prems(1) mem_Collect_eq varmap_rec.surjective wp.stabilizeE)
    have q: "ts_rel_of_vm_rel (step\<^sub>t R),ts_rel_of_vm_rel (step G) \<turnstile> ts_pred_of_vm_pred (Q) {Nil} ts_pred_of_vm_pred (Q)"
      apply (rule rules.nil) apply (rule stable_ts_rel_of_vm_rel)
      using Skip.prems(1) Skip.prems(4) Skip by simp
    then show ?case unfolding valid_def 
    apply auto using q s by (meson equalityD2 rules.rules.conseq rules_axioms)
  next
    case (Op c \<alpha> f)
    have "c \<subseteq> ts_pred_of_vm_pred (local.guar (wp\<^sub>i \<alpha> \<circ> wp\<^sub>a (f \<circ> ts_of_vm)) (step G))" 
      using Op unfolding ts_pred_of_vm_pred_def by auto
    thm guar_of_liftg
    hence "guar\<^sub>\<alpha> (liftg (c) \<alpha> f) (ts_rel_of_vm_rel (step G))" using guar_of_liftg' by auto

    
    show ?case unfolding valid_def apply clarsimp 
    apply (rule rules.basic)
    unfolding atomic_rule_def 
    apply auto 
    defer
    using \<open>guar\<^sub>\<alpha> (liftg c \<alpha> f) (ts_rel_of_vm_rel (step G))\<close> apply linarith
    defer
    using Op.prems(2) apply blast 
    defer
    using Op.prems(1) Op.prems(4) apply blast
    
    
    
  next
    case (Seq c1 c2)
    then show ?case sorry
  next
    case (If x1 c1 c2)
    then show ?case sorry
  next
    case (While x1 x2 x3 c)
    then show ?case sorry
  next
    case (DoWhile x1 x2 c x4)
    then show ?case sorry
  qed
qed

lemma if_wp:
  "R,G \<turnstile>\<^sub>w P\<^sub>1 {c\<^sub>1} Q \<Longrightarrow> R,G \<turnstile>\<^sub>w P\<^sub>2 {c\<^sub>2} Q \<Longrightarrow>
  R,G \<turnstile>\<^sub>w stabilize R ((wp\<^sub>s (vm_lang_of_ts_lang (If b c\<^sub>1 c\<^sub>2)) (Q\<^sup>G))\<^sup>U) {If b c\<^sub>1 c\<^sub>2} UNIV \<Longrightarrow>
  P \<subseteq> (wp\<^sub>i (cmp b) P\<^sub>1 \<inter> wp\<^sub>i (ncmp b) P\<^sub>2) \<Longrightarrow>
            R,G \<turnstile>\<^sub>w stabilize R P {If b c\<^sub>1 c\<^sub>2} Q"
  unfolding valid_def apply clarsimp
apply standard 
apply blast
proof (rule rules.choice, standard, goal_cases)
  case (1 l)
  have "ts_rel_of_vm_rel
          (step\<^sub>t
            R),ts_rel_of_vm_rel
                (step
                  G) \<turnstile> ts_pred_of_vm_pred
                           (((wp\<^sub>s (vm_lang_of_ts_lang c\<^sub>1) (Q\<^sup>G) \<inter> wp\<^sub>s (vm_lang_of_ts_lang c\<^sub>2) (Q\<^sup>G))\<^sup>U) \<inter>

                           ({s. ev\<^sub>B (varmap_st s) b \<longrightarrow> s \<in> P\<^sub>1} \<inter>
                            {s. \<not> ev\<^sub>B (varmap_st s) b \<longrightarrow>
                                s \<in> P\<^sub>2})) {(\<triangle> Capture (emptyFrame (wr\<^sub>l c\<^sub>2)) (Seqw (lift\<^sub>c c\<^sub>2 com.Nil {}) com.Nil)) . Seqw (Basic (liftl (cmp b))) (lift\<^sub>c c\<^sub>1 com.Nil {})} ts_pred_of_vm_pred Q"
  proof (rule rules.seq)
  let ?M = "ts_pred_of_vm_pred (stabilize R (P\<^sub>1 \<inter> {s. ev\<^sub>B (varmap_st s) b}))"
  have cmp: "ts_rel_of_vm_rel (step\<^sub>t R),ts_rel_of_vm_rel (step G) \<turnstile> ?M {Basic (liftl (cmp b))} ?M"
    apply (rule rules.basic) unfolding atomic_rule_def liftl_def wp_def guar_def apply auto using 1(3) unfolding reflexive_def step_def 
    sorry    using 1 by blast
  show "ts_rel_of_vm_rel (step\<^sub>t R),ts_rel_of_vm_rel (step G) \<turnstile> ?M {Seqw (Basic (liftl (cmp b))) (lift\<^sub>c c\<^sub>1 com.Nil {})} ts_pred_of_vm_pred Q"
    apply (rule rules.seq[where ?M = ?M]) using 1(8)
    apply (meson "local.1"(1) Int_iff conseq subsetI vm_of_ts_in_ts_pred_of_vm_pred wp.stabilizeE)
    using cmp.
  show " ts_rel_of_vm_rel
     (step\<^sub>t
       R),ts_rel_of_vm_rel
           (step
             G) \<turnstile> ts_pred_of_vm_pred
                    (((wp\<^sub>s (vm_lang_of_ts_lang c\<^sub>1) (Q\<^sup>G) \<inter> wp\<^sub>s (vm_lang_of_ts_lang c\<^sub>2) (Q\<^sup>G))\<^sup>U) \<inter>
                     ({s. ev\<^sub>B (varmap_st s) b \<longrightarrow> s \<in> P\<^sub>1} \<inter>
                      {s. \<not> ev\<^sub>B (varmap_st s) b \<longrightarrow>
                          s \<in> P\<^sub>2})) {\<triangle> Capture (emptyFrame (wr\<^sub>l c\<^sub>2)) (Seqw (lift\<^sub>c c\<^sub>2 com.Nil {}) com.Nil)} ts_pred_of_vm_pred (stabilize R (P\<^sub>1 \<inter> {s. ev\<^sub>B (varmap_st s) b})) "
    apply (rule rules.interr) prefer 4 apply auto apply (rule rules.capture)
  qed
  then show ?case apply (cases "l = 0"; simp)
qed
  apply (rule local.rules.seq)
  prefer 2
   apply (intro rules.choice)
   apply (intro allI)
   apply (simp split: if_splits)
   apply (intro conjI impI)
  using cmp_sound rules.rules.seq rules.rules.interr stabilize_entail subsetI 
  apply simp
  prefer 3
(*            R,G \<turnstile>\<^sub>w stabilize R (wp\<^sub>s c\<^sub>2 (wp\<^sub>s c\<^sub>3 Q) \<inter> wp\<^sub>s c\<^sub>1 (wp\<^sub>s c\<^sub>3 Q)) \<inter>  *)
(*    apply (simp add: cmp_sound rules.rules.seq stabilize_entail subsetI)+  
  by blast 
*)

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
  assumes "P = {}"
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
