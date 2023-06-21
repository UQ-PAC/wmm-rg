theory SimAsm_Rules
  imports SimAsm_StateStack SimAsm_Reasoning 
  begin

lift_definition vm_of_ts :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) varmap'" 
  is "\<lambda>s. \<lparr> varmap_st = tlookup s, \<dots> = frame.more (last (Rep_tstack s))\<rparr>".

lift_definition ts_of_vm :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) tstack" 
  is "inv vm_of_ts".

lemma ts_of_vm_exists: "\<exists>ts. vm_of_ts ts = vm"
proof
  let ?s = "[\<lparr> frame_st = Some \<circ> varmap_st vm, frame_cap = UNIV, \<dots> = more vm \<rparr>]"
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
  moreover have "more vm = frame.more (last (Rep_tstack (ts_of_vm vm)))"
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
  "ts_lang_of_vm_lang (Seq a b) = Seq (ts_lang_of_vm_lang a) (ts_lang_of_vm_lang b) " |
  "ts_lang_of_vm_lang (If c t f) = If c (ts_lang_of_vm_lang t) (ts_lang_of_vm_lang f)" |
  "ts_lang_of_vm_lang (While b Imix Ispec c) = While b (ts_pred_of_vm_pred Imix) (ts_pred_of_vm_pred Ispec) (ts_lang_of_vm_lang c) " |
  "ts_lang_of_vm_lang (DoWhile Imix Ispec c b) = DoWhile (ts_pred_of_vm_pred Imix) (ts_pred_of_vm_pred Ispec) (ts_lang_of_vm_lang c) b "

fun vm_lang_of_ts_lang :: "('r,'v,('r,'v,'a)tstack,'a) lang \<Rightarrow> ('r, 'v, ('r, 'v, 'a) varmap', 'a) lang" where
  "vm_lang_of_ts_lang (Skip) = Skip " |
  "vm_lang_of_ts_lang (Op pred op auxfn) = Op (vm_of_ts ` pred) op (auxfn \<circ> ts_of_vm)" |
  "vm_lang_of_ts_lang (Seq a b) = Seq (vm_lang_of_ts_lang a) (vm_lang_of_ts_lang b) " |
  "vm_lang_of_ts_lang (If c t f) = If c (vm_lang_of_ts_lang t) (vm_lang_of_ts_lang f)" |
  "vm_lang_of_ts_lang (While b Imix Ispec c) = While b (vm_of_ts ` Imix) (vm_of_ts ` Ispec) (vm_lang_of_ts_lang c) " |
  "vm_lang_of_ts_lang (DoWhile Imix Ispec c b) = DoWhile (vm_of_ts ` Imix) (vm_of_ts ` Ispec) (vm_lang_of_ts_lang c) b "

  
locale simasm_rules = 
  reasoning_spec 
    where st = tlookup
    and st_upd = tupdate
    and aux = taux
    and aux_upd = tauxupd
    and rg = rg 
    and glb = glb
  + rules 
    where exists_act = "undefined :: ('r,'v,'a) auxopSt"
    and push = "tstack_push :: ('r,'v,'a) tstack \<Rightarrow> ('r,'v) frame \<Rightarrow> ('r,'v,'a) tstack"
  for st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v"
  and rg :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) varmap'"
  and glb :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) varmap'"
  
context simasm_rules
begin

(* interpretation srules: rules undefined tstack_push *)
(* proof (unfold_locales, standard) *)
  (* fix m s m' s' *)
  (* assume "tstack_push m s = tstack_push m' s'"  *)
  (* hence 1:  *)
    (* "Abs_tstack (\<lparr>frame_st = frame_st s, frame_cap = frame_cap s, \<dots> = undefined\<rparr> # Rep_tstack m)  *)
    (* = Abs_tstack (\<lparr>frame_st = frame_st s', frame_cap = frame_cap s', \<dots> = undefined\<rparr> # Rep_tstack m')" *)
    (* (is "Abs_tstack ?L = Abs_tstack ?R") *)
    (* unfolding tstack_push_def by simp *)
  (* let "?s # Rep_tstack m" = ?L *)
  (* let "?s' # Rep_tstack m'" = ?R *)
  (* from 1 have Is_tstack: "Is_tstack ?L" "Is_tstack ?R" "Is_tstack (Rep_tstack m)" "Is_tstack (Rep_tstack m')"  *)
    (* by auto *)
  (* hence "?s = ?s'" "Rep_tstack m = Rep_tstack m'" using 1 RepAbs_id list.inject by metis+ *)
  (* show "s = s'" using \<open>?s = ?s'\<close> using frame.equality frame.ext_inject by (metis (full_types) unit.exhaust) *)
  (* show "m = m'" using \<open>Rep_tstack m = Rep_tstack m'\<close> Rep_tstack_inject by auto *)
(* qed *)

abbreviation lifted_abv ("_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,20] 20)
  where "lifted_abv R G P c Q \<equiv> 
      rules (ts_rel_of_vm_rel (step\<^sub>t R)) (ts_rel_of_vm_rel (step G)) (ts_pred_of_vm_pred P) (lift\<^sub>c c com.Nil) (ts_pred_of_vm_pred Q)" 

term lifted_abv

abbreviation validity_abv  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0] 45) 
 where "validity_abv c P R G Q \<equiv> validity (lift\<^sub>c c com.Nil) P (ts_rel_of_vm_rel (step\<^sub>t R)) (ts_rel_of_vm_rel (step G)) Q" 

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

     
lemma tauxupd_in_ts_pred:
  assumes "x \<in> ts_pred_of_vm_pred {t. t\<lparr>varmap_rec.more := f t\<rparr> \<in> Q}" 
  shows "tauxupd x (f \<circ> vm_of_ts) \<in> ts_pred_of_vm_pred Q"
proof -
  have "\<exists>t \<in> {t. t\<lparr>varmap_rec.more := f t\<rparr> \<in> Q}. vm_of_ts x = t" using assms ts_of_vm_exists
    by (simp add: ts_pred_of_vm_pred.rep_eq) 
  hence Q: "(vm_of_ts x) \<lparr> more := f (vm_of_ts x) \<rparr> \<in> Q" by simp

  have Is_tstack: "Is_tstack (auxupd (Rep_tstack x) (\<lambda>tstack. f (vm_of_ts (Abs_tstack tstack))))"
    by auto
  have f: "f (vm_of_ts x) = frame.more (last (Rep_tstack (tauxupd x (f \<circ> vm_of_ts))))"
    unfolding tauxupd_def 
    by (auto simp add: Is_tstack, simp add: auxupd_def Rep_tstack_inverse)
  
  have "(vm_of_ts x) \<lparr> more := f (vm_of_ts x) \<rparr> = vm_of_ts (tauxupd x (f \<circ> vm_of_ts))"
  using f unfolding vm_of_ts_def by auto

  thus ?thesis using Q by (simp add: ts_pred_of_vm_pred.abs_eq)
qed

lemma ts_pred_of_vm_pred_Inter [simp]: 
  "ts_pred_of_vm_pred (P \<inter> Q) = ts_pred_of_vm_pred P \<inter> ts_pred_of_vm_pred Q"
unfolding ts_pred_of_vm_pred_def by simp

lemma
  assumes "ts_rel_of_vm_rel (step\<^sub>t R),ts_rel_of_vm_rel (step G) \<turnstile>\<^sub>A ts_pred_of_vm_pred P {liftg (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)} ts_pred_of_vm_pred Q"
  shows "step\<^sub>t R,step G \<turnstile>\<^sub>s P {Op (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)} Q"
proof (induct \<alpha>)
  case (assign x11 x12)
  have 2: "stable (ts_rel_of_vm_rel (step\<^sub>t R)) (ts_pred_of_vm_pred P)"
    using assms unfolding atomic_rule_def by simp
  have 1: "step\<^sub>t (step\<^sub>t R) = step\<^sub>t R" for R unfolding step\<^sub>t_def apply auto sorry
  show ?case 
  unfolding assign apply simp apply (rule rules.basic)
  unfolding atomic_rule_def apply auto
  unfolding liftg_def apply auto
  prefer 3 unfolding stable_def 1 apply auto
  using  2 unfolding stable_def apply auto
  using assms unfolding atomic_rule_def apply auto 
  unfolding wp_def liftg_def apply auto
  prefer 3 apply (meson State.stable_def)
  defer unfolding guar_def apply auto sorry
next
  case (cmp x2)
  then show ?case sorry
next
  case (leak x31 x32)
  then show ?case sorry
next
  case full_fence
  then show ?case sorry
next
  case nop
  then show ?case sorry
qed
     
section \<open>Soundness\<close>

text \<open>Basic Rule for operations with vc\<close>
lemma basic_wp\<^sub>i_1:
  assumes "P \<subseteq> stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q))" "wellformed R G" "stable\<^sub>t R Q" 
  assumes "c \<subseteq> guar (wp\<^sub>i \<alpha> o wp\<^sub>a f) (step G)"
  shows "(step\<^sub>t R),(step G) \<turnstile>\<^sub>s P {Op (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts)} Q"
proof -
term atomic_rule  
  have "ts_rel_of_vm_rel (step\<^sub>t R),ts_rel_of_vm_rel(step G) \<turnstile>\<^sub>A ts_pred_of_vm_pred(stabilize R (c \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q))) {(liftg (ts_pred_of_vm_pred c) \<alpha> (f \<circ> vm_of_ts))} ts_pred_of_vm_pred Q"
  using assms apply (cases \<alpha>) 

  apply (rule atomicI)
  apply auto
  proof goal_cases
  case (1 x11 x12 x)
  then show ?case sorry
  next
  case (2 x11 x12)
  then show ?case sorry
  next
  case (3 x11 x12)
  then show ?case sorry
  next
  case (4 x11 x12)
  then show ?case sorry
  next
  case (5 x2)
  then show ?case sorry
  next
  case (6 x31 x32)
  then show ?case sorry
  next
  case 7
  then show ?case sorry
  next
  case 8
  then show ?case sorry
  qed
    (* case (1 x) *)
    (* hence x: "x \<in> ts_pred_of_vm_pred (c \<inter> {t. t\<lparr>more := f t\<rparr> \<in> Q})"  *)
      (* using stabilizeE by (metis (no_types, lifting) ts_pred_of_vm_pred.abs_eq vimageE vimageI) *)
    (* thus ?case unfolding wp_def liftg_def  *)
      (* using tauxupd_in_ts_pred by auto *)
  (* next *)
    (* case 2 *)
    (* show ?case unfolding liftg_def State.guar_def apply auto using 2(3) *)
  (* next *)
    (* case 3 *)
    (* then show ?case sorry *)
  (* next *)
    (* case 4 *)
    (* then show ?case sorry *)
  (* next *)
    (* case (5 x11 x12) *)
    (* then show ?case sorry *)
  (* next *)
    (* case (6 x2) *)
    (* then show ?case sorry *)
  (* next *)
    (* case (7 x31 x32) *)
    (* then show ?case sorry *)
  (* next *)
    (* case 8 *)
    (* then show ?case sorry *)
  (* qed *)
  thus ?thesis 
qed

text \<open>Basic Rule for operations without vc\<close>
lemma basic_wp\<^sub>i_2:
  assumes "P \<subseteq> stabilize R (wp\<^sub>i \<alpha> Q)" "wellformed R G" "stable\<^sub>t R Q"
  assumes "\<forall>m. m \<in> guar (wp\<^sub>i \<alpha>) (step G)"
  shows "step\<^sub>t R,step G \<turnstile> P {Basic (liftl \<alpha>)} Q"
proof -
  have "step\<^sub>t R,step G \<turnstile>\<^sub>A stabilize R (wp\<^sub>i \<alpha> Q) {(liftl \<alpha>)} Q"
    using assms by (cases \<alpha>) (auto simp: atomic_rule_def guar_def wp_def step_def 
                                         wp\<^sub>r_def o_def liftl_def elim!: stabilizeE)
  thus ?thesis using assms by (intro conseq[OF basic]) (auto simp:)
qed

text \<open>A rule for cmp operations, used for If/While\<close>
lemma cmp_sound [intro!]:
  assumes "wellformed R G" "stable\<^sub>t R Q"
  assumes "P \<subseteq> stabilize R (wp\<^sub>i (cmp b) Q)"
  shows "step\<^sub>t R,step G \<turnstile> P {Basic ((liftl (cmp b)))} Q"
  using assms by (intro basic_wp\<^sub>i_2) (auto simp: step_def reflexive_def wp\<^sub>r_def)

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
            R,G \<turnstile>\<^sub>w stabilize R (wp\<^sub>s (If b c\<^sub>1 c\<^sub>2) Q) \<inter> 
                    stabilize R (wp\<^sub>i (cmp b) P\<^sub>1 \<inter> wp\<^sub>i (ncmp b) P\<^sub>2) {If b c\<^sub>1 c\<^sub>2} Q"
  unfolding valid_def apply clarsimp 
  apply (intro conjI)
  prefer 2
   apply (intro rules.choice)
   apply (intro allI)
   apply (simp split: if_splits)
   apply (intro conjI impI)
  using cmp_sound rules.rules.seq rules.rules.interr stabilize_entail subsetI 
  sorry
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
  assumes "J \<subseteq>  (wp\<^sub>i (cmp b) P \<inter> wp\<^sub>i (ncmp b) Q)"
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
  shows "validity_abv c P R G Q"
(*  shows "\<Turnstile> c SAT [P, R, G, Q]"  *)
proof -
  have "R,G \<turnstile>\<^sub>s wp R c Q {c} Q" using wf st g com_wp unfolding valid_def by blast
  hence "R,G \<turnstile>\<^sub>s P {c} Q" by (rule rules.conseq) (insert P, auto simp: )
  thus ?thesis by (intro sound thread) auto
qed

end (* of context wp *)

end
