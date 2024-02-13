theory SimAsm_Security
  imports SimAsm_Rules SimAsm_WPIF "HOL-Algebra.Lattice" "../Security" 
begin

(* Temporary definitions to set up access to the components of the tuple type 
      'v option = ('val option, 'sec option) 
   which provides a value and a security level for each variable;
   and access to the security level \<Gamma> of each variable 

   \<L> general lattice 
   \<L>(x) = 'condSec expression, evaluation with 
   ev\<^sub>S m (\<L>(x)) :: 'sec option
   Axiom sec_aux: aux upd does not affect ev\<^sub>S result
 
*)

(*
   'r variable type (register)
   'v value type
   'sec security level type 
   'a auxiliary 
*)

type_synonym ('v, 'sec) val_sec = "'v \<times> 'sec" 
type_synonym ('r,'v,'sec,'a) tstack_sec = "('r,('v,'sec) val_sec,'a) tstack"

locale vst =                                          (* (val,sec) tuple*)
  fixes val :: "('v,'sec) val_sec \<Rightarrow> 'v option"
    and level :: "('v,'sec) val_sec \<Rightarrow> 'sec option"
    and ev\<^sub>S :: "('r,'v,'sec,'a) tstack_sec \<Rightarrow> 'condSec_exp \<Rightarrow> 'sec option" (* eval of cond. Security expr *)
    and attkLev :: "'sec"

locale simasm_sec =  
   vst val level ev\<^sub>S attkLev +  simasm_rules 
   for val :: "('v,'sec::bounded_lattice) val_sec \<Rightarrow> 'v option"
    and level :: "('v,'sec::bounded_lattice) val_sec \<Rightarrow> 'sec option"
    and ev\<^sub>S :: "('r,'v,'sec::bounded_lattice ,'a) tstack_sec \<Rightarrow> 'condSec_exp \<Rightarrow> 'sec option" (* eval of cond. Security expr *)
    and attkLev :: "'sec"
    and st :: " ('r,'v,'sec::bounded_lattice ,'a) tstack_sec \<Rightarrow> 'r \<Rightarrow> ('v,'sec) val_sec"
    and st_upd :: "('r,'v,'sec::bounded_lattice ,'a) tstack_sec \<Rightarrow> 'r \<Rightarrow> ('v, 'sec) val_sec \<Rightarrow> 
                                                           ('r,'v,'sec,'a) tstack_sec"
    and aux :: "('r,'v,'sec::bounded_lattice ,'a) tstack_sec \<Rightarrow> 'a"
    and aux_upd :: "('r,'v,'sec::bounded_lattice ,'a) tstack_sec \<Rightarrow> (('r,'v,'sec,'a) tstack_sec \<Rightarrow> 'a)  \<Rightarrow>
                                                           ('r,'v,'sec,'a) tstack_sec"
(*    and exists_act = "undefined :: ('r,'v,'a) auxopSt"  *)
    and push :: "('r,'v,'sec::bounded_lattice ,'a) tstack_sec \<Rightarrow> ('r,'v,'a option) frame_scheme \<Rightarrow> 
                                                           ('r,'v,'sec,'a) tstack_sec"
      




context simasm_sec
begin

(* compute supremum with bot over list of elements *)
definition supl :: "'sec  list \<Rightarrow> 'sec"
  where "supl l \<equiv> fold sup l bot"

definition \<Gamma> :: "('r,'v,'sec::bounded_lattice,'a) tstack_sec \<Rightarrow> 'r \<Rightarrow> 'sec option"
  where "\<Gamma> m  \<equiv> \<lambda>v. level(st m v)"

(* since (st m) gives us tuple ('val, 'sec) *)
definition stval :: "('r,'v,'sec::bounded_lattice,'a) tstack_sec \<Rightarrow> 'r \<Rightarrow> 'v option"
  where "stval m \<equiv> \<lambda>v. val(st m v)"

definition flow_sec
  where "flow_sec m x \<L> \<equiv> the(\<Gamma> m x) \<le> the(ev\<^sub>S m (\<L> x))"



(* bounded_lattice =  lattice + weak_partial_order_bottom + weak_partial_order_top
    i.e., carrier L
          = eq on obj in carrier L  (refl sym trans)
          \<le> le order relation over carrier L (refl antisym trans congr)
          exists bottom and top in carrier L
          inf and sup over two elements exists
*)

term \<Gamma>

text \<open> Some access functions on trees \<close>

fun base\<Gamma> :: "('r,'v,'sec,'a) tstack_sec \<Rightarrow> 'r \<Rightarrow> 'sec option"
  where "base\<Gamma> t var =  level(tbase_st t var)" 

fun baseSt :: "('r,'v,'sec,'a) tstack_sec \<Rightarrow> 'r \<Rightarrow> 'v option"
  where "baseSt t var =  val(tbase_st t var)" 


text \<open>Describe low equivalence between two memories for one \<Gamma>,
      this is more precise than describing low-equivalence over the security classificaiton \<L> 
      Classification \<L> :: ('g,'r) var => 'condSec_exp\<close>

(* what do we do if \<Gamma> is undefined, i.e., \<Gamma> = None *)

definition low_equiv1
  ("_ =\<^bsub>_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>Gamma\<^esub> m\<^sub>2 \<equiv> \<forall>x. (the(Gamma x) \<le> attkLev) \<longrightarrow> st m\<^sub>1 x = st m\<^sub>2 x"
(*  where "m\<^sub>1 =\<^bsub>Gamma\<^esub> m\<^sub>2 \<equiv> \<forall>x. Gamma x \<longrightarrow> st m\<^sub>1 x = st m\<^sub>2 x" *)

text \<open> Set of secure states: 
       Security invariant policy, ensuring low \<L> variables have a low \<Gamma>.\<close>
definition policy 
  where "policy \<L> \<equiv> {m. \<forall>x. the(\<Gamma> m x) \<le> the(ev\<^sub>S m (\<L> x))}"
(*  where "policy \<L> \<equiv> {m. \<forall>x. st m \<in> \<L> x \<longrightarrow> \<Gamma> m x }" *)

text \<open> low equivalence has to hold for the security level \<Gamma> over both states, m1 and m2 \<close>

definition low_equiv 
  ("_ =\<^bsub>_,_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>\<L>,P\<^esub> m\<^sub>2 \<equiv> 
             m\<^sub>1 \<in> policy \<L> \<inter> P \<and> m\<^sub>2 \<in> policy \<L> \<inter> P \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>1\<^esub> m\<^sub>2 \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>2\<^esub> m\<^sub>2" 

text \<open>S \<L> relates states which are low-equivalent and satisfy the security invariant.\<close>
definition S :: "('r \<Rightarrow> 'condSec_exp) \<Rightarrow> ('r,'v,'sec,'a) tstack_sec rel"
  where "S \<L> \<equiv> {(m,m'). m =\<^bsub>\<L>,UNIV\<^esub> m'}"






(*
text \<open> Interpretation of abstract locale security \<close>

 interpretation security "someAuxOp" "someState"
  done
 *)

(* Simplify lemmas on sec_states *)

(*  
lemma [simp]:
  assumes "st (aux_upd m f) = st m"    (* axiom in locale state (State2.thy) *)
  shows "\<Gamma> (aux_upd m f) = \<Gamma> m"
  using assms by (simp add: \<Gamma>_def) 

(*
   "\<Gamma> (m(aux: f)) = \<Gamma> m" 
  by (simp add: aux_upd_def state_rec.defs \<Gamma>_def) 
 *)

(* lemma [simp]:
  "st (m(aux: f)) = st m"
  by (simp add: aux_upd_def)
 *)

 lemma [simp]:
  shows "(\<forall>x. the (\<Gamma> m x) \<le> the (ev\<^sub>S (aux_upd m f) (\<L> x))) = 
    (\<forall>x. the (\<Gamma> m x) \<le> the (ev\<^sub>S m (\<L> x)))" using assms apply (simp add: \<Gamma>_def) 


lemma [simp]:
  "(aux_upd m f) \<in> policy \<L> = (m \<in> policy \<L>)" 
  unfolding policy_def by simp

lemma [simp]:
  "(m\<^sub>1(aux: f) =\<^bsub>\<L>,UNIV\<^esub> m\<^sub>2(aux: f)) = (m\<^sub>1 =\<^bsub>\<L>,UNIV\<^esub> m\<^sub>2)"
  unfolding low_equiv_def low_equiv1_def by simp  

lemma sec_pres_aux:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> S \<L>"
  shows "(m\<^sub>1(aux: f), m\<^sub>2(aux: f)) \<in> S \<L>"
  using assms unfolding S_def by simp 


(* Simplify lemmas on SecTrees *)

lemma base\<Gamma>Aux [simp]:
  "base\<Gamma> (t(aux\<^sub>t: f)) = base\<Gamma> t" unfolding tr_aux_upd_def 
  by (induct t)(simp_all add: aux_upd_def state_rec.defs \<Gamma>_def) 


lemma [simp]:
  "st (SimAsm_StateTree.top (t(aux\<^sub>t: f))) = st (SimAsm_StateTree.top t)"
  by (simp add: tr_aux_upd_def state_rec.defs)

lemma [simp]:
  "st (base (t(aux\<^sub>t: f))) = st (base t)"
  by  (induct t)(simp_all add: tr_aux_upd_def state_rec.defs)

lemma baseStAux [simp]:
  "baseSt (t(aux\<^sub>t: f)) = baseSt t" 
  by (induct t; simp add: tr_aux_upd_def stval_def) 


lemma [simp]:
  "\<Gamma> (base (t(aux\<^sub>t: f))) = \<Gamma> (base t)"
  by (induct t) (simp_all add: tr_aux_upd_def \<Gamma>_def)


lemma [simp]:
  "t(aux\<^sub>t: f) \<in> policyTree \<L> = (t \<in> policyTree \<L>)" 
  unfolding policyTree_def 
proof (induct t)
  case (Base x)
  then show ?case 
    apply (simp add: tr_aux_upd_def policyTree_def policy_def)
    using sec_aux state_rec.defs \<Gamma>_def by (simp add: aux_upd_def)
next
  case (Branch t1 t2)
  then show ?case by (simp add: tr_aux_upd_def policyTree_def)
qed

lemma [simp]:
  "base (t(aux\<^sub>t: f)) \<in> policy \<L> = ((base t) \<in> policy \<L>)"
  apply (induct t)
    apply (simp_all add: policy_def tr_aux_upd_def)
  using sec_aux state_rec.defs \<Gamma>_def by (simp add: aux_upd_def)

lemma low_equivT1Aux:
 "base t\<^sub>1 =\<^bsub>\<Gamma> (base t\<^sub>1)\<^esub> base t\<^sub>2 \<Longrightarrow> 
         base (t\<^sub>1(aux\<^sub>t: f)) =\<^bsub>\<Gamma> (base t\<^sub>1)\<^esub> base (t\<^sub>2(aux\<^sub>t: f))"
  unfolding low_equiv1_def by simp

lemma low_equivT2Aux:
 "base t\<^sub>1 =\<^bsub>\<Gamma> (base t\<^sub>2)\<^esub> base t\<^sub>2 \<Longrightarrow> 
         base (t\<^sub>1(aux\<^sub>t: f)) =\<^bsub>\<Gamma> (base t\<^sub>2)\<^esub> base (t\<^sub>2(aux\<^sub>t: f))"
  unfolding low_equiv1_def by simp

lemma low_equivBaseAux:
 "base t\<^sub>1 \<in> policy \<L> \<and> base t\<^sub>2 \<in> policy \<L> \<and> 
   base t\<^sub>1 =\<^bsub>\<Gamma> (base t\<^sub>1)\<^esub> base t\<^sub>2 \<and> base t\<^sub>1 =\<^bsub>\<Gamma> (base t\<^sub>2)\<^esub> base t\<^sub>2 \<Longrightarrow>
    base (t\<^sub>1(aux\<^sub>t: f)) =\<^bsub>\<Gamma> (base t\<^sub>1)\<^esub> base (t\<^sub>2(aux\<^sub>t: f)) \<and> 
    base (t\<^sub>1(aux\<^sub>t: f)) =\<^bsub>\<Gamma> (base t\<^sub>2)\<^esub> base (t\<^sub>2(aux\<^sub>t: f))"
  using low_equivT1Aux low_equivT2Aux by simp

lemma low_equivTreesAux:
 "t\<^sub>1 \<approx>\<^bsub>\<L>,UNIV\<^esub> t\<^sub>2 \<Longrightarrow> t\<^sub>1(aux\<^sub>t: f) \<approx>\<^bsub>\<L>,UNIV\<^esub> t\<^sub>2(aux\<^sub>t: f)"    
  unfolding low_equivTree_def low_equiv_def using base\<Gamma>Aux baseStAux apply simp
  using low_equivBaseAux[of t\<^sub>1 \<L> t\<^sub>2 f] by simp
  
lemma sec_pres_auxTree:
  assumes "(t\<^sub>1, t\<^sub>2) \<in> STree \<L>"
  shows "(t\<^sub>1(aux\<^sub>t: f), t\<^sub>2(aux\<^sub>t: f)) \<in> STree \<L>"
  using assms unfolding STree_def by (simp add: low_equivTreesAux)
*)



end

