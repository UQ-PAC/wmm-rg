theory SimAsm_Security
  imports SimAsm "HOL-Algebra.Lattice"
begin

(* Temporary definitions to set up access to the components of the tuple type 
      'v option = ('val option, 'sec option) 
   which provides a value and a security level for each variable;
   and access to the security level \<Gamma> of each variable 
*)


locale vst =                                          (* (val,sec) tuple*)
  fixes val :: "'v option \<Rightarrow> 'val option"
    and level :: "'v option \<Rightarrow> 'sec::bounded_lattice option"
    and ev\<^sub>S :: "('v,'g, 'r,'a) state \<Rightarrow> 'condSec_exp \<Rightarrow> 'sec::bounded_lattice option"
    and attkLev :: "'sec::bounded_lattice"
  assumes sec_aux: "ev\<^sub>S (m(aux:f)) e = ev\<^sub>S m e"
begin

(* compute supremum with bot over list of elements *)
definition supl :: "'sec::bounded_lattice list \<Rightarrow> 'sec"
  where "supl l \<equiv> fold sup l bot"

definition \<Gamma> :: "('v,'g,'r,'a) state \<Rightarrow> ('g,'r) var \<Rightarrow> 'sec option"
  where "\<Gamma> m  \<equiv> \<lambda>v. level(st m v)"

(* since (st m) gives us tuple ('val, 'sec) *)
definition stval :: "('v,'g,'r,'a) state \<Rightarrow> ('g,'r) var \<Rightarrow> 'val option"
  where "stval m \<equiv> \<lambda>v. val(st m v)"

definition flow_sec
  where "flow_sec m x \<L> \<equiv> the(\<Gamma> m x) \<le> the(ev\<^sub>S m (\<L> x))"

end


(* bounded_lattice =  lattice + weak_partial_order_bottom + weak_partial_order_top
    i.e., carrier L
          = eq on obj in carrier L  (refl sym trans)
          \<le> le order relation over carrier L (refl antisym trans congr)
          exists bottom and top in carrier L
          inf and sup over two elements exists
*)

context vst

begin

print_locale vst
term \<Gamma>


text \<open>Describe low equivalence between two memories for one \<Gamma>,
      this is more precise than describing low-equivalence over the security classificaiton \<L> 
      Classification \<L> :: ('g,'r) var => 'condSec_exp\<close>

(* what do we do if \<Gamma> is undefined, i.e., \<Gamma> = None *)

definition low_equiv1
  ("_ =\<^bsub>_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>Gamma\<^esub> m\<^sub>2 \<equiv> \<forall>x. (the(Gamma x) \<le> attkLev) \<longrightarrow> st m\<^sub>1 x = st m\<^sub>2 x"
(*  where "m\<^sub>1 =\<^bsub>Gamma\<^esub> m\<^sub>2 \<equiv> \<forall>x. Gamma x \<longrightarrow> st m\<^sub>1 x = st m\<^sub>2 x" *)


definition policy 
  where "policy \<L> \<equiv> {m. \<forall>x. the(\<Gamma> m x) \<le> the(ev\<^sub>S m (\<L> x))}"
(*  where "policy \<L> \<equiv> {m. \<forall>x. st m \<in> \<L> x \<longrightarrow> \<Gamma> m x }" *)

text \<open> low equivalence has to hold for the security level \<Gamma> over both states, m1 and m2 \<close>

definition low_equiv 
  ("_ =\<^bsub>_,_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>\<L>,P\<^esub> m\<^sub>2 \<equiv> 
             m\<^sub>1 \<in> policy \<L> \<inter> P \<and> m\<^sub>2 \<in> policy \<L> \<inter> P \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>1\<^esub> m\<^sub>2 \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>2\<^esub> m\<^sub>2"

definition S
  where "S \<L> \<equiv> {(m,m'). m =\<^bsub>\<L>,UNIV\<^esub> m'}"

(* definitions on trees  *)
definition low_equiv1Tree ("_ \<approx>\<^bsub>_\<^esub> _" [70,0,70] 100)
  where "t\<^sub>1 \<approx>\<^bsub>Gamma\<^esub> t\<^sub>2 \<equiv> \<forall>x. (base t\<^sub>1) =\<^bsub>Gamma\<^esub> (base t\<^sub>2)" 
(*  where "low_equiv1Tree Gamma t\<^sub>1 t\<^sub>2 \<equiv> \<forall>x. Gamma x \<longrightarrow> lookupSt t\<^sub>1 x = lookupSt t\<^sub>2 x" *)

definition policyTree
    where "policyTree \<L> \<equiv> {t. (base t) \<in> policy \<L>}"

definition low_equivTree  ("_ \<approx>\<^bsub>_,_\<^esub> _" [70,0,70] 100) 
  where "t\<^sub>1 \<approx>\<^bsub>\<L>,P\<^esub> t\<^sub>2 \<equiv> (base t\<^sub>1)  =\<^bsub>\<L>,P\<^esub> (base t\<^sub>2)"

(*  where "low_equivTree \<L> P t\<^sub>1 t\<^sub>2 \<equiv>
             t\<^sub>1 \<in> policyTree \<L> \<inter> P \<and> t\<^sub>2 \<in> policyTree \<L> \<inter> P 
              \<and> low_equiv1Tree (lookup\<Gamma> t\<^sub>1) t\<^sub>1 t\<^sub>2 \<and> low_equiv1Tree (lookup\<Gamma> t\<^sub>2) t\<^sub>1 t\<^sub>2"
*)

definition STree
  where "STree \<L> \<equiv> {(t,t'). t \<approx>\<^bsub>\<L>,UNIV\<^esub> t'}"

(* Simplify lemmas on sec_states *)

lemma [simp]:
  "\<Gamma> (m(aux: f)) = \<Gamma> m"
  by (simp add: aux_upd_def state_rec.defs \<Gamma>_def) 

lemma [simp]:
  "st (m(aux: f)) = st m"
  by (simp add: aux_upd_def)

lemma [simp]:
 "(\<forall>x. the (\<Gamma> m x) \<le> the (ev\<^sub>S (m(aux: f)) (\<L> x))) = 
    (\<forall>x. the (\<Gamma> m x) \<le> the (ev\<^sub>S m (\<L> x)))" using sec_aux by simp

lemma [simp]:
  "m(aux: f) \<in> policy \<L> = (m \<in> policy \<L>)" 
  unfolding policy_def by simp 

lemma [simp]:
  "(m\<^sub>1(aux: f) =\<^bsub>\<L>,UNIV\<^esub> m\<^sub>2(aux: f)) = (m\<^sub>1 =\<^bsub>\<L>,UNIV\<^esub> m\<^sub>2)"
  unfolding low_equiv_def low_equiv1_def by simp
  
lemma sec_pres_aux:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> S \<L>"
  shows "(m\<^sub>1(aux: f), m\<^sub>2(aux: f)) \<in> S \<L>"
  using assms unfolding S_def by simp 

(* Simplify lemmas on SecTrees *)

lemma [simp]:
  "lookup\<Gamma> (t(aux\<^sub>t: f)) = lookup\<Gamma> t"
proof (induct t)
  case (Base x)
  then show ?case apply (simp add: tr_aux_upd_def state_rec.defs)
next
  case (Branch t1 t2)
  then show ?case by (simp add: tr_aux_upd_def sec_state_rec.defs)
qed

lemma [simp]:
  "st (top (t(aux\<^sub>t: f))) = st (top t)"
  by (simp add: tr_aux_upd_def)

lemma [simp]:
  "lookupSt (t(aux\<^sub>t: f)) = lookupSt t"
proof (induct t)
  case (Base x)
  then show ?case by (simp add: tr_aux_upd_def) 
next
  case (Branch t1 t2)
  then show ?case by (simp add: tr_aux_upd_def) 
qed


lemma [simp]:
  "\<Gamma> (base (t(aux\<^sub>t: f))) = \<Gamma> (base t)"
  apply (simp add: tr_aux_upd_def) 
  by (smt (verit, ccfv_threshold) base.simps(1) base.simps(2) sec_state_rec.select_convs(1) 
                sec_state_rec.simps(4) sec_state_rec.surjective top.simps(1) tree_upd.elims)


lemma [simp]:
  "t(aux\<^sub>t: f) \<in> policyTree \<L> = (t \<in> policyTree \<L>)" 
  unfolding policyTree_def 
proof (induct t)
  case (Base x)
  then show ?case by (simp add: tr_aux_upd_def policyTree_def)
next
  case (Branch t1 t2)
  then show ?case by (simp add: tr_aux_upd_def policyTree_def)
qed


lemma [simp]:
  "low_equivTree \<L> UNIV (t\<^sub>1(aux\<^sub>t: f)) (t\<^sub>2(aux\<^sub>t: f)) = low_equivTree \<L> UNIV t\<^sub>1 t\<^sub>2"
  unfolding low_equivTree_def low_equiv1Tree_def by simp
  
lemma sec_pres_auxTree:
  assumes "(t\<^sub>1, t\<^sub>2) \<in> STree \<L>"
  shows "(t\<^sub>1(aux\<^sub>t: f), t\<^sub>2(aux\<^sub>t: f)) \<in> STree \<L>"
  using assms unfolding STree_def by simp 

end (* of locale valueTuple *)

end

(*
lemma "aux_upd m f = \<lparr> st=(st m), cap=(cap m), initState=(initState m), \<dots>=(f m)\<rparr>"
  by (simp add: aux_upd_def)

lemma "m(aux: f) = \<lparr> st=(st m), cap=(cap m), initState=(initState m), \<dots>=(f m)\<rparr>"
  by (simp add: aux_upd_def)

lemma "sec_aux_upd m f = \<lparr> st=(st m), cap=(cap m), initState=(initState m), \<Gamma>=(\<Gamma> m),\<dots>=(f m)\<rparr>"
  by (simp add: sec_aux_upd_def)

lemma "m(aux\<^sub>g: f) = \<lparr> st=(st m), cap=(cap m), initState=(initState m), \<Gamma>=(\<Gamma> m), \<dots>=(f m)\<rparr>"
  by (simp add: sec_aux_upd_def)
*)