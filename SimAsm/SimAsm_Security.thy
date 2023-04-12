theory SimAsm_Security
  imports SimAsm_SecTree
begin

text \<open>Describe low equivalence between two memories for one \<Gamma>,
      this is more precise than describing low-equivalence over the security classificaiton \<L> \<close>

definition low_equiv1
  ("_ =\<^bsub>_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>Gamma\<^esub> m\<^sub>2 \<equiv> \<forall>x. Gamma x \<longrightarrow> st m\<^sub>1 x = st m\<^sub>2 x"

definition low_equiv1Tree
(*  ("_ =\<^bsub>_\<^esub> _" [70,0,70] 100) *)
  where "low_equiv1Tree Gamma t\<^sub>1 t\<^sub>2 \<equiv> \<forall>x. Gamma x \<longrightarrow> lookupSt t\<^sub>1 x = lookupSt t\<^sub>2 x"

definition policy 
  where "policy \<L> \<equiv> {m. \<forall>x. st m \<in> \<L> x \<longrightarrow> \<Gamma> m x}"

definition policyTree
  where "policyTree \<L> \<equiv> {t. \<forall>x. lookupSt t \<in> \<L> x \<longrightarrow> lookup\<Gamma> t x}"


text \<open> low equivalence has to hold for the security level \<Gamma> over both states, m1 and m2 \<close>

definition low_equiv 
  ("_ =\<^bsub>_,_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>\<L>,P\<^esub> m\<^sub>2 \<equiv> 
             m\<^sub>1 \<in> policy \<L> \<inter> P \<and> m\<^sub>2 \<in> policy \<L> \<inter> P \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>1\<^esub> m\<^sub>2 \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>2\<^esub> m\<^sub>2"

definition low_equivTree
(*  ("_ =\<^bsub>_,_\<^esub> _" [70,0,70] 100) *)
  where "low_equivTree \<L> P t\<^sub>1 t\<^sub>2 \<equiv> 
             t\<^sub>1 \<in> policyTree \<L> \<inter> P \<and> t\<^sub>2 \<in> policyTree \<L> \<inter> P 
              \<and> low_equiv1Tree (lookup\<Gamma> t\<^sub>1) t\<^sub>1 t\<^sub>2 \<and> low_equiv1Tree (lookup\<Gamma> t\<^sub>2) t\<^sub>1 t\<^sub>2"

definition S
  where "S \<L> \<equiv> {(m,m'). m =\<^bsub>\<L>,UNIV\<^esub> m'}"

definition STree
  where "STree \<L> \<equiv> {(t,t'). low_equivTree \<L> UNIV t t'}"

(* Simplify lemmas on sec_states *)

lemma [simp]:
  "\<Gamma> (m(aux\<^sub>g: f)) = \<Gamma> m"
  by (simp add: sec_aux_upd_def sec_state_rec.defs) 

lemma [simp]:
  "st (m(aux\<^sub>g: f)) = st m"
  by (simp add: sec_aux_upd_def)

lemma [simp]:
  "m(aux\<^sub>g: f) \<in> policy \<L> = (m \<in> policy \<L>)" 
  unfolding policy_def by simp

lemma [simp]:
  "(m\<^sub>1(aux\<^sub>g: f) =\<^bsub>\<L>,UNIV\<^esub> m\<^sub>2(aux\<^sub>g: f)) = (m\<^sub>1 =\<^bsub>\<L>,UNIV\<^esub> m\<^sub>2)"
  unfolding low_equiv_def low_equiv1_def by simp
  
lemma sec_pres_aux:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> S \<L>"
  shows "(m\<^sub>1(aux\<^sub>g: f), m\<^sub>2(aux\<^sub>g: f)) \<in> S \<L>"
  using assms unfolding S_def by simp 

(* Simplify lemmas on SecTrees *)

lemma [simp]:
  "lookup\<Gamma> (t(aux\<^sub>t: f)) = lookup\<Gamma> t"
  apply (simp add: tr_aux_upd_def sec_state_rec.defs) 
  oops

lemma [simp]:
  "st (top (t(aux\<^sub>t: f))) = st (top t)"
  by (simp add: tr_aux_upd_def)

lemma [simp]:
  "lookupSt (t(aux\<^sub>t: f)) = lookupSt t"
  apply (simp add: tr_aux_upd_def) 
  sorry

lemma [simp]:
  "\<Gamma> (base (t(aux\<^sub>t: f))) = \<Gamma> (base t)"
  apply (simp add: tr_aux_upd_def) 
  by (smt (verit, ccfv_threshold) base.simps(1) base.simps(2) sec_state_rec.select_convs(1) 
                sec_state_rec.simps(4) sec_state_rec.surjective top.simps(1) tree_upd.elims)


lemma [simp]:
  "t(aux\<^sub>t: f) \<in> policyTree \<L> = (t \<in> policyTree \<L>)" 
  unfolding policyTree_def tr_aux_upd_def apply simp 
  sorry

lemma [simp]:
  "low_equivTree \<L> UNIV (t\<^sub>1(aux\<^sub>t: f)) (t\<^sub>2(aux\<^sub>t: f)) = low_equivTree \<L> UNIV t\<^sub>1 t\<^sub>2"
  unfolding low_equivTree_def low_equiv1Tree_def by simp
  
lemma sec_pres_auxTree:
  assumes "(t\<^sub>1, t\<^sub>2) \<in> STree \<L>"
  shows "(t\<^sub>1(aux\<^sub>t: f), t\<^sub>2(aux\<^sub>t: f)) \<in> STree \<L>"
  using assms unfolding STree_def by simp 

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