theory SimAsm_Security
  imports SimAsm_State
begin

text \<open> Extension to the state record with the auxiliary variable \<Gamma> 
        which holds the security level \<close>

datatype sec = bool

record ('v, 'a) sec_state_rec = "('v, 'a) state_rec" +
  \<Gamma> :: "'a \<Rightarrow> bool"


text \<open>Describe low equivalence between two memories for one \<Gamma>,
      this is more precise than describing low-equivalence over the security classificaiton \<L> \<close>

definition low_equiv1
  ("_ =\<^bsub>_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>Gamma\<^esub> m\<^sub>2 \<equiv> \<forall>x. Gamma x \<longrightarrow> st m\<^sub>1 x = st m\<^sub>2 x"

definition policy 
  where "policy \<L> \<equiv> {m. \<forall>x. st m \<in> \<L> x \<longrightarrow> \<Gamma> m x}"


text \<open> low equivalence has to hold for the security level \<Gamma> over both states, m1 and m2 \<close>

definition low_equiv 
  ("_ =\<^bsub>_,_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>\<L>,P\<^esub> m\<^sub>2 \<equiv> 
             m\<^sub>1 \<in> policy \<L> \<inter> P \<and> m\<^sub>2 \<in> policy \<L> \<inter> P \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>1\<^esub> m\<^sub>2 \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>2\<^esub> m\<^sub>2"

definition S
  where "S \<L> \<equiv> {(m,m'). m =\<^bsub>\<L>,UNIV\<^esub> m'}"


lemma "m(aux: f) = \<lparr> st=(st m), cap=(cap m), initState=(initState m), \<dots>=(f m)\<rparr>"
  by (simp add: aux_upd_def)

lemma "\<Gamma> (extend (m(aux: f)) more) = \<Gamma> (f m)"
  by (simp add: aux_upd_def)

(* (f m) = \<lparr>\<Gamma> = (f m), \<dots>=more\<rparr> *)
lemma [simp]:
  "\<Gamma> (m(aux: f)) = \<Gamma> (extend m (f m))"
  apply (simp add: aux_upd_def sec_state_rec.defs) 
  sorry

lemma [simp]:
  "st (m(aux: f)) = st m"
  by (simp add: aux_upd_def)

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

end