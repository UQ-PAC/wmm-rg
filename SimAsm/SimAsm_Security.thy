theory SimAsm_Security
  imports SimAsm_State
begin

datatype color = blue | green

record point =
   x :: int 
   y :: int

record cpoint = point +
   col :: color
  
definition cpt1 :: cpoint 
  where "cpt1 \<equiv> \<lparr> x=1, y=1, col=green \<rparr>"

lemma "point.more cpt1 = \<lparr>col=green\<rparr>" 
  by (simp add: cpt1_def)

(*----------------------------------------*)

datatype sec = bool

record ('v, 'a) sec_state_rec = "('v, 'a) state_rec" +
  \<Gamma> :: "'a \<Rightarrow> bool"

(* sec_state_rec.defs has make, fields, extend truncate *)

lemma "state_rec.more (make s c i g) = \<lparr>\<Gamma> = g\<rparr>"
  by (simp add: sec_state_rec.defs)

lemma "state_rec.more (truncate (make s c i g)) = \<lparr>\<Gamma> = g\<rparr>"
  by (simp add: sec_state_rec.defs)


lemma "make s c i g = \<lparr>st=s, cap=c, initState=i, \<Gamma>=g\<rparr>"
  by (simp add: sec_state_rec.defs)

lemma "fields g = \<lparr>\<Gamma> = g\<rparr>"
  by (simp add: sec_state_rec.defs)

lemma "truncate (make s c i g) =  \<lparr>st=s, cap=c, initState=i\<rparr>"
  by (simp add: sec_state_rec.defs)

definition s1 :: "('v,'a) sec_state_rec"
  where "s1 \<equiv>
    \<lparr> st = undefined, 
      cap = {}, 
      initState = undefined,
      \<Gamma> = (\<lambda>v. True)\<rparr>"

lemma "state_rec.more s1 = \<lparr>\<Gamma>=(\<lambda>v. True)\<rparr>"
  by (simp add: s1_def)

lemma "state_rec.more s1 = \<lparr>\<Gamma>=\<Gamma> s1, \<dots>= more s1\<rparr>" 
  by (simp add: s1_def)





text \<open>Describe low equivalence between two memories for one \<Gamma>\<close>
definition low_equiv1
  ("_ =\<^bsub>_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>Gamma\<^esub> m\<^sub>2 \<equiv> \<forall>x. Gamma x \<longrightarrow> st m\<^sub>1 x = st m\<^sub>2 x"

definition policy 
  where "policy \<L> \<equiv> {m. \<forall>x. st m \<in> \<L> x \<longrightarrow> \<Gamma> m x}"

definition low_equiv 
  ("_ =\<^bsub>_,_\<^esub> _" [70,0,70] 100)
  where "m\<^sub>1 =\<^bsub>\<L>,P\<^esub> m\<^sub>2 \<equiv> 
             m\<^sub>1 \<in> policy \<L> \<inter> P \<and> m\<^sub>2 \<in> policy \<L> \<inter> P \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>1\<^esub> m\<^sub>2 \<and> m\<^sub>1 =\<^bsub>\<Gamma> m\<^sub>2\<^esub> m\<^sub>2"

definition S
  where "S \<L> \<equiv> {(m,m'). m =\<^bsub>\<L>,UNIV\<^esub> m'}"

lemma [simp]:
  "\<Gamma> (m(aux: f)) = \<Gamma> f m"
  apply (simp add: aux_upd_def)
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