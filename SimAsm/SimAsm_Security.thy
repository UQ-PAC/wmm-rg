theory SimAsm_Security
  imports SimAsm
begin

text \<open> Extension to the state record with the auxiliary variable \<Gamma> 
        which holds the security level \<close>

(*
datatype sec = bool
*)

text \<open> 'sec is a generic type for the security lattice, which gets instantiated for
        each example, e.g., Basic_Lattice.thy in Example folder \<close>

record ('v, 'a, 'sec) sec_state_rec = "('v, 'a) state_rec" +
  \<Gamma> :: "'a \<Rightarrow> 'sec"                       


type_synonym ('v,'g,'r,'a, 'sec) sec_state = "('v,('g,'r) var,'a, 'sec) sec_state_rec_scheme"


text \<open> updates on extended state record \<close>

definition sec_st_upd :: "('v,'g,'r,'a,'sec) sec_state \<Rightarrow> ('g,'r) var \<Rightarrow> 'v  \<Rightarrow> ('v,'g,'r,'a,'sec) sec_state"
  where "sec_st_upd m a b = m \<lparr> st := ((st m) (a := Some b)) \<rparr>"

definition sec_aux_upd :: "('v,'r,'a,'sec) sec_state_rec_scheme \<Rightarrow> 
                 (('v,'r,'a,'sec) sec_state_rec_scheme \<Rightarrow> 'a) \<Rightarrow> ('v,'r,'a,'sec) sec_state_rec_scheme"
  where "sec_aux_upd m f \<equiv> m\<lparr>sec_state_rec.more := f m\<rparr>"

nonterminal updbinds and updbind

syntax
  "_updbindms" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"            ("(2_ :=\<^sub>s\<^sub>e\<^sub>c/ _)")
  "_updbindas" :: "'a \<Rightarrow> updbind"                  ("(2aux\<^sub>s:/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "m(x :=\<^sub>s\<^sub>e\<^sub>c y)" \<rightleftharpoons> "CONST sec_st_upd m x y"
  "m(aux\<^sub>s: y)" \<rightleftharpoons> "CONST sec_aux_upd m y"


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

lemma "aux_upd m f = \<lparr> st=(st m), cap=(cap m), initState=(initState m), \<dots>=(f m)\<rparr>"
  by (simp add: aux_upd_def)

lemma "m(aux: f) = \<lparr> st=(st m), cap=(cap m), initState=(initState m), \<dots>=(f m)\<rparr>"
  by (simp add: aux_upd_def)

lemma [simp]:
  "\<Gamma> (m(aux\<^sub>s: f)) = \<Gamma> m"
  by (simp add: sec_aux_upd_def sec_state_rec.defs) 


lemma [simp]:
  "st (m(aux\<^sub>s: f)) = st m"
  by (simp add: sec_aux_upd_def)

lemma [simp]:
  "m(aux\<^sub>s: f) \<in> policy \<L> = (m \<in> policy \<L>)" 
  unfolding policy_def by simp

lemma [simp]:
  "(m\<^sub>1(aux\<^sub>s: f) =\<^bsub>\<L>,UNIV\<^esub> m\<^sub>2(aux\<^sub>s: f)) = (m\<^sub>1 =\<^bsub>\<L>,UNIV\<^esub> m\<^sub>2)"
  unfolding low_equiv_def low_equiv1_def by simp
  
lemma sec_pres_aux:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> S \<L>"
  shows "(m\<^sub>1(aux\<^sub>s: f), m\<^sub>2(aux\<^sub>s: f)) \<in> S \<L>"
  using assms unfolding S_def by simp 

end