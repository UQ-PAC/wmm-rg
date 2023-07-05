theory SimAsm_SecState
  imports Var_map
begin


text \<open> Extension to the state record with the auxiliary variable \<Gamma> 
        which holds the security level \<close>

text \<open> 'sec is a generic type for the security lattice, which gets instantiated for
        each example, e.g., Basic_Lattice.thy in Example folder \<close>

record ('var, 'val, 'sec) sec_rec = sec_st :: "'var \<Rightarrow> 'val" 
                                       \<Gamma> :: "'var \<Rightarrow> 'sec"                       


type_synonym ('var,'val,'r,'sec,'a) sec_state = "('var, 'val, 'sec, 'a) sec_rec_scheme"

(* the possible extension of the state is used to store this auxiliary information *)
type_synonym ('v,'g,'r,'sec,'a) auxfnSec = "('v,('g,'r) var,'sec,'a) sec_state_rec_scheme \<Rightarrow> 'a"

(* obtains the state of global variables that are not \<Gamma> *)
definition glbSec :: "('v,'g,'r,'sec,'a) sec_state \<Rightarrow> ('g \<Rightarrow> 'v option)"
  where "glbSec m \<equiv> (\<lambda>v. st m (Glb v))"

definition rgSec :: "('v,'g,'r,'sec,'a) sec_state \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "rgSec m \<equiv> \<lambda>v. st m (Reg v)"

definition auxSec :: "('v,'g,'r,'sec,'a) sec_state \<Rightarrow> 'a"
  where "auxSec m \<equiv> more m"

(* this contains \<Gamma> variables if they are in aux *)
text \<open>define a state on globals only from a full state record\<close>
definition glbSecSt :: "('v,'g,'r,'sec,'a) sec_state \<Rightarrow> ('v,'g,'sec,'a) gsec_state"
  where "glbSecSt s \<equiv> 
    \<lparr> st = glb s, 
      cap = {g. Glb g \<in> cap s}, 
      initState = (\<lambda>g. initState s (Glb g)), 
      \<Gamma> = (\<lambda>g. \<Gamma> s (Glb g)),
      \<dots> = more s \<rparr>"

text \<open> updates on extended state record \<close>

definition sec_st_upd :: "('v,'g,'r,'sec,'a) sec_state \<Rightarrow> 
                                    ('g,'r) var \<Rightarrow> 'v  \<Rightarrow> ('v,'g,'r,'sec,'a) sec_state"
  where "sec_st_upd m a b = m \<lparr> st := ((st m) (a := Some b)) \<rparr>"

definition sec_aux_upd :: "('v,'r,'sec,'a) sec_state_rec_scheme \<Rightarrow> 
               (('v,'r,'sec,'a) sec_state_rec_scheme \<Rightarrow> 'a) \<Rightarrow> ('v,'r,'sec,'a) sec_state_rec_scheme"
  where "sec_aux_upd m f \<equiv> m\<lparr>sec_state_rec.more := f m\<rparr>"

nonterminal updbinds and updbind

syntax
  "_updbindms" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"            ("(2_ :=\<^sub>g/ _)") 
  "_updbindas" :: "'a \<Rightarrow> updbind"                  ("(2aux\<^sub>g:/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "m(x :=\<^sub>g y)" \<rightleftharpoons> "CONST sec_st_upd m x y"  
  "m(aux\<^sub>g: y)" \<rightleftharpoons> "CONST sec_aux_upd m y"

section \<open>Simp Lemmas\<close>

lemma [simp]:
  "st (m(r :=\<^sub>g e)) q = (if r = q then Some e else st m q)"
  by (auto simp: sec_st_upd_def)

lemma [simp]:
  "st (m(v :=\<^sub>g e)) = (st m)(v := Some e)"
  by (auto simp: sec_st_upd_def) 

lemma [simp]:
  "more (m(aux\<^sub>g: e)) = e m"
  by (auto simp: sec_aux_upd_def)

lemma [simp]:
  "rgSec (m(Glb x :=\<^sub>g e)) = rgSec m"
  by (auto simp: rgSec_def sec_st_upd_def)

lemma [simp]:
  "rgSec (m(Reg x :=\<^sub>g e)) = (rgSec m)(x := Some e)"
  by (auto simp: sec_st_upd_def rgSec_def)

lemma auxSec_nop [simp]:
  "m(aux\<^sub>g:more) = m"
  by (auto simp: sec_aux_upd_def)

lemma auxSec_st [simp]:
  "st (m(aux\<^sub>g: e)) = st m"
  by (auto simp: sec_aux_upd_def)

lemma st_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a :=\<^sub>g b))(c :=\<^sub>g d) = (m(c :=\<^sub>g d))(a :=\<^sub>g b)"
  unfolding sec_st_upd_def by (auto intro!: equality fun_upd_twist)


lemma [simp]:
  "glbSec (m(Reg r :=\<^sub>g e)) = glbSec m"
  by (auto simp: glbSec_def sec_st_upd_def)

lemma [simp]:
  "glbSec (m(Reg r :=\<^sub>g e, aux\<^sub>g: f)) = glbSec (m(aux\<^sub>g: \<lambda>m. f(m(Reg r :=\<^sub>g e))))"
  by (auto simp: auxSec_def glbSec_def)

lemma [simp]:
  "st m (Reg x) = rgSec m x"
  by (auto simp: rgSec_def)

lemma [simp]:
  "auxSec (m(Reg x :=\<^sub>g e)) = auxSec m"
  by (auto simp: auxSec_def sec_st_upd_def)

lemma [simp]:
  "sec_state_rec.more (m(x :=\<^sub>g e)) = sec_state_rec.more m"
  by (auto simp: sec_st_upd_def)

lemma [simp]:
  "sec_state_rec.more (m(aux\<^sub>g: f)) = f m"
  by (auto simp: sec_aux_upd_def)

lemma auxSec_exec [intro!]:
  assumes "(m\<^sub>1,m\<^sub>2) \<in> P"
  shows "(m\<^sub>1,m\<^sub>2(aux\<^sub>g: f)) \<in> P O {(m, m'). m' = m(aux\<^sub>g: f)}"
  using assms by blast

end