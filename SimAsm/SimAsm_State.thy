theory SimAsm_State
  imports Main
begin

section \<open>State\<close>

datatype ('g,'r) var = Reg 'r | Glb 'g
record ('v,'a) state_rec = st :: "'a \<Rightarrow> 'v"

type_synonym ('v,'g,'r,'a) state = "('v,('g,'r) var,'a) state_rec_scheme"
type_synonym ('v,'g,'a) gstate = "('v,'g,'a) state_rec_scheme"

type_synonym ('v,'g,'r,'a) pred = "('v,'g,'r,'a) state set"
type_synonym ('v,'g,'a) gpred = "('v,'g,'a) gstate set"

type_synonym ('v,'g,'r,'a) trel = "('v,'g,'r,'a) state rel"
type_synonym ('v,'g,'a) grel = "('v,'g,'a) gstate rel"

type_synonym ('v,'g,'r,'a) trans = "('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r,'a) pred"
type_synonym ('v,'g,'r,'a) rtrans = "('v,'g,'r,'a) trel \<Rightarrow> ('v,'g,'r,'a) trel"

type_synonym ('v,'g,'r,'a) auxfn = "('v,('g,'r) var,'a) state_rec_scheme \<Rightarrow> 'a"

(*
definition glb
  where "glb m \<equiv> \<lambda>v. m (Glb v)"

definition rg
  where "rg m \<equiv> \<lambda>v. m (Reg v)"
*)

section \<open>Write Operations\<close>

definition st_upd :: "('v,'a,'b) state_rec_scheme \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> ('v,'a,'b) state_rec_scheme"
  where "st_upd m a b = m \<lparr> st := ((st m) (a := b)) \<rparr>"

definition aux_upd :: "('v,'r,'a) state_rec_scheme \<Rightarrow> (('v,'r,'a) state_rec_scheme \<Rightarrow> 'a) \<Rightarrow> ('v,'r,'a) state_rec_scheme"
  where "aux_upd m f \<equiv> m\<lparr>state_rec.more := f m\<rparr>"

nonterminal updbinds and updbind

syntax
  "_updbindm" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"            ("(2_ :=\<^sub>s/ _)")
  "_updbinda" :: "'a \<Rightarrow> updbind"                  ("(2aux:/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "f(x:=\<^sub>sy)" \<rightleftharpoons> "CONST st_upd f x y"
  "f(aux: y)" \<rightleftharpoons> "CONST aux_upd f y"

lemma [simp]:
  "st (m(r :=\<^sub>s e)) q = (if r = q then e else st m q)"
  by (auto simp: st_upd_def)

lemma aux_nop [simp]:
  "m(aux:more) = m"
  by (auto simp: aux_upd_def)

lemma st_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a :=\<^sub>s b))(c :=\<^sub>s d) = (m(c :=\<^sub>s d))(a :=\<^sub>s b)"
  unfolding st_upd_def by (auto intro!: equality fun_upd_twist)

definition glb
  where "glb m \<equiv> \<lparr> st = (\<lambda>v. st m (Glb v)), \<dots> = more m \<rparr>"

definition rg
  where "rg m \<equiv> \<lambda>v. st m (Reg v)"

lemma [simp]:
  "glb (m(Reg r :=\<^sub>s e)) = glb m"
  by (auto simp: glb_def st_upd_def)

lemma [simp]:
  "P O {(m, m'). m' = m} = P"
  by auto

lemma [simp]:
  "state_rec.more (m(x :=\<^sub>s e)) = state_rec.more m"
  by (auto simp: st_upd_def)

lemma [simp]:
  "state_rec.more (m(aux: f)) = f m"
  by (auto simp: aux_upd_def)

lemma aux_exec [intro!]:
  assumes "(m\<^sub>1,m\<^sub>2) \<in> P"
  shows "(m\<^sub>1,m\<^sub>2(aux: f)) \<in> P O {(m, m'). m' = m(aux: f)}"
  using assms by blast

text \<open>Domain of register variables\<close>
abbreviation locals
  where "locals \<equiv> Reg ` UNIV"

text \<open>Domain of register variables\<close>
abbreviation globals
  where "globals \<equiv> Glb ` UNIV"

end