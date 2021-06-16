theory ARMv8_State
  imports Main
begin

section \<open>State Encoding\<close>

datatype ('v,'r) var = Reg 'r | Glb 'v
record ('v,'a) state_rec = st :: "'a \<Rightarrow> 'v"

type_synonym ('v,'r,'a) state = "('v,('v,'r) var,'a) state_rec_scheme"
type_synonym ('v,'a) gstate = "('v,'v,'a) state_rec_scheme"

type_synonym ('v,'r,'a) pred = "('v,'r,'a) state set"
type_synonym ('v,'a) gpred = "('v,'a) gstate set"

type_synonym ('v,'r,'a) trel = "('v,'r,'a) state rel"
type_synonym ('v,'a) grel = "('v,'a) gstate rel"

type_synonym ('v,'r,'a) trans = "('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred"
type_synonym ('v,'r,'a) rtrans = "('v,'r,'a) trel \<Rightarrow> ('v,'r,'a) trel"

type_synonym ('v,'r,'a) auxfn = "('v,('v,'r) var,'a) state_rec_scheme \<Rightarrow> 'a"

definition glb
  where "glb m \<equiv> \<lparr> st = (\<lambda>v. st m (Glb v)), \<dots> = more m \<rparr>"

definition rg :: "('v,'r,'a) state \<Rightarrow> ('r \<Rightarrow> 'v)"
  where "rg m \<equiv> \<lambda>v. st m (Reg v)"

definition aux
  where "aux m \<equiv> more m"

text \<open>Domain of register variables\<close>
abbreviation locals
  where "locals \<equiv> Reg ` UNIV"

text \<open>Domain of register variables\<close>
abbreviation globals
  where "globals \<equiv> Glb ` UNIV"

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

section \<open>Simp Lemmas\<close>

lemma aux_nop [simp]:
  "m(aux:aux) = m"
  by (auto simp: aux_def aux_upd_def)

lemma aux_st [simp]:
  "st (m(aux: e)) = st m"
  by (auto simp: aux_upd_def)

lemma [simp]:
  "st (m(r :=\<^sub>s e)) q = (if r = q then e else st m q)"
  by (auto simp: st_upd_def)

lemma [simp]:
  "st (m(v :=\<^sub>s e)) = (st m)(v := e)"
  by (auto simp: st_upd_def)

lemma [simp]:
  "more (m(r :=\<^sub>s e)) = more m"
  by (auto simp: st_upd_def)

lemma [simp]:
  "more (m(aux: e)) = e m"
  by (auto simp: aux_upd_def)

lemma [simp]:
  "rg (m(Glb x :=\<^sub>s e)) = rg m"
  by (auto simp: rg_def st_upd_def)

lemma [simp]:
  "rg (m(Reg x :=\<^sub>s e)) = (rg m)(x := e)"
  by (auto simp: st_upd_def rg_def)

lemma [simp]:
  "glb (m(Reg r :=\<^sub>s e)) = glb m"
  by (auto simp: glb_def st_upd_def)

lemma [simp]:
  "glb (m(Reg r :=\<^sub>s e, aux: f)) = glb (m(aux: \<lambda>m. f(m(Reg r :=\<^sub>s e))))"
  by (auto simp: aux_def glb_def)

lemma [simp]:
  "st m (Reg x) = rg m x"
  by (auto simp: rg_def)

lemma [simp]:
  "glb (m(Reg x :=\<^sub>s e)) = glb m"
  by (auto simp: glb_def st_upd_def)

lemma [simp]:
  "aux (m(Reg x :=\<^sub>s e)) = aux m"
  by (auto simp: aux_def st_upd_def)

end