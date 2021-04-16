theory ARMv8_State
  imports Main
begin

section \<open>State Encoding\<close>

record 'v gstate_rec = st :: "'v \<Rightarrow> 'v"
record ('v,'r) tstate_rec = "'v gstate_rec" + rg :: "'r \<Rightarrow> 'v"

type_synonym ('v,'r,'a) tstate = "('v,'r,'a) tstate_rec_scheme"
type_synonym ('v,'a) gstate = "('v,'a) gstate_rec_scheme"

type_synonym ('v,'r,'a) pred = "('v,'r,'a) tstate \<Rightarrow> bool"
type_synonym ('v,'a) gpred = "('v,'a) gstate \<Rightarrow> bool"

type_synonym ('v,'r,'a) trel = "(('v,'r,'a) tstate \<times> ('v,'r,'a) tstate) \<Rightarrow> bool"
type_synonym ('v,'a) grel = "(('v,'a) gstate \<times> ('v,'a) gstate) \<Rightarrow> bool"
type_synonym ('v,'r,'a) trans = "('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred"
type_synonym ('v,'r,'a) rtrans = "('v,'r,'a) trel \<Rightarrow> ('v,'r,'a) trel"

type_synonym ('v,'r,'a) auxfn = "('v,'r,'a) tstate \<Rightarrow> 'a"

section \<open>Write Operations\<close>

definition st_upd :: "('v,'a) gstate \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v,'a) gstate"
  where "st_upd m a b = m \<lparr> st := ((st m) (a := b)) \<rparr>"

definition rg_upd :: "('v,'r,'a) tstate \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> ('v,'r,'a) tstate"
  where "rg_upd m a b = m \<lparr> rg := ((rg m) (a := b)) \<rparr>"

definition aux_upd :: "('v,'r,'a) tstate \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) tstate"
  where "aux_upd m f \<equiv> m\<lparr>tstate_rec.more := f m\<rparr>"

nonterminal updbinds and updbind

syntax
  "_updbindm" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"            ("(2_ :=\<^sub>s/ _)")
  "_updbindr" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"            ("(2_ :=\<^sub>r/ _)")
  "_updbinda" :: "'a \<Rightarrow> updbind"                  ("(2aux:/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "f(x:=\<^sub>ry)" \<rightleftharpoons> "CONST rg_upd f x y"
  "f(x:=\<^sub>sy)" \<rightleftharpoons> "CONST st_upd f x y"
  "f(aux: y)" \<rightleftharpoons> "CONST aux_upd f y"

definition glb :: "('v,'r,'a) tstate \<Rightarrow> ('v,'a) gstate"
  where "glb m \<equiv> \<lparr> st = st m, \<dots> = more m \<rparr>"

definition set_glb :: "('v,'r,'a) tstate \<Rightarrow> ('v,'a) gstate \<Rightarrow> ('v,'r,'a) tstate"
  where "set_glb m g \<equiv> \<lparr> st = st g, rg = rg m, \<dots> = gstate_rec.more g \<rparr>"

lemma [simp]:
  "set_glb m (glb m) = m"
  by (auto simp: set_glb_def glb_def)

section \<open>Simple Predicate Encoding\<close>

named_theorems pred_defs

abbreviation conj  (infixr "\<and>\<^sub>p" 35)
  where "conj l r \<equiv> \<lambda>m. (l m) \<and> (r m)"

abbreviation disj  (infixr "\<or>\<^sub>p" 35)
  where "disj l r \<equiv> \<lambda>m. (l m) \<or> (r m)"

abbreviation imp  (infixr "\<longrightarrow>\<^sub>p" 35)
  where "imp l r \<equiv> \<lambda>m. (l m) \<longrightarrow> (r m)"

abbreviation entail (infix "\<turnstile>\<^sub>p" 25)
  where "entail P Q \<equiv> \<forall>m. P m \<longrightarrow> Q m"

definition assert
  where "assert b \<equiv> \<lambda>m. b"

abbreviation True\<^sub>p
  where "True\<^sub>p \<equiv> \<lambda>m. True"

lemma [simp]:
  "(P \<turnstile>\<^sub>p P) = True"
  by (auto simp add: pred_defs)

lemma [simp]:
  "(P \<and>\<^sub>p P) = P"
  by (auto simp: pred_defs)

section \<open>Base Definitions for Relations\<close>

definition reflexive 
  where "reflexive R \<equiv> \<forall>m . R (m,m)"

definition transitive 
  where "transitive R \<equiv> \<forall>m m' m''. R (m,m') \<longrightarrow> R (m',m'') \<longrightarrow> R (m,m'')"

definition stabilize :: "('v,'a) grel \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred"
  where "stabilize R P \<equiv> \<lambda>m. \<forall>g. R (glb m,g) \<longrightarrow> P (set_glb m g)"

section \<open>Simp\<close>

lemma [simp]:
  "rg (set_glb m g) r\<^sub>a = rg m r\<^sub>a"
  by (auto simp: set_glb_def)

lemma [simp]:
  "set_glb (set_glb m g) g' = set_glb m g'"
  by (auto simp: set_glb_def)

lemma [simp]:
  "set_glb (m\<lparr>tstate_rec.more := a\<rparr>) g = set_glb m g"
  by (auto simp: set_glb_def)

lemma [simp]:
  "st (set_glb m g) = st g"
  by (auto simp: set_glb_def)

lemma [simp]:
  "\<forall>m. \<not> P m \<Longrightarrow> Collect P = {}"
  by (auto)

lemma [simp]:
  "glb (m\<lparr>rg := e\<rparr>) = glb m"
  unfolding glb_def by auto

lemma [simp]:
  "m(r :=\<^sub>r e)\<lparr>tstate_rec.more := a\<rparr> = (m\<lparr>tstate_rec.more := a\<rparr>)(r :=\<^sub>r e)"
  by (auto simp: rg_upd_def)

lemma [simp]:
  "glb (m(r :=\<^sub>r T)) = glb m"
  by (auto simp: glb_def rg_upd_def)

lemma [simp]:
  "m(aux: tstate_rec.more) = m"
  by (auto simp: aux_upd_def)

lemma [simp]:
  "glb (set_glb m g) = g"
  by (auto simp: glb_def set_glb_def)

lemma [simp]:
  "glb (x(x3 :=\<^sub>r e, aux: x4)) = glb (x(aux: \<lambda>m. x4 (m(x3 :=\<^sub>r e))))"
  by (auto simp: rg_upd_def aux_upd_def glb_def)

lemma [intro]:
  "reflexive G \<Longrightarrow> G (m,m)"
  by (auto simp: reflexive_def)

lemma entail_refl [intro]:
  "P \<turnstile>\<^sub>p P"
  by (auto simp: pred_defs)

end