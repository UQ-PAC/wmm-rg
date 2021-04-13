theory ARMv8_State
  imports Main
begin


section \<open>State Encoding\<close>

record 'v gstate = st :: "'v \<Rightarrow> 'v"
record ('v,'r) tstate = "'v gstate" + rg :: "'r \<Rightarrow> 'v"
type_synonym ('v,'r,'a) pred = "('v,'r,'a) tstate_scheme \<Rightarrow> bool"
type_synonym ('v,'a) rpred = "(('v,'a) gstate_scheme \<times> ('v,'a) gstate_scheme) \<Rightarrow> bool"



(*
type_synonym ('v) global = "(('v \<Rightarrow> 'v))"
type_synonym ('v,'r) state = "(('v) global \<times> ('r \<Rightarrow> 'v))"
type_synonym ('v,'r) rpred = "(('v) global \<times> ('v) global) \<Rightarrow> bool"
type_synonym ('v,'r) gpred  = "('v) global \<Rightarrow> bool"
*)


section \<open>Write Operations\<close>

definition st_upd :: "(('v,'a) gstate_scheme) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> (('v,'a) gstate_scheme)"
  where "st_upd f a b = f \<lparr> st := ((st f) (a := b)) \<rparr>"

definition rg_upd :: "(('v,'r,'a) tstate_scheme) \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> (('v,'r,'a) tstate_scheme)"
  where "rg_upd f a b = f \<lparr> rg := ((rg f) (a := b)) \<rparr>"

nonterminal updbinds and updbind

syntax
  "_updbindm" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ :=\<^sub>s/ _)")
  "_updbindr" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ :=\<^sub>r/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "f(x:=\<^sub>ry)" \<rightleftharpoons> "CONST rg_upd f x y"
  "f(x:=\<^sub>sy)" \<rightleftharpoons> "CONST st_upd f x y"

section \<open>Simple Predicate Encoding\<close>

named_theorems pred_defs

definition conj  (infixr "\<and>\<^sub>p" 35)
  where "conj l r \<equiv> \<lambda>m. (l m) \<and> (r m)"

definition disj  (infixr "\<or>\<^sub>p" 35)
  where "disj l r \<equiv> \<lambda>m. (l m) \<or> (r m)"

definition imp  (infixr "\<longrightarrow>\<^sub>p" 35)
  where "imp l r \<equiv> \<lambda>m. (l m) \<longrightarrow> (r m)"

definition entail (infix "\<turnstile>\<^sub>p" 25)
  where "entail P Q \<equiv> \<forall>m. P m \<longrightarrow> Q m"

definition assert
  where "assert b \<equiv> \<lambda>m. b"

declare conj_def [pred_defs]
declare disj_def [pred_defs]
declare imp_def [pred_defs]
declare assert_def [pred_defs]
declare entail_def [pred_defs]

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

end