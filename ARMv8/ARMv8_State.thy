theory ARMv8_State
  imports Main "../Push_State"
begin

section \<open>State Encoding\<close>


datatype ('v,'r) var = Reg 'r | Glb 'v | Tmp 'r
record ('v,'a) state_rec = st :: "'a \<Rightarrow> 'v"

(* 
  state_rec to be interpreted as class state in Push_State.thy;
  - the aux component is just reserved for ghost-variables like \<Gamma> etc.
  - the Tmp registers are used when splitting commands into sub-operations,
     e.g. Load is lifted into a sequence of subops via lift\<^sub>c in ARMv8_Rules.thy  

  build a tree structure of state_rec  and instantiate 
  the type-generic tree as (state) state (see below)

*)

(* _scheme add the "more" field to a record to generalise it (Tutorial p.152) *)

type_synonym ('v,'r,'a) state = "('v,('v,'r) var,'a) state_rec_scheme"
type_synonym ('v,'a) gstate = "('v,'v,'a) state_rec_scheme"

type_synonym ('v,'r,'a) pred = "('v,'r,'a) state set"
type_synonym ('v,'a) gpred = "('v,'a) gstate set"

type_synonym ('v,'r,'a) trel = "('v,'r,'a) state rel"  (* transition relation *)
type_synonym ('v,'a) grel = "('v,'a) gstate rel"       (* trans rel reduced to globals/observable *)

type_synonym ('v,'r,'a) trans = "('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred"  (* pred transformer *)
type_synonym ('v,'r,'a) rtrans = "('v,'r,'a) trel \<Rightarrow> ('v,'r,'a) trel" (* rel transformer *)

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

(* (a:=b) to be read as a mapping a \<rightarrow> b, i.e., we upd state record m with m where the mapping 
    to a \<rightarrow> _ is replaced by the new mapping a \<rightarrow> b  *) 
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


text \<open> recTree as data structure in which each leaf is a state record \<close>

datatype  'n tree = Leaf 'n | Branch "'n tree" "'n tree"


text \<open> recTree is instantiated as a Push state such that push creates
        a new sibling branch (to current branch) for which the push
        mapping s becomes defined \<close>

(* the parameter (type) would define that there is no restriction on the 
   generic types 'a 
   the parameter (state) says that 'a has to be a state
    (similar usage found in lattice.thy)
*)

instantiation "tree" :: (state) state
begin
definition  
      push_rec_def: "push m s = Branch m s"

instance proof
  fix m m' s s':: "'a tree"
  show "push m s = push m' s' \<Longrightarrow> (m = m' \<and> s = s')" 
    by (simp add: ARMv8_State.push_rec_def)
qed
end


type_synonym ('v,'r,'a) recTree = "('v,'r,'a) state tree"

end