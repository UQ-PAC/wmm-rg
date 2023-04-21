theory SimAsm_State
  imports Main 
begin

section \<open>State\<close>


(* variable: either a register or a global, where registers equal local vars *)
datatype 'r Reg = reg 'r | tmp 'r
datatype ('g,'r) var = Reg 'r | Glb 'g

text \<open> A state record is a partial mapping from vars to values, st
         capture set, cap, denotes the set of "new" variables that the frame quantifies over
             (these are the variables updated in the framed code)
         initState gives us a slot for initialising a state (if required); 
            it provides a total function 
            (so that lookup can always return a value when st m evaluates to None)
            initState is not in "sync" with st!
       state_rec describes the current "frame" on which an inst operates over, 
         including mappings to variables that are existentially bound within the current 
         "context" 
       useful to model transient buffers which frame mis-speculated executions
         of a branch which should not take effect on actual (core) mem but should reside
         within its "local" frame; 
       \<close>
record ('v,'a) state_rec = st :: "'a \<Rightarrow> 'v option"
                           cap :: "'a set"
                           initState :: "'a \<Rightarrow> 'v"


print_theorems
(*
(* state record mapping some key (for example a variable name) to values *)
record ('v,'a) state_rec = st :: "'a \<Rightarrow> 'v"
*)


(* because records can be arbitrarily extended, a record automatically gives rise to a
*_scheme type which defines arbitrary possible extensions to that record.
for example, given ('v,'a) state_rec, we have ('v,'a,'c) state_rec_scheme which represents an
extension with 'c. *)

(* this is shown below where "st s" :: 'a \<Rightarrow> 'v and this assigns the value of the st field back to
itself. *)
fun test :: "('v,'a,'c) state_rec_scheme \<Rightarrow> ('v,'a,'c) state_rec_scheme" where
"test s = s\<lparr>st := st s\<rparr>"

(* state: in its most general form maps a global or register to values, possibly extended. *)
type_synonym ('v,'g,'r,'a)state = "('v,('g,'r) var,'a) state_rec_scheme"
type_synonym ('v,'g,'a) gstate = "('v,'g,'a) state_rec_scheme"

(* a predicate is defined as a set of states satisfying that predicate.
analagously for global predicates. *)
type_synonym ('v,'g,'r,'a) pred = "('v,'g,'r,'a) state set"
type_synonym ('v,'g,'a) gpred = "('v,'g,'a) gstate set"

type_synonym ('v,'g,'r,'a) trel = "('v,'g,'r,'a) state rel"
type_synonym ('v,'g,'a) grel = "('v,'g,'a) gstate rel"

type_synonym ('v,'g,'r,'a) trans = "('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r,'a) pred"
type_synonym ('v,'g,'r,'a) rtrans = "('v,'g,'r,'a) trel \<Rightarrow> ('v,'g,'r,'a) trel"

(* the possible extension of the state is used to store this auxiliary information *)
type_synonym ('v,'g,'r,'a) auxfn = "('v,('g,'r) var,'a) state_rec_scheme \<Rightarrow> 'a"

(* obtains the state of global variables that are not \<Gamma> *)
definition glb :: "('v,'g,'r,'a) state \<Rightarrow> ('g \<Rightarrow> 'v option)"
  where "glb m \<equiv> (\<lambda>v. st m (Glb v))"

definition rg :: "('v,'g,'r,'a) state \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "rg m \<equiv> \<lambda>v. st m (Reg v)"

definition aux :: "('v,'g,'r,'a) state \<Rightarrow> 'a"
  where "aux m \<equiv> more m"

(* this contains \<Gamma> variables if they are in aux *)
text \<open>define a state on globals only from a full state record\<close>
definition glbSt :: "('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'a) gstate"
  where "glbSt s \<equiv> 
    \<lparr> st = glb s, 
      cap = {g. Glb g \<in> cap s}, 
      initState = (\<lambda>g. initState s (Glb g)), 
      \<dots> = more s \<rparr>"


text \<open>Domain of register variables\<close>

(* Tmp registers are also local? *)
abbreviation locals
  where "locals \<equiv> Reg ` UNIV"

text \<open>Domain of register variables\<close>
abbreviation globals
  where "globals \<equiv> Glb ` UNIV"

section \<open>Write Operations\<close>

(*
definition st_upd :: "('v,'a,'b) state_rec_scheme \<Rightarrow> 'a \<Rightarrow> 'v  \<Rightarrow> ('v,'a,'b) state_rec_scheme"
  where "st_upd m a b = m \<lparr> st := ((st m) (a := Some b)) \<rparr>"
*)
definition st_upd :: "('v,'g,'r,'a) state \<Rightarrow> ('g,'r) var \<Rightarrow> 'v  \<Rightarrow> ('v,'g,'r,'a) state"
  where "st_upd m a b = m \<lparr> st := ((st m) (a := Some b)) \<rparr>"

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
  "m(x :=\<^sub>s y)" \<rightleftharpoons> "CONST st_upd m x y"
  "m(aux: y)" \<rightleftharpoons> "CONST aux_upd m y"

section \<open>Simp Lemmas\<close>

lemma [simp]:
  "st (m(r :=\<^sub>s e)) q = (if r = q then Some e else st m q)"
  by (auto simp: st_upd_def)

lemma [simp]:
  "st (m(v :=\<^sub>s e)) = (st m)(v := Some e)"
  by (auto simp: st_upd_def)

lemma [simp]:
  "more (m(aux: e)) = e m"
  by (auto simp: aux_upd_def)

lemma [simp]:
  "rg (m(Glb x :=\<^sub>s e)) = rg m"
  by (auto simp: rg_def st_upd_def)

lemma [simp]:
  "rg (m(Reg x :=\<^sub>s e)) = (rg m)(x := Some e)"
  by (auto simp: st_upd_def rg_def)

lemma aux_nop [simp]:
  "m(aux:more) = m"
  by (auto simp: aux_upd_def)

lemma aux_st [simp]:
  "st (m(aux: e)) = st m"
  by (auto simp: aux_upd_def)

lemma st_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a :=\<^sub>s b))(c :=\<^sub>s d) = (m(c :=\<^sub>s d))(a :=\<^sub>s b)"
  unfolding st_upd_def by (auto intro!: equality fun_upd_twist)


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
  "aux (m(Reg x :=\<^sub>s e)) = aux m"
  by (auto simp: aux_def st_upd_def)

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

end