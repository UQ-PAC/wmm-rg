theory ARMv8_State
  imports Main "../Push_State"
begin

section \<open>State Encoding\<close>

datatype 'r Reg = reg 'r | tmp 'r
datatype ('v,'r) var = Reg 'r | Glb 'v 

text \<open> A state record is a partial mapping from vars to values, st
         capture set, cap, denotes the set of "new" variables that the frame quantifies over
         (these are the variables updated in the framed code)
       state_rec describes the current "frame" on which an inst operates over, 
         including mappings to variables that are existentially bound within the current 
         "context" 
       useful to model transient buffers which frame mis-speculated executions
         of a branch which should not take effect on actual (core) mem but should reside
         within its "local" frame; 
       \<close>


record ('v,'a) state_rec = st :: "'a \<Rightarrow> 'v option"
                           cap :: "'a set"

(* 
  state_rec to be interpreted as class state in Push_State.thy;
  - the aux component is just reserved for ghost-variables like \<Gamma> etc.
  - the Tmp registers are used when splitting commands into sub-operations,
     e.g. Load is lifted into a sequence of subops via lift\<^sub>c in ARMv8_Rules.thy  

  build a tree structure of state_rec, called stateTree,  and instantiate 
  the type-generic tree as (state) state (see below)

*)

(* _scheme add the "more" field to a record to generalise it (Tutorial p.152) *)

type_synonym ('v,'r,'a) state = "('v,('v,'r) var,'a) state_rec_scheme"
type_synonym ('v,'r,'a) rstate = "('v,'r,'a) state_rec_scheme"
type_synonym ('v,'a) gstate = "('v,'v,'a) state_rec_scheme"

type_synonym ('v,'r,'a) pred = "('v,'r,'a) state set"
type_synonym ('v,'a) gpred = "('v,'a) gstate set"

type_synonym ('v,'r,'a) trel = "('v,'r,'a) state rel"  (* transition relation *)
type_synonym ('v,'a) grel = "('v,'a) gstate rel"       (* trans rel reduced to globals/observable *)

type_synonym ('v,'r,'a) trans = "('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred"  (* pred transformer *)
type_synonym ('v,'r,'a) rtrans = "('v,'r,'a) trel \<Rightarrow> ('v,'r,'a) trel" (* rel transformer *)

type_synonym ('v,'r,'a) auxfn = "('v,('v,'r) var,'a) state_rec_scheme \<Rightarrow> 'a"

definition glb :: "('v,'r,'a) state \<Rightarrow> ('v \<Rightarrow> 'v option)"
  where "glb m \<equiv> \<lambda>v. st m (Glb v)"
(*  where "glb m \<equiv> \<lparr> st = (\<lambda>v. st m (Glb v)), \<dots> = more m \<rparr>" *)


definition rg :: "('v,'r,'a) state \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "rg m \<equiv> \<lambda>v. st m (Reg v)"

definition aux
  where "aux m \<equiv> more m"

text \<open>Domain of register variables\<close>

(* Tmp registers are also local? *)
abbreviation locals
  where "locals \<equiv> Reg ` UNIV"

text \<open>Domain of register variables\<close>
abbreviation globals
  where "globals \<equiv> Glb ` UNIV"

section \<open>Write Operations\<close>

(* (a:=b) to be read as a mapping a \<rightarrow> b, i.e., we upd state record m with m where the mapping 
    to a \<rightarrow> _ is replaced by the new mapping a \<rightarrow> b  *) 
definition 
   st_upd :: "('v,'a,'b) state_rec_scheme \<Rightarrow> 'a \<Rightarrow> 'v option \<Rightarrow> ('v,'a,'b) state_rec_scheme"
    where "st_upd m a b = m \<lparr> st := ((st m) (a := b)) \<rparr>"

definition 
   aux_upd :: "('v,'r,'a) state_rec_scheme \<Rightarrow> (('v,'r,'a) state_rec_scheme \<Rightarrow> 'a) \<Rightarrow> 
                                                           ('v,'r,'a) state_rec_scheme"
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


text \<open> stateTree as data structure in which each leaf is a state record;
       the Base (initial leaf) has a mapping for all variables s \<mapsto> Some v
          and it maintains all globally observable updates;
       the top-most/right-most state record serves as a "frame" or "scope" 
          to the current computation and gets discarded once the frame is exited;

       stateTree is instantiated as a Push state;
       the push operation creates a new sibling frame (to current frame) 
         in which all mappings from m are set to None (all vars are undefined); 
       when reading a variable within a frame and it is not yet defined in the current
         "topmost" frame then a lookup routine goes through the recTree in reverse 
         order of its build until it finds the innermost value available;
       the record entry cap is the set of variables "captured/pushed/quantified"
         in the current frame;
       Globally visible updates (but only those) have to be stored in the Base, 
         e.g. Cache; global stores in general are not observable since they
         are not written to memory when speculating;
       \<close>

datatype  'n tree = Base 'n | Branch "'n tree" "'n tree"

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

type_synonym ('v,'r,'a) stateTree = "(('v,('v,'r) var,'a) state_rec_scheme) tree"



subsection \<open>Tree base, top and lookup and tree update\<close>

fun base :: "('v,'r,'a) stateTree \<Rightarrow> ('v,'r,'a) state" where
  "base (Base s) = s" |
  "base (Branch m m') = (base m)"

fun top :: "('v,'r,'a) stateTree \<Rightarrow> ('v,'r,'a) state" where
  "top (Base s) = s" |
  "top (Branch m m') = (case m' of (Base s) \<Rightarrow> s | _ \<Rightarrow> (top m'))"

text \<open> lookup of var in a stateTree finds the closest frame in which var is defined 
         and returns its value in that frame \<close>


fun lookup :: "('v,'r,'a) stateTree \<Rightarrow> ('v, 'r) ARMv8_State.var \<Rightarrow> 'v option" where
  "lookup (Base s) var =  st s var" |
  "lookup (Branch m m') var =
                      (case (lookup m' var) of Some v \<Rightarrow> Some v |_ \<Rightarrow> lookup m var)"

definition top_upd :: "('v,'r,'a) stateTree \<Rightarrow> ('v,'r) var \<Rightarrow> 'v option \<Rightarrow> ('v,'r,'a) stateTree" where
  "top_upd t r val = Base (st_upd (top t) r val)"

fun tree_upd :: "('v,'r,'a) stateTree \<Rightarrow> ('v,'r,'a) stateTree \<Rightarrow> ('v,'r,'a) stateTree" where
  "tree_upd (Base s) newTop = newTop" |
  "tree_upd (Branch m m') newTop = (Branch m (tree_upd m' newTop))"


subsection \<open> tree lemmas \<close>

lemma [simp]: 
  "tree_upd t (Base (top t)) = t" 
proof (induction t)
  case (Base x)
  then show ?case by auto
next
  case (Branch t1 t2)
  then show ?case apply auto
    by (metis top.elims tree.simps(5) tree.simps(6))
qed


lemma stUpd_single :
   "x \<noteq> r  \<Longrightarrow> st (st_upd m r v) x = st m x" by auto

lemma topUpd_single:
 "x \<noteq> r  \<Longrightarrow> lookup (top_upd (Base s) r (the val)) x = lookup (Base s) x"
  using top_upd_def stUpd_single by (metis(full_types) lookup.simps(1) top.simps(1))
   
lemma treeUpd_change: 
  "x \<noteq> r  \<Longrightarrow> lookup (tree_upd t (top_upd t r (the val))) x = lookup t x"
proof (induct t)
  case (Base s)
  then show ?case using topUpd_single lookup.simps(1) by fastforce
next
  case (Branch t1 t2)
  then show ?case using topUpd_single lookup.simps(2) top.elims top_upd_def tree.distinct(1) 
             tree.inject(2) tree.simps(5) tree.simps(6) tree_upd.simps(2)
    by (smt (verit, ccfv_threshold) )
qed

lemma top_treeUpd:
    "top (tree_upd t (Base newTop)) = newTop" 
proof (induction t)
  case (Base x)
  then show ?case by simp
next
  case (Branch t1 t2)
  then show ?case 
  proof (induction t2)
    case (Base x)
    then show ?case by simp
  next
    case (Branch t21 t22)
    then show ?case by auto
  qed
qed

lemma lookup_upd:
  "val \<noteq> None \<Longrightarrow> lookup (tree_upd t (top_upd t r val)) r = val"
proof (induction t)
  case (Base x)
  then show ?case using lookup.simps(1) tree_upd.simps(1) top_treeUpd topUpd_single
    by (simp add: top_upd_def)
next
  case (Branch t1 t2)
  then show ?case 
  proof (induction t2)
    case (Base x)
    then show ?case using tree_upd.simps lookup.simps(2) top.simps tree.simps(5)
      by (metis (no_types, lifting) option.case_eq_if option.collapse top_upd_def)
  next
    case (Branch t21 t22)
    then show ?case using tree_upd.simps(2) lookup.simps(2) top.simps tree.simps(2,6)
      by (metis (mono_tags, lifting) option.case_eq_if option.collapse top_upd_def)
  qed
qed



(* new tree def *)
definition rgTree :: "('v,'r,'a) stateTree \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "rgTree t \<equiv> \<lambda>v. st (top t) (Reg v)"


end