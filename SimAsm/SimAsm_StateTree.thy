theory SimAsm_StateTree
  imports SimAsm_State "../Push_State"
begin

section \<open>State Trees\<close>

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
      push_rec_def: "push m s = Branch m s"   (* pushes s on top of current tree t *) 

instance proof
  fix m m' s s':: "'a tree"
  show "push m s = push m' s' \<Longrightarrow> (m = m' \<and> s = s')" 
    by (simp add: push_rec_def)
qed
end

type_synonym ('v,'g,'r,'a) stateTree = "(('v,('g,'r) var,'a) state_rec_scheme) tree"

type_synonym ('v,'g,'r,'a) predTree = "('v,'g,'r,'a) stateTree set"

type_synonym ('v,'r,'a) gstateTree = "(('v,'v,'a) state_rec_scheme) tree"
type_synonym ('v,'a) gpredTree = "('v,'v,'a) gstateTree set"



subsection \<open>Tree base, top and lookup and tree update\<close>

fun base :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state" where
  "base (Base s) = s" |
  "base (Branch m m') = (base m)"

fun top :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state" where
  "top (Base s) = s" |
  "top (Branch m m') = (case m' of (Base s) \<Rightarrow> s | _ \<Rightarrow> (top m'))"

text \<open> lookup of var in a stateTree finds the closest (topmost) frame in which var is defined 
         and returns its value in that frame \<close>
fun lookup :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v option" where
  "lookup (Base s) var =  st s var" |
  "lookup (Branch m m') var =
                      (case (lookup m' var) of Some v \<Rightarrow> Some v |_ \<Rightarrow> lookup m var)"

definition top_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v option \<Rightarrow> ('v,'g,'r,'a) stateTree" where
  "top_upd t r val = Base (st_upd (top t) r val)"

definition top_aux_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> (('v,'g,'r,'a) state \<Rightarrow> 'a) \<Rightarrow> ('v,'g,'r,'a) stateTree" where
  "top_aux_upd t f = Base (aux_upd (top t) f)"

fun tree_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) stateTree" where
  "tree_upd (Base s) newTop = newTop" |
  "tree_upd (Branch m m') newTop = (Branch m (tree_upd m' newTop))"



(*
(* new tree def: local state on top of tree *)
definition rgTree :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "rgTree t \<equiv> \<lambda>v. st (top t) (Reg v)"

*)

(* obtains the global state of current tree *)
definition glb\<^sub>t :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g \<Rightarrow> 'v option)"
  where "glb\<^sub>t t \<equiv> \<lambda>v. (lookup t) (Glb v)"

(* local state of current tree *)
definition rg\<^sub>t :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "rg\<^sub>t t \<equiv> \<lambda>v. (lookup t) (Reg v)"


(* auxiliary component of tree is the aux of its top state *)
definition aux\<^sub>t 
  where "aux\<^sub>t t \<equiv> more (top t)"



subsection \<open> tree lemmas \<close>

lemma treeUpd_top [simp]: 
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

lemma top_treeUpd [simp]:
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



end