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

instantiation "tree" :: (state) state         (* state is a type class 
        and tree has to define a push operation whose arg is also a (state) *)
begin
definition  
      push_rec_def: "push m s = Branch m s"   (* pushes s on top of current tree t *) 

instance proof             (* has to verify that the axiom of the class state holds *)
  fix m m' s s':: "'a tree"    
  show "push m s = push m' s' \<Longrightarrow> (m = m' \<and> s = s')" 
    by (simp add: push_rec_def)
qed
end

type_synonym ('v,'g,'r,'a) stateTree = "(('v,('g,'r) var,'a) state_rec_scheme) tree"
type_synonym ('v,'r,'a) gstateTree = "(('v,'v,'a) state_rec_scheme) tree"

type_synonym ('v,'g,'r,'a) predTree = "('v,'g,'r,'a) stateTree set"
type_synonym ('v,'a) gpredTree = "('v,'v,'a) gstateTree set"

type_synonym ('v,'g,'r,'a) trelTree = "('v,'g,'r,'a) stateTree rel"
type_synonym ('v,'g,'a) grelTree = "('v,'g,'a) gstateTree rel"

type_synonym ('v,'g,'r,'a) transTree = "('v,'g,'r,'a) predTree \<Rightarrow> ('v,'g,'r,'a) predTree"
type_synonym ('v,'g,'r,'a) rtransTree = "('v,'g,'r,'a) trelTree \<Rightarrow> ('v,'g,'r,'a) trelTree"



subsection \<open>Tree access: base, top and lookup\<close>

(*
fun base :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state" where
  "base (Base s) = s" |
  "base (Branch m m') = (base m)"
*)
fun base :: "('v,'a,'b) state_rec_scheme tree \<Rightarrow> ('v,'a,'b) state_rec_scheme" where
  "base (Base s) = s" |
  "base (Branch m m') = (base m)"


(*
fun top :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state" where
  "top (Base s) = s" |
  "top (Branch m m') = (case m' of (Base s) \<Rightarrow> s | _ \<Rightarrow> (top m'))"
*)
fun top :: "('v,'a,'b) state_rec_scheme tree \<Rightarrow> ('v,'a,'b) state_rec_scheme" where
  "top (Base s) = s" |
  "top (Branch m m') = (case m' of (Base s) \<Rightarrow> s | _ \<Rightarrow> (top m'))"


text \<open> lookup of var in a stateTree finds the closest (topmost) frame in which var is defined 
         and returns its value in that frame;
        when the variable is undefined (i.e., equals None) in the base of the tree, 
         then lookup uses the initialisation of that that state, initState m
       
       lookupSome turns the option value into a value          \<close>

(*  (lookup t) and (lookupSome t)  match (st m) -- give a mapping var \<rightarrow> val option 
                                                               or var \<rightarrow> val *)
(* fun lookup :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v option" where*)
fun lookup :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 'a \<Rightarrow> 'v option" where
  "lookup (Base s) var =  (st s var)" |
  "lookup (Branch m m') var =
                      (case (lookup m' var) of Some v \<Rightarrow> Some v |_ \<Rightarrow> lookup m var)"

fun lookupSome :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v" where
  "lookupSome t var = (case (lookup t var) of Some v \<Rightarrow> v | 
                                                   _ \<Rightarrow> (initState (base t) var))"

(* obtains the global state of current tree *)
definition glb\<^sub>t :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g \<Rightarrow> 'v option)"
  where "glb\<^sub>t t \<equiv> \<lambda>v. (lookup t) (Glb v)"

(* local state of current tree *)
definition rg\<^sub>t :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "rg\<^sub>t t \<equiv> \<lambda>v. (lookup t) (Reg v)"

(* auxiliary component of tree is the aux of its top state *)
definition aux\<^sub>t 
  where "aux\<^sub>t t \<equiv> more (top t)"


subsection \<open>Write Operations on trees: update top and tree\<close>

(* top_upd :: tree \<Rightarrow> var \<Rightarrow> val \<Rightarrow> state *)
(*definition top_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v \<Rightarrow> ('v,'g,'r,'a) stateTree" where *)
definition top_upd :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 
                                               'a \<Rightarrow> 'v \<Rightarrow> ('v,'a,'c) state_rec_scheme" where
  "top_upd t r val = (st_upd (top t) r val)"

(*definition top_aux_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> (('v,'g,'r,'a) state \<Rightarrow> 'a) \<Rightarrow> ('v,'g,'r,'a) stateTree" where*)
definition top_aux_upd :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 
                     (('v,'a,'c) state_rec_scheme \<Rightarrow> 'c) \<Rightarrow> ('v,'a,'c) state_rec_scheme tree" where
  "top_aux_upd t f = Base (aux_upd (top t) f)"

(* tree_upd :: tree \<Rightarrow> state \<Rightarrow> tree *)
(*fun tree_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r,'a) stateTree" where*)
fun tree_upd :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 
                             ('v,'a,'c) state_rec_scheme \<Rightarrow> ('v,'a,'c) state_rec_scheme tree" where
  "tree_upd (Base s) newTop = (Base newTop)" |
  "tree_upd (Branch m m') newTop = (Branch m (tree_upd m' newTop))"


(* tr_upd :: tree \<Rightarrow> var \<Rightarrow> val \<Rightarrow> tree *)
definition tr_upd :: "('v,'a,'b) state_rec_scheme tree \<Rightarrow> 'a \<Rightarrow> 'v  \<Rightarrow> ('v,'a,'b) state_rec_scheme tree" 
(*  where "tr_upd t a b = tree_upd t ((top t) \<lparr> st := ((st (top t)) (a := Some b)) \<rparr>)" *)
  where "tr_upd t a b = tree_upd t ((top t) \<lparr> st := ((st (top t)) (a := Some b)) \<rparr>)"

definition tr_aux_upd :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 
                            (('v,'a,'c) state_rec_scheme \<Rightarrow> 'c)  \<Rightarrow> ('v,'a,'c) state_rec_scheme tree" 
  where "tr_aux_upd t f = tree_upd t ((top t) \<lparr>state_rec.more := f (top t)\<rparr>)"


syntax
  "_updbindm" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"            ("(2_ :=\<^sub>t/ _)")
  "_updbinda" :: "'a \<Rightarrow> updbind"                  ("(2aux\<^sub>t:/ _)")

translations
  "t(x :=\<^sub>t y)" \<rightleftharpoons> "CONST tr_upd t x y"
  "t(aux\<^sub>t: f)" \<rightleftharpoons> "CONST tr_aux_upd t f"



subsection \<open> tree lemmas \<close>

lemma treeUpd_top [simp]: 
  "tree_upd t (top t) = t" 
proof (induction t)
  case (Base x)
  then show ?case by auto
next
  case (Branch t1 t2)
  then show ?case apply auto
    by (metis top.elims tree.simps(5) tree.simps(6))
qed


lemma stUpd_single :
   "x \<noteq> r  \<Longrightarrow> st (st_upd m r v) x = st m x \<and> 
               initState (st_upd m r v) x = initState m x" 
  by (simp add: st_upd_def)

lemma topUpd_single:
 "x \<noteq> r  \<Longrightarrow> lookup (Base (top_upd (Base s) r (the val))) x = lookup (Base s) x"
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
    "top (tree_upd t newTop) = newTop" 
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
  "lookup (tree_upd t (top_upd t r val)) r = Some val" 
proof (induction t)
  case (Base x)
  then show ?case 
    using lookup.simps(1) tree_upd.simps(1) top_upd_def top_treeUpd topUpd_single
    by (simp add: top_upd_def)
next
  case (Branch t1 t2)
  then show ?case 
  proof (induction t2)
    case (Base x)
    then show ?case using tree_upd.simps lookup.simps(2) top.simps tree.simps(5)
      by (simp add: top_upd_def)
  next
    case (Branch t21 t22)
    then show ?case using tree_upd.simps(2) lookup.simps(2) top.simps tree.simps(2,6) 
      by (simp add: top_upd_def)
  qed 
qed

lemma lookupSome_upd:
  "lookupSome (tree_upd t (top_upd t r val)) r = val"
  using lookup_upd lookupSome.elims by (metis option.simps(5))

section \<open>Simp Lemmas\<close>

lemma [simp]:
  assumes "r = q"
  shows "lookup (tree_upd t (top t\<lparr>st := st (top t)(q \<mapsto> e)\<rparr>)) q = Some e"
  by (metis lookup_upd st_upd_def top_upd_def)

lemma [simp]:
  assumes "r \<noteq> q"
  shows "lookup (tree_upd t (top t\<lparr>st := st (top t)(r \<mapsto> e)\<rparr>)) q = lookup t q"
  by (metis assms option.sel st_upd_def top_upd_def treeUpd_change)

lemma [simp]:
  "lookup (t(r :=\<^sub>t e)) q = (if r = q then Some e else lookup t q)"
  by (auto simp: tr_upd_def st_upd_def) 


lemma [simp]:
  "lookup (t(v :=\<^sub>t e)) = (lookup t)(v := Some e)"
  by (auto simp: st_upd_def)

lemma [simp]:
  "more (top (t(aux\<^sub>t: e))) = e (top t)"
  using tr_aux_upd_def
  by (metis cases_scheme select_convs(4) top_treeUpd update_convs(4))

lemma [simp]:
  "rg\<^sub>t (t(Glb x :=\<^sub>t e)) = rg\<^sub>t t"
  by (auto simp: rg\<^sub>t_def tr_upd_def)

lemma [simp]:
  "rg\<^sub>t (t(Reg x :=\<^sub>t e)) = (rg\<^sub>t t)(x := Some e)"
  by (auto simp: tr_upd_def rg\<^sub>t_def)

lemma tr_aux_nop [simp]:
  "t(aux\<^sub>t:more) = t"
  by (auto simp: tr_aux_upd_def)

lemma tr_aux_st [simp]:
  "lookup (t(aux\<^sub>t: e)) = lookup t"
  apply (auto simp: tr_aux_upd_def)
  sorry

(* todo: define equality on trees to mimic state_rec_scheme equality *)
lemma tree_upd_twist: "a \<noteq> c \<Longrightarrow> (t(a :=\<^sub>t b))(c :=\<^sub>t d) = (t(c :=\<^sub>t d))(a :=\<^sub>t b)"
  unfolding tr_upd_def apply (auto intro!: equality fun_upd_twist)
  sorry

lemma [simp]:
  "glb\<^sub>t (t(Reg r :=\<^sub>t e)) = glb\<^sub>t t"
  by (auto simp: glb\<^sub>t_def tr_upd_def)

(* type checking: LHS is considered typed correct, which is strange?
lemma
  "glb\<^sub>t (t(aux\<^sub>t: f(t(Reg r:=\<^sub>t e)))) = glb\<^sub>t t"
*)

(*
lemma [simp]:
  "glb\<^sub>t (t(Reg r :=\<^sub>t e, aux\<^sub>t: f)) = glb\<^sub>t (t(aux\<^sub>t: \<lambda>m. f(m(Reg r :=\<^sub>s e))))"
  by (auto simp: tr_aux_def glb\<^sub>t_def)
*)


end


(*------ not required if we have an initState slot in the state record:
          the problem without an totalmap initState, the condition (initialised t)
          is carried through all lemmas and even sits in the definition of beh\<^sub>i  



fun total_map :: "('a \<Rightarrow> 'v option) \<Rightarrow> bool"
  where
  "total_map f = (\<forall> v. \<exists> val. (f v) = Some val)"

fun initialised :: "('v,'g,'r,'a) stateTree \<Rightarrow> bool"
  where
  "initialised t = total_map (st (base t))"

(*
lemma lookup_upd:
  "val \<noteq> None \<Longrightarrow> lookup (tree_upd t (top_upd t r val)) r = Some val"
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
      by (simp add: top_upd_def)
  next
    case (Branch t21 t22)
    then show ?case using tree_upd.simps(2) lookup.simps(2) top.simps tree.simps(2,6) 
      by (simp add: top_upd_def)
  qed 
qed
*)




(* we will have to add an invariant/wellformedness condition on programs which states 
   that the variables are initialised and hence the base state is a total mapping  *)

text \<open> lookupSome filters out the lookup calls that result in None \<close>

(*
lemma lookupNotNone:
  assumes "lookup t v \<noteq> None"
  shows "lookupSome t v \<noteq> None"  
  shows counterexample lookup t v = Some None *)



lemma initialised_Some:
  assumes "initialised t"
  shows "st (base t) v \<noteq> None" using assms by force

lemma initialised_lookup:
  assumes "initialised t"
  shows "lookup t v \<noteq> None" using assms 
proof (induct t)
  case (Base x)
  then show ?case using initialised_Some by simp
next
  case (Branch t1 t2)
  then show ?case using lookup.simps(2) by (simp add: option.case_eq_if)
qed

lemma lookupSome_upd:
  assumes "initialised t" 
  shows  "lookupSome (tree_upd t (top_upd t r val)) r = val"
  using lookup_upd lookupSome.elims option.sel assms by metis
*)


(*
(* This was an attempt to encode a subtype of tree for which we know that the
Base is a total map; this falls over with the new Branch constructor which wants
to construct a new element from two of the same type but in an initialised tree
on the LHS of the tree is an initialised tree, the RHS should be allowed any tree *) 

text \<open>InitTree is a tree in which the Base/root is fully initialised, 
         i.e., st on base node it total \<close>

fun total_map :: "('a \<Rightarrow> 'v option) \<Rightarrow> bool"
  where
  "total_map f = (\<forall> v. (f v) \<noteq> None)"

fun initialised :: "('v,'g,'r,'a) stateTree \<Rightarrow> bool"
  where
  "initialised t = total_map (st (base t))"

typedef ('v,'g,'r,'a) initTree = "{t ::('v,'g,'r,'a) stateTree  . initialised t}" 
proof -
  let ?s = "\<lambda>x. Some undefined"
  let ?m = "\<lparr> st = ?s , cap = {}, \<dots> = (p :: 'a) \<rparr>"
  let ?t  = "(Base ?m)"
  have "initialised (?t:: ('v,'g,'r,'a) stateTree)" by simp
  then have "?t \<in> {t. initialised t}" by simp
  then show ?thesis by blast
qed

(* constructors for initialised trees *)
definition iBase:: "(('v,('g,'r) var,'a) state_rec_scheme) \<Rightarrow> ('v,'g,'r,'a) initTree"
  where "iBase s = Abs_initTree (Base s)"

definition iBranch:: "('v,'g,'r,'a) initTree \<Rightarrow> ('v,'g,'r,'a) initTree \<Rightarrow> ('v,'g,'r,'a) initTree"
  where "iBranch t1 t2 = Abs_initTree (Branch (Rep_initTree t1) (Rep_initTree t2))"

subsection \<open>Tree base, top and lookup and tree update\<close>

definition ibase :: "('v,'g,'r,'a) initTree \<Rightarrow> ('v,'g,'r,'a) state" where
  "ibase t = base (Rep_initTree t)"

definition itop :: "('v,'g,'r,'a) initTree \<Rightarrow> ('v,'g,'r,'a) state" where
  "itop t = top (Rep_initTree t)"

text \<open> lookup of var in a stateTree finds the closest (topmost) frame in which var is defined 
         and returns its value in that frame \<close>
definition ilookup :: "('v,'g,'r,'a) initTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v option" where
  "ilookup t var =  lookup (Rep_initTree t) var"

definition itop_upd :: "('v,'g,'r,'a) initTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v option \<Rightarrow> ('v,'g,'r,'a) initTree" where
    "itop_upd t r val = Abs_initTree (top_upd (Rep_initTree t) r val)"

definition itop_aux_upd :: "('v,'g,'r,'a) initTree \<Rightarrow> (('v,'g,'r,'a) state \<Rightarrow> 'a) \<Rightarrow> ('v,'g,'r,'a) initTree" 
  where "itop_aux_upd t f = Abs_initTree (top_aux_upd (Rep_initTree t) f)"

fun itree_upd :: "('v,'g,'r,'a) initTree \<Rightarrow> ('v,'g,'r,'a) initTree \<Rightarrow> ('v,'g,'r,'a) initTree"
  where "itree_upd t\<^sub>1 t\<^sub>2 = Abs_initTree (tree_upd (Rep_initTree t\<^sub>1) (Rep_initTree t\<^sub>2))"


(* obtains the global state of current initialised tree *)
definition iglb\<^sub>t :: "('v,'g,'r,'a) initTree \<Rightarrow> ('g \<Rightarrow> 'v option)"
  where "iglb\<^sub>t t \<equiv> \<lambda>v. (ilookup t) (Glb v)"

(* local state of current initialised tree *)
definition irg\<^sub>t :: "('v,'g,'r,'a) initTree \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "irg\<^sub>t t \<equiv> \<lambda>v. (ilookup t) (Reg v)"

(* auxiliary component of an initialised tree is the aux of its top state *)
definition iaux\<^sub>t
  where "iaux\<^sub>t t \<equiv> more (top t)"

thm tree.induct 


(* this lemma can be used as an induction rule 
         i.e., instead of proof (induct t) \<longrightarrow> proof (induct rule: induct_iTree) ? *)
lemma induct_iTree:
  assumes "\<forall>s.  P (iBase s)"
  assumes "\<forall>t t1 t2. P (iBranch t1 t2)" 
  shows "P t"
  using assms
proof (induct "Rep_initTree t")
  case (Base x)
  hence "Abs_initTree (Base x) =  t" using Rep_initTree_inverse by auto
  then show ?case using Base(2) unfolding iBase_def by auto
next
  case (Branch x1 x2)
  hence a: "Abs_initTree (Branch x1 x2) = t" using Rep_initTree_inverse by auto
  then obtain t1 t2 where m1:"Abs_initTree x1 = t1" "Abs_initTree x2 = t2" by auto
  have i:"x1 \<in> {t. initialised t}" using a 
    by (metis Branch.hyps(3) Rep_initTree base.simps(2) initialised.simps mem_Collect_eq) 
  then have "(Branch (Rep_initTree t1) x2) = Branch x1 x2" 
     using a m1 i Abs_initTree_inverse by auto
  then show ?case using Branch(5) a m1 unfolding iBranch_def sorry
qed
*)

