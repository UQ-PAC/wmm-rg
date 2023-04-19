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

instantiation "tree" :: (type) pstate         (* state is a type class 
        and tree has to define a push operation whose arg is of type *)
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
type_synonym ('v,'g,'a) gstateTree = "(('v,'g,'a) state_rec_scheme) tree"

type_synonym ('v,'g,'r,'a) predTree = "('v,'g,'r,'a) stateTree set"
type_synonym ('v,'g,'a) gpredTree = "('v,'g,'a) gstateTree set"

type_synonym ('v,'g,'r,'a) trelTree = "('v,'g,'r,'a) stateTree rel"
type_synonym ('v,'g,'a) grelTree = "('v,'g,'a) gstateTree rel"

(* trans as in predicate transformer, e.g., wp *)
type_synonym ('v,'g,'r,'a) transTree = "('v,'g,'r,'a) predTree \<Rightarrow> ('v,'g,'r,'a) predTree"
type_synonym ('v,'g,'r,'a) rtransTree = "('v,'g,'r,'a) trelTree \<Rightarrow> ('v,'g,'r,'a) trelTree"

(* the possible extension of the state is used to store this auxiliary information *)
type_synonym ('v,'g,'r,'a) auxfnTree = "('v,'g,'r,'a) stateTree \<Rightarrow> 'a"


subsection \<open>Tree access: base, top and lookup\<close>


fun base :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state" where
  "base (Base s) = s" |
  "base (Branch m m') = (base m)"

(*
fun base :: "('v,'a,'b) state_rec_scheme tree \<Rightarrow> ('v,'a,'b) state_rec_scheme" where
  "base (Base s) = s" |
  "base (Branch m m') = (base m)"
*)


fun treeTop :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state" where
  "treeTop (Base s) = s" |
  "treeTop (Branch m m') = treeTop m'"
(*
fun top :: "('v,'a,'b) state_rec_scheme tree \<Rightarrow> ('v,'a,'b) state_rec_scheme" where
  "top (Base s) = s" |
  "top (Branch m m') = (case m' of (Base s) \<Rightarrow> s | _ \<Rightarrow> (top m'))"
*)

text \<open> lookup of var in a stateTree finds the closest (topmost) frame in which var is defined 
         and returns its value in that frame;
        when the variable is undefined (i.e., equals None) in the base of the tree, 
         then lookup uses the initialisation of that that state, initState m
       
       lookupSome turns the option value into a value          \<close>

(*  (lookup t) and (lookupSome t)  match (st m) -- give a mapping var \<rightarrow> val option 
                                                               or var \<rightarrow> val *)

(* fun lookup :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 'a \<Rightarrow> 'v option" where *)
fun lookup :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v option" where
  "lookup (Base s) var =  (st s var)" |
  "lookup (Branch m m') var =
                      (case (lookup m' var) of Some v \<Rightarrow> Some v |_ \<Rightarrow> lookup m var)"

fun lookupSome :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v" where
  "lookupSome t var = (case (lookup t var) of Some v \<Rightarrow> v | 
                                                   _ \<Rightarrow> (initState (base t) var))"

(* obtains the global state of current tree *)

(* todo: needs to lookup in the base *)

definition glb\<^sub>t :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g \<Rightarrow> 'v option)"
  where "glb\<^sub>t t \<equiv> \<lambda>v. (lookup t) (Glb v)"

definition glb\<^sub>tSome :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g \<Rightarrow> 'v)"
  where "glb\<^sub>tSome t \<equiv> \<lambda>v. (lookupSome t) (Glb v)"

text \<open>Produce a tree on globals only from a full tree\<close>
fun glb\<^sub>tTree :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'a) gstateTree"  where 
  "glb\<^sub>tTree (Base s) = Base (glbSt s)" |
  "glb\<^sub>tTree (Branch t t') = Branch (glb\<^sub>tTree t)(glb\<^sub>tTree t')"

(* local state of current tree *)
definition rg\<^sub>t :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('r \<Rightarrow> 'v option)"
  where "rg\<^sub>t t \<equiv> \<lambda>v. (lookup t) (Reg v)"

definition rg\<^sub>tSome :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('r \<Rightarrow> 'v)"
  where "rg\<^sub>tSome t \<equiv> \<lambda>v. (lookupSome t) (Reg v)"

(* auxiliary component of tree is the aux of its top state *)
definition aux\<^sub>t 
  where "aux\<^sub>t t \<equiv> aux (treeTop t)"



subsection \<open>Write Operations on trees: update top and tree\<close>

(* top_upd :: tree \<Rightarrow> var \<Rightarrow> val \<Rightarrow> state *)
(*definition top_upd :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 
                                               'a \<Rightarrow> 'v \<Rightarrow> ('v,'a,'c) state_rec_scheme" where *)
definition top_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r) var \<Rightarrow> 'v \<Rightarrow> ('v,'g,'r,'a) state" where 
  "top_upd t r val = (st_upd (treeTop t) r val)"

(* definition top_aux_upd :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 
                     (('v,'a,'c) state_rec_scheme \<Rightarrow> 'c) \<Rightarrow> ('v,'a,'c) state_rec_scheme tree" where *)
definition top_aux_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> 
                                  (('v,'g,'r,'a) state \<Rightarrow> 'a) \<Rightarrow> ('v,'g,'r,'a) state" where
  "top_aux_upd t f = (aux_upd (treeTop t) f)"

(* tree_upd :: tree \<Rightarrow> state \<Rightarrow> tree *)
(*fun tree_upd :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow> 
                             ('v,'a,'c) state_rec_scheme \<Rightarrow> ('v,'a,'c) state_rec_scheme tree" where *)
fun tree_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r,'a) stateTree" where
  "tree_upd (Base s) newTop = (Base newTop)" |
  "tree_upd (Branch m m') newTop = (Branch m (tree_upd m' newTop))"

fun base_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r,'a) stateTree" where
  "base_upd (Base s) newBase = (Base newBase)" |
  "base_upd (Branch m m') newBase = (Branch (base_upd m newBase) m')"

(* tr_upd :: tree \<Rightarrow> var \<Rightarrow> val \<Rightarrow> tree *)
(*definition tr_upd :: "('v,'a,'b) state_rec_scheme tree \<Rightarrow> 'a \<Rightarrow> 'v  \<Rightarrow> ('v,'a,'b) state_rec_scheme tree" *)
definition tr_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r)var \<Rightarrow> 'v  \<Rightarrow> ('v,'g,'r,'a) stateTree" 
  where "tr_upd t a b = tree_upd t ((treeTop t) \<lparr> st := ((st (treeTop t)) (a := Some b)) \<rparr>)"

fun tree_base_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r,'a) stateTree"
  where "tree_base_upd (Base m) newBase = (Base newBase)" | 
        "tree_base_upd (Branch m m') newBase = (Branch (tree_base_upd m newBase) m')"

definition tr_base_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('g,'r)var \<Rightarrow> 'v  \<Rightarrow> ('v,'g,'r,'a) stateTree"
  where "tr_base_upd t a b = tree_base_upd t ((base t) \<lparr> st := ((st (base t)) (a := Some b)) \<rparr>)"

(*definition tr_aux_upd :: "('v,'a,'c) state_rec_scheme tree \<Rightarrow>
                            (('v,'a,'c) state_rec_scheme \<Rightarrow> 'c)  \<Rightarrow> ('v,'a,'c) state_rec_scheme tree" *)
definition tr_aux_upd :: "('v,'g,'r,'a) stateTree \<Rightarrow> 
                                   (('v,'g,'r,'a) state \<Rightarrow> 'a)  \<Rightarrow> ('v,'g,'r,'a) stateTree" 
  where "tr_aux_upd t f = tree_upd t ((treeTop t) \<lparr>state_rec.more := f (treeTop t)\<rparr>)"


lemma "tr_aux_upd t f = tree_upd t (top_aux_upd t f)" 
  using tr_aux_upd_def top_aux_upd_def aux_upd_def by metis

syntax
  "_updbindt" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ :=\<^sub>t/ _)")
  "_updbindat" :: "'a \<Rightarrow> updbind"                  ("(2aux\<^sub>t:/ _)")
  "_updbindb" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ :=\<^sub>b/ _)")

translations
  "t(x :=\<^sub>t y)" \<rightleftharpoons> "CONST tr_upd t x y"
  "t(aux\<^sub>t: f)" \<rightleftharpoons> "CONST tr_aux_upd t f"
  "t(x :=\<^sub>b y)" \<rightleftharpoons> "CONST tr_base_upd t x y"


subsection \<open> tree lemmas \<close>



(* lemma [simp]: *)
  (* "glb\<^sub>t (t(Reg r :=\<^sub>t e, aux\<^sub>t: f)) = glb\<^sub>t (t(aux\<^sub>t: \<lambda>m. f(treeTop (t(Reg r :=\<^sub>t e)))))" *)
  (* by (auto simp: glb\<^sub>t_def) *)

lemma [simp]:
  "lookup t (Reg x) = rg\<^sub>t t x"
  by (auto simp: rg\<^sub>t_def)


(* lemma [simp]: *)
  (* shows "base (base_upd t x) = x" *)
  (* by (induct t) auto *)

interpretation treebase: state
  "\<lambda>s v. state_rec.st (base s) v"
  "\<lambda>s v x. base_upd s (st_upd (base s) v x)"
  "aux" 
  "\<lambda>s f. base_upd s (aux_upd (base s) f)"
  "base"
  apply unfold_locales 
  unfolding aux_def
     apply (induct_tac s; auto)
    apply (induct_tac s; auto)
   apply (induct_tac s; auto)
  apply (induct_tac m; auto)
  done

abbreviation region where 
  "region x \<equiv> (case x of Reg _ \<Rightarrow> True | Glb _ \<Rightarrow> False)"

interpretation treetop: state
  "\<lambda>s v. lookup s v" 
  tr_upd
  aux
  "\<lambda>t f. tr_aux_upd t f" 
  "treeTop"
  apply unfold_locales
  unfolding aux_def tr_upd_def tr_aux_upd_def
  apply (induct_tac s; auto)
    apply (induct_tac s; auto)
   apply (induct_tac s; auto)
  apply (induct_tac m; auto)
  done

lemma [simp]:
  "glb\<^sub>t (t(Reg r :=\<^sub>t e)) = glb\<^sub>t t"
  unfolding glb\<^sub>t_def
  by auto

lemma tr_aux_exec [intro!]:
  assumes "(t\<^sub>1,t\<^sub>2) \<in> P"
  shows "(t\<^sub>1,t\<^sub>2(aux\<^sub>t: f)) \<in> P O {(t, t'). t' = t(aux\<^sub>t: f)}"
  using assms by blast

lemma [simp]:
  "aux\<^sub>t (t(Reg x :=\<^sub>t e)) = aux\<^sub>t t"
  unfolding aux\<^sub>t_def
  using treetop.st_upd_aux
  by simp

lemma
  "state_rec.more (treeTop (t(x :=\<^sub>t e))) = state_rec.more (treeTop t)"
  using treetop.st_upd_aux
  by (auto simp add: aux_def)

lemma 
  "state_rec.more (treeTop (t(aux\<^sub>t: f))) = f (treeTop t)"
  using treetop.aux_upd
  by (auto simp add: aux_def)

lemma
  "rg\<^sub>t (t(Reg x :=\<^sub>t e)) = (rg\<^sub>t t)(x := Some e)"
  using treetop.st_upd_map
  unfolding rg\<^sub>t_def
  by auto
 
lemma tr_aux_nop:
  "t(aux\<^sub>t:more) = t"
  using treetop.aux_upd
  unfolding aux_def
  oops


lemma tr_aux_st:
  "lookup (t(aux\<^sub>t: e)) = lookup t" 
  using treetop.aux_upd_st
  by auto


lemma treeUpd_top [simp]: 
  "tree_upd t (treeTop t) = t" 
  using treetop.st_upd
  unfolding tr_upd_def
  oops

lemma [simp]: 
  "st (treeTop (tr_upd t v x)) v = Some x"
  unfolding tr_upd_def
  by (induct t rule: tree.induct) auto


lemma treeUpd_base [simp]:
  "tree_base_upd t (base t) = t" 
  by (induct t)(auto)


lemma stUpd_single :
   "x \<noteq> r  \<Longrightarrow> st (st_upd m r v) x = st m x \<and> 
               initState (st_upd m r v) x = initState m x" 
  by (simp add: st_upd_def)

lemma topUpd_single:
 "x \<noteq> r  \<Longrightarrow> lookup (Base (top_upd (Base s) r (the val))) x = lookup (Base s) x"
  using top_upd_def stUpd_single by (metis(full_types) lookup.simps(1) treeTop.simps(1))

lemma treeUpd_change:
  "x \<noteq> r  \<Longrightarrow> lookup (tree_upd t (top_upd t r (the val))) x = lookup t x"  
  apply (drule treetop.st_upd_diff)
  unfolding tr_upd_def st_upd_def top_upd_def
  by auto

lemma top_treeUpd [simp]:
    "treeTop (tree_upd t newTop) = newTop" 
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
  using treetop.st_upd
  unfolding st_upd_def top_upd_def tr_upd_def
  by metis

lemma lookupSome_upd:
  "lookupSome (tree_upd t (top_upd t r val)) r = val"
  using lookup_upd lookupSome.elims by (metis option.simps(5))


lemma treeUpd_change1:
  "x \<noteq> r  \<Longrightarrow> lookup (tree_upd t ((treeTop t) \<lparr> st := ((st (treeTop t)) (r := Some (ev\<^sub>E t f))) \<rparr>)) x
                                       = lookup t x"
  using treeUpd_change by (metis option.sel st_upd_def top_upd_def)

lemma treeUpd_change2:
  "x = r  \<Longrightarrow> lookup (tree_upd t ((treeTop t) \<lparr> st := ((st (treeTop t)) (r := Some (ev\<^sub>E t f))) \<rparr>)) x
                                       = Some (ev\<^sub>E t f)"
     by (metis lookup_upd st_upd_def top_upd_def)

section \<open>Simp Lemmas\<close>

lemma
  assumes "r = q"
  shows "lookup (tree_upd t (treeTop t\<lparr>st := st (treeTop t)(q \<mapsto> e)\<rparr>)) q = Some e"
  by (metis lookup_upd st_upd_def top_upd_def)

lemma
  assumes "r \<noteq> q"
  shows "lookup (tree_upd t (treeTop t\<lparr>st := st (treeTop t)(r \<mapsto> e)\<rparr>)) q = lookup t q"
  by (metis assms option.sel st_upd_def top_upd_def treeUpd_change)

lemma lookup_upd_var:
  "lookup (t(r :=\<^sub>t e)) q = (if r = q then Some e else lookup t q)"
  using treetop.st_upd
  by simp

lemma lookupSome_upd_var:
  "lookupSome (t (r :=\<^sub>t f))  x = (if x = r then f else (lookupSome t x))"
  using treetop.st_upd lookup_upd_var
  unfolding lookupSome.simps
  apply (cases "lookup (t(r :=\<^sub>t f)) x")
  by auto (smt (verit) base.simps(1) base.simps(2) select_convs(3) surjective top_treeUpd tr_upd_def tree.distinct(1) tree_upd.elims update_convs(1))

lemma initState_auxupd [simp]: 
  "initState (base (t(aux\<^sub>t: f))) x = initState (base t) x"
  unfolding tr_aux_upd_def
  by (induct t) auto

lemma lookupSome_auxupd [simp]:
  "lookupSome (t(aux\<^sub>t: f)) x = lookupSome t x" 
  using treetop.aux_upd_st initState_auxupd
  unfolding lookupSome.simps
  by (cases "lookup (t(aux\<^sub>t: f)) x" ; cases "lookup t x") auto

lemma [simp]:
  "tree_upd t (top_aux_upd t f) = t(aux\<^sub>t: f)"
  unfolding tr_aux_upd_def top_aux_upd_def aux_upd_def
  by simp

lemma
  "lookup (t(v :=\<^sub>t e)) = (lookup t)(v := Some e)"
  by (auto simp: st_upd_def)

lemma 
  "more (treeTop (t(aux\<^sub>t: e))) = e (treeTop t)"
  using treetop.aux_upd
  unfolding aux_def
  by auto


lemma rg\<^sub>t_glbupd:
  "rg\<^sub>t (t(Glb x :=\<^sub>t e)) = rg\<^sub>t t"
  unfolding rg\<^sub>t_def 
  using treetop.st_upd_region[where ?region=region]
  by simp
 

(*
lemma br_eq1:
   "t\<^sub>1 = t\<^sub>2 \<Longrightarrow> \<forall> t. Branch t t\<^sub>1 = Branch t t\<^sub>2" by simp

lemma br_eq2:
   "t\<^sub>1 = t\<^sub>2 \<Longrightarrow> \<forall> t. Branch t\<^sub>1 t = Branch t\<^sub>2 t" by simp

lemma tr_eq:
   "t\<^sub>1 = t\<^sub>2 \<Longrightarrow> 
        (top t\<^sub>1) = (top t\<^sub>2) \<and> (\<exists>t\<^sub>B. Branch t\<^sub>B (Base (top t\<^sub>1)) = Branch t\<^sub>B (Base (top t\<^sub>2)))" 
  by simp
*)

lemma tree_upd_twist: "a \<noteq> c \<Longrightarrow> (t(a :=\<^sub>t b))(c :=\<^sub>t d) = (t(c :=\<^sub>t d))(a :=\<^sub>t b)"
  by (induct t) (auto simp add: fun_upd_twist tr_upd_def)


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
*)
