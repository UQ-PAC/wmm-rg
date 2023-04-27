theory SimAsm_ExpTree
  imports SimAsm_StateTree SimAsm_Exp
begin

section \<open>Expression Language based on state trees \<close>


text \<open>Evaluate an expression given a state tree, such that variable values are looked up in the 
          innermost scope in which a value is mapped to variable \<close>

fun tr_ev\<^sub>E :: "('v,'g, 'r,'a) stateTree \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> 'v"
  where "tr_ev\<^sub>E m r = ev\<^sub>E (lookupSome m) r" 


text \<open>Evaluate an expression given a state tree, such that variable values are looked up in the
        innermost scope in which a value exists \<close>
fun tr_ev\<^sub>B :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r) bexp \<Rightarrow> bool"
  where  "tr_ev\<^sub>B m r = ev\<^sub>B (lookupSome m) r" 



section \<open>Operations\<close>

text \<open>Operation Behaviour\<close>

fun beh\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) stateTree rel"
  where
    "beh\<^sub>i (assign a e) = {(t,t'). t' = t (a :=\<^sub>t (tr_ev\<^sub>E (t) e))}" |
    "beh\<^sub>i (cmp b) = {(t,t'). t = t' \<and> tr_ev\<^sub>B t b}" |
    "beh\<^sub>i (leak Cache e) = {(t,t'). t' = t(Cache :=\<^sub>b (tr_ev\<^sub>E (t) e))}" | 
    "beh\<^sub>i _ = Id"
 
subsection \<open>Expression\<close>

lemma tr_ev_subst\<^sub>E [simp]:
  "tr_ev\<^sub>E t (subst\<^sub>E e r f) = tr_ev\<^sub>E (t (r :=\<^sub>t (tr_ev\<^sub>E t f))) e"
proof (induct e)
  case (Var x)
  then show ?case using lookupSome_upd_var Var by (metis ev\<^sub>E.simps(1) tr_ev\<^sub>E.simps(1) subst\<^sub>E.simps(1))
  next
  case (Val x)
  then show ?case by simp
next
  case (Exp fn rs) 
  hence [simp]: "(map (tr_ev\<^sub>E t \<circ> (\<lambda>x. subst\<^sub>E x r f)) rs) = (map (tr_ev\<^sub>E  (t (r :=\<^sub>t (tr_ev\<^sub>E t f)))) rs)" 
    by auto
  show ?case using ev\<^sub>E.simps(2) subst\<^sub>E.simps(2) apply simp 
    by (smt (verit, ccfv_threshold) Exp comp_apply tr_ev\<^sub>E.simps map_eq_conv)
qed



lemma tr_ev_nop\<^sub>E [simp]:
 "r \<notin> deps\<^sub>E e  \<Longrightarrow> tr_ev\<^sub>E ((t(r :=\<^sub>t f))) e = tr_ev\<^sub>E t e"
proof (induct e)
  case (Var x)
  then show ?case using lookupSome_upd_var ev\<^sub>E.simps(1) tr_ev\<^sub>E.simps(1) Var by (metis deps\<^sub>E.simps(1) insert_iff)
next
  case (Exp fn rs)
  hence [simp]: "map (tr_ev\<^sub>E (t(r :=\<^sub>t f))) rs = map (tr_ev\<^sub>E t) rs" by auto
  show ?case using ev\<^sub>E.simps(2) subst\<^sub>E.simps(2) Exp tr_ev\<^sub>E.simps map_eq_conv apply simp 
    by (metis map_cong)
qed auto


lemma deps_tr_ev\<^sub>E [intro]:
  "\<forall>x \<in> deps\<^sub>E e . lookupSome t x = lookupSome t' x \<Longrightarrow> tr_ev\<^sub>E t e = tr_ev\<^sub>E t' e"
proof (induct e)
  case (Var x) 
  show ?case using deps\<^sub>E.simps(1) tr_ev\<^sub>E.simps(1) lookup.simps tr_ev\<^sub>E.simps(1) using Var by simp
  next
  case (Val x)
  then show ?case by auto
next
  case (Exp fn rs)
  hence [simp]: "map (tr_ev\<^sub>E t) rs = map (tr_ev\<^sub>E t') rs" by (induct rs) auto
  then show ?case using Exp ev\<^sub>E.simps(2) subst\<^sub>E.simps(2) Exp tr_ev\<^sub>E.simps map_eq_conv apply simp 
    by (metis map_cong)
qed


lemma local_tr_ev\<^sub>E [intro]:
  "deps\<^sub>E e \<subseteq> locals \<Longrightarrow> rg\<^sub>tSome t = rg\<^sub>tSome t' \<Longrightarrow> tr_ev\<^sub>E t e = tr_ev\<^sub>E t' e"   
  apply (intro deps_tr_ev\<^sub>E lookup.simps ballI, case_tac x)        
  using rg\<^sub>tSome_def apply metis by blast


lemma help_lookup:
  assumes "lookup (Base s) x = lookup (Base s') x"
  shows "lookup (tree_upd t s) x = lookup (tree_upd t s') x"
  using assms
proof (cases "st s x = Some val")
    case True
    then show ?thesis using assms 
    proof (induct t)
      case (Base x)
      then show ?case by (metis tree_upd.simps(1))
    next
      case (Branch t1 t2)
      then show ?case using top_treeUpd lookup_upd by simp
    qed
  next
    case False
    then show ?thesis using assms 
    proof (induct t)
      case (Base x)
      then show ?case by auto
    next
      case (Branch t1 t2)
      then show ?case by fastforce
    qed
qed

lemma aux_lookup':
 "lookup (t (aux\<^sub>t: f)) x = lookup t x" by simp  


(* if the aux component of top of t is updated, it doesn't have an effect on the evaluation of 
    variable/expression g *)

lemma tr_ev_st_eq: 
  "lookupSome t1 = lookupSome t2 \<Longrightarrow> tr_ev\<^sub>E t1 g = tr_ev\<^sub>E t2 g"
  by (induct g, (auto)[2]) (metis deps_tr_ev\<^sub>E)
  
lemma tr_ev_aux\<^sub>E [simp]:
  "tr_ev\<^sub>E (tree_upd t (top_aux_upd t f)) g = tr_ev\<^sub>E t g"
  using lookupSome_auxupd tr_ev_st_eq
  by fastforce


lemma tr_ev_aux\<^sub>E' [simp]:
  "tr_ev\<^sub>E (t (aux\<^sub>t:f)) g = tr_ev\<^sub>E t g"
  using tr_ev_aux\<^sub>E
  by auto


subsection \<open>Boolean Expression\<close>

lemma tr_ev_subst\<^sub>B [simp]:
  "tr_ev\<^sub>B t (subst\<^sub>B b r e) = tr_ev\<^sub>B (tree_upd t (top_upd t r (tr_ev\<^sub>E t e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs) 
   hence [simp]: "map (tr_ev\<^sub>E t \<circ> (\<lambda>x. subst\<^sub>E x r e)) rs
            = map (tr_ev\<^sub>E (tree_upd t (top_upd t r (tr_ev\<^sub>E t e)))) rs" 
      using top_upd_def by (metis comp_eq_dest_lhs tr_ev_subst\<^sub>E st_upd_def tr_upd_def)
    then show ?case sorry
qed simp+

lemma tr_ev_subst\<^sub>B' [simp]:
  "tr_ev\<^sub>B t (subst\<^sub>B b r e) = tr_ev\<^sub>B (t (r :=\<^sub>t (tr_ev\<^sub>E t e))) b"
  sorry
 (* by (simp add: st_upd_def top_upd_def tr_upd_def) *)


lemma tr_ev_nop\<^sub>B [simp]:
   "r \<notin> deps\<^sub>B b \<Longrightarrow> tr_ev\<^sub>B (tree_upd t (top_upd t r f)) b = tr_ev\<^sub>B t b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (tr_ev\<^sub>E (tree_upd t (top_upd t r f))) rs = map (tr_ev\<^sub>E t) rs" 
    using tr_ev_nop\<^sub>E[of r _ t f] apply (auto simp: top_upd_def)
    by (metis st_upd_def tr_upd_def)
  then show ?case sorry
qed simp


lemma tr_ev_nop\<^sub>B' [simp]:
   "r \<notin> deps\<^sub>B b \<Longrightarrow> tr_ev\<^sub>B (t (r :=\<^sub>t f)) b = tr_ev\<^sub>B t b" 
proof (induct b)
  case (Neg b)
  then show ?case by simp
next
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (tr_ev\<^sub>E (t (r :=\<^sub>t f))) rs = map (tr_ev\<^sub>E t) rs" 
    using top_upd_def apply simp 
    by (smt (verit, ccfv_threshold) SimAsm_ExpTree.tr_ev_nop\<^sub>E tr_ev\<^sub>E.elims)
  then show ?case sorry
qed


lemma deps_tr_ev\<^sub>B [intro]:
  "\<forall>x \<in> deps\<^sub>B e. (lookupSome t) x = (lookupSome t') x \<Longrightarrow> tr_ev\<^sub>B t e = tr_ev\<^sub>B t' e"
proof (induct e)
  case (Exp\<^sub>B fn rs) 
  hence [simp]: "map (tr_ev\<^sub>E t) rs = map (tr_ev\<^sub>E t') rs" by (induct rs) auto
  then show ?case sorry
qed auto


lemma tr_ev_aux\<^sub>B [simp]:
  "tr_ev\<^sub>B (tree_upd t (top_aux_upd t f)) g = tr_ev\<^sub>B t g"
proof (induct g)
  case (Neg g)
  then show ?case by simp
next
  case (Exp\<^sub>B x1a x2)
  then show ?case using tr_ev\<^sub>B.simps tr_ev_aux\<^sub>E map_eq_conv
    by (metis (mono_tags, lifting) ev\<^sub>B.simps(2) tr_ev\<^sub>E.elims)
qed

lemma tr_ev_aux\<^sub>B' [simp]:
  "tr_ev\<^sub>B (t (aux\<^sub>t: f)) g = tr_ev\<^sub>B t g"
  by (metis aux_upd_def tr_ev_aux\<^sub>B top_aux_upd_def tr_aux_upd_def)


subsection \<open>Update lemmas on trees\<close>

definition updTree         (* assume total fun f : 'a \<longrightarrow> 'v *)
  where "updTree S f t \<equiv> 
           tree_upd t ((treeTop t)\<lparr>st := \<lambda>x. if x \<in> S then Some (f x) else st (treeTop t) x\<rparr>)" 

definition updTree_base         (* assume total fun f : 'a \<longrightarrow> 'v *)
  where "updTree_base S f t \<equiv> 
           tree_base_upd t ((base t)\<lparr>st := \<lambda>x. if x \<in> S then Some (f x) else st (base t) x\<rparr>)" 

definition updTree_part      (* assume partial fun f : 'a \<rightarrow> 'v option ; like st *)
  where "updTree_part S f t \<equiv> 
           tree_upd t ((treeTop t)\<lparr>st := \<lambda>x. if x \<in> S then (f x) else st (treeTop t) x\<rparr>)" 

lemma updTree_nil [simp]:
  "updTree {} f t = t"
  unfolding updTree_def 
  by (induct t) auto

lemma updTree_base_nil [simp]:
  "updTree_base {} f t = t"
  by (auto simp: updTree_base_def) 

lemma updTreePart_nil [simp]:
  "updTree_part {} f t = t"
  unfolding updTree_part_def 
  by (induct t) auto 

lemma updTree_insert [simp]:
  "updTree (insert x V) f t = tree_upd t ((treeTop (updTree V f t)) (x :=\<^sub>s (f x)))"
  (*  apply (auto simp: updTree_def st_upd_def intro!: state_rec.equality) *)
proof -
  let ?f1 = "(\<lambda>xa. if xa = x \<or> xa \<in> V then Some (f xa) else (st (treeTop t) xa))"
  let ?f2 = "(\<lambda>x. if            x \<in> V then Some (f x) else st (treeTop t) x)(x \<mapsto> (f x))"
  have a0:"?f1 = ?f2" using st_upd_def by fastforce
  hence a1:"Base (treeTop t\<lparr>st := ?f1\<rparr>) = Base (treeTop t\<lparr>st := ?f2\<rparr>)" by simp
  hence a2:"tree_upd t (treeTop t\<lparr>st := ?f1\<rparr>) = tree_upd t (treeTop t\<lparr>st := ?f2\<rparr>)" by simp
  have a3:"tree_upd t (treeTop t\<lparr>st := ?f2\<rparr>) = tree_upd t ((treeTop (updTree V f t))(x :=\<^sub>s (f x)))" 
    using a2 by (auto simp: updTree_def st_upd_def intro!: state_rec.equality) 
  have a4:"tree_upd t (treeTop t\<lparr>st := ?f1\<rparr>) = updTree (insert x V) f t"
    by (auto simp: updTree_def st_upd_def  intro!: state_rec.equality)   
  have a5:"updTree (insert x V) f t = tree_upd t ((treeTop (updTree V f t))(x :=\<^sub>s (f x)))"
    using a3 a4 a2 by simp
  thus ?thesis by simp
qed

lemma updTree_base_insert [simp]:
  "updTree_base (insert x V) f t = tree_base_upd t ((base (updTree_base V f t)) (x :=\<^sub>s (f x)))"
proof -
  let ?f1 = "(\<lambda>xa. if xa = x \<or> xa \<in> V then Some (f xa) else (st (base t) xa))"
  let ?f2 = "(\<lambda>x. if            x \<in> V then Some (f x) else st (base t) x)(x \<mapsto> (f x))"
  have a0:"?f1 = ?f2" using st_upd_def by fastforce
  hence a1:"Base (base t\<lparr>st := ?f1\<rparr>) = Base (base t\<lparr>st := ?f2\<rparr>)" by simp
  hence a2:"tree_base_upd t (base t\<lparr>st := ?f1\<rparr>) = tree_base_upd t (base t\<lparr>st := ?f2\<rparr>)" by simp
  have a3:"tree_base_upd t (base t\<lparr>st := ?f2\<rparr>) = tree_base_upd t ((base (updTree_base V f t))(x :=\<^sub>s (f x)))" 
    using a2 apply (auto simp: updTree_base_def st_upd_def intro!: state_rec.equality)
  proof (induct t)
    case (Base x)
    then show ?case by simp
  next
    case (Branch t1 t2)
    then show ?case apply simp by (metis base.simps(2))
  qed
  have a4:"tree_base_upd t (base t\<lparr>st := ?f1\<rparr>) = updTree_base (insert x V) f t"
    by (auto simp: updTree_base_def st_upd_def upd_def intro!: state_rec.equality)   
  have a5:"updTree_base (insert x V) f t = tree_base_upd t ((base (updTree_base V f t))(x :=\<^sub>s (f x)))"
    using a3 a4 a2 by simp
  thus ?thesis by simp
qed 

lemma updTree_base_single [simp]: 
  "updTree_base {y} f t = t(y:=\<^sub>b f y)" 
  by auto

text \<open>
a variable, v, is "based" in a particular tree state, t, if it is not defined outside of the tree's
base component. this is encoded as the property that any update to v in the base is always visible.
\<close>
definition based where 
  "based t v \<equiv> (\<forall>x. lookup (t(v:=\<^sub>bx)) v = Some x)"

lemma basedE [elim]:
  "based t v \<Longrightarrow> lookup (t(v:=\<^sub>bx)) v = Some x" 
  unfolding based_def by simp

lemma basedI [intro]:
  "(\<And>x. lookup (t(v:=\<^sub>bx)) v = Some x) \<Longrightarrow> based t v" 
  unfolding based_def by simp

lemma based_branchE: 
  "based (Branch t1 t2) y \<Longrightarrow> based t1 y" 
  unfolding based_def 
  apply simp
  apply (cases "lookup t2 y")
   apply auto
  by (metis (full_types) lookup_tr_base_upd)

lemma based_branchE2: 
  "based (Branch t1 t2) y \<Longrightarrow> based t2 y" 
  unfolding based_def 
  apply simp
  apply (cases "lookup t2 y")
   apply auto
  apply (rule lookup_tr_base_upd_none, simp)
  by (simp add: lookup_tr_base_upd_id)

lemma based_tr_base_upd:
  "based t y \<Longrightarrow> based (t(x:=\<^sub>bvalue)) y"
proof (induct t)
  case (Branch t1 t2)
  hence "based t1 y" using based_branchE by auto
  then show ?case 
    using Branch based_def lookup.simps(2) tr_base_upd_branch
    by metis
qed auto

lemma based_tr_upd:
  "x \<noteq> y \<Longrightarrow> based t y \<Longrightarrow> based (t(x:=\<^sub>tvalue)) y"
proof (induct t)
  case (Branch t1 t2)
  hence "based t1 y" using based_branchE by auto
  then show ?case 
    using Branch based_def tr_base_upd_branch
    by (metis tr_upd_branch treetop.st_upd_diff)
qed auto

lemma based_lookupSome:
  "based t y \<Longrightarrow> (x = y) \<Longrightarrow> lookupSome (t(y :=\<^sub>b value)) x = value"
  unfolding st_upd_def based_def 
  by auto

lemma based_updTree_single:
  "based t y \<Longrightarrow> updTree_base {y} (lookupSome (t(y :=\<^sub>b value))) t = t(y:=\<^sub>bvalue)" 
  using basedE
  by fastforce


lemma help_rep:
  assumes "x \<in> A \<Longrightarrow> (st (upd_part A f m) x) = (f x)"
  shows "(\<lambda>x. if x \<in> A then (st (upd_part A f m) x) else (st (treeTop t) x)) =
          (\<lambda>x. if x \<in> A then (f x) else (st (treeTop t) x))"                       (is "?L = ?R")
proof -
  have a0:"?L = (\<lambda>x. if x \<in> A then (st (m\<lparr>st := \<lambda>x. if x \<in> A then (f x) else st m x\<rparr>) x)
                              else (st (treeTop t) x))" by (metis upd_part_def)
  then have a1:"... = (\<lambda>x. if x \<in> A then (f x) else (st (treeTop t) x))" using assms by auto
  then have a2:"... = ?R" by simp
  then show ?thesis using a0 a1 a2 by simp
qed

lemma updTree_rep [simp]:
  "updTree_part A (st (upd_part A f m\<^sub>1)) t\<^sub>2 = updTree_part A f t\<^sub>2"
(*  apply (auto simp: updTree_opt_def intro!: state_rec.equality) *)
proof -
  let ?f1 = "\<lambda>x. if x \<in> A then (st (upd_part A f m\<^sub>1) x) else st (treeTop t\<^sub>2) x"
  let ?f2 = "\<lambda>x. if x \<in> A then (f x) else st (treeTop t\<^sub>2) x"
  have a0:"x \<in> A \<Longrightarrow> (st (upd_part A f m\<^sub>1) x = f x)" using upd_part_def
    by (smt (verit, best) select_convs(1) surjective update_convs(1))
  then have "?f1 = ?f2" using help_rep by blast
  then have 
  "tree_upd t\<^sub>2 (treeTop t\<^sub>2 \<lparr>st := \<lambda>x. if x \<in> A then (st (upd_part A f m\<^sub>1) x) else st (treeTop t\<^sub>2) x\<rparr>) =
  tree_upd t\<^sub>2 (treeTop t\<^sub>2\<lparr>st := \<lambda>x. if x \<in> A then (f x) else st (treeTop t\<^sub>2) x\<rparr>)" 
    by simp
  then show ?thesis by (auto simp: updTree_part_def intro!: state_rec.equality)
qed

(* use of lookup instead of st does not hold since 
   lookup goes down to base to find a value whereas st only looks at (treeTop t) *)
lemma updTree_st [simp]:
  "st (treeTop (updTree S f t)) x = (if x \<in> S then Some (f x) else st (treeTop t) x)"
  by (auto simp: updTree_def) 

lemma updTree_more [simp]:
  "state_rec.more (treeTop (updTree V f t)) = state_rec.more (treeTop t)"
  by (auto simp: updTree_def)

lemma updTree_cap [simp]:
  "state_rec.cap (treeTop (updTree V f t)) = state_rec.cap (treeTop t)"
  by (auto simp: updTree_def)

lemma updTree_init [simp]:
  "state_rec.initState (treeTop (updTree V f t)) = state_rec.initState (treeTop t)"
  by (auto simp: updTree_def)

lemma updTrePart_st [simp]:
  "st (treeTop (updTree_part S f t)) x = (if x \<in> S then (f x) else st (treeTop t) x)"
   by (auto simp: updTree_part_def) 

lemma updTreePart_more [simp]:
  "state_rec.more (treeTop (updTree_part V f t)) = state_rec.more (treeTop t)"
  by (auto simp: updTree_part_def)

lemma updTreePart_cap [simp]:
  "state_rec.cap (treeTop (updTree_part V f t)) = state_rec.cap (treeTop t)"
  by (auto simp: updTree_part_def)

lemma updTreePart_init [simp]:
  "state_rec.initState (treeTop (updTree_part V f t)) = state_rec.initState (treeTop t)"
  by (auto simp: updTree_part_def)


lemma treeBase_equality:
  "s\<^sub>1 = s\<^sub>2 \<Longrightarrow> (Base s\<^sub>1) = (Base s\<^sub>2)" by auto

lemma treeBranch_equality:
  "t\<^sub>1 = t\<^sub>1' \<Longrightarrow> t\<^sub>2 = t\<^sub>2' \<Longrightarrow> Branch t\<^sub>1 t\<^sub>2 = Branch t\<^sub>1' t\<^sub>2'" by auto 

(* this lemma needs to be split up into different cases (above) as it does not hold for leak instr *)

lemma beh_subst\<^sub>i_nonleak:
  assumes "\<And>y z. \<alpha> \<noteq> leak y z"
  shows   "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = 
              {(t, updTree (wr \<alpha>) (lookupSome t') t) |t t'. (t(x :=\<^sub>t tr_ev\<^sub>E t e), t') \<in> beh\<^sub>i \<alpha>}"
proof (cases \<alpha>)
  case (assign x11 x12)
  then show ?thesis 
    sorry (*by auto (simp_all add: st_upd_def tr_upd_def)*)
next
  case (cmp x2)
  then show ?thesis
    using tr_ev_subst\<^sub>B tr_ev_subst\<^sub>B' sorry
next
  case full_fence
  then show ?thesis by auto
next
  case nop
  then show ?thesis by auto
next
  case (leak x51 x52)
  then show ?thesis using assms by simp
qed

(* these are subsumed by the above *)
lemma beh_subst\<^sub>i_assign [simp]:
  assumes "\<alpha> = assign y z"
  shows   "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = 
              {(t, updTree (wr \<alpha>) (lookupSome t') t) |t t'. (t(x :=\<^sub>t tr_ev\<^sub>E t e), t') \<in> beh\<^sub>i \<alpha>}"
  by (rule beh_subst\<^sub>i_nonleak) (simp add: assms)

lemma beh_subst\<^sub>i_cmp [simp]:
  assumes "\<alpha> = cmp b"
  shows   "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = 
              {(t, updTree (wr \<alpha>) (lookupSome t') t) |t t'. (t(x :=\<^sub>t tr_ev\<^sub>E t e), t') \<in> beh\<^sub>i \<alpha>}"
  by (rule beh_subst\<^sub>i_nonleak) (simp add: assms)

lemma beh_subst\<^sub>i_fence [simp]:
  assumes "\<alpha> = full_fence"
  shows   "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = 
              {(t, updTree (wr \<alpha>) (lookupSome t') t) |t t'. (t(x :=\<^sub>t tr_ev\<^sub>E t e), t') \<in> beh\<^sub>i \<alpha>}"
  by (rule beh_subst\<^sub>i_nonleak) (simp add: assms)  

lemma beh_subst\<^sub>i_nop [simp]:
  assumes "\<alpha> = nop"
  shows   "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = 
              {(t, updTree (wr \<alpha>) (lookupSome t') t) |t t'. (t(x :=\<^sub>t tr_ev\<^sub>E t e), t') \<in> beh\<^sub>i \<alpha>}"
  by (rule beh_subst\<^sub>i_nonleak) (simp add: assms) 
(*---*)


lemma beh_subst\<^sub>i_leak [simp]:
  assumes "\<alpha> = leak y z"
  shows   "beh\<^sub>i (subst\<^sub>i \<alpha> x e) =
              {(t, updTree_base (wr \<alpha>) (lookupSome t') t) |t t'. (t(x :=\<^sub>t tr_ev\<^sub>E t e), t') \<in> beh\<^sub>i \<alpha>}"
  using assms
  apply auto
   apply (case_tac "lookup (a(x :=\<^sub>t tr_ev\<^sub>E a e, y :=\<^sub>b tr_ev\<^sub>E (a(x :=\<^sub>t tr_ev\<^sub>E a e)) z)) y")
    apply auto
    apply (metis lookup_tr_base_upd option.simps(3))
   defer
   apply (case_tac "lookup (t(x :=\<^sub>t tr_ev\<^sub>E t e, y :=\<^sub>b tr_ev\<^sub>E (t(x :=\<^sub>t tr_ev\<^sub>E t e)) z)) y")
    apply auto
    apply (metis lookup_tr_base_upd option.distinct(1))
proof goal_cases
  case (1 t a)
  hence "based t y" "x \<noteq> y" sorry (* are these assumptions required ? ! if so, where? *)
  hence a: "tr_ev\<^sub>E (t(x :=\<^sub>t tr_ev\<^sub>E t e)) z = a" using 1 based_tr_upd  sorry  
  then have c: "t(y :=\<^sub>b a) = t(y :=\<^sub>b tr_ev\<^sub>E (t(x :=\<^sub>t tr_ev\<^sub>E t e)) z)" using 1 sorry
  (* there is another possibility. 
  we do not strictly need the fact (a), we just need to show the ?case. 
  this could be done by arguing in this way: 
    - if y is based, then proceed with (a). then, if x = y then x is also based, otherwise as above.
    - if y is not based in t, then (c) could be argued since y's base update will be hidden in 
      both states, and so they are "visually equivalent" at that time.
  *)
  then show ?case sorry 
next
  case (2 t a)
  show ?case using 2 sorry (* identical argument to 1 *)
qed



end