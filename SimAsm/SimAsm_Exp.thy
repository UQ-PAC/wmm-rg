theory SimAsm_Exp
  imports SimAsm_StateTree
begin

section \<open>Expression Language\<close>

(* first value in Exp is a function used to combine the values from its
subexpressions into one value. *)
datatype ('v,'g,'r) exp = 
  Var "('g,'r) var" | 
  Val 'v | 
  Exp "'v list \<Rightarrow> 'v" "('v,'g,'r) exp list" (* some fct over a list of subexpr *) 


text \<open>Evaluate an expression given a state tree, such that variable values are looked up in the 
          innermost scope in which a value is mapped to variable \<close>

(*
text \<open>Evaluate an expression given a state\<close>
fun ev\<^sub>E :: "('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> 'v"
  where 
    "ev\<^sub>E m (Var r) = st m r" |
    "ev\<^sub>E _ (Val v) = v" |
    "ev\<^sub>E m (Exp f rs) = f (map (ev\<^sub>E m) rs)"
*)

fun ev\<^sub>E :: "('v,'g, 'r,'a) stateTree \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> 'v"
  where 
    "ev\<^sub>E m (Var r) = lookupSome m r" |
    "ev\<^sub>E _ (Val v) = v" |
    "ev\<^sub>E m (Exp f rs) = f (map (ev\<^sub>E m) rs)"  (* eg, Exp(+ a1 a2 a3) = (ev a1) + (ev a2) + (ev a3) *)



text \<open>The syntactic dependencies of an expression\<close>
fun deps\<^sub>E :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var set"
  where 
    "deps\<^sub>E (Var r) = {r}" |
    "deps\<^sub>E (Exp _ rs) = \<Union>(deps\<^sub>E ` set rs)" |
    "deps\<^sub>E _ = {}"


text \<open>Substitute a variable for an expression\<close>
fun subst\<^sub>E :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) exp"
  where
    "subst\<^sub>E (Var r) r' e = (if r = r' then e else Var r)" |
    "subst\<^sub>E (Exp f rs) r e = (Exp f (map (\<lambda>x. subst\<^sub>E x r e) rs))" |
    "subst\<^sub>E e _ _ = e"

datatype ('v,'g,'r) bexp = 
  Neg "('v,'g,'r) bexp" | 
  Exp\<^sub>B "'v list \<Rightarrow> bool" "('v,'g,'r) exp list"

text \<open>Evaluate an expression given a state tree, such that variable values are looked up in the
        innermost scope in which a value exists \<close>
fun ev\<^sub>B :: "('v,'g,'r,'a) stateTree \<Rightarrow> ('v,'g,'r) bexp \<Rightarrow> bool"
  where 
    "ev\<^sub>B m (Neg e) = (\<not> (ev\<^sub>B m e))" |
    "ev\<^sub>B m (Exp\<^sub>B f rs) = f (map (ev\<^sub>E m) rs)"

(*
text \<open>Evaluate an expression given a state\<close>
fun ev\<^sub>B :: "('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r) bexp \<Rightarrow> bool"
  where 
    "ev\<^sub>B m (Neg e) = (\<not> (ev\<^sub>B m e))" |
    "ev\<^sub>B m (Exp\<^sub>B f rs) = f (map (ev\<^sub>E m) rs)"
*)

text \<open>The syntactic dependencies of an expression\<close>
fun deps\<^sub>B :: "('v,'g,'r) bexp \<Rightarrow> ('g,'r) var set"
  where 
    "deps\<^sub>B (Neg e) = deps\<^sub>B e" |
    "deps\<^sub>B (Exp\<^sub>B _ rs) = \<Union>(deps\<^sub>E ` set rs)"

text \<open>Substitute a variable for an expression\<close>
fun subst\<^sub>B :: "('v,'g,'r) bexp \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) bexp"
  where
    "subst\<^sub>B (Neg b) r e = Neg (subst\<^sub>B b r e)" |
    "subst\<^sub>B (Exp\<^sub>B f rs) r e = (Exp\<^sub>B f (map (\<lambda>x. subst\<^sub>E x r e) rs))"

section \<open>Operations\<close>

datatype ('v,'g,'r) op =
    assign "('g,'r) var" "('v,'g,'r) exp"
  | cmp "('v,'g,'r) bexp"
  | full_fence
  | nop

text \<open>Operation Behaviour\<close>
fun beh\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) state rel"
  where
    "beh\<^sub>i (assign a e) = {(m,m'). m' = m (a :=\<^sub>s (ev\<^sub>E (Base m) e))}" |
    "beh\<^sub>i (cmp b) = {(m,m'). m = m' \<and> ev\<^sub>B (Base m) b}" |
    "beh\<^sub>i _ = Id"

(* todo: assignment to cache variable should not sit in top state but at the base *)
fun behTree\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) stateTree rel"
  where 
  "behTree\<^sub>i \<alpha> = {(t,t')| t t' m m'. (m,m')\<in>beh\<^sub>i \<alpha> \<and> top t = m \<and> t'=tree_upd t (Base m')}"
 
(*
fun beh\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) stateTree rel"  
  where
    "beh\<^sub>i (assign a e) = {(t,t'). t' = tree_upd t ((top_upd t a (ev\<^sub>E t e)))}" | 
    "beh\<^sub>i (cmp b) = {(t,t'). t = t' \<and> ev\<^sub>B t b}" |
    "beh\<^sub>i _ = Id"

fun beh\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) state rel"
  where
    "beh\<^sub>i (assign a e) = {(m,m'). m' = m (a :=\<^sub>s ev\<^sub>E m e)}" |
    "beh\<^sub>i (cmp b) = {(m,m'). m = m' \<and> ev\<^sub>B m b}" |
    "beh\<^sub>i _ = Id"
*)


text \<open>Variables written by an operation\<close>
fun wr :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var set"
  where 
    "wr (assign y _) = {y}" |
    "wr _ = {}"

text \<open>Variables read by an operation\<close>
fun rd :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var set"
  where
    "rd (assign _ e) = deps\<^sub>E e" |
    "rd (cmp b) = deps\<^sub>B b" |
    "rd _ = {}"

text \<open>Test if an instruction is a memory barrier\<close>
fun barriers :: "('v,'g,'r) op \<Rightarrow> bool"
  where "barriers full_fence = True" | "barriers _ = False"

text \<open>Operation Substitution\<close>
fun subst\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) op"
  where
    "subst\<^sub>i (assign x e) y f = assign x (subst\<^sub>E e y f)" |
    "subst\<^sub>i (cmp b) y f = cmp (subst\<^sub>B b y f)" |
    "subst\<^sub>i \<alpha> _ _ = \<alpha>"

definition smap1
  where "smap1 V x \<alpha> \<equiv> if x \<in> dom V then subst\<^sub>i \<alpha> x (Val (the (V x))) else \<alpha>"

definition smap 
  where "smap \<alpha> V \<equiv> Finite_Set.fold (smap1 V) \<alpha> (rd \<alpha>)"

definition forall
  where "forall V \<alpha> \<equiv> {smap \<alpha> M | M. dom M = V}"

section \<open>Rules\<close>

subsection \<open>Expression\<close>

 

(*
lemma ev_subst\<^sub>E [simp]:
  "ev\<^sub>E m (subst\<^sub>E e r f) = ev\<^sub>E (m(r :=\<^sub>s (ev\<^sub>E m f))) e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r f)) rs = map (ev\<^sub>E (m(r :=\<^sub>s ev\<^sub>E m f))) rs" by auto
  show ?case by simp
qed auto
*)


lemma ev_subst\<^sub>E [simp]:
  "ev\<^sub>E t (subst\<^sub>E e r f) = ev\<^sub>E (tree_upd t (top_upd t r (ev\<^sub>E t f))) e"
proof (induct e)
  case (Var x)
  then show ?case 
  proof -
    have a1:"top_upd t r (ev\<^sub>E t f) = Base (st_upd (top t) r (ev\<^sub>E t f))" using 
                top_upd_def by metis
    obtain t' where a2:"t'= tree_upd t (Base (st_upd (top t) r (ev\<^sub>E t f)))" by simp
    then have a3:"lookupSome t' r = (ev\<^sub>E t f)" using lookupSome_upd  
        by (metis a1)
    thus ?case using treeUpd_change a1 a2 ev\<^sub>E.simps(1) option.sel subst\<^sub>E.simps(1)
      by (metis lookupSome.elims)
  qed
  next
  case (Val x)
  then show ?case by simp
next
  case (Exp fn rs) 
    hence [simp]: "(map (ev\<^sub>E t \<circ> (\<lambda>x. subst\<^sub>E x r f)) rs) = 
                      (map (ev\<^sub>E (tree_upd t (top_upd t r (ev\<^sub>E t f)))) rs)"by simp
  show ?case by simp
qed



lemma subst_nop\<^sub>E [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> subst\<^sub>E e r f = e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (\<lambda>x. subst\<^sub>E x r f) rs = rs" by (induct rs) auto
  show ?case by simp
qed auto



(*
lemma ev_nop\<^sub>E [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> ev\<^sub>E (m(r :=\<^sub>s f)) e = ev\<^sub>E m e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E (m(r :=\<^sub>s f))) rs = map (ev\<^sub>E m) rs" by auto
  show ?case by simp
qed auto
*)
lemma ev_nop\<^sub>E [simp]:
 "r \<notin> deps\<^sub>E e  \<Longrightarrow> ev\<^sub>E (tree_upd t (top_upd t r (the f))) e = ev\<^sub>E t e"
proof (induct e)
  case (Var x)
  hence [simp]: " lookup (tree_upd t (top_upd t r (the f))) x = lookup t x" 
    using treeUpd_change by (metis deps\<^sub>E.simps(1) singletonI)           
  then show ?case by auto
next
  case (Val x)
  then show ?case by simp
next
  case (Exp x1a x2a)
  hence [simp]: "map (ev\<^sub>E (tree_upd t (top_upd t r (the f)))) x2a 
                  = (map (ev\<^sub>E t) x2a)" by simp
  then show ?case by auto
qed


lemma deps_subst\<^sub>E [simp]:
  "deps\<^sub>E (subst\<^sub>E e x e') = deps\<^sub>E e - {x} \<union> (if x \<in> deps\<^sub>E e then deps\<^sub>E e' else {})"
  by (induct e; auto simp: if_splits)


(*
lemma deps_ev\<^sub>E [intro]:
  "\<forall>x \<in> deps\<^sub>E e. st m x = st m' x \<Longrightarrow> ev\<^sub>E m e = ev\<^sub>E m' e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E m) rs = map (ev\<^sub>E m') rs" by (induct rs) auto
  show ?case by simp
qed auto
*)
lemma deps_ev\<^sub>E [intro]:
  "\<forall>x \<in> deps\<^sub>E e . lookup t x = lookup t' x \<Longrightarrow> ev\<^sub>E t e = ev\<^sub>E t' e"
proof (induct e)
  case (Var x)
  show ?case using deps\<^sub>E.simps(1) ev\<^sub>E.simps(1) 
  proof -
    obtain r where "r \<in> deps\<^sub>E (Var x)" by simp
    thus ?case using lookup.simps ev\<^sub>E.simps(1) using Var by auto
  qed
  next
  case (Val x)
  then show ?case by auto
next
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E t) rs = map (ev\<^sub>E t') rs" by (induct rs) auto
  show ?case by simp
qed

(*
lemma local_ev\<^sub>E [intro]:
  "deps\<^sub>E e \<subseteq> locals \<Longrightarrow> rg m = rg m' \<Longrightarrow> ev\<^sub>E (Base m) e = ev\<^sub>E (Base m') e"
  apply (intro deps_ev\<^sub>E ballI, case_tac x) 
  by (auto simp: rg_def) metis *)

lemma local_ev\<^sub>E [intro]:
  "deps\<^sub>E e \<subseteq> locals \<Longrightarrow> rg\<^sub>t t = rg\<^sub>t t' \<Longrightarrow> ev\<^sub>E t e = ev\<^sub>E t' e"
  apply (intro deps_ev\<^sub>E lookup.simps ballI, case_tac x) apply auto 
proof (induct t)
  case (Base x)
  then show ?case unfolding lookup.simps(1) rg\<^sub>t_def by metis
next
  case (Branch t1 t2)
  then show ?case using rg\<^sub>t_def by metis 
qed


(*
lemma ev_aux\<^sub>E [simp]:
  "ev\<^sub>E (m(aux: f)) g = ev\<^sub>E m g"
proof (induct g)
  case (Var x)
  then show ?case by (auto simp: aux_upd_def)
next
  case (Val x)
  then show ?case by (auto simp: aux_upd_def)
next
  case (Exp x1a x2a)
  then show ?case by (metis (mono_tags, lifting) ev\<^sub>E.simps(3) map_eq_conv)
qed
*)

lemma help_lookup:
  assumes "lookup (Base s) x = lookup (Base s') x"
  shows "lookup (tree_upd t (Base s)) x = lookup (tree_upd t (Base s')) x"
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


lemma aux_lookup:
 "lookup (tree_upd t (Base (top t\<lparr>more := f (top t)\<rparr>))) x = lookup t x"  
proof -
  have a0:"st (top t\<lparr>more := f (top t)\<rparr>) x = st (top t) x" by simp
  have a1:"lookup (Base (top t\<lparr>more := f (top t)\<rparr>)) x = lookup (Base (top t)) x" 
    using a0 by (metis lookup.simps(1) select_convs(3) surjective update_convs(4))
  have a2:"lookup (tree_upd t(Base (top t\<lparr>more := f (top t)\<rparr>))) x = 
         lookup (tree_upd t (Base (top t))) x" 
    using a1 help_lookup by blast
  then show ?thesis using a0 treeUpd_top by simp
qed

(* if the aux component of top of t is updated, it doesn't have an effect on the evaluation of 
    variable/expression g *)
lemma ev_aux\<^sub>E [simp]:
  "ev\<^sub>E (tree_upd t (top_aux_upd t f)) g = ev\<^sub>E t g"
proof (induct g)
  case (Var x)
  then show ?case by (auto simp: aux_upd_def top_aux_upd_def aux_lookup) 
next
  case (Val x)
  then show ?case by (auto simp: aux_upd_def top_aux_upd_def aux_lookup)
next
  case (Exp x1a x2a)
  then show ?case by (metis (mono_tags, lifting) ev\<^sub>E.simps(3) map_eq_conv)
qed

lemma subst\<^sub>E_flip [simp]:
  "x \<noteq> y \<Longrightarrow> 
       subst\<^sub>E (subst\<^sub>E e x (Val v')) y (Val v) = subst\<^sub>E (subst\<^sub>E e y (Val v)) x (Val v')"
  by (induct e) auto

lemma subst\<^sub>E_rep [simp]:
  "subst\<^sub>E (subst\<^sub>E e x (Val v')) x (Val v) = subst\<^sub>E e x (Val v')"
  by (induct e) auto

lemma finite_deps\<^sub>E [intro]:
  "finite (deps\<^sub>E e)"
  by (induct e) auto

subsection \<open>Boolean Expression\<close>

(*
lemma ev_subst\<^sub>B [simp]:
  "ev\<^sub>B m (subst\<^sub>B b r e) = ev\<^sub>B (m(r :=\<^sub>s (ev\<^sub>E m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r e)) rs = map (ev\<^sub>E (m(r :=\<^sub>s ev\<^sub>E m e))) rs"
    by (auto simp: fun_upd_def)     
  show ?case by simp
qed simp
*)

lemma ev_subst\<^sub>B [simp]:
  "ev\<^sub>B t (subst\<^sub>B b r e) = ev\<^sub>B (tree_upd t (top_upd t r (ev\<^sub>E t e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs) 
   hence [simp]: "map (ev\<^sub>E t \<circ> (\<lambda>x. subst\<^sub>E x r e)) rs
            = map (ev\<^sub>E (tree_upd t (top_upd t r (ev\<^sub>E t e)))) rs" 
      using top_upd_def by auto
  show ?case by simp
qed simp+


(*
lemma ev_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> ev\<^sub>B (m(r :=\<^sub>s f)) b = ev\<^sub>B m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev\<^sub>E (m(r :=\<^sub>s f))) rs = map (ev\<^sub>E m) rs"
    using ev_nop\<^sub>E[of r _ m f] by (auto simp: fun_upd_def) 
  show ?case by simp
qed simp
*)
lemma ev_nop\<^sub>B [simp]:
   "r \<notin> deps\<^sub>B b \<Longrightarrow> ev\<^sub>B (tree_upd t (top_upd t r (the f))) b = ev\<^sub>B t b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev\<^sub>E (tree_upd t (top_upd t r (the f)))) rs = map (ev\<^sub>E t) rs" 
    using top_upd_def by force
  show ?case by auto
qed simp+



lemma subst_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B e \<Longrightarrow> subst\<^sub>B e r f = e"
proof (induct e)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (\<lambda>x. subst\<^sub>E x r f) rs = rs"  by (induct rs) auto
  show ?case by simp
qed auto

lemma deps_subst\<^sub>B [simp]:
  "deps\<^sub>B (subst\<^sub>B e x e') = deps\<^sub>B e - {x} \<union> (if x \<in> deps\<^sub>B e then deps\<^sub>E e' else {})"
  by (induct e; auto simp: if_splits)

(*
lemma deps_ev\<^sub>B [intro]:
  "\<forall>x \<in> deps\<^sub>B e. st m x = st m' x \<Longrightarrow> ev\<^sub>B m e = ev\<^sub>B m' e"
proof (induct e)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev\<^sub>E m) rs = map (ev\<^sub>E m') rs" by (induct rs) auto
  show ?case by simp
qed auto
*)
lemma deps_ev\<^sub>B [intro]:
  "\<forall>x \<in> deps\<^sub>B e. (lookup t) x = (lookup t') x \<Longrightarrow> ev\<^sub>B t e = ev\<^sub>B t' e"
proof (induct e)
  case (Exp\<^sub>B fn rs) 
    hence [simp]: "map (ev\<^sub>E t) rs = map (ev\<^sub>E t') rs" by auto
  show ?case by simp
qed auto


lemma ev_aux\<^sub>B [simp]:
  "ev\<^sub>B (tree_upd t (top_aux_upd t f)) g = ev\<^sub>B t g"
proof (induct g)
  case (Neg g)
  then show ?case by simp
next
  case (Exp\<^sub>B x1a x2)
  then show ?case by (metis (no_types, lifting) ev\<^sub>B.simps(2) ev_aux\<^sub>E map_eq_conv)
qed

lemma subst\<^sub>B_flip [simp]:
  "x \<noteq> y \<Longrightarrow> subst\<^sub>B (subst\<^sub>B e x (Val v')) y (Val v) = subst\<^sub>B (subst\<^sub>B e y (Val v)) x (Val v')"
  by (induct e) auto

lemma subst\<^sub>B_rep [simp]:
  "subst\<^sub>B (subst\<^sub>B e x (Val v')) x (Val v) = subst\<^sub>B e x (Val v')"
  by (induct e) auto

lemma finite_deps\<^sub>B [intro]:
  "finite (deps\<^sub>B e)"
  by (induct e) auto

subsection \<open>Operations\<close>

lemma subst_wr [simp]:
  "wr (subst\<^sub>i \<alpha> x e) = wr \<alpha>"
  by (cases \<alpha>; auto)

lemma subst_rd [simp]:
  "rd (subst\<^sub>i \<alpha> x e) = rd \<alpha> - {x} \<union> (if x \<in> rd \<alpha> then deps\<^sub>E e else {})"
  by (cases \<alpha>; auto)

lemma subst_barriers [simp]:
  "barriers (subst\<^sub>i \<alpha> x e) = barriers \<alpha>"
  by (cases \<alpha>; auto)

lemma subst_not_fence [simp]:
  "(subst\<^sub>i \<alpha> x e \<noteq> full_fence) = (\<alpha> \<noteq> full_fence)"
  by (cases \<alpha>; auto)

lemma subst_nop [simp]:
  "x \<notin> rd \<beta> \<Longrightarrow> subst\<^sub>i \<beta> x e = \<beta>"
  unfolding smap1_def by (cases \<beta>) (auto split: if_splits)

lemma finite_rd [intro]:
  "finite (rd \<alpha>)"
  by (cases \<alpha>) auto

abbreviation ncmp
  where "ncmp b \<equiv> cmp (Neg b)"

subsection \<open>smap1 Theories\<close>

lemma smap1_flip [simp]:
  "smap1 V y (smap1 V x \<alpha>) = smap1 V x (smap1 V y \<alpha>)"
  by (cases \<alpha>; cases "x = y"; auto simp: smap1_def)

lemma smap1_rep [simp]:
  "smap1 V x (smap1 V x \<alpha>) = smap1 V x \<alpha>"
  by (cases \<alpha>; auto simp: smap1_def)

interpretation cfi: comp_fun_idem "smap1 V"  by standard auto

lemma smap1_rd [simp]:
  "rd (smap1 M x \<beta>) = rd \<beta> - ({x} \<inter> dom M)"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_wr [simp]:
  "wr (smap1 M x \<beta>) = wr \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_barriers [simp]:
  "barriers (smap1 M x \<beta>) = barriers \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_nop [simp]:
  "x \<notin> rd \<beta> \<Longrightarrow> smap1 M x \<beta> = \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_nop2 [simp]:
  "M x = None \<Longrightarrow> smap1 M x \<beta> = \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_empty [simp]:
  "smap1 Map.empty x \<beta> = \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_fold_rd [simp]:
  assumes "finite F"
  shows "rd (Finite_Set.fold (smap1 M) \<beta> F) = rd \<beta> - (dom M \<inter> F)"
  using assms
proof (induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "Finite_Set.fold (smap1 M) \<beta> (insert x F) = smap1 M x (Finite_Set.fold (smap1 M) \<beta> F)"
    using cfi.fold_insert_idem by blast
  then show ?case by (auto simp: insert(3))
qed

lemma smap1_fold_wr [simp]:
  assumes "finite F"
  shows "wr (Finite_Set.fold (smap1 M) \<beta> F) = wr \<beta>"
  using assms
proof (induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "Finite_Set.fold (smap1 M) \<beta> (insert x F) = smap1 M x (Finite_Set.fold (smap1 M) \<beta> F)"
    using cfi.fold_insert_idem by blast
  then show ?case by (auto simp: insert(3))
qed

lemma smap1_fold_barriers [simp]:
  assumes "finite F"
  shows "barriers (Finite_Set.fold (smap1 M) \<beta> F) = barriers \<beta>"
  using assms
proof (induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "Finite_Set.fold (smap1 M) \<beta> (insert x F) = smap1 M x (Finite_Set.fold (smap1 M) \<beta> F)"
    using cfi.fold_insert_idem by blast
  then show ?case by (auto simp: insert(3))
qed

lemma smap1_fold_empty:
  assumes "finite F"
  shows "Finite_Set.fold (smap1 Map.empty) \<alpha> F = \<alpha>"
  using assms
proof (induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "Finite_Set.fold (smap1 Map.empty) \<alpha> (insert x F) = 
         smap1 Map.empty x (Finite_Set.fold (smap1 Map.empty) \<alpha> F)"
    using cfi.fold_insert_idem by blast
  also have "... = Finite_Set.fold (smap1 Map.empty) \<alpha> F" by auto
  also have "... = \<alpha>" using insert(3) by blast
  finally show ?case .
qed

subsection \<open>smap Theories\<close>

lemma smap_rd [simp]:
  "rd (smap \<beta> M) = rd \<beta> - dom M"
proof -
  have "finite (rd \<beta>)" by auto
  thus ?thesis unfolding smap_def by auto
qed

lemma smap_wr [simp]:
  "wr (smap \<beta> M) = wr \<beta>"
proof -
  have "finite (rd \<beta>)" by auto
  thus ?thesis unfolding smap_def by auto
qed

lemma smap_barriers [simp]:
  "barriers (smap \<beta> M) = barriers \<beta>"
proof -
  have "finite (rd \<beta>)" by auto
  thus ?thesis unfolding smap_def by auto
qed

lemma smap_empty [simp]:
  "smap \<beta> Map.empty = \<beta>"
proof -
  have "finite (rd \<beta>)" by auto
  thus ?thesis using smap1_fold_empty unfolding smap_def by auto
qed

lemma smap_rep [simp]:
  "smap1 M x (smap \<beta> M) = smap \<beta> M"
proof (cases "x \<in> rd \<beta>")
  case True
  have "Finite_Set.fold (smap1 M) \<beta> (insert x (rd \<beta>)) =
        smap1 M x (Finite_Set.fold (smap1 M) \<beta> (rd \<beta>))"
    using cfi.fold_insert_idem by blast
  moreover have "insert x (rd \<beta>) = rd \<beta>" using True by auto
  ultimately show ?thesis unfolding smap_def by auto
next
  case False
  thus ?thesis by simp
qed

subsection \<open>forall Theories\<close>

lemma forall_rd [simp]:
  "\<forall>\<alpha> \<in> forall V \<beta>. rd \<alpha> = rd \<beta> - V"
  unfolding forall_def by auto

lemma forall_wr [simp]:
  "\<forall>\<alpha> \<in> forall V \<beta>. wr \<alpha> = wr \<beta>"
  unfolding forall_def by auto

lemma forall_barriers [simp]:
  "\<forall>\<alpha> \<in> forall V \<beta>. barriers \<alpha> = barriers \<beta>"
  unfolding forall_def by auto

lemma forall_fence [simp]:
  "\<forall>\<alpha> \<in> forall V \<beta>.  (\<alpha> \<noteq> full_fence) = (\<beta> \<noteq> full_fence)"
proof -
  have "\<forall>\<alpha>. barriers \<alpha> = (\<alpha> = full_fence)" by (intro allI, case_tac \<alpha>; auto)
  thus ?thesis using forall_barriers by blast
qed

lemma forall_nil [simp]:
  "forall {} \<alpha> = {\<alpha>}"
  unfolding forall_def by auto

lemma smap1_cong [intro]:
  "M x = N x \<Longrightarrow> smap1 M x = smap1 N x"
  unfolding smap1_def using domIff by fastforce

lemma
  "comp_fun_commute_on (rd \<alpha>) (smap1 (\<lambda>y. if x = y then None else M y))"
  by (rule Finite_Set.comp_fun_commute_on.intro) auto

lemma
  "comp_fun_commute_on (rd \<alpha>) (smap1 (\<lambda>y. if x = y then None else M y))"
  by (rule Finite_Set.comp_fun_commute_on.intro) auto
  
lemma forall_unfold:
  shows "forall (insert x V) \<alpha> = {subst\<^sub>i \<alpha>' x (Val c) | c \<alpha>'. \<alpha>' \<in> forall V \<alpha>}" (is "?L = ?R")
proof -
  have "?L \<subseteq> ?R"
  proof (clarsimp simp: forall_def, cases "x \<in> V")
    fix M assume d: "dom (M :: ('b, 'c) SimAsm_State.var \<Rightarrow> 'a option) = insert x V" "x \<in> V"
    hence "smap \<alpha> M = subst\<^sub>i (smap \<alpha> M) x (Val (the (M x)))" by simp
    moreover have "dom M = V" using d by auto
    ultimately show "\<exists>c \<alpha>'. smap \<alpha> M = subst\<^sub>i \<alpha>' x (Val c) \<and> (\<exists>M. \<alpha>' = smap \<alpha> M \<and> dom M = V)"
      by blast
  next
    fix M assume d: "dom (M :: ('b, 'c) SimAsm_State.var \<Rightarrow> 'a option) = insert x V" "x \<notin> V"
    let ?M = "\<lambda>y. if x = y then None else M y"
    have "smap \<alpha> M = subst\<^sub>i (smap \<alpha> ?M) x (Val (the (M x)))"
    proof -
      have 
        "comp_fun_commute_on (rd \<alpha>) (smap1 M)" 
        "comp_fun_commute_on (rd \<alpha>) (smap1 (\<lambda>y. if x = y then None else M y))"
        by standard auto
      hence mx: "Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}) = Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x})"
        by (auto intro!: Finite_Set.fold_cong simp add: cfi.comp_fun_commute_axioms)
      show ?thesis
      proof (cases "x \<in> rd \<alpha>")
        case True
        hence [simp]: "insert x (rd \<alpha>) = rd \<alpha>" by auto
        have fx: "Finite_Set.fold (smap1 M) \<alpha> (insert x (rd \<alpha>)) = 
                  smap1 M x (Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}))"
          by (rule cfi.fold_insert_remove) blast
        have "Finite_Set.fold (smap1 ?M) \<alpha> (insert x (rd \<alpha>)) = 
                  smap1 ?M x (Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x}))"
          by (rule cfi.fold_insert_remove) blast
        also have "... = Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x})" by auto
        finally show ?thesis using fx mx unfolding smap_def apply simp
          unfolding smap1_def using d(1) by (auto split: if_splits)
      next
        case False
        hence [simp]: "rd \<alpha> - {x} = rd \<alpha>" by auto
        have "x \<notin> rd (smap \<alpha> ?M)" using False by simp
        then show ?thesis using mx unfolding smap_def by simp
      qed
    qed
    moreover have "dom ?M = V" using d by (auto split: if_splits)
    ultimately show "\<exists>c \<alpha>'. smap \<alpha> M = subst\<^sub>i \<alpha>' x (Val c) \<and> (\<exists>M. \<alpha>' = smap \<alpha> M \<and> dom M = V)"
      by blast
  qed

  moreover have "?R \<subseteq> ?L"
  proof (clarsimp simp: forall_def, cases "x \<in> V")
    fix M c assume d: "V = dom (M :: ('b, 'c) SimAsm_State.var \<Rightarrow> 'a option)" "x \<in> V" 
    have "dom M = insert x (dom M)" using d by auto
    moreover have "subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> M" using d by simp
    ultimately show "\<exists>Ma. subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> Ma \<and> dom Ma = insert x (dom M)"
      by blast
  next
    fix M c assume d: "V = dom (M :: ('b, 'c) SimAsm_State.var \<Rightarrow> 'a option)" "x \<notin> V" 
    let ?M = "\<lambda>y. if y = x then Some c else M y"
    have "dom ?M = insert x (dom M)" using d by auto
    moreover have "subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> ?M"
    proof -
      have 
        "comp_fun_commute_on (rd \<alpha>) (smap1 M)" 
        "comp_fun_commute_on (rd \<alpha>) (smap1 (\<lambda>y. if y = x then Some c else M y))"
        by standard auto
      hence mx: "Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}) = Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x})"
        by (auto intro!: Finite_Set.fold_cong simp add: cfi.comp_fun_commute_axioms)
      show ?thesis
      proof (cases "x \<in> rd \<alpha>")
        case True
        hence [simp]: "insert x (rd \<alpha>) = rd \<alpha>" by auto
        have fx: "Finite_Set.fold (smap1 ?M) \<alpha> (insert x (rd \<alpha>)) = 
                  smap1 ?M x (Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x}))"
          by (rule cfi.fold_insert_remove) blast
        have "Finite_Set.fold (smap1 M) \<alpha> (insert x (rd \<alpha>)) = 
                  smap1 M x (Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}))"
          by (rule cfi.fold_insert_remove) blast
        also have "... = Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x})" using d by auto        
        finally show ?thesis using fx mx unfolding smap_def apply simp
          unfolding smap1_def using d(1) by (auto split: if_splits)
      next
        case False
        hence [simp]: "rd \<alpha> - {x} = rd \<alpha>" by auto
        have "x \<notin> rd (smap \<alpha> ?M)" using False by simp
        then show ?thesis using mx unfolding smap_def by simp
      qed
    qed
    ultimately show "\<exists>Ma. subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> Ma \<and> dom Ma = insert x (dom M)"
      by blast
  qed

  ultimately show ?thesis by blast
qed

lemma forall_one [simp]:
  "forall {x} \<alpha> = {subst\<^sub>i \<alpha> x (Val c) | c. True}"
  unfolding forall_unfold[of x "{}" \<alpha>] by auto

lemma forall_nop [simp]:
  assumes "x \<notin> rd \<alpha>" 
  shows "forall (insert x V) \<alpha> = forall V \<alpha>"
  using assms forall_unfold by force

lemma forallI [intro]:
  "smap \<alpha> M \<in> forall (dom M) \<alpha>"
  by (auto simp: forall_def)

subsection \<open>TODO\<close>


definition upd                   (* use if f is a total fun: 'a \<Rightarrow> 'v *)
  where "upd S f m \<equiv> m\<lparr>st := \<lambda>x. if x \<in> S then Some (f x) else st m x\<rparr>"

definition upd_part       (* use if f is a partial fun: 'a \<Rightarrow> 'v option *)
  where "upd_part S f m \<equiv> m\<lparr>st := \<lambda>x. if x \<in> S then (f x) else st m x\<rparr>"

lemma upd_nil [simp]:
  "upd {} f m = m"
  by (auto simp: upd_def)

lemma upd_insert [simp]:
  "upd (insert x V) f m = (upd V f m)(x :=\<^sub>s f x)"
  by (auto simp: upd_def st_upd_def intro!: state_rec.equality)

(*
lemma upd_rep [simp]:
  "upd A (st (upd A f m\<^sub>1)) m\<^sub>2 = upd A f m\<^sub>2"
  by (auto simp: upd_def intro!: state_rec.equality)
*)

lemma upd_rep [simp]:
  "upd_part A (st (upd A f m\<^sub>1)) m\<^sub>2 = upd A f m\<^sub>2"
  by (auto simp: upd_part_def upd_def intro!: state_rec.equality)

lemma upd_rep' [simp]:
  "upd A f (upd B f m) = upd (A \<union> B) f m"
  by (auto simp: upd_def intro!: state_rec.equality)

lemma upd_st [simp]:
  "st (upd S f m) x = (if x \<in> S then Some (f x) else st m x)"
  by (auto simp: upd_def)

lemma upd_more [simp]:
  "state_rec.more (upd V f m) = state_rec.more m"
  by (auto simp: upd_def)

lemma upd_cap [simp]:
  "state_rec.cap (upd V f m) = state_rec.cap m"
  by (auto simp: upd_def)

(* new: same updates on trees *)  

definition updTree         (* assume total fun f : 'a \<longrightarrow> 'v *)
  where "updTree S f t \<equiv> 
           tree_upd t (Base ((top t)\<lparr>st := \<lambda>x. if x \<in> S then Some (f x) else st (top t) x\<rparr>))" 

definition updTree_part      (* assume partial fun f : 'a \<rightarrow> 'v option ; like st *)
  where "updTree_part S f t \<equiv> 
           tree_upd t (Base ((top t)\<lparr>st := \<lambda>x. if x \<in> S then (f x) else st (top t) x\<rparr>))" 

lemma updTree_nil [simp]:
  "updTree {} f t = t"
  by (auto simp: updTree_def) 

lemma updTree_insert [simp]:
  "updTree (insert x V) f t = tree_upd t (Base ((top (updTree V f t)) (x :=\<^sub>s (f x))))"
  (*  apply (auto simp: updTree_def st_upd_def intro!: state_rec.equality) *)
proof -
  let ?f1 = "(\<lambda>xa. if xa = x \<or> xa \<in> V then Some (f xa) else (st (top t) xa))"
  let ?f2 = "(\<lambda>x. if            x \<in> V then Some (f x) else st (top t) x)(x \<mapsto> (f x))"
  have a0:"?f1 = ?f2" using st_upd_def by fastforce
  hence a1:"Base (top t\<lparr>st := ?f1\<rparr>) = Base (top t\<lparr>st := ?f2\<rparr>)" by simp
  hence a2:"tree_upd t (Base (top t\<lparr>st := ?f1\<rparr>)) = tree_upd t(Base (top t\<lparr>st := ?f2\<rparr>))" by simp
  have a3:"tree_upd t(Base (top t\<lparr>st := ?f2\<rparr>)) = 
         tree_upd t (Base ((top (updTree V f t))(x :=\<^sub>s (f x))))" using a2 
    by (auto simp: updTree_def st_upd_def intro!: state_rec.equality) 
  have a4:"tree_upd t (Base (top t\<lparr>st := ?f1\<rparr>)) = updTree (insert x V) f t"
    by (auto simp: updTree_def st_upd_def upd_def intro!: state_rec.equality)   
  have a5:"updTree (insert x V) f t = tree_upd t (Base ((top (updTree V f t))(x :=\<^sub>s (f x))))"
    using a3 a4 a2 by simp
  thus ?thesis by simp
qed


lemma st_upd_eq [intro]:
  "state_rec.more m = state_rec.more m' \<Longrightarrow> 
              state_rec.cap m = state_rec.cap m' \<Longrightarrow>
                 initState m = initState m' \<Longrightarrow>
                    \<forall>x. x \<noteq> y \<longrightarrow> st m x = st m' x \<Longrightarrow> m(y :=\<^sub>s e) = m'(y :=\<^sub>s e)"
  by (auto simp: upd_def st_upd_def intro!: state_rec.equality)

lemma updTree_rep [simp]:
  "updTree_part A (st (upd_part A f m\<^sub>1)) t\<^sub>2 = updTree_part A f t\<^sub>2"
(*  apply (auto simp: updTree_opt_def intro!: state_rec.equality) *)
proof -
  let ?f1 = "\<lambda>x. if x \<in> A then (st (upd_part A f m\<^sub>1) x) else st (top t\<^sub>2) x"
  let ?f2 = "\<lambda>x. if x \<in> A then (f x) else st (top t\<^sub>2) x"
  have a0:"x \<in> A \<Longrightarrow> (st (upd_part A f m\<^sub>1) x = f x)" using upd_part_def
    by (smt (verit, best) select_convs(1) surjective update_convs(1))
  then have "(\<lambda>x. if x \<in> A then (st (upd_part A f m\<^sub>1) x) else st (top t\<^sub>2) x) =
             (\<lambda>x. if x \<in> A then (f x)                   else st (top t\<^sub>2) x)" sorry 
  then have "?f1 = ?f2" by simp
  then have 
  "tree_upd t\<^sub>2
     (Base (top t\<^sub>2 \<lparr>st := \<lambda>x. if x \<in> A then (st (upd_part A f m\<^sub>1) x) else st (top t\<^sub>2) x\<rparr>)) =
  tree_upd t\<^sub>2
     (Base (top t\<^sub>2\<lparr>st := \<lambda>x. if x \<in> A then (f x) else st (top t\<^sub>2) x\<rparr>))" 
    by simp
  then show ?thesis by (auto simp: updTree_part_def intro!: state_rec.equality)
qed


lemma [simp]:
  "rg (upd_part V f m) x = (if Reg x \<in> V then f (Reg x) else rg m x)"
  unfolding rg_def upd_part_def
  by simp

lemma [simp]:
  "rg (m(aux: f)) = rg m"
  unfolding rg_def aux_upd_def by simp


(*
lemma beh_substi [simp]:
  "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) | m m\<^sub>1. (m\<^sub>1(x :=\<^sub>s (ev\<^sub>E m\<^sub>1 e)),m) \<in> beh\<^sub>i \<alpha>}"
  apply (cases \<alpha>)
  defer 1
  apply (clarsimp simp: upd_def)
  apply blast
  apply (clarsimp simp: upd_def)
  apply blast
  apply (clarsimp simp: upd_def)
  apply blast
  apply (clarsimp simp: upd_def st_upd_def)
  apply auto
  apply (rule state_rec.equality)
  apply auto
  apply (rule state_rec.equality)
  apply auto
  done
*)

lemma eq_comm:
  "(a \<Longrightarrow> (b = c)) \<Longrightarrow> (a \<Longrightarrow> (c = b))" by blast


thm state_rec.equality

lemma beh_substi [simp]:
  "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = 
          {(m\<^sub>1,upd_part (wr \<alpha>) (st m) m\<^sub>1) | m m\<^sub>1. (m\<^sub>1(x :=\<^sub>s (ev\<^sub>E (Base m\<^sub>1) e)),m) \<in> beh\<^sub>i \<alpha>}"
  apply (cases \<alpha>)
  defer 1
  apply (clarsimp simp: upd_part_def top_upd_def) 
  apply blast
  apply (clarsimp simp: upd_part_def)
  apply blast
  apply (clarsimp simp: upd_part_def)
  apply blast
  apply (clarsimp simp: upd_part_def st_upd_def)
  apply auto     
  apply (rule state_rec.equality)
      apply (auto simp: top_upd_def) 
   using fun_upd_other fun_upd_same select_convs(1) st_upd_def surjective update_convs(1) 
   apply (metis (no_types, lifting))
  apply (rule state_rec.equality)
      apply (auto simp: top_upd_def)
   apply (rule eq_comm)
   apply auto
   using fun_upd_other fun_upd_same select_convs(1) st_upd_def surjective update_convs(1) 
by (metis (no_types, lifting))
 
   

lemma behTree_substi [simp]:
  "behTree\<^sub>i (subst\<^sub>i \<alpha> x e) = {(t,t')| t t' m m'. (m,m') \<in> beh\<^sub>i(subst\<^sub>i \<alpha> x e) \<and> 
                                            top t = m \<and> t'=tree_upd t (Base m')}"
  using beh_substi by simp



(*todo *)


lemma [simp]:
  "st (m(x :=\<^sub>s e)) = (st m)(x := Some e)"
  by (auto simp: st_upd_def)

lemma [simp]:
  "Base (st (m(x :=\<^sub>s e))) = Base ((st m)(x := Some e))"
  by (auto simp: st_upd_def)

(* 
lemma beh_smap1 [simp]:
  "beh\<^sub>i (smap1 M x \<alpha>) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1.(upd ({x} \<inter> dom M) (the o M) m\<^sub>1,m) \<in> beh\<^sub>i \<alpha>}"
by (cases \<alpha> ; auto simp: smap1_def) 
*)



lemma state_simp:
  assumes "m2 = m1\<lparr>st := \<lambda>xa. if xa = x \<and> xa \<in> dom M then M xa else st m1 xa\<rparr>"
          "t = (Base (m2))"
  shows "st (m1 (x :=\<^sub>s ev\<^sub>E t y)) =
         st (m1 \<lparr>st := \<lambda>xa. if xa = x then st ( m2 (x :=\<^sub>s ev\<^sub>E t y)) xa else st m1 xa\<rparr>)"
  sorry


lemma beh_smap1 [simp]:
  "beh\<^sub>i (smap1 M x \<alpha>) = {(m\<^sub>1,upd_part (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1.(upd_part ({x} \<inter> dom M) (M) m\<^sub>1,m) \<in> beh\<^sub>i \<alpha>}"
  apply (cases \<alpha> ; auto simp: smap1_def upd_part_def) 
         apply (rule state_rec.equality)
  


(*          apply (auto simp: top_upd_def)
        apply (clarsimp simp: upd_def upd_part_def st_upd_def)
        defer 1
  apply (simp add: st_upd_def)+
         defer 3
         apply (smt (verit, best) deps_ev\<^sub>B domIff ext_inject 
              fun_upd_other fun_upd_same lookup.simps(1) not_None_eq st_upd_def surjective update_convs(1))
*)  
  
   
       
  sorry


lemma behTree_smap1 [simp]:
  "behTree\<^sub>i (smap1 M x \<alpha>) = {(m\<^sub>1,updTree (wr \<alpha>) (lookupSome m) m\<^sub>1) |m m\<^sub>1. 
                               (updTree ({x} \<inter> dom M) (the o M) m\<^sub>1,m) \<in> behTree\<^sub>i \<alpha>}"
proof (cases \<alpha>)
  case (assign x11 x12)
  then show ?thesis sorry
next
  case (cmp x2)
  then show ?thesis using smap1_def sorry
qed auto


lemma beh_fold_smap1:
  assumes "finite F" 
  shows "beh\<^sub>i (Finite_Set.fold (smap1 M) \<alpha> F) = {(m\<^sub>1, upd_part (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd (F \<inter> dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
  using assms
proof (induct)
  case empty
  then show ?case apply (cases \<alpha> ; auto) sorry
next
  case (insert x F)
  hence f: "Finite_Set.fold (smap1 M) \<alpha> (insert x F) = 
         smap1 M x (Finite_Set.fold (smap1 M) \<alpha> F)"
    using cfi.fold_insert_idem by blast

  show ?case using insert(1)
    unfolding f beh_smap1 insert(3)
    apply auto unfolding o_def 
    apply (intro exI conjI)
    apply blast
    sorry
(*  
  apply (metis Int_Un_distrib2 Un_insert_right inf_bot_right sup_inf_absorb)
    apply (intro exI conjI)
    prefer 2
    apply blast
    apply simp
    apply (metis Int_Un_distrib2 Un_insert_right inf_bot_right sup_inf_absorb)
    done
*)
qed


lemma beh_smap [simp]:
  "beh\<^sub>i (smap \<alpha> M) = {(m\<^sub>1,upd_part (wr \<alpha>) (st m) m\<^sub>1) | m m\<^sub>1. (upd (dom M) (the o M) m\<^sub>1,m) \<in> beh\<^sub>i \<alpha>}"
proof -
  have "finite (rd \<alpha>)" by auto
  hence "beh\<^sub>i (Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha>)) = 
          {(m\<^sub>1, upd_part (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd ((rd \<alpha>) \<inter> dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
    using beh_fold_smap1 by blast

  also have "... = {(m\<^sub>1, upd_part (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd (dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
    apply (cases \<alpha>; auto)
(*
             apply (rule equality; auto)
    apply fastforce
    apply (rule equality; auto)
    apply fastforce
    apply (subgoal_tac "ev\<^sub>B (upd (deps\<^sub>B x2 \<inter> dom M) (the \<circ> M) m\<^sub>1) x2 = ev\<^sub>B (upd (dom M) (the \<circ> M) m\<^sub>1) x2")
    apply blast
    apply (rule deps_ev\<^sub>B)
    apply auto
    apply (subgoal_tac "ev\<^sub>B (upd (deps\<^sub>B x2 \<inter> dom M) (the \<circ> M) m\<^sub>1) x2 = ev\<^sub>B (upd (dom M) (the \<circ> M) m\<^sub>1) x2")
    apply blast
    apply (rule deps_ev\<^sub>B)
    apply auto
    done
*) sorry
  finally show ?thesis unfolding smap_def .
qed

end