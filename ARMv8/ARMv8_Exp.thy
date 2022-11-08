theory ARMv8_Exp
  imports ARMv8_State
begin


section \<open>Expression Language\<close>

datatype ('v,'r) exp = 
  Var 'r | 
  Val 'v | 
  Exp "'v option list \<Rightarrow> 'v option" "('v,'r) exp list"  (* some fct over a list of subexpr *) 


text \<open>Evaluate an expression given a state tree, such that variable values are looked up in the 
          innermost scope in which a value is mapped to variable \<close>
fun ev\<^sub>E :: "('v,'r,'a) stateTree \<Rightarrow> ('v,'r) exp \<Rightarrow> 'v option"
  where 
    "ev\<^sub>E m (Var r) = lookup m (Reg r)" |
    "ev\<^sub>E _ (Val v) = Some v" |
    "ev\<^sub>E m (Exp f rs) = f (map (ev\<^sub>E m) rs)"  (* eg, Exp(+ a1 a2 a3) = (ev a1) + (ev a2) + (ev a3) *)

text \<open>The syntactic dependencies of an expression\<close>
fun deps\<^sub>E :: "('v,'r) exp \<Rightarrow> 'r set"
  where 
    "deps\<^sub>E (Var r) = {r}" |
    "deps\<^sub>E (Exp _ rs) = \<Union>(deps\<^sub>E ` set rs)" |
    "deps\<^sub>E _ = {}"

text \<open>Substitute a variable for an expression\<close>
fun subst\<^sub>E :: "('v,'r) exp \<Rightarrow> 'r \<Rightarrow> ('v,'r) exp \<Rightarrow> ('v,'r) exp"
  where
    "subst\<^sub>E (Var r) r' e = (if r = r' then e else Var r)" |
    "subst\<^sub>E (Exp f rs) r e = (Exp f (map (\<lambda>x. subst\<^sub>E x r e) rs))" |
    "subst\<^sub>E e _ _ = e"

datatype ('v,'r) bexp = True\<^sub>B | Neg "('v,'r) bexp" | 
                        Exp\<^sub>B "'v option list \<Rightarrow> bool" "('v,'r) exp list"

text \<open>Evaluate an expression given a state tree, such that variable values are looked up in the
        innermost scope in which a value exists \<close>
fun ev\<^sub>B :: "('v,'r,'a) stateTree \<Rightarrow> ('v,'r) bexp \<Rightarrow> bool"
  where 
    "ev\<^sub>B m (True\<^sub>B) = True" |
    "ev\<^sub>B m (Neg e) = (\<not> (ev\<^sub>B m e))" |
    "ev\<^sub>B m (Exp\<^sub>B f rs) = f (map (ev\<^sub>E m) rs)"

text \<open>The syntactic dependencies of an expression\<close>
fun deps\<^sub>B :: "('v,'r) bexp \<Rightarrow> 'r set"
  where 
    "deps\<^sub>B (True\<^sub>B) = {}" |
    "deps\<^sub>B (Neg e) = deps\<^sub>B e" |
    "deps\<^sub>B (Exp\<^sub>B _ rs) = \<Union>(deps\<^sub>E ` set rs)"

text \<open>Substitute a variable for an expression\<close>
fun subst\<^sub>B :: "('v,'r) bexp \<Rightarrow> 'r \<Rightarrow> ('v,'r) exp \<Rightarrow> ('v,'r) bexp"
  where
    "subst\<^sub>B (Neg b) r e = Neg (subst\<^sub>B b r e)" |
    "subst\<^sub>B (Exp\<^sub>B f rs) r e = (Exp\<^sub>B f (map (\<lambda>x. subst\<^sub>E x r e) rs))" |
    "subst\<^sub>B b _ _ = b"

section \<open>Sub-operations\<close>

text \<open>
To model the possible reordering behaviour seen in ARMv8, it is necessary
to model each operation as a series of sub-operations.
For example a load would consist of an operation that first determines the memory address
to access, followed by the memory access, followed by a store to a register.

Updating the cache is also a sub-operation
\<close>
datatype ('v,'r) subop =
    load 'v "('v,'r) exp"
  | cstore "('v,'r) bexp"  'v "('v,'r) exp"
  | cas\<^sub>T 'v "('v,'r) exp" "('v,'r) exp"
  | cas\<^sub>F 'v "('v,'r) exp"
  | op 'r "('v,'r) exp"
  | cmp "('v,'r) bexp"
  | fence
  | cfence
  | stfence
  | nop
  | cacheUpd 'r 'v   (* 'r is cache variable, 'v is the address to be added to cache *)

text \<open>Common Sub-Instructions\<close>
abbreviation assign
  where "assign r v \<equiv> op r (Exp (\<lambda>x. v) [])"

abbreviation ncmp
  where "ncmp b \<equiv> cmp (Neg b)"

abbreviation eq
  where "eq e\<^sub>1 e\<^sub>2 \<equiv> cmp (Exp\<^sub>B (\<lambda>x. x ! 0 = x ! 1) [e\<^sub>1,e\<^sub>2])"

abbreviation neq
  where "neq e\<^sub>1 e\<^sub>2 \<equiv> cmp (Exp\<^sub>B (\<lambda>x. x ! 0 \<noteq> x ! 1) [e\<^sub>1,e\<^sub>2])"

abbreviation rubbish
  where "rubbish v e\<^sub>1 e\<^sub>2 e\<^sub>3 \<equiv> cstore (Exp\<^sub>B (\<lambda>x. x ! 0 = x ! 1) [e\<^sub>1,e\<^sub>3]) v e\<^sub>2"


text \<open>Sub-operation execution behaviour\<close>
fun beh\<^sub>i :: "('v,'r,'a) stateTree \<Rightarrow> ('v,'r) subop \<Rightarrow> ('v,'r,'a) state rel"
  where
    "beh\<^sub>i t (cstore b a e) = {(m,m'). m=(top t) \<and> ev\<^sub>B t b \<and> m' = m (Glb a :=\<^sub>s ev\<^sub>E t e)}" | 
    "beh\<^sub>i t (load a e) = {(m,m'). m=(top t) \<and> m' = m \<and> st m (Glb a) = ev\<^sub>E t e}" |
    "beh\<^sub>i t (cas\<^sub>T a e\<^sub>1 e\<^sub>2) = {(m,m'). m=(top t) \<and> m' = m (Glb a :=\<^sub>s ev\<^sub>E t e\<^sub>2) \<and> st m (Glb a) = ev\<^sub>E t e\<^sub>1}" |
    "beh\<^sub>i t (cas\<^sub>F a e\<^sub>1) = {(m,m'). m=(top t) \<and> m' = m \<and> st m (Glb a) \<noteq> ev\<^sub>E t e\<^sub>1}" |
    "beh\<^sub>i t (op r e) = {(m,m'). m=(top t) \<and> m' = m (Reg r :=\<^sub>s ev\<^sub>E t e)}" |
    "beh\<^sub>i t (cmp b) = {(m,m'). m=(top t) \<and> m = m' \<and> ev\<^sub>B t b}" |
    "beh\<^sub>i t (cacheUpd c g) = {(m,m'). m = (base t) \<and> m' = st_upd m (Reg c) (Some g) }" | (* fix me *)
    "beh\<^sub>i _ _ = Id" 

text \<open>Variables modified by an operation, except cache variable \<close>
fun wr :: "('v,'r) subop \<Rightarrow> ('v,'r) var set"
  where 
    "wr (cstore _ y _) = {Glb y}" |
    "wr (op y _) = {Reg y}" |
    "wr (cas\<^sub>T y _ _) = {Glb y}" |
    "wr _ = {}"

text \<open>Variables that influence an operation\<close>
fun rd :: "('v,'r) subop \<Rightarrow> ('v,'r) var set"
  where
    "rd (load y e) = {Glb y} \<union> Reg ` deps\<^sub>E e" |
    "rd (cas\<^sub>T y e\<^sub>1 e\<^sub>2) = {Glb y} \<union> Reg ` deps\<^sub>E e\<^sub>1 \<union> Reg ` deps\<^sub>E e\<^sub>2" |
    "rd (cas\<^sub>F y e\<^sub>1) = {Glb y} \<union> Reg ` deps\<^sub>E e\<^sub>1" |
    "rd (op _ e) = Reg ` deps\<^sub>E e" |
    "rd (cstore b _ e) = Reg ` deps\<^sub>E e \<union> Reg ` deps\<^sub>B b" |
    "rd (cmp b) = Reg ` deps\<^sub>B b" |
    "rd _ = {}"

text \<open>Test if an instruction is a memory barrier\<close>
fun barriers :: "('v,'r) subop \<Rightarrow> ('v,'r) subop set"
  where 
    "barriers fence = {fence}" | 
    "barriers stfence = {stfence}" |
    "barriers cfence = {cfence}" |
    "barriers _ = {}"

text \<open>Operation Substitution\<close>
fun subst\<^sub>r :: "('v,'r) subop \<Rightarrow> 'r \<Rightarrow> ('v,'r) exp \<Rightarrow> ('v,'r) subop"
  where
    "subst\<^sub>r (load v\<^sub>a e\<^sub>a) r e\<^sub>b = (load v\<^sub>a (subst\<^sub>E e\<^sub>a r e\<^sub>b))" |
    "subst\<^sub>r (cstore b v\<^sub>a e\<^sub>a) r e\<^sub>b = (cstore (subst\<^sub>B b r e\<^sub>b) v\<^sub>a (subst\<^sub>E e\<^sub>a r e\<^sub>b))" |
    "subst\<^sub>r (op v\<^sub>a e\<^sub>a) r e\<^sub>b = (op v\<^sub>a (subst\<^sub>E e\<^sub>a r e\<^sub>b))" |
    "subst\<^sub>r (cmp b) r e\<^sub>b = (cmp (subst\<^sub>B b  r e\<^sub>b))" |
    "subst\<^sub>r (cas\<^sub>T v\<^sub>a e\<^sub>1 e\<^sub>2) r e\<^sub>b = (cas\<^sub>T v\<^sub>a (subst\<^sub>E e\<^sub>1 r e\<^sub>b) (subst\<^sub>E e\<^sub>2 r e\<^sub>b))" |
    "subst\<^sub>r (cas\<^sub>F v\<^sub>a e\<^sub>1) r e\<^sub>b = (cas\<^sub>F v\<^sub>a (subst\<^sub>E e\<^sub>1 r e\<^sub>b))" |
    "subst\<^sub>r \<alpha> _ _ = \<alpha>"

fun subst\<^sub>g :: "('v,'r) subop \<Rightarrow> 'v \<Rightarrow> ('v,'r) exp \<Rightarrow> ('v,'r) subop"
  where
    "subst\<^sub>g (load v\<^sub>a e\<^sub>a) v\<^sub>b e\<^sub>b = (if v\<^sub>a = v\<^sub>b then eq e\<^sub>a e\<^sub>b else load v\<^sub>a e\<^sub>a)" |
    "subst\<^sub>g (cas\<^sub>F v\<^sub>a e\<^sub>a) v\<^sub>b e\<^sub>b = (if v\<^sub>a = v\<^sub>b then neq e\<^sub>a e\<^sub>b else cas\<^sub>F v\<^sub>a e\<^sub>a)" |
    "subst\<^sub>g (cas\<^sub>T v\<^sub>a e\<^sub>1 e\<^sub>2) v\<^sub>b e\<^sub>b = (if v\<^sub>a = v\<^sub>b then rubbish v\<^sub>a e\<^sub>1 e\<^sub>2 e\<^sub>b else cas\<^sub>T v\<^sub>a e\<^sub>1 e\<^sub>2)" |
    "subst\<^sub>g \<alpha> _ _ = \<alpha>"

fun subst\<^sub>i :: "('v,'r) subop \<Rightarrow> ('v,'r) var \<Rightarrow> ('v,'r) exp \<Rightarrow> ('v,'r) subop"
  where
    "subst\<^sub>i i (Reg r) e = subst\<^sub>r i r e" |
    "subst\<^sub>i i (Glb g) e = subst\<^sub>g i g e" |
    "subst\<^sub>i i (Tmp r) e = subst\<^sub>r i r e" 
    

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
  "ev\<^sub>E m (subst\<^sub>E e r f) = ev\<^sub>E (m (r := (ev\<^sub>E m f))) e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r f)) rs = map (ev\<^sub>E (\<lambda>a. if a = r then ev\<^sub>E m f else m a)) rs"
    by auto
  show ?case by simp
qed auto
*)

fun top_upd :: "('v,'r,'a) stateTree \<Rightarrow> 'r \<Rightarrow> 'v option \<Rightarrow> ('v,'r,'a) stateTree" where
  "top_upd t r val = Base (st_upd (top t) (Reg r) val)"

lemma ev_subst\<^sub>E [simp]:
  "ev\<^sub>E t (subst\<^sub>E e r f) = ev\<^sub>E (top_upd t r (ev\<^sub>E t f)) e"
proof (induct e)
  case (Var x)
  then show ?case sorry
next
  case (Val x)
  then show ?case sorry
next
  case (Exp x1a x2a)
  then show ?case sorry
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
  "r \<notin> deps\<^sub>E e \<Longrightarrow> ev\<^sub>E (m(r := f)) e = ev\<^sub>E m e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E (\<lambda>a. if a = r then f else m a)) rs = map (ev\<^sub>E m) rs" by auto
  show ?case by simp
qed auto
*)
lemma ev_nop\<^sub>E [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> ev\<^sub>E (top_upd m r f) e = ev\<^sub>E m e"
proof (induct e)
  case (Var x)
  then show ?case using ev\<^sub>E.simps(3) ev_subst\<^sub>E subst_nop\<^sub>E sorry
next
  case (Val x)
  then show ?case by simp
next
  case (Exp x1a x2a)
  then show ?case using ev\<^sub>E.simps(3) ev_subst\<^sub>E subst_nop\<^sub>E sorry
qed


lemma deps_subst\<^sub>E [simp]:
  "deps\<^sub>E (subst\<^sub>E e x e') = deps\<^sub>E e - {x} \<union> (if x \<in> deps\<^sub>E e then deps\<^sub>E e' else {})"
  by (induct e; auto simp: if_splits)

lemma deps_ev\<^sub>E [intro]:
  "\<forall>x \<in> deps\<^sub>E e. m x = m' x \<Longrightarrow> ev\<^sub>E m e = ev\<^sub>E m' e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E m) rs = map (ev\<^sub>E m') rs" by (induct rs) auto
  show ?case by simp
qed (auto)

lemma subst\<^sub>E_flip [simp]:
  "x \<noteq> y \<Longrightarrow> subst\<^sub>E (subst\<^sub>E e x (Val v')) y (Val v) = subst\<^sub>E (subst\<^sub>E e y (Val v)) x (Val v')"
  by (induct e) auto

lemma subst\<^sub>E_rep [simp]:
  "subst\<^sub>E (subst\<^sub>E e x (Val v')) x (Val v) = subst\<^sub>E e x (Val v')"
  by (induct e) auto

lemma finite_deps\<^sub>E [intro]:
  "finite (deps\<^sub>E e)"
  by (induct e) auto

subsection \<open>Boolean Expression\<close>

lemma ev_subst\<^sub>B [simp]:
  "ev\<^sub>B m (subst\<^sub>B b r e) = ev\<^sub>B (m(r := (ev\<^sub>E m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r e)) rs = map (ev\<^sub>E (\<lambda>a. if a = r then ev\<^sub>E m e else m a)) rs"
    by (auto simp: fun_upd_def)     
  show ?case by simp
qed simp+

lemma ev_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> ev\<^sub>B (m(r := f)) b = ev\<^sub>B m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev\<^sub>E (\<lambda>a. if a = r then f else m a)) rs = map (ev\<^sub>E m) rs"
    using ev_nop\<^sub>E[of r _ m f] by (auto simp: fun_upd_def) 
  show ?case by simp
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

lemma deps_ev\<^sub>B [intro]:
  "\<forall>x \<in> deps\<^sub>B e. m x = m' x \<Longrightarrow> ev\<^sub>B m e = ev\<^sub>B m' e"
proof (induct e)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev\<^sub>E m) rs = map (ev\<^sub>E m') rs" by (induct rs) auto
  show ?case by simp
qed auto

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
  by (cases \<alpha>; cases x; auto)

lemma [simp]:
  "Glb x \<in> Reg ` e = False"
  by auto

lemma [simp]:
  "Reg x \<in> Reg ` e = (x \<in> e)"
  by auto

lemma subst_rd [simp]:
  "rd (subst\<^sub>i \<alpha> x e) = rd \<alpha> - {x} \<union> (if x \<in> rd \<alpha> then Reg ` deps\<^sub>E e else {})"
  sorry
(*  by (cases \<alpha>; cases x; auto)
*)

lemma subst_barriers [simp]:
  "barriers (subst\<^sub>i \<alpha> x e) = barriers \<alpha>"
  by (cases \<alpha>; cases x; auto)

lemma subst_nop [simp]:
  "x \<notin> rd \<beta> \<Longrightarrow> subst\<^sub>i \<beta> x e = \<beta>"
  unfolding smap1_def 
  sorry
(*  by (cases \<beta>; cases x) (auto split: if_splits)
 *)

lemma finite_rd [intro]:
  "finite (rd \<alpha>)"
  by (cases \<alpha>) auto

subsection \<open>smap1 Theories\<close>

lemma smap1_flip [simp]:
  "smap1 V y (smap1 V x \<alpha>) = smap1 V x (smap1 V y \<alpha>)"
  sorry
  (*by (cases \<alpha>; cases x; cases y; cases "x = y"; auto simp: smap1_def)
*)

lemma smap1_rep [simp]:
  "smap1 V x (smap1 V x \<alpha>) = smap1 V x \<alpha>"
  by (cases \<alpha>; cases x; auto simp: smap1_def)

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

lemma forall_nil [simp]:
  "forall {} \<alpha> = {\<alpha>}"
  unfolding forall_def by auto

lemma smap1_cong [intro]:
  "M x = N x \<Longrightarrow> smap1 M x = smap1 N x"
  unfolding smap1_def using domIff by fastforce
  
lemma forall_unfold:
  shows "forall (insert x V) \<alpha> = {subst\<^sub>i \<alpha>' x (Val c) | c \<alpha>'. \<alpha>' \<in> forall V \<alpha>}" (is "?L = ?R")
proof -
  have "?L \<subseteq> ?R"
  proof (clarsimp simp: forall_def, cases "x \<in> V")
    fix M assume d: "dom (M :: ('a, 'b) ARMv8_State.var \<Rightarrow> 'a option) = insert x V" "x \<in> V"
    hence "smap \<alpha> M = subst\<^sub>i (smap \<alpha> M) x (Val (the (M x)))" by simp
    moreover have "dom M = V" using d by auto
    ultimately show "\<exists>c \<alpha>'. smap \<alpha> M = subst\<^sub>i \<alpha>' x (Val c) \<and> (\<exists>M. \<alpha>' = smap \<alpha> M \<and> dom M = V)"
      by blast
  next
    fix M assume d: "dom (M :: ('a, 'b) ARMv8_State.var \<Rightarrow> 'a option) = insert x V" "x \<notin> V"
    let ?M = "\<lambda>y. if x = y then None else M y"
    have "smap \<alpha> M = subst\<^sub>i (smap \<alpha> ?M) x (Val (the (M x)))"
    proof -
      have mx: "Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}) = Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x})"
        apply (auto intro!: Finite_Set.fold_cong simp add: cfi.comp_fun_commute_axioms) 
         apply (simp add: cfi.comp_fun_commute_on comp_fun_commute_on.intro) 
        by (simp add: cfi.comp_fun_commute_on comp_fun_commute_on.intro)
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
    fix M c assume d: "V = dom (M :: ('a, 'b) ARMv8_State.var \<Rightarrow> 'a option)" "x \<in> V" 
    have "dom M = insert x (dom M)" using d by auto
    moreover have "subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> M" using d by simp
    ultimately show "\<exists>Ma. subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> Ma \<and> dom Ma = insert x (dom M)"
      by blast
  next
    fix M c assume d: "V = dom (M :: ('a, 'b) ARMv8_State.var \<Rightarrow> 'a option)" "x \<notin> V" 
    let ?M = "\<lambda>y. if y = x then Some c else M y"
    have "dom ?M = insert x (dom M)" using d by auto
    moreover have "subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> ?M"
    proof -
      have mx: "Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}) = Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x})"
        apply (auto intro!: Finite_Set.fold_cong simp add: cfi.comp_fun_commute_axioms)
         apply (simp add: cfi.comp_fun_commute_on comp_fun_commute_on.intro)
        by (simp add: cfi.comp_fun_commute_on comp_fun_commute_on.intro)
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

definition upd
  where "upd S f m \<equiv> m\<lparr>st := \<lambda>x. if x \<in> S then f x else st m x\<rparr>"

lemma upd_nil [simp]:
  "upd {} f m = m"
  by (auto simp: upd_def)

lemma upd_insert [simp]:
  "upd (insert x V) f m = (upd V f m)(x :=\<^sub>s f x)"
  by (auto simp: upd_def st_upd_def intro!: state_rec.equality)

lemma upd_rep [simp]:
  "upd A (st (upd A f m\<^sub>1)) m\<^sub>2 = upd A f m\<^sub>2"
  by (auto simp: upd_def intro!: state_rec.equality)

lemma upd_rep' [simp]:
  "upd A f (upd B f m) = upd (A \<union> B) f m"
  by (auto simp: upd_def intro!: state_rec.equality)

lemma upd_st [simp]:
  "st (upd S f m) x = (if x \<in> S then f x else st m x)"
  by (auto simp: upd_def)

lemma upd_more [simp]:
  "state_rec.more (upd V f m) = state_rec.more m"
  by (auto simp: upd_def)

lemma st_upd_eq [intro]:
  "state_rec.more m = state_rec.more m' \<Longrightarrow> \<forall>x. x \<noteq> y \<longrightarrow> st m x = st m' x \<Longrightarrow> m(y :=\<^sub>s e) = m'(y :=\<^sub>s e)"
  oops
  (*by (auto simp: upd_def st_upd_def intro!: state_rec.equality)
*)

(*
lemma beh_substi [simp]:
  "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (m\<^sub>1(x :=\<^sub>s ev\<^sub>E (rg m\<^sub>1) e),m) \<in> beh\<^sub>i \<alpha>}"
  apply (cases \<alpha>; cases x; clarsimp simp: upd_def)
  by (auto intro!: equality split: if_splits) auto


lemma beh_smap1 [simp]:
  "beh\<^sub>i (smap1 M x \<alpha>) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd ({x} \<inter> dom M) (the o M) m\<^sub>1,m) \<in> beh\<^sub>i \<alpha>}"
  by (cases \<alpha> ; auto simp: smap1_def)

lemma beh_fold_smap1:
  assumes "finite F" 
  shows "beh\<^sub>i (Finite_Set.fold (smap1 M) \<alpha> F) = {(m\<^sub>1, upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd (F \<inter> dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
  using assms
proof (induct)
  case empty
  then show ?case by (cases \<alpha> ; auto)
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
    apply (metis Int_Un_distrib2 Un_insert_right inf_bot_right sup_inf_absorb)
    apply (intro exI conjI)
    prefer 2
    apply blast
    apply simp
    apply (metis Int_Un_distrib2 Un_insert_right inf_bot_right sup_inf_absorb)
    done
qed
*)

lemma [simp]:
  "rg (upd V f m) x = (if Reg x \<in> V then f (Reg x) else rg m x)"
  unfolding rg_def upd_def
  by simp

lemma [simp]:
  "rg (m(aux: f)) = rg m"
  unfolding rg_def aux_upd_def by simp

lemma [simp]:
  "Reg ` deps\<^sub>E e \<subseteq> V \<Longrightarrow> ev\<^sub>E (rg (upd (V \<inter> dom M) (the \<circ> M) m\<^sub>1)) e = ev\<^sub>E (rg (upd (dom M) (the \<circ> M) m\<^sub>1)) e"
  by (rule deps_ev\<^sub>E) auto

lemma [simp]:
  "Reg ` deps\<^sub>B e \<subseteq> V \<Longrightarrow> ev\<^sub>B (rg (upd (V \<inter> dom M) (the \<circ> M) m\<^sub>1)) e = ev\<^sub>B (rg (upd (dom M) (the \<circ> M) m\<^sub>1)) e"
  by (rule deps_ev\<^sub>B) auto

(*
lemma beh_smap [simp]:
  "beh\<^sub>i (smap \<alpha> M) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) | m m\<^sub>1. (upd (dom M) (the o M) m\<^sub>1,m) \<in> beh\<^sub>i \<alpha>}"
proof -
  have "finite (rd \<alpha>)" by auto
  hence "beh\<^sub>i (Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha>)) = 
          {(m\<^sub>1, upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd ((rd \<alpha>) \<inter> dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
    using beh_fold_smap1 by blast

  also have "... = {(m\<^sub>1, upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd (dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
    by (cases \<alpha>; clarsimp)

  finally show ?thesis unfolding smap_def .
qed
*)

end