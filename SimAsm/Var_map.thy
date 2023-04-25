theory Var_map
  imports Main State2

begin

(* variable: either a register or a global, where registers equal local vars *)
datatype 'r Reg = reg 'r | tmp 'r
datatype ('g,'r) var = Reg 'r | Glb 'g


section \<open>Expression Language based on a generic mapping of variables to values \<close>

(* first value in Exp is a function used to combine the values from its
subexpressions into one value. *)

datatype ('v,'g,'r) exp =
  Var "('g,'r) var" | 
  Val 'v | 
  Exp "'v list \<Rightarrow> 'v" "('v,'g,'r) exp list" (* some fct over a list of subexpr *) 

text \<open>Evaluate an expression given a state\<close>

fun ev\<^sub>E' :: "(('g,'r) var \<Rightarrow> 'v) \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> 'v"
  where 
    "ev\<^sub>E' m (Var r) =  m r" |
    "ev\<^sub>E' _ (Val v) = v" |
    "ev\<^sub>E' m (Exp f rs) = f (map (ev\<^sub>E' m) rs)"  (* eg, Exp(+ a1 a2 a3) = (ev a1) + (ev a2) + (ev a3) *)

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

text \<open>Evaluate an expression given a state \<close>
fun ev\<^sub>B' :: "(('g,'r) var\<Rightarrow> 'v) \<Rightarrow> ('v,'g,'r) bexp \<Rightarrow> bool"
  where 
    "ev\<^sub>B' m (Neg e) = (\<not> (ev\<^sub>B' m e))" |
    "ev\<^sub>B' m (Exp\<^sub>B f rs) = f (map (ev\<^sub>E' m) rs)"

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

text \<open> Some lemmas \<close>

lemma ev_subst\<^sub>E [simp]:
  "ev\<^sub>E' m (subst\<^sub>E e r f) = ev\<^sub>E' (m (r := (ev\<^sub>E' m f))) e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E' m \<circ> (\<lambda>x. subst\<^sub>E x r f)) rs = map (ev\<^sub>E' (m(r := ev\<^sub>E' m f))) rs" 
    using fun_upd_def apply auto using Exp by presburger
  then show ?case by (simp add: fun_upd_def)
qed auto

lemma ev_subst\<^sub>B [simp]:
  "ev\<^sub>B' m (subst\<^sub>B b r e) = ev\<^sub>B' (m(r := (ev\<^sub>E' m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (ev\<^sub>E' m \<circ> (\<lambda>x. subst\<^sub>E x r e)) rs = map (ev\<^sub>E' (m(r := ev\<^sub>E' m e))) rs"
    by (auto simp: fun_upd_def)     
  then show ?case by (simp add: fun_upd_def)
qed simp

lemma subst_nop\<^sub>E [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> subst\<^sub>E e r f = e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (\<lambda>x. subst\<^sub>E x r f) rs = rs" by (induct rs) auto
  show ?case by simp
qed auto

lemma ev_nop\<^sub>E [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> ev\<^sub>E' (m(r := f)) e = ev\<^sub>E' m e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E' (m(r := f))) rs = map (ev\<^sub>E' m) rs" 
    using fun_upd_def apply auto using Exp by blast
  then show ?case by (metis ev\<^sub>E'.simps(3))
qed auto

lemma ev_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> ev\<^sub>B' (m(r := f)) b = ev\<^sub>B' m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev\<^sub>E' (m(r := f))) rs = map (ev\<^sub>E' m) rs"
    using ev_nop\<^sub>E[of r _ m f] by (auto simp: fun_upd_def) 
  then show ?case by (metis ev\<^sub>B'.simps(2))
qed simp

lemma subst_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B e \<Longrightarrow> subst\<^sub>B e r f = e"
proof (induct e)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (\<lambda>x. subst\<^sub>E x r f) rs = rs"  by (induct rs) auto
  show ?case by simp
qed auto

lemma deps_subst\<^sub>B [simp]:
  "deps\<^sub>B (subst\<^sub>B e x e') = deps\<^sub>B e - {x} \<union> (if x \<in> deps\<^sub>B e then deps\<^sub>E e' else {})"
proof (induct e)
  case (Neg e)
  then show ?case by (auto simp: if_splits)
next
  case (Exp\<^sub>B x1a x2)
  then show ?case using if_splits apply auto sorry
qed


(*  by (induct e; auto simp: if_splits) *)

lemma deps_subst\<^sub>E [simp]:
  "deps\<^sub>E (subst\<^sub>E e x e') = deps\<^sub>E e - {x} \<union> (if x \<in> deps\<^sub>E e then deps\<^sub>E e' else {})"
  by (induct e; auto simp: if_splits)
                                     
lemma deps_ev\<^sub>E [intro]:
  "\<forall>x \<in> deps\<^sub>E e. m x = m' x \<Longrightarrow> ev\<^sub>E' m e = ev\<^sub>E' m' e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E' m) rs = map (ev\<^sub>E' m') rs" by (induct rs) auto
  show ?case by simp
qed auto

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

end


