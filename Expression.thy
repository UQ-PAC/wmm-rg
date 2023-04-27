theory Expression
  imports Main 
begin

section \<open>Expression Language\<close>

datatype ('v,'r) exp = 
  Var 'r | 
  Val 'v | 
  Exp "'v list \<Rightarrow> 'v" "('v,'r) exp list"

locale expression =
  fixes lookup :: "'m \<Rightarrow> 'r \<Rightarrow> 'v"
  fixes update :: "'m \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'm"
  assumes lookup_update: "\<And>m r r' v. lookup (update m r v) r' = (if r = r' then v else lookup m r')"

context expression
begin

definition Uop
  where "Uop f i = Exp (\<lambda>l. case l of [v] \<Rightarrow> f v | _ \<Rightarrow> undefined) [i]"

definition Bop
  where "Bop f i j = Exp (\<lambda>l. case l of [v,v'] \<Rightarrow> f v v' | _ \<Rightarrow> undefined) [i,j]"

text \<open>Evaluate an expression given a state\<close>
fun eval :: "'m \<Rightarrow> ('v,'r) exp \<Rightarrow> 'v"
  where 
    "eval m (Var r) = lookup m r" |
    "eval _ (Val v) = v" |
    "eval m (Exp f rs) = f (map (eval m) rs)"

text \<open>The syntactic dependencies of an expression\<close>
fun deps :: "('v,'r) exp \<Rightarrow> 'r set"
  where 
    "deps (Var r) = {r}" |
    "deps (Exp _ rs) = \<Union>(deps ` set rs)" |
    "deps _ = {}"

text \<open>Substitute a variable for an expression\<close>
fun subst :: "('v,'r) exp \<Rightarrow> 'r \<Rightarrow> ('v,'r) exp \<Rightarrow> ('v,'r) exp"
  where
    "subst (Var r) r' e = (if r = r' then e else Var r)" |
    "subst (Exp f rs) r e = (Exp f (map (\<lambda>x. subst x r e) rs))" |
    "subst e _ _ = e"


subsection \<open>Expression\<close>

lemma eval_subst [simp]:
  "eval m (subst e r f) = eval (update m r (eval m f)) e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (eval m \<circ> (\<lambda>x. subst x r f)) rs = map (eval (update m r (eval m f))) rs" 
    by auto
  show ?case by simp
qed (auto simp: lookup_update)

lemma eval_eq_state [intro]:
  "\<forall>x \<in> deps e. lookup m x = lookup m' x \<Longrightarrow> eval m e = eval m' e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (eval m) rs = map (eval m') rs" by auto
  thus ?case by simp
qed auto

lemma subst_nop [simp]:
  "r \<notin> deps e \<Longrightarrow> subst e r f = e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (\<lambda>x. subst x r f) rs = rs" by (induct rs) auto
  show ?case by simp
qed auto

lemma deps_subst [simp]:
  "deps (subst e x e') = deps e - {x} \<union> (if x \<in> deps e then deps e' else {})"
  by (induct e; auto simp: if_splits)

lemma finite_deps [intro]:
  "finite (deps e)"
  by (induct e) auto

lemma subst_fp [simp]:
  "subst (subst e x (Val v')) x (Val v) = subst e x (Val v')"
  by (induct e) auto

lemma subst_flip [simp]:
  "x \<noteq> y \<Longrightarrow> subst (subst e x (Val v')) y (Val v) = subst (subst e y (Val v)) x (Val v')"
  by (induct e) auto

end

class truth =
  fixes holds :: "'a \<Rightarrow> bool"
  fixes neg :: "'a \<Rightarrow> 'a"
  assumes inv: "holds (neg a) \<equiv> \<not> holds a"

end