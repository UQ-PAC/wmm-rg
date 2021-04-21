theory SimAsm
  imports Soundness
begin

datatype ('g,'r) var = Reg 'r | Glb 'g
type_synonym ('v,'g,'r) state = "('g,'r) var \<Rightarrow> 'v"
datatype ('v,'g,'r) exp = Var "('g,'r) var" | Val 'v | Exp "'v list \<Rightarrow> 'v" "('v,'g,'r) exp list"

text \<open>Evaluate an expression given a state\<close>
fun ev :: "('v,'g,'r) state \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> 'v"
  where 
    "ev m (Var r) = m r" |
    "ev _ (Val v) = v" |
    "ev m (Exp f rs) = f (map (ev m) rs)"

text \<open>The syntactic dependencies of an expression\<close>
fun deps :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var set"
  where 
    "deps (Var r) = {r}" |
    "deps (Exp _ rs) = \<Union>(deps ` set rs)" |
    "deps _ = {}"

text \<open>Substitute a variable for an expression\<close>
fun subst :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) exp"
  where
    "subst (Var r) r' e = (if r = r' then e else Var r)" |
    "subst (Exp f rs) r e = (Exp f (map (\<lambda>x. subst x r e) rs))" |
    "subst e _ _ = e"

datatype ('v,'g,'r) bexp = Neg "('v,'g,'r) bexp" | Exp\<^sub>B "'v list \<Rightarrow> bool" "('v,'g,'r) exp list"

text \<open>Evaluate an expression given a state\<close>
fun ev\<^sub>B :: "('v,'g,'r) state \<Rightarrow> ('v,'g,'r) bexp \<Rightarrow> bool"
  where 
    "ev\<^sub>B m (Neg e) = (\<not> (ev\<^sub>B m e))" |
    "ev\<^sub>B m (Exp\<^sub>B f rs) = f (map (ev m) rs)"

text \<open>The syntactic dependencies of an expression\<close>
fun deps\<^sub>B :: "('v,'g,'r) bexp \<Rightarrow> ('g,'r) var set"
  where 
    "deps\<^sub>B (Neg e) = deps\<^sub>B e" |
    "deps\<^sub>B (Exp\<^sub>B _ rs) = \<Union>(deps ` set rs)"

text \<open>Substitute a variable for an expression\<close>
fun subst\<^sub>B :: "('v,'g,'r) bexp \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) bexp"
  where
    "subst\<^sub>B (Neg b) r e = Neg (subst\<^sub>B b r e)" |
    "subst\<^sub>B (Exp\<^sub>B f rs) r e = (Exp\<^sub>B f (map (\<lambda>x. subst x r e) rs))"

section \<open>Operations\<close>

datatype ('v,'g,'r) op =
    assign "('g,'r) var" "('v,'g,'r) exp"
  | cmp "('v,'g,'r) bexp"
  | fence
  | cfence
  | nop

fun beh\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) state rel"
  where
    "beh\<^sub>i (assign a e) = {(m,m'). m' = m (a := ev m e)}" |
    "beh\<^sub>i (cmp b) = {(m,m'). m = m' \<and> ev\<^sub>B m b}" |
    "beh\<^sub>i _ = Id"

text \<open>Variables written by a sub-operation\<close>
fun wr :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var set"
  where 
    "wr (assign y _) = {y}" |
    "wr _ = {}"

text \<open>Variables read by a sub-operation\<close>
fun rd :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var set"
  where
    "rd (assign _ e) = deps e" |
    "rd (cmp b) = deps\<^sub>B b" |
    "rd _ = {}"

abbreviation refs
  where "refs a \<equiv> wr a \<union> rd a"

abbreviation locals
  where "locals \<equiv> Reg ` UNIV"

text \<open>Sub-Instruction Reordering\<close>
text \<open>Only pattern match on first argument due to performance issues\<close>
fun re\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op \<Rightarrow> bool" 
  where
    "re\<^sub>i fence \<alpha> = False" |
    "re\<^sub>i (cmp b) \<alpha> = (wr \<alpha> \<subseteq> locals \<and> \<alpha> \<noteq> cfence \<and> rd (cmp b) \<inter> wr \<alpha> = {} \<and> rd (cmp b) \<inter> rd \<alpha> \<subseteq> locals)" |
    "re\<^sub>i cfence \<alpha> = (rd \<alpha> \<subseteq> locals)" |
    "re\<^sub>i \<alpha> \<beta> = (\<alpha> \<noteq> fence \<and> wr \<alpha> \<inter> wr \<beta> = {} \<and> rd \<alpha> \<inter> wr \<beta> = {} \<and> refs \<alpha> \<inter> refs \<beta> \<subseteq> locals)"

text \<open>Sub-Instruction Forwarding\<close>
fun fwd\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op" 
  where
    "fwd\<^sub>i (assign r e) (assign r' e') = (assign r (subst e r' e'))" |
    "fwd\<^sub>i (cmp b) (assign r e) = (cmp (subst\<^sub>B b r e))" |
    "fwd\<^sub>i \<alpha> _ = \<alpha>"

definition comp (infix "\<Otimes>" 60)
  where "comp a b \<equiv> {(m,m'). \<exists>m''. (m,m'') \<in> a \<and> (m'',m') \<in> b}"

lemma [simp]:
  "ev m (subst e r f) = ev (m(r := (ev m f))) e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev m \<circ> (\<lambda>x. subst x r f)) rs = map (ev (\<lambda>a. if a = r then ev m f else m a)) rs"
    by auto
  show ?case by simp
qed auto

lemma ev_nop [simp]:
  "r \<notin> deps e \<Longrightarrow> ev (m(r := f)) e = ev m e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev (\<lambda>a. if a = r then f else m a)) rs = (map (ev m) rs)" by auto
  show ?case by simp
qed auto

lemma [simp]:
  "ev\<^sub>B m (subst\<^sub>B b r e) = ev\<^sub>B (m(r := (ev m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (ev m \<circ> (\<lambda>x. subst x r e)) rs = map (ev (\<lambda>a. if a = r then ev m e else m a)) rs"
    by (auto simp: fun_upd_def)     
  show ?case by simp
qed simp

lemma ev\<^sub>B_nop [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> ev\<^sub>B (m(r := f)) b = ev\<^sub>B m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev (\<lambda>a. if a = r then f else m a)) rs = map (ev m) rs"
    using ev_nop[of r _ m f] by (auto simp: fun_upd_def) 
  show ?case by simp
qed simp

lemma re_consistent:
  "re\<^sub>i \<alpha> (fwd\<^sub>i \<beta> \<alpha>) \<Longrightarrow> beh\<^sub>i \<alpha> \<Otimes> beh\<^sub>i \<beta> \<supseteq> beh\<^sub>i (fwd\<^sub>i \<beta> \<alpha>) \<Otimes> beh\<^sub>i \<alpha>" 
  by (cases \<alpha>; cases \<beta>; auto simp add: comp_def)

type_synonym ('v,'g,'r) opbasic = "(('v,'g,'r) op, ('v,'g,'r) state) basic"
 
text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'g,'r) opbasic \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('v,'g,'r) opbasic" 
  where "fwd\<^sub>s (\<alpha>,v,_) \<beta> =  (fwd\<^sub>i \<alpha> \<beta>, v, beh\<^sub>i (fwd\<^sub>i \<alpha> \<beta>))" 

section \<open>Language Definition\<close>

datatype ('v,'g,'r) lang =
  Skip
  | Op "('v,'g,'r) state set" "('v,'g,'r) op"
  | Seq "('v,'g,'r) lang" "('v,'g,'r) lang"
  | If "('v,'g,'r) bexp" "('v,'g,'r) lang" "('v,'g,'r) lang"
  | While "('v,'g,'r) bexp" "('v,'g,'r) state set" "('v,'g,'r) lang"

interpretation rules fwd\<^sub>s re\<^sub>i by (unfold_locales) (auto)

end
