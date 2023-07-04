theory SimAsm_Exp
  imports Var_map
begin

context expression
begin

section \<open>Expression Language based on states \<close>

text \<open>Evaluate an expression given a state\<close>
fun st_ev\<^sub>E 
  where "st_ev\<^sub>E m r = ev\<^sub>E (st m) r" 


text \<open>Evaluate a boolean expression given a state\<close>
fun st_ev\<^sub>B :: "'s \<Rightarrow> ('r,'v) bexp \<Rightarrow> bool"
  where  "st_ev\<^sub>B m r = ev\<^sub>B (st m) r" 


text \<open>Operation Behaviour\<close>

fun st_beh\<^sub>i :: "('r,'v) op \<Rightarrow> 's rel"
  where
    "st_beh\<^sub>i (assign a e) = {(s,s'). s' =  s(a :=\<^sub>u (st_ev\<^sub>E (s) e))}" | 
    "st_beh\<^sub>i (cmp b) = {(s,s'). s = s' \<and> st_ev\<^sub>B s b}" |
    "st_beh\<^sub>i (leak Cache e) = {(s,s'). s' =  s(Cache :=\<^sub>u (st_ev\<^sub>E (s) e))}" | 
    "st_beh\<^sub>i _ = Id"
 

subsection \<open>Expression\<close>


lemma st_ev_subst\<^sub>E [simp]:
  "st_ev\<^sub>E m (subst\<^sub>E e r f) = st_ev\<^sub>E (m(r :=\<^sub>u (st_ev\<^sub>E m f))) e"
proof (induct e)
  case (Var x)
  then show ?case
  by (cases "x=r") simp_all
next
  case (Val x)
  then show ?case by simp
next
  case (Exp fn rs)
  hence [simp]: "map (st_ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r f)) rs = map (st_ev\<^sub>E (m(r :=\<^sub>u st_ev\<^sub>E m f))) rs" by auto
  then show ?case  using ev\<^sub>E.simps(3) map_map subst\<^sub>E.simps(2) 
  by (smt (verit, best) ev_subst\<^sub>E' expression.st_ev\<^sub>E.simps expression_axioms state.st_upd_map state_axioms)
qed                          


lemma st_ev_nop\<^sub>E [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> st_ev\<^sub>E (m(r :=\<^sub>u f)) e = st_ev\<^sub>E m e"
proof (induct e)
  case (Var x)
  then show ?case using Var
  proof(cases "x=r")
    case True
    hence "r \<in> deps\<^sub>E (Var x)" using deps\<^sub>E.simps(1) by simp
    then show ?thesis using Var by simp
  next
    case False
    then show ?thesis using fun_upd_def ev\<^sub>E.simps(1) by simp 
  qed
next
  case (Val x)
  then show ?case by simp
next
  case (Exp fn rs)
  hence [simp]: "map (st_ev\<^sub>E (m(r :=\<^sub>u f))) rs = map (st_ev\<^sub>E m) rs" by auto
  then show ?case using st_ev\<^sub>E.simps 
    by (metis Exp.prems ev_nop\<^sub>E' st_upd_map)
qed 

term st

lemma deps_st_ev\<^sub>E [intro]:
  "(\<forall>x \<in> deps\<^sub>E e. st m x = st m' x) \<Longrightarrow> st_ev\<^sub>E m e = st_ev\<^sub>E m' e"
proof (induct e)
  case (Var x)
  then show ?case using st_ev\<^sub>E.simps deps\<^sub>E.simps(1) ev\<^sub>E.simps(1) 
  proof -
    have a0:"deps\<^sub>E (Var x) ={x}" by simp
    then have a1:"st m x = st m' x" using Var by simp
    then show ?thesis       using st_ev\<^sub>E.simps deps\<^sub>E.simps(1) ev\<^sub>E.simps(1) Var by simp
  qed
next
  case (Val x)
  then show ?case by simp
next
  case (Exp fn rs)
  hence [simp]: "map (st_ev\<^sub>E m) rs = map (st_ev\<^sub>E m') rs" by (induct rs) auto
  then show ?case using ev\<^sub>E.simps(3)st_ev\<^sub>E.simps map_eq_conv 
    by (metis (no_types, lifting))
qed 


lemma local_st_ev\<^sub>E [intro]:
  "deps\<^sub>E e \<subseteq> locals \<Longrightarrow> (\<forall>v \<in> locals. st m v = st m' v) \<Longrightarrow> st_ev\<^sub>E m e = st_ev\<^sub>E m' e"
  by auto

lemma st_ev_aux\<^sub>E [simp]:
  "st_ev\<^sub>E (m(aux: f)) g = st_ev\<^sub>E m g"
by (induct g) (simp, simp, fastforce)


subsection \<open>Boolean Expression\<close>

lemma st_ev_subst\<^sub>B [simp]:
  "st_ev\<^sub>B m (subst\<^sub>B b r e) = st_ev\<^sub>B (m(r :=\<^sub>u (st_ev\<^sub>E m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (st_ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r e)) rs = map (st_ev\<^sub>E (m(r :=\<^sub>u st_ev\<^sub>E m e))) rs"
    using fun_upd_def by auto   
  thus ?case by (metis ev_subst\<^sub>B st_ev\<^sub>B.elims(1) st_ev\<^sub>E.simps st_upd_map)
qed simp



lemma st_ev_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> st_ev\<^sub>B (m(r :=\<^sub>u f)) b = st_ev\<^sub>B m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (st_ev\<^sub>E (m(r :=\<^sub>u f))) rs = map (st_ev\<^sub>E m) rs"
    using st_ev_nop\<^sub>E[of r _ m f] by (auto simp: fun_upd_def) 
  then show ?case by (metis Exp\<^sub>B ev_nop\<^sub>B st_ev\<^sub>B.elims(1) st_upd_map)
qed simp


lemma deps_st_ev\<^sub>B [intro]:
  "\<forall>x \<in> deps\<^sub>B e. st m x = st m' x \<Longrightarrow> st_ev\<^sub>B m e = st_ev\<^sub>B m' e"
proof (induct e)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (st_ev\<^sub>E m) rs = map (st_ev\<^sub>E m') rs" by (induct rs) auto
  then show ?case by (metis (mono_tags, lifting) ev\<^sub>B.simps(2) map_eq_conv st_ev\<^sub>B.elims(1) st_ev\<^sub>E.elims)
qed auto


lemma st_ev_aux\<^sub>B [simp]:
  "st_ev\<^sub>B (s (aux:f)) g = st_ev\<^sub>B s g"
proof (induct g)
  case (Neg g)
  then show ?case by simp
next
  case (Exp\<^sub>B x1a x2)
  then show ?case using st_ev\<^sub>B.simps st_ev_aux\<^sub>E map_eq_conv aux_upd_st by presburger
qed



lemma eq_comm:
  "(a \<Longrightarrow> (b = c)) \<Longrightarrow> (a \<Longrightarrow> (c = b))" by blast


end (* of context expression *)
end