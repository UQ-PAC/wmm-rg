theory SimAsm_Exp
  imports SimAsm_State
begin



section \<open>Expression Language based on states \<close>

text \<open>Evaluate an expression given a state\<close>
fun st_ev\<^sub>E :: "('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> 'v"
  where "st_ev\<^sub>E m r = ev\<^sub>E (lookupSome m) r" 


text \<open>Evaluate a boolean expression given a state\<close>
fun st_ev\<^sub>B :: "('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r) bexp \<Rightarrow> bool"
  where  "st_ev\<^sub>B m r = ev\<^sub>B (lookupSome m) r" 


text \<open>Operation Behaviour\<close>

fun st_beh\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) state rel"
  where
    "st_beh\<^sub>i (assign a e) = {(s,s'). s' = s (a :=\<^sub>s (st_ev\<^sub>E (s) e))}" | 
    "st_beh\<^sub>i (cmp b) = {(s,s'). s = s' \<and> st_ev\<^sub>B s b}" |
    "st_beh\<^sub>i (leak Cache e) = {(s,s'). s' = s (Cache :=\<^sub>b (st_ev\<^sub>E (s) e))}" | 
    "st_beh\<^sub>i _ = Id"
 

subsection \<open>Expression\<close>


lemma st_ev_subst\<^sub>E [simp]:
  "st_ev\<^sub>E m (subst\<^sub>E e r f) = st_ev\<^sub>E (m(r :=\<^sub>s (st_ev\<^sub>E m f))) e"
proof (induct e)
  case (Var x)
  then show ?case 
  proof(cases "x=r")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using st_upd_def fun_upd_def ev\<^sub>E.simps(1) by simp 
  qed
next
  case (Val x)
  then show ?case by simp
next
  case (Exp fn rs)
  hence [simp]: "map (st_ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r f)) rs = map (st_ev\<^sub>E (m(r :=\<^sub>s st_ev\<^sub>E m f))) rs" by auto
  then show ?case  using ev\<^sub>E.simps(3) map_map subst\<^sub>E.simps(2) 
    by (metis (no_types, lifting) st_ev\<^sub>E.simps map_eq_conv)
qed                          


lemma st_ev_nop\<^sub>E [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> st_ev\<^sub>E (m(r :=\<^sub>s f)) e = st_ev\<^sub>E m e"
proof (induct e)
  case (Var x)
  then show ?case using Var
  proof(cases "x=r")
    case True
    hence "r \<in> deps\<^sub>E (Var x)" using deps\<^sub>E.simps(1) by simp
    then show ?thesis using st_upd_def Var by simp
  next
    case False
    then show ?thesis using st_upd_def fun_upd_def ev\<^sub>E.simps(1) by simp 
  qed
next
  case (Val x)
  then show ?case by simp
next
  case (Exp fn rs)
  hence [simp]: "map (st_ev\<^sub>E (m(r :=\<^sub>s f))) rs = map (st_ev\<^sub>E m) rs" by auto
  then show ?case using ev\<^sub>E.simps(3) st_ev\<^sub>E.simps 
    by (metis (mono_tags, lifting) map_eq_conv)
qed 



lemma deps_st_ev\<^sub>E [intro]:
  "(\<forall>x \<in> deps\<^sub>E e. st m x = st m' x) \<Longrightarrow> st_ev\<^sub>E m e = st_ev\<^sub>E m' e"
proof (induct e)
  case (Var x)
  then show ?case using equality st_ev\<^sub>E.simps deps\<^sub>E.simps(1) ev\<^sub>E.simps(1) 
  proof -
    have a0:"deps\<^sub>E (Var x) ={x}" by simp
    then have a1:"st m x = st m' x" using Var by simp
    then have a2:"lookupSome m x = lookupSome m' x" using Var lookupSome.simps[of m x] 
           lookupSome.simps[of m' x] by simp
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


lemma deps_st_ev\<^sub>E'' [intro]:
  "\<forall>x \<in> deps\<^sub>E e . lookupSome s x = lookupSome s' x \<Longrightarrow> st_ev\<^sub>E s e = st_ev\<^sub>E s' e"
proof (induct e)
  case (Var x) 
  show ?case using deps\<^sub>E.simps(1) st_ev\<^sub>E.simps(1) lookupSome.simps st_ev\<^sub>E.simps(1) using Var by simp
  next
  case (Val x)
  then show ?case by auto
next
  case (Exp fn rs)
  hence [simp]: "map (st_ev\<^sub>E s) rs = map (st_ev\<^sub>E s') rs" by (induct rs) auto
  show ?case using st_ev\<^sub>E.simps by (metis (mono_tags, lifting) Exp.prems deps_ev\<^sub>E)
qed


lemma local_st_ev\<^sub>E [intro]:
  "deps\<^sub>E e \<subseteq> locals \<Longrightarrow> rg m = rg m' \<Longrightarrow> st_ev\<^sub>E m e = st_ev\<^sub>E m' e"
  apply (intro deps_st_ev\<^sub>E ballI, case_tac x) 
  using rg_def apply simp
  by blast  


lemma st_ev_aux\<^sub>E [simp]:
  "st_ev\<^sub>E (m(aux: f)) g = st_ev\<^sub>E m g"
proof (induct g)
  case (Var x)
  then show ?case by simp 
next
  case (Val x)
  then show ?case by simp 
next
  case (Exp x1a x2a)
  then show ?case apply simp by (metis (mono_tags, lifting) map_eq_conv)
qed


subsection \<open>Boolean Expression\<close>

lemma st_ev_subst\<^sub>B [simp]:
  "st_ev\<^sub>B m (subst\<^sub>B b r e) = st_ev\<^sub>B (m(r :=\<^sub>s (st_ev\<^sub>E m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (st_ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r e)) rs = map (st_ev\<^sub>E (m(r :=\<^sub>s st_ev\<^sub>E m e))) rs"
    using fun_upd_def by auto     
  then show ?case 
    using ev_subst\<^sub>B lookupSome.simps st_ev\<^sub>B.elims(1) st_ev\<^sub>E.elims st_ev\<^sub>B.simps st_ev\<^sub>E.simps st_upd_map 
    sorry
qed simp



lemma st_ev_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> st_ev\<^sub>B (m(r :=\<^sub>s f)) b = st_ev\<^sub>B m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (st_ev\<^sub>E (m(r :=\<^sub>s f))) rs = map (st_ev\<^sub>E m) rs"
    using st_ev_nop\<^sub>E[of r _ m f] by (auto simp: fun_upd_def) 
  then show ?case 
    by (metis ev\<^sub>B.simps(2) map_cong st_ev\<^sub>B.elims(2) st_ev\<^sub>B.elims(3) st_ev\<^sub>E.simps)
qed simp


lemma deps_st_ev\<^sub>B [intro]:
  "\<forall>x \<in> deps\<^sub>B e. st m x = st m' x \<Longrightarrow> st_ev\<^sub>B m e = st_ev\<^sub>B m' e"
proof (induct e)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (st_ev\<^sub>E m) rs = map (st_ev\<^sub>E m') rs" by (induct rs) auto 
  then show ?case 
    by (metis (mono_tags, lifting) ev\<^sub>B.simps(2) map_eq_conv st_ev\<^sub>B.elims(1) st_ev\<^sub>E.simps)
qed auto


lemma st_ev_aux\<^sub>B [simp]:
  "st_ev\<^sub>B (s (aux:f)) g = st_ev\<^sub>B s g"
proof (induct g)
  case (Neg g)
  then show ?case by simp
next
  case (Exp\<^sub>B x1a x2)
  then show ?case by (metis aux_st deps_st_ev\<^sub>B)
qed


subsection \<open>Update lemmas\<close>

definition upd                   (* use if f is a total fun: 'a \<Rightarrow> 'v *)
  where "upd S f m \<equiv> m\<lparr>st := \<lambda>x. if x \<in> S then (f x) else st m x\<rparr>"

definition upd_part       (* use if f is a partial fun: 'a \<Rightarrow> 'v option *)
  where "upd_part S f m \<equiv> m\<lparr>st := \<lambda>x. if x \<in> S then (f x) else st m x\<rparr>"

lemma upd_nil [simp]:
  "upd {} f m = m"
  by (auto simp: upd_def)


lemma upd_insert' [simp]:
  "upd (insert x V) f m = (upd V f m)(x :=\<^sub>s (f x))"
  by (auto simp: upd_def st_upd_def intro!: state_rec.equality)

lemma upd_rep [simp]:
  "upd_part A (st (upd A f m\<^sub>1)) m\<^sub>2 = upd A f m\<^sub>2"
  by (auto simp: upd_part_def upd_def intro!: state_rec.equality)

lemma upd_rep' [simp]:
  "upd A f (upd B f m) = upd (A \<union> B) f m"
  by (auto simp: upd_def intro!: state_rec.equality)

lemma upd_st [simp]:
  "st (upd S f m) x = (if x \<in> S then (f x) else st m x)"
  by (auto simp: upd_def)

lemma upd_more [simp]:
  "state_rec.more (upd V f m) = state_rec.more m"
  by (auto simp: upd_def)

lemma upd_cap [simp]:
  "state_rec.cap (upd V f m) = state_rec.cap m"
  by (auto simp: upd_def)

lemma upd_init [simp]:
  "state_rec.initState (upd V f m) = state_rec.initState m"
  by (auto simp: upd_def)




thm state_rec.equality

(* if \<Gamma> is in aux then this will include equality of \<Gamma> mapping *)
lemma st_upd_eq [intro]:
  "state_rec.more m = state_rec.more m' \<Longrightarrow> 
              state_rec.cap m = state_rec.cap m' \<Longrightarrow>
                 initState m = initState m' \<Longrightarrow>
                    \<forall>x. x \<noteq> y \<longrightarrow> st m x = st m' x \<Longrightarrow> m(y :=\<^sub>s e) = m'(y :=\<^sub>s e)"
  by (auto simp: upd_def st_upd_def intro!: state_rec.equality)



lemma [simp]:
  "rg (upd_part V f m) x = (if Reg x \<in> V then f (Reg x) else rg m x)"
  unfolding rg_def upd_part_def
  by simp

lemma [simp]:
  "rg (m(aux: f)) = rg m"
  unfolding rg_def aux_upd_def by simp



lemma eq_comm:
  "(a \<Longrightarrow> (b = c)) \<Longrightarrow> (a \<Longrightarrow> (c = b))" by blast



lemma beh_substi [simp]:
  "st_beh\<^sub>i (subst\<^sub>i \<alpha> x e) = 
                     {(m\<^sub>1,upd_part (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (m\<^sub>1(x :=\<^sub>s st_ev\<^sub>E m\<^sub>1 e),m) \<in> st_beh\<^sub>i \<alpha>}"
  sorry

lemma [simp]:
  "st (m(x :=\<^sub>s e)) = (st m)(x := e)"
  by (auto simp: st_upd_def st_upd_map)

lemma [simp]:
  "Base (st (m(x :=\<^sub>s e))) = Base ((st m)(x := e))"
  by (auto simp: st_upd_def)

(*end*) (* of context expression *)

end