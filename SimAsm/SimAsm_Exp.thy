theory SimAsm_Exp
  imports State2 Var_map
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
    (* then have a2:"lookupSome m x = lookupSome m' x" using Var lookupSome.simps[of m x]  *)
           (* lookupSome.simps[of m' x] sorry *)
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


subsection \<open>Update lemmas\<close>

(*
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

*)


(* if \<Gamma> is in aux then this will include equality of \<Gamma> mapping *)
(* lemma st_upd_eq [intro]: *)
  (* "state_rec.more m = state_rec.more m' \<Longrightarrow>  *)
              (* state_rec.cap m = state_rec.cap m' \<Longrightarrow> *)
                 (* initState m = initState m' \<Longrightarrow> *)
                    (* \<forall>x. x \<noteq> y \<longrightarrow> st m x = st m' x \<Longrightarrow> m(y :=\<^sub>s e) = m'(y :=\<^sub>s e)" *)
  (* by (auto simp: upd_def st_upd_def intro!: state_rec.equality) *)



(* lemma [simp]: *)
  (* "rg (upd_part V f m) x = (if Reg x \<in> V then f (Reg x) else rg m x)" *)
  (* unfolding  upd_part_def *)
  (* by simp *)

(* lemma [simp]: *)
  (* "rg (m(aux: f)) = rg m" *)
  (* unfolding rg_def aux_upd_def by simp *)



lemma eq_comm:
  "(a \<Longrightarrow> (b = c)) \<Longrightarrow> (a \<Longrightarrow> (c = b))" by blast

(*

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

*)

end (* of context expression *)
end