theory State
  imports Main
begin

chapter \<open>Abstract State\<close>

text \<open>
To ensure the logic is sufficiently abstract,
we make no assumptions about its structure and represent it as a single type variable.
Therefore, rules that manipulate the state, such as removal of auxiliary variables
and local state require operators over the state to express the necessary transformations.
\<close>


type_synonym ('b) pred = "('b) set"
type_synonym ('b) rpred = "('b) rel"

section \<open>Definitions\<close>

text \<open>Stability of a predicate across an environment step\<close>
definition stable :: "('b) rpred \<Rightarrow> ('b) pred \<Rightarrow> bool"
  where "stable R P \<equiv> \<forall>m m'. m \<in> P \<longrightarrow> (m,m') \<in> R \<longrightarrow> m' \<in> P"

text \<open>Weakest precondition for a pre-condition and post-relation\<close>
definition wp :: "'b pred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp pre post Q \<equiv>
    pre \<inter> {m. (\<forall>m'. (m,m') \<in> post \<longrightarrow> m' \<in> Q) }"

text \<open>Equivalent definitions for stable and wp using relation operations.\<close>

lemma stable_rel:
  "stable R P = (R `` P \<subseteq> P)"
unfolding stable_def by auto

(*
lemma wp_rel_partial:
  "wp pre post Q = pre \<inter> Domain post \<inter> {m. (\<forall>m'. (m,m') \<in> post \<longrightarrow> m' \<in> Q)}"
unfolding wp_def by auto
*)

(*  "r `` s = {y. \<exists>x\<in>s. (x, y) \<in> r}"  *)

lemma wp_rel:
  "wp pre post Q = pre \<inter> -(post\<inverse> `` (-Q))"
  unfolding wp_def by auto


text \<open>Guarantee check for a pre-condition and post-relation\<close>
definition guar :: "'b pred \<Rightarrow> 'b rpred \<Rightarrow> 'b rpred \<Rightarrow> bool"
  where "guar pre post G \<equiv> {(m,m'). m \<in> pre \<and> (m,m') \<in> post} \<subseteq> G"

fun guar2 :: "'b pred \<Rightarrow> 'b rpred \<Rightarrow> 'b rpred \<Rightarrow> bool" where
"guar2 pre post G = (pre \<subseteq> {m. (\<forall>m'. ((m,m') \<in> post \<longrightarrow> (m,m') \<in> G))})"

lemma "guar pre post G = guar2 pre post G"
by (auto simp add: guar_def)

text \<open>Shorthand for the weakest-precondition of an environment step\<close>
abbreviation wp\<^sub>e :: "'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp\<^sub>e R Q \<equiv> wp UNIV (R\<^sup>* ) Q"

section \<open>Stability Properties\<close>

lemma stable_conseqI [intro]:
  assumes "stable R' P" "R \<subseteq> R'" 
  shows "stable R P"
  using assms rtrancl_mono unfolding stable_def by blast

lemma stable_conjI [intro]:
  assumes "stable R P" "stable R' P'"
  shows "stable (R \<inter> R') (P \<inter> P')"
  using assms by (auto simp: stable_def)

lemma stable_transitive:
  assumes "(m,m') \<in> R\<^sup>*" "m \<in> P" "stable R P"
  shows "m' \<in> P"
  using assms by (induct rule: rtrancl.induct) (auto simp: stable_def)

lemma stable_wpI:
  "stable R P \<Longrightarrow> P \<subseteq> wp UNIV (R\<^sup>*) P"
  unfolding wp_def using stable_transitive by fast

lemma stable_falseI [intro]:
  "stable R {}"
  by (auto simp: stable_def)

lemma stable_wp: "stable R (wp UNIV (R\<^sup>*) P)"
unfolding stable_def wp_def
by (auto simp: converse_rtrancl_into_rtrancl)

lemma "P \<subseteq> (R\<^sup>*) `` P"
unfolding wp_def
by auto


lemma "stable R ((R\<^sup>*) `` P)"
unfolding stable_def
by (meson Image_iff rtrancl.rtrancl_into_rtrancl)


section \<open>Guarantee Properties\<close>

lemma "G \<subseteq> G\<^sup>*" by auto

lemma guar_conseqI [intro]:
  assumes "guar pre post G" "G \<subseteq>  G'"
  shows "guar pre post G'"
  using assms by (auto simp: guar_def)

lemma guar_trancl [intro]:
  assumes "guar pre post G" 
  shows "guar pre post (G\<^sup>*)"
  using assms guar_conseqI by (auto simp: guar_def)


section \<open>Thread-Local State\<close>

text \<open>
To support thread-local state, we require an operation capable of merging two states, such
that the global component from the first is merged with the local component of the second.
We refer to this operation as op throughout the definitions.
\<close>

type_synonym 'b merge = "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (* note merge is just a type syn! *) 

text \<open>Collect all states where their combination with the local state of l satisfies P\<close>
definition thr\<^sub>P :: "'b merge \<Rightarrow> 'b \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "thr\<^sub>P op l P \<equiv> {m. op m l \<in> P}"

text \<open>Collect all states where some local state satisfies Q\<close>
definition thr\<^sub>Q :: "'b merge \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "thr\<^sub>Q op Q \<equiv> {m. \<exists>l. op m l \<in> Q}"

text \<open>Collect all transitions in R that preserve the local state\<close>
definition thr\<^sub>R :: "'b merge \<Rightarrow> 'b rpred \<Rightarrow> 'b rpred"
  where "thr\<^sub>R op R \<equiv> {(m,m') |m m'. \<forall>l. (op m l,op m' l) \<in> R}"

text \<open>Collect all transitions where their combinations with arbitrary local states satisfies G\<close>
definition thr\<^sub>G :: "'b merge \<Rightarrow> 'b rpred \<Rightarrow> 'b rpred"
  where "thr\<^sub>G op G \<equiv> {(m,m') |m m' l l'. (op m l,op m' l') \<in> G}"

definition invthr\<^sub>G :: "'b merge \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b rpred \<Rightarrow> 'b rpred" where
  "invthr\<^sub>G op l l' G' \<equiv> {(op m l, op m' l') |m m'. (m,m') \<in> G'}"


text \<open>Collect all states where all local states satisfy P\<close>
definition thr\<^sub>A :: "'b merge \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "thr\<^sub>A op P \<equiv> {m. \<forall>l. op m l \<in> P}"

text \<open>Lift a local transition to a global transition given the pre and post local state\<close>
definition thr2glb :: "'b merge \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b rpred \<Rightarrow> 'b rpred"
  where "thr2glb op l l' r \<equiv> {(m,m'). (op m l,op m' l') \<in> r}"

text \<open>The predicate transformations preserve ordering\<close>
lemma thr_mono:
  "P \<subseteq> Q \<Longrightarrow> thr\<^sub>P op l P \<subseteq> thr\<^sub>P op l Q"
  unfolding thr\<^sub>P_def by auto

lemma thr_mono':
  "P \<subseteq> Q \<Longrightarrow> thr\<^sub>A op P \<subseteq> thr\<^sub>A op Q"
  unfolding thr\<^sub>A_def by auto

text \<open>The predicate transformations preserve stability\<close>
lemma thr_stable:
  "stable R P \<Longrightarrow> stable (thr\<^sub>R op R) (thr\<^sub>P op l P)"
  unfolding thr\<^sub>P_def thr\<^sub>R_def stable_def by auto

lemma thr_stable':
  "stable R P \<Longrightarrow> stable (thr\<^sub>R op R) (thr\<^sub>A op P)"
  unfolding thr\<^sub>A_def thr\<^sub>R_def stable_def by auto

lemma thr_stableQ:
  "stable R P \<Longrightarrow> stable (thr\<^sub>R op R) (thr\<^sub>Q op P)"
  unfolding thr\<^sub>Q_def thr\<^sub>R_def stable_def by auto

lemma thr_wp:
  "P \<subseteq> wp v r M \<Longrightarrow> thr\<^sub>P op l P \<subseteq> wp (thr\<^sub>P op l v) (thr2glb op l l' r) (thr\<^sub>P op l' M)"
  unfolding wp_def thr2glb_def thr\<^sub>P_def
  apply auto
  oops
  

lemma thr_guar:
  "guar v r G \<Longrightarrow> guar (thr\<^sub>P op l v) (thr2glb op l l' r) (thr\<^sub>G op G)"
  unfolding thr2glb_def thr\<^sub>P_def thr\<^sub>G_def guar_def by auto

section \<open>Auxiliary State\<close>

text \<open>
To support auxiliary state, we require a state relation that relates two states given their
real components are equivalent.
\<close>

definition aux\<^sub>P                           (* r\<^sup>= \<equiv> r \<union> Id *)
  where "aux\<^sub>P r P \<equiv> {m. \<exists>m'. (m,m') \<in> r\<^sup>= \<and> m' \<in> P}"

definition aux\<^sub>R
  where "aux\<^sub>R r R \<equiv> {(m,m'). \<forall>n. (m,n) \<in> r\<^sup>= \<longrightarrow> (\<exists>n'. (m',n') \<in> r\<^sup>= \<and> (n,n') \<in> R)}"

definition aux\<^sub>G
  where "aux\<^sub>G r R \<equiv> {(m,m'). \<exists>n n'. (m,n) \<in> r\<^sup>= \<and> (m',n') \<in> r\<^sup>= \<and> (n,n') \<in> R}"

lemma aux\<^sub>P_mono [intro]:
  "P \<subseteq> Q \<Longrightarrow> aux\<^sub>P a P \<subseteq> aux\<^sub>P a Q"
  unfolding aux\<^sub>P_def by auto

lemma aux\<^sub>R_mono [intro]:
  "P \<subseteq> Q \<Longrightarrow> aux\<^sub>R a P \<subseteq> aux\<^sub>R a Q"
  unfolding aux\<^sub>R_def by fast

lemma aux\<^sub>P_self [intro]:
  "P \<subseteq> aux\<^sub>P r P"
  unfolding aux\<^sub>P_def by auto

lemma aux\<^sub>G_self [intro]:
  "R \<subseteq> aux\<^sub>G r R"
  unfolding aux\<^sub>G_def by auto

lemma aux_stable [intro]:
  assumes "stable R P" 
  shows "stable (aux\<^sub>R r R) (aux\<^sub>P r P)"
  unfolding stable_def aux\<^sub>R_def aux\<^sub>P_def
proof (clarsimp, goal_cases)
  case (1 m n p)
  then obtain n' where a: "(p, n') \<in> r\<^sup>=" "(n, n') \<in> R" by auto
  hence "n' \<in> P" using 1 assms by (auto simp: stable_def)
  then show ?case using a(1) by auto
qed

(*
lemma aux_wp [intro]:
  assumes "P \<subseteq> wp v b Q"
  shows "aux\<^sub>P r P \<subseteq> wp (aux\<^sub>P r v) (aux\<^sub>R r b) (aux\<^sub>P r Q)"
  unfolding wp_def aux\<^sub>P_def
proof (clarsimp, (intro conjI; clarsimp), goal_cases)
  case (1 n m')
  then show ?case using assms by (auto simp: wp_def aux\<^sub>P_def)
next
  case (2 n m')
  then show ?case using assms
  proof (intro conjI, goal_cases)
    case 1
    then show ?case unfolding aux\<^sub>R_def wp_def by fast
  next
    case 2
    then show ?case 
  qed 
oops *)

lemma aux_guar [intro]:
  assumes "guar v b G" 
  shows "guar (aux\<^sub>P r v) (aux\<^sub>R r b) (aux\<^sub>G r G)"
  unfolding wp_def aux\<^sub>G_def aux\<^sub>P_def aux\<^sub>R_def guar_def
proof (clarsimp, goal_cases)
  case (1 m m' n)
  then obtain n' where a: "(m', n') \<in> r\<^sup>=" "(n, n') \<in> b" by auto
  hence "(n,n') \<in> G" using assms 1 by (auto simp: guar_def)
  thus ?case using a(1) 1(2) by auto
qed

end