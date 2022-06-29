theory Push_State
  imports Main
begin

chapter \<open>Push State\<close>

text \<open>
This describes a structured state which supports stack-like operations
for joining and splitting states.

It is intended that this is used to support notions of capturing and
scoped state.
\<close>

class state =
  fixes push :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes popl :: "'a \<Rightarrow> 'a"
  (* fixes popr :: "'a \<Rightarrow> 'a" *)
  assumes popl_push [simp]: "popl (push a b) = a"
  assumes push_popl [simp]: "\<exists>s. push (popl m) s = m"
  (* assumes popr_push [simp]: "popr (push a b) = b" *)
  (* assumes push_intro: "\<exists>m. m' = push m s" *)
  assumes push_inj: "push m s = push m' s' \<Longrightarrow> (m = m' \<and> s = s')"

context state
begin

section \<open>Operations on predicates and relations\<close>

definition pushpred :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"pushpred s P = {push m s |m. m \<in> P}"

definition poppred :: "'a set \<Rightarrow> 'a set" where
"poppred P = {popl m |m. m \<in> P}"

(* rarely used except in specific proof steps which require
showing something is inside a pushrelAll or similar. *)
definition pushpredAll :: "'a set \<Rightarrow> 'a set" where
"pushpredAll P \<equiv> {push m s |m s. m \<in> P}"


definition poprel :: "'a rel \<Rightarrow> 'a rel" where
"poprel b = {(popl m,popl m') |m m'. (m,m') \<in> b}" 

definition pushrel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
"pushrel s s' b = {(push m s,push m' s') |m m'. (m,m') \<in> b}" 

definition pushrelSame :: "'a rel \<Rightarrow> 'a rel" where
"pushrelSame R = {(push m s, push m' s) |m m' s. (m,m') \<in> R}"

definition pushrelAll :: "'a rel \<Rightarrow> 'a rel" where
"pushrelAll G = {(push m s, push m' s') |m m' s s'. (m,m') \<in> G}"

section \<open>Introduction rules for the definitions\<close>

lemma pushpred_inI [intro]:
  assumes "p \<in> P" "m = push p s"
  shows "m \<in> pushpred s P"
using assms
unfolding pushpred_def by auto

lemma pushrelSame_inE [elim]:
  assumes "(p,p') \<in> pushrelSame R"
  obtains m m' s where "p = push m s" "p' = push m' s" "(m,m') \<in> R"
using assms pushrelSame_def by auto

lemma pushrelSame_inI [intro]:
  assumes "p = push m s" "p' = push m' s" "(m,m') \<in> R"
  shows "(p,p') \<in> pushrelSame R"
using assms pushrelSame_def by auto

section \<open>Lemmas for push/pop on predicates/relations\<close>

subsection \<open>Introduction of pushes\<close>

text \<open>These allow introducing pushes when given arbitrary predicates.\<close>


subsection \<open>Inverses\<close>

lemma push_poprelAll [simp]: "pushrelAll (poprel G) = G"
unfolding poprel_def pushrelAll_def
oops

lemma pop_pushrelAll [simp]: "poprel (pushrelAll G) = G"
unfolding poprel_def pushrelAll_def
by (auto, metis popl_push)

lemma pop_pushrelSame [simp]: "poprel (pushrelSame G) = G"
unfolding poprel_def pushrelSame_def
by (auto, metis popl_push)

text \<open>Pop a previously pushed predicate or relation.\<close>

lemma pop_pushpred [simp]: "poppred (pushpred s P) = P"
unfolding poppred_def pushpred_def by force

lemma pop_pushrel [simp]: "poprel (pushrel s s' R) = R"
unfolding poprel_def pushrel_def by force

text \<open>These push after pop lemmas are *suspicious*...\<close>

lemma push_poppred [simp]: "pushpred s (poppred P) = P"
unfolding poppred_def pushpred_def 
oops

lemma push_poprel [simp]: "pushrel s s' (poprel R) = R"
unfolding poprel_def pushrel_def
oops


subsection \<open>Monotonicity\<close>

lemma pushpred_mono [simp]: "P \<subseteq> P' \<Longrightarrow> pushpred s P \<subseteq> pushpred s P'"
unfolding pushpred_def by auto

lemma poppred_mono [simp]: "P \<subseteq> P' \<Longrightarrow> poppred P \<subseteq> poppred P'"
unfolding poppred_def by auto

lemma pushpredAll_mono [simp]: "P \<subseteq> P' \<Longrightarrow> pushpredAll P \<subseteq> pushpredAll P'"
unfolding pushpredAll_def by auto

lemma poprel_mono [simp]: "G \<subseteq> G' \<Longrightarrow> poprel G \<subseteq> poprel G'"
unfolding poprel_def pushrelAll_def by auto

lemma pushrel_mono [simp]: "G \<subseteq> G' \<Longrightarrow> pushrel s s' G \<subseteq> pushrel s s' G'"
unfolding pushrel_def by auto

lemma pushrelSame_mono [simp]: "G \<subseteq> G' \<Longrightarrow> pushrelSame G \<subseteq> pushrelSame G'"
unfolding pushrelSame_def by auto

lemma pushrelAll_mono [simp]: "G \<subseteq> G' \<Longrightarrow> pushrelAll G \<subseteq> pushrelAll G'"
unfolding pushrelAll_def by auto

lemma pushrelAll_eq: "(pushrelAll G \<subseteq> pushrelAll G') = (G \<subseteq> G')"
using poprel_mono pop_pushrelAll pushrelAll_mono
by metis

subsection \<open>Relation composition\<close>

lemma poprel_relcomp: "poprel (G O G') \<subseteq> poprel G O poprel G'"
unfolding poprel_def
by auto

lemma pushrelAll_relcomp [simp]: "pushrelAll (G O G') = pushrelAll G O pushrelAll G'"
unfolding pushrelAll_def
by (auto, blast, metis popl_push relcomp.relcompI)

subsubsection \<open>Special cases for popping a relational composition of pushes\<close>

lemma poprel_relcomp_pushrel1: "poprel (pushrel s s' G O pushrelSame G') = G O G'"
unfolding poprel_def pushrel_def pushrelSame_def
by auto (metis popl_push relcomp.simps, force)

lemma poprel_relcomp_pushrel2: "poprel (pushrel s s' G O pushrelAll G') = G O G'"
unfolding poprel_def pushrel_def pushrelAll_def
by auto (metis popl_push relcomp.simps, force)

lemma poprel_relcomp_pushrelSame: "poprel (pushrelSame G O pushrelSame G') = G O G'"
unfolding poprel_def pushrelSame_def
by auto (metis popl_push relcomp.simps, force)

lemma poprel_relcomp_pushrelAll: "poprel (pushrelAll G O pushrelAll G') = G O G'"
unfolding poprel_def pushrelAll_def
by auto (metis popl_push relcomp.simps, force)

lemma poprel_relcomp_pushpred: "poprel (Id_on (pushpred s P) O pushrel s s' P') = Id_on P O P'"
unfolding poprel_def pushpred_def pushrel_def
by auto (metis Id_on_iff popl_push relcompI, force)

lemma pushrel_relcomp_id: "pushrel s s' (Id_on P O P') = Id_on (pushpred s P) O pushrel s s' P'"
unfolding pushrel_def pushpred_def
by auto (metis Id_onI popl_push relcompI)

lemma pushpredAll_poppred_supset: "P \<subseteq> pushpredAll (poppred P)"
unfolding pushpredAll_def poppred_def 
by clarsimp (metis push_popl)

lemma pushrelAll_poprel_supset: "G \<subseteq> pushrelAll (poprel G)"
unfolding pushrelAll_def poprel_def
by clarsimp (metis push_popl)

lemma pushrel_in_pushrelAll: "pushrel s s' G \<subseteq> pushrelAll G"
unfolding pushrel_def pushrelAll_def by fast

lemma pushrelSame_in_pushrelAll: "pushrelSame G \<subseteq> pushrelAll G"
unfolding pushrelSame_def pushrelAll_def by fast

(* unlikely to hold, after popping more relations will link up. *)
lemma "poprel (Id_on P) O poprel P' \<subseteq> poprel (Id_on P O P')"
proof (rule subrelI)
  fix m m' assume mm': "(m,m') \<in> poprel (Id_on P) O poprel P'"
  hence "m \<in> poppred P" unfolding poprel_def poppred_def by auto
  have "(m,m') \<in> poprel P'" using mm' unfolding poprel_def by auto

  show "(m,m') \<in> poprel (Id_on P O P')" sorry
oops

text \<open>If P is contained in a pushed set, popping then pushing again is the identity.\<close>
lemma pushpred_poppred_id: "P \<subseteq> pushpred s P' \<Longrightarrow> P = pushpred s (poppred P)"
unfolding pushpred_def poppred_def
by force

subsection \<open>Intersection\<close>

lemma pushpred_inter [simp]: "pushpred s (P \<inter> P') = pushpred s P \<inter> pushpred s P'"
unfolding pushpred_def
by (auto, metis popl_push)

lemma poppred_inter [simp]: "poppred (P \<inter> P') \<subseteq> poppred P \<inter> poppred P'"
unfolding poppred_def
by auto

lemma poppred_inter2: "poppred (pushpred s P \<inter> pushpred s P') = P \<inter> P'"
unfolding poppred_def pushpred_def
by (auto, (metis popl_push)+)

lemma pushrel_inter [simp]: "pushrel s s' (G \<inter> G') = pushrel s s' G \<inter> pushrel s s' G'"
unfolding pushrel_def
by (auto, metis popl_push)

lemma pushrelSame_inter [simp]: "pushrelSame (G \<inter> G') = pushrelSame G \<inter> pushrelSame G'"
unfolding pushrelSame_def
by (auto, metis popl_push)

lemma pushrelAll_inter [simp]: "pushrelAll (G \<inter> G') = pushrelAll G \<inter> pushrelAll G'"
unfolding pushrelAll_def
by (auto, metis popl_push)

text \<open>Special case where we intersect a narrowed push with a more general push.\<close>
lemma pushpred_inter_pushpredAll: "pushpred s P \<inter> pushpredAll P' = pushpred s (P \<inter> P')"
unfolding pushpred_def pushpredAll_def
by (auto, metis popl_push)

subsection \<open>Union\<close>

lemma pushpred_union: "pushpred s (P \<union> P') = pushpred s P \<union> pushpred s P'"
unfolding pushpred_def by auto

subsection \<open>Image of relations\<close>

lemma pushpred_relimage: "pushpred s (R `` P) = pushrelSame R `` pushpred s P"
unfolding pushpred_def pushrelSame_def
by (auto, insert push_inj, blast) 

lemma pushpredAll_relimage: "pushpredAll (R `` P) = pushrelAll R `` pushpredAll P"
unfolding pushpredAll_def pushrelAll_def
by (auto, insert push_inj, blast+)

subsection \<open>Empty set\<close>

lemma pushpred_empty [simp]: "pushpred s {} = {}"
unfolding pushpred_def by simp

lemma poppred_empty [simp]: "poppred {} = {}"
unfolding poppred_def by simp


lemma poprel_empty [simp]: "poprel {} = {}"
unfolding poprel_def by simp

lemma pushrel_empty [simp]: "pushrel s s' {} = {}"
unfolding pushrel_def by simp

lemma pushrelSame_empty [simp]: "pushrelSame {} = {}"
unfolding pushrelSame_def by simp

lemma pushrelAll_empty [simp]: "pushrelAll {} = {}"
unfolding pushrelAll_def by simp


subsection \<open>Correspondences between predicates and Id_on.\<close>

lemma Id_in_pushrelAll_poppred: "Id_on G \<subseteq> pushrelAll (Id_on (poppred G))"
using pushpredAll_poppred_supset subsetD
unfolding pushrelAll_def pushpredAll_def
by fast

lemma poppred_eq_poprel: "Id_on (poppred a) = poprel (Id_on a)"
unfolding poppred_def poprel_def by auto

lemma poppred_in_poprel: "m \<in> poppred G \<Longrightarrow> (m,m) \<in> poprel (Id_on G)"
using poppred_eq_poprel by fast

subsection \<open>Other\<close>

lemma pushrelSame_in_eq: "((push m s, push m' s) \<in> pushrelSame R) = ((m,m') \<in> R)"
unfolding pushrelSame_def
by (auto, metis local.popl_push)

(* lemma "(pushrelSame R)\<^sup>* = pushrelSame (R\<^sup>* )"
proof (intro antisym subrelI, goal_cases)
  case (1 p p')
  then obtain m m' s where mm': "p = push m s" "p' = push m' s"
    apply (induct, auto)
    by (metis push_popl, metis push_inj pushrelSame_inE)
  show ?case using 1
  proof (induct)
    case base
    have "(m,m) \<in> R\<^sup>*" by simp
    then show ?case using mm' by (simp add: pushrelSame_in_eq)
  next
    case (step y z)
    then show ?case unfolding pushrelSame_def apply auto
    by (metis (no_types, lifting) local.push_inj rtrancl.rtrancl_into_rtrancl)
  qed
next
  case (2 p p')
  then obtain m m' s where mm': "p = push m s" "p' = push m' s" "(m,m') \<in> R\<^sup>*"
    by (rule pushrelSame_inE)
  with mm'(3) show ?case
  proof (induct)
    case base
    then show ?case sorry
  next
    case (step y z)
    then show ?case 
  qed
qed *)

end

text \<open>
Image through transitive closure + reflexive on set is the original set.
Used for stabilise proofs. Also note similarities with the linked lemma
which applies to the builtin rtrancl.
\<close>
thm Transitive_Closure.Image_closed_trancl
lemma Image_closed_trancl': 
  assumes "R `` P \<subseteq> P"
  shows "P \<union> R\<^sup>+ `` P = P"
proof -
  have "m' \<in> P" if "(m, m') \<in> R\<^sup>+" "m \<in> P" for m m'
    using that assms by induct auto
  thus ?thesis by auto
qed

lemma pushrelSame_trancl: "(pushrelSame R)\<^sup>+ = pushrelSame (R\<^sup>+)"
proof (intro antisym subrelI, goal_cases)
  case (1 p p')
  then show ?case
  proof (induct)
    case (base p') thus ?case by auto
  next
    case (step p' p'')
    obtain m m' s where mm': 
      "p = push m s" "p' = push m' s" "(m,m') \<in> R\<^sup>+"
      using step by auto
    obtain m'2 m'' s2 where
      "p' = push m'2 s2" "p'' = push m'' s2" "(m'2,m'') \<in> R"
      using step by auto
    hence m'': "p'' = push m'' s" "(m',m'') \<in> R"
      using mm' push_inj by auto
    hence "(m,m'') \<in> R\<^sup>+" using mm' by simp
    thus ?case using mm' m'' by auto
  qed
next
  case (2 p p'')
  then obtain m m'' s where
    "(m,m'') \<in> R\<^sup>+" "p = push m s" "p'' = push m'' s"
    by auto
  then show ?case 
  proof (induct arbitrary: p p'' s)
    case (base m'') thus ?case by auto
  next
    case (step m' m'')
    hence "(push m s, push m' s) \<in> (pushrelSame R)\<^sup>+" 
      "(push m' s, push m'' s) \<in> pushrelSame R" by auto
    thus ?case using step(4,5) by simp
  qed
qed

end