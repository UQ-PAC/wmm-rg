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
  assumes push_inj: "push m s = push m' s' \<Longrightarrow> (m = m' \<and> s = s')"

context state
begin

section \<open>Operations on predicates and relations\<close>

definition pop
  where "pop A \<equiv> THE C. \<exists>B. A = push C B"

lemma push_inj_eq:
  "(push m s = push m' s') = (m = m' \<and> s = s')"
  by rule (auto dest: push_inj)

lemma pop_push [simp]:
  "pop (push a b) = a"
  unfolding pop_def push_inj_eq by auto

definition pushpred :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"pushpred s P = {push m s |m. m \<in> P}"

definition poppred :: "'a set \<Rightarrow> 'a set" where
"poppred P = {pop m |m. m \<in> P}"

definition poppred' :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"poppred' s P = {m |m. push m s \<in> P}"

(* rarely used except in specific proof steps which require
showing something is inside a pushrelAll or similar. *)
definition pushpredAll :: "'a set \<Rightarrow> 'a set" where
"pushpredAll P \<equiv> {push m s |m s. m \<in> P}"


definition poprel :: "'a rel \<Rightarrow> 'a rel" where
"poprel b = {(pop m,pop m') |m m'. (m,m') \<in> b}" 

definition poprel' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
"poprel' s s' R = {(m,m') |m m'. (push m s,push m' s') \<in> R}" 

definition pushrel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
"pushrel s s' b = {(push m s,push m' s') |m m'. (m,m') \<in> b}" 

definition pushrelSame :: "'a rel \<Rightarrow> 'a rel" where
"pushrelSame R = {(push m s, push m' s) |m m' s. (m,m') \<in> R}"

definition pushrelAll :: "'a rel \<Rightarrow> 'a rel" where
"pushrelAll G = {(push m s, push m' s') |m m' s s'. (m,m') \<in> G}"

abbreviation poppable :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
"poppable s P \<equiv> (P = pushpred s (poppred P))"

section \<open>Introduction/elimination rules for the definitions\<close>

lemma pushpred_inI [intro]:
  assumes "p \<in> P" "m = push p s"
  shows "m \<in> pushpred s P"
using assms
unfolding pushpred_def by auto

lemma pushpred_inE:
  assumes "m \<in> pushpred s P"
  obtains p s where "p \<in> P" "m = push p s"
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

lemma poppable_inE:
  assumes "p \<in> P" "poppable s P"
  obtains m where "p = push m s"
using assms unfolding poppred_def pushpred_def by auto

text \<open>TRICKY! Extracting local states from a given state.\<close>
text \<open>Obtains the set of states which were pushed onto a given set.\<close>
definition pushed where
"pushed P \<equiv> {s |s m. m \<in> P \<and> push (pop m) s = m}"

lemma pushed_inE [elim]:
  assumes "s \<in> pushed P"
  obtains p where "p \<in> P" "push (pop p) s = p"
using assms unfolding pushed_def by auto 

(*
lemma pushed_set_supset: "P \<subseteq> (\<Union>s \<in> pushed P. pushpred s (poppred' s P))"
unfolding pushed_def pushpred_def poppred'_def
by auto (metis push_pop) *)

lemma push_poppred_subset: "pushpred s (poppred' s P) \<subseteq> P"
unfolding pushpred_def poppred'_def
by auto

(*
lemma pushed_empty: "pushed P = {} \<Longrightarrow> P = {}"
unfolding pushed_def 
using push_pop by fastforce *)


section \<open>Lemmas for push/pop on predicates/relations\<close>

lemma poppred'_subset: "poppred' s P \<subseteq> poppred P"
unfolding poppred'_def poppred_def
by force

lemma poprel'_subset: "poprel' s s' R \<subseteq> poprel R"
unfolding poprel_def poprel'_def
by force

subsection \<open>Introduction of pushes\<close>

text \<open>These allow introducing pushes when given arbitrary predicates.\<close>


subsection \<open>Inverses\<close>

lemma push_poprelAll [simp]: "pushrelAll (poprel G) = G"
unfolding poprel_def pushrelAll_def
oops

lemma pop_pushrelAll [simp]: "poprel (pushrelAll G) = G"
unfolding poprel_def pushrelAll_def
by (auto, metis pop_push)

lemma pop_pushrelSame [simp]: "poprel (pushrelSame G) = G"
unfolding poprel_def pushrelSame_def
by (auto, metis pop_push)

text \<open>Pop a previously pushed predicate or relation.\<close>

lemma pop_pushpred [simp]: "poppred (pushpred s P) = P"
unfolding poppred_def pushpred_def by force

lemma pop_pushpredAll [simp]: "poppred (pushpredAll P) = P"
unfolding poppred_def pushpredAll_def by force

lemma pop_pushrel [simp]: "poprel (pushrel s s' R) = R"
unfolding poprel_def pushrel_def by force

text \<open>These push after pop lemmas are *suspicious*...\<close>

lemma push_poprel [simp]: "pushrel s s' (poprel R) = R"
unfolding poprel_def pushrel_def
oops


subsection \<open>Monotonicity\<close>

lemma pushpred_mono [simp]: "P \<subseteq> P' \<Longrightarrow> pushpred s P \<subseteq> pushpred s P'"
unfolding pushpred_def by auto

lemma poppred_mono [simp]: "P \<subseteq> P' \<Longrightarrow> poppred P \<subseteq> poppred P'"
unfolding poppred_def by auto

lemma poppred'_mono: "P \<subseteq> P' \<Longrightarrow> poppred' s P \<subseteq> poppred' s P'"
unfolding poppred'_def by auto

lemma pushpredAll_mono [simp]: "P \<subseteq> P' \<Longrightarrow> pushpredAll P \<subseteq> pushpredAll P'"
unfolding pushpredAll_def by auto

lemma poprel_mono [simp]: "G \<subseteq> G' \<Longrightarrow> poprel G \<subseteq> poprel G'"
unfolding poprel_def pushrelAll_def by auto

lemma poprel'_mono [simp]: "G \<subseteq> G' \<Longrightarrow> poprel' s s' G \<subseteq> poprel' s s' G'"
unfolding poprel'_def pushrelAll_def by auto


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
by (auto, blast, metis pop_push relcomp.relcompI)

subsubsection \<open>Special cases for popping a relational composition of pushes\<close>

lemma poprel_relcomp_pushrel1: "poprel (pushrel s s' G O pushrelSame G') = G O G'"
unfolding poprel_def pushrel_def pushrelSame_def
by auto (metis pop_push relcomp.simps, force)

lemma poprel_relcomp_pushrel2: "poprel (pushrel s s' G O pushrelAll G') = G O G'"
unfolding poprel_def pushrel_def pushrelAll_def
by auto (metis pop_push relcomp.simps, force)

lemma poprel_relcomp_pushrelSame: "poprel (pushrelSame G O pushrelSame G') = G O G'"
unfolding poprel_def pushrelSame_def
by auto (metis pop_push relcomp.simps, force)

lemma poprel_relcomp_pushrelAll: "poprel (pushrelAll G O pushrelAll G') = G O G'"
unfolding poprel_def pushrelAll_def
by auto (metis pop_push relcomp.simps, force)

lemma poprel_relcomp_pushpred: "poprel (Id_on (pushpred s P) O pushrel s s' P') = Id_on P O P'"
unfolding poprel_def pushpred_def pushrel_def
by auto (metis Id_on_iff pop_push relcompI, force)

lemma pushrel_relcomp_id: "pushrel s s' (Id_on P O P') = Id_on (pushpred s P) O pushrel s s' P'"
unfolding pushrel_def pushpred_def
by auto (metis Id_onI pop_push relcompI)

(*
lemma pushpredAll_poppred_supset: "P \<subseteq> pushpredAll (poppred P)"
unfolding pushpredAll_def poppred_def 
by clarsimp (metis push_pop)

lemma pushrelAll_poprel_supset: "G \<subseteq> pushrelAll (poprel G)"
unfolding pushrelAll_def poprel_def
by clarsimp (metis push_pop) *)

lemma pushrel_in_pushrelAll: "pushrel s s' G \<subseteq> pushrelAll G"
unfolding pushrel_def pushrelAll_def by fast

lemma pushrelSame_in_pushrelAll: "pushrelSame G \<subseteq> pushrelAll G"
unfolding pushrelSame_def pushrelAll_def by fast

(* unlikely to hold, after popping more relations will link up. *)
(*lemma "poprel (Id_on P) O poprel P' \<subseteq> poprel (Id_on P O P')"
proof (rule subrelI)
  fix m m' assume mm': "(m,m') \<in> poprel (Id_on P) O poprel P'"
  hence "m \<in> poppred P" unfolding poprel_def poppred_def by auto
  have "(m,m') \<in> poprel P'" using mm' unfolding poprel_def by auto

  show "(m,m') \<in> poprel (Id_on P O P')" oops
oops *)

text \<open>If P is contained in a pushed set, popping then pushing again is the identity.\<close>
lemma pushpred_poppable: "P \<subseteq> pushpred s P' \<Longrightarrow> P = pushpred s (poppred P)"
unfolding pushpred_def poppred_def
by force

subsection \<open>Intersection\<close>

lemma pushpred_inter [simp]: "pushpred s (P \<inter> P') = pushpred s P \<inter> pushpred s P'"
unfolding pushpred_def
by (auto, metis pop_push)

lemma poppred_inter [simp]: "poppred (P \<inter> P') \<subseteq> poppred P \<inter> poppred P'"
unfolding poppred_def
by auto

lemma poppred_inter2: "poppred (pushpred s P \<inter> pushpred s P') = P \<inter> P'"
unfolding poppred_def pushpred_def
by (auto, (metis pop_push)+)

lemma pushrel_inter [simp]: "pushrel s s' (G \<inter> G') = pushrel s s' G \<inter> pushrel s s' G'"
unfolding pushrel_def
by (auto, metis pop_push)

lemma pushrelSame_inter [simp]: "pushrelSame (G \<inter> G') = pushrelSame G \<inter> pushrelSame G'"
unfolding pushrelSame_def
by (auto, metis pop_push)

lemma pushrelAll_inter [simp]: "pushrelAll (G \<inter> G') = pushrelAll G \<inter> pushrelAll G'"
unfolding pushrelAll_def
by (auto, metis pop_push)

lemma pushpredAll_inter: "pushpredAll (P \<inter> P') = pushpredAll P \<inter> pushpredAll P'"
unfolding pushpredAll_def
by auto (metis local.pop_push)

text \<open>Special case where we intersect a narrowed push with a more general push.\<close>
lemma pushpred_inter_pushpredAll: "pushpred s P \<inter> pushpredAll P' = pushpred s (P \<inter> P')"
unfolding pushpred_def pushpredAll_def
by (auto, metis pop_push)

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

lemma poppable_empty [simp]: "poppable s {}"
by simp


subsection \<open>Correspondences between predicates and Id_on.\<close>

(*
lemma Id_in_pushrelAll_poppred: "Id_on G \<subseteq> pushrelAll (Id_on (poppred G))"
using pushpredAll_poppred_supset subsetD
unfolding pushrelAll_def pushpredAll_def
by fast *)

lemma poppred_eq_poprel: "Id_on (poppred a) = poprel (Id_on a)"
unfolding poppred_def poprel_def by auto

lemma poppred_in_poprel: "m \<in> poppred G \<Longrightarrow> (m,m) \<in> poprel (Id_on G)"
using poppred_eq_poprel by fast

subsection \<open>Other\<close>

lemma pushrelSame_in_eq: "((push m s, push m' s) \<in> pushrelSame R) = ((m,m') \<in> R)"
unfolding pushrelSame_def
by (auto, metis local.pop_push)

lemma domain_pushrel: "Domain (pushrel s s' R) = pushpred s (Domain R)"
unfolding pushrel_def pushpred_def
by auto

(* lemma "(pushrelSame R)\<^sup>* = pushrelSame (R\<^sup>* )"
proof (intro antisym subrelI, goal_cases)
  case (1 p p')
  then obtain m m' s where mm': "p = push m s" "p' = push m' s"
    apply (induct, auto)
    by (metis push_pop, metis push_inj pushrelSame_inE)
  show ?case using 1
  proof (induct)
    case base
    have "(m,m) \<in> R\<^sup>*" by simp
    then show ?case using mm' by (simp add: pushrelSame_in_eq)
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
    then show ?case 
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

(*
lemma push_pop_one: "\<exists>!s. push (pop m) s = m"
using push_pop push_inj
by metis
*)

lemma "poppable s P \<Longrightarrow> pushed P \<subseteq> {s}"
proof
  assume poppable: "poppable s P"
  fix x assume "x \<in> pushed P"
  then obtain p where p: "p \<in> P" "p = push (pop p) x" by auto
  then obtain m where m: "p = push m s" using poppable poppable_inE by blast
  have "x = s" using p m push_inj by metis
  thus "x \<in> {s}" by simp
qed

(*
lemma "pushed P \<subseteq> {s} \<Longrightarrow> poppable s P"
proof -
  assume "pushed P \<subseteq> {s}"
  then consider "pushed P = {}" | "pushed P = {s}" by auto
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis using pushed_empty[of P] by simp
  next
    case 2
    then show ?thesis
    proof (intro antisym, goal_cases)
      case 1
      then have "P \<subseteq> pushpred s (poppred' s P)"
        using pushed_set_supset by force
      then show ?case using pushpred_mono[OF poppred'_subset] by fast
    next
      case 2
      then show ?case unfolding pushed_def pushpred_def poppred_def
        by clarsimp (metis (mono_tags, lifting) mem_Collect_eq push_pop singleton_iff)
    qed  
  qed
qed*)

lemma [simp]:
  "pushpredAll {} = {}"
  by (auto simp: pushpredAll_def)

abbreviation (input) uncapBeh where
"uncapBeh s B \<equiv> pushrel s B" 

abbreviation (input) capGuar where
"capGuar G \<equiv> poprel G"

abbreviation (input) uncapGuar where
"uncapGuar G \<equiv> pushrelAll G"

abbreviation (input) uncapPred where
"uncapPred s P \<equiv> pushpred s P"

abbreviation (input) capPred where
"capPred P \<equiv> poppred P"

abbreviation (input) uncapRely where
"uncapRely R \<equiv> pushrelSame R"


end