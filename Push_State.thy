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
  (* assumes popr_push [simp]: "popr (push a b) = b" *)
  assumes push_intro: "\<exists>m. m' = push m s"

context state
begin

section \<open>Operations on predicates and relations\<close>

definition pushpred :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"pushpred s P = {push m s |m. m \<in> P}"

definition poppred :: "'a set \<Rightarrow> 'a set" where
"poppred P = {popl m |m. m \<in> P}"

definition poprel :: "'a rel \<Rightarrow> 'a rel" where
"poprel b = {(popl m,popl m') |m m'. (m,m') \<in> b}" 

definition pushrel :: "'a \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
"pushrel s b = {(push m s,push m' s') |m m' s'. (m,m') \<in> b}" 

definition pushrelSame :: "'a rel \<Rightarrow> 'a rel" where
"pushrelSame R = {(push m s, push m' s) |m m' s. (m,m') \<in> R}"

definition pushrelAll :: "'a rel \<Rightarrow> 'a rel" where
"pushrelAll G = {(push m s, push m' s') |m m' s s'. (m,m') \<in> G}"


section \<open>Lemmas for push/pop on predicates/relations\<close>

subsection \<open>Introduction of pushes\<close>

text \<open>These allow introducing pushes when given arbitrary predicates.\<close>

lemma push_intro_fun: 
  "\<exists>f. m' = push (f m' s) s"
using push_intro
by fast

lemma pushpred_intro:
  "\<exists>P'. P = pushpred s P'"
proof 
  have "m = push (SOME x. m = push x s) s" for m
    using push_intro[of m s] someI_ex by fast
  thus "P = pushpred s {SOME x. m = push x s |m. m \<in> P}"
    unfolding pushpred_def by auto
qed

lemma push_pop_intro: "m \<in> P \<Longrightarrow> push (popl m) s \<in> P"
by (metis popl_push push_intro)

lemma push_pop_intro2: "(m,m') \<in> G \<Longrightarrow> (push (popl m) s, push (popl m') s') \<in> G"
by (metis popl_push push_intro)

subsection \<open>Inverses\<close>

lemma push_poprelAll [simp]: "pushrelAll (poprel G) = G"
unfolding poprel_def pushrelAll_def
by auto (metis local.popl_push local.push_intro)+

lemma pop_pushrelAll [simp]: "poprel (pushrelAll G) = G"
unfolding poprel_def pushrelAll_def
by auto (metis popl_push)


lemma pop_pushpred [simp]: "poppred (pushpred s P) = P"
unfolding poppred_def pushpred_def by force

lemma pop_pushrel [simp]: "poprel (pushrel s R) = R"
unfolding poprel_def pushrel_def by force

text \<open>These push after pop lemmas are *suspicious*...\<close>

lemma push_poppred [simp]: "pushpred s (poppred P) = P"
unfolding poppred_def pushpred_def 
using push_pop_intro by blast

lemma push_poprel [simp]: "pushrel s (poprel R) = R"
unfolding poprel_def pushrel_def
using push_pop_intro2
by auto (metis popl_push push_intro)


subsection \<open>Monotonicity\<close>

lemma pushpred_mono [simp]: "P \<subseteq> P' \<Longrightarrow> pushpred s P \<subseteq> pushpred s P'"
unfolding pushpred_def by auto

lemma poppred_mono [simp]: "P \<subseteq> P' \<Longrightarrow> poppred P \<subseteq> poppred P'"
unfolding poppred_def by auto

lemma poprel_mono [simp]: "G \<subseteq> G' \<Longrightarrow> poprel G \<subseteq> poprel G'"
unfolding poprel_def pushrelAll_def by auto

lemma pushrel_mono [simp]: "G \<subseteq> G' \<Longrightarrow> pushrel s G \<subseteq> pushrel s G'"
unfolding pushrel_def by auto

lemma pushrelSame_mono [simp]: "G \<subseteq> G' \<Longrightarrow> pushrelSame G \<subseteq> pushrelSame G'"
unfolding pushrelSame_def by auto

lemma pushrelAll_mono [simp]: "G \<subseteq> G' \<Longrightarrow> pushrelAll G \<subseteq> pushrelAll G'"
unfolding pushrelAll_def by auto

lemma pushrelAll_eq [simp]: "(pushrelAll G \<subseteq> pushrelAll G') = (G \<subseteq> G')"
using poprel_mono pop_pushrelAll pushrelAll_mono
by metis

subsection \<open>Relation composition\<close>

lemma poprel_relcomp [simp]: "poprel (G O G') = poprel G O poprel G'"
unfolding poprel_def
by auto (metis (mono_tags) popl_push push_intro relcomp.simps)

lemma pushrelAll_relcomp [simp]: "pushrelAll (G O G') = pushrelAll G O pushrelAll G'"
unfolding pushrelAll_def
by (auto, blast, metis popl_push relcomp.relcompI)

subsection \<open>Intersection\<close>

lemma pushpred_inter [simp]: "pushpred s (P \<inter> P') = pushpred s P \<inter> pushpred s P'"
unfolding pushpred_def
by auto (metis popl_push)

lemma poppred_inter [simp]: "poppred (P \<inter> P') = poppred P \<inter> poppred P'"
unfolding poppred_def
by auto (metis popl_push push_intro)

lemma pushrel_inter [simp]: "pushrel s (G \<inter> G') = pushrel s G \<inter> pushrel s G'"
unfolding pushrel_def
by auto (metis popl_push)

lemma pushrelSame_inter [simp]: "pushrelSame (G \<inter> G') = pushrelSame G \<inter> pushrelSame G'"
unfolding pushrelSame_def
by auto (metis popl_push)

lemma pushrelAll_inter [simp]: "pushrelAll (G \<inter> G') = pushrelAll G \<inter> pushrelAll G'"
unfolding pushrelAll_def
by auto (metis popl_push)

subsection \<open>Empty set\<close>

lemma pushpred_empty [simp]: "pushpred s {} = {}"
unfolding pushpred_def by simp

lemma poppred_empty [simp]: "poppred {} = {}"
unfolding poppred_def by simp


lemma poprel_empty [simp]: "poprel {} = {}"
unfolding poprel_def by simp

lemma pushrel_empty [simp]: "pushrel s {} = {}"
unfolding pushrel_def by simp

lemma pushrelSame_empty [simp]: "pushrelSame {} = {}"
unfolding pushrelSame_def by simp

lemma pushrelAll_empty [simp]: "pushrelAll {} = {}"
unfolding pushrelAll_def by simp

subsection \<open>Other properties\<close>

lemma pushrel_in_pushrelAll: "pushrel s G \<subseteq> pushrelAll G"
unfolding pushrel_def pushrelAll_def by fast

text \<open>Correspondences between predicates and Id_on.\<close>

lemma Id_in_pushrelAll_poppred: "Id_on G \<subseteq> pushrelAll (Id_on (poppred G))"
proof -
  have "G \<subseteq> {push m s |m s. m \<in> poppred G}"
    unfolding poppred_def by clarsimp (metis popl_push push_intro)
  thus ?thesis using Id_on_eqI 
    unfolding pushrelAll_def by clarsimp blast
qed

lemma poppred_eq_poprel: "Id_on (poppred a) = poprel (Id_on a)"
unfolding poppred_def poprel_def by auto

lemma poppred_in_poprel: "m \<in> poppred G \<Longrightarrow> (m,m) \<in> poprel (Id_on G)"
using poppred_eq_poprel by fast

end

end