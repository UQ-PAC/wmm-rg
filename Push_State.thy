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

context state
begin

section \<open>Operations on predicates and relations\<close>

definition pushpred :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"pushpred s P = {push m s |m. m \<in> P}"

definition poppred :: "'a set \<Rightarrow> 'a set" where
"poppred P = {popl m |m. m \<in> P}"

(* rarely used except in specific proof steps which require
showing something is inside a pushrelAll or similar. *)
(* definition pushpredAll :: "'a set \<Rightarrow> 'a set" where
"pushpredAll P \<equiv> {push m s |m s. m \<in> P}" *)


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


subsection \<open>Inverses\<close>

lemma push_poprelAll [simp]: "pushrelAll (poprel G) = G"
unfolding poprel_def pushrelAll_def
oops

lemma pop_pushrelAll [simp]: "poprel (pushrelAll G) = G"
unfolding poprel_def pushrelAll_def
by auto (metis popl_push)

lemma pop_pushrelSame [simp]: "poprel (pushrelSame G) = G"
unfolding poprel_def pushrelSame_def
by auto (metis popl_push)

text \<open>Pop a previously pushed predicate or relation.\<close>

lemma pop_pushpred [simp]: "poppred (pushpred s P) = P"
unfolding poppred_def pushpred_def by force

lemma pop_pushrel [simp]: "poprel (pushrel s R) = R"
unfolding poprel_def pushrel_def by force

text \<open>These push after pop lemmas are *suspicious*...\<close>

lemma push_poppred [simp]: "pushpred s (poppred P) = P"
unfolding poppred_def pushpred_def 
oops

lemma push_poprel [simp]: "pushrel s (poprel R) = R"
unfolding poprel_def pushrel_def
oops


subsection \<open>Monotonicity\<close>

lemma pushpred_mono [simp]: "P \<subseteq> P' \<Longrightarrow> pushpred s P \<subseteq> pushpred s P'"
unfolding pushpred_def by auto

lemma poppred_mono [simp]: "P \<subseteq> P' \<Longrightarrow> poppred P \<subseteq> poppred P'"
unfolding poppred_def by auto

(* lemma pushpredAll_mono [simp]: "P \<subseteq> P' \<Longrightarrow> pushpredAll P \<subseteq> pushpredAll P'"
unfolding pushpredAll_def by auto *)

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

lemma poprel_relcomp [simp]: "poprel (G O G') \<subseteq> poprel G O poprel G'"
unfolding poprel_def
by auto

lemma pushrelAll_relcomp [simp]: "pushrelAll (G O G') = pushrelAll G O pushrelAll G'"
unfolding pushrelAll_def
by (auto, blast, metis popl_push relcomp.relcompI)

subsubsection \<open>Special cases for popping a relational composition of pushes\<close>

lemma poprel_relcomp_pushrel1 [simp]: "poprel (pushrel s G O pushrelSame G') = G O G'"
unfolding poprel_def pushrel_def pushrelSame_def
by auto (metis popl_push relcomp.simps, force)

lemma poprel_relcomp_pushrel2 [simp]: "poprel (pushrel s G O pushrelAll G') = G O G'"
unfolding poprel_def pushrel_def pushrelAll_def
by auto (metis popl_push relcomp.simps, force)

lemma poprel_relcomp_pushrelSame [simp]: "poprel (pushrelSame G O pushrelSame G') = G O G'"
unfolding poprel_def pushrelSame_def
by auto (metis popl_push relcomp.simps, force)

lemma poprel_relcomp_pushrelAll [simp]: "poprel (pushrelAll G O pushrelAll G') = G O G'"
unfolding poprel_def pushrelAll_def
by auto (metis popl_push relcomp.simps, force)

lemma poprel_relcomp_pushpred [simp]: "poprel (Id_on (pushpred s P) O pushrel s P') = Id_on P O P'"
unfolding poprel_def pushpred_def pushrel_def
by auto (metis Id_on_iff popl_push relcompI, force)

lemma pushrel_relcomp_id: "pushrel s (Id_on P O P') = Id_on (pushpred s P) O pushrel s P'"
unfolding pushrel_def pushpred_def
by auto (metis Id_onI popl_push relcompI)

(* lemma pushpredAll_supset: "P \<subseteq> pushpredAll (poppred P)"
unfolding pushpredAll_def poppred_def 
by clarsimp (metis push_popl) *)

lemma pushrelAll_poprel_supset: "R \<subseteq> pushrelAll (poprel R)"
unfolding pushrelAll_def poprel_def
by clarsimp (metis push_popl)

subsection \<open>Intersection\<close>

lemma pushpred_inter [simp]: "pushpred s (P \<inter> P') = pushpred s P \<inter> pushpred s P'"
unfolding pushpred_def
by auto (metis popl_push)

lemma poppred_inter [simp]: "poppred (P \<inter> P') \<subseteq> poppred P \<inter> poppred P'"
unfolding poppred_def
by auto

lemma poppred_inter2 [simp]: "poppred (pushpred s P \<inter> pushpred s P') = P \<inter> P'"
unfolding poppred_def pushpred_def
by auto (metis local.popl_push)+

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

lemma pushpred_im_in_im_pushrel:
  "pushpred s (R `` P) \<subseteq> pushrelSame R `` pushpred s P"
unfolding pushrelSame_def pushpred_def 
by fast


text \<open>Correspondences between predicates and Id_on.\<close>

lemma Id_in_pushrelAll_poppred: "Id_on G \<subseteq> pushrelAll (Id_on (poppred G))"
proof -
  have "G \<subseteq> {push m s |m s. m \<in> poppred G}"
    unfolding poppred_def 
    by clarsimp (metis local.push_popl)
  thus ?thesis using Id_on_eqI 
    unfolding pushrelAll_def by clarsimp blast
qed

lemma poppred_eq_poprel: "Id_on (poppred a) = poprel (Id_on a)"
unfolding poppred_def poprel_def by auto

lemma poppred_in_poprel: "m \<in> poppred G \<Longrightarrow> (m,m) \<in> poprel (Id_on G)"
using poppred_eq_poprel by fast


end

end