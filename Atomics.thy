theory Atomics
  imports Syntax State
begin

chapter \<open>Atomic Actions\<close>

text \<open>
Describe concepts the logic must know about atomic instructions. 
\<close>

section \<open>Atomic Properties\<close>

text \<open>Weakest precondition of a basic instruction, based on the locale's 
      verification conditions and behaviours.\<close>
abbreviation wp\<^sub>\<alpha> :: "('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp\<^sub>\<alpha> \<alpha> Q \<equiv> wp (vc \<alpha>) (beh \<alpha>) Q"

text \<open>Specification check, ensuring an instruction conforms to a relation\<close>
abbreviation guar\<^sub>\<alpha> :: "('a,'b) basic \<Rightarrow> 'b rpred \<Rightarrow> bool"
  where "guar\<^sub>\<alpha> \<alpha> G \<equiv> guar (vc \<alpha>) (beh \<alpha>) G"

section \<open>Atomic Rule\<close>

text \<open>Rule for an atomic operation\<close>
definition atomic_rule :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> ('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>A _ {_} _" [65,0,0,0,65] 65)
  where "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<equiv> P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q \<and> guar\<^sub>\<alpha> \<alpha> G \<and> stable R P \<and> stable R Q"

lemma atomicI [intro]:
  assumes "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "guar\<^sub>\<alpha> \<alpha> G" "stable R P" "stable R Q"
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
using assms
by (auto simp add: atomic_rule_def)

(* 
lemma thr_atomic:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  shows "thr\<^sub>R op R,thr\<^sub>G op G \<turnstile>\<^sub>A thr\<^sub>P op l P {thr\<^sub>\<alpha> op l l' \<alpha>} thr\<^sub>P op l' Q"
using assms
unfolding atomic_rule_def thr\<^sub>\<alpha>_def 
(* by (simp add: thr_stable thr_wp thr_guar) *)
oops
 *)

subsection \<open>Derived Properties\<close>

text \<open>the postcondition may be weakened (i.e. made larger, accepting more states).\<close>
lemma wp\<^sub>\<alpha>_mono: "Q \<subseteq> Q' \<Longrightarrow> wp\<^sub>\<alpha> \<alpha> Q \<subseteq> wp\<^sub>\<alpha> \<alpha> Q'"
unfolding wp_def by auto

text \<open>Re-establish an atomic judgement over a stronger stable precondition\<close>
lemma atomic_pre:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "P' \<subseteq> P" "stable R P'"
  shows "R,G \<turnstile>\<^sub>A P' {\<alpha>} Q"
  using assms unfolding atomic_rule_def by fast

text \<open>Strengthen the rely and weaken the guarantee for an atomic judgement\<close>
lemma atomic_conseqI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "R' \<subseteq> R" "G \<subseteq> G'"
  shows "R',G' \<turnstile>\<^sub>A P {\<alpha>} Q"
  using assms unfolding atomic_rule_def guar_def by blast

text \<open>Atomic judgements over the same instruction can be combined\<close>
lemma actomic_conjI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P\<^sub>1 {\<alpha>} Q\<^sub>1" "R,G  \<turnstile>\<^sub>A P\<^sub>2 {\<alpha>} Q\<^sub>2"
  shows "R,G \<turnstile>\<^sub>A P\<^sub>1 \<inter> P\<^sub>2 {\<alpha>} Q\<^sub>1 \<inter> Q\<^sub>2"
  using assms unfolding atomic_rule_def wp_def stable_def by blast

text \<open>Add an invariant across an atomic judgement\<close>
lemma atomic_invI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  assumes "stable R\<^sub>2 I" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>A P \<inter> I {\<alpha>} Q \<inter> I"
  unfolding atomic_rule_def
proof (safe, goal_cases)
  case (1 m)
  hence "{(m,m'). m \<in> P \<inter> vc \<alpha> \<and> (m,m') \<in> beh \<alpha>} \<subseteq> R\<^sub>2\<^sup>=" "m \<in> vc \<alpha>"
    using assms(1,3) by (auto simp: wp_def guar_def atomic_rule_def)
  hence "m \<in> wp\<^sub>\<alpha> \<alpha> I" using assms(2) 1 by (auto simp: wp_def stable_def)
  moreover have "m \<in> wp\<^sub>\<alpha> \<alpha> Q" using 1 assms(1) by (auto simp: atomic_rule_def wp_def)
  ultimately show ?case by (auto simp: wp_def)
qed (insert assms, auto simp: atomic_rule_def wp_def)

text \<open>Atomic rule for a false precondition\<close>
lemma atomic_falseI [intro]:
  assumes "guar\<^sub>\<alpha> \<beta> G"
  shows "R,G \<turnstile>\<^sub>A {} {\<beta>} {}"
  using assms unfolding atomic_rule_def by auto

(*---- new: *)

text \<open> Stabilising P over R \<close>

(*  "r `` s = {y. \<exists>x\<in>s. (x, y) \<in> r}"  *)

definition stabilise :: "'b rel \<Rightarrow> 'b set \<Rightarrow> 'b set" where
"stabilise R P \<equiv> P \<union> R\<^sup>+ `` P"

lemma stabilise_rtrancl: "stabilise R P = (R\<^sup>*) `` P"
unfolding stabilise_def
by (simp add: Un_Image Un_commute rtrancl_trancl_reflcl)

lemma stable_stabilise: "stable R (stabilise R P)"
unfolding stable_rel stabilise_def
by auto (metis ImageI Transitive_Closure.trancl_into_trancl)

lemma stabilise_supset: "P \<subseteq> stabilise R P"
unfolding stabilise_def
by auto

lemma stabilise_stable: "stable R P \<Longrightarrow> stabilise R P = P"
unfolding stable_rel stabilise_def
by (erule Image_closed_trancl')

lemma stabilise_inter_P: "stabilise R (P1 \<inter> P2) \<subseteq> stabilise R P1 \<inter> stabilise R P2"
unfolding stabilise_def
by auto

lemma stabilise_inter_R1: "stabilise (R1 \<inter> R2) P \<subseteq> stabilise R1 P"
unfolding stabilise_def
by safe (metis Int_lower1 rev_ImageI trancl_mono)

lemma stabilise_inter_R2: "stabilise (R1 \<inter> R2) P \<subseteq> stabilise R2 P"
by (metis stabilise_inter_R1 Int_commute)


lemma stabilise_inter_RP: "stabilise (R1 \<inter> R2) (P1 \<inter> P2) \<subseteq> stabilise R1 P1 \<inter> stabilise R2 P2"
unfolding stabilise_def
by (safe; meson Image_iff inf_sup_ord(1,2) trancl_mono)

lemma stabilise_mono: "P \<subseteq> P' \<Longrightarrow> stabilise R P \<subseteq> stabilise R P'"
unfolding stabilise_def
by auto

lemma stabilise_mono_R: "R \<subseteq> R' \<Longrightarrow> stabilise R P \<subseteq> stabilise R' P"
by (metis inf.orderE stabilise_inter_R2)

lemma stabilise_mono_RP: "R \<subseteq> R' \<Longrightarrow> P \<subseteq> P' \<Longrightarrow> stabilise R P \<subseteq> stabilise R' P'"
by (metis stabilise_mono stabilise_mono_R subset_trans)

lemma stabilise_pushrel: "stabilise (pushrelSame R) (pushpred s P) = pushpred s (stabilise R P)"
unfolding stabilise_def
by (simp add: pushpred_relimage pushpred_union pushrelSame_trancl)

lemma stabilise_atomic: "R,G \<turnstile>\<^sub>A P {c} Q \<Longrightarrow> R,G \<turnstile>\<^sub>A stabilise R P {c} Q"
unfolding atomic_rule_def
by (simp add: stabilise_stable)

lemma stabilise_atomic_post: "R,G \<turnstile>\<^sub>A P {c} Q \<Longrightarrow> R,G \<turnstile>\<^sub>A P {c} stabilise R Q"
unfolding atomic_rule_def
by (simp add: stabilise_stable)

lemma stabilise_min: "P \<subseteq> P' \<Longrightarrow> stable R P' \<Longrightarrow> stabilise R P \<subseteq> P'"
unfolding stabilise_rtrancl
by auto (metis stable_transitive subset_iff)

lemma [simp]:
  "stabilise R {} = {}"
  by (auto simp: stabilise_def)


text \<open>Manually computing the strongest postcondition which might hold.\<close>

(*  "r `` s = {y. \<exists>x\<in>s. (x, y) \<in> r}"  *)

definition sp :: "('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> 'b pred" where
  "sp \<alpha> P \<equiv> beh \<alpha> `` (P)"

lemma wp_sp: "P \<subseteq> vc \<alpha> \<Longrightarrow> P \<subseteq> wp\<^sub>\<alpha> \<alpha> (sp \<alpha> P)"
unfolding sp_def wp_def
by auto

lemma sp_wp: "sp \<alpha> (wp\<^sub>\<alpha> \<alpha> Q) \<subseteq> Q"
unfolding sp_def wp_def
by auto

lemma sp_mono: "P \<subseteq> P' \<Longrightarrow> sp \<alpha> P \<subseteq> sp \<alpha> P'"
unfolding sp_def by auto

lemma sp_pushbasic: "sp (pushbasic s s' \<alpha>) (pushpred s P) = pushpred s' (sp \<alpha> P)" 
unfolding pushpred_def pushrel_def sp_def
by auto (metis ImageI pop_push)

end