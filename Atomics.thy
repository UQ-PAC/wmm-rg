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

lemma wp_relcomp:
  assumes "(Id_on P) O ((Id_on (vc \<alpha>) O (beh \<alpha>))) \<subseteq> (P \<times> Q)" "P \<subseteq> vc \<alpha>" 
  shows  "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" using assms wp_def 
  using  Id_onI IntE IntI inf.orderE mem_Collect_eq mem_Sigma_iff 
        relcomp.relcompI subsetI  by (smt (verit, del_insts))
 
text \<open>Re-establish an atomic judgement over a stronger stable precondition\<close>
lemma atomic_pre:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "P' \<subseteq> P" "stable R P'"
  shows "R,G \<turnstile>\<^sub>A P' {\<alpha>} Q"
  using assms unfolding atomic_rule_def by fast

lemma atomic_post:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "Q \<subseteq> Q'" "stable R Q'"
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} Q'"
  using assms wp\<^sub>\<alpha>_mono unfolding atomic_rule_def by fast

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

text \<open> P stabilised over transitive closure G is maintained \<close>


lemma "P \<subseteq> (stabilise (G\<^sup>*) P)"
unfolding stabilise_def  wp_def by auto

lemma stabilise_rtrancl_mono:
 "(stabilise (G) P) \<subseteq> (stabilise (G\<^sup>*) P)" using stabilise_mono 
  by (simp add: stabilise_rtrancl)


lemma atomic_stab_pre [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "stable R (stabilise (G\<^sup>*) P)"
  shows "R,(G\<^sup>*) \<turnstile>\<^sub>A P {\<alpha>} (stabilise (G\<^sup>*) P)"
proof -
  have a0:"P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" using assms atomic_rule_def by fast
  have a1a:"stable R P" using assms atomic_rule_def by fast
  have a1:"guar\<^sub>\<alpha> \<alpha> G" using assms atomic_rule_def by blast
  have a2:"(vc \<alpha>) \<subseteq> {m. (\<forall> m'. ((m,m') \<in> (beh \<alpha>) \<longrightarrow> (m,m') \<in> G))}" 
     using assms guar2.simps guar_def atomic_rule_def case_prodI mem_Collect_eq subset_eq 
     by (smt (verit))
  have a3:"P \<subseteq> (vc \<alpha>) \<inter> {m. (\<forall> m'. ((m,m') \<in> (beh \<alpha>) \<longrightarrow> m' \<in> Q))}" using a0 wp_def by force 
  have a4:"P \<subseteq> {m. (\<forall> m'. ((m,m') \<in> (beh \<alpha>) \<longrightarrow> (m,m') \<in> G))} \<inter> 
                {m. (\<forall> m'. ((m,m') \<in> (beh \<alpha>) \<longrightarrow> m' \<in> Q))}" using a2 a3 by auto
  have a5:"P \<subseteq> {m. (\<forall> m'. ((m,m') \<in> (beh \<alpha>) \<longrightarrow> m' \<in> (stabilise (G) P)))}"
      using assms a1 stabilise_def stabilise_supset stable_rel stable_stabilise subset_eq
      by (smt (verit) ImageI a4 le_inf_iff mem_Collect_eq)
  have a6:"P \<subseteq> (vc \<alpha>) \<inter> {m. (\<forall> m'. ((m,m') \<in> (beh \<alpha>) \<longrightarrow> m' \<in> (stabilise (G) P)))}" 
      using a3 a1 a2 a5 by simp
    have a7:"P \<subseteq>  wp\<^sub>\<alpha> \<alpha> (stabilise (G) P)" using a6 wp_def by fast
    have a8:"P \<subseteq>  wp\<^sub>\<alpha> \<alpha> (stabilise (G\<^sup>*) P)" 
       using a7 stabilise_rtrancl_mono wp\<^sub>\<alpha>_mono by (simp add: stabilise_rtrancl)
     thus ?thesis using a1 a1a assms stable_stabilise atomic_rule_def by auto
   qed


lemma atomic_stab_guarTrans [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "stable R P" "stable G P" 
  shows "R,(G\<^sup>*) \<turnstile>\<^sub>A P {\<alpha>} P"
  using assms atomic_stab_pre 
  by (metis stabilise_rtrancl stabilise_stable stable_rel subset_refl)

lemma atomic_stab_guar:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "stable R P" "stable G P" 
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} P"
  using assms by (metis atomic_rule_def atomic_stab_guarTrans)


text \<open>Manually computing the strongest postcondition which might hold.\<close>

(*  "r `` s = {y. \<exists>x\<in>s. (x, y) \<in> r}"  *)

definition sp :: "('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> 'b pred" where
  "sp \<alpha> P \<equiv> beh \<alpha> `` (P)"


lemma wp_sp: "P \<subseteq> vc \<alpha> \<Longrightarrow> P \<subseteq> wp\<^sub>\<alpha> \<alpha> (sp \<alpha> P)"
unfolding sp_def wp_def
by auto

lemma wp_spR: "P \<subseteq> vc \<alpha> \<Longrightarrow> P \<subseteq> wp\<^sub>\<alpha> \<alpha> (stabilise R (sp \<alpha> P))"
  by (metis Image_subset_eq le_infI sp_def stabilise_supset wp_rel)

lemma sp_wp: "sp \<alpha> (wp\<^sub>\<alpha> \<alpha> Q) \<subseteq> Q"
unfolding sp_def wp_def
by auto

lemma sp_mono: "P \<subseteq> P' \<Longrightarrow> sp \<alpha> P \<subseteq> sp \<alpha> P'"
unfolding sp_def by auto

lemma sp_pushbasic: "sp (pushbasic s s' \<alpha>) (pushpred s P) = pushpred s' (sp \<alpha> P)" 
unfolding pushpred_def pushrel_def sp_def
by auto (metis ImageI pop_push)


text \<open>Definitions and lemmas for capturing guarantee and stability properties.\<close>

lemma stable_cap: "stable (capRely R) (capPred s P) \<Longrightarrow> stable R P"
unfolding stable_def pushrelSame_def pushpred_def
by (auto, metis pop_push)

(*
lemma stable_mix: "stable (pushrelSame R) M \<Longrightarrow> stable R (poppred M)"
unfolding stable_def pushrelSame_def poppred_def
by auto (metis pop_push push_pop) *)

lemma stable_pushrelSame: "stable R P \<Longrightarrow> stable (pushrelSame R) (pushpred s P)"
unfolding stable_rel
using pushpred_relimage pushpred_mono
by metis

lemma stable_pushrelAll: "stable R P \<Longrightarrow> stable (pushrelAll R) (pushpredAll P)"
unfolding stable_rel
using pushpredAll_relimage pushpredAll_mono
by blast


lemma guar\<^sub>\<alpha>_rel: "guar\<^sub>\<alpha> \<alpha> G = (Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G)"
unfolding guar_def by fast


lemma guar_capE:
  "guar\<^sub>\<alpha> (pushbasic s s' \<alpha>) (capGuar G) \<Longrightarrow> guar\<^sub>\<alpha> \<alpha> G"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume assms: "Id_on (vc (pushbasic s s' \<alpha>)) O beh (pushbasic s s' \<alpha>) \<subseteq> capGuar G"
  have "uncapGuar (Id_on (capPred s (vc \<alpha>)) O capBeh s s' (beh \<alpha>)) = Id_on (vc \<alpha>) O beh \<alpha>"
    by (simp add: poprel_relcomp_pushpred)
  thus "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
    using poprel_mono[OF assms] by simp
qed


lemma guar_capI:
  "guar\<^sub>\<alpha> \<alpha> G \<Longrightarrow> guar\<^sub>\<alpha> (pushbasic s s' \<alpha>) (capGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
  hence subset: "pushrel s s' (Id_on (vc \<alpha>) O beh \<alpha>) \<subseteq> pushrel s s' G"
    by simp
  have "pushrel s s' (Id_on (vc \<alpha>) O beh \<alpha>) = Id_on (pushpred s (vc \<alpha>)) O pushrel s s' (beh \<alpha>)"
    by (rule pushrel_relcomp_id)
  hence "Id_on (pushpred s (vc \<alpha>)) O pushrel s s' (beh \<alpha>) \<subseteq> pushrel s s' G" 
    using subset by simp
  thus "Id_on (vc (pushbasic s s' \<alpha>)) O beh (pushbasic s s' \<alpha>) \<subseteq> capGuar G"
    using pushrel_in_pushrelAll[of s s'] by auto
qed

(*
lemma guar_mix:
  assumes "\<forall>s s'. guar\<^sub>\<alpha> (popbasic s s' \<alpha>) G"
  shows "guar\<^sub>\<alpha> \<alpha> (uncapGuar G)"
  unfolding guar\<^sub>\<alpha>_rel Id_on_def poprel'_def poppred'_def 
proof (clarsimp)
  fix m\<^sub>1 m\<^sub>2
  assume a: "(m\<^sub>1, m\<^sub>2) \<in> beh \<alpha>" "m\<^sub>1 \<in> vc \<alpha>"
  obtain s\<^sub>1 s\<^sub>2 where s: "m\<^sub>1 = push (pop m\<^sub>1) s\<^sub>1" "m\<^sub>2 = push (pop m\<^sub>2) s\<^sub>2" using push_pop by metis+
  hence a': "(push (pop m\<^sub>1) s\<^sub>1, push (pop m\<^sub>2) s\<^sub>2) \<in> beh \<alpha>" "push (pop m\<^sub>1) s\<^sub>1 \<in> vc \<alpha>"
    using a by simp+
  hence "(pop m\<^sub>1, pop m\<^sub>2) \<in> G"
    using assms unfolding guar\<^sub>\<alpha>_rel poprel'_def poppred'_def guar_def by auto
  thus "(m\<^sub>1, m\<^sub>2) \<in> pushrelAll G" using s by (auto simp: pushrelAll_def)
qed*)

(*
lemma guar_capE:
  "guar\<^sub>\<alpha> (popbasic \<alpha>) (capGuar G) \<Longrightarrow> guar\<^sub>\<alpha> \<alpha> G"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc (popbasic \<alpha>)) O beh (popbasic \<alpha>) \<subseteq> capGuar G"
  hence "uncapGuar (Id_on (capPred (vc \<alpha>))) O beh \<alpha> \<subseteq> G"
  
  thus "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
    using Id_in_pushrelAll_poppred by fast
oops

lemma guar_capI:
  "guar\<^sub>\<alpha> \<alpha> G \<Longrightarrow> guar\<^sub>\<alpha> (popbasic \<alpha>) (capGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
  hence "poprel (Id_on (vc \<alpha>) O beh \<alpha>) \<subseteq> poprel G" by simp
  hence "poprel (Id_on (vc \<alpha>)) O poprel (beh \<alpha>) \<subseteq> poprel G"
    using poprel_relcomp poprel_mono 
  moreover have "Id_on (capPred (vc \<alpha>)) = capGuar (Id_on (vc \<alpha>))"
    using poppred_eq_poprel by auto
  ultimately show "Id_on (vc (popbasic \<alpha>)) O beh (popbasic \<alpha>) \<subseteq> capGuar G"
    by auto
oops*)

(*
text \<open>If P satisfies the wp of a pushbasic, then it must have had 's' pushed onto it.\<close>
lemma wp_pushbasic_poppable:
  assumes "P \<subseteq> wp\<^sub>\<alpha> (pushbasic s s' \<alpha>) Q"
  shows "poppable s P"
proof -
  have "P \<subseteq> Domain (pushrel s s' (beh \<alpha>))" using assms unfolding wp_rel by simp
  hence "P \<subseteq> pushpred s (Domain (beh \<alpha>))" by (simp add: domain_pushrel)
  thus ?thesis by (rule pushpred_poppable)
qed

lemma atomic_poppable:
  assumes "R,G \<turnstile>\<^sub>A P {pushbasic s s' \<alpha>} Q"
  shows "poppable s P"
using assms unfolding atomic_rule_def
by (intro wp_pushbasic_poppable) auto
*)

text \<open>We can replace an atomic judgement with its strongest postcondition.\<close>
lemma atomic_spI:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} stabilise R (sp \<alpha> P)"
        "stabilise R (sp \<alpha> P) \<subseteq> Q"
unfolding atomic_rule_def
proof (intro conjI)
  have A:
    "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q"
    "guar\<^sub>\<alpha> \<alpha> G"
    "stable R P"
    "stable R Q"
    using assms unfolding atomic_rule_def by auto
  thus "stable R P" "guar\<^sub>\<alpha> \<alpha> G" by auto

  show "stable R (stabilise R (sp \<alpha> P))" by (rule stable_stabilise)
  
  have "P \<subseteq> vc \<alpha>" using A(1) unfolding wp_def by auto
  hence "P \<subseteq> wp\<^sub>\<alpha> \<alpha> (sp \<alpha> P)" by (intro wp_sp, simp)
  moreover have "sp \<alpha> P \<subseteq> stabilise R (sp \<alpha> P)" by (rule stabilise_supset)
  ultimately show "P \<subseteq> wp\<^sub>\<alpha> \<alpha> (stabilise R (sp \<alpha> P))" using wp\<^sub>\<alpha>_mono by fastforce

  have "sp \<alpha> P \<subseteq> Q" using A(1) sp_mono sp_wp by fast
  thus "stabilise R (sp \<alpha> P) \<subseteq> Q" using A(4) stabilise_min[of _ Q] by simp
qed


lemma poppable_stabilise_sp:
  assumes "poppable s P"
  shows "poppable s' (stabilise (pushrelSame R) (sp (pushbasic s s' \<alpha>) P))"
proof -
  define Q' where "Q' = stabilise (pushrelSame R) (sp (pushbasic s s' \<alpha>) P)"
 
  have "sp (pushbasic s s' \<alpha>) P = sp (pushbasic s s' \<alpha>) (pushpred s (poppred P))" 
    using assms by simp
  also have "... = pushpred s' (sp \<alpha> (poppred P))" 
    using sp_pushbasic by fastforce
    
  finally have "Q' = pushpred s' (stabilise R (sp \<alpha> (poppred P)))"
    using stabilise_pushrel unfolding Q'_def by fastforce
  thus "poppable s' Q'" by simp
qed

(*
lemma atomic_pushbasic_postE:
  assumes "pushrelSame R,G \<turnstile>\<^sub>A P {pushbasic s s' \<alpha>} Q"
  obtains Q' where "Q' \<subseteq> Q" "poppable s' Q'" "pushrelSame R,G \<turnstile>\<^sub>A P {pushbasic s s' \<alpha>} Q'"
using assms atomic_spI poppable_stabilise_sp[OF atomic_poppable]
by metis 

lemma poppred_wp_subset: "poppred (wp\<^sub>\<alpha> (pushbasic s s' \<alpha>) (pushpred s' Q)) \<subseteq> wp\<^sub>\<alpha> \<alpha> Q"
unfolding wp_def poppred_def pushpred_def pushrel_def
by auto (metis popl_push)+


lemma atomic_pushbasic: 
  assumes "pushrelSame R,pushrelAll G \<turnstile>\<^sub>A pushpred s P {pushbasic s s' \<alpha>} pushpred s' Q"
  shows "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
unfolding atomic_rule_def
proof (intro conjI)
  have a:
    "pushpred s P \<subseteq> wp\<^sub>\<alpha> (pushbasic s s' \<alpha>) (pushpred s' Q)"
    "guar\<^sub>\<alpha> (pushbasic s s' \<alpha>) (pushrelAll G)"
    "stable (pushrelSame R) (pushpred s P)"
    "stable (pushrelSame R) (pushpred s' Q)"
    using assms unfolding atomic_rule_def by auto
    
  show "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" using poppred_mono[OF a(1)] poppred_wp_subset by fastforce
  show "guar\<^sub>\<alpha> \<alpha> G" using guar_capE[OF a(2)] by simp
  show "stable R P" "stable R Q" using a(3,4) stable_cap by auto
qed*)


lemma help1:
  assumes "stable (pushrelSame R) M"
  shows "stable R (poppred' n M)"
  unfolding stable_def poppred'_def
proof (clarsimp)
  fix m m' assume a: "push m n \<in> M" "(m,m') \<in> R"
  hence "(push m n, push m' n) \<in> pushrelSame R" by (auto simp: pushrelSame_def)
  thus "push m' n \<in> M" using a assms by (auto simp: stable_def) 
qed

lemma help3:
  assumes "guar\<^sub>\<alpha> \<alpha> (pushrelAll G)"
  shows "guar (poppred' s (vc \<alpha>)) (poprel' s s' (beh \<alpha>)) G"
  unfolding guar_def
proof (clarify)
  fix m m' assume a: "m \<in> poppred' s (vc \<alpha>)" "(m,m') \<in> poprel' s s' (beh \<alpha>)" 
  hence "push m s \<in> vc \<alpha>" by (auto simp: poppred'_def)
  moreover have "(push m s, push m' s') \<in> beh \<alpha>" using a by (auto simp: poprel'_def)
  ultimately have "(push m s, push m' s') \<in> pushrelAll G" using assms by (auto simp: guar_def)
  thus "(m,m') \<in> G" unfolding pushrelAll_def using push_inj apply (auto ) by blast
qed

lemma help4:
  assumes "pushpred s P \<subseteq> wp\<^sub>\<alpha> \<alpha> M"
  shows "P \<subseteq> wp\<^sub>\<alpha> (popbasic s s' \<alpha>) (poppred' s' M)"
  unfolding wp_def 
proof (clarify)
  fix x assume "x \<in> P"
  hence "push x s \<in> pushpred s P" by (auto simp: pushpred_def)
  hence "push x s \<in> wp\<^sub>\<alpha> \<alpha> M" using assms by auto
  hence "push x s \<in> vc \<alpha> \<inter> {m. (\<forall>m'. (m, m') \<in> beh \<alpha> \<longrightarrow> m' \<in> M)}" unfolding wp_def by auto
  thus "x \<in> vc (popbasic s s' \<alpha>) \<inter>
              {m. (\<forall>m'. (m, m') \<in> beh (popbasic s s' \<alpha>) \<longrightarrow> m' \<in> (poppred' s' M))}"
    by (auto simp: poppred'_def poprel'_def)
qed

text \<open>
Critical for soundness: atomic judgement with a hidden top-most state fixed to an initial s
can be lifted to a judgement over its observable behaviour fixed to a final internal state s'\<close>
lemma helpa:
  assumes "pushrelSame R,pushrelAll G \<turnstile>\<^sub>A pushpred s P {\<alpha>} M"
  shows "R,G \<turnstile>\<^sub>A P {popbasic s s' \<alpha>} (poppred' s' M)"
proof (unfold atomic_rule_def, intro conjI, goal_cases)
  case 1
  then show ?case using assms help4 unfolding atomic_rule_def by blast
next
  case 2
  then show ?case using assms help3 by (auto simp: atomic_rule_def)
next
  case 3
  then show ?case using assms stable_cap by (auto simp: atomic_rule_def)
next
  case 4
  then show ?case using assms help1 by (auto simp: atomic_rule_def)
qed


end