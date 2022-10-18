theory CaptureReasoning
  imports Atomics
begin

text \<open>Lemmas for capturing stability properties.\<close>

(*         same as: "stable (pushrelSame R) (pushPred s P) \<Longrightarrow> stable R P" *)
lemma stable_uncap: "stable (uncapRely R) (uncapPred s P) \<Longrightarrow> stable R P"
unfolding stable_def pushrelSame_def pushpred_def
by (auto, metis popl_push)

lemma stable_mix: "stable (pushrelSame R) M \<Longrightarrow> stable R (poppred M)"
unfolding stable_def pushrelSame_def poppred_def
by auto (metis popl_push push_popl)

lemma stable_pushrelSame: "stable R P \<Longrightarrow> stable (pushrelSame R) (pushpred s P)"
unfolding stable_rel
using pushpred_relimage pushpred_mono
by metis

lemma stable_pushrelAll: "stable R P \<Longrightarrow> stable (pushrelAll R) (pushpredAll P)"
unfolding stable_rel
using pushpredAll_relimage pushpredAll_mono
by blast

lemma stable_pushrel_iff: "stable R P \<longleftrightarrow> stable (pushrelSame R) (pushpred s P)"
  using stable_uncap stable_pushrelSame by auto

text \<open>Lemmas for capturing guarantee properties.\<close>

lemma guar\<^sub>\<alpha>_rel: "guar\<^sub>\<alpha> \<alpha> G = (Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G)"
unfolding guar_def by fast

(*  "guar\<^sub>\<alpha> (pushbasic s s' \<alpha>) (pushRelAll G) \<Longrightarrow> guar\<^sub>\<alpha> \<alpha> G" ; push on any s s' on G*)
lemma guar_uncapE:
  "guar\<^sub>\<alpha> (pushbasic s s' \<alpha>) (uncapGuar G) \<Longrightarrow> guar\<^sub>\<alpha> \<alpha> G"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume assms: "Id_on (vc (pushbasic s s' \<alpha>)) O beh (pushbasic s s' \<alpha>) \<subseteq> uncapGuar G"
  have "capGuar (Id_on (uncapPred s (vc \<alpha>)) O uncapBeh s s' (beh \<alpha>)) = Id_on (vc \<alpha>) O beh \<alpha>"
    by (simp add: poprel_relcomp_pushpred)
  thus "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
    using poprel_mono[OF assms] by simp
qed

lemma guar_uncapI:
  "guar\<^sub>\<alpha> \<alpha> G \<Longrightarrow> guar\<^sub>\<alpha> (pushbasic s s' \<alpha>) (uncapGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
  hence subset: "pushrel s s' (Id_on (vc \<alpha>) O beh \<alpha>) \<subseteq> pushrel s s' G"
    by simp
  have "pushrel s s' (Id_on (vc \<alpha>) O beh \<alpha>) = Id_on (pushpred s (vc \<alpha>)) O pushrel s s' (beh \<alpha>)"
    by (rule pushrel_relcomp_id)
  hence "Id_on (pushpred s (vc \<alpha>)) O pushrel s s' (beh \<alpha>) \<subseteq> pushrel s s' G" 
    using subset by simp
  thus "Id_on (vc (pushbasic s s' \<alpha>)) O beh (pushbasic s s' \<alpha>) \<subseteq> uncapGuar G"
    using pushrel_in_pushrelAll[of s s'] by auto
qed


lemma guar_mix:
  "guar\<^sub>\<alpha> (popbasic \<alpha>) G \<Longrightarrow> guar\<^sub>\<alpha> \<alpha> (uncapGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc (popbasic \<alpha>)) O beh (popbasic \<alpha>) \<subseteq> G"
  hence "Id_on (poppred (vc \<alpha>)) O poprel (beh \<alpha>) \<subseteq> G" by simp
  hence "pushrelAll (Id_on (poppred (vc \<alpha>))) O pushrelAll (poprel (beh \<alpha>)) \<subseteq> pushrelAll G"       
    by (metis pushrelAll_relcomp pushrelAll_mono)
  moreover have "Id_on (vc \<alpha>) \<subseteq> pushrelAll (Id_on (poppred (vc \<alpha>)))"
    by (simp add: Id_in_pushrelAll_poppred)
  moreover have "beh \<alpha> \<subseteq> pushrelAll (poprel (beh \<alpha>))"
    by (simp add: pushrelAll_poprel_supset)
  ultimately show "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> pushrelAll G" by auto
qed


(* doesn't hold, I think, for the reasons given : 

lemma guar_capE:
  "guar\<^sub>\<alpha> (popbasic \<alpha>) (poprel G) \<Longrightarrow> guar\<^sub>\<alpha> \<alpha> G"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc (popbasic \<alpha>)) O beh (popbasic \<alpha>) \<subseteq> poprel G"
  hence "Id_on (poppred (vc \<alpha>)) O beh (popbasic \<alpha>) \<subseteq> poprel G" by simp
  hence "poprel (Id_on (vc \<alpha>)) O beh (popbasic \<alpha>) \<subseteq> poprel G" by (simp add: poppred_eq_poprel)
  hence "poprel (Id_on (vc \<alpha>)) O poprel (beh \<alpha>) \<subseteq> poprel G" by (simp add: poppred_eq_poprel) 
  hence "poprel ((Id_on (vc \<alpha>)) O (beh \<alpha>)) \<subseteq> poprel G" using poprel_relcomp by blast
(* G \<subseteq> G' \<Longrightarrow> poprel G \<subseteq> poprel G' using poprel_mono; but not the other way around *)
  thus "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
    using Id_in_pushrelAll_poppred (* fails *)
oops
*)

(*  this needs to fix the middle state in (Id O Beh) so that poprel can be pushed 
into the relational comp: problem solved in help3 (Transition_Rules.thy)

lemma guar_capI:
  "guar\<^sub>\<alpha> \<alpha> G \<Longrightarrow> guar\<^sub>\<alpha> (popbasic \<alpha>) (capGuar G)"
unfolding guar\<^sub>\<alpha>_rel
proof -
  assume "Id_on (vc \<alpha>) O beh \<alpha> \<subseteq> G"
  hence "poprel (Id_on (vc \<alpha>) O beh \<alpha>) \<subseteq> poprel G" by simp
(* we have poprel (Id_on P O P') \<subseteq> poprel (Id_on P) O poprel P' using poprel_relcomp 
  but not the other way around *)
  moreover have "Id_on (poppred (vc \<alpha>)) = poprel (Id_on (vc \<alpha>))"
   (* hence this does not hold *)
  ultimately show "Id_on (vc (popbasic \<alpha>)) O beh (popbasic \<alpha>) \<subseteq> capGuar G"
    by sledgehammer
 *)


(*
text \<open>If P satisfies the wp of a pushbasic, then it must have had 's' pushed onto it.\<close>
lemma wp_pushbasic_poppable:
  assumes "P \<subseteq> wp\<^sub>\<alpha> (pushbasic s s' \<alpha>) Q"
  shows "poppable s P"
proof -
  have "P \<subseteq> wp (pushpred s (vc \<alpha>)) (pushrel s s' (beh \<alpha>)) Q" using assms by simp
  have "P \<subseteq>  -((pushrel s s' (beh \<alpha>))\<inverse> `` (-Q))" using wp_rel by (metis assms le_inf_iff snd_conv) 
  have "P \<subseteq>  -((pushrel s s' (beh \<alpha>))\<inverse> `` ({}))" using wp_rel by (simp add: assms le_inf_iff)
this step requires for \<alpha> to be deterministic, and that the reachable states of two
instr do not overlap - see assms for inverse_sets 
  have "P \<subseteq>   (pushrel s s' (beh \<alpha>))\<inverse> `` (UNIV)" using wp_reach by blast
  hence "P \<subseteq> Domain (pushrel s s' (beh \<alpha>))" by auto
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
*)

(*
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
  show "guar\<^sub>\<alpha> \<alpha> G" using guar_uncapE[OF a(2)] by simp
  show "stable R P" "stable R Q" using a(3,4) stable_uncap by auto
qed
*)


end