theory CaptureReasoning
  imports Atomics
begin

text \<open>Lemmas for capturing stability properties.\<close>

text \<open>Definitions and lemmas for capturing guarantee and stability properties.\<close>

lemma stable_uncap: "stable (uncapRely R) (uncapPred s P) \<Longrightarrow> stable R P"
unfolding stable_def pushrelSame_def pushpred_def
by (auto, metis pop_push)

lemma stable_mix: "stable (pushrelSame R) M \<Longrightarrow> stable R (poppred M)"
unfolding stable_def pushrelSame_def poppred_def
by auto (metis pop_push push_pop)

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
qed

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
  show "guar\<^sub>\<alpha> \<alpha> G" using guar_uncapE[OF a(2)] by simp
  show "stable R P" "stable R Q" using a(3,4) stable_uncap by auto
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
  then show ?case using assms stable_uncap by (auto simp: atomic_rule_def)
next
  case 4
  then show ?case using assms help1 by (auto simp: atomic_rule_def)
qed

end
