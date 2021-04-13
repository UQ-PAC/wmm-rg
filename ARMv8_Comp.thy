theory ARMv8_Comp
  imports ARMv8_Rules
begin

chapter \<open>ARMv8 Composition Theory\<close>

definition local_op :: "('v,'r,'a) tstate_scheme \<Rightarrow> ('v,'r,'a) tstate_scheme \<Rightarrow> ('v,'r,'a) tstate_scheme"
  where "local_op g lcl \<equiv>  g\<lparr> rg := rg lcl \<rparr>"

definition ARMThread
  where "ARMThread c = Thread local_op (lift\<^sub>c c)"

lemma thr\<^sub>R [simp]:
  "thr\<^sub>R local_op (step\<^sub>R R) = step R"
  unfolding thr\<^sub>R_def step\<^sub>R_def step_def local_op_def by auto

lemma thr\<^sub>G [simp]:
  "thr\<^sub>G local_op (step G) = step G"
  unfolding thr\<^sub>G_def step_def local_op_def by auto

definition univL
  where "univL P \<equiv> (\<lambda>m. \<forall>l. P (m\<lparr> rg := l \<rparr>))"

definition exL
  where "exL P \<equiv> (\<lambda>m. \<exists>l. P (m\<lparr> rg := l \<rparr>))"

lemma [simp]:
  "thr\<^sub>Q local_op (Collect Q) = Collect (exL Q)"
  unfolding exL_def local_op_def thr\<^sub>Q_def by auto

lemma [simp]:
  "thr\<^sub>A local_op (Collect P) = Collect (univL P)"
  unfolding univL_def local_op_def thr\<^sub>A_def by auto

lemma armv8_thread:
  assumes "guar\<^sub>c c G" "wellformed R G Q" "inter (step\<^sub>R R) (step G) (lift\<^sub>c c)" "P \<turnstile>\<^sub>p wp R G c Q"
  shows "step R,step G \<turnstile> Collect (univL P) {ARMThread c} Collect (exL Q)"
proof -
  have a: "R,G \<turnstile>\<^sub>s wp R G c Q {c} Q" using assms wp_valid unfolding valid_def by blast
  have "step R,step G \<turnstile> Collect (univL (wp R G c Q)) {ARMThread c} Collect (exL Q)"
    using rules.thread[OF a assms(3), of local_op] by (simp add: ARMThread_def)
  thus ?thesis
    apply (rule rules.conseq)
    using assms(4) by (auto simp: univL_def pred_defs)
qed

type_synonym ('v,'r,'a) thread = "(('v,'a) rpred \<times> ('v,'a) rpred \<times> ('v,'r,'a) pred \<times> ('v,'r,'a) lang \<times> ('v,'r,'a) pred)"
type_synonym ('v,'r,'a) threads = "('v,'r,'a) thread list"

fun Qs :: "('v,'r,'a) threads \<Rightarrow> ('v,'r,'a) pred"
  where 
    "Qs [] = (\<lambda>m. True)" | 
    "Qs ((R,G,P,c,Q)#t) = (Qs t \<and>\<^sub>p exL Q)"

fun Ps :: "('v,'r,'a) threads \<Rightarrow>('v,'r,'a) pred"
  where 
    "Ps [] = (\<lambda>m. True)" | 
    "Ps ((R,G,P,c,Q)#t) = (Ps t \<and>\<^sub>p univL P)"

fun Rs :: "('v,'r,'a) threads \<Rightarrow> ('v,'a) rpred"
  where
    "Rs [] = (\<lambda>m. True)" |
    "Rs ((R,G,c,Q)#t) = (Rs t \<and>\<^sub>p R)"

fun Gs :: "('v,'r,'a) threads \<Rightarrow> ('v,'a) rpred"
  where
    "Gs [] = (\<lambda>m. False)" |
    "Gs ((R,G,c,Q)#t) = (Gs t \<or>\<^sub>p G)"

fun Cs :: "('v,'r,'a) threads \<Rightarrow> (('v,'r,'a) inst,('v,'r,'a) tstate_scheme) com"
  where 
    "Cs [] = undefined " |
    "Cs [(R,G,P,c,Q)] = ARMThread c" |
    "Cs (c#ts) = Cs [c] || Cs ts"

definition wfs :: "('v,'r,'a) threads \<Rightarrow> bool"
  where "wfs t \<equiv> \<forall>(R,G,P,c,Q) \<in> set t. 
                  wellformed R G Q \<and> 
                  guar\<^sub>c c G \<and> 
                  inter (step\<^sub>R R) (step G) (lift\<^sub>c c) \<and>
                  (P \<turnstile>\<^sub>p wp R G c Q)"

definition rg_comp :: "('v,'r,'a) threads \<Rightarrow> bool"
  where "rg_comp t \<equiv> \<forall>i j. i < length t \<longrightarrow> j < length t \<longrightarrow> i \<noteq> j \<longrightarrow> fst (snd (t ! i)) \<turnstile>\<^sub>p fst (t ! j)"

lemma rg_comp_tailI:
  "rg_comp (a#t) \<Longrightarrow> rg_comp t"
  unfolding rg_comp_def apply auto
  by (metis (no_types, lifting) Ex_less_Suc Suc_inject less_trans_Suc nth_Cons_Suc)

lemma Gs_rel:
  assumes "\<forall>i. i < length t \<longrightarrow> step (fst (snd ((t :: ('v,'r,'a) threads) ! i))) \<subseteq> ((step R) :: ('v,'r,'a) tstate_scheme rel)"
  shows "step (Gs t) \<subseteq> step R"
  using assms
proof (induct t)
  case Nil
  then show ?case by (auto simp: step_def)
next
  case (Cons a t)
  obtain R' G c Q where a [simp]: "a = (R',G,c,Q)" by (cases a, auto)
  have i: "\<And>i. i < length (a # t) \<Longrightarrow> step (fst (snd ((a # t) ! i))) \<subseteq> ((step R) :: ('v,'r,'a) tstate_scheme rel)"
    using Cons(2) by auto

  have b: "\<forall>i. i <length t \<longrightarrow> step (fst (snd (t ! i))) \<subseteq> ((step R) :: ('v,'r,'a) tstate_scheme rel)" 
          "step G \<subseteq> ((step R) :: ('v,'r,'a) tstate_scheme rel)"
    apply (intro allI impI)
    apply (subgoal_tac "step (fst (snd ((a # t) ! Suc i))) \<subseteq> step R")
    apply auto[1]
    apply (rule i)
    apply auto
    using i[of 0]
    apply auto
    done

  show ?case using Cons(1)[OF b(1)] b(2)
    apply (auto simp: step_def pred_defs)
    sorry
qed

lemma Rs_rel:
  assumes "\<forall>i. i < length t \<longrightarrow> (step G  :: ('v,'r,'a) tstate_scheme rel) \<subseteq> step (fst ( ((t :: ('v,'r,'a) threads) ! i)))"
  shows "step G \<subseteq> step (Rs t)"
  using assms
proof (induct t)
  case Nil
  then show ?case by (auto simp: step_def)
next
  case (Cons a t)
  obtain R G' c Q where a [simp]: "a = (R,G',c,Q)" by (cases a, auto)
  have i: "\<And>i. i < length (a # t) \<Longrightarrow> ((step G) :: ('v,'r,'a) tstate_scheme rel) \<subseteq> step  (fst ((a # t) ! i))"
    using Cons(2) by auto

  have b: "\<forall>i. i <length t \<longrightarrow> ((step G) :: ('v,'r,'a) tstate_scheme rel) \<subseteq> step  (fst (t ! i))"
          "step G \<subseteq> ((step R) :: ('v,'r,'a) tstate_scheme rel)"
    apply (intro allI impI)
    using i apply force using i by force

  show ?case using Cons(1)[OF b(1)] b(2)
    apply (auto simp: step_def pred_defs)
    sorry
qed

lemma rg_comp_Gs:
  assumes "rg_comp ((R,G,P,c,Q)#t)" 
  shows "step (Gs t) \<subseteq> step R"
proof -
  have "\<forall>i. i < length t \<longrightarrow> fst (snd (t ! i)) \<turnstile>\<^sub>p R"
    using assms unfolding rg_comp_def sorry
  hence "\<forall>i. i < length t \<longrightarrow> step (fst (snd (t ! i))) \<subseteq> step R"
    unfolding step_def pred_defs by auto
  thus ?thesis using Gs_rel by blast
qed

lemma rg_comp_Rs:
  assumes "rg_comp ((R,G,P,c,Q)#t)" 
  shows "step G \<subseteq> step (Rs t)"
proof -
  have "\<forall>i. i < length t \<longrightarrow> G \<turnstile>\<^sub>p fst (t ! i)"
    using assms unfolding rg_comp_def by force
  hence "\<forall>i. i < length t \<longrightarrow> step G \<subseteq> step (fst (t ! i))"
    unfolding step_def pred_defs by auto
  thus ?thesis using Rs_rel by blast
qed

lemma armv8_parallel:
  assumes "length t \<noteq> 0" "wfs t" "rg_comp t"
  shows "step (Rs t), step (Gs t) \<turnstile> Collect (Ps t) {Cs t} Collect (Qs t)"
  using assms
proof (induct t)
  case (Cons a t)
  obtain R G P c Q where a [simp]: "a = (R,G,P,c,Q)" by (cases a, auto)
  have wf: "guar\<^sub>c c G" "wellformed R G Q" 
           "inter (step\<^sub>R R) (step G) (lift\<^sub>c c)" "wfs t"
           "P \<turnstile>\<^sub>p  wp R G c Q"
    using Cons(3) by (auto simp: wfs_def)
  have j: "step R,step G \<turnstile> Collect (univL P) {ARMThread c} Collect (exL Q)" 
    using armv8_thread[OF wf(1,2,3,5)] by blast
  have c: "step (Gs t) \<subseteq> step R" "step G \<subseteq> step (Rs t)"
    using rg_comp_Rs rg_comp_Gs Cons sorry (* apply fastforce
    using rg_comp_Rs rg_comp_Gs Cons apply fastforce
    done *)
  show ?case 
  proof (cases "t = []")
    case True
    then show ?thesis using j by (auto simp: exL_def pred_defs)
  next
    case False
    hence t: "step (Rs t),step (Gs t) \<turnstile> Collect (Ps t) {Cs t} Collect (Qs t)" 
      using Cons wf(4) rg_comp_tailI by blast
    have [simp]: "Cs ((R, G, P, c, Q) # t) = ARMThread c || Cs t" using False by (cases t) auto
    show ?thesis
      apply clarsimp
      apply (rule rules.conseq[OF rules.par[OF j t c]])
      by (auto simp: step_def o_def exL_def pred_defs)
  qed
qed auto

lemma armv8_sound:
  assumes "length t \<noteq> 0" "wfs t" "rg_comp t"
  shows "validity (Cs t) (Collect (Ps t)) (step (Rs t)) (step (Gs t)) (Collect (Qs t))"
proof -
  have "step (Rs t), step (Gs t) \<turnstile> Collect (Ps t) {Cs t} Collect (Qs t)"
    using assms armv8_parallel by auto
  thus ?thesis by (rule sound)
qed

end