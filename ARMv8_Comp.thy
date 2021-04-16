theory ARMv8_Comp
  imports ARMv8_Rules
begin

chapter \<open>ARMv8 Composition Theory\<close>

type_synonym ('v,'r,'a) thread = "(('v,'a) grel \<times> ('v,'a) grel \<times> ('v,'r,'a) pred \<times> ('v,'r,'a) pred \<times> ('v,'r,'a) com_armv8 \<times> ('v,'r,'a) pred)"
type_synonym ('v,'r,'a) threads = "('v,'r,'a) thread list"

definition set_rg :: "('v,'r,'a) tstate \<Rightarrow> ('v,'r,'a) tstate \<Rightarrow> ('v,'r,'a) tstate"
  where "set_rg g lcl \<equiv> g\<lparr> rg := rg lcl \<rparr>"

definition ARMThread
  where "ARMThread c = Thread set_rg (lift\<^sub>c c)"

lemma thr\<^sub>R [simp]:
  "thr\<^sub>R set_rg \<langle>step\<^sub>t R\<rangle> = \<langle>step R\<rangle>"
  unfolding thr\<^sub>R_def step\<^sub>t_def step_def set_rg_def by auto

lemma thr\<^sub>G [simp]:
  "thr\<^sub>G set_rg \<langle>step G\<rangle> = \<langle>step G\<rangle>"
  unfolding thr\<^sub>G_def step_def set_rg_def by auto

definition univL
  where "univL P \<equiv> (\<lambda>m. \<forall>l. P (m\<lparr> rg := l \<rparr>))"

definition exL
  where "exL P \<equiv> (\<lambda>m. \<exists>l. P (m\<lparr> rg := l \<rparr>))"

definition inv2
  where "inv2 I \<equiv> \<lambda>(m,m'). \<forall>l. I (set_glb l m) \<longrightarrow> I (set_glb l m')"

lemma [simp]:
  "thr\<^sub>Q set_rg (Collect Q) = Collect (exL Q)"
  unfolding exL_def set_rg_def thr\<^sub>Q_def
  by auto (metis tstate_rec.select_convs(1))

lemma [simp]:
  "thr\<^sub>A set_rg (Collect P) = Collect (univL P)"
  unfolding univL_def set_rg_def thr\<^sub>A_def
  by auto (metis tstate_rec.select_convs(1))

lemma armv8_thread:
  assumes "guar\<^sub>c c (inv I \<and>\<^sub>p G)" "wellformed R G" "stable\<^sub>t R Q" "inter \<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle> \<langle>step (inv I \<and>\<^sub>p G)\<rangle> (lift\<^sub>c c)" "P \<turnstile>\<^sub>p wp R c Q"
  shows "\<langle>step (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p univL P\<rangle> {ARMThread c} \<langle>all\<^sub>t I \<and>\<^sub>p exL Q\<rangle>"
proof -
  have a: "R,G,I \<turnstile>\<^sub>s wp R c Q {c} Q" using assms com_wp unfolding valid_def by blast
  have "\<langle>step (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p univL (wp R c Q)\<rangle> {ARMThread c} \<langle>all\<^sub>t I \<and>\<^sub>p exL Q\<rangle>"
    using rules.thread[OF a assms(4), of set_rg] by (simp add: ARMThread_def)
  thus ?thesis by (rule rules.conseq) (insert assms(5), auto simp: univL_def )
qed

section \<open>Parallel Composition Rules\<close>

text \<open>Parallel composition of post-conditions\<close>
fun Qs :: "('v,'r,'a) threads \<Rightarrow> ('v,'r,'a) pred"
  where 
    "Qs [] = (\<lambda>m. True)" | 
    "Qs ((R,G,I,P,c,Q)#t) = (Qs t \<and>\<^sub>p exL Q)"

text \<open>Parallel composition of pre-conditions\<close>
fun Ps :: "('v,'r,'a) threads \<Rightarrow>('v,'r,'a) pred"
  where 
    "Ps [] = (\<lambda>m. True)" | 
    "Ps ((R,G,I,P,c,Q)#t) = (Ps t \<and>\<^sub>p univL P)"

text \<open>Parallel composition of rely specification\<close>
fun Rs :: "('v,'r,'a) threads \<Rightarrow> ('v,'r,'a) trel"
  where
    "Rs [] = (\<lambda>m. True)" |
    "Rs ((R,G,c,Q)#t) = (Rs t \<and>\<^sub>p step R)"

text \<open>Parallel composition of guarantee specification\<close>
fun Gs :: "('v,'r,'a) threads \<Rightarrow> ('v,'r,'a) trel"
  where
    "Gs [] = (\<lambda>m. False)" |
    "Gs ((R,G,c,Q)#t) = (Gs t \<or>\<^sub>p step G)"

text \<open>Parallel composition of a list of programs\<close>
fun Cs :: "('v,'r,'a) threads \<Rightarrow> (('v,'r,'a) auxop,('v,'r,'a) tstate) com"
  where 
    "Cs [] = undefined " |
    "Cs [(R,G,I,P,c,Q)] = ARMThread c" |
    "Cs (c#ts) = Cs [c] || Cs ts"

text \<open>Parallel composition of a list of programs\<close>
fun Is :: "('v,'r,'a) threads \<Rightarrow> ('v,'a) gpred"
  where 
    "Is [] = (\<lambda>m. True)" | 
    "Is ((R,G,I,P,c,Q)#t) = (Is t \<and>\<^sub>p I)"

text \<open>Properties required for each thread\<close>
definition local_props :: "('v,'r,'a) threads \<Rightarrow> bool"
  where "local_props t \<equiv> \<forall>(R,G,I,P,c,Q) \<in> set t. 
            stable\<^sub>t R Q \<and> wellformed R G \<and> 
            guar\<^sub>c c (inv2 I \<and>\<^sub>p G) \<and> (P \<turnstile>\<^sub>p wp R c Q) \<and> 
            inter \<langle>step\<^sub>t (inv2 I \<and>\<^sub>p R)\<rangle> \<langle>step (inv2 I \<and>\<^sub>p G)\<rangle> (lift\<^sub>c c)"

text \<open>Rely/guarantee compatibility for a list of threads\<close>
definition rg_comp :: "('v,'r,'a) threads \<Rightarrow> bool"
  where "rg_comp t \<equiv> 
            \<forall>i j. i < length t \<longrightarrow> j < length t \<longrightarrow> i \<noteq> j \<longrightarrow> fst (snd (t ! i)) \<turnstile>\<^sub>p fst (t ! j)"

subsection \<open>Composition Properties\<close>

text \<open>Subset of compositional threads are compositional\<close>
lemma rg_comp_tailI:
  assumes "rg_comp (s#t)" 
  shows "rg_comp t"
proof (clarsimp simp: rg_comp_def)
  fix i j a b
  assume "i < length t" "j < length t" "i \<noteq> j" "fst (snd (t ! i)) (a, b)" 
  hence "Suc i < length (s#t)" "Suc j < length (s#t)" 
        "Suc i \<noteq> Suc j" "fst (snd ((s#t) ! Suc i)) (a, b)"  by auto
  hence "fst ((s#t) ! Suc j) (a, b)" using assms unfolding rg_comp_def by blast
  thus "fst (t ! j) (a, b)" by auto
qed

lemma Gs_rel:
  assumes "\<forall>i. i < length t \<longrightarrow> step (fst (snd ((t :: ('v,'r,'a) threads) ! i))) \<turnstile>\<^sub>p (step R :: ('v,'r,'a) trel)"
  shows "\<langle>Gs t\<rangle> \<subseteq> \<langle>step R\<rangle>"
  using assms
proof (induct t)
  case Nil
  then show ?case by (auto simp: step_def)
next
  case (Cons a t)
  obtain R' G c Q where a [simp]: "a = (R',G,c,Q)" by (cases a, auto)
  have i: "\<And>i. i < length (a # t) \<Longrightarrow> step (fst (snd ((a # t) ! i))) \<turnstile>\<^sub>p ((step R) :: ('v,'r,'a) trel)"
    using Cons(2) by auto

  have b: "\<forall>i. i <length t \<longrightarrow> step (fst (snd (t ! i))) \<turnstile>\<^sub>p ((step R) :: ('v,'r,'a) trel)" 
          "step G \<turnstile>\<^sub>p ((step R) :: ('v,'r,'a) trel)"
    apply (intro allI impI)
    apply (subgoal_tac "step (fst (snd ((a # t) ! Suc i))) \<turnstile>\<^sub>p step R")
    apply auto[1]
    apply (rule i)
    apply auto
    using i[of 0]
    apply auto
    done

  show ?case using Cons(1)[OF b(1)] b(2) by (auto simp: step_def pred_defs)
qed

lemma Rs_rel:
  assumes "\<forall>i. i < length t \<longrightarrow> (step G  :: ('v,'r,'a) trel) \<turnstile>\<^sub>p step (fst ( ((t :: ('v,'r,'a) threads) ! i)))"
  shows "\<langle>step G\<rangle> \<subseteq> \<langle>Rs t\<rangle>"
  using assms
proof (induct t)
  case Nil
  then show ?case by (auto simp: step_def)
next
  case (Cons a t)
  obtain R G' c Q where a [simp]: "a = (R,G',c,Q)" by (cases a, auto)
  have i: "\<And>i. i < length (a # t) \<Longrightarrow> ((step G) :: ('v,'r,'a) trel) \<turnstile>\<^sub>p step  (fst ((a # t) ! i))"
    using Cons(2) by auto

  have b: "\<forall>i. i <length t \<longrightarrow> ((step G) :: ('v,'r,'a) trel) \<turnstile>\<^sub>p step  (fst (t ! i))"
          "step G \<turnstile>\<^sub>p ((step R) :: ('v,'r,'a) trel)"
    apply (intro allI impI)
    using i 
    apply (metis (no_types, hide_lams) length_Suc_conv not_less_eq nth_Cons_Suc)
    using i[of 0] by auto

  show ?case using Cons(1)[OF b(1)] b(2) by (auto simp: step_def pred_defs)
qed

lemma rg_comp_Gs:
  assumes "rg_comp ((R,G,I,P,c,Q)#t)" 
  shows "\<langle>Gs t\<rangle> \<subseteq> \<langle>step R\<rangle>"
proof -
  have "\<forall>i. i < length t \<longrightarrow> fst (snd (t ! i)) \<turnstile>\<^sub>p R"
    using assms unfolding rg_comp_def
    by (metis (no_types, lifting) Suc_mono fst_conv length_Cons length_greater_0_conv list.distinct(1) list.sel(3) nat.simps(3) nth_Cons_0 nth_tl)
  hence "\<forall>i. i < length t \<longrightarrow> step (fst (snd (t ! i))) \<turnstile>\<^sub>p step R"
    unfolding step_def by auto
  thus ?thesis using Gs_rel by blast
qed

lemma rg_comp_Rs:
  assumes "rg_comp ((R,G,I,P,c,Q)#t)" 
  shows "\<langle>step G\<rangle> \<subseteq> \<langle>Rs t\<rangle>"
proof -
  have "\<forall>i. i < length t \<longrightarrow> G \<turnstile>\<^sub>p fst (t ! i)"
    using assms unfolding rg_comp_def 
    by (metis (no_types, lifting) Suc_mono fst_conv length_Cons length_greater_0_conv list.distinct(1) list.sel(3) nat.simps(3) nth_Cons_0 nth_tl snd_conv)
  hence "\<forall>i. i < length t \<longrightarrow> step G \<turnstile>\<^sub>p step (fst (t ! i))"
    unfolding step_def pred_defs by auto
  thus ?thesis using Rs_rel by blast
qed

lemma armv8_parallel:
  assumes "length t \<noteq> 0" "local_props t" "rg_comp t"
  shows "\<langle>Rs t\<rangle>, \<langle>Gs t\<rangle> \<turnstile> \<langle>Ps t\<rangle> {Cs t} \<langle>Qs t\<rangle>"
  using assms
proof (induct t)
  case (Cons a t)
  obtain R G I P c Q where a [simp]: "a = (R,G,I,P,c,Q)" by (cases a, auto)
  have wf: 
      "guar\<^sub>c c (inv I \<and>\<^sub>p G)" "wellformed R G" "stable\<^sub>t R Q" 
      "inter \<langle>step\<^sub>t (inv I \<and>\<^sub>p R)\<rangle> \<langle>step (inv I \<and>\<^sub>p G)\<rangle> (lift\<^sub>c c)" 
      "P \<turnstile>\<^sub>p wp R c Q" "local_props t"
    using Cons(3) by (auto simp: local_props_def)
  have j: "\<langle>step (inv I \<and>\<^sub>p R)\<rangle>,\<langle>step (inv I \<and>\<^sub>p G)\<rangle> \<turnstile> \<langle>all\<^sub>t I \<and>\<^sub>p univL P\<rangle> {ARMThread c} \<langle>all\<^sub>t I \<and>\<^sub>p exL Q\<rangle>" 
    using armv8_thread[OF wf(1,2,3,4,5)] by blast
  have c: "\<langle>Gs t\<rangle> \<subseteq> \<langle>step R\<rangle>" "\<langle>step G\<rangle> \<subseteq> \<langle>Rs t\<rangle>"
    using rg_comp_Rs[of _ _ I P] rg_comp_Gs[of _ _ I P] Cons by auto
  show ?case 
  proof (cases "t = []")
    case True
    then show ?thesis using j by (auto simp: exL_def)
  next
    case False
    hence t: "\<langle>Rs t\<rangle>, \<langle>Gs t\<rangle> \<turnstile> \<langle>Ps t\<rangle> {Cs t} \<langle>Qs t\<rangle>" using Cons wf(6) rg_comp_tailI sorry
    have [simp]: "Cs ((R, G, I, P, c, Q) # t) = ARMThread c || Cs t" using False by (cases t) auto
    show ?thesis by (clarsimp, rule rules.conseq[OF rules.par[OF j t c]]) auto
  qed
qed auto

lemma armv8_sound:
  assumes "length t \<noteq> 0" "local_props t" "rg_comp t"
  shows "validity (Cs t) \<langle>Ps t\<rangle> \<langle>Rs t\<rangle> \<langle>Gs t\<rangle> \<langle>Qs t\<rangle>"
  using assms by (intro sound armv8_parallel) auto

end