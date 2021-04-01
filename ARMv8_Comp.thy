theory ARMv8_Comp
  imports ARMv8_Rules
begin

chapter \<open>ARMv8 Composition Theory\<close>

definition local_op :: "('v,'r) state \<Rightarrow> ('v,'r) state \<Rightarrow> ('v,'r) state"
  where "local_op glb lcl \<equiv> (fst glb, snd lcl)"

definition ARMThread
  where "ARMThread c = Thread local_op (lift\<^sub>c c)"

lemma thr\<^sub>R [simp]:
  "thr\<^sub>R local_op (step\<^sub>R R) = step\<^sub>G R"
  unfolding thr\<^sub>R_def step\<^sub>R_def step\<^sub>G_def local_op_def by auto

lemma thr\<^sub>G [simp]:
  "thr\<^sub>G local_op (step\<^sub>G G) = step\<^sub>G G"
  unfolding thr\<^sub>G_def step\<^sub>G_def local_op_def by auto

definition univL
  where "univL P \<equiv> (\<lambda>m. \<forall>l. P (fst m,l))"

definition exL
  where "exL P \<equiv> (\<lambda>m. \<exists>l. P (fst m,l))"

lemma [simp]:
  "thr\<^sub>Q local_op (state Q) = state (exL Q)"
  unfolding exL_def local_op_def thr\<^sub>Q_def by auto

lemma [simp]:
  "thr\<^sub>A local_op (state P) = state (univL P)"
  unfolding univL_def local_op_def thr\<^sub>A_def by auto

lemma armv8_thread:
  assumes "guar\<^sub>c c G" "wellformed R G Q" "inter (step\<^sub>R R) (step\<^sub>G G) (lift\<^sub>c c)"
  shows "step\<^sub>G R,step\<^sub>G G \<turnstile> state (univL (wp R G c Q)) {ARMThread c} state (exL Q)"
proof -
  have a: "R,G \<turnstile>\<^sub>s wp R G c Q {c} Q" using assms wp_valid unfolding valid_def by blast
  thus ?thesis
    using rules.thread[OF a assms(3), of local_op]
    by (simp add: ARMThread_def)
qed

type_synonym ('v,'r) threads = "(('v,'r) rpred \<times> ('v,'r) rpred \<times> ('v,'r) lang \<times> ('v,'r) gpred) list"

abbreviation conjr (infixr "\<and>\<^sub>r" 35)
  where "conjr l r \<equiv> \<lambda>m m'. (l m m') \<and> (r m m')"

abbreviation disjr (infixr "\<or>\<^sub>r" 35)
  where "disjr l r \<equiv> \<lambda>m m'. (l m m') \<or> (r m m')"

definition entailr (infix "\<turnstile>\<^sub>r" 25)
  where "entailr P Q \<equiv> \<forall>m m'. P m m' \<longrightarrow> Q m m'"

fun Qs :: "('v,'r) threads \<Rightarrow> ('v,'r) pred"
  where 
    "Qs [] = PTrue" | 
    "Qs ((R,G,c,Q)#t) = (Qs t \<and>\<^sub>p (\<lambda>m. Q (fst m)))"

fun Ps :: "('v,'r) threads \<Rightarrow> ('v,'r) pred"
  where 
    "Ps [] = PTrue" | 
    "Ps (a#t) = (Ps t \<and>\<^sub>p univL (wp (fst a) (fst (snd a)) (fst (snd (snd a))) (\<lambda>m. (snd (snd (snd a))) (fst m))))"

fun Rs :: "('v,'r) threads \<Rightarrow> ('v,'r) rpred"
  where
    "Rs [] = (\<lambda>m m'. True)" |
    "Rs ((R,G,c,Q)#t) = (Rs t \<and>\<^sub>r R)"

fun Gs :: "('v,'r) threads \<Rightarrow> ('v,'r) rpred"
  where
    "Gs [] = (\<lambda>m m'. False)" |
    "Gs ((R,G,c,Q)#t) = (Gs t \<or>\<^sub>r G)"

fun Cs :: "('v,'r) threads \<Rightarrow> (('v,'r) inst,('v,'r) state) com"
  where 
    "Cs [] = undefined " |
    "Cs [c] = ARMThread (fst (snd (snd c)))" |
    "Cs (c#ts) = Cs [c] || Cs ts"

definition wfs :: "('v,'r) threads \<Rightarrow> bool"
  where "wfs t \<equiv> \<forall>(R,G,c,Q) \<in> set t. 
                  wellformed R G (\<lambda>m :: ('v,'r) state. Q (fst m)) \<and> guar\<^sub>c c G \<and> inter (step\<^sub>R R) (step\<^sub>G G) (lift\<^sub>c c)"

definition rg_comp :: "('v,'r) threads \<Rightarrow> bool"
  where "rg_comp t \<equiv> \<forall>i j. i < length t \<longrightarrow> j < length t \<longrightarrow> i \<noteq> j \<longrightarrow> fst (snd (t ! i)) \<turnstile>\<^sub>r fst (t ! j)"

lemma rg_comp_tailI:
  "rg_comp (a#t) \<Longrightarrow> rg_comp t"
  unfolding rg_comp_def apply auto
  by (metis (no_types, lifting) Ex_less_Suc Suc_inject less_trans_Suc nth_Cons_Suc)

lemma Gs_rel:
  assumes "\<forall>i. i < length t \<longrightarrow> step\<^sub>G (fst (snd ((t :: ('a,'b) threads) ! i))) \<subseteq> ((step\<^sub>G R) :: ('a,'b) state rel)"
  shows "step\<^sub>G (Gs t) \<subseteq> step\<^sub>G R"
  using assms
proof (induct t)
  case Nil
  then show ?case by (auto simp: step\<^sub>G_def)
next
  case (Cons a t)
  obtain R' G c Q where a [simp]: "a = (R',G,c,Q)" by (cases a, auto)
  have i: "\<And>i. i < length (a # t) \<Longrightarrow> step\<^sub>G (ld (snd ((a # t) ! i))) \<subseteq> ((step\<^sub>G R) :: ('a,'b) state rel)"
    using Cons(2) by auto

  have b: "\<forall>i. i <length t \<longrightarrow> step\<^sub>G (ld (snd (t ! i))) \<subseteq> ((step\<^sub>G R) :: ('a,'b) state rel)" 
          "step\<^sub>G G \<subseteq> ((step\<^sub>G R) :: ('a,'b) state rel)"
    apply (intro allI impI)
    apply (subgoal_tac "step\<^sub>G (ld (snd ((a # t) ! Suc i))) \<subseteq> step\<^sub>G R")
    apply auto[1]
    apply (rule i)
    apply auto
    using i[of 0]
    apply auto
    done

  show ?case using Cons(1)[OF b(1)] b(2)
    apply (auto simp: step\<^sub>G_def)
    apply fast
    apply fast
    done
qed

lemma Rs_rel:
  assumes "\<forall>i. i < length t \<longrightarrow> (step\<^sub>G G  :: ('a,'b) state rel) \<subseteq> step\<^sub>G (fst ( ((t :: ('a,'b) threads) ! i)))"
  shows "step\<^sub>G G \<subseteq> step\<^sub>G (Rs t)"
  using assms
proof (induct t)
  case Nil
  then show ?case by (auto simp: step\<^sub>G_def)
next
  case (Cons a t)
  obtain R G' c Q where a [simp]: "a = (R,G',c,Q)" by (cases a, auto)
  have i: "\<And>i. i < length (a # t) \<Longrightarrow> ((step\<^sub>G G) :: ('a,'b) state rel) \<subseteq> step\<^sub>G  (fst ((a # t) ! i))"
    using Cons(2) by auto

  have b: "\<forall>i. i <length t \<longrightarrow> ((step\<^sub>G G) :: ('a,'b) state rel) \<subseteq> step\<^sub>G  (fst (t ! i))"
          "step\<^sub>G G \<subseteq> ((step\<^sub>G R) :: ('a,'b) state rel)"
    apply (intro allI impI)
    using i apply force using i by force

  show ?case using Cons(1)[OF b(1)] b(2)
    apply (auto simp: step\<^sub>G_def)
    apply fast
    apply fast
    done
qed

lemma rg_comp_Gs:
  assumes "rg_comp ((R,G,c,Q)#t)" 
  shows "step\<^sub>G (Gs t) \<subseteq> step\<^sub>G R"
proof -
  have "\<forall>i. i < length t \<longrightarrow> fst (snd (t ! i)) \<turnstile>\<^sub>r R"
    using assms unfolding rg_comp_def by force
  hence "\<forall>i. i < length t \<longrightarrow> step\<^sub>G (fst (snd (t ! i))) \<subseteq> step\<^sub>G R"
    unfolding step\<^sub>G_def entailr_def by auto
  thus ?thesis using Gs_rel by blast
qed

lemma rg_comp_Rs:
  assumes "rg_comp ((R,G,c,Q)#t)" 
  shows "step\<^sub>G G \<subseteq> step\<^sub>G (Rs t)"
proof -
  have "\<forall>i. i < length t \<longrightarrow> G \<turnstile>\<^sub>r fst (t ! i)"
    using assms unfolding rg_comp_def by force
  hence "\<forall>i. i < length t \<longrightarrow> step\<^sub>G G \<subseteq> step\<^sub>G (fst (t ! i))"
    unfolding step\<^sub>G_def entailr_def by auto
  thus ?thesis using Rs_rel by blast
qed

lemma armv8_parallel:
  assumes "length t \<noteq> 0" "wfs t" "rg_comp t"
  shows "step\<^sub>G (Rs t), step\<^sub>G (Gs t) \<turnstile> state (Ps t) {Cs t} state (Qs t)"
  using assms
proof (induct t)
  case (Cons a t)
  obtain R G c Q where a [simp]: "a = (R,G,c,Q)" by (cases a, auto)
  have wf: "guar\<^sub>c c G" "wellformed R G (\<lambda>m :: ('a,'b) state. Q (fst m))" 
           "inter (step\<^sub>R R) (step\<^sub>G G) (lift\<^sub>c c)" "wfs t"
    using Cons(3) by (auto simp: wfs_def)
  have j: "step\<^sub>G R,step\<^sub>G G \<turnstile> state (univL (wp R G c (\<lambda>m :: ('a,'b) state. Q (ld m)))) {ARMThread c}   
                            state (exL (\<lambda>m :: ('a,'b) state. Q (ld m)))" 
    using armv8_thread[OF wf(1,2,3)] by blast
  have c: "step\<^sub>G (Gs t) \<subseteq> step\<^sub>G R" "step\<^sub>G G \<subseteq> step\<^sub>G (Rs t)"
    using rg_comp_Rs rg_comp_Gs Cons apply fastforce
    using rg_comp_Rs rg_comp_Gs Cons apply fastforce
    done
  show ?case 
  proof (cases "t = []")
    case True
    then show ?thesis using j by (auto simp: exL_def pred_defs)
  next
    case False
    hence t: "step\<^sub>G (Rs t),step\<^sub>G (Gs t) \<turnstile> state (Ps t) {Cs t} state (Qs t)" 
      using Cons wf(4) rg_comp_tailI by blast
    have [simp]: "Cs ((R, G, c, Q) # t) = ARMThread c || Cs t" using False by (cases t) auto
    show ?thesis
      apply clarsimp
      apply (rule rules.conseq[OF rules.par[OF j t c]])
      by (auto simp: step\<^sub>G_def o_def exL_def pred_defs)
  qed
qed auto

end