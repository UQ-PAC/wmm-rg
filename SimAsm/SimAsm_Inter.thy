theory SimAsm_Inter
  imports SimAsm_WP "HOL-Library.While_Combinator"
begin

record ('v,'g,'r,'a) point =
  op  :: "('v,'g,'r,'a) opbasic"
  rgs :: "'r set"          
  wrs :: "'g set"
  rds :: "'g set"
  fen :: bool
  inv :: bool

fun upd_assign
  where 
    "upd_assign (Reg r) e p = p" |
    "upd_assign (Glb g) e p = p"

fun upd_cmp
  where
    "upd_cmp b p = p"

abbreviation shr
  where "shr A \<equiv> {g. Glb g \<in> A}"

abbreviation priv
  where "priv A \<equiv> {g. Reg g \<in> A}"

abbreviation inst
  where "inst a \<equiv> fst (tag a)"

fun ord
  where
    "ord nop p = False" |
    "ord (cmp b) p = (wrs p \<noteq> {} \<or> shr (deps\<^sub>B b) \<inter> rds p \<noteq> {})" |
    "ord (assign (Reg r) e) p = (shr (deps e) \<inter> (rds p \<union> wrs p) \<noteq> {} \<or> (r \<in> rgs p \<and> shr (deps e) \<noteq> {}))" |
    "ord (assign (Glb x) e) p = (shr (deps e) \<inter> (rds p \<union> wrs p) \<noteq> {} \<or> x \<in> wrs p)" |
    "ord full_fence _ = True"

fun wp\<^sub>b :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) trans"
  where "wp\<^sub>b R ((\<alpha>,f),v,_) Q = stabilize R (v \<inter> wp\<^sub>i \<alpha> (wp\<^sub>a f Q))"

fun chk :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> bool"
  where
    "chk R a p = 
      (inst a = full_fence \<or>
      (\<forall>Q. stable\<^sub>t R Q \<longrightarrow> wp\<^sub>b Id a (wp\<^sub>b R (op p) Q) \<subseteq> wp\<^sub>b Id (op p) (wp\<^sub>b R a Q)))"

fun stren :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "stren a p = p\<lparr> rgs := rgs p - priv (wr a) \<union> priv (rd a), 
                    wrs := wrs p \<union> shr (wr a), 
                    rds := rds p \<union> shr (rd a), 
                    fen := fen p \<or> (a = full_fence) \<rparr>"

fun weaken :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) point \<Rightarrow> ('v,'g,'r,'a) point"
  where
    "weaken a p = p\<lparr> rds := rds p - shr (wr a) \<rparr>"

fun upd\<^sub>i
  where
    "upd\<^sub>i R a p = (if fen p \<or> ord (inst a) p then stren (inst a) p 
                  else (weaken (inst a) p)\<lparr>inv := inv p \<and> chk R a p\<rparr>)"

definition gen
  where
    "gen a = \<lparr> op = a, 
              rgs = priv (rd (inst a)), 
              wrs = shr (wr (inst a)), 
              rds = shr (rd (inst a)), 
              fen = (inst a = full_fence),
              inv = True\<rparr>"

definition upd\<^sub>a
  where "upd\<^sub>a R a P = ({ gen a } \<union> ((upd\<^sub>i R a) ` P))"

fun upd2
  where 
    "upd2 R (Basic a) P = upd\<^sub>a R a P" |
    "upd2 R (Choice c\<^sub>1 c\<^sub>2) P = (upd2 R c\<^sub>1 P \<union> upd2 R c\<^sub>2 P)" |
    "upd2 R (Loop c) P = lfp (\<lambda>Y. (P \<union> upd2 R c Y))" |
    "upd2 R (c\<^sub>1 ;; c\<^sub>2) P = upd2 R c\<^sub>1 (upd2 R c\<^sub>2 P)" |
    "upd2 R _ P = P"

declare upd2.simps(3)[simp del]

lemma mono_upd\<^sub>a:
  "mono (upd\<^sub>a R a)"
  by (smt Un_mono image_Un monoI order_refl sup.orderE sup_ge2 upd\<^sub>a_def)

lemma mono_upd:
  "mono (upd2 R c)"
proof (induct c)
  case (Seq c1 c2)
  then show ?case by (simp add: mono_def)
next
  case (Choice c1 c2)
  then show ?case
    by (smt Un_mono mono_def upd2.simps(2))
next
  case (Loop c)
  then show ?case 
    by (smt Un_iff lfp_mono monoI subset_eq upd2.simps(3))
qed (simp add: monoI mono_upd\<^sub>a)+

lemma mono_union_upd2:
  "mono (\<lambda>Y. (P \<union> upd2 R c Y))"
  by (smt Un_mono monoD monoI mono_upd sup.idem sup.order_iff)

subsection \<open>Correctness\<close>

lemma upd_rw:
  assumes "c \<leadsto> c'" "local c"
  shows "upd2 R c' P \<subseteq> upd2 R c P"
  using assms
proof (induct arbitrary: P)
  case (seq2 c\<^sub>2 c\<^sub>2' c\<^sub>1)
  then show ?case by (simp add: monoD mono_upd)
next
  case (loop1 c)
  then show ?case unfolding upd2.simps
    using def_lfp_unfold[OF _ mono_union_upd2] by blast
next
  case (loop2 c)
  then show ?case unfolding upd2.simps
    using def_lfp_unfold[OF _ mono_union_upd2] by blast
qed auto

lemma upd_exec:
  assumes "lexecute c r \<alpha> c'"
  assumes "\<forall>p \<in> upd2 R c P. inv p"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha> \<and> (\<forall>p \<in> upd2 R c' P. inv p)"
  sorry

lemma upd\<^sub>aI1:
  assumes "p \<in> P"
  shows "ord (inst \<alpha>) p \<longrightarrow> stren (inst \<alpha>) p \<in> upd\<^sub>a R \<alpha> P"
        "\<not> ord (inst \<alpha>) p \<longrightarrow> (weaken (inst \<alpha>) p)\<lparr>inv := inv p \<and> chk R \<alpha> p\<rparr> \<in> upd\<^sub>a R \<alpha> P"
  using assms unfolding upd\<^sub>a_def by auto

lemma inv_orig\<^sub>a [intro]:
  assumes "\<forall>x\<in>upd\<^sub>a R \<alpha> P. point.inv x" shows "\<forall>p \<in> P. inv p"
proof (clarsimp)
    fix x assume a: "x \<in> P"
    show "point.inv x" 
    proof (cases "ord (inst \<alpha>) x")
      case True
      hence "stren (inst \<alpha>) x \<in> upd\<^sub>a R \<alpha> P" using upd\<^sub>aI1[OF a, of \<alpha>] by simp
      then show ?thesis using assms by auto
    next
      case False
      hence "(weaken (inst \<alpha>) x)\<lparr>inv := inv x \<and> chk R \<alpha> x\<rparr> \<in> upd\<^sub>a R \<alpha> P"
        using upd\<^sub>aI1[OF a, of \<alpha>] by simp
      then show ?thesis using assms by auto
    qed
  qed

lemma inv_orig [intro]:
  assumes "\<forall>p \<in> upd2 R c P. inv p"
  shows "\<forall>p \<in> P. inv p"
  using assms
proof (induct c arbitrary: P)
  case (Basic x)
  then show ?case using inv_orig\<^sub>a by fastforce
next
  case (Seq c1 c2)
  then show ?case unfolding upd2.simps by blast
next
  case (Choice c1 c2)
  then show ?case unfolding upd2.simps by blast
next
  case (Loop c)
  then show ?case unfolding upd2.simps 
    using lfp_unfold mono_union_upd2 by blast 
qed (unfold upd2.simps, blast)

definition point_cmp
  where "point_cmp a b \<equiv> rgs a \<subseteq> rgs b \<and> wrs a \<subseteq> wrs b \<and> rds a \<subseteq> rds b"

lemma point_cmp_refl [intro]:
  "point_cmp a a"
  by (auto simp: point_cmp_def)

lemma [simp]:
  "deps (subst e r e') = deps e - {r} \<union> (if r \<in> deps e then deps e' else {})"
  sorry

lemma [simp]:
  "deps\<^sub>B (subst\<^sub>B e r e') = deps\<^sub>B e - {r} \<union> (if r \<in> deps\<^sub>B e then deps e' else {})"
  sorry


lemma upd_reorder_com:
  assumes "reorder_com \<alpha>' c \<alpha>" "p \<in> P" "point_cmp p (gen \<alpha>)" 
  shows "\<exists>p'. p' \<in> upd2 R c P \<and> op p' = op p \<and> point_cmp p' (gen \<alpha>')"
  using assms
  sorry (*
proof (induct rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  hence [simp]: "op p = \<alpha>'" by auto
  have "\<not> ord (inst \<beta>) p"
    using 2(1,4)
    apply (cases "inst \<beta>"; cases "tag \<beta>"; cases "\<alpha>'")
    apply (auto simp: gen_def point_cmp_def)
    prefer 3
    apply (subgoal_tac "Glb x \<in> rd aa"; blast)
    prefer 2
    apply (subgoal_tac "Glb x \<in> wr aa"; blast)
    apply (case_tac x11, simp)
    apply (case_tac aa, simp split: if_splits)

    apply (elim impE)
    apply (subgoal_tac "rds p \<subseteq> shr ((deps x12a - {Reg x1} \<union> deps x12))")
    apply (subgoal_tac "shr (insert (Reg x1) (deps x12)) \<inter> shr (deps x12a - {Reg x1} \<union> deps x12) = {}")
    apply blast
    apply blast
    apply auto[1]

    apply (elim conjE exE)
    apply (subgoal_tac "Glb x \<in> insert (Reg x1) (deps x12)")
    apply (subgoal_tac "Glb x \<in> (deps x12a - {Reg x1} \<union> deps x12)")
    apply auto[3]

    apply (elim impE)
    apply (subgoal_tac "rds p \<subseteq> shr ((deps x12a ))")
    apply (subgoal_tac "shr ( (deps x12)) \<inter> shr (deps x12a ) = {}")
    apply blast
    apply blast
    apply blast

    apply (elim conjE exE)
    apply (subgoal_tac "Glb x \<in> insert (Reg x1) (deps x12)")
    apply (subgoal_tac "Glb x \<in> (deps x12a - {Reg x1} \<union> deps x12)")
    apply auto[3]

    apply (simp split: if_splits)
    apply (elim impE)

    apply (subgoal_tac "rds p \<subseteq> shr (deps\<^sub>B x2 - {Reg x1} \<union> deps x12)")
    apply (subgoal_tac "shr (insert (Reg x1) (deps x12)) \<inter> shr (deps\<^sub>B x2 - {Reg x1} \<union> deps x12) = {}")
    apply blast
    apply blast
    apply auto[1]

    apply (elim conjE exE)
    apply (subgoal_tac "Glb x \<in> insert (Reg x1) (deps x12)")
    apply (subgoal_tac "Glb x \<in> (deps\<^sub>B x2 - {Reg x1} \<union> deps x12)")
    apply auto[3]

    apply (subgoal_tac "rds p \<subseteq> shr (deps\<^sub>B x2 )")
    apply (subgoal_tac "shr (insert (Reg x1) (deps x12)) \<inter> shr (deps\<^sub>B x2 ) = {}")
    apply blast
    apply blast
    apply auto[1]

    apply simp
    apply simp

    apply simp

    apply (case_tac aa, simp split: if_splits)
    apply blast
    apply blast

    apply (simp split: if_splits)
    apply blast
    apply blast

    apply (simp split: if_splits)
    apply (simp split: if_splits)
    done

  hence "(weaken (inst \<beta>) p)\<lparr>inv := inv p \<and> chk R \<beta> p\<rparr> \<in> upd\<^sub>a R \<beta> P"
    using 2 by (auto simp: upd\<^sub>a_def)

  moreover have "point_cmp ((weaken (inst \<beta>) p)\<lparr>inv := inv p \<and> chk R \<beta> p\<rparr>) (gen \<alpha>)"
    using 2(1,4) unfolding point_cmp_def gen_def
    apply auto
    apply (cases \<alpha>'; cases \<beta>; case_tac a; case_tac aa; case_tac ab; case_tac ac; simp split: if_splits)
    
    sorry

  moreover have "op ((weaken (inst \<beta>) p)\<lparr>inv := inv p \<and> chk R \<beta> p\<rparr>) = \<alpha>'" using 2 by auto

  ultimately show ?case by auto
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then show ?case
    apply simp
    sorry
qed auto
*)

lemma execute_act:
  assumes "lexecute c r \<alpha> c'"
  shows "\<exists>p. p \<in> upd2 R c P \<and> op p = \<alpha> \<and> point_cmp p (gen (fwd_com \<alpha> r))"
  using assms
proof (induct arbitrary: P)
  case (act \<alpha>)
  have "gen \<alpha> \<in> upd\<^sub>a R \<alpha> P" by (auto simp: upd\<^sub>a_def)
  then show ?case by (auto simp: gen_def)
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case by simp
next
  case (ooo c\<^sub>1 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>2)
  obtain p where p: "p \<in> upd2 R c\<^sub>1 P" "op p = \<alpha>" "point_cmp p (gen (fwd_com \<alpha> r))"
    using ooo by blast
  have r: "reorder_com \<alpha>' (c\<^sub>2) (fwd_com \<alpha> r)" using ooo by auto
  then show ?case using p(2) upd_reorder_com[OF r p(1,3), of R] by auto
qed

lemma upd_po:
  assumes "reorder_com \<alpha>' c \<alpha>" "p \<in> P" "point_cmp p (gen \<alpha>)" "\<alpha> = fwd_com (op p) r" "\<forall>a\<in>upd2 R c P. point.inv a"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) c \<alpha>"
  using assms
proof (induct \<alpha>' c \<alpha> arbitrary: P rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  hence "\<not> ord (inst \<beta>) p" sorry (* correctness of ordering analysis *)
  hence "(weaken (inst \<beta>) p)\<lparr>inv := inv p \<and> chk R \<beta> p\<rparr> \<in> upd\<^sub>a R \<beta> P"
    using 2(2) unfolding upd\<^sub>a_def upd2.simps upd\<^sub>i.simps by auto
  hence "chk R \<beta> p" using 2 by auto
  then show ?case
    apply simp
    sorry (* correctness of chk *)
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then show ?case sorry
qed auto

lemma upd_exec':
  assumes "lexecute c r \<alpha> c'"
  assumes "\<forall>p \<in> upd2 R c P. inv p"
  shows "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct arbitrary: P)
  case (act \<alpha>)
  then show ?case by auto
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case by auto
next
  case (ooo c\<^sub>1 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>2)
  then obtain p where p: "p \<in> upd2 R c\<^sub>1 P" "op p = \<alpha>" "point_cmp p (gen (fwd_com \<alpha> r))"
    using execute_act by blast
  have r: "reorder_com \<alpha>' (c\<^sub>2) (fwd_com \<alpha> r)" using ooo by auto
  have f: "fwd_com \<alpha> r = fwd_com (op p) r" using p by auto
  have "inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>" using ooo inv_orig by force
  thus ?case using upd_po[OF r p(1,3) f] ooo(4) by auto
qed

lemma upd\<^sub>aE:
  assumes "x \<in> upd\<^sub>a R \<alpha> P"
  obtains (ord) p where "ord (inst \<alpha>) p" "x = stren (inst \<alpha>) p" "p \<in> P" |
          (ooo) p where "\<not> ord (inst \<alpha>) p" "x = (weaken (inst \<alpha>) p)\<lparr>inv := inv p \<and> chk R \<alpha> p\<rparr>" "p \<in> P" |
          (gen) "x = gen \<alpha>"
proof -
  have "x = gen \<alpha> \<or> x \<in> upd\<^sub>i R \<alpha> ` P" using assms by (auto simp: upd\<^sub>a_def)
  thus ?thesis
  proof (elim disjE)
    assume "x = gen \<alpha>"
    thus ?thesis using gen by auto
  next
    assume "x \<in> upd\<^sub>i R \<alpha> ` P"
    then obtain p where p: "p \<in> P" "x = upd\<^sub>i R \<alpha> p" by blast
    thus ?thesis
    proof (cases "ord (inst \<alpha>) p")
      case True
      thus ?thesis using p ord by auto
    next
      case False
      thus ?thesis using p ooo by auto
    qed
  qed
qed

lemma upd_exec'':
  assumes "lexecute c r \<alpha> c'"
  assumes "\<forall>p \<in> upd2 R c P. inv p"
  shows "\<forall>p \<in> upd2 R c' P. inv p"
  using assms
proof (induct arbitrary: P)
  case (act \<alpha>)
  then show ?case
  proof (clarsimp)
    fix x assume a: "x \<in> P"
    show "point.inv x" 
    proof (cases "ord (inst \<alpha>) x")
      case True
      hence "stren (inst \<alpha>) x \<in> upd\<^sub>a R \<alpha> P" using upd\<^sub>aI1[OF a, of \<alpha>] by simp
      then show ?thesis using act by auto
    next
      case False
      hence "(weaken (inst \<alpha>) x)\<lparr>inv := inv x \<and> chk R \<alpha> x\<rparr> \<in> upd\<^sub>a R \<alpha> P"
        using upd\<^sub>aI1[OF a, of \<alpha>] by simp
      then show ?thesis using act by auto
    qed
  qed
next
  case (ino c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case by auto
next
  case (ooo c\<^sub>1 r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>2)
  then show ?case apply auto sorry
qed

theorem try_again:
  assumes "reorder_trace t c" "local c"
  assumes "\<forall>p \<in> upd2 R c P. inv p"
  shows "\<forall>(r,\<alpha>) \<in> set t. inter\<^sub>c (step\<^sub>t R) (step G) r \<alpha>"
  using assms
proof (induct)
  case (1 c)
  then show ?case by auto
next
  case (2 c c' t)
  then show ?case using upd_rw[OF 2(1)] local_silent by blast
next
  case (3 c r \<alpha> c' t)
  then show ?case using upd_exec[OF 3(1,5), of G] local_execute[OF 3(1,4)] by auto
qed

theorem upd_correct:
  assumes "\<forall>p \<in> upd2 R (lift\<^sub>c c) P. inv p"
  shows "rif (step\<^sub>t R) (step G) (lift\<^sub>c c)"
  using assms unfolding rif_def
proof (intro impI allI ballI, goal_cases)
  case (1 t x)
  have l: "local (lift\<^sub>c c)" by blast
  then show ?case using try_again[OF 1(2) l 1(1)] 1(3) by auto
qed

fun com_rgs
  where 
    "com_rgs (Basic a) = priv (rd (fst (tag a)))" |
    "com_rgs (com.Seq c\<^sub>1 c\<^sub>2) = com_rgs c\<^sub>1 \<union> com_rgs c\<^sub>2" |
    "com_rgs (Choice c\<^sub>1 c\<^sub>2) = com_rgs c\<^sub>1 \<union> com_rgs c\<^sub>2" |
    "com_rgs (Loop c) = com_rgs c" |
    "com_rgs _ = {}"

fun com_glbs
  where 
    "com_glbs (Basic a) = shr (rd (fst (tag a))) \<union> shr (wr (fst (tag a)))" |
    "com_glbs (com.Seq c\<^sub>1 c\<^sub>2) = com_glbs c\<^sub>1 \<union> com_glbs c\<^sub>2" |
    "com_glbs (Choice c\<^sub>1 c\<^sub>2) = com_glbs c\<^sub>1 \<union> com_glbs c\<^sub>2" |
    "com_glbs (Loop c) = com_glbs c" |
    "com_glbs _ = {}"


(*

fun prog_rgs
  where 
    "prog_rgs Skip = {}" |
    "prog_rgs (Op v e f) = priv (rd e)" |
    "prog_rgs (Seq c\<^sub>1 c\<^sub>2) = prog_rgs c\<^sub>1 \<union> prog_rgs c\<^sub>2" |
    "prog_rgs (If b c\<^sub>1 c\<^sub>2) = priv (deps\<^sub>B b) \<union> prog_rgs c\<^sub>1 \<union> prog_rgs c\<^sub>2" |
    "prog_rgs (While b I c) = priv (deps\<^sub>B b) \<union> prog_rgs c" |
    "prog_rgs (DoWhile I c b) = priv (deps\<^sub>B b) \<union> prog_rgs c"

fun prog_glbs
  where 
    "prog_glbs Skip = {}" |
    "prog_glbs (Op v e f) = shr (rd e) \<union> shr (wr e)" |
    "prog_glbs (Seq c\<^sub>1 c\<^sub>2) = prog_glbs c\<^sub>1 \<union> prog_glbs c\<^sub>2" |
    "prog_glbs (If b c\<^sub>1 c\<^sub>2) = shr (deps\<^sub>B b) \<union> prog_glbs c\<^sub>1 \<union> prog_glbs c\<^sub>2" |
    "prog_glbs (While b I c) = shr (deps\<^sub>B b) \<union> prog_glbs c" |
    "prog_glbs (DoWhile I c b) = shr (deps\<^sub>B b) \<union> prog_glbs c"

fun prog_ops
  where 
    "prog_ops Skip = {}" |
    "prog_ops (Op v e f) = { (\<lfloor>v,e,f\<rfloor>) }" |
    "prog_ops (Seq c\<^sub>1 c\<^sub>2) = prog_ops c\<^sub>1 \<union> prog_ops c\<^sub>2" |
    "prog_ops (If b c\<^sub>1 c\<^sub>2) = { (\<lfloor>cmp b\<rfloor>) } \<union> prog_ops c\<^sub>1 \<union> prog_ops c\<^sub>2" |
    "prog_ops (While b I c) = { (\<lfloor>cmp b\<rfloor>) } \<union> prog_ops c" |
    "prog_ops (DoWhile I c b) = { (\<lfloor>cmp b\<rfloor>) } \<union> prog_ops c"
*)

fun glbs
  where
    "glbs p = rds p \<union> wrs p"

definition all_points
  where "all_points rs gs os \<equiv> {p. op p \<in> os \<and> rgs p \<subseteq> rs \<and> wrs p \<subseteq> gs \<and> rds p \<subseteq> gs}"

lemma bound:
  "upd2 R c P \<subseteq> all_points (com_rgs c \<union> \<Union> (rgs ` P)) (com_glbs c \<union> \<Union> (glbs ` P)) (basics c \<union> (op ` P))"
  sorry

lemma finite_all_points:
  "finite rs \<Longrightarrow> finite gs \<Longrightarrow> finite os \<Longrightarrow> finite (all_points rs gs os)"
  unfolding all_points_def sorry

lemma upd_While:
  fixes b c P R
  assumes "finite P"
  defines "f == (\<lambda>Y. (P \<union> upd2 R c Y))"
  shows "upd2 R (Loop c) P = while (\<lambda>Y. f Y \<noteq> Y) f {}" (is "_ = ?r")
proof -
  let ?V = "all_points (com_rgs c \<union> \<Union> (rgs ` P)) (com_glbs c \<union> \<Union> (glbs ` P)) (basics c \<union> (op ` P))"
  have "lfp f = ?r"
  proof(rule lfp_while[where C = "?V"])
    show "mono f" using f_def mono_union_upd2 by blast
  next
    fix Y show "Y \<subseteq> ?V \<Longrightarrow> f Y \<subseteq> ?V"
      unfolding f_def using bound[of R c] by blast
  next
    show "finite ?V" using \<open>finite P\<close>
      apply (intro finite_all_points)
      by simp
  qed
  thus ?thesis by (simp add: f_def)
qed

lemma upd_While_let: "finite X \<Longrightarrow> upd2 R (Loop c) X =
  (let f = (\<lambda>Y. X \<union> upd2 R c Y)
   in while (\<lambda>Y. f Y \<noteq> Y) f {})"
by(simp add: upd_While)

lemma upd_While_set: "upd2 R (Loop c) (set xs) =
  (let f = (\<lambda>Y. set xs \<union> upd2 R c Y)
   in while (\<lambda>Y. f Y \<noteq> Y) f {})"
by(rule upd_While_let, simp)

lemmas [code] = upd2.simps(1,2,4,5) upd_While_set


end