theory SimAsm_Exp
  imports SimAsm_State "../Expression"
begin

interpretation expression st st_upd
  by standard auto

section \<open>Operations\<close>

type_synonym ('v,'g,'r) exp = "('v,('g,'r) var) exp"

datatype ('v,'g,'r) op =
    assign "('g,'r) var" "('v,'g,'r) exp"
  | cmp "('v,'g,'r) exp"
  | full_fence
  | nop

abbreviation ncmp
  where "ncmp b \<equiv> cmp (Uop neg b)"

text \<open>Operation Behaviour\<close>
fun beh\<^sub>i :: "('v::truth,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) state rel"
  where
    "beh\<^sub>i (assign a e) = {(m,m'). m' = m (a :=\<^sub>s eval m e)}" |
    "beh\<^sub>i (cmp b) = {(m,m'). m = m' \<and> holds (eval m b)}" |
    "beh\<^sub>i _ = Id"

text \<open>Variables written by an operation\<close>
fun wr :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var set"
  where 
    "wr (assign y _) = {y}" |
    "wr _ = {}"

text \<open>Variables read by an operation\<close>
fun rd :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var set"
  where
    "rd (assign _ e) = deps e" |
    "rd (cmp b) = deps b" |
    "rd _ = {}"

text \<open>Test if an instruction is a memory barrier\<close>
fun barriers :: "('v,'g,'r) op \<Rightarrow> bool"
  where "barriers full_fence = True" | "barriers _ = False"

text \<open>Operation Substitution\<close>
fun subst\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) op"
  where
    "subst\<^sub>i (assign x e) y f = assign x (subst e y f)" |
    "subst\<^sub>i (cmp b) y f = cmp (subst b y f)" |
    "subst\<^sub>i \<alpha> _ _ = \<alpha>"

definition smap1
  where "smap1 V x \<alpha> \<equiv> if x \<in> dom V then subst\<^sub>i \<alpha> x (Val (the (V x))) else \<alpha>"

definition smap
  where "smap \<alpha> V \<equiv> Finite_Set.fold (smap1 V) \<alpha> (rd \<alpha>)"

definition forall
  where "forall V \<alpha> \<equiv> {smap \<alpha> M | M. dom M = V}"

section \<open>Rules\<close>

lemma local_ev\<^sub>E [intro]:
  "deps e \<subseteq> locals \<Longrightarrow> rg (m :: ('v,'g,'r,'a) state) = rg (m' :: ('v,'g,'r,'a) state) \<Longrightarrow> 
    eval m e = eval m' e"
  apply (intro eval_eq_state ballI, case_tac x)
  by (auto simp: rg_def) metis

lemma ev_aux\<^sub>E [simp]:
  "eval (x(aux: f)) g = eval x g"
  apply (intro eval_eq_state ballI, case_tac x)
  by (auto simp: aux_upd_def)

subsection \<open>Operations\<close>

lemma subst_wr [simp]:
  "wr (subst\<^sub>i \<alpha> x e) = wr \<alpha>"
  by (cases \<alpha>; auto)

lemma subst_rd [simp]:
  "rd (subst\<^sub>i \<alpha> x e) = rd \<alpha> - {x} \<union> (if x \<in> rd \<alpha> then deps e else {})"
  by (cases \<alpha>; auto)

lemma subst_barriers [simp]:
  "barriers (subst\<^sub>i \<alpha> x e) = barriers \<alpha>"
  by (cases \<alpha>; auto)

lemma subst_not_fence [simp]:
  "(subst\<^sub>i \<alpha> x e \<noteq> full_fence) = (\<alpha> \<noteq> full_fence)"
  by (cases \<alpha>; auto)

lemma subst\<^sub>i_nop [simp]:
  "x \<notin> rd \<beta> \<Longrightarrow> subst\<^sub>i \<beta> x e = \<beta>"
  by (cases \<beta>) (auto split: if_splits)

lemma finite_rd [intro]:
  "finite (rd \<alpha>)"
  by (cases \<alpha>) auto

subsection \<open>smap1 Theories\<close>

lemma smap1_flip [simp]:
  "smap1 V y (smap1 V x \<alpha>) = smap1 V x (smap1 V y \<alpha>)"
  by (cases \<alpha>; cases "x = y"; auto simp: smap1_def)

lemma smap1_rep [simp]:
  "smap1 V x (smap1 V x \<alpha>) = smap1 V x \<alpha>"
  by (cases \<alpha>; auto simp: smap1_def)

interpretation cfi: comp_fun_idem "smap1 V"  by standard auto

lemma smap1_rd [simp]:
  "rd (smap1 M x \<beta>) = rd \<beta> - ({x} \<inter> dom M)"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_wr [simp]:
  "wr (smap1 M x \<beta>) = wr \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_barriers [simp]:
  "barriers (smap1 M x \<beta>) = barriers \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_nop [simp]:
  "x \<notin> rd \<beta> \<Longrightarrow> smap1 M x \<beta> = \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_nop2 [simp]:
  "M x = None \<Longrightarrow> smap1 M x \<beta> = \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_empty [simp]:
  "smap1 Map.empty x \<beta> = \<beta>"
  unfolding smap1_def by (auto split: if_splits)

lemma smap1_fold_rd [simp]:
  assumes "finite F"
  shows "rd (Finite_Set.fold (smap1 M) \<beta> F) = rd \<beta> - (dom M \<inter> F)"
  using assms
proof (induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "Finite_Set.fold (smap1 M) \<beta> (insert x F) = smap1 M x (Finite_Set.fold (smap1 M) \<beta> F)"
    using cfi.fold_insert_idem by blast
  then show ?case by (auto simp: insert(3))
qed

lemma smap1_fold_wr [simp]:
  assumes "finite F"
  shows "wr (Finite_Set.fold (smap1 M) \<beta> F) = wr \<beta>"
  using assms
proof (induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "Finite_Set.fold (smap1 M) \<beta> (insert x F) = smap1 M x (Finite_Set.fold (smap1 M) \<beta> F)"
    using cfi.fold_insert_idem by blast
  then show ?case by (auto simp: insert(3))
qed

lemma smap1_fold_barriers [simp]:
  assumes "finite F"
  shows "barriers (Finite_Set.fold (smap1 M) \<beta> F) = barriers \<beta>"
  using assms
proof (induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "Finite_Set.fold (smap1 M) \<beta> (insert x F) = smap1 M x (Finite_Set.fold (smap1 M) \<beta> F)"
    using cfi.fold_insert_idem by blast
  then show ?case by (auto simp: insert(3))
qed

lemma smap1_fold_empty:
  assumes "finite F"
  shows "Finite_Set.fold (smap1 Map.empty) \<alpha> F = \<alpha>"
  using assms
proof (induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  hence "Finite_Set.fold (smap1 Map.empty) \<alpha> (insert x F) = 
         smap1 Map.empty x (Finite_Set.fold (smap1 Map.empty) \<alpha> F)"
    using cfi.fold_insert_idem by blast
  also have "... = Finite_Set.fold (smap1 Map.empty) \<alpha> F" by auto
  also have "... = \<alpha>" using insert(3) by blast
  finally show ?case .
qed

subsection \<open>smap Theories\<close>

lemma smap_rd [simp]:
  "rd (smap \<beta> M) = rd \<beta> - dom M"
proof -
  have "finite (rd \<beta>)" by auto
  thus ?thesis unfolding smap_def by auto
qed

lemma smap_wr [simp]:
  "wr (smap \<beta> M) = wr \<beta>"
proof -
  have "finite (rd \<beta>)" by auto
  thus ?thesis unfolding smap_def by auto
qed

lemma smap_barriers [simp]:
  "barriers (smap \<beta> M) = barriers \<beta>"
proof -
  have "finite (rd \<beta>)" by auto
  thus ?thesis unfolding smap_def by auto
qed

lemma smap_empty [simp]:
  "smap \<beta> Map.empty = \<beta>"
proof -
  have "finite (rd \<beta>)" by auto
  thus ?thesis using smap1_fold_empty unfolding smap_def by auto
qed

lemma smap_rep [simp]:
  "smap1 M x (smap \<beta> M) = smap \<beta> M"
proof (cases "x \<in> rd \<beta>")
  case True
  have "Finite_Set.fold (smap1 M) \<beta> (insert x (rd \<beta>)) =
        smap1 M x (Finite_Set.fold (smap1 M) \<beta> (rd \<beta>))"
    using cfi.fold_insert_idem by blast
  moreover have "insert x (rd \<beta>) = rd \<beta>" using True by auto
  ultimately show ?thesis unfolding smap_def by auto
next
  case False
  thus ?thesis by simp
qed

subsection \<open>forall Theories\<close>

lemma forall_rd [simp]:
  "\<forall>\<alpha> \<in> forall V \<beta>. rd \<alpha> = rd \<beta> - V"
  unfolding forall_def by auto

lemma forall_wr [simp]:
  "\<forall>\<alpha> \<in> forall V \<beta>. wr \<alpha> = wr \<beta>"
  unfolding forall_def by auto

lemma forall_barriers [simp]:
  "\<forall>\<alpha> \<in> forall V \<beta>. barriers \<alpha> = barriers \<beta>"
  unfolding forall_def by auto

lemma forall_fence [simp]:
  "\<forall>\<alpha> \<in> forall V \<beta>.  (\<alpha> \<noteq> full_fence) = (\<beta> \<noteq> full_fence)"
proof -
  have "\<forall>\<alpha>. barriers \<alpha> = (\<alpha> = full_fence)" by (intro allI, case_tac \<alpha>; auto)
  thus ?thesis using forall_barriers by blast
qed

lemma forall_nil [simp]:
  "forall {} \<alpha> = {\<alpha>}"
  unfolding forall_def by auto

lemma smap1_cong [intro]:
  "M x = N x \<Longrightarrow> smap1 M x = smap1 N x"
  unfolding smap1_def using domIff by fastforce

lemma
  "comp_fun_commute_on (rd \<alpha>) (smap1 (\<lambda>y. if x = y then None else M y))"
  by (rule Finite_Set.comp_fun_commute_on.intro) auto

lemma
  "comp_fun_commute_on (rd \<alpha>) (smap1 (\<lambda>y. if x = y then None else M y))"
  by (rule Finite_Set.comp_fun_commute_on.intro) auto
  
lemma forall_unfold:
  shows "forall (insert x V) \<alpha> = {subst\<^sub>i \<alpha>' x (Val c) | c \<alpha>'. \<alpha>' \<in> forall V \<alpha>}" (is "?L = ?R")
proof -
  have "?L \<subseteq> ?R"
  proof (clarsimp simp: forall_def, cases "x \<in> V")
    fix M assume d: "dom (M :: ('b, 'c) SimAsm_State.var \<Rightarrow> 'a option) = insert x V" "x \<in> V"
    hence "smap \<alpha> M = subst\<^sub>i (smap \<alpha> M) x (Val (the (M x)))" by simp
    moreover have "dom M = V" using d by auto
    ultimately show "\<exists>c \<alpha>'. smap \<alpha> M = subst\<^sub>i \<alpha>' x (Val c) \<and> (\<exists>M. \<alpha>' = smap \<alpha> M \<and> dom M = V)"
      by blast
  next
    fix M assume d: "dom (M :: ('b, 'c) SimAsm_State.var \<Rightarrow> 'a option) = insert x V" "x \<notin> V"
    let ?M = "\<lambda>y. if x = y then None else M y"
    have "smap \<alpha> M = subst\<^sub>i (smap \<alpha> ?M) x (Val (the (M x)))"
    proof -
      have 
        "comp_fun_commute_on (rd \<alpha>) (smap1 M)" 
        "comp_fun_commute_on (rd \<alpha>) (smap1 (\<lambda>y. if x = y then None else M y))"
        by standard auto
      hence mx: "Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}) = Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x})"
        by (auto intro!: Finite_Set.fold_cong simp add: cfi.comp_fun_commute_axioms)
      show ?thesis
      proof (cases "x \<in> rd \<alpha>")
        case True
        hence [simp]: "insert x (rd \<alpha>) = rd \<alpha>" by auto
        have fx: "Finite_Set.fold (smap1 M) \<alpha> (insert x (rd \<alpha>)) = 
                  smap1 M x (Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}))"
          by (rule cfi.fold_insert_remove) blast
        have "Finite_Set.fold (smap1 ?M) \<alpha> (insert x (rd \<alpha>)) = 
                  smap1 ?M x (Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x}))"
          by (rule cfi.fold_insert_remove) blast
        also have "... = Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x})" by auto
        finally show ?thesis using fx mx unfolding smap_def apply simp
          unfolding smap1_def using d(1) by (auto split: if_splits)
      next
        case False
        hence [simp]: "rd \<alpha> - {x} = rd \<alpha>" by auto
        have "x \<notin> rd (smap \<alpha> ?M)" using False by simp
        then show ?thesis using mx unfolding smap_def by simp
      qed
    qed
    moreover have "dom ?M = V" using d by (auto split: if_splits)
    ultimately show "\<exists>c \<alpha>'. smap \<alpha> M = subst\<^sub>i \<alpha>' x (Val c) \<and> (\<exists>M. \<alpha>' = smap \<alpha> M \<and> dom M = V)"
      by blast
  qed

  moreover have "?R \<subseteq> ?L"
  proof (clarsimp simp: forall_def, cases "x \<in> V")
    fix M c assume d: "V = dom (M :: ('b, 'c) SimAsm_State.var \<Rightarrow> 'a option)" "x \<in> V" 
    have "dom M = insert x (dom M)" using d by auto
    moreover have "subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> M" using d by simp
    ultimately show "\<exists>Ma. subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> Ma \<and> dom Ma = insert x (dom M)"
      by blast
  next
    fix M c assume d: "V = dom (M :: ('b, 'c) SimAsm_State.var \<Rightarrow> 'a option)" "x \<notin> V" 
    let ?M = "\<lambda>y. if y = x then Some c else M y"
    have "dom ?M = insert x (dom M)" using d by auto
    moreover have "subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> ?M"
    proof -
      have 
        "comp_fun_commute_on (rd \<alpha>) (smap1 M)" 
        "comp_fun_commute_on (rd \<alpha>) (smap1 (\<lambda>y. if y = x then Some c else M y))"
        by standard auto
      hence mx: "Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}) = Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x})"
        by (auto intro!: Finite_Set.fold_cong simp add: cfi.comp_fun_commute_axioms)
      show ?thesis
      proof (cases "x \<in> rd \<alpha>")
        case True
        hence [simp]: "insert x (rd \<alpha>) = rd \<alpha>" by auto
        have fx: "Finite_Set.fold (smap1 ?M) \<alpha> (insert x (rd \<alpha>)) = 
                  smap1 ?M x (Finite_Set.fold (smap1 ?M) \<alpha> (rd \<alpha> - {x}))"
          by (rule cfi.fold_insert_remove) blast
        have "Finite_Set.fold (smap1 M) \<alpha> (insert x (rd \<alpha>)) = 
                  smap1 M x (Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x}))"
          by (rule cfi.fold_insert_remove) blast
        also have "... = Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha> - {x})" using d by auto        
        finally show ?thesis using fx mx unfolding smap_def apply simp
          unfolding smap1_def using d(1) by (auto split: if_splits)
      next
        case False
        hence [simp]: "rd \<alpha> - {x} = rd \<alpha>" by auto
        have "x \<notin> rd (smap \<alpha> ?M)" using False by simp
        then show ?thesis using mx unfolding smap_def by simp
      qed
    qed
    ultimately show "\<exists>Ma. subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> Ma \<and> dom Ma = insert x (dom M)"
      by blast
  qed

  ultimately show ?thesis by blast
qed

lemma forall_one [simp]:
  "forall {x} \<alpha> = {subst\<^sub>i \<alpha> x (Val c) | c. True}"
  unfolding forall_unfold[of x "{}" \<alpha>] by auto

lemma forall_nop [simp]:
  assumes "x \<notin> rd \<alpha>" 
  shows "forall (insert x V) \<alpha> = forall V \<alpha>"
  using assms forall_unfold by force

lemma forallI [intro]:
  "smap \<alpha> M \<in> forall (dom M) \<alpha>"
  by (auto simp: forall_def)

subsection \<open>TODO\<close>

definition upd
  where "upd S f m \<equiv> m\<lparr>st := \<lambda>x. if x \<in> S then f x else st m x\<rparr>"

lemma upd_nil [simp]:
  "upd {} f m = m"
  by (auto simp: upd_def)

lemma upd_insert [simp]:
  "upd (insert x V) f m = (upd V f m)(x :=\<^sub>s f x)"
  by (auto simp: upd_def st_upd_def intro!: state_rec.equality)

lemma upd_rep [simp]:
  "upd A (st (upd A f m\<^sub>1)) m\<^sub>2 = upd A f m\<^sub>2"
  by (auto simp: upd_def intro!: state_rec.equality)

lemma upd_rep' [simp]:
  "upd A f (upd B f m) = upd (A \<union> B) f m"
  by (auto simp: upd_def intro!: state_rec.equality)

lemma upd_st [simp]:
  "st (upd S f m) x = (if x \<in> S then f x else st m x)"
  by (auto simp: upd_def)

lemma upd_more [simp]:
  "state_rec.more (upd V f m) = state_rec.more m"
  by (auto simp: upd_def)

lemma st_upd_eq [intro]:
  "state_rec.more m = state_rec.more m' \<Longrightarrow> \<forall>x. x \<noteq> y \<longrightarrow> st m x = st m' x \<Longrightarrow> m(y :=\<^sub>s e) = m'(y :=\<^sub>s e)"
  by (auto simp: upd_def st_upd_def intro!: state_rec.equality)

lemma beh_substi [simp]:
  "beh\<^sub>i (subst\<^sub>i \<alpha> x e) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (m\<^sub>1(x :=\<^sub>s eval m\<^sub>1 e),m) \<in> beh\<^sub>i \<alpha>}"
  apply (cases \<alpha>)
  defer 1
     apply (clarsimp simp: upd_def)
  apply blast
  apply (clarsimp simp: upd_def)
  apply blast
  apply (clarsimp simp: upd_def)
  apply blast
  apply (clarsimp simp: upd_def st_upd_def)
  apply auto     
  apply (rule state_rec.equality)
  apply auto
  apply (rule state_rec.equality)
  apply auto
  done

lemma [simp]:
  "st (m(x :=\<^sub>s e)) = (st m)(x := e)"
  by (auto simp: st_upd_def)

lemma beh_smap1 [simp]:
  "beh\<^sub>i (smap1 M x \<alpha>) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd ({x} \<inter> dom M) (the o M) m\<^sub>1,m) \<in> beh\<^sub>i \<alpha>}"
  by (cases \<alpha> ; auto simp: smap1_def)

lemma beh_fold_smap1:
  assumes "finite F" 
  shows "beh\<^sub>i (Finite_Set.fold (smap1 M) \<alpha> F) = {(m\<^sub>1, upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd (F \<inter> dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
  using assms
proof (induct)
  case empty
  then show ?case by (cases \<alpha> ; auto)
next
  case (insert x F)
  hence f: "Finite_Set.fold (smap1 M) \<alpha> (insert x F) = 
         smap1 M x (Finite_Set.fold (smap1 M) \<alpha> F)"
    using cfi.fold_insert_idem by blast

  show ?case using insert(1)
    unfolding f beh_smap1 insert(3)
    apply auto unfolding o_def 
    apply (intro exI conjI)
    apply blast
    apply (metis Int_Un_distrib2 Un_insert_right inf_bot_right sup_inf_absorb)
    apply (intro exI conjI)
    prefer 2
    apply blast
    apply simp
    apply (metis Int_Un_distrib2 Un_insert_right inf_bot_right sup_inf_absorb)
    done
qed

lemma beh_smap [simp]:
  "beh\<^sub>i (smap \<alpha> M) = {(m\<^sub>1,upd (wr \<alpha>) (st m) m\<^sub>1) | m m\<^sub>1. (upd (dom M) (the o M) m\<^sub>1,m) \<in> beh\<^sub>i \<alpha>}"
proof -
  have "finite (rd \<alpha>)" by auto
  hence "beh\<^sub>i (Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha>)) = 
          {(m\<^sub>1, upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd ((rd \<alpha>) \<inter> dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
    using beh_fold_smap1 by blast

  also have "... = {(m\<^sub>1, upd (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd (dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
    apply (cases \<alpha>; auto)
    apply (rule equality; auto)
    apply fastforce
    apply (rule equality; auto)
    apply fastforce
     apply (subgoal_tac "eval (upd (deps x2 \<inter> dom M) (the \<circ> M) m\<^sub>1) x2 = eval (upd (dom M) (the \<circ> M) m\<^sub>1) x2")
    apply simp
    apply (rule eval_eq_state)
    apply auto
    apply (subgoal_tac "eval (upd (deps x2 \<inter> dom M) (the \<circ> M) m\<^sub>1) x2 = eval (upd (dom M) (the \<circ> M) m\<^sub>1) x2")
    apply simp
    apply (rule eval_eq_state)
    apply auto
    done

  finally show ?thesis unfolding smap_def .
qed

end