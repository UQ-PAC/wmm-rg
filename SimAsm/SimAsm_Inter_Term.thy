theory SimAsm_Inter_Term
  imports SimAsm_Inter_Exec "HOL-Library.While_Combinator" "HOL-Eisbach.Eisbach"
begin

text \<open>
Theorems to demonstrate termination of the SimAsm_Inter analysis 
and demonstrate its conversion to executable definitions.
\<close>

section \<open>Termination Proof\<close>

abbreviation vars
  where "vars p \<equiv> (rds p |\<union>| wrs p |\<union>| esc p |\<union>| Sup (snd ` (fset (pairs p))))"

definition nmax
  where "nmax V \<equiv> if V = {||} then 0 else fMax V"

definition pmax
  where "pmax p \<equiv> max (id p) (nmax (fst |`| pairs p))"

definition Pmax
  where "Pmax P \<equiv> if P = {} then 0 else Max (pmax ` P)"

definition varsL
  where "varsL l = Sup ((\<lambda>p. fwr p |\<union>| frd p) ` (set l))"

definition all_points
  where "all_points vs i \<equiv> {p. vars p |\<subseteq>| vs \<and> id p \<le> i \<and> (nmax (fst |`| (pairs p))) \<le> i}"


lemma finite_all_points [intro]:
  "finite (all_points vs i :: ('a, 'b) point set)"
proof -
  let ?f = "\<lambda>d w r b e p. \<lparr>id = d, wrs = w, rds = r, bar = b, esc = e, pairs = p\<rparr>"
  have a: "finite {w. w |\<subseteq>| vs}"
  proof -
    have "finite (Abs_fset ` {w. w \<subseteq> fset vs})" by simp
    moreover have "{w. w |\<subseteq>| vs} \<subseteq> Abs_fset ` {w. w \<subseteq> fset vs}"
      by (auto simp: fset_inverse less_eq_fset.rep_eq rev_image_eqI)
    ultimately show ?thesis by (meson finite_subset)
  qed
  have b: "finite {p. nmax p \<le> i}"
  proof -
    have "finite {p. p \<subseteq> {j. j \<le> i}}" by blast
    hence f: "finite {p. finite p \<and> Max p \<le> i}"
      by (rule rev_finite_subset; insert Max.boundedE; auto)
    hence "finite (insert {||} (Abs_fset ` {p. finite p \<and> Max p \<le> i}))" 
      by blast
    thus ?thesis
      apply (rule rev_finite_subset)
      apply (auto simp: nmax_def)
      by (metis (no_types, lifting) fMax.F.rep_eq finite_fset fset_inverse image_iff mem_Collect_eq)
  qed

  have e: "finite {p. (snd  p) |\<subseteq>| vs \<and>  (fst  p) \<le> i}"
    apply (rule finite_subset[where 
              B="\<Union>d \<in> {d. d |\<subseteq>| vs}. \<Union>e \<in> {e.  e \<le> i}. {(e,d)}"])
    apply fastforce
    using b a by simp

  have e: "finite {fset p | p. Sup (snd ` fset p) |\<subseteq>| vs \<and> nmax (fst |`| p) \<le> i}"
    apply (rule finite_subset[OF _ finite_Collect_subsets[OF e]])
    apply auto
    apply (metis (no_types, lifting) fimage.rep_eq finite_fset fsubsetD le_cSup_finite rev_image_eqI snd_conv)
    unfolding nmax_def
    apply (auto split: if_splits)
    by (metis (no_types, lifting) Max_ge dual_order.trans fMax.F.rep_eq fimage.rep_eq finite_fset fst_conv rev_image_eqI)

  hence "finite
     (Abs_fset `
      {fset p |p.
       Sup (snd ` fset p) |\<subseteq>| vs \<and>
       nmax (fst |`| p) \<le> i})"
    using finite_imageI[OF e, of Abs_fset]
    by auto

  moreover have "(Abs_fset `
      {fset p |p.
       Sup (snd ` fset p) |\<subseteq>| vs \<and>
       nmax (fst |`| p) \<le> i}) = {p. Sup (snd ` fset p) |\<subseteq>| vs \<and> nmax (fst |`| p) \<le> i}"
    apply auto
    apply (subgoal_tac "finite (fset p)")
    apply (simp add: Abs_fset_inverse fin_mono)
    using finite_fset apply blast
    apply (subgoal_tac "finite (fset p)")
    apply (simp add: fset_inverse)
    using finite_fset apply blast
    by (metis (mono_tags, lifting) fset_inverse image_eqI mem_Collect_eq) 

  ultimately have e: "finite {p. Sup (snd ` fset p) |\<subseteq>| vs \<and> nmax (fst |`| p) \<le> i}"
    by simp

  have c: "finite {?f d w r b e p | d w r b e p. w |\<subseteq>| vs \<and> r |\<subseteq>| vs \<and> e |\<subseteq>| vs \<and> Sup (snd ` fset p) |\<subseteq>| vs \<and> d \<le> i \<and> nmax (fst |`| p) \<le> i}"
    using a e finite_subset[where 
        A="{?f d w r b e p | d w r b e p. w |\<subseteq>| vs \<and> r |\<subseteq>| vs \<and> e |\<subseteq>| vs \<and> Sup (snd ` fset p) |\<subseteq>| vs \<and> d \<le> i \<and> nmax (fst |`| p) \<le> i}" and 
        B="\<Union>d \<in> {d. d \<le> i}. \<Union>w \<in> {w. w |\<subseteq>| vs}. \<Union>r \<in> {r. r |\<subseteq>| vs}. \<Union>b \<in> UNIV. \<Union>e \<in> {e. e |\<subseteq>| vs}. \<Union>p \<in> {p. Sup (snd ` fset p) |\<subseteq>| vs \<and> nmax (fst |`| p) \<le> i}. {?f d w r b e p}"]
    by fastforce
  have d: "all_points vs i \<subseteq> {?f d w r b e p | d w r b e p. w |\<subseteq>| vs \<and> r |\<subseteq>| vs \<and>  e |\<subseteq>| vs \<and> Sup (snd ` fset p) |\<subseteq>| vs \<and> d \<le> i \<and> nmax (fst |`| p) \<le> i}"
    unfolding all_points_def
    by (smt Collect_mono SimAsm_Inter_Exec.point.surjective old.unit.exhaust sup.boundedE)
  show "finite (all_points vs i :: ('a, 'b) point set)"
    using finite_subset[OF d c] .
qed

lemma all_points_rel:
  "P |\<subseteq>| P' \<Longrightarrow> i \<le> i' \<Longrightarrow> all_points P i \<subseteq> all_points P' i'"
  unfolding all_points_def by auto

lemma max_fg:
  assumes "finite P" "\<forall>p. f p \<le> g p"
  shows "Max (f ` P) \<le> Max (g ` P)"
  using assms 
  by (smt Max_ge_iff Max_in finite_imageI imageE image_eqI image_is_empty order_refl) 

lemma Max_max :
  "finite V \<Longrightarrow> Max ((\<lambda>p. max (f p) (g p)) ` V) = max (Max (f ` V)) (Max (g ` V))" (is "finite V \<Longrightarrow> ?L = ?R")
proof -
  assume a: "finite V"
  have "?L \<ge> ?R"
  proof -
    have "Max (f ` V) \<le> ?L" using a by (rule max_fg) auto
    moreover have "Max (g ` V) \<le> ?L" using a by (rule max_fg) auto
    ultimately show "?L \<ge> ?R" by auto
  qed
  moreover have "?R \<ge> ?L"
  proof (cases "Max (f ` V) \<ge> Max (g ` V)")
    case True
    hence "max (Max (f ` V)) (Max (g ` V)) = Max (f ` V)" using max_absorb1 by blast
    moreover have "(MAX p\<in>V. max (f p) (g p)) \<le> (Max (f ` V))" using a
      by (smt Max_ge Max_in calculation dual_order.trans finite_imageI image_iff image_is_empty max.absorb_iff1 max_def)
    ultimately show ?thesis by auto
  next
    case False
    hence "max (Max (f ` V)) (Max (g ` V)) = Max (g ` V)" using linear max_absorb2 by blast
    moreover have "(MAX p\<in>V. max (f p) (g p)) \<le> (Max (g ` V))" using a
      by (smt Max_ge Max_in calculation dual_order.trans finite_imageI image_iff image_is_empty max.absorb_iff1 max_def)
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis using eq_iff by blast
qed

lemma set_all_points_bound:
  "finite P \<Longrightarrow> P \<subseteq> all_points (Sup (vars ` P)) (Pmax P)"
  unfolding all_points_def
proof (clarsimp, intro conjI, goal_cases)
  case (1 x)
  hence "vars x |\<subseteq>| Sup (vars ` P)" 
    by (meson finite_imageI image_iff le_cSup_finite)
  then show ?case by blast
next
  case (2 x)
  hence "vars x |\<subseteq>| Sup (vars ` P)" 
    by (meson finite_imageI image_iff le_cSup_finite)
  then show ?case by blast
next
  case (3 x)
  hence "vars x |\<subseteq>| Sup (vars ` P)" 
    by (meson finite_imageI image_iff le_cSup_finite)
  then show ?case by blast
next
  case (5 x)
  hence "id x \<le> (MAX p\<in>P. id p)" by simp
  also have "... \<le> (MAX p\<in>P. max (id p) (nmax (fst |`| pairs p)))"
    apply (rule max_fg)
    using 5 by auto
  also have "... \<le> Pmax P" using 5 by (auto simp: Pmax_def pmax_def)
  finally show ?case .
next
  case (6 x)
  hence "nmax (fst |`| pairs x) \<le> (MAX p\<in>P. nmax (fst |`| pairs p))" by simp
  also have "... \<le> (MAX p\<in>P. max (id p) (nmax (fst |`| pairs p)))"
    apply (rule max_fg)
    using 6 by auto
  also have "... \<le> Pmax P" using 6 by (auto simp: Pmax_def pmax_def)
  finally show ?case .
next
  case (4 x)
  hence "vars x |\<subseteq>| Sup (vars ` P)" 
    by (meson finite_imageI image_iff le_cSup_finite)
  thus ?case by blast
qed

lemma set_all_points_bound':
  "finite P \<Longrightarrow> P \<subseteq> all_points (varsL l |\<union>| Sup (vars ` P)) (max (length l) (Pmax P))"
  using set_all_points_bound all_points_rel
  by (metis (mono_tags, lifting) subset_trans sup_ge2 sup_max)

lemma fsubset_sup:
  "\<forall>j \<in> Y. f j |\<subseteq>| X \<Longrightarrow> Sup (f ` Y) |\<subseteq>| X"
proof -
  assume "\<forall>j \<in> Y. f j |\<subseteq>| X"
  hence "\<forall>j \<in> Y. fset (f j) \<subseteq> fset X" by (simp add: less_eq_fset.rep_eq)
  hence "Sup ((fset o f) ` Y) \<subseteq> fset X" by auto
  thus "Sup (f ` Y) |\<subseteq>| X" 
    by (simp add: Sup_fset.rep_eq less_eq_fset.rep_eq) 
qed

lemma all_points_sub:
  assumes "Y \<subseteq> (all_points vs i :: ('a, 'b) point set)"
  shows "all_points (Sup (vars ` Y)) (Pmax Y) \<subseteq> all_points vs i"
proof (rule all_points_rel)
  have "\<forall>j \<in> pmax ` Y. j \<le> i"
    using assms by (auto simp: all_points_def pmax_def)
  moreover have "finite Y" using finite_subset[OF assms finite_all_points] .
  ultimately show "Pmax Y \<le> i" unfolding Pmax_def by auto
next
  have "\<forall>j \<in> Y. vars j |\<subseteq>| vs" using assms by (auto simp: all_points_def)
  thus "Sup (vars ` Y) |\<subseteq>| vs" by (simp add: fsubset_sup)
qed

lemma [simp]:
  "x |\<in>| Sup {} = False"
  by (simp add: Sup_fset.rep_eq notin_fset)

lemma all_points_rel_rev:
  "all_points v i \<subseteq> (all_points v' i' :: ('a, 'b) point set) \<Longrightarrow> (v |\<subseteq>| v' \<and> i \<le> i')"
proof (rule ccontr)
  assume s: "all_points v i \<subseteq> (all_points v' i' :: ('a, 'b) point set)" "\<not> (v |\<subseteq>| v' \<and> i \<le> i')"
  hence "\<not> v |\<subseteq>| v' \<or> i > i'" by auto
  hence "\<lparr>id = i, wrs = v, rds = v, bar = True, esc = {||}, pairs = {||}\<rparr> \<notin> all_points v' i'"
    by (auto simp: all_points_def nmax_def)
  moreover have "\<lparr>id = i, wrs = v, rds = v, bar = True, esc = {||}, pairs = {||}\<rparr> \<in> all_points v i"
    by (auto simp: all_points_def nmax_def)
 ultimately show "False" using s(1) by auto
qed

lemma all_points_const:
  assumes "all_points v i \<subseteq> (all_points v' i' :: ('a, 'b) point set)"
  shows "all_points (c |\<union>| v) (max ic i) \<subseteq> all_points (c |\<union>| v') (max ic i')"
proof -
  have "v |\<subseteq>| v' \<and> i \<le> i'" using all_points_rel_rev[OF assms] by auto
  thus ?thesis by (intro all_points_rel) auto
qed

lemma [simp]:
  "Sup (vars ` (all_points vs i :: ('a, 'b) point set) ) = vs"
proof -
  let ?f = "\<lambda>d w r b e p. \<lparr>id = d, wrs = w, rds = r, bar = b, esc = e, pairs = p\<rparr>"
  have a: "(all_points vs i :: ('a, 'b) point set) = {?f d w r b e p | d w r b e p. w |\<subseteq>| vs \<and> r |\<subseteq>| vs \<and> e |\<subseteq>| vs \<and> Sup (snd ` fset p) |\<subseteq>| vs \<and> d \<le> i \<and> nmax (fst |`| p) \<le> i}"
    unfolding all_points_def apply auto 
    by (metis (full_types) old.unit.exhaust point.surjective)

  have "(vars ` (all_points vs i :: ('a, 'b) point set)) = {j. j |\<subseteq>| vs}"
    apply (auto simp: a)
    apply (subgoal_tac "?f i x x True {||} {||} \<in> all_points vs i")
    unfolding a
    defer 1
    apply (auto simp: nmax_def)[1]
  proof -
    fix x :: "('a, 'b) SimAsm_State.var fset"
    assume a1: "\<lparr>point.id = i, wrs = x, rds = x, bar = True, esc = {||}, pairs = {||}\<rparr> \<in> {\<lparr>point.id = d, wrs = w, rds = r, bar = b, esc = e, pairs = p\<rparr> | d w r b e p. w |\<subseteq>| vs \<and> r |\<subseteq>| vs \<and> e |\<subseteq>| vs \<and> Sup (snd ` fset p) |\<subseteq>| vs \<and> d \<le> i \<and> nmax (fst |`| p) \<le> i}"
    have f2: "\<forall>p P f fa. (p::('a, 'b) SimAsm_Inter_Exec.point) \<notin> P \<or> (f::('a, 'b) SimAsm_State.var fset) \<noteq> fa p \<or> f \<in> fa ` P"
      by blast
    have "x = vars \<lparr>point.id = i, wrs = x, rds = x, bar = True, esc = {||}, pairs = {||}\<rparr>"
      by force
    then show "x \<in> vars ` {\<lparr>point.id = n, wrs = f, rds = fa, bar = b, esc = fb, pairs = fc\<rparr> | n f fa b fb fc. f |\<subseteq>| vs \<and> fa |\<subseteq>| vs \<and> fb |\<subseteq>| vs \<and> Sup (snd ` fset fc) |\<subseteq>| vs \<and> n \<le> i \<and> nmax (fst |`| fc) \<le> i}"
      using f2 a1 by meson
  qed

  moreover have "Sup {j. j |\<subseteq>| vs} = vs"
    by (metis cSup_eq_maximum mem_Collect_eq order_refl)
  ultimately show ?thesis by metis
qed


lemma all_points_nil:
  "(all_points vs i :: ('a, 'b) point set) \<noteq> {}"
proof -
  have a: "\<lparr>id = 0, wrs = {||}, rds = {||}, bar = True, esc = {||}, pairs = {||}\<rparr> \<in> all_points vs i"
    by (auto simp: all_points_def nmax_def)
  show ?thesis apply (rule ccontr) apply simp using a by blast
qed

lemma [simp]:
  "Pmax (all_points vs i :: ('a, 'b) point set) = i"
proof -
  let ?f = "\<lambda>d w r b e p. \<lparr>id = d, wrs = w, rds = r, bar = b, esc = e, pairs = p\<rparr>"
  have a: "(all_points vs i :: ('a, 'b) point set) = {?f d w r b e p | d w r b e p. w |\<subseteq>| vs \<and> r |\<subseteq>| vs \<and> e |\<subseteq>| vs \<and> Sup (snd ` fset p) |\<subseteq>| vs \<and> d \<le> i \<and> nmax (fst |`| p) \<le> i}"
    unfolding all_points_def apply auto 
    by (metis (full_types) old.unit.exhaust point.surjective)

  have "id ` (all_points vs i  :: ('a, 'b) point set) = {j. j \<le> i}" unfolding a
    apply auto 
    apply (subgoal_tac "?f x vs vs True {||} {|(x,{||})|} \<in> (all_points vs i  :: ('a, 'b) point set)")
    apply (metis (no_types, lifting) SimAsm_Inter_Exec.point.select_convs(1) a rev_image_eqI)
    unfolding a by (auto simp: nmax_def)
  moreover have b: "Max {j. j \<le> i} = i"
    by (metis Max_ge Max_in antisym emptyE finite_Collect_le_nat mem_Collect_eq order_refl)
  ultimately have c: "Max (id ` (all_points vs i  :: ('a, 'b) point set)) = i" by simp

  have "(nmax o (\<lambda>p. fst |`| pairs p)) ` (all_points vs i  :: ('a, 'b) point set) = {j. j \<le> i}" unfolding a
    apply auto
    apply (subgoal_tac "?f i vs vs True {||} {|(x,{||})|} \<in> all_points vs i")
    prefer 2
     apply (unfold a, auto simp: nmax_def)[1]
    apply (subgoal_tac "x \<in> (\<lambda>x. nmax (fst |`| SimAsm_Inter_Exec.point.pairs x)) ` {?f i vs vs True {||} {|(x,{||})|}}")
    prefer 2
    apply (auto simp: nmax_def)[1]
    unfolding a by fastforce
  hence d: "Max ((nmax o (\<lambda>p. fst |`| pairs p)) ` (all_points vs i  :: ('a, 'b) point set)) = i" using b by simp

  have "(MAX p\<in>(all_points vs i :: ('a, 'b) point set). max (point.id p) (nmax (fst |`| pairs p))) = i"
    using Max_max[OF finite_all_points, of id "nmax o (\<lambda>p. fst |`| pairs p)" vs i]
    unfolding c d by auto
  thus "Pmax (all_points vs i :: ('a, 'b) point set) = i"
    unfolding Pmax_def pmax_def using all_points_nil
    by auto
qed

lemma sup_in:
  assumes "finite P" "y \<in> P" "x |\<in>| f y"
  shows "x |\<in>| Sup (f ` P)"
proof -
  have "x \<in> fset (f y)" using assms(3) by (meson notin_fset)
  hence a: "x \<in> Sup ((fset o f) ` P)" using assms(2) by auto
  have f: "finite ((\<Union>a\<in>P. fset (f a)))" using assms(1) by simp
  hence "Sup ((fset o f) ` P) =  fset (Sup (f ` P))" 
    unfolding Sup_fset_def apply auto
    using Abs_fset_inverse f apply blast
    using Abs_fset_inverse f by blast  
  thus ?thesis using a notin_fset by metis
qed

lemma sup_in_l:
  assumes "i < length l" "x |\<in>| f (l ! i)"
  shows "x |\<in>| Sup (f ` set l)"
  using assms sup_in[of "set l" "l ! i" x f] by auto

lemma [simp]:
  "nmax (finsert a b) = max (a :: nat) (nmax b)"
  unfolding nmax_def by auto

lemma stren_all_points:
  "finite P \<Longrightarrow> xa \<in> P \<Longrightarrow> tag x < length l \<Longrightarrow>
          stren (l ! tag x) xa
          \<in> all_points
              (varsL l |\<union>| Sup (vars ` P))
              (max (length l) (Pmax P))"
  unfolding stren_def
  apply (subgoal_tac "xa \<in> all_points
              (varsL l |\<union>| Sup (vars ` P))
              (max (length l) (Pmax P))")
  apply (auto simp: all_points_def varsL_def)
  apply (rule sup_in_l; blast)
  apply (rule sup_in_l; blast)

  apply (subgoal_tac "xb |\<in>| Sup (vars ` P)")
  apply simp
  apply (rule sup_in)
  apply blast
  apply blast
  apply blast

  apply (subgoal_tac "xb |\<in>| Sup (vars ` P)")
  apply simp
  apply (rule sup_in)
  apply blast
  apply blast
  apply blast

  apply (subgoal_tac "xb |\<in>| Sup (vars ` P)")
  apply simp
  apply (rule sup_in)
  apply blast
  apply blast
  apply blast

  apply (subgoal_tac "xb |\<in>| Sup (vars ` P)")
  apply simp
  apply (rule sup_in)
  apply blast
  apply blast
  apply blast

  unfolding Pmax_def pmax_def
  apply (simp add: Max_max)
  apply (metis Max.bounded_iff empty_iff finite_imageI image_eqI max.cobounded1 max.coboundedI2)
  apply (simp add: Max_max)
  by (meson Max_ge empty_iff finite_imageI imageI le_max_iff_disj)



lemma [simp]:
  "finite b \<Longrightarrow> x |\<in>| Sup (insert a b) = (x |\<in>| a \<or> x |\<in>| Sup b)"
  unfolding Sup_fset_def
  apply auto
  by (metis Abs_fset_inverse Un_iff finite_UN_I finite_UnI finite_fset mem_Collect_eq notin_fset)+

lemma "finite (fset s)"
  by simp

lemma wken_all_points:
  "finite P \<Longrightarrow> xa \<in> P \<Longrightarrow> tag x < length l \<Longrightarrow>
          wken (tag x) (l ! tag x) xa
          \<in> all_points
              (varsL l |\<union>| Sup (vars ` P))
              (max (length l) (Pmax P))"
  unfolding wken_def
  apply (subgoal_tac "xa \<in> all_points
              (varsL l |\<union>| Sup (vars ` P))
              (max (length l) (Pmax P))")
  apply (auto simp: all_points_def varsL_def)
  apply (rule sup_in_l; blast)
  apply (rule sup_in_l; blast)
  apply (rule sup_in_l; blast)

  apply (subgoal_tac "xb |\<in>| Sup (vars ` P)")
  apply simp
  apply (rule sup_in)
  apply blast
  apply blast
  apply blast

  apply (subgoal_tac "xb |\<in>| Sup (vars ` P)")
  apply simp
  apply (rule sup_in)
  apply blast
  apply blast
  apply blast

  apply (subgoal_tac "xb |\<in>| Sup (vars ` P)")
  apply simp
  apply (rule sup_in)
  apply blast
  apply blast
  apply blast

  apply (subgoal_tac "xb |\<in>| Sup (vars ` P)")
  apply simp
  apply (rule sup_in)
  apply blast
  apply blast
  apply blast

  unfolding Pmax_def pmax_def
  apply (simp add: Max_max)
  apply (metis Max.bounded_iff empty_iff finite_imageI image_eqI max.cobounded1 max.coboundedI2)
  apply (simp add: Max_max)
  by (meson Max_ge empty_iff finite_imageI imageI le_max_iff_disj)

lemma proc1_all_points:
  "finite P \<Longrightarrow> xa \<in> P \<Longrightarrow> tag x < length l \<Longrightarrow>
          proc1 (tag x) (l ! tag x) xa
          \<subseteq> all_points
              (varsL l |\<union>| Sup (vars ` P))
              (max (length l) (Pmax P))"
  unfolding proc1_def
  apply clarsimp
  apply (intro conjI impI)
  using stren_all_points apply blast
  using stren_all_points apply blast
  using wken_all_points apply blast
  done

lemma gen_all_points:
  "tag x < length l \<Longrightarrow>
          gen (tag x) (l ! tag x)
          \<in> all_points
              (varsL l |\<union>| Sup (vars ` P))
              (max (length l) (Pmax P))"
  unfolding all_points_def nmax_def varsL_def
  apply auto
  apply (rule sup_in_l; blast)+
  done

lemma rif_bound:
  "finite P \<Longrightarrow> rif c l P \<subseteq> (all_points (varsL l |\<union>| Sup (vars ` P)) (max (length l) (Pmax P)) :: ('a, 'b) point set)"
proof (induct c arbitrary: P)
  case Nil
  then show ?case using set_all_points_bound' by auto
next
  case (Basic x)
  show ?case using Basic
    apply (auto simp: rif\<^sub>i_def)
    apply (rule gen_all_points; auto)
    using proc1_all_points apply blast
    using set_all_points_bound' by blast
next
  case (Seq c1 c2)
  let ?V="(all_points(varsL l |\<union>| Sup (vars ` P)) (max (length l) (Pmax P)) :: ('a, 'b) point set)"
  have f: "finite ?V" using finite_all_points by auto
  show ?case using Seq(1)[OF f] Seq(2)[OF Seq(3)] by simp (meson dual_order.trans monoD mono_rif)
next
  case (Choice c1 c2)
  then show ?case by auto
next
  case (Loop c)
  show ?case
    unfolding rif.simps
    apply (rule lfp_lowerbound)
    using Loop(1)[OF finite_all_points, of "(varsL l |\<union>| Sup (vars ` P))" "(max (length l) (Pmax P))"] set_all_points_bound'[OF Loop(2), of l]
    by auto    
next
  case (Parallel c1 c2)
  show ?case unfolding rif.simps using set_all_points_bound'[OF Parallel(3)] by auto
next
  case (Thread c)
  show ?case unfolding rif.simps using set_all_points_bound'[OF Thread(2)] by auto
qed

subsection \<open>While Rule\<close>

lemma rif_While:
  fixes b c P l
  assumes "finite (P :: ('a, 'b) point set)"
  defines "f == (\<lambda>Y. (P \<union> rif c l Y))"
  shows "rif (Loop c) l P = while (\<lambda>Y. f Y \<noteq> Y) f {}" (is "_ = ?r")
proof -
  let ?V = "all_points (varsL l |\<union>| Sup (vars ` P)) (max (length l) (Pmax P)) :: ('a, 'b) point set"
  have "lfp f = ?r"
  proof(rule lfp_while[where C = "?V"])
    show "mono f" using f_def mono_union_rif' by blast
  next
    fix Y assume a: "Y \<subseteq> ?V"
    have f: "finite Y" using a finite_all_points finite_subset by blast 
    have "P \<subseteq> ?V" using set_all_points_bound' assms(1) by blast
    moreover have "rif c l Y \<subseteq> ?V"
      using rif_bound[OF f, of c l] all_points_const[OF all_points_sub[OF a]] by force
    ultimately show "f Y \<subseteq> ?V" unfolding f_def by blast
  next
    show "finite ?V" by (rule finite_all_points)
  qed
  thus ?thesis unfolding f_def rif.simps(3) by blast
qed

lemma rif_While_let: "finite X \<Longrightarrow> rif (Loop c) l X =
  (let f = (\<lambda>Y. X \<union> rif c l Y) in while (\<lambda>Y. f Y \<noteq> Y) f {})"
  by (simp add: rif_While)

lemma rif_While_set: "rif (Loop c) l (set xs) =
  (let f = (\<lambda>Y. set xs \<union> rif c l Y) in while (\<lambda>Y. f Y \<noteq> Y) f {})"
  by (rule rif_While_let, simp)

lemmas [code] = rif.simps(1,2,4,5,6,7) rif_While_set

section \<open>fset Execution\<close>

text \<open>List implementation of fset, similar to that of set\<close>

code_datatype fset_of_list

lemma fset_empty [code]:
  "{||} = fset_of_list []"
  by simp

lemma fset_insert [code]:
  "finsert a (fset_of_list x) = fset_of_list (List.insert a x)"
  by (simp add: List.insert_def finsert_absorb fset_of_list_elem)

lemma fset_union [code]:
  "fset_of_list a |\<union>| fset_of_list b = fset_of_list (List.union a b)"
  by (metis fset_of_list.abs_eq fset_of_list_append set_append set_union)

lemma fset_inter [code]:
  "A |\<inter>| fset_of_list xs = fset_of_list (List.filter (\<lambda>x. x |\<in>| A) xs)"
  by auto

lemma fset_remove [code]:
  "fset_of_list xs |-| A = fset_of_list (List.filter (\<lambda>x. x |\<notin>| A) xs)"
  by auto

lemma fset_hasGlobal [code]:
  "hasGlobal\<^sub>e (fset_of_list a) = hasGlobalL a"
  by (induct a) (auto simp: hasGlobal_def; case_tac a1, auto)+

lemma fset_mem [code]:
  "(x |\<in>| fset_of_list F) = (List.member F x)"
  by (simp add: fset_of_list_elem member_def)

lemma fset_subset [code]:
  "fset_of_list xs \<le> B \<longleftrightarrow> (\<forall>x\<in>set xs. x |\<in>| B)"
  using fset_of_list.rep_eq notin_fset 
  by (metis (full_types) fin_mono fsubsetI) 

declare fset_of_list_simps [code_post]

section \<open>Tactics\<close>

text \<open>Tactic to match the executable analysis within more abstract properties\<close>

attribute_setup get_conv = \<open>Args.term >> (fn t =>
        Thm.rule_attribute [] (fn context => fn _ =>
          (Code_Simp.dynamic_conv (Context.proof_of context) o Thm.cterm_of (Context.proof_of context)) t))\<close>

method rif_eval = 
  (unfold rif_executable; simp add: Let_def del: rif.simps(1,2,4,5,6,7);
   match conclusion in "wellformed R G \<longrightarrow> checks (expand_points (rif c l {}) l') R G" for c and R and G 
      and l' :: "('v :: equal,'g :: equal,'r :: equal,'a :: equal) enuml" 
      and l :: "('v,'g,'r) op list"  \<Rightarrow>
    \<open>match [[get_conv "rif c l {}"]] in U: _ \<Rightarrow> \<open>subst U\<close>\<close>)

end