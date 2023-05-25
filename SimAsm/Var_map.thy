theory Var_map
  imports Main State2
begin


(* variable: either a register or a global, where registers equal local vars *)
datatype 'r Reg = reg 'r | tmp 'r
(* datatype 'v = Reg 'r | Glb 'g *)

(* first value in Exp is a function used to combine the values from its
subexpressions into one value. *)

datatype ('var,'val) exp =
  Var "'var" | 
  Val 'val | 
  Exp "'val list \<Rightarrow> 'val" "('var,'val) exp list" (* some fct over a list of subexpr *) 

  
datatype ('var,'val) bexp = 
  Neg "('var,'val) bexp" | 
  Exp\<^sub>B "'val list \<Rightarrow> bool" "('var,'val) exp list"
  

type_synonym ('var,'val) varmap = "'var \<Rightarrow> 'val"

(* the leak operation corresponds to Cache+=x in the Refine2019 paper
    here the op also specifies where the leak goes, e.g., Cache*)
datatype ('r,'v) op =
    assign "'r" "('r,'v) exp"
  | cmp "('r,'v) bexp"
  | leak "'r" "('r,'v) exp"
  | full_fence
  | nop

locale expression = state st st_upd aux aux_upd 
  for st :: "'s \<Rightarrow> 'r \<Rightarrow> 'v" 
  and st_upd ("_'((2_/ :=\<^sub>u/ (2_))')" [900,0,0] 901) and aux and aux_upd ("_'((2aux:/ _)')" [900,0] 901)
(*  and locals :: "'r set"    Do we need local variables? *)
    

(* context expression *)
(* begin *)

(* definition rg :: "'s \<Rightarrow> 'r \<Rightarrow> 'v option" *)
  (* where "rg m v \<equiv> (if v \<in> locals then Some (st m v) else None)" *)

term restrict

text \<open>Domain of register variables\<close>

(* Tmp registers are also local? *)
(* abbreviation locals *)
  (* where "locals \<equiv> Reg ` UNIV" *)

(* text \<open>Domain of register variables\<close> *)
(* abbreviation globals *)
  (* where "globals \<equiv> Glb ` UNIV" *)

section \<open>Expression Language based on a generic mapping of variables to values \<close>


text \<open>Evaluate an expression given a state\<close>

fun ev\<^sub>E :: "('r,'v) varmap \<Rightarrow> ('r,'v) exp \<Rightarrow> 'v"
  where 
    "ev\<^sub>E m (Var r) =  m r" |
    "ev\<^sub>E _ (Val v) = v" |
    "ev\<^sub>E m (Exp f rs) = f (map (ev\<^sub>E m) rs)"  (* eg, Exp(+ a1 a2 a3) = (ev a1) + (ev a2) + (ev a3) *)

text \<open>The syntactic dependencies of an expression\<close>
fun deps\<^sub>E :: "('r,_) exp \<Rightarrow> 'r set"
  where 
    "deps\<^sub>E (Var r) = {r}" |
    "deps\<^sub>E (Exp _ rs) = \<Union>(deps\<^sub>E ` set rs)" |
    "deps\<^sub>E _ = {}"


text \<open>Substitute a variable for an expression\<close>
fun subst\<^sub>E :: "('r,'v) exp \<Rightarrow> 'r \<Rightarrow> ('r,'v) exp \<Rightarrow> ('r,'v) exp"
  where
    "subst\<^sub>E (Var r) r' e = (if r = r' then e else Var r)" |
    "subst\<^sub>E (Exp f rs) r e = (Exp f (map (\<lambda>x. subst\<^sub>E x r e) rs))" |
    "subst\<^sub>E e _ _ = e"

text \<open>Evaluate an expression given a state \<close>
fun ev\<^sub>B :: "('r \<Rightarrow> 'v) \<Rightarrow> ('r,'v) bexp \<Rightarrow> bool"
  where 
    "ev\<^sub>B m (Neg e) = (\<not> (ev\<^sub>B m e))" |
    "ev\<^sub>B m (Exp\<^sub>B f rs) = f (map (ev\<^sub>E m) rs)"

text \<open>The syntactic dependencies of an expression\<close>
fun deps\<^sub>B :: "('r,'v) bexp \<Rightarrow> 'r set"
  where 
    "deps\<^sub>B (Neg e) = deps\<^sub>B e" |
    "deps\<^sub>B (Exp\<^sub>B _ rs) = \<Union>(deps\<^sub>E ` set rs)"

text \<open>Substitute a variable for an expression\<close>
fun subst\<^sub>B :: "('r,'v) bexp \<Rightarrow> 'r \<Rightarrow> ('r,'v) exp \<Rightarrow> ('r,'v) bexp"
  where
    "subst\<^sub>B (Neg b) r e = Neg (subst\<^sub>B b r e)" |
    "subst\<^sub>B (Exp\<^sub>B f rs) r e = (Exp\<^sub>B f (map (\<lambda>x. subst\<^sub>E x r e) rs))"


section \<open>Operations\<close>

      

text \<open>Variables written by an operation\<close>
fun wr :: "('r,'v) op \<Rightarrow> 'r set"
  where 
    "wr (assign y _) = {y}" |
    "wr (leak c _) = {}" |         (* for the sake of fwd we assume no var is written  *)
(*    "wr (leak c _) = {c}" |         (* where variable c is part of the the (base t) *) *)
    "wr _ = {}"

text \<open>Variables read by an operation\<close>
fun rd :: "('r,'v) op \<Rightarrow> 'r set"
  where
    "rd (assign _ e) = deps\<^sub>E e" |
    "rd (cmp b) = deps\<^sub>B b" |
    "rd (leak _ e) = deps\<^sub>E e" |
    "rd _ = {}"

text \<open>Test if an instruction is a memory barrier\<close>
fun barriers :: "('r,'v) op \<Rightarrow> bool"
  where "barriers full_fence = True" | "barriers _ = False"

text \<open>Operation Substitution\<close>
fun subst\<^sub>i :: "('r,'v) op \<Rightarrow> 'r \<Rightarrow> ('r,'v) exp \<Rightarrow> ('r,'v) op"
  where
    "subst\<^sub>i (assign x e) y f = assign x (subst\<^sub>E e y f)" |
    "subst\<^sub>i (cmp b) y f = cmp (subst\<^sub>B b y f)" |
    "subst\<^sub>i (leak c e) y f = leak c (subst\<^sub>E e y f)" |
    "subst\<^sub>i \<alpha> _ _ = \<alpha>"

text \<open>Replaces a variable r with the corresponding value from the map V.\<close>
definition smap1
  where "smap1 V r \<alpha> \<equiv> case V r of None \<Rightarrow> \<alpha> | Some x' \<Rightarrow> subst\<^sub>i \<alpha> r (Val x')"

text \<open>Replaces all variables in V that are read by \<alpha>.\<close>
definition smap 
  where "smap \<alpha> V \<equiv> Finite_Set.fold (smap1 V) \<alpha> (rd \<alpha>)"

text \<open>Given \<alpha>, chaos all variables within the given set V.\<close>
definition forall
  where "forall V \<alpha> \<equiv> {smap \<alpha> M | M. dom M = V}"

text \<open> Some lemmas \<close>

(* simple lemmas from SimAsm_State *)

lemma [simp]:
  "(m (r := e)) q = (if r = q then e else m q)"
  by (auto simp: fun_upd_def)

(* lemma [simp]: *)
  (* "rg' (m(Reg x := e)) = (rg' m)(x := e)" *)
  (* by (auto simp: fun_upd_def rg'_def) *)


lemma map_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a := b))(c := d) = (m(c := d))(a := b)"
  unfolding fun_upd_twist  by auto

(* lemma [simp]: *)
  (* "rg' m x = m (Reg x)" *)
  (* by (auto simp: rg'_def) *)

(* lemma [simp]: *)
  (* "glb' m x = m (Glb x)" *)
  (* by (auto simp: glb'_def) *)

(* lemma [simp]: *)
  (* "g \<notin> locals \<Longrightarrow> rg (m(g :=\<^sub>u x)) = rg m" *)
  (* unfolding rg_def by auto *)

(* lemma [dest]: *)
  (* "rg m = rg m' \<Longrightarrow> x \<in> locals \<Longrightarrow> st m x = st m' x" *)
  (* unfolding rg_def by (meson option.inject) *)

(* lemma [intro]: *)
  (* "(\<And>x. x \<in> locals \<Longrightarrow> st m x = st m' x) \<Longrightarrow> rg m = rg m'" *)
  (* unfolding rg_def by auto *)

lemma [simp]:
  "P O {(m, m'). m' = m} = P"
  by auto


(*-  lemmas from SimAsm_Exp  -------------*)


lemma ev_subst\<^sub>E' [simp]:
  "ev\<^sub>E m (subst\<^sub>E e r f) = ev\<^sub>E (m (r := (ev\<^sub>E m f))) e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r f)) rs = map (ev\<^sub>E (m(r := ev\<^sub>E m f))) rs" 
    using fun_upd_def apply auto using Exp by presburger
  then show ?case by (simp add: fun_upd_def)
qed auto

lemma ev_subst\<^sub>B [simp]:
  "ev\<^sub>B m (subst\<^sub>B b r e) = ev\<^sub>B (m(r := (ev\<^sub>E m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (ev\<^sub>E m \<circ> (\<lambda>x. subst\<^sub>E x r e)) rs = map (ev\<^sub>E (m(r := ev\<^sub>E m e))) rs"
    by (auto simp: fun_upd_def)     
  then show ?case by (simp add: fun_upd_def)
qed simp

lemma subst_nop\<^sub>E [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> subst\<^sub>E e r f = e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (\<lambda>x. subst\<^sub>E x r f) rs = rs" by (induct rs) auto
  show ?case by simp
qed auto

lemma ev_nop\<^sub>E' [simp]:
  "r \<notin> deps\<^sub>E e \<Longrightarrow> ev\<^sub>E (m(r := f)) e = ev\<^sub>E m e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E (m(r := f))) rs = map (ev\<^sub>E m) rs" 
    using fun_upd_def apply auto using Exp by blast
  then show ?case by (metis ev\<^sub>E.simps(3))
qed auto

lemma ev_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> ev\<^sub>B (m(r := f)) b = ev\<^sub>B m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev\<^sub>E (m(r := f))) rs = map (ev\<^sub>E m) rs"
    using ev_nop\<^sub>E'[of r _ m f] by (auto simp: fun_upd_def) 
  then show ?case by (metis ev\<^sub>B.simps(2))
qed simp

lemma subst_nop\<^sub>B [simp]:
  "r \<notin> deps\<^sub>B e \<Longrightarrow> subst\<^sub>B e r f = e"
proof (induct e)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (\<lambda>x. subst\<^sub>E x r f) rs = rs"  by (induct rs) auto
  show ?case by simp
qed auto


lemma deps_subst\<^sub>E [simp]:
  "deps\<^sub>E (subst\<^sub>E e x e') = deps\<^sub>E e - {x} \<union> (if x \<in> deps\<^sub>E e then deps\<^sub>E e' else {})"
  by (induct e; auto simp: if_splits)

lemma deps_subst\<^sub>B [simp]:
  "deps\<^sub>B (subst\<^sub>B e x e') = deps\<^sub>B e - {x} \<union> (if x \<in> deps\<^sub>B e then deps\<^sub>E e' else {})"
  by (induct e; auto simp: if_splits)

                                    
lemma deps_ev\<^sub>E [intro]:
  "\<forall>x \<in> deps\<^sub>E e. m x = m' x \<Longrightarrow> ev\<^sub>E m e = ev\<^sub>E m' e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev\<^sub>E m) rs = map (ev\<^sub>E m') rs" by (induct rs) auto
  show ?case by simp
qed auto

lemma subst\<^sub>E_flip [simp]:
  "x \<noteq> y \<Longrightarrow> 
       subst\<^sub>E (subst\<^sub>E e x (Val v')) y (Val v) = subst\<^sub>E (subst\<^sub>E e y (Val v)) x (Val v')"
  by (induct e) auto

lemma subst\<^sub>E_rep [simp]:
  "subst\<^sub>E (subst\<^sub>E e x (Val v')) x (Val v) = subst\<^sub>E e x (Val v')"
  by (induct e) auto

lemma finite_deps\<^sub>E [intro]:
  "finite (deps\<^sub>E e)"
  by (induct e) auto

lemma finite_deps\<^sub>B [intro]:
  "finite (deps\<^sub>B e)"
  by (induct e) auto


(* lemma local_ev\<^sub>E [intro]: *)
  (* "deps\<^sub>E e \<subseteq> locals \<Longrightarrow> rg' m = rg' m' \<Longrightarrow> ev\<^sub>E m e = ev\<^sub>E m' e" *)
  (* by auto *)

subsection \<open>Operations\<close>

lemma subst_wr [simp]:
  "wr (subst\<^sub>i \<alpha> x e) = wr \<alpha>"
  by (cases \<alpha>; auto)

lemma subst_rd [simp]:
  "rd (subst\<^sub>i \<alpha> x e) = rd \<alpha> - {x} \<union> (if x \<in> rd \<alpha> then deps\<^sub>E e else {})"
  by (cases \<alpha>; auto)

lemma subst_barriers [simp]:
  "barriers (subst\<^sub>i \<alpha> x e) = barriers \<alpha>"
  by (cases \<alpha>; auto)

lemma subst_not_fence [simp]:
  "(subst\<^sub>i \<alpha> x e \<noteq> full_fence) = (\<alpha> \<noteq> full_fence)"
  by (cases \<alpha>; auto)

lemma subst_nop [simp]:
  "x \<notin> rd \<beta> \<Longrightarrow> subst\<^sub>i \<beta> x e = \<beta>"
  unfolding smap1_def by (cases \<beta>) (auto split: if_splits)

lemma finite_rd [intro]:
  "finite (rd \<alpha>)"  
by (cases \<alpha>) auto

abbreviation ncmp
  where "ncmp b \<equiv> cmp (Neg b)"


subsection \<open>smap1 Theories\<close>

lemma smap1_flip [simp]:
  "smap1 V y (smap1 V x \<alpha>) = smap1 V x (smap1 V y \<alpha>)"
unfolding smap1_def
proof (induct \<alpha>; cases "x = y"; cases "V x"; cases "V y"; simp; goal_cases)
  case (1 bexp a aa)
  then show ?case by (induct bexp) auto
qed


lemma smap1_rep [simp]:
  "smap1 V x (smap1 V x \<alpha>) = smap1 V x \<alpha>"
unfolding smap1_def by (cases "V x") auto

interpretation cfi: comp_fun_idem "smap1 V"  by standard auto

lemma smap1_rd [simp]:
  "rd (smap1 M x \<beta>) = rd \<beta> - ({x} \<inter> dom M)"
unfolding smap1_def by (cases "M x") auto

lemma smap1_wr [simp]:
  "wr (smap1 M x \<beta>) = wr \<beta>"
unfolding smap1_def by (cases "M x") auto

lemma smap1_barriers [simp]:
  "barriers (smap1 M x \<beta>) = barriers \<beta>"
unfolding smap1_def by (cases "M x") auto

lemma smap1_nop [simp]:
  "x \<notin> rd \<beta> \<Longrightarrow> smap1 M x \<beta> = \<beta>"
unfolding smap1_def by (cases "M x") auto

lemma smap1_nop2 [simp]:
  "M x = None \<Longrightarrow> smap1 M x \<beta> = \<beta>"
unfolding smap1_def by (cases "M x") auto

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
    using cfi.fold_insert_idem by auto
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
    using cfi.fold_insert_idem by auto
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
    using cfi.fold_insert_idem by auto
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
    using cfi.fold_insert_idem by auto
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
    using cfi.fold_insert_idem by (simp add: finite_rd)
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
    fix M :: "'a \<Rightarrow> 'b option" assume d: "dom M = insert x V" "x \<in> V"
    hence "smap \<alpha> M = subst\<^sub>i (smap \<alpha> M) x (Val (the (M x)))" by simp
    moreover have "dom M = V" using d by auto
    ultimately show "\<exists>c \<alpha>'. smap \<alpha> M = subst\<^sub>i \<alpha>' x (Val c) \<and> (\<exists>M. \<alpha>' = smap \<alpha> M \<and> dom M = V)"
      by blast
  next
    fix M :: "'a \<Rightarrow> 'b option" assume d: "dom M = insert x V" "x \<notin> V"
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
          unfolding smap1_def using d(1) by (cases "M x") auto
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
    fix M :: "'a \<Rightarrow> 'b option" and c assume d: "V = dom M" "x \<in> V" 
    have "dom M = insert x (dom M)" using d by auto
    moreover have "subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> M" using d by simp
    ultimately show "\<exists>Ma. subst\<^sub>i (smap \<alpha> M) x (Val c) = smap \<alpha> Ma \<and> dom Ma = insert x (dom M)"
      by blast
  next
    fix M :: "'a \<Rightarrow> 'b option" and c assume d: "V = dom M" "x \<notin> V" 
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

(* end (*of locale *) *)

(*
lemma local_ev\<^sub>E' [intro]:
  "deps\<^sub>E e \<subseteq> locals \<Longrightarrow> rg' m = rg' m' \<Longrightarrow> ev\<^sub>E m e = ev\<^sub>E m' e"
  by (standard; intro ballI) auto
*)


end



(*todo: smap1 lemmas only needed for static analysis part (to compute reorderable pairs?)
        leave for now  *)

(*
lemma beh_smap1 [simp]:
  "beh\<^sub>i (smap1 M x \<alpha>) = {(t,updTree (wr \<alpha>) (lookupSome t') t) |t t'.
                           (updTree_part ({x} \<inter> dom M) (M) t,t') \<in> beh\<^sub>i \<alpha>}"
(*  apply (cases \<alpha> ; auto simp: smap1_def updTree_def updTree_part_def) *)
proof (cases \<alpha>)
  case (assign x11 x12)
  then show ?thesis sorry
next
  case (cmp b)
  then show ?thesis 
  proof -
    have a0:"smap1 M x (cmp b) = (if x \<in> dom M then subst\<^sub>i (cmp b) x (Val (the (M x))) else (cmp b))"
       using smap1_def cmp by blast
     then have a1:"beh\<^sub>i (smap1 M x (cmp b)) = 
         {(t,t'). t=t' \<and> ev\<^sub>B t (if (x \<in> dom M) then (subst\<^sub>B b x (Val(the (M x)))) else b)}" 
      using smap1_def beh\<^sub>i.simps(2) subst\<^sub>i.simps(2) cmp by force
    then have a2:"... = {(t,t)| t . ev\<^sub>B t (if (x \<in> dom M) then (subst\<^sub>B b x (Val(the (M x)))) else b)}"
      using a1 by blast
    have b0:"wr(cmp b) = {}" by simp
    have b1:"\<forall> t t'. updTree (wr (cmp b)) (lookupSome t') t = t" using updTree_def b0 by simp
    then have b2:"{(t,updTree(wr(cmp b))(lookupSome t') t)|t t'.
                                  (updTree_part ({x} \<inter> dom M) M t, t') \<in> beh\<^sub>i (cmp b)} = 
                    {(t,t)| t t'. (updTree_part ({x} \<inter> dom M) M t, t') \<in> beh\<^sub>i (cmp b)}" 
      using b1 by simp
    then have b3:"... = {(t,t)| t. ev\<^sub>B (updTree_part ({x} \<inter> dom M) M t) b}" using b2 beh\<^sub>i.simps(2) 
         by simp
    then have b4:"... = {(t,t)| t . ev\<^sub>B t (if (x \<in> dom M) then (subst\<^sub>B b x (Val(the (M x)))) else b)}"
      using ev_updTreePart sorry
    then show ?thesis using a0 a1 a2 b1 b2 b3 cmp by (smt (verit, del_insts) Collect_cong)
  qed
qed auto
*)

(*

lemma beh_fold_smap1:
  assumes "finite F" 
  shows "beh\<^sub>i (Finite_Set.fold (smap1 M) \<alpha> F) = {(m\<^sub>1, upd_part (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd (F \<inter> dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
  using assms
proof (induct)
  case empty
  then show ?case apply (cases \<alpha> ; auto) sorry
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
    sorry
(*  
  apply (metis Int_Un_distrib2 Un_insert_right inf_bot_right sup_inf_absorb)
    apply (intro exI conjI)
    prefer 2
    apply blast
    apply simp
    apply (metis Int_Un_distrib2 Un_insert_right inf_bot_right sup_inf_absorb)
    done
*)
qed


lemma beh_smap [simp]:
  "beh\<^sub>i (smap \<alpha> M) = {(m\<^sub>1,upd_part (wr \<alpha>) (st m) m\<^sub>1) | m m\<^sub>1. (upd (dom M) (the o M) m\<^sub>1,m) \<in> beh\<^sub>i \<alpha>}"
proof -
  have "finite (rd \<alpha>)" by auto
  hence "beh\<^sub>i (Finite_Set.fold (smap1 M) \<alpha> (rd \<alpha>)) = 
          {(m\<^sub>1, upd_part (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd ((rd \<alpha>) \<inter> dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
    using beh_fold_smap1 by blast

  also have "... = {(m\<^sub>1, upd_part (wr \<alpha>) (st m) m\<^sub>1) |m m\<^sub>1. (upd (dom M) (the \<circ> M) m\<^sub>1, m) \<in> beh\<^sub>i \<alpha>}"
    apply (cases \<alpha>; auto)
 sorry
  finally show ?thesis unfolding smap_def .
qed
*)
