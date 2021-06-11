theory SimAsm_Inter_Exec
  imports "HOL-Library.FSet" "SimAsm_Inter" 
begin

text \<open>
This theory file describes the executable interference pairs analysis
and relates it to the abstract.
\<close>

type_synonym ('v,'g,'r,'a) enumi = "('v,'g,'r,'a) pred \<times> ('v,'g,'r) op \<times> ('v,'g,'r,'a) auxfn"
type_synonym ('v,'g,'r,'a) enuml = "('v,'g,'r,'a) enumi list"

text \<open>A data point, extends an instruction with reordering information\<close>
record ('g,'r) point =
  id :: nat
  wrs :: "('g,'r) var fset"
  rds :: "('g,'r) var fset"
  bar :: bool
  esc :: "('g,'r) var fset"
  pairs :: "(nat \<times> ('g,'r) var fset) fset"

definition hasGlobal\<^sub>e
  where "hasGlobal\<^sub>e S \<equiv> \<exists>e. Glb e |\<in>| S"

fun hasGlobalL
  where "hasGlobalL (Glb x#a) = True" | 
        "hasGlobalL [] = False" |
        "hasGlobalL (b#a) = hasGlobalL a"

text \<open>Substitute a variable for an expression\<close>
fun subst :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) exp"
  where
    "subst (Var r) r' e = (if r = r' then e else Var r)" |
    "subst (Exp f rs) r e = (Exp f (map (\<lambda>x. subst x r e) rs))" |
    "subst e _ _ = e"

text \<open>The syntactic dependencies of an expression\<close>
fun ldeps :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var list"
  where 
    "ldeps (Var r) = [r]" |
    "ldeps (Exp _ rs) = List.bind rs ldeps" |
    "ldeps _ = []"

fun ldeps\<^sub>B :: "('v,'g,'r) bexp \<Rightarrow> ('g,'r) var list"
  where 
    "ldeps\<^sub>B (Neg e) = ldeps\<^sub>B e" |
    "ldeps\<^sub>B (Exp\<^sub>B _ rs) = List.bind rs ldeps"

definition fdeps 
  where "fdeps a = fset_of_list (ldeps a)"

definition fdeps\<^sub>B
  where "fdeps\<^sub>B a = fset_of_list (ldeps\<^sub>B a)"

text \<open>Variables written by an operation\<close>
fun fwr :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var fset"
  where 
    "fwr (assign y _) = {|y|}" |
    "fwr _ = {||}"

fun lfwr :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var fset"
  where 
    "lfwr (assign (Reg y) _) = {|Reg y|}" |
    "lfwr _ = {||}"

text \<open>Variables read by an operation\<close>
fun frd :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var fset"
  where
    "frd (assign _ e) = fdeps e" |
    "frd (cmp b) = fdeps\<^sub>B b" |
    "frd _ = {||}"

text \<open>Conditions under which a point is ordered after an instruction\<close>
fun ord\<^sub>e
  where
    "ord\<^sub>e nop p = (bar p)" |
    "ord\<^sub>e (cmp b) p = (bar p \<or> hasGlobal\<^sub>e (wrs p) \<or> hasGlobal\<^sub>e (fdeps\<^sub>B b |\<inter>| rds p) \<or>  wrs p |\<inter>| fdeps\<^sub>B b \<noteq> {||})" |
    "ord\<^sub>e (assign v e) p = 
      (bar p \<or> 
        hasGlobal\<^sub>e (fdeps e |\<inter>| (rds p |\<union>| wrs p)) \<or> 
        (case v of Glb g \<Rightarrow> Glb g |\<in>| wrs p | _ \<Rightarrow> False) \<or> 
        (hasGlobal\<^sub>e (fdeps e) \<and> v |\<in>| rds p))" |
    "ord\<^sub>e full_fence _ = True"

text \<open>Strengthen a point based on a strictly earlier instruction\<close>
definition stren :: "('v,'g,'r) op \<Rightarrow> ('g,'r) point \<Rightarrow> ('g,'r) point"
  where
    "stren a p = p\<lparr> wrs := wrs p |\<union>| fwr a, 
                    rds := rds p |-| lfwr a |\<union>| frd a, 
                    bar := bar p \<or> barriers a \<rparr>"

text \<open>Weaken a point based on a reorderable instruction\<close>
definition wken :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('g,'r) point \<Rightarrow> ('g,'r) point"
  where
    "wken n \<alpha> p = p\<lparr> rds := rds p - fwr \<alpha> |\<union>| 
                            (if fwr \<alpha> |\<inter>| rds p \<noteq> {||} then frd \<alpha> else {||}), 
                     esc := esc p |\<union>| fwr \<alpha>,
                     pairs := pairs p |\<union>| {|(n, esc p)|} \<rparr>"

text \<open>Convert an instruction into a point\<close>
abbreviation gen :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('g,'r) point"
  where
    "gen n a \<equiv> \<lparr> id = n, wrs = fwr a, rds = frd a, bar = barriers a, esc = {||}, pairs = {||} \<rparr>"

text \<open>Process a new instruction against one point\<close>
definition proc1 :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> (_,_) point \<Rightarrow> (_,_) point set"
  where "proc1 n \<alpha> p \<equiv> if ord\<^sub>e \<alpha> p then {stren \<alpha> p} else {stren \<alpha> p, wken n \<alpha> p}"

text \<open>Process a new instruction against a set of points\<close>
definition rif\<^sub>i :: "nat \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('g,'r) point set \<Rightarrow> ('g,'r) point set"
  where 
    "rif\<^sub>i n a P \<equiv> { gen n a } \<union> \<Union> (proc1 n a ` P)"

text \<open>Process a full program\<close>
fun rif :: "(nat, nat) com \<Rightarrow> ('v,'g,'r) op list \<Rightarrow> ('g,'r) point set \<Rightarrow> ('g,'r) point set"
  where 
    "rif (Basic a) l P = (if tag a < length l then rif\<^sub>i (tag a) (l ! (tag a)) P else P)" |
    "rif (Choice c\<^sub>1 c\<^sub>2) l P = (rif c\<^sub>1 l P \<union> rif c\<^sub>2 l P)" |
    "rif (Loop c) l P = lfp (\<lambda>Y. (P \<union> rif c l Y))" |
    "rif (c\<^sub>1 ;; c\<^sub>2) l P = rif c\<^sub>1 l (rif c\<^sub>2 l P)" |
    "rif _ _ P = P"
declare rif.simps(3)[simp del]

fun enum :: "('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> (nat, nat) com \<times> ('v,'g,'r,'a) enuml"
  where
    "enum Skip l = (com.Nil,l)" |
    "enum (Op v a f) l = (Basic (length l,{},{}),l@[(v,a,f)])" |
    "enum (Seq c\<^sub>1 c\<^sub>2) l = 
      (case enum c\<^sub>2 l of (n\<^sub>2,l) \<Rightarrow> (case enum c\<^sub>1 l of (n\<^sub>1,l) \<Rightarrow> (com.Seq n\<^sub>1 n\<^sub>2,l)))" |
    "enum (If b c\<^sub>1 c\<^sub>2) l = 
      (case enum c\<^sub>2 l of (n\<^sub>2,l) \<Rightarrow> case enum c\<^sub>1 l of (n\<^sub>1,l) \<Rightarrow> 
        (Choice (com.Seq (Basic (length l,{},{})) n\<^sub>1) (com.Seq (Basic (Suc (length l),{},{})) n\<^sub>2),
          l@[(UNIV,cmp b,state_rec.more),(UNIV,cmp (Neg b),state_rec.more)]))" |
    "enum (While b I c) l = 
      (case enum c l of (n,l) \<Rightarrow> 
        (com.Seq ((com.Seq (Basic (length l,{},{})) n)*) (Basic (Suc (length l),{},{})),
          l@[(UNIV,cmp b,state_rec.more),(UNIV,cmp (Neg b),state_rec.more)]))" |
    "enum (DoWhile I c b) l = 
      (case enum c l of (n,l) \<Rightarrow> 
        ((n ;; Basic (length l,{},{}))* ;; n ;; Basic (Suc (length l),{},{}), 
          l@[(UNIV,cmp b,state_rec.more),(UNIV,cmp (Neg b),state_rec.more)]))" 

subsection \<open>Refinement\<close>

fun expand :: "(nat, nat) com \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> (('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) com"
  where
    "expand Nil l = Nil" |
    "expand (Basic a) l = (case l ! tag a of (v,\<alpha>,f) \<Rightarrow> Basic (\<lfloor>v,\<alpha>,f\<rfloor>))" |
    "expand (com.Seq c\<^sub>1 c\<^sub>2) l = com.Seq (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Choice c\<^sub>1 c\<^sub>2) l = Choice (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Loop c\<^sub>1) l = Loop (expand c\<^sub>1 l)" |
    "expand (Parallel c\<^sub>1 c\<^sub>2) l = Parallel (expand c\<^sub>1 l) (expand c\<^sub>2 l)" |
    "expand (Thread c\<^sub>1) l = Thread (expand c\<^sub>1 l)"

fun expand_op 
  where "expand_op (v,\<alpha>,f) = \<lfloor>v,\<alpha>,f\<rfloor>"

fun expand_pairs :: "(nat \<times> ('g,'r) var fset) fset \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> (('v,'g,'r,'a) opbasic \<times> ('g,'r) var set) set"
  where
    "expand_pairs p l = {(expand_op (l ! i), fset s) | i s. (i,s) \<in> fset p}"

fun expand_point :: "('g,'r) point \<Rightarrow> ('v,'g,'r,'a) enuml \<Rightarrow> ('v,'g,'r,'a) SimAsm_Inter.point"
  where
    "expand_point p l = \<lparr> op = expand_op (l ! id p), 
                          wrs = fset (wrs p), 
                          rds = fset (rds p), 
                          bar = bar p, 
                          esc = fset (esc p),
                          pairs = expand_pairs (pairs p) l \<rparr>"

definition expand_points
  where "expand_points P l = (\<lambda>s. expand_point s l) ` P"

lemma [simp]:
  "inst (\<lfloor>x1,x2,x3\<rfloor>) = x2"
  by (auto simp: liftg_def)

lemma ldeps [simp]:
  "set (ldeps e) = deps\<^sub>E e"
proof (induct e)
  case (Exp x1a x2a)
  then show ?case apply ( simp add: fdeps_def)
    by (smt Sup.SUP_cong fset_of_list.rep_eq set_list_bind)
qed (auto simp: fdeps_def)

lemma [simp]:
  "fset (fdeps e) = deps\<^sub>E e"
  by (simp add: fset_of_list.rep_eq fdeps_def)

lemma [simp]:
  "fset (fdeps\<^sub>B e) = deps\<^sub>B e"
proof (induct e)
  case (Exp\<^sub>B x1a x2a)
  then show ?case by (simp add: fset_of_list.rep_eq fdeps\<^sub>B_def set_list_bind)
qed (auto simp: fdeps\<^sub>B_def)

lemma [simp]:
  "fset (fwr a) = wr a"
  by (cases a; auto)

lemma [simp]:
  "fset (frd a) = rd a"
  by (cases a; auto)

lemma [simp]:
  "fset (lfwr \<alpha>) = wr \<alpha> \<inter> locals"
  by (cases \<alpha>; auto; case_tac x11; auto)

lemma [simp]:
  "hasGlobal\<^sub>e V = hasGlobal (fset V)"
  unfolding hasGlobal\<^sub>e_def hasGlobal_def
  by (meson notin_fset)

lemma [simp]:
  "((map (\<lambda>a. fst (snd a)) l' @ [x2]) ! length l') = x2"
  by (metis length_map nth_append_length)

lemma [simp]:
  "(l @ [a,b]) ! Suc (length l) = b"
  by (metis append_Cons append_Nil append_assoc length_append_singleton nth_append_length)

lemma [intro]:
  "a \<noteq> b \<Longrightarrow> fset a \<noteq> fset b"
  by (simp add: fset_inject)

lemma stren_exec:
  "SimAsm_Inter.stren (expand_op \<alpha>) (expand_point p l) = expand_point (stren (fst (snd \<alpha>)) p) l"
  by (cases \<alpha>; auto simp: stren_def SimAsm_Inter.stren_def)

lemma wken_exec:
  "l ! n = \<alpha> \<Longrightarrow> SimAsm_Inter.wken (expand_op \<alpha>) (expand_point p l) = expand_point (wken n (fst (snd \<alpha>)) p) l"
  apply (clarsimp simp: wken_def SimAsm_Inter.wken_def)
  apply (intro impI conjI)
  apply (cases "l ! n"; clarsimp)
  apply (cases "l ! n"; clarsimp)
  apply (cases "l ! n"; clarsimp)
  apply force
  apply (cases "l ! n"; clarsimp)
  apply (subgoal_tac "fset (fwr b |\<inter>| point.rds p) \<noteq> fset {||}")
  apply simp
  using fset_inject apply metis
  apply (cases "l ! n"; clarsimp)
  apply (cases "l ! n"; clarsimp)
  apply force
  apply (cases "l ! n"; clarsimp)
  apply (subgoal_tac "fset (fwr b |\<inter>| point.rds p) = fset {||}")
  apply fastforce
  apply metis
  apply (cases "l ! n"; clarsimp)
  apply blast
  apply (cases "l ! n"; clarsimp)
  apply (cases "l ! n"; clarsimp)
  apply (cases "l ! n"; clarsimp)
  by (smt Collect_cong expand_op.simps insert_Collect)

lemma [intro]:
  "x \<in> fset P \<Longrightarrow> x |\<in>| P"
  by (meson notin_fset)

lemma fin [intro]:
  "x |\<in>| P \<Longrightarrow> x \<in> fset P"
  by (meson notin_fset)

lemma ord_exec:
  "ord (inst (expand_op \<alpha>)) (expand_point p l) = ord\<^sub>e (fst (snd \<alpha>)) p"
  apply (cases \<alpha>; case_tac b; auto split: var.splits)
  apply (subgoal_tac "fset (wrs p |\<inter>| fdeps\<^sub>B x2) = fset {||}")
  apply force
  apply simp
  apply (subgoal_tac "x \<in> fset (SimAsm_Inter_Exec.point.wrs p) \<inter> deps\<^sub>B x2")
  apply force
  apply (subgoal_tac "x \<in> fset (SimAsm_Inter_Exec.point.wrs p)")
  apply (subgoal_tac "x \<in> fset (fdeps\<^sub>B x2)")
  apply auto[1]
  apply blast+
  done

lemma proc1_exec:
  "l ! n = \<alpha> \<Longrightarrow> SimAsm_Inter.proc1 (expand_op \<alpha>) (expand_point p l) = expand_points (proc1 n (fst (snd \<alpha>)) p) l"
  apply (simp only: expand_points_def wken_exec proc1_def SimAsm_Inter.proc1_def ord_exec stren_exec)
  by simp

lemma gen_exec:
  "l ! n = \<alpha> \<Longrightarrow> SimAsm_Inter.gen (expand_op \<alpha>) = expand_point (gen n (fst (snd \<alpha>))) l"
  by (cases "l ! n"; clarsimp)

lemma rif\<^sub>i_exec:
  "l ! n = \<alpha> \<Longrightarrow> SimAsm_Inter.rif\<^sub>i (expand_op \<alpha>) (expand_points P l) = expand_points (rif\<^sub>i n (fst (snd \<alpha>)) P) l"
  apply (simp add: expand_points_def rif\<^sub>i_def SimAsm_Inter.rif\<^sub>i_def gen_exec proc1_exec del: expand_point.simps)
  by blast

lemma expand_points_union [simp]:
  "expand_points (P \<union> Q) l = expand_points P l \<union> expand_points Q l"
  by (auto simp: expand_points_def)

lemma expand_points_empty [simp]:
  "expand_points {} l = {}"
  by (auto simp: expand_points_def)

lemma mono_rif\<^sub>i:
  "mono (rif\<^sub>i n a)"
  apply (rule monoI)
  unfolding rif\<^sub>i_def by blast

lemma mono_rif:
  "mono (rif c l)"
proof (induct c)
  case (Basic x)
  then show ?case by (cases "tag x < length l"; simp add: monoI mono_rif\<^sub>i)
next
  case (Seq c1 c2)
  then show ?case by (simp add: mono_def)
next
  case (Choice c1 c2)
  then show ?case
    by (smt Un_mono mono_def rif.simps(2))
next
  case (Loop c)
  then show ?case 
    by (smt Un_iff lfp_mono monoI subset_eq rif.simps(3))
qed (simp add: monoI mono_rif\<^sub>i)+

lemma mono_union_rif':
  "mono (\<lambda>Y. P \<union> rif c l Y)"
  by (smt Un_mono monoD monoI mono_rif sup.idem sup.order_iff)

lemma rif_exec:
  "\<forall>\<beta> \<in> basics c. tag \<beta> < length l \<Longrightarrow>
   SimAsm_Inter.rif (expand c l) (expand_points P l) = expand_points (rif c (map (fst o snd) l) P) l"
proof (induct c arbitrary: P l)
  case (Basic \<alpha>)
  have e: "expand (Basic \<alpha>) l = Basic (expand_op (l ! tag \<alpha>))" by (cases \<alpha>; case_tac "l ! a"; auto)
  have d: "map (\<lambda>a. fst (snd a)) l ! tag \<alpha> = fst (snd (l ! tag \<alpha>))" using Basic by simp
  show ?case using Basic unfolding e by (simp add: d rif\<^sub>i_exec)
next
  case (Loop c)
  let ?f="\<lambda>Y. expand_points P l \<union> SimAsm_Inter.rif (expand c l) Y"
  let ?f'="\<lambda>Y. P \<union> rif c (map (\<lambda>a. fst (snd a)) l) Y"

  have r: "\<forall>P. SimAsm_Inter.rif (expand c l) (expand_points P l) = 
               expand_points (rif c (map (fst \<circ> snd) l) P) l"
    using Loop by fastforce

  have r': "\<And>P. expand_points (rif c (map (\<lambda>a. fst (snd a)) l) P) l = 
                SimAsm_Inter.rif (expand c l) (expand_points P l)"
    using Loop unfolding o_def by fastforce

  have "lfp ?f \<subseteq> expand_points (lfp ?f') l"
  proof (induct rule: lfp_ordinal_induct[where ?f="?f"])
    case mono
    then show ?case by (simp add: mono_union_rif) 
  next
    case (step S)
    hence "?f S \<subseteq> ?f (expand_points (lfp ?f') l)" 
      using SimAsm_Inter.mono_rif monoD by blast      
    also have "... \<subseteq> expand_points P l \<union> expand_points (rif c (map (\<lambda>a. fst (snd a)) l) (lfp ?f')) l"
      using step by (simp add: o_def r)
    also have "... \<subseteq> expand_points (P \<union> rif c (map (\<lambda>a. fst (snd a)) l) (lfp ?f')) l"
      by auto
    also have "... \<subseteq> expand_points (lfp ?f') l" 
      by (metis lfp_unfold[OF mono_union_rif'] subset_refl)
    finally show ?case  .
  next
    case (union M)
    then show ?case by (cases "M = {}"; auto)
  qed

  moreover have "expand_points (lfp ?f') l \<subseteq> lfp ?f"
  proof (induct rule: lfp_ordinal_induct[where ?f="?f'"])
    case mono
    then show ?case by (simp add: mono_union_rif')
  next
    case (step S)
    hence "?f (expand_points S l) \<subseteq>  ?f (lfp ?f)"
      using SimAsm_Inter.mono_rif monoD by blast
    also have "... \<subseteq> lfp ?f" using lfp_unfold[OF mono_union_rif] by blast
    finally show ?case unfolding r' expand_points_union .
  next
    case (union M)
    then show ?case by (cases "M = {}"; auto simp: expand_points_def)
  qed

  ultimately show ?case by (simp add: rif.simps(3))
qed simp_all

subsection \<open>Enumeration Properties\<close>

text \<open>Enumeration only extends the list\<close>
lemma enum_extends:
  "enum c l\<^sub>1 = (r,l\<^sub>2) \<Longrightarrow> \<exists>l. l\<^sub>2 = l\<^sub>1 @ l"
proof (induct c arbitrary: r l\<^sub>1 l\<^sub>2)
  case (Seq c\<^sub>1 c\<^sub>2)
  obtain r\<^sub>1 r\<^sub>2 l'' where r: "enum c\<^sub>2 l\<^sub>1 = (r\<^sub>2,l'')" "enum c\<^sub>1 l'' = (r\<^sub>1,l\<^sub>2)" "r = r\<^sub>1 ;; r\<^sub>2"
    using Seq(3) by (cases "(lang.Seq c\<^sub>1 c\<^sub>2,l\<^sub>1)" rule: enum.cases) (auto split: prod.splits)
  show ?case using Seq(1)[OF r(2)] Seq(2)[OF r(1)] Seq(3)  append.assoc by blast
next
  case (If b c\<^sub>1 c\<^sub>2)
  obtain r\<^sub>1 r\<^sub>2 l\<^sub>3 l\<^sub>4 where r: 
      "enum c\<^sub>2 l\<^sub>1 = (r\<^sub>2,l\<^sub>3)" 
      "enum c\<^sub>1 l\<^sub>3 = (r\<^sub>1,l\<^sub>4)" 
      "l\<^sub>2 = l\<^sub>4@[(UNIV,cmp b,state_rec.more),(UNIV,cmp (Neg b),state_rec.more)]"
    using If(3) by (cases "(lang.If b c\<^sub>1 c\<^sub>2,l\<^sub>1)" rule: enum.cases) (auto split: prod.splits)
  show ?case using If(1)[OF r(2)] If(2)[OF r(1)] If(3) r(3) by force
next
  case (While b x2 c)
  obtain r\<^sub>1 l\<^sub>3 where r: 
      "enum c l\<^sub>1 = (r\<^sub>1,l\<^sub>3)" 
      "l\<^sub>2 = l\<^sub>3@[(UNIV,cmp b,state_rec.more),(UNIV,cmp (Neg b),state_rec.more)]"
    using While(2) by (cases "(lang.While b x2 c,l\<^sub>1)" rule: enum.cases) (auto split: prod.splits)
  show ?case using While(1)[OF r(1)] r(2) by auto
next
  case (DoWhile x1 c b)
  obtain r\<^sub>1 l\<^sub>3 where r: 
      "enum c l\<^sub>1 = (r\<^sub>1,l\<^sub>3)" 
      "l\<^sub>2 = l\<^sub>3@[(UNIV,cmp b,state_rec.more),(UNIV,cmp (Neg b),state_rec.more)]"
    using DoWhile(2) by (cases "(lang.DoWhile x1 c b,l\<^sub>1)" rule: enum.cases) (auto split: prod.splits)
  then show ?case using DoWhile(1)[OF r(1)] by auto
qed auto

text \<open>Bounds on the instruction ids in the enumeration function\<close>
lemma enum_basics_upper:
  "enum c l' = (r,l) \<Longrightarrow> \<beta> \<in> basics r \<Longrightarrow> tag \<beta> < length l"
  by (induct c arbitrary: r l l') (insert enum_extends, auto split: prod.splits; fastforce)+

lemma expand_cong:
  "\<forall>\<beta> \<in> basics c. l ! tag \<beta> = l' ! tag \<beta> \<Longrightarrow> expand c l = expand c l'"
  by (induct c arbitrary: l l'; auto)

lemma enum_expand_cong:
  "enum c\<^sub>2 l\<^sub>1 = (r\<^sub>2, l\<^sub>2) \<Longrightarrow> enum c\<^sub>1 l\<^sub>2 = (r\<^sub>1, l\<^sub>3) \<Longrightarrow> expand r\<^sub>2 l\<^sub>2 = expand r\<^sub>2 l\<^sub>3"
  by (metis (no_types, lifting) enum_basics_upper enum_extends expand_cong nth_append) 

lemma concat_expand_cong:
  "enum c\<^sub>1 l\<^sub>1 = (r\<^sub>1, l\<^sub>2) \<Longrightarrow> expand r\<^sub>1 l\<^sub>2 = expand r\<^sub>1 (l\<^sub>2 @ l)"
  by (metis (no_types, lifting) enum_basics_upper expand_cong nth_append) 

lemma liftl_lifg [intro!]:
  "(liftl b) = (\<lfloor>UNIV,b,state_rec.more\<rfloor>)"
  by (auto simp: liftg_def liftl_def)

lemma enum_exec:
  "enum c l' = (r,l) \<Longrightarrow> lift\<^sub>c c = expand r l"
proof (induct c arbitrary: r l l')
  case (Seq c1 c2)
  thus ?case by (auto intro: enum_expand_cong split: prod.splits)
next
  case (If x1 c1 c2)
  then show ?case
    apply (auto split: prod.splits)
    apply (rule concat_expand_cong; auto)
    apply (rule expand_cong)
    by (metis (no_types, lifting) append_assoc enum_basics_upper enum_extends nth_append)
next
  case (While x1 x2 c)
  then show ?case by (auto intro: concat_expand_cong split: prod.splits)
next
  case (DoWhile x1 c x3)
  then show ?case by (auto intro: concat_expand_cong split: prod.splits)
qed auto

subsection \<open>Link Abstract & Executable\<close>

text \<open>Expand the abstract rif definition to an executable form\<close>
lemma rif_executable:
  "SimAsm_Inter.rif (lift\<^sub>c c) {} = (let (r,l) = enum c [] in expand_points (rif r (map (fst o snd) l) {}) l)"
proof (unfold Let_def, case_tac "enum c []", clarsimp)
  fix r l assume a: "enum c [] = (r,l)"
  have "\<forall>\<beta>\<in>basics r. tag \<beta> < length l" using enum_basics_upper[OF a] by auto
  hence "SimAsm_Inter.rif (expand r l) {} = expand_points (rif r (map (fst o snd) l) {}) l"
    using rif_exec[where ?P="{}"] by auto
  thus "SimAsm_Inter.rif (lift\<^sub>c c) {} = expand_points (rif r (map (fst \<circ> snd) l) {}) l"
    using enum_exec a by force
qed

end