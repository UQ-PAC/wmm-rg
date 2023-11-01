theory SimAsm_WP
  imports SimAsm HOL.Lattices "../State"
begin

text \<open>Labels on global variables only \<close>
datatype 'g label = Ul 'g | Gl 'g      

fun unlabel where 
  "unlabel (Ul x) = x" | "unlabel (Gl x) = x"

text \<open>
Further, note that the ('r,'v,'a) varmap' type is a varmap with added auxiliary state.
This takes the place of the "state" type in previous theories.

'r is the variable name type (r for register), 'v is the value type, and 'a is auxiliary.
\<close>

(* varmap_rec is a record with only one mapping in it, varmap_st, i.e., varmap_st replaces
    the old st mapping that provides the mapping from var to val  *)

record ('r,'v) varmap_rec = varmap_st :: "'r \<Rightarrow> 'v"
type_synonym ('r,'v,'a) varmap' = "('r,'v,'a) varmap_rec_scheme" 
type_synonym ('r,'v,'a) auxop' = "('r,'v,('r,'v,'a) varmap','a) auxop"

text \<open>Labelled state (record) in which every variable appears in its Gl and UL variation \<close>
type_synonym ('r,'v,'a) lvarmap' = "('r label,'v,'a) varmap'"
type_synonym ('r,'v,'a) lauxop = "('r,'v,('r,'v,'a) lvarmap','a) auxop"

type_synonym ('r,'v,'a) spec_state = "('r,'v,'a) lvarmap' set \<times> ('r,'v,'a) varmap' set"

(*-----------------------------------------------------------------------------------*)

text \<open> General WP reasoning
       the added rg and glb are projections onto the local and global states.\<close>

locale wp =
  fixes rg :: "('r,'v,'a) varmap' \<Rightarrow> 'l"
  fixes glb :: "('r,'v,'a) varmap' \<Rightarrow> 'g"



type_synonym 'a pred = "'a set" 
type_synonym 'a trans = "'a pred \<Rightarrow> 'a pred"
type_synonym 'a rtrans = "'a rel \<Rightarrow> 'a rel"

context wp
begin

text \<open> Reasoning is performed on "simple" predicates, not on stateTrees, which are 
        later (in the soundness proof) matched to the stateTrees on which the semantics operates \<close>

section \<open>Wellformedness\<close>

text \<open>stabilize R P is effectively the weakest (i.e. largest) precondition
that is guaranteed to arrive at P after R steps. 
This is something like the weakest precondition of the environment steps.\<close>
definition stabilize
  where "stabilize R P \<equiv> {m. \<forall>m'. (glb m,glb m') \<in> R \<longrightarrow> rg m = rg m' \<longrightarrow> m' \<in> P}"

definition reflexive
  where "reflexive R \<equiv> (\<forall>m. (m,m) \<in> R)"

definition transitive
  where "transitive R \<equiv> (\<forall>m m' m''. (m,m') \<in> R \<longrightarrow> (m',m'') \<in> R \<longrightarrow> (m,m'') \<in> R)"

definition assert
  where "assert b \<equiv> {m. b}"


text \<open>Lift a relational predicate\<close>
definition step\<^sub>t :: "'g rel \<Rightarrow> ('r,'v,'a) varmap' rel"
  where "step\<^sub>t R \<equiv> {(m,m'). (glb m, glb m') \<in> R \<and> rg m = rg m'}"


text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step :: "'g rel \<Rightarrow> ('r,'v,'a) varmap' rel"
  where "step R \<equiv> {(t,t'). (glb t, glb t') \<in> R}"


text \<open>Define stability in terms of a relational predicate that preserves the thread state\<close>
abbreviation stable\<^sub>t
  where "stable\<^sub>t R P \<equiv> stable (step\<^sub>t R) P"

text \<open>Couple all wellformedness conditions into a single definition\<close>
abbreviation wellformed :: "'g rel \<Rightarrow> 'g rel \<Rightarrow> bool"
  where "wellformed R G \<equiv> reflexive R \<and> transitive R \<and> reflexive G" 

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G"
  shows "stable\<^sub>t R (stabilize R Q)"
  unfolding stable_def step\<^sub>t_def
proof (clarsimp)
  fix m m'
  assume a: "m \<in> stabilize R Q" "(glb m, glb m') \<in> R" "rg m = rg m'"
  have "\<forall>g''. (glb m',g'') \<in> R \<longrightarrow> (glb m,g'') \<in> R"
    using assms a(2) unfolding transitive_def
    using trans_def by fast
  thus "m' \<in> stabilize R Q" using a(1,3) by (auto simp: stabilize_def)
qed

text \<open>The conjunction of two stable predicates is stable\<close>
lemma stable\<^sub>t_conj [intro]:
  assumes "stable\<^sub>t R P" "stable\<^sub>t R Q"
  shows "stable\<^sub>t R (P \<inter> Q)"
  using assms by (auto simp: stable_def)

text \<open>Elimination rule to ignore the stabilization process\<close>
lemma stabilizeE:
  assumes "m \<in> stabilize R P"
  assumes "reflexive R"
  obtains "m \<in> P"
proof - 
  have "\<forall>g. (glb m, glb g) \<in> R \<longrightarrow> rg m = rg g \<longrightarrow> g \<in> P" 
       "(glb m, glb m) \<in>  R"
    using assms by (simp_all add: stabilize_def reflexive_def)
  thus ?thesis using that by auto
qed

text \<open>Stabilization preserves entailment\<close>
lemma stabilize_entail :
  assumes "t \<in> stabilize R P" 
  assumes "reflexive R"
  assumes "P \<subseteq> Q"
  shows "t \<in> stabilize R Q"
  using assms by (auto simp: stabilize_def)



section \<open>Predicate Transformations\<close>

(* define (spec c) = \<triangle>(Capture s c)? No, only in the semantics (i.e., the abstract logic) *)

text \<open> Transform a predicate based on an sub-operation, simple wp \<close>
(* this is the normal wp transformer on ops *)
fun wp\<^sub>i :: "('r','v') op \<Rightarrow> ('r','v','a') varmap' set \<Rightarrow> ('r','v','a') varmap' set" 
  where 
    "wp\<^sub>i (assign r e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)(r := ev\<^sub>E (varmap_st s) e)\<rparr>) \<in> Q}" |
    "wp\<^sub>i (cmp b) Q =  {s. (ev\<^sub>B (varmap_st s) b) \<longrightarrow> s \<in> Q}" | 
    "wp\<^sub>i (leak c e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)(c := ev\<^sub>E (varmap_st s) e)\<rparr>) \<in> Q}" |
    "wp\<^sub>i _ Q = Q"



text \<open>Transform a predicate based on an auxiliary state update\<close>
fun wp\<^sub>a :: "(('r','v','a') varmap','a') auxfn \<Rightarrow> ('r','v','a') varmap' set \<Rightarrow> ('r','v','a') varmap' set"
  where "wp\<^sub>a a Q = {t. t\<lparr>more := a t\<rparr> \<in> Q}" 

declare wp\<^sub>a.simps[simp del]

text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "('r,'v,'a) varmap' trans \<Rightarrow> ('r,'v,'a) varmap' rtrans"
  where "wp\<^sub>r f G \<equiv> {(s,s'). s' \<in> f {t'. (s,t') \<in> G}}"


subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar
  where "guar f G \<equiv> {t. (t,t) \<in> (wp\<^sub>r f G)}"

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c Skip G = True" |
    "guar\<^sub>c (Op v a f) G = (v \<subseteq> guar (wp\<^sub>i a o wp\<^sub>a f) (step G))" |
    "guar\<^sub>c (SimAsm.lang.Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If _ c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While _ _ _ c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c (DoWhile _ _ c _) G = (guar\<^sub>c c G)"

end  (* of locale wp *)

(*---------------------------------------------------------------------------------------*)
text \<open> Locale for reasoning without speculation in mind  \<close>

locale wp_WOspec = wp rg glb
(*  for project :: "('r \<Rightarrow> 'v) \<Rightarrow> ('r,'v,'a) varmap'" *)
  for rg :: "('r,'v,'a) varmap' \<Rightarrow> 'l"
  and glb :: "('r,'v,'a) varmap' \<Rightarrow> 'g"


context wp_WOspec
begin


(* create an annotation type for loops that can be just one pred for wp_WOspec, or two pred for wp_spec *)

text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "'g rel \<Rightarrow> ('r,'v,('r,'v,'a) varmap','a) lang \<Rightarrow> ('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) varmap' set"
  where
    "wp R Skip Q = Q" |
    "wp R (Op v a f) Q = stabilize R (v \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = stabilize R (wp\<^sub>i (cmp b) (wp R c\<^sub>1 Q) \<inter> wp\<^sub>i (ncmp b) (wp R c\<^sub>2 Q))" |
     "wp R (While b I _ c) Q = (stabilize R I \<inter> 
       assert (I \<subseteq> wp\<^sub>i (cmp b) (wp R c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" |
    "wp R (DoWhile I _ c b) Q = (stabilize R I \<inter> 
       assert (I \<subseteq>  wp R c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"

end (* end of locale wp_WOspec *)

(*---------------------------------------------------------------------------------------*)
text \<open> Locale for reasoning with speculation in mind  \<close>

locale wp_spec = wp rg glb
  for rg :: "('r,'v,'a) varmap' \<Rightarrow> 'l"
  and glb :: "('r,'v,'a) varmap' \<Rightarrow> 'g"


fun map\<^sub>E :: "('r \<Rightarrow> 'r2) \<Rightarrow> ('v \<Rightarrow> 'v2) \<Rightarrow> ('v2 \<Rightarrow> 'v) \<Rightarrow> ('r,'v) exp \<Rightarrow> ('r2,'v2) exp" where
  "map\<^sub>E f g h (Var v) = Var (f v)" |
  "map\<^sub>E f g h (Exp eval es) = Exp (\<lambda>vs. g (eval (map h vs))) (map (map\<^sub>E f g h) es)" |
  "map\<^sub>E f g h (Val v) = Val (g v)"


fun ul\<^sub>E :: "('r,'v) exp \<Rightarrow> ('r label,'v) exp" ("(2_)\<^sup>u" [901] 900) where
  "ul\<^sub>E e = map\<^sub>E Ul id id e"

fun gl\<^sub>E :: "('r,'v) exp \<Rightarrow> ('r label,'v) exp" ("(2_)\<^sup>g" [901] 900) where
  "gl\<^sub>E e = map\<^sub>E Gl id id e"

fun map\<^sub>B :: "('r \<Rightarrow> 'r2) \<Rightarrow> ('v \<Rightarrow> 'v2) \<Rightarrow> ('v2 \<Rightarrow> 'v) \<Rightarrow> ('r,'v) bexp \<Rightarrow> ('r2,'v2) bexp" where
  "map\<^sub>B f g h (Neg b) =  Neg (map\<^sub>B f g h b) " |
  "map\<^sub>B f g h (Exp\<^sub>B eval es) = Exp\<^sub>B (\<lambda>vs. (eval (map h vs))) (map (map\<^sub>E f g h) es)" 

fun ul\<^sub>B :: "('r,'v) bexp \<Rightarrow> ('r label,'v) bexp" ("(2_)\<^sup>u" [901] 900) where
  "ul\<^sub>B b = map\<^sub>B Ul id id b"

fun gl\<^sub>B :: "('r,'v) bexp \<Rightarrow> ('r label,'v) bexp" ("(2_)\<^sup>g" [901] 900) where
  "gl\<^sub>B b = map\<^sub>B Gl id id b"

fun ul\<^sub>s :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) lvarmap'" where
  "ul\<^sub>s e = undefined"

(* alternative, simpler definition of map\<^sub>E which omits second and third paramerter which are currently not used: 
fun map\<^sub>E' :: "('r \<Rightarrow> 'r2) \<Rightarrow> ('r,'v) exp \<Rightarrow> ('r2,'v) exp" where
  "map\<^sub>E' f (Var v) = Var (f v)" |
  "map\<^sub>E' f (Exp eval es) = Exp (\<lambda>vs. (eval (vs))) (map (map\<^sub>E' f) es)" |
  "map\<^sub>E' f (Val v) = Val (v)"
*)

text \<open> Producing a labelled predicate from an unlabelled predicate \<close>

text \<open>Restricts the given predicate to its unlabelled part.\<close>
fun ul_restrict :: "('r,'v,'a) lvarmap' \<Rightarrow> ('r,'v,'a) varmap'" where 
  "ul_restrict s = \<lparr> varmap_st = (\<lambda>v. varmap_st s (Ul v)), \<dots> = more s \<rparr>"

text \<open>Restricts the given predicate to its globally labelled part.\<close>
fun gl_restrict :: "('r,'v,'a) lvarmap' \<Rightarrow> ('r,'v,'a) varmap'" where 
  "gl_restrict s = \<lparr> varmap_st = (\<lambda>v. varmap_st s (Gl v)), \<dots> = more s \<rparr>"

text \<open>Lifts a predicate into a labelled predicate, treating the state as Global 
                                            and without constraining Unlabelled.\<close>
definition gl_lift_pred :: "('r,'v,'a) varmap' pred \<Rightarrow> ('r,'v,'a) lvarmap' pred" ("(2_)\<^sup>G" [901] 900) where
  "gl_lift_pred Q = {s. gl_restrict s \<in> Q }"

text \<open>Lifts a predicate into a labelled predicate, treating the state as Unlabelled 
                                                    and without constraining Global.\<close>
definition ul_lift_pred :: "('r,'v,'a) varmap' pred \<Rightarrow> ('r,'v,'a) lvarmap' pred" ("(_\<^sup>L)" [1000] 1000) where
  "ul_lift_pred Q = {s. ul_restrict s \<in> Q }"

text \<open>Lifts a predicate into a labelled predicate, requiring the local and
      global states to both be equal to s.\<close>
definition glul_lift_pred :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) lvarmap'" ("(_\<^sup>G\<^sup>L)" [1000] 1000) where
  "glul_lift_pred s = \<lparr> varmap_st = (\<lambda>v. varmap_st s (unlabel v)), \<dots> = more s \<rparr> " 


text \<open> Unlabelling a predicate, such that variables with differing labels need to be equal 
         as they become indistinguishable without their label \<close>

definition restrict_pred :: "('r,'v,'a) lvarmap' pred \<Rightarrow> ('r,'v,'a) varmap' pred"   ("(_\<^sup>U)" [1000] 1000) where
  "restrict_pred Q = gl_restrict ` {s. (\<forall>v. varmap_st s(Gl v) = varmap_st s (Ul v)) \<and> s \<in> Q}"

context wp_spec
begin

text \<open> stablilizing the verification conditions in the speculated part:
              - global variables (labelled with G, i.e., sit in the base frame) related by R
              - local variables (labelled with G) need to be equal 
              - all other parts of the labelled state (all unlabelled parts, i.e., frame vars)
                  are unchanged \<close>
definition stabilize\<^sub>L
  where "stabilize\<^sub>L R P \<equiv> {m. \<forall>m'. 
        (glb (gl_restrict m),glb (gl_restrict m')) \<in> R \<longrightarrow> rg (gl_restrict m) = rg (gl_restrict m') 
                                                       \<and> ul_restrict m = ul_restrict m' \<longrightarrow> m' \<in> P}"

text \<open> Transform a predicate over a speculation, which introduces labels to predicates \<close>
fun wp\<^sub>i\<^sub>s :: "('r,'v) op \<Rightarrow> ('r,'v,'a) lvarmap' set \<Rightarrow> ('r,'v,'a) lvarmap' set"          (* wp_spec on ops *)
  where 
    "wp\<^sub>i\<^sub>s (assign r e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)((Ul r) := (ev\<^sub>E (varmap_st s) (ul\<^sub>E e)))\<rparr>) \<in> Q}" |
    "wp\<^sub>i\<^sub>s (cmp b) Q =  {s. (ev\<^sub>B (varmap_st s) (ul\<^sub>B b)) \<longrightarrow> s \<in> Q}" | 
    "wp\<^sub>i\<^sub>s (leak c e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)((Gl c) := ev\<^sub>E (varmap_st s) (ul\<^sub>E e))\<rparr>) \<in> Q}" |
    "wp\<^sub>i\<^sub>s full_fence Q = UNIV"  |
    "wp\<^sub>i\<^sub>s nop Q = Q"  


text \<open>Merge function integrates the Qs speculative predicate into the sequential predicate. 
      This considers the case that speculation may have started at this merge point. \<close>
fun merge :: "'g rel \<Rightarrow> ('r,'v,'a) spec_state \<Rightarrow> ('r,'v,'a) spec_state"
  where "merge R (Qs,Q) = (Qs, (stabilize R Qs\<^sup>U)  \<inter> Q)"



text \<open>  \<close>

text \<open> lifts the predicate to a "labelled" predicate, in which all variables are marked as UL \<close>
fun spec :: "('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) lvarmap' set"
  where "(spec Q) = (Q)\<^sup>L"

fun spec_op :: "('r,'v) op \<Rightarrow> ('r label,'v) op" where
  "spec_op x = undefined"

fun spec_bexp :: "('r,'v) bexp \<Rightarrow> ('r label,'v) bexp" where
  "spec_bexp x = undefined"

fun spec_part :: "('r,'v,'a) spec_state \<Rightarrow> ('r,'v,'a) lvarmap' pred" ("[(_)]\<^sub>s") where
  "spec_part (Qs,_) = Qs"

fun seq_part :: "('r,'v,'a) spec_state \<Rightarrow> ('r,'v,'a) varmap' pred" ("[(_)]\<^sub>;") where
  "seq_part (Qs,Q) = Q"

abbreviation spec_inter :: "('r,'v,'a) spec_state \<Rightarrow> 
                             ('r,'v,'a) spec_state  \<Rightarrow> ('r,'v,'a) spec_state" (infixr "\<inter>\<^sub>s" 80) 
  where "spec_inter c\<^sub>1 c\<^sub>2 \<equiv> (([c\<^sub>1]\<^sub>s \<inter> [c\<^sub>2]\<^sub>s) , ([c\<^sub>1]\<^sub>; \<inter> [c\<^sub>2]\<^sub>;))"

abbreviation spec_subset :: "('r,'v,'a) spec_state \<Rightarrow> 
                             ('r,'v,'a) spec_state \<Rightarrow> bool" (infixr "\<subseteq>\<^sub>s" 80) 
  where "spec_subset c\<^sub>1 c\<^sub>2 \<equiv> ([c\<^sub>1]\<^sub>s \<subseteq> [c\<^sub>2]\<^sub>s) \<and> ([c\<^sub>1]\<^sub>; \<subseteq> [c\<^sub>2]\<^sub>;)"


text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "'g rel \<Rightarrow> ('r,'v,('r,'v,'a) varmap','a) lang \<Rightarrow> ('r,'v,'a) spec_state \<Rightarrow> ('r,'v,'a) spec_state"
  where
    "wp R Skip Q = Q" |
    "wp R (Op v a f) (Qs, Q) = (stabilize\<^sub>L R (v\<^sup>L \<inter> wp\<^sub>i\<^sub>s a (wp\<^sub>a (f \<circ> gl_restrict) Qs)), 
                                stabilize R (v \<inter> wp\<^sub>i a (wp\<^sub>a f Q)))" |
    "wp R (SimAsm.lang.Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
(* note: speculative component is not conditional on b because speculation may have started earlier. *)
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = merge R 
       ([wp R c\<^sub>2 Q]\<^sub>s \<inter> [wp R c\<^sub>1 Q]\<^sub>s, 
        stabilize R (wp\<^sub>i (cmp b) [wp R c\<^sub>1 Q]\<^sub>; \<inter> wp\<^sub>i (ncmp b) [wp R c\<^sub>2 Q]\<^sub>;))" |
    "wp R (While b Inv\<^sub>s Inv c) Q = merge R (Inv\<^sub>s\<^sup>L, Inv) \<inter>\<^sub>s
       (assert (Inv\<^sub>s\<^sup>L \<subseteq> [Q]\<^sub>s) \<inter>  assert (Inv\<^sub>s\<^sup>L \<subseteq> [(wp R c (Inv\<^sub>s\<^sup>L, Inv))]\<^sub>s), 
        assert (Inv \<subseteq> (wp\<^sub>i (ncmp b) [Q]\<^sub>;)) \<inter> assert (Inv \<subseteq> (wp\<^sub>i (cmp b) [(wp R c (Inv\<^sub>s\<^sup>L, (stabilize R Inv)))]\<^sub>;)))" |
      "wp R (DoWhile Inv\<^sub>s Inv c b) Q = wp R c (merge R (Inv\<^sub>s\<^sup>L, Inv) \<inter>\<^sub>s
       (assert (Inv\<^sub>s\<^sup>L \<subseteq> [Q]\<^sub>s) \<inter>  assert (Inv\<^sub>s\<^sup>L \<subseteq> [(wp R c (Inv\<^sub>s\<^sup>L, Inv))]\<^sub>s), 
        assert (Inv \<subseteq> (wp\<^sub>i (ncmp b) [Q]\<^sub>;)) \<inter> assert (Inv \<subseteq> (wp\<^sub>i (cmp b) [(wp R c (Inv\<^sub>s\<^sup>L, (stabilize R Inv)))]\<^sub>;))))"
(* with DoWhile Inv\<^sub>s Inv c b \<equiv> c ; While b Inv\<^sub>s Inv c) *)

text \<open>transformer over a spec_state. given two mapping functions, applies them to both
      components of the spec_state, element-wise.\<close>
fun biwp :: "(('r_,'v_,'a_) varmap' pred \<Rightarrow> ('r_,'v_,'a_) varmap' pred)
              \<Rightarrow> (('r_,'v_,'a_) lvarmap' pred \<Rightarrow> ('r_,'v_,'a_) lvarmap' pred)
              \<Rightarrow> ('r_,'v_,'a_) spec_state \<Rightarrow> ('r_,'v_,'a_) spec_state"
  where
    "biwp f fs = (\<lambda>(Qs,Q). (fs Qs, f Q))"

lemma "(THE s'. gl_restrict s' = s \<and> ul_restrict s' = s) = s\<^sup>G\<^sup>L"
unfolding glul_lift_pred_def gl_lift_pred_def ul_lift_pred_def
proof (standard, standard, goal_cases)
  case (3 s')
  thus ?case
  by (induct s', clarsimp) (metis unlabel.elims)
qed auto

lemma gl_restrict_of_glul [simp]: "gl_restrict (s\<^sup>G\<^sup>L) = s" 
unfolding glul_lift_pred_def
by simp

lemma ul_restrict_of_glul [simp]: "ul_restrict (s\<^sup>G\<^sup>L) = s" 
unfolding glul_lift_pred_def
by simp

lemma varmap_st_of_glul: "varmap_st (s\<^sup>G\<^sup>L) (Gl v) = varmap_st (s\<^sup>G\<^sup>L) (Ul v)"
unfolding glul_lift_pred_def
by simp

lemma [simp]: "(Q\<^sup>G)\<^sup>U = Q" 
unfolding gl_lift_pred_def restrict_pred_def 
proof (standard, goal_cases)
  case 2
  then show ?case
  proof (standard, goal_cases)
    case (1 s0)
    then show ?case 
      using gl_restrict_of_glul varmap_st_of_glul 
      by (intro image_eqI[where ?x="s0\<^sup>G\<^sup>L"]) auto 
  qed
qed auto

lemma [simp]: "(Q\<^sup>L)\<^sup>U = Q" 
unfolding ul_lift_pred_def restrict_pred_def 
proof (standard, goal_cases)
  case 2
  then show ?case
  proof (standard, goal_cases)
    case (1 s0)
    then show ?case 
      using gl_restrict_of_glul varmap_st_of_glul
      by (intro image_eqI[where ?x="s0\<^sup>G\<^sup>L"]) auto
  qed
qed auto

end (* end of locale wp_spec *)


end
