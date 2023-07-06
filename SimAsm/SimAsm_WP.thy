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
fun wp\<^sub>i :: "('r,'v) op \<Rightarrow> ('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) varmap' set" 
  where 
    "wp\<^sub>i (assign r e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)(r := ev\<^sub>E (varmap_st s) e)\<rparr>) \<in> Q}" |
    "wp\<^sub>i (cmp b) Q =  {s. (ev\<^sub>B (varmap_st s) b) \<longrightarrow> s \<in> Q}" | 
    "wp\<^sub>i (leak c e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)(c := ev\<^sub>E (varmap_st s) e)\<rparr>) \<in> Q}" |
    "wp\<^sub>i _ Q = Q"



text \<open>Transform a predicate based on an auxiliary state update\<close>
 fun wp\<^sub>a :: "(('r,'v,'a) varmap','a) auxfn \<Rightarrow> ('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) varmap' set"
   where "wp\<^sub>a a Q = {t. t\<lparr>more := a t\<rparr> \<in> Q}" 

text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "('r,'v,'a) varmap' trans \<Rightarrow> ('r,'v,'a) varmap' rtrans"
  where "wp\<^sub>r f G \<equiv> {(s,s'). s' \<in> f {s'. (s,s') \<in> G}}"


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


context wp_spec
begin

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


text \<open> Other direction: Producing an unlabelled predicate from a labelled predicate \<close>

text \<open>Lifts the given unlabelled state to its Ul labelled counterpart.\<close>
fun ul_lift :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) lvarmap'" where 
  "ul_lift s = \<lparr> varmap_st = \<lambda>v. varmap_st s (unlabel v), \<dots> = more s \<rparr>"

text \<open>Lifts the given unlabelled state to its Gl labelled counterpart.\<close>
fun gl_lift :: "('r,'v,'a) varmap' \<Rightarrow> ('r,'v,'a) lvarmap'" where 
  "gl_lift s = \<lparr> varmap_st = \<lambda>v. varmap_st s (unlabel v), \<dots> = more s \<rparr>"
(* Kait: these do not really work..? *)

text \<open>Restricts a labelled predicate into an unlabelled predicate, 
            constraining both, global and unlabelled predicates.\<close>
definition restrict_pred :: "('r,'v,'a) lvarmap' pred \<Rightarrow> ('r,'v,'a) varmap' pred"   ("(_\<^sup>U)" [1000] 1000) where
  "restrict_pred Q = {s. gl_lift s \<in> Q}"


text \<open> Transform a predicate over a speculation, which introduces labels to predicates \<close>
fun wp\<^sub>i\<^sub>s :: "('r,'v) op \<Rightarrow> ('r,'v,'a) lvarmap' set \<Rightarrow> ('r,'v,'a) lvarmap' set"          (* wp_spec on ops *)
  where 
    "wp\<^sub>i\<^sub>s (assign r e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)((Ul r) := (ev\<^sub>E (varmap_st s) (ul\<^sub>E e)))\<rparr>) \<in> Q}" |
    "wp\<^sub>i\<^sub>s (cmp b) Q =  {s. (ev\<^sub>B (varmap_st s) (ul\<^sub>B b)) \<longrightarrow> s \<in> Q}" | 
    "wp\<^sub>i\<^sub>s (leak c e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)((Gl c) := ev\<^sub>E (varmap_st s) (ul\<^sub>E e))\<rparr>) \<in> Q}" |
    "wp\<^sub>i\<^sub>s full_fence Q = UNIV"  |
    "wp\<^sub>i\<^sub>s nop Q = Q"  


text \<open>wp_spec transformer on lang.\<close>
fun wp\<^sub>s :: "('r,'v,('r,'v,'a) varmap','a) lang \<Rightarrow> ('r,'v,'a) lvarmap' pred \<Rightarrow> ('r,'v,'a) lvarmap' pred"   
  where 
    "wp\<^sub>s Skip Q = Q" |
    "wp\<^sub>s (Op v a f) Q = (v\<^sup>L \<inter> (wp\<^sub>i\<^sub>s a (wp\<^sub>a f Q\<^sup>U)\<^sup>L))" |
    "wp\<^sub>s (Seq c\<^sub>1 c\<^sub>2) Q = wp\<^sub>s c\<^sub>1 (wp\<^sub>s c\<^sub>2 Q)" |
    "wp\<^sub>s (If b c\<^sub>1 c\<^sub>2) Q = (wp\<^sub>s c\<^sub>1 Q) \<inter> (wp\<^sub>s c\<^sub>2 Q)" |
    "wp\<^sub>s (While b Imix Ispec c) Q = undefined" | 
    "wp\<^sub>s (DoWhile Imix Ispec c b) Q = undefined"


text \<open>Merge function to merge sequential and speculative predicates into a single weakest precondition. \<close>
fun merge :: "'g rel \<Rightarrow> ('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) varmap' set"
  where "merge R Q\<^sub>1 Q\<^sub>2 = Q\<^sub>1 \<inter> (stabilize R  Q\<^sub>1)  \<inter> Q\<^sub>2"


text \<open>  \<close>
(* wp over speculation needs to relate (wp r Q) and (wp_s  r Q) without knowing r

  todo: something like (spec Q) = Q \<inter> \<And>x \<in> wr(r). (\<L>(x) \<inter> \<And>y \<in> ctrl(x). \<L>(y))
                                       "minus" stability conditions 
   or maybe just add in the context of the non-speculated behaviour: (spec b Q) = Q \<inter> {s. (st_ev\<^sub>B s b)}
   or maybe, wp c Q \<subseteq> (spec c Q)  where c is the speculated command, which in case c=r
   means we can set (spec r Q) = Q  
*)

text \<open> lifts the predicate to a "labelled" predicate, in which all variable are marked as UL \<close>
fun spec :: "('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) lvarmap' set"
  where "(spec Q) = (Q)\<^sup>L"


text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "'g rel \<Rightarrow> ('r,'v,('r,'v,'a) varmap','a) lang \<Rightarrow> ('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) varmap' set"
  where
    "wp R Skip Q = Q" |
    "wp R (Op v a f) Q = stabilize R (v \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wp R (SimAsm.lang.Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = 
           (merge R  (stabilize R (wp\<^sub>s c\<^sub>2  (spec Q))\<^sup>U) (stabilize R (wp\<^sub>i (cmp b) (wp R c\<^sub>1 Q))))
         \<inter> (merge R  (stabilize R (wp\<^sub>s c\<^sub>1  (spec Q))\<^sup>U) (stabilize R (wp\<^sub>i (ncmp b) (wp R c\<^sub>2 Q))))" |
(* here (wp\<^sub>s r true) is simplified to Q *)
    "wp R (While b Imix Ispec c) Q =
      (stabilize R Imix \<inter>  
        assert (Imix \<subseteq> (merge R Q (wp\<^sub>i (cmp b) (wp R c (stabilize R Imix)))) \<inter>
                        (merge R  (stabilize R (wp\<^sub>s c (spec Ispec))\<^sup>U) (wp\<^sub>i (ncmp b) Q))))" |
    "wp R (DoWhile Imix Ispec c b) Q =
      (stabilize R Imix \<inter>  
        assert (Imix \<subseteq> (merge R (stabilize R ((wp\<^sub>s c (Q\<^sup>L \<inter> (stabilize R Ispec)\<^sup>L))\<^sup>U))  
                                  (wp R c ((stabilize R (wp\<^sub>i (cmp b) (stabilize R Imix))) \<inter>
                                           (stabilize R (wp\<^sub>i (ncmp b) Q)))))))" 

end (* end of locale wp_spec *)


end
