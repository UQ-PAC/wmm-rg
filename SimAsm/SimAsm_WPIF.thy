theory SimAsm_WPIF
  imports SimAsm Var_map HOL.Lattices
begin

text \<open> The type secvarmap introduces the current security level for each variable,
        i.e., for each variable var \<mapsto> (val, secLevel) 
       'sec here is abstract but will be used as a general bounded_lattice or complete_lattice 
          with the corresponding operators \<sqinter> and \<squnion> in the definitions where required,
          we assume the order Low \<le> High  \<close>

type_synonym ('r,'v,'sec,'a) secvarmap = "('r,'v\<times>'sec,'a) varmap'"
type_synonym ('r,'v,'sec,'a) secauxop = "('r,'v,('r,'v,'sec,'a) secvarmap,'a) auxop"
type_synonym ('r,'v,'sec,'a) secopbasic = "('r,'v,('r,'v,'sec,'a) secvarmap,'a) opbasic" 

text \<open> secClass provides a type for security classifications for each variable v, \<L>(v) \<close>

type_synonym ('r,'v,'sec,'a) secClass = "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'r \<Rightarrow> 'sec"


(* If we assume that 'sec is a boolean lattice: 
type_synonym sec = bool
definition \<Gamma>\<^sub>E :: "('r,'v,sec,'a) secvarmap \<Rightarrow> ('r, 'v \<times>sec) exp \<Rightarrow> sec"
  where "\<Gamma>\<^sub>E s e \<equiv>  (\<forall>v. v \<in> (vars e) \<longrightarrow> \<Gamma> s v)" 
*)

text \<open> (\<Gamma> s v) provides the security level (of the current content of) variable v in state s \<close>

abbreviation \<Gamma> :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'r \<Rightarrow> 'sec"
  where "\<Gamma> s v \<equiv> snd (varmap_st s v)"



text \<open> @{term \<Gamma>\<^sub>E} is relative to a state and a classification \<L> since both \<L> and \<Gamma> depend on the state   \<close>
 (*      the below matches the definition  \<Gamma>\<^sub>E(e) = \<Squnion>\<^sub>v\<^sub>\<in>\<^sub>v\<^sub>a\<^sub>r\<^sub>s\<^sub>(\<^sub>e\<^sub>) \<Gamma>\<^sub>v \<sqinter> \<L>(v)
       inf = \<sqinter> = meet    and     Sup = \<Squnion> = Join   with
       x \<le> y <=> x \<sqinter> y = x     and   x \<le> y <=> x \<squnion> y = y 
*)

definition \<Gamma>\<^sub>E :: "('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> ('r,'v,'sec,'a) secClass 
                                                                    \<Rightarrow> ('r, 'v \<times>'sec) exp \<Rightarrow> 'sec"
  where "\<Gamma>\<^sub>E s \<L> e \<equiv>  Sup ((\<lambda>v. inf (\<L> s v)  (\<Gamma> s v)) ` (vars e))"


(* from wp-if-rg: Base.thy and Typed_Predicate_Language.thy
 
definition supl :: "'a::bounded_lattice list \<Rightarrow> 'a"
  where "supl l \<equiv> fold sup l bot"

abbreviation lower (infix "\<sqinter>" 60)
  where "lower a b \<equiv> SOp (inf) a b"

abbreviation upper (infix "\<squnion>" 60)
  where "upper a b \<equiv> SOp (sup) a b"

abbreviation higher (infix "\<sqsupseteq>" 62)
  where "higher a b \<equiv> PSec (\<ge>) a b"
*)
text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c Skip \<L> G = True" |
    "guar\<^sub>c (Op v a f) \<L> G = ((v \<inter> (po a \<L>)) \<subseteq> guar (wp\<^sub>i a o wp\<^sub>a f) (step G))" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2)  \<L> G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If _ c\<^sub>1 c\<^sub>2) \<L> G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While _ _ _ c) \<L> G = (guar\<^sub>c c G)" |
    "guar\<^sub>c (DoWhile _ _ c _) \<L> G = (guar\<^sub>c c G)"



text \<open>Additional proof obligations to check information flow security, see CSF'2021 paper\<close>
fun po :: "('r,'v\<times>'sec) op \<Rightarrow> ('r,'v,'sec::complete_lattice,'a) secClass \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where
    "po (assign r e) \<L> =  {s| s. (\<Gamma>\<^sub>E s \<L> e) \<le> (\<L> s r)}" |
    "po (cmp v) \<L> = undefined" |
    "po (leak v va) \<L> = undefined"  |
    "po full_fence \<L> = undefined" |
    "po nop \<L> = undefined" 
 

text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wpif :: "'g rel \<Rightarrow> ('r,'v,('r,'v,'a) varmap','a) lang \<Rightarrow> ('r,'v,'a) varmap' set \<Rightarrow> ('r,'v,'a) varmap' set"
  where
    "wp R Skip Q = Q" |
    "wp R (Op v a f) Q = stabilize R (v \<inter> (po a) \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = stabilize R (po (cmp b)) \<inter> 
                           stabilize R (wp\<^sub>i (cmp b) (wp R c\<^sub>1 Q) \<inter> wp\<^sub>i (ncmp b) (wp R c\<^sub>2 Q))" |
     "wp R (While b I _ c) Q = (stabilize R I \<inter> 
       assert (I \<subseteq> (po (cmp b)) \<inter> wp\<^sub>i (cmp b) (wp R c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" |
    "wp R (DoWhile I _ c b) Q = (stabilize R I \<inter> 
       assert (I \<subseteq> (po (cmp b)) \<inter> wp R c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"


end