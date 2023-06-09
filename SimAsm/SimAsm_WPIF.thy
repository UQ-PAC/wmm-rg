theory SimAsm_WPIF
  imports SimAsm_WP HOL.Lattices
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

(* --- from locale wp -------*)

print_locale wp

locale wpif = wp project rg glb
  for  project :: "('r \<Rightarrow> 'v\<times>'sec::complete_lattice) \<Rightarrow> ('r,'v,'sec,'a) secvarmap" 
  and rg :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"


context wpif
begin

text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step_if :: "'g rel \<Rightarrow> ('r,'v,'sec,'a) secvarmap rel"
  where "step_if R \<equiv> {(t,t'). (glb t, glb t') \<in> R}"

text \<open> Transform a predicate based on an sub-operation, simple wp \<close>
(* this is the normal wp transformer on ops *)
fun wp\<^sub>i_if :: "('r,'v\<times>'sec) op \<Rightarrow> ('r,'v,'sec,'a) secvarmap set \<Rightarrow> ('r,'v,'sec,'a) secvarmap set" 
  where 
    "wp\<^sub>i_if (assign r e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)(r := ev\<^sub>E (varmap_st s) e)\<rparr>) \<in> Q}" |
    "wp\<^sub>i_if (cmp b) Q =  {s. (ev\<^sub>B (varmap_st s) b) \<longrightarrow> s \<in> Q}" | 
    "wp\<^sub>i_if (leak c e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)(c := ev\<^sub>E (varmap_st s) e)\<rparr>) \<in> Q}" |
    "wp\<^sub>i_if _ Q = Q"

text \<open>Transform a predicate based on an auxiliary state update\<close>
fun wp\<^sub>a_if :: "(('r,'v,'sec,'a) secvarmap,'a) auxfn \<Rightarrow> ('r,'v,'sec,'a) secvarmap set \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  (* where "wp\<^sub>a a Q = {t. t(aux: a) \<in> Q}" *)
  where "wp\<^sub>a_if a Q = {t. t\<lparr>more := a t\<rparr> \<in> Q}"



text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r_if :: "('r,'v,'sec,'a) secvarmap trans \<Rightarrow> ('r,'v,'sec,'a) secvarmap rtrans"
  where "wp\<^sub>r_if f G \<equiv> {(s,s'). s' \<in> f {s'. (s,s') \<in> G}}"

subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar_if
  where "guar_if f G \<equiv> {t. (t,t) \<in> (wp\<^sub>r_if f G)}"


text \<open>Additional proof obligations to check information flow security, see CSF'2021 paper\<close>
fun po :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec::complete_lattice) op \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where
    "po \<L> (assign r e) =  {s| s. (\<Gamma>\<^sub>E s \<L> e) \<le> (\<L> s r)}" |
    "po \<L> (cmp v) = undefined" |
    "po \<L> (leak v va) = undefined"  |
    "po \<L> full_fence = undefined" |
    "po \<L> nop = undefined" 

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c_if
  where 
    "guar\<^sub>c_if Skip \<L> G = True" |
    "guar\<^sub>c_if (Op v a f) \<L> G = ((v \<inter> (po \<L> a)) \<subseteq> guar_if (wp\<^sub>i_if a o wp\<^sub>a_if f) (step_if G))" |
    "guar\<^sub>c_if (Seq c\<^sub>1 c\<^sub>2)  \<L> G = (guar\<^sub>c_if c\<^sub>1 \<L> G \<and> guar\<^sub>c_if c\<^sub>2 \<L> G)" |
    "guar\<^sub>c_if (If _ c\<^sub>1 c\<^sub>2) \<L> G = (guar\<^sub>c_if c\<^sub>1 \<L> G \<and> guar\<^sub>c_if c\<^sub>2 \<L> G)" |
    "guar\<^sub>c_if (While _ _ _ c) \<L> G = (guar\<^sub>c_if c \<L> G)" |
    "guar\<^sub>c_if (DoWhile _ _ c _) \<L> G = (guar\<^sub>c_if c \<L> G)"

end (* locale wpif  *)
(* ------------------------------------------------ *)

locale wpif_WOspec = wpif project rg glb
  for project :: "('r \<Rightarrow> 'v\<times>'sec::complete_lattice) \<Rightarrow> ('r,'v,'sec,'a) secvarmap" 
  and rg :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"

context wpif_WOspec
begin

text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wpif :: "'g rel \<Rightarrow> ('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec,('r,'v,'sec,'a) secvarmap,'a) lang \<Rightarrow> 
                             ('r,'v,'sec,'a) secvarmap set \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where
    "wpif R \<L> Skip Q = Q" |
    "wpif R \<L> (Op v a f) Q = stabilize R (v \<inter> (po \<L> a) \<inter> wp\<^sub>i_if a (wp\<^sub>a_if f Q))" |
    "wpif R \<L> (Seq c\<^sub>1 c\<^sub>2) Q = wpif R \<L> c\<^sub>1 (wpif R \<L> c\<^sub>2 Q)" |
    "wpif R \<L> (If b c\<^sub>1 c\<^sub>2) Q = stabilize R (po \<L> (cmp b)) \<inter> 
                           stabilize R (wp\<^sub>i (cmp b) (wpif R \<L> c\<^sub>1 Q) \<inter> wp\<^sub>i (ncmp b) (wpif R \<L> c\<^sub>2 Q))" |
     "wpif R \<L> (While b I _ c) Q = (stabilize R I \<inter> 
       assert (I \<subseteq> (po \<L> (cmp b)) \<inter> wp\<^sub>i (cmp b) (wpif R \<L> c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" |
    "wpif R \<L> (DoWhile I _ c b) Q = (stabilize R I \<inter> 
       assert (I \<subseteq> (po \<L> (cmp b)) \<inter> wpif R \<L> c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"

end   (* locale wpif_WOspec *)
(* -------------------------------------------------- *)

locale wpif_spec = wp_spec project rg glb + wpif project rg glb
  for project :: "('r \<Rightarrow> 'v\<times>'sec::complete_lattice) \<Rightarrow> ('r,'v,'sec,'a) secvarmap" 
  and rg :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"

text \<open>Labelled state (record) in which every variable appears in its Gl and UL variation \<close>
type_synonym ('r,'v,'sec,'a) lsecvarmap = "('r label,'v,'sec,'a) secvarmap"
type_synonym ('r,'v,'sec,'a) lsecopbasic = "('r label,'v,('r,'v,'sec,'a) lsecvarmap,'a) opbasic" 
type_synonym ('r,'v,'sec,'a) lsecauxop = "('r,'v,('r,'v,'sec,'a) lsecvarmap,'a) auxop"

context wpif_spec
begin

text \<open>Additional proof obligations during speculation, different po for speculated leaks \<close>
fun po\<^sub>s :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec::complete_lattice) op \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap set"
  where
    "po\<^sub>s \<L> (assign r e) = undefined" |
    "po\<^sub>s \<L> (cmp v) = undefined" |
    "po\<^sub>s \<L> full_fence = undefined" |
    "po\<^sub>s \<L> nop = undefined" |
    "po\<^sub>s \<L> (leak v va) = undefined" 


text \<open> Transform a predicate over a speculation, which introduces labels to predicates \<close>
fun wp\<^sub>i\<^sub>s_if :: "('r,'v\<times>'sec) op \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap set \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap set"          (* wp_spec on ops *)
  where 
    "wp\<^sub>i\<^sub>s_if (assign r e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)((Ul r) := (ev\<^sub>E (varmap_st s) (ul\<^sub>E e)))\<rparr>) \<in> Q}" |
    "wp\<^sub>i\<^sub>s_if (cmp b) Q =  {s. (ev\<^sub>B (varmap_st s) (ul\<^sub>B b)) \<longrightarrow> s \<in> Q}" | 
    "wp\<^sub>i\<^sub>s_if (leak c e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)((Gl c) := ev\<^sub>E (varmap_st s) (ul\<^sub>E e))\<rparr>) \<in> Q}" |
    "wp\<^sub>i\<^sub>s_if full_fence Q = UNIV"  |
    "wp\<^sub>i\<^sub>s_if nop Q = Q"  


text \<open>wp_spec transformer on lang.\<close>
fun wp\<^sub>s_if :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec,('r,'v,'sec,'a) secvarmap,'a) lang \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap pred \<Rightarrow> 
                                                                            ('r,'v,'sec,'a) lsecvarmap pred"   
  where 
    "wp\<^sub>s_if \<L> Skip Q = Q" |
    "wp\<^sub>s_if \<L> (Op v a f) Q = (v\<^sup>L \<inter> (po\<^sub>s \<L> a) \<inter> (wp\<^sub>i\<^sub>s_if a (wp\<^sub>a f Q\<^sup>U)\<^sup>L))" |
    "wp\<^sub>s_if \<L> (Seq c\<^sub>1 c\<^sub>2) Q = wp\<^sub>s_if \<L> c\<^sub>1 (wp\<^sub>s_if \<L> c\<^sub>2 Q)" |
    "wp\<^sub>s_if \<L> (If b c\<^sub>1 c\<^sub>2) Q = (wp\<^sub>s_if \<L> c\<^sub>1 Q) \<inter> (wp\<^sub>s_if \<L> c\<^sub>2 Q)" |
    "wp\<^sub>s_if \<L> (While b Imix Ispec c) Q = undefined" | 
    "wp\<^sub>s_if \<L> (DoWhile Imix Ispec c b) Q = undefined"


text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wpif :: "'g rel \<Rightarrow> ('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec,('r,'v,'sec,'a) secvarmap,'a) lang \<Rightarrow> 
                             ('r,'v,'sec,'a) secvarmap set \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where
    "wpif R \<L> Skip Q = Q" |
    "wpif R \<L> (Op v a f) Q = stabilize R (v \<inter> (po \<L> a) \<inter> wp\<^sub>i_if a (wp\<^sub>a_if f Q))" |
    "wpif R \<L> (Seq c\<^sub>1 c\<^sub>2) Q = wpif R \<L> c\<^sub>1 (wpif R \<L> c\<^sub>2 Q)" |
    "wpif R \<L> (If b c\<^sub>1 c\<^sub>2) Q = 
           (merge R  (stabilize R (wp\<^sub>s_if \<L> c\<^sub>2  (spec Q))\<^sup>U) (stabilize R (wp\<^sub>i_if (cmp b) (wpif R \<L> c\<^sub>1 Q))))
         \<inter> (merge R  (stabilize R (wp\<^sub>s_if \<L> c\<^sub>1  (spec Q))\<^sup>U) (stabilize R (wp\<^sub>i_if (ncmp b) (wpif R \<L> c\<^sub>2 Q))))" |
(* here (wp\<^sub>s r true) is simplified to Q *)
    "wpif R \<L> (While b Imix Ispec c) Q =
      (stabilize R Imix \<inter>  
        assert (Imix \<subseteq> (po \<L> (cmp b)) \<inter>
                        (merge R Q (wp\<^sub>i_if (cmp b) (wpif R \<L> c (stabilize R Imix)))) \<inter>
                        (merge R  (stabilize R (wp\<^sub>s_if \<L> c (spec Ispec))\<^sup>U) (wp\<^sub>i_if (ncmp b) Q))))" |
    "wpif R \<L> (DoWhile Imix Ispec c b) Q =
      (stabilize R Imix \<inter>  
        assert (Imix \<subseteq> (po \<L> (cmp b)) \<inter>
                        (merge R (stabilize R ((wp\<^sub>s_if \<L> c (Q\<^sup>L \<inter> (stabilize R Ispec)\<^sup>L))\<^sup>U))  
                                  (wpif R \<L> c ((stabilize R (wp\<^sub>i_if (cmp b) (stabilize R Imix))) \<inter>
                                           (stabilize R (wp\<^sub>i_if (ncmp b) Q)))))))" 


end