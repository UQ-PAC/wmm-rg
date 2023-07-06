theory SimAsm_WPIF
  imports SimAsm_WP HOL.Complete_Lattices
begin

text \<open> The type secvarmap introduces the current security level for each variable,
        i.e., for each variable var \<mapsto> (val, secLevel) 
       'sec here is abstract but will be used as a general bounded_lattice or complete_lattice 
          with the corresponding operators \<sqinter> and \<squnion> in the definitions where required,
          we assume the order Low \<le> High  \<close>

type_synonym ('r,'v,'sec,'a) secvarmap = "('r,'v\<times>'sec,'a) varmap'"
type_synonym ('r,'v,'sec,'a) secauxop = "('r,'v,('r,'v,'sec,'a) secvarmap,'a) auxop"

text \<open> condSec models conditional security values that need to be evaluated in each state; 
       secClass provides a type for (conditional) security classifications for each variable v \<close>

(* type_synonym ('r,'v,'sec) condSec = "(('r, 'v) bexp \<times> 'sec) list" *)
(* e.g., ([a = b, c < d], \<lambda> vList. if vList[0] then Low else vList[1] then High else...) *)

type_synonym ('r,'v,'sec) condSec = "(('r, 'v \<times> 'sec) bexp list \<times> (bool list \<Rightarrow> 'sec))"
type_synonym ('r,'v,'sec,'a) secClass = "'r \<Rightarrow> ('r,'v,'sec) condSec"


(* If we assume that 'sec is a boolean lattice: 
type_synonym sec = bool
definition \<Gamma>\<^sub>E :: "('r,'v,sec,'a) secvarmap \<Rightarrow> ('r, 'v \<times>sec) exp \<Rightarrow> sec"
  where "\<Gamma>\<^sub>E s e \<equiv>  (\<forall>v. v \<in> (vars e) \<longrightarrow> \<Gamma> s v)" 
*)

text \<open> (\<Gamma> s v) provides the security level (of the current content of) variable v in state s \<close>

abbreviation \<Gamma> :: "'r \<Rightarrow> ('r,'v,'sec,'a) secvarmap \<Rightarrow> 'sec"
  where "\<Gamma> v s \<equiv> snd (varmap_st s v)"

fun eval\<^sub>s\<^sub>e\<^sub>c :: "('r,'v,'sec) condSec \<Rightarrow> ('r,'v,'sec,'a) secvarmap \<Rightarrow> 'sec"
  where "eval\<^sub>s\<^sub>e\<^sub>c (blist, f) s  = f (map (ev\<^sub>B  (varmap_st s)) blist)" 


text \<open> @{term \<Gamma>\<^sub>E} is relative to a state and a classification \<L> since both \<L> and \<Gamma> depend on the state   \<close>
 (*      the below matches the definition  \<Gamma>\<^sub>E(e) = \<Squnion>\<^sub>v\<^sub>\<in>\<^sub>v\<^sub>a\<^sub>r\<^sub>s\<^sub>(\<^sub>e\<^sub>) \<Gamma>\<^sub>v \<sqinter> \<L>(v)
       inf = \<sqinter> = meet    and     Sup = \<Squnion> = Join   with
       x \<le> y <=> x \<sqinter> y = x     and   x \<le> y <=> x \<squnion> y = y 
*)


definition \<Gamma>\<^sub>E :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r, 'v \<times>'sec) expBexp => ('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> 'sec"
  where "\<Gamma>\<^sub>E \<L> e s \<equiv>  Sup ((\<lambda>v. inf ((eval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) v s)  (\<Gamma> v s)) ` (vars e))"
  (* where "\<Gamma>\<^sub>E s \<L> e \<equiv>  Sup ((\<lambda>v. inf (\<L> s v)  (\<Gamma> s v)) ` (vars e))" *)


text \<open> Locale wpif sets up reasoning with additional proof obligations to verify information flow security \<close>

locale wpif = wp rg glb 
  for  rg :: "('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"

context wpif
begin

text \<open>Additional proof obligations to check information flow security, see CSF'2021 paper\<close>
fun po :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec) op \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where
    "po \<L> (assign r e) =  {s| s. (\<Gamma>\<^sub>E \<L> (Expr e) s) \<le> ((eval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) r s)}" |
    "po \<L> (cmp b) =  {s| s. (\<Gamma>\<^sub>E \<L> (Bexpr b) s) \<le> bot}" |
    "po \<L> (leak v va) = {s| s. (\<Gamma>\<^sub>E \<L> (Expr va) s) \<le> ((eval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) v s)}"  |
    "po \<L> full_fence = {}" |
    "po \<L> nop = {}" 


text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c_if
  where 
    "guar\<^sub>c_if Skip \<L> G = True" |
    "guar\<^sub>c_if (Op v a f) \<L> G = ((v \<inter> (po \<L> a)) \<subseteq> guar (wp\<^sub>i a o wp\<^sub>a f) (step G))" |
    "guar\<^sub>c_if (Seq c\<^sub>1 c\<^sub>2)  \<L> G = (guar\<^sub>c_if c\<^sub>1 \<L> G \<and> guar\<^sub>c_if c\<^sub>2 \<L> G)" |
    "guar\<^sub>c_if (If _ c\<^sub>1 c\<^sub>2) \<L> G = (guar\<^sub>c_if c\<^sub>1 \<L> G \<and> guar\<^sub>c_if c\<^sub>2 \<L> G)" |
    "guar\<^sub>c_if (While _ _ _ c) \<L> G = (guar\<^sub>c_if c \<L> G)" |
    "guar\<^sub>c_if (DoWhile _ _ c _) \<L> G = (guar\<^sub>c_if c \<L> G)"

end (* locale wpif  *)
(* ------------------------------------------------ *)

locale wpif_WOspec = wpif rg glb
  for rg :: "('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"

context wpif_WOspec
begin

text \<open>Transform a predicate based on a program c within an environment R under classification \<L> \<close>
fun wpif :: "'g rel \<Rightarrow> ('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec,('r,'v,'sec,'a) secvarmap,'a) lang \<Rightarrow> 
                             ('r,'v,'sec,'a) secvarmap set \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where
    "wpif R \<L> Skip Q = Q" |
    "wpif R \<L> (Op v a f) Q = stabilize R (v \<inter> (po \<L> a) \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wpif R \<L> (Seq c\<^sub>1 c\<^sub>2) Q = wpif R \<L> c\<^sub>1 (wpif R \<L> c\<^sub>2 Q)" |
    "wpif R \<L> (If b c\<^sub>1 c\<^sub>2) Q = stabilize R (po \<L> (cmp b)) \<inter> 
                           stabilize R (wp\<^sub>i (cmp b) (wpif R \<L> c\<^sub>1 Q) \<inter> wp\<^sub>i (ncmp b) (wpif R \<L> c\<^sub>2 Q))" |
     "wpif R \<L> (While b I _ c) Q = (stabilize R I \<inter> 
       assert (I \<subseteq> (po \<L> (cmp b)) \<inter> wp\<^sub>i (cmp b) (wpif R \<L> c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" |
    "wpif R \<L> (DoWhile I _ c b) Q = (stabilize R I \<inter> 
       assert (I \<subseteq> (po \<L> (cmp b)) \<inter> wpif R \<L> c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"

end   (* locale wpif_WOspec *)
(* -------------------------------------------------- *)

locale wpif_spec = wp_spec rg glb + wpif rg glb
  for rg :: "('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"

text \<open>Labelled state (record) in which every variable appears in its Gl and UL variation \<close>
type_synonym ('r,'v,'sec) lcondSec = "('r label,'v,'sec) condSec"
type_synonym ('r,'v,'sec,'a) lsecvarmap = "('r label,'v,'sec,'a) secvarmap"
type_synonym ('r,'v,'sec,'a) lsecauxop = "('r,'v,('r,'v,'sec,'a) lsecvarmap,'a) auxop"

context wpif_spec
begin

fun leval\<^sub>s\<^sub>e\<^sub>c :: "('r,'v,'sec) condSec \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap \<Rightarrow> 'sec"
  where "leval\<^sub>s\<^sub>e\<^sub>c (blist, f) s  = f (map ((ev\<^sub>B  (varmap_st s))\<circ> gl\<^sub>B) blist)" 


text \<open> @{term \<Gamma>\<^sub>E\<^sub>L} models the security level of an expression in which all expression
                   produced via \<L> are labelled as global, 
                   and all variables in other expressions are labelled as UL 
                   i.e., \<Squnion>_v ((\<L> v)^G  \<sqinter> (\<Gamma> v)^U),\<close>

definition \<Gamma>\<^sub>E\<^sub>L :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r, 'v \<times>'sec) expBexp \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap \<Rightarrow> 'sec"
  where "\<Gamma>\<^sub>E\<^sub>L \<L> e s \<equiv>  Sup ((\<lambda>v. inf ((leval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) v s)  (\<Gamma> v (ul_restrict s))) ` (vars e))" 

text \<open>Additional proof obligations during speculation, different po for speculated leaks \<close>
fun po\<^sub>s :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec::complete_lattice) op \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap set"
  where
    "po\<^sub>s \<L> (assign r e) = {s| s. (\<Gamma>\<^sub>E\<^sub>L \<L> (Expr e) s) \<le> ((leval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) r s)}" |
    "po\<^sub>s \<L> (cmp b) = {s| s. (\<Gamma>\<^sub>E\<^sub>L \<L> (Bexpr b) s) \<le> bot}" |
    "po\<^sub>s \<L> (leak v va) = {s| s. (\<Gamma>\<^sub>E\<^sub>L \<L> (Expr va) s) \<le> bot}" |
    "po\<^sub>s \<L> full_fence = {}" |
    "po\<^sub>s \<L> nop = {}" 


text \<open> Transform a predicate over a speculation, which introduces labels to predicates \<close>
fun wp\<^sub>i\<^sub>s_if :: "('r,'v\<times>'sec) op \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap set \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap set"     
  where 
    "wp\<^sub>i\<^sub>s_if (assign r e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)((Ul r) := (ev\<^sub>E (varmap_st s) (ul\<^sub>E e)))\<rparr>) \<in> Q}" |
    "wp\<^sub>i\<^sub>s_if (cmp b) Q =  {s. (ev\<^sub>B (varmap_st s) (ul\<^sub>B b)) \<longrightarrow> s \<in> Q}" | 
    "wp\<^sub>i\<^sub>s_if (leak c e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)((Gl c) := ev\<^sub>E (varmap_st s) (ul\<^sub>E e))\<rparr>) \<in> Q}" |
    "wp\<^sub>i\<^sub>s_if full_fence Q = UNIV"  |
    "wp\<^sub>i\<^sub>s_if nop Q = Q"  


text \<open>wp_spec transformer on lang.\<close>
fun wp\<^sub>s_if :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec,('r,'v,'sec,'a) secvarmap,'a) lang \<Rightarrow> 
                                  ('r,'v,'sec,'a) lsecvarmap pred \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap pred"   
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
    "wpif R \<L> (Op v a f) Q = stabilize R (v \<inter> (po \<L> a) \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wpif R \<L> (Seq c\<^sub>1 c\<^sub>2) Q = wpif R \<L> c\<^sub>1 (wpif R \<L> c\<^sub>2 Q)" |
    "wpif R \<L> (If b c\<^sub>1 c\<^sub>2) Q = 
           (merge R  (stabilize R (wp\<^sub>s_if \<L> c\<^sub>2  (spec Q))\<^sup>U) (stabilize R (wp\<^sub>i (cmp b) (wpif R \<L> c\<^sub>1 Q))))
         \<inter> (merge R  (stabilize R (wp\<^sub>s_if \<L> c\<^sub>1  (spec Q))\<^sup>U) (stabilize R (wp\<^sub>i (ncmp b) (wpif R \<L> c\<^sub>2 Q))))" |
(* here (wp\<^sub>s r true) is simplified to Q *)
    "wpif R \<L> (While b Imix Ispec c) Q =
      (stabilize R Imix \<inter>  
        assert (Imix \<subseteq> (po \<L> (cmp b)) \<inter>
                        (merge R Q (wp\<^sub>i (cmp b) (wpif R \<L> c (stabilize R Imix)))) \<inter>
                        (merge R  (stabilize R (wp\<^sub>s_if \<L> c (spec Ispec))\<^sup>U) (wp\<^sub>i (ncmp b) Q))))" |
    "wpif R \<L> (DoWhile Imix Ispec c b) Q =
      (stabilize R Imix \<inter>  
        assert (Imix \<subseteq> (po \<L> (cmp b)) \<inter>
                        (merge R (stabilize R ((wp\<^sub>s_if \<L> c (Q\<^sup>L \<inter> (stabilize R Ispec)\<^sup>L))\<^sup>U))  
                                  (wpif R \<L> c ((stabilize R (wp\<^sub>i (cmp b) (stabilize R Imix))) \<inter>
                                           (stabilize R (wp\<^sub>i (ncmp b) Q)))))))" 

end  (* of wpif_spec *)

end