theory SimAsm_WPIF
  imports SimAsm_WP HOL.Complete_Lattices
begin

text \<open> The type secvarmap extends the state with the current security level for each variable,
        i.e., for each variable var \<mapsto> (val, secLevel) 
       'sec here is abstract but will be used as a general bounded_lattice or complete_lattice 
          with the corresponding operators \<sqinter> and \<squnion> in the definitions where required,
          we assume the order Low \<le> High  \<close>

type_synonym ('r,'v,'sec,'a) secvarmap = "('r,'v\<times>'sec,'a) varmap'"
type_synonym ('r,'v,'sec,'a) secauxop = "('r,'v,('r,'v,'sec,'a) secvarmap,'a) auxop"

text \<open> condSec models conditional security values that need to be evaluated in each state
          as a list of conditions and a function mapping a list of booleans mapped to a security value;
       secClass provides a type for (conditional) security classifications for each variable v
          (the type of \<L>)  \<close>

(* type_synonym ('r,'v,'sec) condSec = "(('r, 'v) bexp \<times> 'sec) list" *)
(* e.g., ([a = b, c < d], \<lambda> vList. if vList[0] then Low else vList[1] then High else...) *)

type_synonym ('r,'v,'sec) condSec = "(('r, 'v \<times> 'sec) bexp list \<times> (bool list \<Rightarrow> 'sec))"
type_synonym ('r,'v,'sec,'a) secClass = "'r \<Rightarrow> ('r,'v,'sec) condSec"


text \<open> (\<Gamma> s v) provides the security level (of the current content of) variable v in state s \<close>

abbreviation \<Gamma> :: "'r \<Rightarrow> ('r,'v,'sec,'a) secvarmap \<Rightarrow> 'sec"
  where "\<Gamma> v s \<equiv> snd (varmap_st s v)"

text \<open> @{term eval\<^sub>s\<^sub>e\<^sub>c} evaluates the conditional security level in the current state \<close>

fun eval\<^sub>s\<^sub>e\<^sub>c :: "('r,'v,'sec) condSec \<Rightarrow> ('r,'v,'sec,'a) secvarmap \<Rightarrow> 'sec"
  where "eval\<^sub>s\<^sub>e\<^sub>c (blist, f) s  = f (map (ev\<^sub>B  (varmap_st s)) blist)" 


text \<open> @{term \<Gamma>\<^sub>E} is relative to a state and a classification \<L> since both \<L> and \<Gamma> depend on the state   \<close>
 (*      the below matches the definition  \<Gamma>\<^sub>E(e) = \<Squnion>\<^sub>v\<^sub>\<in>\<^sub>v\<^sub>a\<^sub>r\<^sub>s\<^sub>(\<^sub>e\<^sub>) \<Gamma>\<^sub>v \<sqinter> \<L>(v)
       inf = \<sqinter> = meet    and     Sup = \<Squnion> = Join   with
       x \<le> y <=> x \<sqinter> y = x     and   x \<le> y <=> x \<squnion> y = y     *)

definition \<Gamma>\<^sub>E :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r, 'v \<times>'sec) expBexp 
                                       \<Rightarrow> ('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> 'sec"
  where "\<Gamma>\<^sub>E \<L> e s \<equiv>  Sup ((\<lambda>v. inf ((eval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) v s)  (\<Gamma> v s)) ` (vars e))"

definition bexpr :: "('r,'v,'sec,'a) secClass \<Rightarrow> 'r \<Rightarrow> ('r,'v\<times>'sec) expBexp list"
  where "bexpr \<L> r =  (map Bexpr \<circ> fst \<circ> \<L>) r" 

definition ctrlVars :: "('r,'v,'sec,'a) secClass \<Rightarrow> 'r set"
  where "ctrlVars \<L> \<equiv>  {cvar | cvar r. cvar \<in>  \<Union> (set (map vars ((bexpr \<L>) r)))}"

definition ctrled :: "('r,'v,'sec,'a) secClass \<Rightarrow> 'r \<Rightarrow> 'r set"
  where "ctrled \<L> c \<equiv> {r | r. c \<in> \<Union> (set (map vars ((bexpr \<L>) r)))}"


definition secureUpd :: "('r,'v,'sec::complete_lattice,'a) secClass \<Rightarrow> 'r \<Rightarrow> ('r,'v\<times>'sec) exp 
                                                    \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
   where "secureUpd \<L> r e \<equiv> {s | s. (\<forall> y. y \<in> (ctrled \<L> r) \<longrightarrow> 
    (\<Gamma>\<^sub>E \<L> (Expr e) s) \<le> ((eval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) y (s \<lparr>varmap_st := (varmap_st s)(r := ev\<^sub>E (varmap_st s) e)\<rparr>)))}" 


text \<open> Locale wpif sets up reasoning with additional proof obligations to verify information flow security \<close>

locale wpif = wp rg glb 
  for  rg :: "('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"

context wpif
begin

 (* (eval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) v (s \<lparr>varmap_st := (varmap_st s)(r := ev\<^sub>E (varmap_st s) e)\<rparr>)  *)

text \<open>Additional proof obligations to check information flow security, see CSF'2021 paper\<close>
fun po :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec) op \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where
    "po \<L> (assign r e) =  {s| s. ((\<Gamma>\<^sub>E \<L> (Expr e) s) \<le> ((eval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) r s)) \<and>
                             (r \<in> (ctrlVars \<L>) \<longrightarrow> s \<in> secureUpd \<L> r e)}" |
    "po \<L> (cmp b) =  {s| s. (\<Gamma>\<^sub>E \<L> (Bexpr b) s) \<le> bot}" |
    "po \<L> (leak c e) = {s| s. (\<Gamma>\<^sub>E \<L> (Expr e) s) \<le> ((eval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) c s)}"  |
    "po \<L> full_fence = {}" |
    "po \<L> nop = {}" 



section \<open>Predicate Transformations which takes \<L> and evaluation of  @{term \<Gamma>\<^sub>E} into account,
         this should happen "automatically" through the lifting of the value type 'v to ('v\<times>'sec)\<close>

(*  the normal wp\<^sub>i transformer should deliver the right results already:

fun wpif\<^sub>i :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec) op \<Rightarrow> ('r,'v,'sec,'a) secvarmap set
                                                              \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where 
    "wpif\<^sub>i \<L> (assign r e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)(r := ev\<^sub>E (varmap_st s) e)\<rparr>) \<in> Q}" |
    "wpif\<^sub>i \<L> (cmp b) Q =  {s. (ev\<^sub>B (varmap_st s) b) \<longrightarrow> s \<in> Q}" | 
    "wpif\<^sub>i \<L> (leak c e) Q = {s. (s \<lparr>varmap_st := (varmap_st s)(c := ev\<^sub>E (varmap_st s) e)\<rparr>) \<in> Q}" |
    "wpif\<^sub>i \<L> _ Q = Q"
*)


text \<open>Ensure all global operations in a thread conform to its guarantee - this glues in the PO \<close>
fun guar\<^sub>c_if
  where 
    "guar\<^sub>c_if Skip \<L> G = True" |
    "guar\<^sub>c_if (Op v a f) \<L> G = ((v \<inter> (po \<L> a)) \<subseteq> guar (wp\<^sub>i a o wp\<^sub>a f) (step G))" |
    "guar\<^sub>c_if (Seq c\<^sub>1 c\<^sub>2)  \<L> G = (guar\<^sub>c_if c\<^sub>1 \<L> G \<and> guar\<^sub>c_if c\<^sub>2 \<L> G)" |
    "guar\<^sub>c_if (If _ c\<^sub>1 c\<^sub>2) \<L> G = (guar\<^sub>c_if c\<^sub>1 \<L> G \<and> guar\<^sub>c_if c\<^sub>2 \<L> G)" |
    "guar\<^sub>c_if (While _ _ _ c) \<L> G = (guar\<^sub>c_if c \<L> G)" (*|
    "guar\<^sub>c_if (DoWhile _ _ c _) \<L> G = (guar\<^sub>c_if c \<L> G)" *)




end (* locale wpif  *)
(* ------------------------------------------------ *)

locale wpif_WOspec = wpif rg glb
  for rg :: "('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"

context wpif_WOspec
begin

text \<open>Transform a predicate based on a program c within an environment R under classification \<L> \<close>
fun wpif :: "'g rel \<Rightarrow> ('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec,('r,'v,'sec,'a) secvarmap,('r,'v,'sec,'a) secvarmap,'a) lang \<Rightarrow> 
                             ('r,'v,'sec,'a) secvarmap set \<Rightarrow> ('r,'v,'sec,'a) secvarmap set"
  where
    "wpif R \<L> Skip Q = Q" |
    "wpif R \<L> (Op v a f) Q = stabilize R (v \<inter> (po \<L> a) \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wpif R \<L> (Seq c\<^sub>1 c\<^sub>2) Q = wpif R \<L> c\<^sub>1 (wpif R \<L> c\<^sub>2 Q)" |
    "wpif R \<L> (If b c\<^sub>1 c\<^sub>2) Q = stabilize R (po \<L> (cmp b)) \<inter> 
                           stabilize R (wp\<^sub>i (cmp b) (wpif R \<L> c\<^sub>1 Q) \<inter> wp\<^sub>i (ncmp b) (wpif R \<L> c\<^sub>2 Q))" |
     "wpif R \<L> (While b I _ c) Q = (stabilize R I \<inter> 
       assert (I \<subseteq> (po \<L> (cmp b)) \<inter> wp\<^sub>i (cmp b) (wpif R \<L> c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" (* |
    "wpif R \<L> (DoWhile I _ c b) Q = (stabilize R  I \<inter> 
       assert (I \<subseteq> (po \<L> (cmp b)) \<inter> wpif R \<L> c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"
*)

end   (* locale wpif_WOspec *)
(* -------------------------------------------------- *)

text \<open> Information flow under speculative behaviour - this requires the labelling of variables  \<close>

locale wpif_spec = wp_spec rg glb + wpif rg glb
  for rg :: "('r,'v,'sec::complete_lattice,'a) secvarmap \<Rightarrow> 'l"
  and glb :: "('r,'v,'sec,'a) secvarmap \<Rightarrow> 'g"

text \<open>Labelled state (record) in which every variable appears in its Gl or UL variation \<close>
type_synonym ('r,'v,'sec) lcondSec = "('r label,'v,'sec) condSec"
type_synonym ('r,'v,'sec,'a) lsecvarmap = "('r label,'v,'sec,'a\<times>'a) secvarmap"
type_synonym ('r,'v,'sec,'a) lsecauxop = "('r,'v,('r,'v,'sec,'a) lsecvarmap,'a) auxop"

context wpif_spec
begin

text \<open> since the eval fct is used for the \<L> predicates, we label all variables as global \<close>

fun leval\<^sub>s\<^sub>e\<^sub>c :: "('r,'v,'sec) condSec \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap \<Rightarrow> 'sec"
   where "leval\<^sub>s\<^sub>e\<^sub>c (blist, f) s  = f (map ((ev\<^sub>B  (varmap_st s))\<circ> gl\<^sub>B) blist)"  


text \<open> @{term \<Gamma>\<^sub>E\<^sub>L} models the security level of an expression in which all expression
                   produced via \<L> are labelled as global, 
                   and all variables in other expressions are labelled as UL 
                   i.e., \<Squnion>_v ((\<L> v)^G  \<sqinter> (\<Gamma> v)^U) \<close>

definition \<Gamma>\<^sub>E\<^sub>L :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r, 'v \<times>'sec) expBexp \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap \<Rightarrow> 'sec"
   where "\<Gamma>\<^sub>E\<^sub>L \<L> e s \<equiv>  Sup ((\<lambda>v. inf ((leval\<^sub>s\<^sub>e\<^sub>c \<circ> \<L>) v s)  (\<Gamma> v (ul_restrict s))) ` (vars e))"  

text \<open>Additional proof obligations during speculation, only leaks operations produce a po \<close>
fun po\<^sub>s :: "('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec) op \<Rightarrow> ('r,'v,'sec,'a) lsecvarmap set"
  where
    "po\<^sub>s \<L> (assign r e) = {}" |
    "po\<^sub>s \<L> (cmp b) = {}" |
    "po\<^sub>s \<L> (leak c e) = {s| s. (\<Gamma>\<^sub>E\<^sub>L \<L> (Expr e) s) \<le> bot}" |
    "po\<^sub>s \<L> full_fence = {}" |
    "po\<^sub>s \<L> nop = {}" 


text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wpif :: "'g rel \<Rightarrow> ('r,'v,'sec,'a) secClass \<Rightarrow> ('r,'v\<times>'sec,('r,'v,'sec,'a) secvarmap,('r,'v,'sec,'a) lsecvarmap,'a) lang \<Rightarrow> 
                           ('r,'v\<times>'sec,'a) spec_state \<Rightarrow> ('r,'v\<times>'sec,'a) spec_state" 
  where
    "wpif R \<L> Skip Q = Q" |
    "wpif R \<L> (Op v a f) Q = (stabilize\<^sub>L R (v \<inter> (po\<^sub>s \<L> a) \<inter> wp\<^sub>i\<^sub>s a (wp\<^sub>i\<^sub>a f (fst Q))), 
                             stabilize R (v\<^sup>U \<inter> (po \<L> a) \<inter> wp\<^sub>i a (wp\<^sub>a f (snd Q))))" |
    "wpif R  \<L> (SimAsm.lang.Seq c\<^sub>1 c\<^sub>2) Q = wpif R  \<L> c\<^sub>1 (wpif R  \<L> c\<^sub>2 Q)" |
(* note: speculative component is not conditional on b because speculation may have started earlier. *)
    "wpif R  \<L> (If b c\<^sub>1 c\<^sub>2) Q = (let (Qs1,Q1) = wpif R \<L> c\<^sub>1 Q; (Qs2,Q2) = wpif R \<L> c\<^sub>2 Q in
       (Qs1 \<inter> Qs2, 
        stabilize R  (po \<L> (cmp b)) \<inter> (wp\<^sub>i (cmp b) Q1 \<inter> Qs2[y\<phi> sub y] \<inter> wp\<^sub>i (ncmp b) Q2 \<inter> Qs1[y\<phi> sub y])))" |
     "wpif R \<L> (While b Inv Inv\<^sub>s c) Q = 
      (assert\<^sub>s (Inv \<subseteq> [Q]\<^sub>s\<^sup>U \<inter>  po \<L> (cmp b) \<inter> wp\<^sub>i (cmp b) [(wpif R \<L> c (stabilize\<^sub>L R Inv\<^sub>s, stabilize R Inv))]\<^sub>;)) \<inter>\<^sub>s
      (assert\<^sub>s (Inv \<subseteq> (stabilize\<^sub>L R Inv\<^sub>s)\<^sup>U \<inter> wp\<^sub>i (ncmp b) [Q]\<^sub>;)) \<inter>\<^sub>s
      (assert\<^sub>s (Inv\<^sub>s \<subseteq> [Q]\<^sub>s \<inter> [(wpif R \<L> c (stabilize\<^sub>L R Inv\<^sub>s, stabilize R Inv))]\<^sub>s)) \<inter>\<^sub>s
      (stabilize\<^sub>L R Inv\<^sub>s, stabilize R Inv)"

(*
(* with  DoWhile Inv\<^sub>s Inv c b \<equiv> (c ; [b])* ; c ; [\<not>b]  *)
    "wpif R \<L> (DoWhile Inv\<^sub>s Inv c b) Q = merge R (Inv\<^sub>s\<^sup>L, Inv) \<inter>\<^sub>s
        (assert (Inv\<^sub>s\<^sup>L \<subseteq> [Q]\<^sub>s) \<inter> assert (Inv\<^sub>s\<^sup>L \<subseteq> [(wpif R \<L> c (Inv\<^sub>s\<^sup>L, Inv))]\<^sub>s), 
         assert (Inv \<subseteq> (po \<L> (cmp b))) \<inter> 
         assert (Inv \<subseteq> [(wpif R \<L> c (Inv\<^sub>s\<^sup>L, (stabilize R (wp\<^sub>i (cmp b) Inv))))]\<^sub>;) \<inter>
         assert (Inv \<subseteq> [(wpif R \<L> c (Inv\<^sub>s\<^sup>L, (stabilize R (wp\<^sub>i (ncmp b) [Q]\<^sub>;))))]\<^sub>;))"
 *)
end  (* of wpif_spec *)

end



