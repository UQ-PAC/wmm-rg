theory SimAsm
  imports  "../Security"  SimAsm_Exp
begin

text \<open>Instruction Reordering\<close>
text \<open>Only pattern match on first argument due to performance issues\<close>
fun re\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op \<Rightarrow> bool" 
  where
    "re\<^sub>i full_fence \<alpha> = False" |
    "re\<^sub>i (cmp b) \<alpha> = (\<alpha> \<noteq> full_fence \<and> wr \<alpha> \<subseteq> locals \<and> rd (cmp b) \<inter> wr \<alpha> = {} \<and> rd (cmp b) \<inter> rd \<alpha> \<subseteq> locals)" |
    "re\<^sub>i \<alpha> \<beta> = (\<beta> \<noteq> full_fence \<and> wr \<alpha> \<inter> wr \<beta> = {} \<and> rd \<alpha> \<inter> wr \<beta> = {} \<and> rd \<alpha> \<inter> rd \<beta> \<subseteq> locals)"

fun re\<^sub>i' :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op \<Rightarrow> bool" where
"re\<^sub>i' full_fence \<alpha> = False" |
"re\<^sub>i' \<alpha> full_fence = False" |
"re\<^sub>i' (cmp b) \<alpha> = ((wr \<alpha> \<subseteq> locals) \<and> (wr \<alpha> \<inter> rd (cmp b) = {}) \<and> (rd (cmp b) \<inter> rd \<alpha> \<subseteq> locals))" |
"re\<^sub>i' \<alpha> \<beta> = ((wr \<alpha> \<inter> wr \<beta> = {}) \<and> (wr \<beta> \<inter> rd \<alpha> = {}) \<and> (rd \<alpha> \<inter> rd \<beta> \<subseteq> locals))"

lemma "re\<^sub>i' \<alpha> \<beta> = re\<^sub>i \<alpha> \<beta>"
by (induction rule: re\<^sub>i'.induct) auto

fun fwd\<^sub>i  :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op" 
  where "fwd\<^sub>i \<alpha> (assign x e) = subst\<^sub>i \<alpha> x e" | "fwd\<^sub>i \<alpha> _ = \<alpha>"

section \<open>Auxiliary State Updates\<close>

text \<open>
We wish to support auxiliary state to support more abstract reasoning about data structures
and concurrency.
This is achieved by allowing arbitrary extensions to the state representation, which
can be updated atomically at any sub-operation.
This auxiliary state cannot influence real execution behaviour by definition.
\<close>
type_synonym ('v,'g,'r,'a) auxop = "('v,'g,'r) op \<times> ('v,'g,'r,'a) auxfn"

fun beh\<^sub>a :: "('v,'g,'r,'a) auxop \<Rightarrow> ('v,'g,'r,'a) state rel"
  where "beh\<^sub>a (\<alpha>,f) = st_beh\<^sub>i \<alpha> O {(t,t'). t' = t(aux: f)}"

fun re\<^sub>a :: "('v,'g,'r,'a) auxop \<Rightarrow> ('v,'g,'r,'a) auxop \<Rightarrow> bool" 
  where "re\<^sub>a (\<alpha>,_) (\<beta>,_) = re\<^sub>i \<alpha> \<beta>"


section \<open>Instruction Specification Language\<close>

text \<open>
To instantiate the abstract theory, we must couple each sub-operation with its precondition
and behaviour in a tuple\<close>
(* ('a,'b) basic = ('a \<times> 'b set \<times> 'b rel); 'a = (inst \<times> aux);  'b = state *)
type_synonym ('v,'g,'r,'a) opbasic = "(('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) basic"

fun re\<^sub>s :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) opbasic \<Rightarrow> bool"
  where "re\<^sub>s (\<alpha>,_,_) (\<beta>,_,_) = re\<^sub>a \<alpha> \<beta>"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) auxop \<Rightarrow> ('v,'g,'r,'a) opbasic" 
  where 
    "fwd\<^sub>s ((\<alpha>,f),v,b) (assign x e,_) = (let p = (subst\<^sub>i \<alpha> x e, f) in  (p,v, beh\<^sub>a p))" |
    "fwd\<^sub>s ((\<alpha>,f),v,b) (leak c e,_) = ((\<alpha>,f),v,beh\<^sub>a (\<alpha>,f))" |
                                    (* (let p = (subst\<^sub>i \<alpha> c e, f) in  (p,v, beh\<^sub>a p))" | *)
    "fwd\<^sub>s ((\<alpha>,f),v,b) (\<beta>,_) = ((\<alpha>,f),v,beh\<^sub>a (\<alpha>,f))"

text \<open>Lift an operation with specification\<close>
definition liftg :: "('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) auxfn \<Rightarrow> ('v,'g,'r,'a) opbasic" 
  ("\<lfloor>_,_,_\<rfloor>" 100)
  where "liftg v \<alpha> f \<equiv> ((\<alpha>,f), v, beh\<^sub>a (\<alpha>,f))"

text \<open>Lift an operation without specification\<close>
definition liftl :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) opbasic" 
  ("\<lfloor>_\<rfloor>" 100)
  where "liftl \<alpha> \<equiv> ((\<alpha>,state_rec.more), UNIV, beh\<^sub>a (\<alpha>,state_rec.more))"

section \<open>Language Definition\<close>


(* predicates are no longer sets of states but sets of trees, ie., of type predTree *)
(* IF has another sub-command c\<^sub>3 to model the program after the If -- for the semantics of 
         the speculation; even though for wp reasoning we make use of the wp(c\<^sub>3, Q) instead *)

datatype ('v,'g,'r,'a) lang =
  Skip
  | Op "('v,'g,'r,'a) pred" "('v,'g,'r) op" "('v,'g,'r,'a) auxfn"
  | Seq "('v,'g,'r,'a) lang" "('v,'g,'r,'a) lang"
  | If "('v,'g,'r) bexp" "('v,'g,'r,'a) lang" "('v,'g,'r,'a) lang" "('v,'g,'r,'a) lang"  
(*  | If "('v,'g,'r) bexp" "('v,'g,'r,'a) lang" "('v,'g,'r,'a) lang" *)
  | While "('v,'g,'r) bexp" "('v,'g,'r,'a) pred" "('v,'g,'r,'a) lang"
  | DoWhile "('v,'g,'r,'a) pred" "('v,'g,'r,'a) lang" "('v,'g,'r) bexp"



end
