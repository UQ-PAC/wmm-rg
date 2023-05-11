theory SimAsm
  imports  "../Security"  SimAsm_Exp
begin

type_synonym ('s,'a) auxfn = "'s \<Rightarrow> 'a"
type_synonym ('r,'v,'s,'a) auxop = "('r,'v) op \<times> ('s,'a) auxfn"

type_synonym ('r,'v,'s,'a) opbasic = "(('r,'v,'s,'a) auxop, 's) basic"

type_synonym ('r,'v,'s,'a) pred = "'s set"



(* predicates are no longer sets of states but sets of trees, ie., of type predTree *)
(* IF has another sub-command c\<^sub>3 to model the program after the If -- for the semantics of 
         the speculation; even though for wp reasoning we make use of the wp(c\<^sub>3, Q) instead *)

datatype ('r,'v,'s,'a) lang =
  Skip
  | Op "('r,'v,'s,'a) pred" "('r,'v) op" "('s,'a) auxfn"
  | Seq "('r,'v,'s,'a) lang" "('r,'v,'s,'a) lang"
  | If "('r,'v) bexp" "('r,'v,'s,'a) lang" "('r,'v,'s,'a) lang" "('r,'v,'s,'a) lang"  
(*  | If "('v,'g,'r) bexp" "('r,'v,'s,'a) lang" "('r,'v,'s,'a) lang" *)
  | While "('r,'v) bexp" "('r,'v,'s,'a) pred" "('r,'v,'s,'a) lang"
  | DoWhile "('r,'v,'s,'a) pred" "('r,'v,'s,'a) lang" "('r,'v) bexp"


context expression
begin

text \<open>Instruction Reordering\<close>
text \<open>Only pattern match on first argument due to performance issues\<close>
fun re\<^sub>i :: "('r,'v) op \<Rightarrow> ('r,'v) op \<Rightarrow> bool" 
  where
    "re\<^sub>i full_fence \<alpha> = False" |
    "re\<^sub>i (cmp b) \<alpha> = (\<alpha> \<noteq> full_fence \<and> wr \<alpha> \<subseteq> locals \<and> rd (cmp b) \<inter> wr \<alpha> = {} \<and> rd (cmp b) \<inter> rd \<alpha> \<subseteq> locals)" |
    "re\<^sub>i \<alpha> \<beta> = (\<beta> \<noteq> full_fence \<and> wr \<alpha> \<inter> wr \<beta> = {} \<and> rd \<alpha> \<inter> wr \<beta> = {} \<and> rd \<alpha> \<inter> rd \<beta> \<subseteq> locals)"

fun re\<^sub>i' :: "('r,'v) op \<Rightarrow> ('r,'v) op \<Rightarrow> bool" where
"re\<^sub>i' full_fence \<alpha> = False" |
"re\<^sub>i' \<alpha> full_fence = False" |
"re\<^sub>i' (cmp b) \<alpha> = ((wr \<alpha> \<subseteq> locals) \<and> (wr \<alpha> \<inter> rd (cmp b) = {}) \<and> (rd (cmp b) \<inter> rd \<alpha> \<subseteq> locals))" |
"re\<^sub>i' \<alpha> \<beta> = ((wr \<alpha> \<inter> wr \<beta> = {}) \<and> (wr \<beta> \<inter> rd \<alpha> = {}) \<and> (rd \<alpha> \<inter> rd \<beta> \<subseteq> locals))"

lemma "re\<^sub>i' \<alpha> \<beta> = re\<^sub>i \<alpha> \<beta>"
by (induction rule: re\<^sub>i'.induct) auto

fun fwd\<^sub>i  :: "('r,'v) op \<Rightarrow> ('r,'v) op \<Rightarrow> ('r,'v) op" 
  where "fwd\<^sub>i \<alpha> (assign x e) = subst\<^sub>i \<alpha> x e" | "fwd\<^sub>i \<alpha> _ = \<alpha>"

section \<open>Auxiliary State Updates\<close>

text \<open>
We wish to support auxiliary state to support more abstract reasoning about data structures
and concurrency.
This is achieved by allowing arbitrary extensions to the state representation, which
can be updated atomically at any sub-operation.
This auxiliary state cannot influence real execution behaviour by definition.
\<close>

fun beh\<^sub>a :: "('r,'v,'s,'a) auxop \<Rightarrow> 's rel"
  where "beh\<^sub>a (\<alpha>,f) = st_beh\<^sub>i \<alpha> O {(t,t'). t' = t(aux: f)}"

fun re\<^sub>a :: "('r,'v,'s,'a) auxop \<Rightarrow> ('r,'v,'s,'a) auxop \<Rightarrow> bool" 
  where "re\<^sub>a (\<alpha>,_) (\<beta>,_) = re\<^sub>i \<alpha> \<beta>"


section \<open>Instruction Specification Language\<close>

text \<open>
To instantiate the abstract theory, we must couple each sub-operation with its precondition
and behaviour in a tuple\<close>
(* ('a,'b) basic = ('a \<times> 'b set \<times> 'b rel); 'a = (inst \<times> aux);  'b = state *)

fun re\<^sub>s :: "('r,'v,'s,'a) opbasic \<Rightarrow> ('r,'v,'s,'a) opbasic \<Rightarrow> bool"
  where "re\<^sub>s (\<alpha>,_,_) (\<beta>,_,_) = re\<^sub>a \<alpha> \<beta>"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('r,'v,'s,'a) opbasic \<Rightarrow> ('r,'v,'s,'a) auxop \<Rightarrow> ('r,'v,'s,'a) opbasic" 
  where 
    "fwd\<^sub>s ((\<alpha>,f),v,b) (assign x e,_) = (let p = (subst\<^sub>i \<alpha> x e, f) in  (p,v, beh\<^sub>a p))" |
    "fwd\<^sub>s ((\<alpha>,f),v,b) (leak c e,_) = ((\<alpha>,f),v,beh\<^sub>a (\<alpha>,f))" |
                                    (* (let p = (subst\<^sub>i \<alpha> c e, f) in  (p,v, beh\<^sub>a p))" | *)
    "fwd\<^sub>s ((\<alpha>,f),v,b) (\<beta>,_) = ((\<alpha>,f),v,beh\<^sub>a (\<alpha>,f))"

text \<open>Lift an operation with specification\<close>
definition liftg :: "('r,'v,'s,'a) pred \<Rightarrow> ('r,'v) op \<Rightarrow> ('s,'a) auxfn \<Rightarrow> ('r,'v,'s,'a) opbasic" 
  ("\<lfloor>_,_,_\<rfloor>" 100)
  where "liftg v \<alpha> f \<equiv> ((\<alpha>,f), v, beh\<^sub>a (\<alpha>,f))"

text \<open>Lift an operation without specification\<close>
definition liftl :: "('r,'v) op \<Rightarrow> ('r,'v,'s,'a) opbasic" 
  ("\<lfloor>_\<rfloor>" 100)
  where "liftl \<alpha> \<equiv> ((\<alpha>,aux), UNIV, beh\<^sub>a (\<alpha>,aux))"

section \<open>Language Definition\<close>





end

end
