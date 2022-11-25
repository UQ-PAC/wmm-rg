theory ARMv8
  imports "../State" ARMv8_Exp "../Syntax" 
begin

chapter \<open>ARMv8\<close>

text \<open>Sub-Instruction Reordering\<close>
text \<open>Only pattern match on first argument due to performance issues\<close>
fun re\<^sub>i :: "('v,'r) subop \<Rightarrow> ('v,'r) subop \<Rightarrow> bool" 
  where
    "re\<^sub>i fence \<alpha> = False" |
    "re\<^sub>i stfence \<alpha> = (\<alpha> \<noteq> fence \<and> wr \<alpha> \<subseteq> locals)" |
    "re\<^sub>i cfence \<alpha> = (\<alpha> \<noteq> fence \<and> rd \<alpha> \<subseteq> locals)" |
    "re\<^sub>i (cmp b) \<alpha> = (wr \<alpha> \<subseteq> locals \<and> \<alpha> \<noteq> cfence \<and> \<alpha> \<noteq> fence \<and> rd (cmp b) \<inter> wr \<alpha> = {})" |
  (*  "re\<^sub>i \<alpha> (cacheUpd c x) = False"  | *)
    "re\<^sub>i \<alpha> \<beta> = (\<beta> \<noteq> fence \<and> (\<beta> = stfence \<longrightarrow> wr \<alpha> \<subseteq> locals) \<and> (\<beta> = cfence \<longrightarrow> \<not>(\<exists>b. \<alpha> = cmp b)) \<and>
                (wr \<alpha> \<union> rd \<alpha>) \<inter> rd \<beta> \<subseteq> locals \<and> 
                wr \<alpha> \<inter> wr \<beta> = {} \<and> 
                rd \<alpha> \<inter> wr \<beta> = {})" 

text \<open>Sub-Instruction Forwarding\<close>   (* fwd\<^sub>i \<alpha> \<beta> == forward \<alpha> over \<beta>  == \<alpha>\<^sub><\<^sub>\<beta>\<^sub>> *) 
fun fwd\<^sub>i :: "('v,'r) subop \<Rightarrow> ('v,'r) subop \<Rightarrow> ('v,'r) subop" 
  where
    "fwd\<^sub>i \<alpha> (cstore b g e) = subst\<^sub>g \<alpha> g e" |
    "fwd\<^sub>i \<alpha> (cas\<^sub>T g _ e) = subst\<^sub>g \<alpha> g e" |
    "fwd\<^sub>i \<alpha> (op r e) = subst\<^sub>r \<alpha> r e" |
    "fwd\<^sub>i \<alpha> _ = \<alpha>"

definition comp (infixr "\<Otimes>" 60)   
  where "comp a b \<equiv> {(m,m'). \<exists>m''. (m,m'') \<in> a \<and> (m'',m') \<in> b}"

lemma [simp]:
  "(Reg x \<notin> Reg ` e) = (x \<notin> e)"
  by blast

lemma re_consistent:
  "re\<^sub>i \<alpha> (fwd\<^sub>i \<beta> \<alpha>) \<Longrightarrow> beh\<^sub>i \<alpha> \<Otimes> beh\<^sub>i \<beta> \<supseteq> beh\<^sub>i (fwd\<^sub>i \<beta> \<alpha>) \<Otimes> beh\<^sub>i \<alpha>" sorry
  (*by (cases \<alpha>; cases \<beta>; clarsimp simp add: comp_def fun_upd_twist split: if_splits) *)



section \<open>Auxiliary State Updates\<close>

text \<open>
We wish to support auxiliary state to support more abstract reasoning about data structures
and concurrency.
This is achieved by allowing arbitrary extensions to the state representation, which
can be updated atomically at any sub-operation.
This auxiliary state cannot influence real execution behaviour by definition.
\<close>
(* to be used for ghost/aux variables like \<Gamma> and their updates *) 
(* aux state not affected by reord or forwarding *)
(* when used to capture the Cache, does the Cache state influence the execution behaviour?? *)

type_synonym ('v,'r,'a) auxop = "('v,('v,'r) var) subop \<times> ('v,'r,'a) auxfn"

(* old version
fun beh\<^sub>a :: "('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) state rel"
  where "beh\<^sub>a (\<alpha>,f) = beh\<^sub>i \<alpha> O {(m,m'). m' = m(aux: f)}"
*)

(* like beh\<^sub>i this fun returns a relation over stateTrees! *)

fun beh\<^sub>a :: "('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) stateTree rel"
  where "beh\<^sub>a (\<alpha>,f) = (beh\<^sub>i \<alpha>) O 
                          {(t,t'). t' = tree_upd t (Base ((top t)\<lparr>state_rec.more := f (top t)\<rparr>)) } "


fun re\<^sub>a :: "('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) auxop \<Rightarrow> bool" 
  where "re\<^sub>a (\<alpha>,f) (\<beta>,f') = re\<^sub>i \<alpha> \<beta>"

fun fwd\<^sub>a :: "('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) auxop" 
  where "fwd\<^sub>a (\<alpha>,f) \<beta> = (fwd\<^sub>i \<alpha> (fst \<beta>),f)"

section \<open>Sub-Instruction Specification Language\<close>

text \<open>
To instantiate the abstract theory, we must couple each sub-operation with its precondition/vc
and behaviour in a tuple\<close>
type_synonym ('v,'r,'a) subbasic = "(('v,'r,'a) auxop, ('v,'r,'a) stateTree) basic"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'r,'a) subbasic \<Rightarrow> ('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) subbasic" 
  where "fwd\<^sub>s (\<alpha>,v,_) \<beta> =  (fwd\<^sub>a \<alpha> \<beta>, v, beh\<^sub>a (fwd\<^sub>a \<alpha> \<beta>))" 
(*   where "fwd\<^sub>s (\<alpha>,v,_) \<beta> =  (fwd\<^sub>a \<alpha> \<beta>, wp UNIV (beh\<^sub>a \<beta>) v, beh\<^sub>a (fwd\<^sub>a \<alpha> \<beta>))" 
 *)

text \<open>Lift an operation with vc specification \<close>
(*
definition liftg :: "('v,'r,'a) pred \<Rightarrow> ('v,'r) subop \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) subbasic"
  ("\<lfloor>_,_,_\<rfloor>" 100)
  where "liftg v \<alpha> f \<equiv> ((\<alpha>,f), v, beh\<^sub>a (\<alpha>,f))"
*)
definition liftg :: "('v,'r,'a) predTree \<Rightarrow> ('v,('v,'r) var) subop \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) subbasic"
  ("\<lfloor>_,_,_\<rfloor>" 100)
  where "liftg v \<alpha> f \<equiv> ((\<alpha>,f), v, beh\<^sub>a (\<alpha>,f))"


text \<open>Lift an operation without vc specification\<close>
definition liftl :: "('v,('v,'r) var) subop \<Rightarrow> ('v,'r,'a) subbasic" 
  ("\<lfloor>_\<rfloor>" 100)
  where "liftl \<alpha> \<equiv> ((\<alpha>,aux), UNIV, beh\<^sub>a (\<alpha>,aux))"

section \<open>ARMv8 Language Definition\<close>

text \<open>
We define a basic while language to capture the assembly level instructions
for ARMv8. Notably we do not support general jumps, constraining control flow
significantly.
\<close>
datatype ('v,'r,'a) com_armv8 =
  Skip
  | Fence
  | Load "('v,'r,'a) pred" "'v set" "('v,'r) exp" 'r "('v,'r,'a) auxfn"
  | Store "('v,'r,'a) pred" "'v set" "('v,'r) exp" 'r "('v,'r,'a) auxfn"
  | Op 'r "('v,'r) exp" 
  | CAS "('v,'r,'a) pred" "'v set" 'r 'r 'r 'r 'v 'v "('v,'r,'a) auxfn"
  | Seq "('v,'r,'a) com_armv8" "('v,'r,'a) com_armv8"
  | If "('v,'r) bexp" "('v,'r,'a) com_armv8" "('v,'r,'a) com_armv8"
  | Capture "'v"

end