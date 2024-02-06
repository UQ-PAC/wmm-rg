theory SimAsm
  imports SimAsm_Exp
begin

type_synonym ('s,'a) auxfn = "'s \<Rightarrow> 'a"
type_synonym ('r,'v,'s,'a) auxop = "('r,'v) op \<times> ('s,'a) auxfn"


type_synonym ('r,'v,'s,'a) pred = "'s set"


section \<open>Language Definition\<close>

datatype ('r,'v,'s,'ss,'a) lang =
  Skip
  | Op "'ss set" "('r,'v) op" "('s,'a) auxfn"
  | Seq "('r,'v,'s,'ss,'a) lang" "('r,'v,'s,'ss,'a) lang"
  | If "('r,'v) bexp" "('r,'v,'s,'ss,'a) lang" "('r,'v,'s,'ss,'a) lang"  
  | While "('r,'v) bexp" "'s set" "'ss set" "('r,'v,'s,'ss,'a) lang"
  | DoWhile "'s set" "'ss set" "('r,'v,'s,'ss,'a) lang" "('r,'v) bexp"

fun ops :: "('r,'v,'s,'ss,'a) lang \<Rightarrow> ('r,'v) op set" where 
  "ops Skip = {}" |
  "ops (Op _ op _) = {op}" |
  "ops (Seq a b) = ops a \<union> ops b" | 
  "ops (If _ a b) = ops a \<union> ops b" | 
  "ops (While _ _ _ a) = ops a" |
  "ops (DoWhile _ _ a _) = ops a"

abbreviation wr\<^sub>l where 
  "wr\<^sub>l l \<equiv> \<Union>(wr ` ops l)"

abbreviation lk\<^sub>l where
  "lk\<^sub>l l \<equiv> \<Union>(lk ` ops l)"

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


end

end
