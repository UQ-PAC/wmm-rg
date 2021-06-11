theory ARMv8
  imports ARMv8_State "../Syntax"
begin

chapter \<open>ARMv8\<close>

section \<open>Local Expression Language\<close>

text \<open>
Simple AST to represent expressions based on registers.
Used to capture register operations and handle the implications of forwarding:
the rewriting of expressions to enable additional reordering behaviours.

Notably we include a tagged constant, the Glb, that represents a constant value that is
dependent on a memory address. 
This is necessary to capture the dependencies within a load operation.
\<close>
datatype ('v,'r) exp = Reg 'r | Val 'v | Glb 'v 'v | Exp "'v list \<Rightarrow> 'v" "('v,'r) exp list"

text \<open>Evaluate an expression given a register state\<close>
fun ev :: "('r \<Rightarrow> 'v) \<Rightarrow> ('v,'r) exp \<Rightarrow> 'v"
  where 
    "ev m (Reg r) = m r" | 
    "ev _ (Val v) = v" |
    "ev _ (Glb v _) = v" |
    "ev m (Exp f rs) = f (map (ev m) rs)"

text \<open>The syntactic register dependencies of an expression\<close>
fun deps :: "('v,'r) exp \<Rightarrow> 'r set"
  where 
    "deps (Reg r) = {r}" |
    "deps (Exp _ rs) = \<Union>(deps ` set rs)" |
    "deps _ = {}"

text \<open>The global dependencies of an expression\<close>
fun glbs :: "('v,'r) exp \<Rightarrow> 'v set"
  where
    "glbs (Glb _ v) = {v}" |
    "glbs (Exp _ rs) = \<Union>(glbs ` set rs)" |
    "glbs _ = {}"

text \<open>Substitute a register for an expression\<close>
fun subst :: "('v,'r) exp \<Rightarrow> 'r \<Rightarrow> ('v,'r) exp \<Rightarrow> ('v,'r) exp"
  where
    "subst (Reg r) r' e = (if r = r' then e else Reg r)" |
    "subst (Exp f rs) r e = (Exp f (map (\<lambda>x. subst x r e) rs))" |
    "subst e _ _ = e"

datatype ('v,'r) bexp = Neg "('v,'r) bexp" | Exp\<^sub>B "'v list \<Rightarrow> bool" "('v,'r) exp list"

text \<open>Evaluate an expression given a register state\<close>
fun ev\<^sub>B :: "('r \<Rightarrow> 'v) \<Rightarrow> ('v,'r) bexp \<Rightarrow> bool"
  where 
    "ev\<^sub>B m (Neg e) = (\<not> (ev\<^sub>B m e))" |
    "ev\<^sub>B m (Exp\<^sub>B f rs) = f (map (ev m) rs)"

text \<open>The syntactic register dependencies of an expression\<close>
fun deps\<^sub>B :: "('v,'r) bexp \<Rightarrow> 'r set"
  where 
    "deps\<^sub>B (Neg e) = deps\<^sub>B e" |
    "deps\<^sub>B (Exp\<^sub>B _ rs) = \<Union>(deps ` set rs)"

text \<open>The global dependencies of an expression\<close>
fun glbs\<^sub>B :: "('v,'r) bexp \<Rightarrow> 'v set"
  where
    "glbs\<^sub>B (Neg e) = glbs\<^sub>B e" |
    "glbs\<^sub>B (Exp\<^sub>B _ rs) = \<Union>(glbs ` set rs)"

text \<open>Substitute a register for an expression\<close>
fun subst\<^sub>B :: "('v,'r) bexp \<Rightarrow> 'r \<Rightarrow> ('v,'r) exp \<Rightarrow> ('v,'r) bexp"
  where
    "subst\<^sub>B (Neg b) r e = Neg (subst\<^sub>B b r e)" |
    "subst\<^sub>B (Exp\<^sub>B f rs) r e = (Exp\<^sub>B f (map (\<lambda>x. subst x r e) rs))"

section \<open>Sub-operations\<close>

text \<open>
To model the possible reordering behaviour seen in ARMv8, it is necessary
to model each operation as a series of sub-operations.
For example a load would consist of an operation that first determines the memory address
to access, followed by the memory access, followed by a store to a register.
\<close>
datatype ('v,'r) subop =
    load 'v "('v,'r) exp"
  | store 'v "('v,'r) exp"
  | cas\<^sub>T 'v "('v,'r) exp" "('v,'r) exp"
  | cas\<^sub>F 'v "('v,'r) exp" "('v,'r) exp"
  | op 'r "('v,'r) exp"
  | cmp "('v,'r) bexp"
  | fence
  | cfence
  | stfence
  | nop

text \<open>Common Sub-Instructions\<close>
abbreviation assign
  where "assign r v \<equiv> op r (Exp (\<lambda>x. v) [])"

abbreviation ncmp
  where "ncmp b \<equiv> cmp (Neg b)"

abbreviation eq
  where "eq e\<^sub>1 e\<^sub>2 \<equiv> cmp (Exp\<^sub>B (\<lambda>x. x ! 0 = x ! 1) [e\<^sub>1,e\<^sub>2])"

text \<open>Sub-operation execution behaviour\<close>
fun beh\<^sub>i :: "('v,'r) subop \<Rightarrow> ('v,'r,'a) tstate rel"
  where
    "beh\<^sub>i (store a e) = {(m,m'). m' = m (a :=\<^sub>s ev (rg m) e)}" |
    "beh\<^sub>i (load a e) = {(m,m'). m' = m \<and> st m a = ev (rg m) e}" |
    "beh\<^sub>i (cas\<^sub>T a e\<^sub>1 e\<^sub>2) = {(m,m'). m' = m (a :=\<^sub>s ev (rg m) e\<^sub>2) \<and> st m a = ev (rg m) e\<^sub>1}" |
    "beh\<^sub>i (cas\<^sub>F a e\<^sub>1 e\<^sub>2) = {(m,m'). m' = m \<and> st m a \<noteq> ev (rg m) e\<^sub>1}" |
    "beh\<^sub>i (op r e) = {(m,m'). m' = m (r :=\<^sub>r ev (rg m) e)}" |
    "beh\<^sub>i (cmp b) = {(m,m'). m = m' \<and> ev\<^sub>B (rg m) b}" |
    "beh\<^sub>i _ = Id"

text \<open>Memory addresses written by a sub-operation\<close>
fun wr\<^sub>s :: "('v,'r) subop \<Rightarrow> 'v set"
  where 
    "wr\<^sub>s (store y _) = {y}" |
    "wr\<^sub>s (cas\<^sub>T y _ _) = {y}" |
    "wr\<^sub>s _ = {}"

text \<open>Memory addresses reads by a sub-operation\<close>
fun rd\<^sub>s :: "('v,'r) subop \<Rightarrow> 'v set"
  where 
    "rd\<^sub>s (load y _) = {y}" |
    "rd\<^sub>s (cas\<^sub>T y _ _) = {y}" |
    "rd\<^sub>s (cas\<^sub>F y _ _) = {y}" |
    "rd\<^sub>s _ = {}"

text \<open>Memory addresses accessed by a sub-operation\<close>
abbreviation mems
  where "mems \<alpha> \<equiv> rd\<^sub>s \<alpha> \<union> wr\<^sub>s \<alpha>"

text \<open>Registers written by a sub-operation\<close>
fun wr\<^sub>r :: "('v,'r) subop \<Rightarrow> 'r set"
  where 
    "wr\<^sub>r (op r _) = {r}" |
    "wr\<^sub>r _ = {}"

text \<open>Registers read by a sub-operation\<close>
fun rd\<^sub>r :: "('v,'r) subop \<Rightarrow> 'r set"
  where
    "rd\<^sub>r (op _ e) = deps e" |
    "rd\<^sub>r (store _ e) = deps e" |
    "rd\<^sub>r (load _ e) = deps e" |
    "rd\<^sub>r (cas\<^sub>T _ e\<^sub>1 e\<^sub>2) = deps e\<^sub>1 \<union> deps e\<^sub>2" |
    "rd\<^sub>r (cas\<^sub>F _ e\<^sub>1 e\<^sub>2) = deps e\<^sub>1 \<union> deps e\<^sub>2" |
    "rd\<^sub>r (cmp b) = deps\<^sub>B b" |
    "rd\<^sub>r _ = {}"

text \<open>Tagged memory addresses an expression is dependent on\<close>
fun tags :: "('v,'r) subop \<Rightarrow> 'v set"
  where 
    "tags (op _ e) = glbs e" |
    "tags (store _ e) = glbs e" |
    "tags (load _ e) = glbs e" |
    "tags (cas\<^sub>T _ e\<^sub>1 e\<^sub>2) = glbs e\<^sub>1 \<union> glbs e\<^sub>2" |
    "tags (cas\<^sub>F _ e\<^sub>1 e\<^sub>2) = glbs e\<^sub>1 \<union> glbs e\<^sub>2" |
    "tags (cmp b) = glbs\<^sub>B b" |
    "tags _ = {}"

text \<open>Sub-Instruction Reordering\<close>
text \<open>Only pattern match on first argument due to performance issues\<close>
fun re\<^sub>i :: "('v,'r) subop \<Rightarrow> ('v,'r) subop \<Rightarrow> bool" 
  where
    "re\<^sub>i fence \<alpha> = False" |
    "re\<^sub>i stfence \<alpha> = (wr\<^sub>s \<alpha> = {})" |
    "re\<^sub>i (cmp b) \<alpha> = (wr\<^sub>s \<alpha> = {} \<and> \<alpha> \<noteq> cfence  \<and> rd\<^sub>r (cmp b) \<inter> wr\<^sub>r \<alpha> = {})" |
    "re\<^sub>i cfence \<alpha> = (rd\<^sub>s \<alpha> = {})" |
    "re\<^sub>i \<alpha> \<beta> = (\<alpha> \<noteq> fence \<and>
                (\<alpha> = stfence \<longrightarrow> wr\<^sub>s \<beta> = {}) \<and>
                mems \<alpha> \<inter> mems \<beta> = {} \<and> 
                mems \<alpha> \<inter> tags \<beta> = {} \<and> 
                wr\<^sub>r \<alpha> \<inter> wr\<^sub>r \<beta> = {} \<and> 
                rd\<^sub>r \<alpha> \<inter> wr\<^sub>r \<beta> = {})"
  
text \<open>Sub-Instruction Forwarding\<close>
fun fwd\<^sub>i :: "('v,'r) subop \<Rightarrow> ('v,'r) subop \<Rightarrow> ('v,'r) subop" 
  where
    "fwd\<^sub>i (load v\<^sub>a r\<^sub>a) (store v\<^sub>b r\<^sub>b) = (if v\<^sub>a = v\<^sub>b then eq r\<^sub>a r\<^sub>b else load v\<^sub>a r\<^sub>a)" |
    "fwd\<^sub>i (load v\<^sub>a r\<^sub>a) (cas\<^sub>T v\<^sub>b _ e\<^sub>2) = (if v\<^sub>a = v\<^sub>b then eq r\<^sub>a e\<^sub>2 else load v\<^sub>a r\<^sub>a)" |
    "fwd\<^sub>i (store v\<^sub>a e) (op r e') = (store v\<^sub>a (subst e r e'))" |
    "fwd\<^sub>i (load v\<^sub>a e) (op r e') = (load v\<^sub>a (subst e r e'))" |
    "fwd\<^sub>i (cmp b) (op r e) = (cmp (subst\<^sub>B b r e))" |
    "fwd\<^sub>i (op r e) (op r' e') = (op r (subst e r' e'))" |
    "fwd\<^sub>i (cas\<^sub>T v\<^sub>a e\<^sub>1 e\<^sub>2) (op r e) = (cas\<^sub>T v\<^sub>a (subst e\<^sub>1 r e) (subst e\<^sub>2 r e))" |
    "fwd\<^sub>i (cas\<^sub>F v\<^sub>a e\<^sub>1 e\<^sub>2) (op r e) = (cas\<^sub>F v\<^sub>a (subst e\<^sub>1 r e) (subst e\<^sub>2 r e))" |
    "fwd\<^sub>i \<alpha> _ = \<alpha>"

lemma [simp]:
  "ev m (subst e r f) = ev (m(r := (ev m f))) e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev m \<circ> (\<lambda>x. subst x r f)) rs = map (ev (\<lambda>a. if a = r then ev m f else m a)) rs"
    by auto
  show ?case by simp
qed auto

lemma [simp]:
  "ev\<^sub>B m (subst\<^sub>B b r e) = ev\<^sub>B (m(r := (ev m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (ev m \<circ> (\<lambda>x. subst x r e)) rs = map (ev (\<lambda>a. if a = r then ev m e else m a)) rs"
    by (auto simp: fun_upd_def)     
  show ?case by simp
qed simp

lemma ev_nop [simp]:
  "r \<notin> deps e \<Longrightarrow> ev (m(r := f)) e = ev m e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev (\<lambda>a. if a = r then f else m a)) rs = (map (ev m) rs)" by auto
  show ?case by simp
qed auto

lemma ev\<^sub>B_nop [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> ev\<^sub>B (m(r := f)) b = ev\<^sub>B m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev (\<lambda>a. if a = r then f else m a)) rs = map (ev m) rs"
    using ev_nop[of r _ m f] by (auto simp: fun_upd_def) 
  show ?case by simp
qed simp

definition comp (infix "\<Otimes>" 60)
  where "comp a b \<equiv> {(m,m'). \<exists>m''. (m,m'') \<in> a \<and> (m'',m') \<in> b}"

lemma re_consistent:
  "re\<^sub>i \<alpha> (fwd\<^sub>i \<beta> \<alpha>) \<Longrightarrow> beh\<^sub>i \<alpha> \<Otimes> beh\<^sub>i \<beta> \<supseteq> beh\<^sub>i (fwd\<^sub>i \<beta> \<alpha>) \<Otimes> beh\<^sub>i \<alpha>" 
  by (cases \<alpha>; cases \<beta>; auto simp add: comp_def st_upd_def rg_upd_def intro!: fun_upd_twist equality)
 
section \<open>Auxiliary State Updates\<close>

text \<open>
We wish to support auxiliary state to support more abstract reasoning about data structures
and concurrency.
This is achieved by allowing arbitrary extensions to the state representation, which
can be updated atomically at any sub-operation.
This auxiliary state cannot influence real execution behaviour by definition.
\<close>
type_synonym ('v,'r,'a) auxop = "('v,'r) subop \<times> ('v,'r,'a) auxfn"

fun beh\<^sub>a :: "('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) tstate rel"
  where "beh\<^sub>a (\<alpha>,f) = beh\<^sub>i \<alpha> O {(m,m'). m' = m(aux: f)}"

fun re\<^sub>a :: "('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) auxop \<Rightarrow> bool" 
  where "re\<^sub>a (\<alpha>,f) (\<beta>,f') = re\<^sub>i \<alpha> \<beta>"

fun fwd\<^sub>a :: "('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) auxop" 
  where "fwd\<^sub>a (\<alpha>,f) (\<beta>,f') = (fwd\<^sub>i \<alpha> \<beta>,f)"

section \<open>Sub-Instruction Specification Language\<close>

text \<open>
To instantiate the abstract theory, we must couple each sub-operation with its precondition
and behaviour in a tuple\<close>
type_synonym ('v,'r,'a) subbasic = "(('v,'r,'a) auxop, ('v,'r,'a) tstate) basic"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'r,'a) subbasic \<Rightarrow> ('v,'r,'a) auxop \<Rightarrow> ('v,'r,'a) subbasic" 
  where "fwd\<^sub>s (\<alpha>,v,_) \<beta> =  (fwd\<^sub>a \<alpha> \<beta>, v, beh\<^sub>a (fwd\<^sub>a \<alpha> \<beta>))" 

text \<open>Lift an operation with specification\<close>
definition liftg :: "('v,'r,'a) pred \<Rightarrow> ('v,'r) subop \<Rightarrow> ('v,'r,'a) auxfn \<Rightarrow> ('v,'r,'a) subbasic" 
  ("\<lfloor>_,_,_\<rfloor>" 100)
  where "liftg v \<alpha> f \<equiv> ((\<alpha>,f), Collect v, beh\<^sub>a (\<alpha>,f))"

text \<open>Lift an operation without specification\<close>
definition liftl :: "('v,'r) subop \<Rightarrow> ('v,'r,'a) subbasic" 
  ("\<lfloor>_\<rfloor>" 100)
  where "liftl \<alpha> \<equiv> ((\<alpha>,tstate_rec.more), UNIV, beh\<^sub>a (\<alpha>,tstate_rec.more))"

section \<open>ARMv8 Language Definition\<close>

text \<open>
We define a basic while language to capture the assembly level instructions
for ARMv8. Notably we do not support general jumps, constraining control flow
significantly.
\<close>
datatype ('v,'r,'a) com_armv8 =
  Skip
  | Fence
  | Load "('v,'r,'a) pred" "('v,'r) exp" 'r "('v,'r,'a) auxfn"
  | Store "('v,'r,'a) pred" "('v,'r) exp" 'r "('v,'r,'a) auxfn"
  | Op 'r "('v,'r) exp" 
  | CAS "('v,'r,'a) pred" 'r 'r 'r 'r 'v 'v "('v,'r,'a) auxfn"
  | Seq "('v,'r,'a) com_armv8" "('v,'r,'a) com_armv8"
  | If "('v,'r) bexp" "('v,'r,'a) com_armv8" "('v,'r,'a) com_armv8"
  | While "('v,'r) bexp" "('v,'r,'a) pred" "('v,'r,'a) com_armv8"
  | DoWhile "('v,'r,'a) pred" "('v,'r,'a) com_armv8" "('v,'r) bexp"
  | Test "('v,'r,'a) pred"
  | Assert "('v,'r,'a) pred"

end