theory ARMv8
  imports ARMv8_State Syntax
begin

chapter \<open>ARMv8\<close>

section \<open>Sub-Instruction Language Definition\<close>

datatype ('v,'r) exp = Reg 'r | Val 'v | Glb 'v 'v | Exp "'v list \<Rightarrow> 'v" "('v,'r) exp list"

fun ev 
  where 
    "ev m (Reg r) = m r" | 
    "ev _ (Val v) = v" |
    "ev _ (Glb v _) = v" |
    "ev m (Exp f rs) = f (map (ev m) rs)"

fun deps
  where 
    "deps (Reg r) = {r}" |
    "deps (Exp _ rs) = \<Union>(deps ` set rs)" |
    "deps _ = {}"

fun addr
  where
    "addr (Glb _ v) = {v}" |
    "addr (Exp _ rs) = \<Union>(addr ` set rs)" |
    "addr _ = {}"

fun subst
  where
    "subst (Reg r) r' e = (if r = r' then e else Reg r)" |
    "subst (Exp f rs) r e = (Exp f (map (\<lambda>x. subst x r e) rs))" |
    "subst e _ _ = e"

type_synonym ('v,'r,'a) aux = "('v,'r,'a) tstate_scheme \<Rightarrow> 'a"

text \<open>Capture a simple set of sub-instructions, covering memory operations and fences\<close>
datatype ('v,'r,'a) inst =
    load 'v "('v,'r) exp" "('v,'r,'a) aux"
  | store 'v "('v,'r) exp" "('v,'r,'a) aux"
  | cas\<^sub>T 'v "('v,'r) exp" "('v,'r) exp" "('v,'r,'a) aux"
  | cas\<^sub>F 'v "('v,'r) exp" "('v,'r) exp" "('v,'r,'a) aux"
  | op 'r "('v,'r) exp"
  | cmp "('v,'r) exp" "'v \<Rightarrow> 'v \<Rightarrow> bool" "('v,'r) exp"
  | fence
  | cfence
  | stfence
  | nop

text \<open>Sub-Instruction Behaviour\<close>
fun beh\<^sub>i :: "('v,'r,'a) inst \<Rightarrow> ('v,'r,'a) tstate_scheme rel"
  where
    "beh\<^sub>i (store a e f) = {(m,m'). m' = m (a :=\<^sub>s ev (rg m) e)} O {(m,m'). m' = more_update (\<lambda>x. f m) m}" |
    "beh\<^sub>i (load a e f) = {(m,m'). m' = m \<and> st m a = ev (rg m) e} O {(m,m'). m' = more_update (\<lambda>x. f m) m}" |
    "beh\<^sub>i (cas\<^sub>T a e\<^sub>1 e\<^sub>2 f) = {(m,m'). m' = m (a :=\<^sub>s ev (rg m) e\<^sub>2) \<and> st m a = ev (rg m) e\<^sub>1} O {(m,m'). m' = more_update (\<lambda>x. f m) m}" |
    "beh\<^sub>i (cas\<^sub>F a e\<^sub>1 e\<^sub>2 f) = {(m,m'). m' = m \<and> st m a \<noteq> ev (rg m) e\<^sub>1} O {(m,m'). m' = more_update (\<lambda>x. f m) m}" |
    "beh\<^sub>i (op r e) = {(m,m'). m' = m (r :=\<^sub>r ev (rg m) e)}" |
    "beh\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) = {(m,m'). m = m' \<and> f (ev (rg m) e\<^sub>1) (ev (rg m) e\<^sub>2)}" |
    "beh\<^sub>i _ = Id"

fun mems
  where 
    "mems (load y _ _) = {y}" |
    "mems (store y _ _) = {y}" |
    "mems (cas\<^sub>T y _ _ _) = {y}" |
    "mems (cas\<^sub>F y _ _ _) = {y}" |
    "mems _ = {}"

fun wrs
  where 
    "wrs (op r _) = {r}" |
    "wrs _ = {}"

fun rds
  where 
    "rds (op _ e) = deps e" |
    "rds (store _ e _) = deps e" |
    "rds (load _ e _) = deps e" |
    "rds (cas\<^sub>T _ e\<^sub>1 e\<^sub>2 _) = deps e\<^sub>1 \<union> deps e\<^sub>2" |
    "rds (cas\<^sub>F _ e\<^sub>1 e\<^sub>2 _) = deps e\<^sub>1 \<union> deps e\<^sub>2" |
    "rds _ = {}"

fun addrs
  where 
    "addrs (op _ e) = addr e" |
    "addrs (store _ e _) = addr e" |
    "addrs (load _ e _) = addr e" |
    "addrs (cas\<^sub>T _ e\<^sub>1 e\<^sub>2 _) = addr e\<^sub>1 \<union> addr e\<^sub>2" |
    "addrs (cas\<^sub>F _ e\<^sub>1 e\<^sub>2 _) = addr e\<^sub>1 \<union> addr e\<^sub>2" |
    "addrs _ = {}"

text \<open>Sub-Instruction Reordering\<close>
fun re\<^sub>i :: "('v,'r,'a) inst \<Rightarrow> ('v,'r,'a) inst \<Rightarrow> bool" 
  where
    "re\<^sub>i _ fence = False" |
    "re\<^sub>i fence _ = False" |
    "re\<^sub>i (store _ _ _) stfence = False" |
    "re\<^sub>i stfence (store _ _ _) = False" | 
    "re\<^sub>i (cmp _ _ _) cfence = False" |
    "re\<^sub>i cfence (load _ _ _) = False" |
    "re\<^sub>i (cmp _ _ _) (store _ _ _) = False" |
    "re\<^sub>i \<alpha> \<beta> = (mems \<alpha> \<inter> mems \<beta> = {} \<and> mems \<alpha> \<inter> addrs \<beta> = {} \<and> 
                wrs \<alpha> \<inter> wrs \<beta> = {} \<and> rds \<alpha> \<inter> wrs \<beta> = {})"

text \<open>Sub-Instruction Forwarding\<close>
fun fwd\<^sub>i :: "('v,'r,'a) inst \<Rightarrow> ('v,'r,'a) inst \<Rightarrow> ('v,'r,'a) inst" 
  where
    "fwd\<^sub>i (load v\<^sub>a r\<^sub>a f) (store v\<^sub>b r\<^sub>b f') = (if v\<^sub>a = v\<^sub>b then cmp r\<^sub>a (=) r\<^sub>b else load v\<^sub>a r\<^sub>a f)" |
    "fwd\<^sub>i (load v\<^sub>a r\<^sub>a f) (cas\<^sub>T v\<^sub>b _ e\<^sub>2 f') = (if v\<^sub>a = v\<^sub>b then cmp r\<^sub>a (=) e\<^sub>2 else load v\<^sub>a r\<^sub>a f)" |
    "fwd\<^sub>i (store v\<^sub>a e f) (op r e') = (store v\<^sub>a (subst e r e') f)" |
    "fwd\<^sub>i (load v\<^sub>a e f) (op r e') = (load v\<^sub>a (subst e r e') f)" |
    "fwd\<^sub>i (cmp e\<^sub>1 f e\<^sub>2) (op r e) = (cmp (subst e\<^sub>1 r e) f (subst e\<^sub>2 r e))" |
    "fwd\<^sub>i (op r e) (op r' e') = (op r (subst e r' e'))" |
    "fwd\<^sub>i (cas\<^sub>T v\<^sub>a e\<^sub>1 e\<^sub>2 f) (op r e) = (cas\<^sub>T v\<^sub>a (subst e\<^sub>1 r e) (subst e\<^sub>2 r e) f)" |
    "fwd\<^sub>i (cas\<^sub>F v\<^sub>a e\<^sub>1 e\<^sub>2 f) (op r e) = (cas\<^sub>F v\<^sub>a (subst e\<^sub>1 r e) (subst e\<^sub>2 r e) f)" |
    "fwd\<^sub>i \<alpha> _ = \<alpha>"

text \<open>Common Sub-Instructions\<close>

abbreviation eq
  where "eq r v \<equiv> cmp (Reg r) (=) (Val v)"

abbreviation assign
  where "assign r v \<equiv> op r (Exp (\<lambda>x. v) [])"

abbreviation ncmp
  where "ncmp e\<^sub>1 f e\<^sub>2 \<equiv> cmp e\<^sub>1 (\<lambda>x y. \<not> f x y) e\<^sub>2"

section \<open>Sub-Instruction Specification Language\<close>

text \<open>Wrap instructions in more abstract specification to facilitate verification\<close>
type_synonym ('v,'r,'a) ispec = "(('v,'r,'a) inst, ('v,'r,'a) tstate_scheme) basic"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'r,'a) ispec \<Rightarrow> ('v,'r,'a) inst \<Rightarrow> ('v,'r,'a) ispec" 
  where "fwd\<^sub>s (\<alpha>,v,_) \<beta> =  (fwd\<^sub>i \<alpha> \<beta>, v, beh\<^sub>i (fwd\<^sub>i \<alpha> \<beta>))" 

abbreviation no_vc :: "('v,'r,'a) inst \<Rightarrow> ('v,'r,'a) ispec" ("\<lfloor>_\<rfloor>" 100)
  where "no_vc \<alpha> \<equiv> (\<alpha>, UNIV, beh\<^sub>i \<alpha>)"

abbreviation with_vc :: "('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) inst \<Rightarrow> ('v,'r,'a) ispec" ("\<lfloor>_,_\<rfloor>" 100)
  where "with_vc v \<alpha> \<equiv> (\<alpha>, Collect v, beh\<^sub>i \<alpha>)"

section \<open>While Language Definition\<close>
datatype ('v,'r,'a) lang =
  Skip
  | Fence
  | Load "('v,'r,'a) pred" 'r 'r "('v,'r,'a) aux"
  | Store "('v,'r,'a) pred" 'r 'r "('v,'r,'a) aux"
  | Op 'r "('v,'r) exp" 
  | CAS "('v,'r,'a) pred" 'r 'r 'r 'r 'v 'v "('v,'r,'a) aux"
  | Seq "('v,'r,'a) lang" "('v,'r,'a) lang"
  | If "('v,'r) exp" "'v \<Rightarrow> 'v \<Rightarrow> bool" "('v,'r) exp" "('v,'r,'a) lang" "('v,'r,'a) lang"
  | While "('v,'r) exp" "'v \<Rightarrow> 'v \<Rightarrow> bool" "('v,'r) exp" "('v,'r,'a) pred" "('v,'r,'a) lang"
  | DoWhile "('v,'r,'a) pred" "('v,'r,'a) lang" "('v,'r) exp" "'v \<Rightarrow> 'v \<Rightarrow> bool" "('v,'r) exp"
  | Test "('v,'r,'a) pred"
  | Assert "('v,'r,'a) pred"

end