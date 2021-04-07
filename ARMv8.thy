theory ARMv8
  imports Syntax Semantics
begin

chapter \<open>ARMv8\<close>

section \<open>State Encoding\<close>

type_synonym ('v,'r) state = "(('v \<Rightarrow> 'v) \<times> ('r \<Rightarrow> 'v))"
type_synonym ('v,'r) pred  = "('v,'r) state \<Rightarrow> bool"
type_synonym ('v,'r) rpred = "('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> bool"
type_synonym ('v,'r) gpred  = "('v \<Rightarrow> 'v) \<Rightarrow> bool"

named_theorems pred_defs
definition conj  (infixr "\<and>\<^sub>p" 35)
  where "conj l r \<equiv> \<lambda>m. (l m) \<and> (r m)"
definition imp  (infixr "\<longrightarrow>\<^sub>p" 35)
  where "imp l r \<equiv> \<lambda>m. (l m) \<longrightarrow> (r m)"
definition entail (infix "\<turnstile>\<^sub>p" 25)
  where "entail P Q \<equiv> \<forall>m. P m \<longrightarrow> Q m"
definition assert
  where "assert b \<equiv> \<lambda>m. b"
declare assert_def [pred_defs]
declare entail_def [pred_defs]
declare conj_def [pred_defs]
declare imp_def [pred_defs]
definition stabilize 
  where "stabilize R P \<equiv> \<lambda>m. \<forall>m'. R m m' \<longrightarrow> P m'"
definition reflexive 
  where "reflexive R \<equiv> \<forall>m . R m  m"
definition transitive 
  where "transitive R \<equiv> \<forall>m m' m''. R m m' \<longrightarrow> R m' m'' \<longrightarrow> R m m''"
abbreviation PFalse 
  where "PFalse \<equiv> \<lambda>m. False"
abbreviation PTrue 
  where "PTrue \<equiv> \<lambda>m. True"

subsection \<open>Write Operations\<close>

definition pair_upd1 :: "(('v \<Rightarrow> 'v) \<times> ('c \<Rightarrow> 'v)) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> (('v \<Rightarrow> 'v) \<times> ('c \<Rightarrow> 'v))"
  where "pair_upd1 f a b = (\<lambda>x. if x = a then b else (fst f) x, snd f)"

definition pair_upd2 :: "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd))"
  where "pair_upd2 f a b = (fst f, \<lambda>x. if x = a then b else (snd f) x)"

nonterminal updbinds and updbind

syntax
  "_updbind1" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ :=\<^sub>1/ _)")
  "_updbind2" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ :=\<^sub>2/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "f(x:=\<^sub>1y)" \<rightleftharpoons> "CONST pair_upd1 f x y"
  "f(x:=\<^sub>2y)" \<rightleftharpoons> "CONST pair_upd2 f x y"

subsection \<open>Read Operations\<close>

abbreviation rg
  where "rg m r \<equiv> (snd m) r"

abbreviation ld
  where "ld m x \<equiv> (fst m) x"

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

fun addrs
  where
    "addrs (Glb _ v) = {v}" |
    "addrs (Exp _ rs) = \<Union>(addrs ` set rs)" |
    "addrs _ = {}"

fun subst
  where
    "subst (Reg r) r' e = (if r = r' then e else Reg r)" |
    "subst (Exp f rs) r e = (Exp f (map (\<lambda>x. subst x r e) rs))" |
    "subst e _ _ = e"

text \<open>Capture a simple set of sub-instructions, covering memory operations and fences\<close>
datatype ('v,'r) inst =
    load 'v "('v,'r) exp"
  | store 'v "('v,'r) exp"
  | op 'r "('v,'r) exp"
  | test "('v,'r) exp" "'v \<Rightarrow> 'v \<Rightarrow> bool" "('v,'r) exp"
  | fence
  | cfence
  | stfence

text \<open>Sub-Instruction Behaviour\<close>
fun beh\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) state rel"
  where
    "beh\<^sub>i (store addr e) = {(m,m'). m' = m (addr :=\<^sub>1 ev (snd m) e)}" |
    "beh\<^sub>i (load addr e) = {(m,m'). m' = m \<and> ld m addr = ev (snd m) e}" |
    "beh\<^sub>i (op r e) = {(m,m'). m' = m (r :=\<^sub>2 ev (snd m) e)}" |
    "beh\<^sub>i (test e\<^sub>1 f e\<^sub>2) = {(m,m'). m = m' \<and> f (ev (snd m) e\<^sub>1) (ev (snd m) e\<^sub>2)}" |
    "beh\<^sub>i _ = Id"

text \<open>Sub-Instruction Reordering\<close>
fun re\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) inst \<Rightarrow> bool" 
  where
    "re\<^sub>i _ fence = False" |
    "re\<^sub>i fence _ = False" |
    "re\<^sub>i (store _ _) stfence = False" |
    "re\<^sub>i stfence (store _ _) = False" | 
    "re\<^sub>i (test _ _ _) cfence = False" |
    "re\<^sub>i cfence (load _ _) = False" |
    "re\<^sub>i (load y _) (load x e) = (y \<noteq> x \<and> y \<notin> addrs e)" |
    "re\<^sub>i (load y _) (store x e) = (y \<noteq> x \<and> y \<notin> addrs e)" |
    "re\<^sub>i (load y e) (op r e') = (y \<notin> addrs e' \<and> r \<notin> deps e)" |
    "re\<^sub>i (load y _) (test e\<^sub>1 _ e\<^sub>2) = (y \<notin> addrs e\<^sub>1 \<union> addrs e\<^sub>2)" |
    "re\<^sub>i (store x _) (load y _) = (y \<noteq> x)" |
    "re\<^sub>i (store x _) (store y _) = (y \<noteq> x)" |
    "re\<^sub>i (store _ e) (op r _) = (r \<notin> deps e)" |
    "re\<^sub>i (op r e) (op r' e') = (r \<notin> deps e' \<and> r' \<notin> deps e \<and> r \<noteq> r')" |
    "re\<^sub>i (op r _) (test e\<^sub>1 _ e\<^sub>2) = (r \<notin> deps e\<^sub>1 \<and> r \<notin> deps e\<^sub>2)" |
    "re\<^sub>i (op r _) (store _ e) = (r \<notin> deps e)" |
    "re\<^sub>i (op r _) (load v e) = (r \<notin> deps e)" |
    "re\<^sub>i (test _ _ _) (store _ _) = False" |
    "re\<^sub>i (test e\<^sub>1 _ e\<^sub>2) (op r _) = (r \<notin> deps e\<^sub>1 \<and> r \<notin> deps e\<^sub>2)" |
    "re\<^sub>i _ _ = True"

text \<open>Sub-Instruction Forwarding\<close>
fun fwd\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) inst \<Rightarrow> ('v,'r) inst" 
  where
    "fwd\<^sub>i (load v\<^sub>a r\<^sub>a) (store v\<^sub>b r\<^sub>b) = (if v\<^sub>a = v\<^sub>b then test r\<^sub>a (=) r\<^sub>b else load v\<^sub>a r\<^sub>a)" |
    "fwd\<^sub>i (store v\<^sub>a e) (op r e') = (store v\<^sub>a (subst e r e'))" |
    "fwd\<^sub>i (load v\<^sub>a e) (op r e') = (load v\<^sub>a (subst e r e'))" |
    "fwd\<^sub>i (test e\<^sub>1 f e\<^sub>2) (op r e) = (test (subst e\<^sub>1 r e) f (subst e\<^sub>2 r e))" |
    "fwd\<^sub>i (op r e) (op r' e') = (op r (subst e r' e'))" |
    "fwd\<^sub>i \<alpha> _ = \<alpha>"

text \<open>Common Sub-Instructions\<close>

abbreviation eq
  where "eq r v \<equiv> test (Reg r) (=) (Val v)"

abbreviation assign
  where "assign r v \<equiv> op r (Exp (\<lambda>x. v) [])"

abbreviation ntest
  where "ntest e\<^sub>1 f e\<^sub>2 \<equiv> test e\<^sub>1 (\<lambda>x y. \<not> f x y) e\<^sub>2"

section \<open>Sub-Instruction Specification Language\<close>

text \<open>Wrap instructions in more abstract specification to facilitate verification\<close>
type_synonym ('v,'r) ispec = "(('v,'r) inst,('v,'r) state) basic"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) inst \<Rightarrow> ('v,'r) ispec" 
  where "fwd\<^sub>s (\<alpha>,v,_) \<beta> =  (fwd\<^sub>i \<alpha> \<beta>,v,beh\<^sub>i (fwd\<^sub>i \<alpha> \<beta>))" 

abbreviation no_vc :: "('v,'r) inst \<Rightarrow> (('v,'r) inst,('v,'r) state) basic" ("\<lfloor>_\<rfloor>" 100)
  where "no_vc \<alpha> \<equiv> (\<alpha>, UNIV, beh\<^sub>i \<alpha>)"

abbreviation with_vc :: "('v,'r) pred \<Rightarrow> ('v,'r) inst \<Rightarrow> (('v,'r) inst,('v,'r) state) basic" ("\<lfloor>_,_\<rfloor>" 100)
  where "with_vc v \<alpha> \<equiv> (\<alpha>, Collect v, beh\<^sub>i \<alpha>)"

section \<open>While Language Definition\<close>

datatype ('v,'r) lang =
  Skip
  | Load "('v,'r) pred" 'r 'r
  | Store "('v,'r) pred" 'r 'r
  | Op 'r "('v,'r) exp"
  | Seq "('v,'r) lang" "('v,'r) lang"
  | If "('v,'r) exp" "'v \<Rightarrow> 'v \<Rightarrow> bool" "('v,'r) exp" "('v,'r) lang" "('v,'r) lang"
  | While "('v,'r) exp" "'v \<Rightarrow> 'v \<Rightarrow> bool" "('v,'r) exp" "('v,'r) pred" "('v,'r) lang"

end