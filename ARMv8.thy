theory ARMv82
  imports Syntax Semantics
begin

chapter \<open>ARMv8\<close>

section \<open>State Encoding\<close>

type_synonym ('v,'r) state = "(('v \<Rightarrow> 'v) \<times> ('r \<Rightarrow> 'v))"
type_synonym ('v,'r) pred  = "('v,'r) state \<Rightarrow> bool"
type_synonym ('v,'r) rpred = "('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> bool"

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

text \<open>Capture a simple set of sub-instructions, covering memory operations and fences\<close>
datatype ('v,'r) inst =
    load 'v 'v
  | store 'v 'r
  | cas 'v 'v 'v
  | op 'r "'v list \<Rightarrow> 'v" "'r list"
  | test "'v list \<Rightarrow> bool" "'r list"
  | fence
  | cfence
  | stfence

text \<open>Sub-Instruction Behaviour\<close>
fun beh\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) state rel"
  where
    "beh\<^sub>i (store addr r) = {(m,m'). m' = m (addr :=\<^sub>1 rg m r)}" |
    "beh\<^sub>i (load addr val) = {(m,m'). m' = m \<and> ld m addr = val}" |
    "beh\<^sub>i (cas addr tst val) = {(m,m'). (m' = m \<and> ld m addr \<noteq> tst) \<or> (m' = m (addr :=\<^sub>1 val) \<and> ld m addr = tst)}" |
    "beh\<^sub>i (op r f rs) = {(m,m'). m' = m (r :=\<^sub>2 f (map (rg m) rs))}" |
    "beh\<^sub>i (test f rs) = {(m,m'). m = m' \<and> f (map (rg m) rs)}" |
    "beh\<^sub>i _ = Id"

text \<open>Sub-Instruction Reordering\<close>
fun re\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) inst \<Rightarrow> bool" 
  where
    "re\<^sub>i _ fence = False" |
    "re\<^sub>i fence _ = False" |
    "re\<^sub>i (store _ _) stfence = False" |
    "re\<^sub>i stfence (store _ _) = False" | 
    "re\<^sub>i (test _ _) cfence = False" |
    "re\<^sub>i cfence (load _ _) = False" |
    "re\<^sub>i (load y _) (load x _) = (y \<noteq> x)" |
    "re\<^sub>i (load y _) (store x _) = (y \<noteq> x)" |
    "re\<^sub>i (store x _) (load y _) = (y \<noteq> x)" |
    "re\<^sub>i (store x _) (store y _) = (y \<noteq> x)" |
    "re\<^sub>i (store _ r) (op r' _ _) = (r \<noteq> r')" |
    "re\<^sub>i (op r _ rs) (op r' _ rs') = (r \<notin> set rs' \<and> r' \<notin> set rs \<and> r \<noteq> r')" |
    "re\<^sub>i (op r _ _) (test _ rs') = (r \<notin> set rs')" |
    "re\<^sub>i (op r _ _) (store _ r') = (r \<noteq> r')" |
    "re\<^sub>i (test _ _) (store _ _) = False" |
    "re\<^sub>i (test _ rs) (op r _ _) = (r \<notin> set rs)" |
    "re\<^sub>i _ _ = True"

text \<open>Sub-Instruction Forwarding\<close>
fun fwd\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) inst \<Rightarrow> ('v,'r) inst" 
  where
    "fwd\<^sub>i (load v\<^sub>a v) (store v\<^sub>a' r) = (if v\<^sub>a = v\<^sub>a' then test (\<lambda>x. x ! 0 = v) [r] else load v\<^sub>a v)" |
    "fwd\<^sub>i \<alpha> _ = \<alpha>"

text \<open>Common Sub-Instructions\<close>
abbreviation eq
  where "eq r v \<equiv> test (\<lambda>x. x ! 0 = v) [r]"

abbreviation assign
  where "assign r v \<equiv> op r (\<lambda>x. v) []"

abbreviation ntest
  where "ntest f rs \<equiv> test (\<lambda>x. \<not> f x) rs"

section \<open>Sub-Instruction Specification Language\<close>

text \<open>Wrap instructions in more abstract specification to facilitate verification\<close>
type_synonym ('v,'r) ispec = "(('v,'r) pred \<times> ('v,'r) inst)"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) ispec \<Rightarrow> ('v,'r) ispec" 
  where "fwd\<^sub>s (vc,\<alpha>) (_,\<beta>) =  (vc,fwd\<^sub>i \<alpha> \<beta>)" 

fun beh\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) state rel" 
  where "beh\<^sub>s (_,\<alpha>) = beh\<^sub>i \<alpha>" 

fun vc\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) state set" 
  where "vc\<^sub>s (p,\<alpha>) = Collect p" 

abbreviation no_vc ("\<lfloor>_\<rfloor>" 100)
  where "no_vc \<alpha> \<equiv> (\<lambda>x. True, \<alpha>)"

abbreviation yes_vc ("\<lfloor>_,_\<rfloor>" 100)
  where "yes_vc v \<alpha> \<equiv> (v, \<alpha>)"

section \<open>While Language Definition\<close>

datatype ('v,'r) lang =
  Skip
  | Load "('v,'r) pred" 'r 'r
  | Store "('v,'r) pred" 'r 'r
  | Op 'r "'v list \<Rightarrow> 'v" "'r list"
  | Seq "('v,'r) lang" "('v,'r) lang"
  | If "'v list \<Rightarrow> bool" "'r list" "('v,'r) lang" "('v,'r) lang"
  | While "'v list \<Rightarrow> bool" "'r list" "('v,'r) pred" "('v,'r) lang"

end