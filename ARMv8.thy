theory ARMv8
  imports Syntax
begin

chapter \<open>ARMv8\<close>

section \<open>State Encoding\<close>

type_synonym ('v,'r,'g) state = "(('g \<Rightarrow> 'v) \<times> ('r \<Rightarrow> 'v))"
type_synonym ('v,'r,'g) pred = "('v,'r,'g) state \<Rightarrow> bool"
type_synonym ('v,'r,'g) rpred = "('v,'r,'g) state \<Rightarrow> ('v,'r,'g) state \<Rightarrow> bool"

subsection \<open>Write Operations\<close>

definition pair_upd1 :: "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd))"
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
  where "rg r m \<equiv> (snd m) r"

abbreviation ld
  where "ld x m \<equiv> (fst m) x"

section \<open>Instruction Language Definition\<close>

text \<open>Capture a simple set of instructions, covering memory operations and fences\<close>
(* TODO: Need support for CAS and other RMW *)
datatype ('v,'r,'g) inst =
    Load 'r 'g
  | Store 'g 'r
  | Op 'r "'v \<Rightarrow> 'v \<Rightarrow> 'v" 'r 'r
  | Cond "'v \<Rightarrow> bool" 'r
  | Fence
  | CFence
  | StFence

text \<open>Shorthand for a negative condition\<close>
abbreviation NCond
  where "NCond f r \<equiv> Cond (\<lambda>v. \<not> f v) r"

text \<open>Instruction Behaviour\<close>
fun beh\<^sub>i :: "('v,'r,'g) inst \<Rightarrow> ('v,'r,'g) state rel"
  where
    "beh\<^sub>i (Store x r) = {(m,m'). m' = m (x :=\<^sub>1 rg r m)}" |
    "beh\<^sub>i (Load r y) = {(m,m'). m' = m (r :=\<^sub>2 ld y m)}" |
    "beh\<^sub>i (Op r\<^sub>t f r\<^sub>1 r\<^sub>2) = {(m,m'). m' = m (r\<^sub>t :=\<^sub>2 f (rg r\<^sub>1 m) (rg r\<^sub>2 m))}" |
    "beh\<^sub>i (Cond f r) = {(m,m'). m = m' \<and> f (rg r m)}" |
    "beh\<^sub>i _ = Id"

subsection \<open>Reordering\<close>

text \<open>Define forwarding as the elimination of loads given a store to the same address\<close>
fun fwd :: "('v,'r,'g) inst \<Rightarrow> ('v,'r,'g) inst \<Rightarrow> ('v,'r,'g) inst" 
  ("_\<langle>_\<rangle>" [1000,0] 1000)
  where 
    "fwd (Load r\<^sub>2 y) (Store x r\<^sub>1) = (if (x = y) then Op r\<^sub>2 (\<lambda>x y. x) r\<^sub>1 r\<^sub>1 else Load r\<^sub>2 y)" |
    "fwd \<alpha> _ = \<alpha>"

text \<open>Define reordering based on Colvin & Smith\<close>
fun re :: "('v,'r,'g) inst \<Rightarrow> ('v,'r,'g) inst \<Rightarrow> bool" 
  (infix "\<hookleftarrow>" 100)
  where
    "re _ Fence = False" |
    "re Fence _ = False" |
    "re (Store _ _) StFence = False" |
    "re StFence (Store _ _) = False" | 
    "re (Cond _ _) CFence = False" |
    "re CFence (Load _ _) = False" |
    "re (Cond _ _) (Store _ _) = False" |
    "re (Cond _ r\<^sub>c) (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) = (r\<^sub>c \<noteq> r\<^sub>t)" |
    "re (Cond _ r\<^sub>c) (Load r\<^sub>t _) = (r\<^sub>c \<noteq> r\<^sub>t)" |
    "re (Store y r\<^sub>s) (Load r\<^sub>t x) = (r\<^sub>s \<noteq> r\<^sub>t \<and> x \<noteq> y)" |
    "re (Store y _) (Store x _) = (x \<noteq> y)" |
    "re (Store _ r\<^sub>s) (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) = (r\<^sub>s \<noteq> r\<^sub>t)" |
    "re (Load r\<^sub>t y) (Load r\<^sub>t' x) = (r\<^sub>t \<noteq> r\<^sub>t' \<and> x \<noteq> y)" |
    "re (Load r\<^sub>t y) (Store x r\<^sub>s) = (r\<^sub>s \<noteq> r\<^sub>t \<and> x \<noteq> y)" |
    "re (Load r\<^sub>t _) (Op r\<^sub>t' _ r\<^sub>1 r\<^sub>2) = (r\<^sub>t \<noteq> r\<^sub>t' \<and> r\<^sub>t \<noteq> r\<^sub>1 \<and> r\<^sub>t \<noteq> r\<^sub>2)" |
    "re (Load r\<^sub>t _) (Cond _ r\<^sub>s) = (r\<^sub>t \<noteq> r\<^sub>s)" |
    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Load r\<^sub>t' _) = (r\<^sub>t' \<noteq> r\<^sub>t \<and> r\<^sub>t' \<noteq> r\<^sub>1 \<and> r\<^sub>t' \<noteq> r\<^sub>2)" |
    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Store _ r\<^sub>s) = (r\<^sub>t \<noteq> r\<^sub>s)" |
    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Op r\<^sub>t' _ r\<^sub>1' r\<^sub>2') = (r\<^sub>t' \<noteq> r\<^sub>t \<and> r\<^sub>t' \<noteq> r\<^sub>1 \<and> r\<^sub>t' \<noteq> r\<^sub>2 \<and> r\<^sub>t \<noteq> r\<^sub>1' \<and> r\<^sub>t \<noteq> r\<^sub>2')" |
    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Cond _ r\<^sub>s) = (r\<^sub>t \<noteq> r\<^sub>s)" |
    "re _ _ = True"

section \<open>Instruction Specification Language Definition\<close>

text \<open>Wrap instructions in more abstract specification to facilitate verification\<close>
type_synonym ('v,'r,'g) ispec = "(('v,'r,'g) pred\<times>('v,'r,'g) inst)"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
(* TODO: We should provide a method to introduce new VCs for forwarded instructions *)
fun fwd\<^sub>s :: "('v,'r,'g) ispec \<Rightarrow> ('v,'r,'g) ispec \<Rightarrow> ('v,'r,'g) ispec" 
  where "fwd\<^sub>s (p,\<alpha>) (_,\<beta>) = (p,fwd \<alpha> \<beta>)" 

fun re\<^sub>s :: "('v,'r,'g) ispec \<Rightarrow> ('v,'r,'g) ispec \<Rightarrow> bool" 
  where "re\<^sub>s (_,\<alpha>) (_,\<beta>) = re \<alpha> \<beta>" 

fun beh\<^sub>s :: "('v,'r,'g) ispec \<Rightarrow> ('v,'r,'g) state rel" 
  where "beh\<^sub>s (p,\<alpha>) = beh\<^sub>i \<alpha>" 

fun vc\<^sub>s :: "('v,'r,'g) ispec \<Rightarrow> ('v,'r,'g) state set" 
  where "vc\<^sub>s (p,\<alpha>) = Collect p" 

text \<open>Common case of a true verification condition\<close>
abbreviation VC\<^sub>T
  where "VC\<^sub>T \<alpha> \<equiv> (\<lambda>m. True,\<alpha>)"

section \<open>While Language Definition\<close>

datatype ('v,'r,'g) lang =
    Skip
  | Inst "('v,'r,'g) ispec"
  | Seq "('v,'r,'g) lang" "('v,'r,'g) lang"
  | If "'v \<Rightarrow> bool" 'r "('v,'r,'g) lang" "('v,'r,'g) lang"
  | While "'v \<Rightarrow> bool" 'r "('v,'r,'g) pred" "('v,'r,'g) lang"

text \<open>Convert the While language into the com language expected by the underlying logic\<close> 
(* TODO: This should be later, closer to the soundness proof *)
fun lift\<^sub>c :: "('v,'r,'g) lang \<Rightarrow> (('v,'r,'g) ispec,('v,'r,'g) state) com"
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Inst \<alpha>) = Basic \<alpha>"|
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) = (com.Seq (lift\<^sub>c c\<^sub>1) (lift\<^sub>c c\<^sub>2))" |
    "lift\<^sub>c (If f r c\<^sub>1 c\<^sub>2) = (Choice (com.Seq (Basic (VC\<^sub>T (Cond f r))) (lift\<^sub>c c\<^sub>1)) 
                                    (com.Seq (Basic (VC\<^sub>T (NCond f r))) (lift\<^sub>c c\<^sub>2)))" |
    "lift\<^sub>c (While f r I c) = (com.Seq ((com.Seq (Basic (VC\<^sub>T (Cond f r))) (lift\<^sub>c c))*) 
                                      (Basic (VC\<^sub>T (NCond f r))))"

end