theory ARMv8
  imports Syntax
begin

chapter \<open>ARMv8\<close>

section \<open>State Encoding\<close>

type_synonym ('v,'r) state = "(('v \<Rightarrow> 'v) \<times> ('r \<Rightarrow> 'v))"
type_synonym ('v,'r) pred = "('v,'r) state \<Rightarrow> bool"
type_synonym ('v,'r) rpred = "('v,'r) state \<Rightarrow> ('v,'r) state \<Rightarrow> bool"

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

definition pair_upd1 :: "(('v \<Rightarrow> 'v) \<times> ('c \<Rightarrow> 'v)) \<Rightarrow> 'c \<Rightarrow> 'v \<Rightarrow> (('v \<Rightarrow> 'v) \<times> ('c \<Rightarrow> 'v))"
  where "pair_upd1 f a b = (\<lambda>x. if x = snd f a then b else (fst f) x, snd f)"

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
  where "ld x m \<equiv> (fst m) (snd m x)"

section \<open>Instruction Language Definition\<close>

text \<open>Capture a simple set of instructions, covering memory operations and fences\<close>
(* TODO: Need support for CAS and other RMW *)
datatype ('v,'r) inst =
    Load1 'r 'v
  | Load2 'r 'r 'v
  | Store 'r 'r
  | Op 'r "'v \<Rightarrow> 'v \<Rightarrow> 'v" 'r 'r
  | Cond "'v \<Rightarrow> bool" 'r
  | Fence
  | CFence
  | StFence

text \<open>Shorthand for a negative condition\<close>
abbreviation NCond
  where "NCond f r \<equiv> Cond (\<lambda>v. \<not> f v) r"

text \<open>Instruction Behaviour\<close>
fun beh\<^sub>i :: "('v,'r) inst \<Rightarrow> ('v,'r) state rel"
  where
    "beh\<^sub>i (Store x r) = {(m,m'). m' = m (x :=\<^sub>1 rg r m)}" |
    "beh\<^sub>i (Load1 y v) = {(m,m'). m' = m  \<and> v = ld y m}" |
    "beh\<^sub>i (Load2 r y v) = {(m,m'). m' = m (r :=\<^sub>2 v)}" |
    "beh\<^sub>i (Op r\<^sub>t f r\<^sub>1 r\<^sub>2) = {(m,m'). m' = m (r\<^sub>t :=\<^sub>2 f (rg r\<^sub>1 m) (rg r\<^sub>2 m))}" |
    "beh\<^sub>i (Cond f r) = {(m,m'). m = m' \<and> f (rg r m)}" |
    "beh\<^sub>i _ = Id"

subsection \<open>Reordering\<close>

(*
text \<open>Define forwarding as the elimination of loads given a store to the same address\<close>
fun fwd :: "('v,'r) inst \<Rightarrow> ('v,'r) inst \<Rightarrow> ('v,'r) inst" 
  ("_\<langle>_\<rangle>" [1000,0] 1000)
  where 
    "fwd (Load r\<^sub>2 y) (Store x r\<^sub>1) = (if (x = y) then Op r\<^sub>2 (\<lambda>x y. x) r\<^sub>1 r\<^sub>1 else Load r\<^sub>2 y)" |
    "fwd \<alpha> _ = \<alpha>" *)

fun reads
  where
    "reads (Store x r) = {x,r}" |
    "reads (Load1 y v) = {y}" |
    "reads (Load2 r y v) = {r,y}" |
    "reads (Op _ _ r\<^sub>1 r\<^sub>2) = {r\<^sub>1,r\<^sub>2}" |
    "reads (Cond _ r) = {r}" |
    "reads _ = {}"

fun writes
  where
    "writes (Op r _ _ _) = {r}" |
    "writes (Load2 r _ _) = {r}" |
    "writes _ = {}"

fun addrs
  where
    "addrs (Store x _) = {x}" |
    "addrs (Load1 y _) = {y}" |
    "addrs _ = {}"

fun re :: "('v,'r) inst \<Rightarrow> ('v,'r) inst \<Rightarrow> bool" 
  where
    "re _ Fence = False" |
    "re Fence _ = False" |
    "re (Store _ _) StFence = False" |
    "re StFence (Store _ _) = False" | 
    "re (Cond _ _) CFence = False" |
    "re CFence (Load1 _ _) = False" |

    "re (Cond _ _) (Store _ _) = False" |
    "re (Cond _ r\<^sub>c) (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) = (r\<^sub>c \<noteq> r\<^sub>t)" |
    "re (Cond _ r\<^sub>c) (Load2 r\<^sub>t _ _) = (r\<^sub>c \<noteq> r\<^sub>t)" |

    "re (Store x r\<^sub>s) (Load2 r\<^sub>t _ _) = (r\<^sub>s \<noteq> r\<^sub>t \<and> x \<noteq> r\<^sub>t)" |
    "re (Store x r\<^sub>s) (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) = (r\<^sub>s \<noteq> r\<^sub>t \<and> x \<noteq> r\<^sub>t)" |

    "re (Load1 y _) (Load2 r\<^sub>t x _) = (y \<noteq> x \<and> r\<^sub>t \<noteq> y)" |
    "re (Load1 y _) (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) = (y \<noteq> r\<^sub>t)" |

    "re (Load2 r\<^sub>t x _) (Load1 y _) = (y \<noteq> x \<and> r\<^sub>t \<noteq> y)" |
    "re (Load2 r\<^sub>t y _) (Load2 r\<^sub>t' x _) = (r\<^sub>t \<noteq> r\<^sub>t' \<and> r\<^sub>t \<noteq> x \<and> r\<^sub>t' \<noteq> y)" |
    "re (Load2 r\<^sub>t _ _) (Store x r\<^sub>s) = (r\<^sub>s \<noteq> r\<^sub>t \<and> x \<noteq> r\<^sub>t)" |
    "re (Load2 r\<^sub>t y _) (Op r\<^sub>t' _ r\<^sub>1 r\<^sub>2) = (r\<^sub>t \<noteq> r\<^sub>t' \<and> r\<^sub>t' \<noteq> y \<and> r\<^sub>t \<noteq> r\<^sub>1 \<and> r\<^sub>t \<noteq> r\<^sub>2)" |
    "re (Load2 r\<^sub>t _ _) (Cond _ r\<^sub>s) = (r\<^sub>t \<noteq> r\<^sub>s)" |

    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Load1 y _) = (y \<noteq> r\<^sub>t)" |
    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Load2 r\<^sub>t' y _) = (r\<^sub>t' \<noteq> r\<^sub>t \<and> r\<^sub>t' \<noteq> r\<^sub>1 \<and> r\<^sub>t' \<noteq> r\<^sub>2 \<and> r\<^sub>t \<noteq> y)" |

    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Store x r\<^sub>s) = (r\<^sub>t \<noteq> r\<^sub>s \<and> r\<^sub>t \<noteq> x)" |
    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Op r\<^sub>t' _ r\<^sub>1' r\<^sub>2') = (r\<^sub>t' \<noteq> r\<^sub>t \<and> r\<^sub>t' \<noteq> r\<^sub>1 \<and> r\<^sub>t' \<noteq> r\<^sub>2 \<and> r\<^sub>t \<noteq> r\<^sub>1' \<and> r\<^sub>t \<noteq> r\<^sub>2')" |
    "re (Op r\<^sub>t _ r\<^sub>1 r\<^sub>2) (Cond _ r\<^sub>s) = (r\<^sub>t \<noteq> r\<^sub>s)" |

    "re _ _ = True"

lemma
  "re \<alpha> \<beta> \<Longrightarrow> writes \<alpha> \<inter> writes \<beta> = {}"
  by (cases \<alpha>; cases \<beta>; auto)

lemma
  "re \<alpha> \<beta> \<Longrightarrow> writes \<alpha> \<inter> reads \<beta> = {}"
  by (cases \<alpha>; cases \<beta>; auto)

lemma
  "re \<alpha> \<beta> \<Longrightarrow> reads \<alpha> \<inter> writes \<beta> = {}"
  by (cases \<alpha>; cases \<beta>; auto)



text \<open>Define reordering based on Colvin & Smith\<close>
fun re_m :: "('v,'r) inst \<Rightarrow> ('v,'r) inst \<Rightarrow> ('v,'r) pred" 
  where
    "re_m (Store y _) (Load1 x _) = (\<lambda>m. rg x m \<noteq> rg y m)" |
    "re_m (Store y _) (Store x _) = (\<lambda>m. rg x m \<noteq> rg y m)" |
    "re_m (Load1 y _) (Store x _) = (\<lambda>m. rg x m \<noteq> rg y m)" |
    "re_m _ _ = PTrue"

section \<open>Instruction Specification Language Definition\<close>

text \<open>Wrap instructions in more abstract specification to facilitate verification\<close>
type_synonym ('v,'r) ispec = "(('v,'r) pred \<times> ('v,'r) pred \<times> ('v,'r) inst)"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) ispec \<Rightarrow> ('v,'r) ispec" 
  where 
    "fwd\<^sub>s (vc,ts,\<alpha>) (_,_,\<beta>) = (if re \<beta> \<alpha> then (vc,ts \<and>\<^sub>p re_m \<beta> \<alpha>,\<alpha>) else (vc,PFalse,\<alpha>))" 

fun beh\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) state rel" 
  where "beh\<^sub>s (_,ts,\<alpha>) = {(m,m'). (m,m') \<in> beh\<^sub>i \<alpha>}" 

fun vc\<^sub>s :: "('v,'r) ispec \<Rightarrow> ('v,'r) state set" 
  where "vc\<^sub>s (p,ts,\<alpha>) = {m. ts m \<longrightarrow> p m}" 

(* does ts\<^sub>\<alpha> depend on writes in \<beta>? *)

definition comp (infixr "\<otimes>" 60)
  where "comp a b \<equiv> {((g,l),(g',l')). (\<exists>g'' l'' . ((g,l),(g'',l'')) \<in> a \<and> ((g'',l''),(g',l')) \<in> b)}"

lemma
  "re (snd (snd \<alpha>))  (snd (snd \<beta>)) \<Longrightarrow> beh\<^sub>s \<alpha> \<otimes> beh\<^sub>s \<beta> \<supseteq> {((g,l),(g',l')). (re_m (snd (snd \<alpha>))  (snd (snd \<beta>))) (g,l) \<and> g = g' \<and> l = l' } \<otimes> beh\<^sub>s (fwd\<^sub>s \<beta> \<alpha>) \<otimes> beh\<^sub>s \<alpha>"
  apply (cases \<alpha>; cases \<beta>)
  apply (case_tac c; case_tac ca)
  by (auto simp: pred_defs pair_upd1_def pair_upd2_def comp_def split: if_splits)


(*
  apply (rename_tac vc\<^sub>\<alpha> ts\<^sub>\<alpha> a vc\<^sub>\<beta> ts\<^sub>\<beta> b x v r\<^sub>2 y v')
  apply (auto simp: pred_defs comp_def pair_upd2_def)[1]
  defer 1
  apply (auto simp: pred_defs comp_def pair_upd1_def pair_upd2_def)[1]
  defer 1
  apply (auto simp: pred_defs comp_def pair_upd1_def pair_upd2_def)[1]
  defer 1
  apply (auto simp: pred_defs comp_def pair_upd1_def pair_upd2_def)[1]
  apply (auto simp: pred_defs comp_def pair_upd1_def pair_upd2_def)[1]
  apply (auto simp: pred_defs comp_def pair_upd1_def pair_upd2_def)[1]
  apply (auto simp: pred_defs comp_def pair_upd1_def pair_upd2_def)[1]
  apply (auto simp: pred_defs comp_def pair_upd1_def pair_upd2_def)[1]
*)



text \<open>Common case of a true verification condition\<close>
abbreviation VC\<^sub>T
  where "VC\<^sub>T \<alpha> \<equiv> (PTrue,PTrue,\<alpha>)"

section \<open>While Language Definition\<close>

datatype ('v,'r) lang =
    Skip
  | Inst "('v,'r) ispec"
  | Seq "('v,'r) lang" "('v,'r) lang"
  | If "'v \<Rightarrow> bool" 'r "('v,'r) lang" "('v,'r) lang"
  | While "'v \<Rightarrow> bool" 'r "('v,'r) pred" "('v,'r) lang"

text \<open>Convert the While language into the com language expected by the underlying logic\<close> 
(* TODO: This should be later, closer to the soundness proof *)
fun lift\<^sub>c :: "('v,'r) lang \<Rightarrow> (('v,'r) ispec,('v,'r) state) com"
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Inst \<alpha>) = Basic \<alpha>"|
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) = (com.Seq (lift\<^sub>c c\<^sub>1) (lift\<^sub>c c\<^sub>2))" |
    "lift\<^sub>c (If f r c\<^sub>1 c\<^sub>2) = (Choice (com.Seq (Basic (VC\<^sub>T (Cond f r))) (lift\<^sub>c c\<^sub>1)) 
                                    (com.Seq (Basic (VC\<^sub>T (NCond f r))) (lift\<^sub>c c\<^sub>2)))" |
    "lift\<^sub>c (While f r I c) = (com.Seq ((com.Seq (Basic (VC\<^sub>T (Cond f r))) (lift\<^sub>c c))*) 
                                      (Basic (VC\<^sub>T (NCond f r))))"

end