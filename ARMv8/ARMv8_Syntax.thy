theory ARMv8_Syntax
  imports ARMv8_Rules ARMv8_Inter
begin

datatype register = r\<^sub>0 | r\<^sub>1 | r\<^sub>2 | r\<^sub>3 | r\<^sub>4 | r\<^sub>5

syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)
  "_Assert"    :: "'a \<Rightarrow> 'a set"                    ("(\<llangle>_\<rrangle>)" [0] 1000)

translations
  "\<llangle>b\<rrangle>" \<rightharpoonup> "CONST Collect \<guillemotleft>b\<guillemotright>"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr \<^syntax_const>\<open>_antiquote\<close> t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(\<^syntax_const>\<open>_quote\<close>, K quote_tr)] end
\<close>

type_synonym ('v,'r,'a) thread = "(('v,'a) grel \<times> ('v,'a) grel \<times> ('v,'r,'a) pred \<times> ('v,'r,'a) pred \<times> ('v,'r,'a) com_armv8 \<times> ('v,'r,'a) pred)"
type_synonym ('v,'r,'a) threads = "('v,'r,'a) thread list"

definition addI
  where "addI I \<equiv> \<lambda>x. x ! 0 + I"

definition subI
  where "subI I \<equiv> \<lambda>x. x ! 0 - I"

definition addR
  where "addR \<equiv> \<lambda>x. x ! 0 + x ! 1"

definition subR
  where "subR \<equiv> \<lambda>x. x ! 0 - x ! 1"

definition modI
  where "modI I \<equiv> \<lambda>x. x ! 0 mod I"

definition modR
  where "modR \<equiv> \<lambda>x. x ! 0 mod x ! 1"

definition movI
  where "movI I \<equiv> \<lambda>x. I"

definition ODD :: "'b \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp)"
  where "ODD r = (Exp (\<lambda>x. x ! 0 mod 2) [Var r], (=), Val 1)"

definition NEQ :: "'b \<Rightarrow> 'b \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp)"
  where "NEQ r1 r2 = (Var r1, (\<noteq>), Var r2)"

definition LE :: "'b \<Rightarrow> 'b \<Rightarrow> ((nat,'b) bexp)"
  where "LE r1 r2 = Exp\<^sub>B (\<lambda>x. x!0 < x!1) [Var r1, Var r2]"

definition Z ::  "'b \<Rightarrow> ((nat,'b) bexp)"
  where "Z r = Exp\<^sub>B (\<lambda>x. x!0 = 0) [Var r]"

syntax
  "_Load"  :: "'r \<Rightarrow> 'r \<Rightarrow> 'v set \<Rightarrow> ('v,'r,'a) com_armv8" ("(_ := [_]~_)" [70, 65] 61)
  "_LoadC"  :: "'r \<Rightarrow> 'r \<Rightarrow> 'v set \<Rightarrow> 'c \<Rightarrow> ('v,'r,'a) com_armv8" ("(_ := [_ + #_]~_)" [70, 65] 61)
  "_LoadIC"  :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v set \<Rightarrow> 'c \<Rightarrow> ('v,'r,'a) com_armv8" ("(\<lbrace>_\<rbrace> _ := [_ + #_]~_)" [20, 70, 65] 61)

  "_Store" :: "'r \<Rightarrow> 'r \<Rightarrow> 'v set \<Rightarrow> ('v,'r,'a) com_armv8" ("([_] := _ ~ _)" [70, 65] 61)
  "_StoreI" :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> 'v set \<Rightarrow> ('v,'r,'a) com_armv8" ("(\<lbrace>_\<rbrace> [_ + #_] := _ ~ _)" [20, 70, 65] 61)
  "_StoreIA" :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> 'v set \<Rightarrow> ('v,'r,'a) auxfn  \<Rightarrow> ('v,'r,'a) com_armv8" ("(\<lbrace>_\<rbrace> [_ + #_] := _ ~ _ :\<^sub>a _)" [20, 70, 65] 61)
  
  "_Fence" :: "(nat,'b,'a) com_armv8" ("(fence)" 61)
  "_CFence" :: "(nat,'b,'a) com_armv8" ("(cfence)" 61)
  "_Cas" :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v set \<Rightarrow> ('v,'r,'a) auxfn  \<Rightarrow> ('v,'b,'a) com_armv8" ("(\<lbrace>_\<rbrace> _ := cas _ _ _ ~ _, _)" [20, 70, 65] 61)

  "_AddI"  :: "'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> (nat,'b,'a) com_armv8" ("(_ := _ + #_)" [70, 65, 65] 61)
  "_SubI"  :: "'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> (nat,'b,'a) com_armv8" ("(_ := _ - #_)" [70, 65, 65] 61)

  "_AddR"  :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> (nat,'b,'a) com_armv8" ("(_ := _ + _)" [70, 65, 65] 61)
  "_SubR"  :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> (nat,'b,'a) com_armv8" ("(_ := _ - _)" [70, 65, 65] 61)

  "_ModI"  :: "'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> (nat,'b,'a) com_armv8" ("(_ := _ % #_)" [70, 65, 65] 61)
  "_ModR"  :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> (nat,'b,'a) com_armv8" ("(_ := _ % _)" [70, 65, 65] 61)
  "_MovI"  :: "'b \<Rightarrow> nat \<Rightarrow> (nat,'b,'a) com_armv8" ("(_ := #_)" [70, 65] 61)
  "_Seq"   :: "(nat,'b,'a) com_armv8 \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> (nat,'b,'a) com_armv8" ("(_;/ _)" [60,61] 60)

  "_If" :: "((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> (nat,'b,'a) com_armv8" 
                ("(if _/ then _ //else _ /fi)"   [0,0,0] 61)
  "_If1" :: "'b \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> ('v,'r,'a) com_armv8" 
                ("(if _/ then _ /fi)"   [0,0] 61)
  "_Spec" :: "('v,'a) grel \<Rightarrow> ('v,'a) grel \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) thread"
                ("(R: _ //G:_ //I: _ //P: _ //{ _ } //Q: _)" [0,0,0,0] 61)
  "_AuxAssign"    :: "idt \<Rightarrow> 'b \<Rightarrow> ('v,'r,'a) auxfn" ("(\<^sup>a_ :=/ _)" [70, 65] 61)

translations
  "\<^sup>ax := a" \<rightharpoonup> "CONST state_rec.more o \<guillemotleft>\<acute>(state_rec.more_update (_update_name x (\<lambda>_. a)))\<guillemotright>"

  "x := [a]~v" \<rightharpoonup> "CONST Load (CONST UNIV) v (CONST Var a) x (CONST state_rec.more)"
  "x := [a + #I]~v" \<rightharpoonup> "CONST Load (CONST UNIV) v (CONST Exp (CONST addI I) [CONST Var a]) x (CONST state_rec.more)"
  "\<lbrace>P\<rbrace> x := [a + #I]~v" \<rightharpoonup> "CONST Load \<llangle>P\<rrangle> v (CONST Exp (CONST addI I) [CONST Var a]) x (CONST state_rec.more)"

  "[a] := r ~ v" \<rightharpoonup> "CONST Store (CONST UNIV) v (CONST Var a) r (CONST state_rec.more)"
  "\<lbrace>P\<rbrace> [a + #I] := x ~ v" \<rightharpoonup> "CONST Store \<llangle>P\<rrangle> v (CONST Exp (CONST addI I) [CONST Var a]) x (CONST state_rec.more)"
  "\<lbrace>P\<rbrace> [ra + #I] := r ~ v :\<^sub>a a" \<rightharpoonup> "CONST Store \<llangle>P\<rrangle> v (CONST Exp (CONST addI I) [CONST Var ra]) r a"

  "\<lbrace>P\<rbrace> r\<^sub>1 := cas r\<^sub>2 r\<^sub>3 r\<^sub>4 ~ v, a" \<rightharpoonup> "CONST CAS \<llangle>P\<rrangle> v r\<^sub>2 r\<^sub>3 r\<^sub>4 r\<^sub>1 1 0 a"

  "X := Y - #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST subI I) [CONST Var Y])"
  "X := Y + #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST addI I) [CONST Var Y])"
  "X := Y + Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST addR) [CONST Var Y, CONST Var Z])"
  "X := Y - Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST subR) [CONST Var Y, CONST Var Z])"
  "X := Y % #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST modI I) [CONST Var Y])"
  "X := Y % Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST modR) [CONST Var Y, CONST Var Z])"

  "X := #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST movI I) [])"
  "fence" \<rightharpoonup> "CONST Fence"
  "cfence" \<rightharpoonup> "CONST Fence"
  "c\<^sub>1 ; c\<^sub>2" \<rightharpoonup> "CONST Seq c\<^sub>1 c\<^sub>2"
  "if b then c\<^sub>1 else c\<^sub>2 fi" \<rightharpoonup> "CONST If b c\<^sub>1 c\<^sub>2"
  "if b then c\<^sub>1 fi" \<rightharpoonup> "CONST If b c\<^sub>1 (CONST Skip)"
  "R: R G: G I: I P: P {c} Q: Q" \<rightharpoonup> "(\<llangle>R\<rrangle>,\<llangle>G\<rrangle>,\<llangle>I\<rrangle>,\<llangle>P\<rrangle>,c,\<llangle>Q\<rrangle>)"

definition inv2
  where "inv2 I \<equiv> {(m,m'). m \<in> glb ` I \<longrightarrow> m' \<in> glb ` I}"

fun fn_valid :: "('v::equal,'r::equal,'a) threads \<Rightarrow> bool"
  where 
    "fn_valid [(R,G,I,P,c,Q)] = (stable\<^sub>t R Q \<and> wellformed R G \<and> guar\<^sub>c c (inv2 I \<inter> G) \<and> 
                                (stable\<^sub>t R Q \<longrightarrow> P \<subseteq> wp (inv2 I \<inter> R) c Q) \<and>
                                (wellformed R G \<longrightarrow> rif_checks c R G))" |
    "fn_valid _ = undefined"

nonterminal prgs

syntax
  "_PAR"        :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" 60)
  "_FN"        :: "prgs \<Rightarrow> 'a"              ("FNBEGIN//_//FNEND" 60)
  "_prg"        :: "'a \<Rightarrow> prgs"              ("_" 57)
  "_prgs"       :: "['a, prgs] \<Rightarrow> prgs"      ("_//\<parallel>//_" [60,57] 57)

translations
  "_prg a" \<rightharpoonup> "[a]"
  "_prgs a ps" \<rightharpoonup> "a # ps"
  "_FN t" \<rightharpoonup> "CONST fn_valid t"

syntax
  "_before"  :: "'b \<Rightarrow> 'a" ("\<^sup>1_" [100] 400)
  "_after"   :: "'b \<Rightarrow> 'a" ("\<^sup>2_" [100] 400)
  "_mem"     :: "'g \<Rightarrow> 'a" ("\<^sup>s[_]")
  "_mbefore" :: "'g \<Rightarrow> 'a" ("\<^sup>1[_]")
  "_mafter"  :: "'g \<Rightarrow> 'a" ("\<^sup>2[_]")
  "_reg"     :: "'r \<Rightarrow> 'a" ("\<^sup>r_" [100] 1000)
  "_rbefore" :: "'r \<Rightarrow> 'a" ("\<^sup>1\<^sup>r_")
  "_rafer"   :: "'r \<Rightarrow> 'a" ("\<^sup>2\<^sup>r_")
  "_aux"     :: "'b \<Rightarrow> 'a" ("\<^sup>a_" [100] 1000)
  "_abefore" :: "'b \<Rightarrow> 'a" ("\<^sup>1\<^sup>a_" [100] 400)
  "_aafer"   :: "'b \<Rightarrow> 'a" ("\<^sup>2\<^sup>a_" [100] 400)

definition gld :: "('v,'r,'a) state \<Rightarrow> ('v \<Rightarrow> 'v)"
  where "gld m \<equiv> \<lambda>v. st m (Glb v)"

translations
  "\<^sup>1x" \<rightleftharpoons> "x (\<acute>CONST fst)"
  "\<^sup>2x" \<rightleftharpoons> "x (\<acute>CONST snd)"
  "\<^sup>s[X]" \<rightleftharpoons> "(\<acute>CONST gld) X"
  "\<^sup>1[X]" \<rightleftharpoons> "(CONST st (\<acute>CONST fst)) X"
  "\<^sup>2[X]" \<rightleftharpoons> "(CONST st (\<acute>CONST snd)) X"
  "\<^sup>rX" \<rightleftharpoons> "(\<acute>CONST rg) X"
  "\<^sup>1\<^sup>rX" \<rightleftharpoons> "(CONST rg (\<acute>CONST fst)) X"
  "\<^sup>2\<^sup>rX" \<rightleftharpoons> "(CONST rg (\<acute>CONST snd)) X"
  "\<^sup>aX" \<rightleftharpoons> "X (\<acute>CONST state_rec.more)"
  "\<^sup>1\<^sup>aX" \<rightleftharpoons> "X (CONST state_rec.more (\<acute>CONST fst))"
  "\<^sup>2\<^sup>aX" \<rightleftharpoons> "X (CONST state_rec.more (\<acute>CONST snd))"

(*
syntax
  "_before"  :: "'b \<Rightarrow> 'a" ("\<^sup>1_" [100] 400)
  "_after"   :: "'b \<Rightarrow> 'a" ("\<^sup>2_" [100] 400)
  "_mem"     :: "'b \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>")
  "_mat"     :: "'b \<Rightarrow> 'a" ("\<^sup>0\<lbrakk>_\<rbrakk>")
  "_mbefore" :: "'b \<Rightarrow> 'a" ("\<^sup>1\<lbrakk>_\<rbrakk>")
  "_mafter"  :: "'b \<Rightarrow> 'a" ("\<^sup>2\<lbrakk>_\<rbrakk>")
  "_reg"     :: "'r \<Rightarrow> 'a" ("\<^bold>r_" [1000] 1000)
  "_rar"     :: "'r \<Rightarrow> 'a" ("\<^sup>0\<^bold>r_" [100] 1000)
  "_rbefore" :: "'r \<Rightarrow> 'a" ("\<^sup>1\<^bold>r_")
  "_rafer"   :: "'r \<Rightarrow> 'a" ("\<^sup>2\<^bold>r_")
  "_val"     :: "'b \<Rightarrow> 'a" ("#_" [100] 1000)
  "_aux"     :: "'b \<Rightarrow> 'a" ("\<^sup>a_" [100] 1000)
  "_abefore" :: "'b \<Rightarrow> 'a" ("\<^sup>1\<^sup>a_" [100] 400)
  "_aafer"   :: "'b \<Rightarrow> 'a" ("\<^sup>2\<^sup>a_" [100] 400)

translations
  "\<^sup>1x" \<rightleftharpoons> "x (\<acute>CONST fst)"
  "\<^sup>2x" \<rightleftharpoons> "x (\<acute>CONST snd)"
  "\<lbrakk>X\<rbrakk>" \<rightleftharpoons> "CONST Var (CONST Glb X)"
  "\<^sup>0\<lbrakk>X\<rbrakk>" \<rightleftharpoons> "(CONST st (\<acute>CONST glb)) X"
  "\<^sup>1\<lbrakk>X\<rbrakk>" \<rightleftharpoons> "(CONST st (\<acute>CONST fst)) X"
  "\<^sup>2\<lbrakk>X\<rbrakk>" \<rightleftharpoons> "(CONST st (\<acute>CONST snd)) X"
  "\<^bold>rX" \<rightleftharpoons> "CONST Var (CONST Var X)"
  "\<^sup>0\<^bold>rX" \<rightleftharpoons> "(\<acute>CONST rg) X"
  "\<^sup>1\<^bold>rX" \<rightleftharpoons> "(CONST rg (\<acute>CONST fst)) X"
  "\<^sup>2\<^bold>rX" \<rightleftharpoons> "(CONST rg (\<acute>CONST snd)) X"
  "#X" \<rightleftharpoons> "CONST Val X"
  "\<^sup>aX" \<rightleftharpoons> "X (\<acute>CONST state_rec.more)"
  "\<^sup>1\<^sup>aX" \<rightleftharpoons> "X (CONST state_rec.more (\<acute>CONST fst))"
  "\<^sup>2\<^sup>aX" \<rightleftharpoons> "X (CONST state_rec.more (\<acute>CONST snd))"
*)

syntax
  "_con" :: "nat \<Rightarrow> 'a" ("=[_]" [100] 1000)
  "_inc" :: "nat \<Rightarrow> 'a" ("\<le>[_]" [100] 1000)

translations
  "=[X]" \<rightharpoonup> "(CONST st (\<acute>CONST snd)) X = (CONST st (\<acute>CONST fst)) X"
  "\<le>[X]" \<rightharpoonup> "(CONST st (\<acute>CONST snd)) X \<ge> (CONST st (\<acute>CONST fst)) X"

lemma [simp]:
  "stabilize R UNIV = UNIV"
  by (auto simp: stabilize_def)

lemma [simp]:
  "reflexive R \<Longrightarrow> stabilize R {} = {}"
  by (auto simp: reflexive_def stabilize_def)

lemma [simp]:
  "reflexive R \<Longrightarrow> stabilize R (assert P) = assert P"
  by (auto simp: assert_def)

lemma [simp]:
  "{m. m(a :=\<^sub>s e) \<in> (assert P)} = assert P"
  by (auto simp: assert_def)

lemma [simp]:
  "reflexive R \<Longrightarrow> UNIV \<subseteq> stabilize R P = (\<forall>m. m \<in> P)"
  by (auto simp: reflexive_def stabilize_def assert_def glb_def)

lemma [simp]:
  "stabilize R (P \<inter> Q) = stabilize R P \<inter> stabilize R Q"
  by (auto simp: stabilize_def)

lemma [simp]:
  "{m. (f m) \<in> assert P} = assert P"
  by (auto simp: assert_def)

lemma [simp]:
  "UNIV \<subseteq> assert P = P"
  by (auto simp: assert_def)

lemma [simp]:
  "x(aux: state_rec.more) = x"
  by (auto simp: aux_upd_def)

lemma [simp]:
  "st (glb (x(Glb z :=\<^sub>s e))) = (st (glb x))(z := e)"
  by (auto simp: st_upd_def glb_def)

lemma [simp]:
  "st (glb (x(aux:f ))) = (st (glb x))"
  by (auto simp: st_upd_def glb_def)

lemma glb_in [intro!]:
  assumes "\<exists>l. \<lparr> st = (\<lambda>v. case v of Reg v \<Rightarrow> l v | _ \<Rightarrow> st m v), \<dots> = state_rec.more m \<rparr> \<in> P"
  shows "glb m \<in> glb ` P"
proof -
  obtain l where "\<lparr> st = (\<lambda>v. case v of Reg v \<Rightarrow> l v | _ \<Rightarrow> st m v), \<dots> = state_rec.more m \<rparr> \<in> P"
    (is "?m \<in> P")
    using assms by auto
  hence "glb ?m \<in> glb ` P" by auto
  moreover have "glb m = glb ?m" by (auto simp: glb_def)
  ultimately show ?thesis by auto
qed

lemma  a:
  "glb x = glb y \<Longrightarrow> st x (Glb e) = st y (Glb e)"
  unfolding glb_def
  by (metis state_rec.select_convs(1))

lemma  b:
  "glb x = glb y \<Longrightarrow> state_rec.more x = state_rec.more y"
  unfolding glb_def by simp

lemma [simp]:
  "st (glb x) y = st x (Glb y)"
  unfolding glb_def by auto

fun chain
  where "chain [] Q = Q" | "chain (a#xs) Q = chain xs (wpre a Q)"
declare chain.simps [simp del]

lemma chain_singleI:
  "wpre a Q = chain [a] Q"
  unfolding chain.simps by auto

lemma chain_singleI':
  "stabilize R Q = chain [env R] Q"
  unfolding chain.simps by auto

lemma chain_lastE:
  "chain (xs @ [a]) Q = wpre a ( (chain xs Q))"
  by (induct xs arbitrary: Q) (auto simp: chain.simps)

lemma chain_lastI:
  "chain [a] (chain xs Q) = chain (xs@[a]) Q"
  by (induct xs) (auto simp: chain_lastE chain.simps)

lemma chain_merge:
  "chain l (chain l' Q) = chain (l'@l) Q"
  by (induct l' arbitrary: Q) (simp add: chain.simps)+

lemma stabilize_mono:
  "P \<subseteq> Q \<Longrightarrow> stabilize R P  \<subseteq> stabilize R Q"
  unfolding stabilize_def by auto

lemma pre_mono:
  "P \<subseteq> Q \<Longrightarrow> wpre a P \<subseteq> wpre a Q"
  using  stabilize_mono apply (cases a) apply (auto)
  by blast

lemma chain_mono:
  "P \<subseteq> Q \<Longrightarrow> chain xs P \<subseteq> chain xs Q"
  by (induct xs arbitrary: P Q) (auto simp: pre_mono stabilize_mono chain.simps)

lemma chain1_wpre:
  "P \<subseteq> chain xs (wpre a Q) \<Longrightarrow> P \<subseteq> chain (a#xs) Q"
  unfolding chain.simps .

lemma chain1_stab:
  "P \<subseteq> chain xs (stabilize R Q) \<Longrightarrow> P \<subseteq> chain (env R#xs) Q"
  unfolding chain.simps by auto

lemma chain0:
  "P \<subseteq> Q \<Longrightarrow> P \<subseteq>  chain [] Q"
  unfolding chain.simps .

lemma chain_extend:
  "P \<subseteq> chain xs (Q \<inter> X) \<Longrightarrow> P \<subseteq> chain xs Q"
  using chain_mono[of "Q \<inter> X" Q] by (auto simp: )

lemma chain_rewrite:
  "X \<subseteq> Q \<Longrightarrow> P \<subseteq> chain xs X \<Longrightarrow> P \<subseteq> chain xs Q"
  using chain_mono  by blast

definition str where
  "str R P \<equiv> if P \<subseteq> stabilize R P then P else UNIV"

lemma str_mono:
  "Q \<subseteq> P \<Longrightarrow> Q \<subseteq> str R P"
  unfolding str_def by (auto simp: )

lemma stabilize_univ:
  "UNIV \<subseteq> stabilize R UNIV"
  unfolding stabilize_def by auto

lemma stabilize_str:
  "str R P \<subseteq> stabilize R (str R P)"
  unfolding str_def stabilize_def by simp

lemma [simp]: "wpre a (P \<inter> Q) = (wpre a P \<inter> wpre a Q)"
  by (cases a, auto)

lemma chain_inter: "chain l (P \<inter> Q) = (chain l P \<inter> chain l Q)"
  by (induct l arbitrary: P Q, auto simp: chain.simps)

lemma stable_stabilize:
  "stable\<^sub>t R Q \<Longrightarrow> Q \<subseteq> stabilize R Q"
  unfolding stabilize_def stable_def step\<^sub>t_def
  by auto

lemma strI:
  "stable\<^sub>t R Q \<Longrightarrow> K \<subseteq> chain l (str R Q) \<Longrightarrow>  K \<subseteq> chain (env R#l) Q"
  unfolding chain.simps str_def apply simp
  using stable_stabilize
  by (metis (mono_tags) chain_rewrite)

lemma envI:
  "stable\<^sub>t R Q \<Longrightarrow> K \<subseteq> chain l (Q) \<Longrightarrow>  K \<subseteq> chain (env R#l) Q"
  unfolding chain.simps str_def apply simp
  using stable_stabilize
  by (metis (mono_tags) chain_rewrite)

lemma ir_str:
  "wpre (ir r e) (str R Q) \<supseteq> str R (wpre (ir r e) Q)"
  apply (auto simp: str_def stabilize_def st_upd_def)
   apply (subgoal_tac "rg (x\<lparr>st := (st x)(Reg r := ev\<^sub>E (rg m') e)\<rparr>) = rg (m'\<lparr>st := (st m')(Reg r := ev\<^sub>E (rg m') e)\<rparr>)")
     apply (subgoal_tac "(glb (x\<lparr>st := (st x)(Reg r := ev\<^sub>E (rg m') e)\<rparr>), glb (m'\<lparr>st := (st m')(Reg r := ev\<^sub>E (rg m') e)\<rparr>)) \<in> R")
     apply blast
  apply (auto simp: glb_def)[1]
  unfolding rg_def apply auto[1]
  done

lemma cm_str:
  "wpre (cm b) (str R Q) \<supseteq> str R (wpre (cm b) Q)"
  by (auto simp: str_def stabilize_def st_upd_def)

lemma ncm_str:
  "wpre (ncm b) (str R Q) \<supseteq> str R (wpre (ncm b) Q)"
  by (auto simp: str_def stabilize_def st_upd_def)

lemma ign_str:
  "Q \<subseteq> str R Q"
  by (auto simp: str_def)

lemma [simp]:
  "state_rec.more (glb x) = state_rec.more x"
  unfolding glb_def by auto

end