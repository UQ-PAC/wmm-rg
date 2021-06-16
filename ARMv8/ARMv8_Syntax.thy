theory ARMv8_Syntax
  imports ARMv8_Rules
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
  "_Load"  :: "'r \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) com_armv8" ("(_ := [_])" [70, 65] 61)
  "_LoadC"  :: "'r \<Rightarrow> 'r \<Rightarrow> 'c \<Rightarrow> ('v,'r,'a) com_armv8" ("(_ := [_ + #_])" [70, 65] 61)
  "_LoadIC"  :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'c \<Rightarrow> ('v,'r,'a) com_armv8" ("(\<lbrace>_\<rbrace> _ := [_ + #_])" [20, 70, 65] 61)

  "_Store" :: "'r \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) com_armv8" ("([_] := _)" [70, 65] 61)
  "_StoreI" :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) com_armv8" ("(\<lbrace>_\<rbrace> [_ + #_] := _)" [20, 70, 65] 61)
  "_StoreIA" :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) auxfn  \<Rightarrow> ('v,'r,'a) com_armv8" ("(\<lbrace>_\<rbrace> [_ + #_] := _ :\<^sub>a _)" [20, 70, 65] 61)
  
  "_Fence" :: "(nat,'b,'a) com_armv8" ("(fence)" 61)
  "_CFence" :: "(nat,'b,'a) com_armv8" ("(cfence)" 61)
  "_Cas" :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) auxfn  \<Rightarrow> ('v,'b,'a) com_armv8" ("(\<lbrace>_\<rbrace> _ := cas _ _ _, _)" [20, 70, 65] 61)

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

  "x := [a]" \<rightharpoonup> "CONST Load (CONST UNIV) (CONST Reg a) x (CONST state_rec.more)"
  "x := [a + #I]" \<rightharpoonup> "CONST Load (CONST UNIV) (CONST Exp (CONST addI I) [CONST Reg a]) x (CONST state_rec.more)"
  "\<lbrace>P\<rbrace> x := [a + #I]" \<rightharpoonup> "CONST Load \<llangle>P\<rrangle> (CONST Exp (CONST addI I) [CONST Reg a]) x (CONST state_rec.more)"

  "[a] := r" \<rightharpoonup> "CONST Store (CONST UNIV) (CONST Reg a) r (CONST state_rec.more)"
  "\<lbrace>P\<rbrace> [a + #I] := x" \<rightharpoonup> "CONST Store \<llangle>P\<rrangle> (CONST Exp (CONST addI I) [CONST Reg a]) x (CONST state_rec.more)"
  "\<lbrace>P\<rbrace> [ra + #I] := r :\<^sub>a a" \<rightharpoonup> "CONST Store \<llangle>P\<rrangle> (CONST Exp (CONST addI I) [CONST Reg ra]) r a"

  "\<lbrace>P\<rbrace> r\<^sub>1 := cas r\<^sub>2 r\<^sub>3 r\<^sub>4, a" \<rightharpoonup> "CONST CAS \<llangle>P\<rrangle> r\<^sub>2 r\<^sub>3 r\<^sub>4 r\<^sub>1 1 0 a"

  "X := Y - #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST subI I) [CONST Reg Y])"
  "X := Y + #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST addI I) [CONST Reg Y])"
  "X := Y + Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST addR) [CONST Reg Y, CONST Reg Z])"
  "X := Y - Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST subR) [CONST Reg Y, CONST Reg Z])"
  "X := Y % #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST modI I) [CONST Reg Y])"
  "X := Y % Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST modR) [CONST Reg Y, CONST Reg Z])"

  "X := #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST movI I) [])"
  "fence" \<rightharpoonup> "CONST Fence"
  "cfence" \<rightharpoonup> "CONST Fence"
  "c\<^sub>1 ; c\<^sub>2" \<rightharpoonup> "CONST Seq c\<^sub>1 c\<^sub>2"
  "if b then c\<^sub>1 else c\<^sub>2 fi" \<rightharpoonup> "CONST If b c\<^sub>1 c\<^sub>2"
  "if b then c\<^sub>1 fi" \<rightharpoonup> "CONST If b c\<^sub>1 (CONST Skip)"
  "R: R G: G I: I P: P {c} Q: Q" \<rightharpoonup> "(\<llangle>R\<rrangle>,\<llangle>G\<rrangle>,\<llangle>I\<rrangle>,\<llangle>P\<rrangle>,c,\<llangle>Q\<rrangle>)"

definition inv2
  where "inv2 I \<equiv> {(m,m'). m \<in> glb ` I \<longrightarrow> m' \<in> glb ` I}"

definition rif_checks
  where "rif_checks c R G = True"

fun fn_valid :: "('v::equal,'r::equal,'a) threads \<Rightarrow> bool"
  where 
    "fn_valid [(R,G,I,P,c,Q)] = (stable\<^sub>t R Q \<and> wellformed R G \<and> guar\<^sub>c c (inv2 I \<inter> G) \<and> 
                                (wellformed R G \<longrightarrow> stable\<^sub>t R Q \<longrightarrow> P \<subseteq> wp R c Q) \<and>
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
  "_mem"     :: "nat \<Rightarrow> 'a" ("\<^sup>s[_]")
  "_mbefore" :: "nat \<Rightarrow> 'a" ("\<^sup>1[_]")
  "_mafter"  :: "nat \<Rightarrow> 'a" ("\<^sup>2[_]")
  "_reg"     :: "'r \<Rightarrow> 'a" ("\<^sup>r_" [100] 1000)
  "_rbefore" :: "'r \<Rightarrow> 'a" ("\<^sup>1\<^sup>r_")
  "_rafer"   :: "'r \<Rightarrow> 'a" ("\<^sup>2\<^sup>r_")
  "_aux"     :: "'b \<Rightarrow> 'a" ("\<^sup>a_" [100] 1000)
  "_abefore" :: "'b \<Rightarrow> 'a" ("\<^sup>1\<^sup>a_" [100] 400)
  "_aafer"   :: "'b \<Rightarrow> 'a" ("\<^sup>2\<^sup>a_" [100] 400)

translations
  "\<^sup>1x" \<rightleftharpoons> "x (\<acute>CONST fst)"
  "\<^sup>2x" \<rightleftharpoons> "x (\<acute>CONST snd)"
  "\<^sup>s[X]" \<rightleftharpoons> "(\<acute>CONST st) X"
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
  "\<^bold>rX" \<rightleftharpoons> "CONST Var (CONST Reg X)"
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

end