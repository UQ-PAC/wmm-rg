theory Example_Lang
  imports ARMv8_Comp
begin

datatype register = r\<^sub>0 | r\<^sub>1 | r\<^sub>2 | r\<^sub>3 | r\<^sub>4 | r\<^sub>5

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
  where "ODD r = (Exp (\<lambda>x. x ! 0 mod 2) [Reg r], (=), Val 1)"

definition NEQ :: "'b \<Rightarrow> 'b \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp)"
  where "NEQ r1 r2 = (Reg r1, (\<noteq>), Reg r2)"

definition LE :: "'b \<Rightarrow> 'b \<Rightarrow> ((nat,'b) bexp)"
  where "LE r1 r2 = Exp\<^sub>B (\<lambda>x. x!0 < x!1) [Reg r1, Reg r2]"

definition Z ::  "'b \<Rightarrow> ((nat,'b) bexp)"
  where "Z r = Exp\<^sub>B (\<lambda>x. x!0 = 0) [Reg r]"


syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr \<^syntax_const>\<open>_antiquote\<close> t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(\<^syntax_const>\<open>_quote\<close>, K quote_tr)] end
\<close>

syntax
  "_Load"  :: "'r \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) com_armv8" ("(_ := [_])" [70, 65] 61)
  "_LoadC"  :: "'r \<Rightarrow> 'r \<Rightarrow> 'c \<Rightarrow> ('v,'r,'a) com_armv8" ("(_ := [_ + #_])" [70, 65] 61)

  "_Store" :: "'r \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) com_armv8" ("([_] := _)" [70, 65] 61)
  "_StoreI" :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) com_armv8" ("(\<lbrace>_\<rbrace> [_ + #_] := _)" [20, 70, 65] 61)
  "_StoreIA" :: "('v,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> ('v,'r,'a) auxfn  \<Rightarrow> ('v,'r,'a) com_armv8" ("(\<lbrace>_\<rbrace> [_ + #_] := _, _)" [20, 70, 65] 61)
  
  "_Assert" :: "(nat,'b,'a) pred \<Rightarrow> (nat,'b,'a) com_armv8" ("(\<lparr>_\<rparr>)" [20] 61)
  "_Test" :: "(nat,'b,'a) pred \<Rightarrow> (nat,'b,'a) com_armv8" ("(\<lbrakk>_\<rbrakk>)" [20] 61)
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
  "_While" :: "((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b,'a) pred \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> (nat,'b,'a) com_armv8" 
                ("(while _/ inv \<lbrace>_\<rbrace> //do _ /od)"   [0,0,0] 61)
  "_If" :: "((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> (nat,'b,'a) com_armv8" 
                ("(if _/ then _ //else _ /fi)"   [0,0,0] 61)
  "_If1" :: "'b \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> ('v,'r,'a) com_armv8" 
                ("(if _/ then _ /fi)"   [0,0] 61)
  "_DoWhile" :: "(nat,'b,'a) pred \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b,'a) com_armv8" 
                ("(1do _/ inv \<lbrace>_\<rbrace> //while _)"  [0,0,100] 61)
  "_WhileT" :: "((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b,'a) pred \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> (nat,'b,'a) com_armv8" 
                ("(while _ //do _ /od)"   [0,0] 61)
  "_DoWhileT" :: "(nat,'b,'a) pred \<Rightarrow> (nat,'b,'a) com_armv8 \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b,'a) com_armv8" 
                ("(1do _ //while _)"  [0,100] 61)
  "_Spec" :: "('v,'a) grel \<Rightarrow> ('v,'a) grel \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) com_armv8 \<Rightarrow> ('v,'r,'a) pred \<Rightarrow> ('v,'r,'a) thread"
                ("(R: _ //G:_ //I: _ //P: _ //{ _ } //Q: _)" [0,0,0,0] 61)
  "_AuxAssign"    :: "idt \<Rightarrow> 'b \<Rightarrow> ('v,'r,'a) auxfn" ("(\<^sup>a_ :=/ _)" [70, 65] 61)

translations
  "\<^sup>ax := a" \<rightharpoonup> "CONST tstate_rec.more o \<guillemotleft>\<acute>(tstate_rec.more_update (_update_name x (\<lambda>_. a)))\<guillemotright>"

  "x := [a]" \<rightharpoonup> "CONST Load (CONST True\<^sub>p) (CONST Reg a) x (CONST tstate_rec.more)"
  "x := [a + #I]" \<rightharpoonup> "CONST Load (CONST True\<^sub>p) (CONST Exp (CONST addI I) [CONST Reg a]) x (CONST tstate_rec.more)"

  "[a] := r" \<rightharpoonup> "CONST Store (CONST True\<^sub>p) (CONST Reg a) r (CONST tstate_rec.more)"
  "\<lbrace>P\<rbrace> [a + #I] := x" \<rightharpoonup> "CONST Store \<guillemotleft>P\<guillemotright> (CONST Exp (CONST addI I) [CONST Reg a]) x (CONST tstate_rec.more)"
  "\<lbrace>P\<rbrace> [ra + #I] := r, a" \<rightharpoonup> "CONST Store \<guillemotleft>P\<guillemotright> (CONST Exp (CONST addI I) [CONST Reg ra]) r a"

  "\<lbrace>P\<rbrace> r\<^sub>1 := cas r\<^sub>2 r\<^sub>3 r\<^sub>4, a" \<rightharpoonup> "CONST CAS \<guillemotleft>P\<guillemotright> r\<^sub>2 r\<^sub>3 r\<^sub>4 r\<^sub>1 1 0 a"

  "X := Y - #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST subI I) [CONST Reg Y])"
  "X := Y + #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST addI I) [CONST Reg Y])"
  "X := Y + Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST addR) [CONST Reg Y, CONST Reg Z])"
  "X := Y - Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST subR) [CONST Reg Y, CONST Reg Z])"
  "X := Y % #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST modI I) [CONST Reg Y])"
  "X := Y % Z" \<rightharpoonup> "CONST Op X (CONST Exp (CONST modR) [CONST Reg Y, CONST Reg Z])"

  "X := #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST movI I) [])"
  "\<lparr>P\<rparr>" \<rightharpoonup> "CONST Test \<guillemotleft>P\<guillemotright>"
  "\<lbrakk>P\<rbrakk>" \<rightharpoonup> "CONST Assert \<guillemotleft>P\<guillemotright>"
  "fence" \<rightharpoonup> "CONST Fence"
  "cfence" \<rightharpoonup> "CONST Fence"
  "c\<^sub>1 ; c\<^sub>2" \<rightharpoonup> "CONST Seq c\<^sub>1 c\<^sub>2"
  "if b then c\<^sub>1 else c\<^sub>2 fi" \<rightharpoonup> "CONST If b c\<^sub>1 c\<^sub>2"
  "if b then c\<^sub>1 fi" \<rightharpoonup> "CONST If b c\<^sub>1 (CONST Skip)"
  "while b inv \<lbrace>P\<rbrace> do c od" \<rightharpoonup> "CONST While b \<guillemotleft>P\<guillemotright> c"
  "do c inv \<lbrace>P\<rbrace> while b" \<rightharpoonup> "CONST DoWhile \<guillemotleft>P\<guillemotright> c b"
  "while b do c od" \<rightharpoonup> "CONST While b (CONST True\<^sub>p) c"
  "do c while b" \<rightharpoonup> "CONST DoWhile (CONST True\<^sub>p) c b"
  "R: R G: G I: I P: P {c} Q: Q" \<rightharpoonup> "(\<guillemotleft>R\<guillemotright>,\<guillemotleft>G\<guillemotright>,\<guillemotleft>I\<guillemotright>,\<guillemotleft>P\<guillemotright>,c,\<guillemotleft>Q\<guillemotright>)"

nonterminal prgs

syntax
  "_PAR"        :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" 60)
  "_FN"        :: "prgs \<Rightarrow> 'a"              ("FNBEGIN//_//FNEND" 60)
  "_prg"        :: "'a \<Rightarrow> prgs"              ("_" 57)
  "_prgs"       :: "['a, prgs] \<Rightarrow> prgs"      ("_//\<parallel>//_" [60,57] 57)

definition com_valid :: "(nat,register,'a) threads \<Rightarrow> bool"
  where "com_valid t \<equiv> validity (Cs t) \<langle>Ps t\<rangle> \<langle>Rs t\<rangle> \<langle>Gs t\<rangle> \<langle>Qs t\<rangle>"

fun fn_valid :: "(nat,register,'a) threads \<Rightarrow> bool"
  where "fn_valid [(R,G,I,P,c,Q)] = 
            (stable\<^sub>t R Q \<and> wellformed R G \<and> 
            guar\<^sub>c c (inv2 I \<and>\<^sub>p G) \<and> (P \<turnstile>\<^sub>p wp R c Q))"

translations
  "_prg a" \<rightharpoonup> "[a]"
  "_prgs a ps" \<rightharpoonup> "a # ps"
  "_PAR t" \<rightharpoonup> "CONST com_valid t"
  "_FN t" \<rightharpoonup> "CONST fn_valid t"

syntax
  "_before"  :: "'b \<Rightarrow> 'a" ("\<^sup>1_" [100] 400)
  "_after"   :: "'b \<Rightarrow> 'a" ("\<^sup>2_" [100] 400)
  "_mem"     :: "nat \<Rightarrow> 'a" ("\<^sup>s[_]")
  "_mbefore" :: "nat \<Rightarrow> 'a" ("\<^sup>1[_]")
  "_mafter"  :: "nat \<Rightarrow> 'a" ("\<^sup>2[_]")
  "_reg"     :: "register \<Rightarrow> 'a" ("\<^sup>r_" [100] 1000)
  "_rbefore" :: "register \<Rightarrow> 'a" ("\<^sup>1\<^sup>r_")
  "_rafer"   :: "register \<Rightarrow> 'a" ("\<^sup>2\<^sup>r_")
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
  "\<^sup>aX" \<rightleftharpoons> "X (\<acute>CONST tstate_rec.more)"
  "\<^sup>1\<^sup>aX" \<rightleftharpoons> "X (CONST gstate_rec.more (\<acute>CONST fst))"
  "\<^sup>2\<^sup>aX" \<rightleftharpoons> "X (CONST gstate_rec.more (\<acute>CONST snd))"

syntax
  "_con" :: "nat \<Rightarrow> 'a" ("=[_]" [100] 1000)
  "_inc" :: "nat \<Rightarrow> 'a" ("\<le>[_]" [100] 1000)

translations
  "=[X]" \<rightharpoonup> "(CONST st (\<acute>CONST snd)) X = (CONST st (\<acute>CONST fst)) X"
  "\<le>[X]" \<rightharpoonup> "(CONST st (\<acute>CONST snd)) X \<ge> (CONST st (\<acute>CONST fst)) X"

lemma stabilize_true [simp]:
  "stabilize R (\<lambda>m. True) = (\<lambda>m. True)"
  unfolding stabilize_def by auto


end