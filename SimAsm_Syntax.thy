theory SimAsm_Syntax
  imports SimAsm_Rules
begin

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

type_synonym ('v,'g,'r,'a) thread = "(('v,'g,'a) grel \<times> ('v,'g,'a) grel \<times> ('v,'g,'r,'a) pred \<times> ('v,'g,'r,'a) lang \<times> ('v,'g,'r,'a) pred)"
type_synonym ('v,'g,'r,'a) threads = "('v,'g,'r,'a) thread list"

definition test 
  where "test e = Exp\<^sub>B (\<lambda>x. x ! 0) [e]"

syntax
  "_AssignR"  :: "'r \<Rightarrow> 'b \<Rightarrow> ('v,'g,'r,'a) lang" ("(\<^bold>r_ := _)" [70, 65] 61)
  "_AssignRA"  :: "'r \<Rightarrow> 'b \<Rightarrow> ('v,'g,'r,'a) auxfn \<Rightarrow> ('v,'g,'r,'a) lang" ("(\<^bold>r_ := _ :\<^sub>a _)" [70, 65] 61)
  "_AssignRC"  :: "('v,'g,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'b \<Rightarrow> ('v,'g,'r,'a) lang" ("(\<lbrace>_\<rbrace> \<^bold>r_ := _)" [20, 70, 65] 61)
  "_AssignRCA"  :: "('v,'g,'r,'a) pred \<Rightarrow> 'r \<Rightarrow> 'b \<Rightarrow> ('v,'g,'r,'a) auxfn \<Rightarrow> ('v,'g,'r,'a) lang" ("(\<lbrace>_\<rbrace> \<^bold>r_ := _ :\<^sub>a _)" [20, 70, 65] 61)

  "_AssignG"  :: "'g \<Rightarrow> 'b \<Rightarrow> ('v,'g,'r,'a) lang" ("(\<lbrakk>_\<rbrakk> := _)" [70, 65] 61)
  "_AssignGC"  :: "('v,'g,'r,'a) pred \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> ('v,'g,'r,'a) lang" ("(\<lbrace>_\<rbrace> \<lbrakk>_\<rbrakk> := _)" [20, 70, 65] 61)
  "_AssignGCA"  :: "('v,'g,'r,'a) pred \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> ('v,'g,'r,'a) auxfn \<Rightarrow> ('v,'g,'r,'a) lang" ("(\<lbrace>_\<rbrace> \<lbrakk>_\<rbrakk> := _, _)" [20, 70, 65] 61)

  "_Fence" :: "('v,'g,'r,'a) lang" ("(fence)" 61)
  "_CFence" :: "('v,'g,'r,'a) lang" ("(cfence)" 61)

  "_Seq"   :: "('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) lang" ("(_;/ _)" [60,61] 60)
  "_While" :: "'c \<Rightarrow> ('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) lang" 
                ("(while _/ inv \<lbrace>_\<rbrace> //do _ /od)"   [0,0,0] 61)
  "_If" :: "'c \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) lang" 
                ("(if _/ then _ //else _ /fi)"   [0,0,0] 61)
  "_If1" :: "'b \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) lang" 
                ("(if _/ then _ /fi)"   [0,0] 61)
  "_WhileT" :: "'c \<Rightarrow> ('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) lang" 
                ("(while _ //do _ /od)"   [0,0] 61)
  "_Spec" :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r,'a) thread"
                ("(R: _ //G:_ //P: _ //{ _ } //Q: _)" [0,0,0,0,40] 61)
  "_DoWhileT" :: "('v,'g,'r,'a) lang \<Rightarrow> 'c \<Rightarrow> ('v,'g,'r,'a) lang" 
                ("(1do _ //while _)"  [0,100] 61)
  "_DoWhile" :: "('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) pred \<Rightarrow>  'c \<Rightarrow> ('v,'g,'r,'a) lang" 
                ("(1do _/ inv \<lbrace>_\<rbrace> //while _)"  [0,0,100] 61)
  "_AuxAssign"    :: "idt \<Rightarrow> 'b \<Rightarrow> ('v,'g,'r,'a) auxfn" ("(\<^sup>a_ :=/ _)" [70, 65] 61)

translations
  "\<^sup>ax := a" \<rightharpoonup> "CONST more o \<guillemotleft>\<acute>(state_rec.more_update (_update_name x (\<lambda>_. a)))\<guillemotright>"

  "\<^bold>rx := a" \<rightharpoonup> "CONST Op (CONST UNIV) (CONST assign (CONST Reg x) a) (CONST more)"
  "\<^bold>rx := a :\<^sub>a f" \<rightharpoonup> "CONST Op (CONST UNIV) (CONST assign (CONST Reg x) a) f"

  "\<lbrakk>x\<rbrakk> := a" \<rightharpoonup> "CONST Op (CONST UNIV) (CONST assign (CONST Glb x) a) (CONST more)"
  "\<lbrace>P\<rbrace> \<lbrakk>x\<rbrakk> := a" \<rightharpoonup> "CONST Op \<llangle>P\<rrangle> (CONST assign (CONST Glb x) a) (CONST more)"
  "\<lbrace>P\<rbrace> \<lbrakk>x\<rbrakk> := a, f" \<rightharpoonup> "CONST Op \<llangle>P\<rrangle> (CONST assign (CONST Glb x) a) f"

  "fence" \<rightharpoonup> "CONST Op (CONST UNIV) (CONST full_fence) (CONST more)"
  "cfence" \<rightharpoonup> "CONST Op (CONST UNIV) (CONST ctrl_fence) (CONST more)"
  "c\<^sub>1 ; c\<^sub>2" \<rightharpoonup> "CONST lang.Seq c\<^sub>1 c\<^sub>2"
  "if b then c\<^sub>1 else c\<^sub>2 fi" \<rightharpoonup> "CONST If (CONST test b) c\<^sub>1 c\<^sub>2"
  "if b then c\<^sub>1 fi" \<rightharpoonup> "CONST If (CONST test b) c\<^sub>1 (CONST Skip)"
  "while b inv \<lbrace>P\<rbrace> do c od" \<rightharpoonup> "CONST While (CONST test b) \<guillemotleft>P\<guillemotright> c"
  "while b do c od" \<rightharpoonup> "CONST While (CONST test b) (CONST UNIV) c"
  "R: R G: G P: P {c} Q: Q" \<rightharpoonup> "(\<llangle>R\<rrangle>,\<llangle>G\<rrangle>,\<llangle>P\<rrangle>,c,\<llangle>Q\<rrangle>)"
  "do c while b" \<rightharpoonup> "CONST DoWhile (CONST UNIV) c (CONST test b)"
  "do c inv \<lbrace>P\<rbrace> while b" \<rightharpoonup> "CONST DoWhile \<llangle>P\<rrangle> c (CONST test b)"

fun fn_valid :: "('v,'r,'g,'a) threads \<Rightarrow> bool"
  where 
    "fn_valid [(R,G,P,c,Q)] = (stable\<^sub>t R Q \<and> wellformed R G \<and> guar\<^sub>c c G \<and> (P \<subseteq> wp R c Q))" | 
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
  "\<^sup>aX" \<rightleftharpoons> "X (\<acute>CONST more)"
  "\<^sup>1\<^sup>aX" \<rightleftharpoons> "X (CONST more (\<acute>CONST fst))"
  "\<^sup>2\<^sup>aX" \<rightleftharpoons> "X (CONST more (\<acute>CONST snd))"

definition c_and (infixr "&&" 35)
  where "c_and e\<^sub>1 e\<^sub>2 = Exp (\<lambda>x. x ! 0 \<and> x ! 1) [e\<^sub>1,e\<^sub>2]"

definition c_eq (infixl "==" 50)
  where "c_eq e\<^sub>1 e\<^sub>2 = Exp (\<lambda>x. if x ! 0 = x ! 1 then 1 else 0) [e\<^sub>1,e\<^sub>2]"

end