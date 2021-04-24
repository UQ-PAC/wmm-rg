theory Sequence_Lock
  imports ARMv8_Comp
begin

datatype register = r\<^sub>1 | r\<^sub>2 | r\<^sub>3 | r\<^sub>4 | r\<^sub>z | r\<^sub>x

type_synonym ('v,'r) gexp  = "('v,'r) state \<Rightarrow> 'v"
type_synonym ('v,'r) rexp  = "('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> 'v"

definition val :: "nat \<Rightarrow> (nat,'b) gexp" ("(#_)" [70] 61)
  where "val I \<equiv> \<lambda>m. I"

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
  "_Load"  :: "'b \<Rightarrow> 'b \<Rightarrow> (nat,'b) lang" ("(_ := [_])" [70, 65] 61)
  "_Store" :: "'b \<Rightarrow> 'b \<Rightarrow> (nat,'b) lang" ("([_] := _)" [70, 65] 61)
  "_StoreI" :: "(nat,'b) pred \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> (nat,'b) lang" ("(\<lbrace>_\<rbrace> [_] := _)" [20, 70, 65] 61)
  "_Assert" :: "(nat,'b) pred \<Rightarrow> (nat,'b) lang" ("(\<lparr>_\<rparr>)" [20] 61)
  "_Test" :: "(nat,'b) pred \<Rightarrow> (nat,'b) lang" ("(\<lbrakk>_\<rbrakk>)" [20] 61)
  "_Fence" :: "(nat,'b) lang" ("(fence)" 61)
  "_AddI"  :: "'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> (nat,'b) lang" ("(_ := _ + #_)" [70, 65, 65] 61)
  "_MovI"  :: "'b \<Rightarrow> nat \<Rightarrow> (nat,'b) lang" ("(_ := #_)" [70, 65] 61)
  "_Seq"   :: "(nat,'b) lang \<Rightarrow> (nat,'b) lang \<Rightarrow> (nat,'b) lang" ("(_;/ _)" [60,61] 60)
  "_While" :: "((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b) pred \<Rightarrow> (nat,'b) lang \<Rightarrow> (nat,'b) lang" 
                ("(while _/ inv \<lbrace>_\<rbrace> //do _ /od)"   [0,0,0] 61)
  "_DoWhile" :: "(nat,'b) pred \<Rightarrow> (nat,'b) lang \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b) lang" 
                ("(1do _/ inv \<lbrace>_\<rbrace> //while _)"  [0,0,100] 61)
  "_WhileT" :: "((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b) pred \<Rightarrow> (nat,'b) lang \<Rightarrow> (nat,'b) lang" 
                ("(while _ //do _ /od)"   [0,0] 61)
  "_DoWhileT" :: "(nat,'b) pred \<Rightarrow> (nat,'b) lang \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp) \<Rightarrow> (nat,'b) lang" 
                ("(1do _ //while _)"  [0,100] 61)
  "_Spec" :: "('v,'r) rpred \<Rightarrow> ('v,'r) rpred \<Rightarrow> ('v,'r) pred \<Rightarrow> ('v,'r) lang \<Rightarrow> ('v,'r) pred \<Rightarrow> ('v,'r) thread"
                ("(R: _ //G:_ //P: _ //{ _ } //Q: _)" [0,0,0,0] 61)

definition addI
  where "addI I \<equiv> \<lambda>x. x ! 0 + I"

definition movI
  where "movI I \<equiv> \<lambda>x. I"

definition ODD :: "'b \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp)"
  where "ODD r = (Exp (\<lambda>x. x ! 0 mod 2) [Reg r], (=), Val 1)"

definition NEQ :: "'b \<Rightarrow> 'b \<Rightarrow> ((nat,'b) exp \<times> (nat \<Rightarrow> nat \<Rightarrow> bool) \<times> (nat,'b) exp)"
  where "NEQ r1 r2 = (Reg r1, (\<noteq>), Reg r2)"

translations
  "x := [a]" \<rightharpoonup> "CONST Load (CONST PTrue) a x"
  "[a] := x" \<rightharpoonup> "CONST Store (CONST PTrue) a x"
  "\<lbrace>P\<rbrace> [a] := x" \<rightharpoonup> "CONST Store  \<guillemotleft>P\<guillemotright> a x"
  "X := Y + #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST addI I) [CONST Reg Y])"
  "X := #I" \<rightharpoonup> "CONST Op X (CONST Exp (CONST movI I) [])"
  "\<lparr>P\<rparr>" \<rightharpoonup> "CONST Test \<guillemotleft>P\<guillemotright>"
  "\<lbrakk>P\<rbrakk>" \<rightharpoonup> "CONST Assert \<guillemotleft>P\<guillemotright>"
  "fence" \<rightharpoonup> "CONST Fence"
  "c\<^sub>1 ; c\<^sub>2" \<rightharpoonup> "CONST Seq c\<^sub>1 c\<^sub>2"
  "while T inv \<lbrace>P\<rbrace> do c od" \<rightharpoonup> "CONST While (CONST fst T) (CONST fst (CONST snd T)) (CONST snd (CONST snd T)) \<guillemotleft>P\<guillemotright> c"
  "do c inv \<lbrace>P\<rbrace> while T" \<rightharpoonup> "CONST DoWhile \<guillemotleft>P\<guillemotright> c (CONST fst T) (CONST fst (CONST snd T)) (CONST snd (CONST snd T))"
  "while T do c od" \<rightharpoonup> "CONST While (CONST fst T) (CONST fst (CONST snd T)) (CONST snd (CONST snd T)) (CONST PTrue) c"
  "do c while T" \<rightharpoonup> "CONST DoWhile (CONST PTrue) c (CONST fst T) (CONST fst (CONST snd T)) (CONST snd (CONST snd T))"
  "R: R G: G P: P {c} Q: Q" \<rightharpoonup> "(\<guillemotleft>R\<guillemotright>,\<guillemotleft>G\<guillemotright>,\<guillemotleft>P\<guillemotright>,c,\<guillemotleft>Q\<guillemotright>)"

nonterminal prgs

syntax
  "_PAR"        :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" 60)
  "_prg"        :: "'a \<Rightarrow> prgs"              ("_" 57)
  "_prgs"       :: "['a, prgs] \<Rightarrow> prgs"      ("_//\<parallel>//_" [60,57] 57)

definition com_valid :: "('v,'r) threads \<Rightarrow> bool"
  where "com_valid t \<equiv> validity (Cs t) (state (Ps t)) (step\<^sub>G (Rs t)) (step\<^sub>G (Gs t)) (state (Qs t))"

translations
  "_prg a" \<rightharpoonup> "[a]"
  "_prgs a ps" \<rightharpoonup> "a # ps"
  "_PAR t" \<rightharpoonup> "CONST com_valid t"

syntax
  "_reg" :: "id \<Rightarrow> 'a" ("\<ordmasculine>_")
  "_orig" :: "nat \<Rightarrow> 'a" ("\<ordmasculine>[_]" [100] 1000)
  "_prime" :: "nat \<Rightarrow> 'a" ("\<ordfeminine>[_]" [100] 1000)
  "_const" :: "nat \<Rightarrow> 'a" ("=[_]" [100] 1000)

translations
  "\<ordmasculine>X" \<rightleftharpoons> "(\<acute>CONST snd) X"
  "\<ordmasculine>[X]" \<rightleftharpoons> "(\<acute>CONST fst) X"
  "\<ordfeminine>[X]" \<rightleftharpoons> "(\<acute>CONST snd) X"
  "=[X]" \<rightharpoonup> "(\<acute>CONST snd) X = (\<acute>CONST fst) X"

lemma stabilize_true [simp]:
  "stabilize R (\<lambda>m. True) = (\<lambda>m. True)"
  unfolding stabilize_def by auto

lemma sequence_lock:
   "Z < X \<Longrightarrow>
    COBEGIN
      R: =[Z] \<and> =[X] \<and> =[Suc X]
      G: \<ordmasculine>[Z] \<le> \<ordfeminine>[Z] \<and> ((even \<ordmasculine>[Z] \<and> =[Z]) \<longrightarrow> (=[X] \<and> =[Suc X])) \<and> ((even \<ordmasculine>[Z] \<longrightarrow> P \<ordmasculine>[X] \<ordmasculine>[Suc X]) \<longrightarrow> (even \<ordfeminine>[Z] \<longrightarrow> P \<ordfeminine>[X] \<ordfeminine>[Suc X]))
      P: even \<ordmasculine>[Z]
      {
        \<lparr>P \<ordmasculine>r\<^sub>2 \<ordmasculine>r\<^sub>3\<rparr>;
        r\<^sub>z := #Z;
        r\<^sub>x := #X;
        r\<^sub>1 := [r\<^sub>z];
        r\<^sub>1 := r\<^sub>1 + #1;
        \<lbrace>\<ordmasculine>r\<^sub>z = Z \<and> \<ordmasculine>r\<^sub>1 = \<ordmasculine>[Z] + 1 \<and> even \<ordmasculine>[Z]\<rbrace> [r\<^sub>z] := r\<^sub>1;
        fence;
        \<lbrace>\<ordmasculine>r\<^sub>x = X \<and> odd \<ordmasculine>[Z]\<rbrace> [r\<^sub>x] := r\<^sub>2;
        r\<^sub>x := r\<^sub>x + #1;
        \<lbrace>\<ordmasculine>r\<^sub>x = Suc X \<and> odd \<ordmasculine>[Z]\<rbrace> [r\<^sub>x] := r\<^sub>3;
        fence;
        r\<^sub>1 := [r\<^sub>z];
        r\<^sub>1 := r\<^sub>1 + #1;
        \<lbrace>\<ordmasculine>r\<^sub>z = Z \<and> \<ordmasculine>r\<^sub>1 = \<ordmasculine>[Z] + 1 \<and> P \<ordmasculine>[X] \<ordmasculine>[Suc X]\<rbrace> [r\<^sub>z] := r\<^sub>1 
      }
      Q: True 
    \<parallel>
      R: \<ordmasculine>[Z] \<le> \<ordfeminine>[Z] \<and> ((even \<ordmasculine>[Z] \<and> =[Z]) \<longrightarrow> (=[X] \<and> =[Suc X])) \<and> ((even \<ordmasculine>[Z] \<longrightarrow> P \<ordmasculine>[X] \<ordmasculine>[Suc X]) \<longrightarrow> (even \<ordfeminine>[Z] \<longrightarrow> P \<ordfeminine>[X] \<ordfeminine>[Suc X]))
      G: =[Z] \<and> =[X] \<and> =[Suc X]
      P: even \<ordmasculine>[Z] \<longrightarrow> P \<ordmasculine>[X] \<ordmasculine>[Suc X]
      {
        r\<^sub>z := #Z;
        do
          do
            r\<^sub>1 := [r\<^sub>z]
          inv \<lbrace> \<ordmasculine>r\<^sub>z = Z \<and> (even \<ordmasculine>[Z] \<longrightarrow> P \<ordmasculine>[X] \<ordmasculine>[Suc X]) \<rbrace>
          while (ODD r\<^sub>1);
          fence;
          r\<^sub>x := #X;
          r\<^sub>2 := [r\<^sub>x];
          r\<^sub>x := r\<^sub>x + #1;
          r\<^sub>3 := [r\<^sub>x];
          fence;
          r\<^sub>4 := [r\<^sub>z]
        inv \<lbrace> \<ordmasculine>r\<^sub>z = Z \<and> (even \<ordmasculine>[Z] \<longrightarrow> P \<ordmasculine>[X] \<ordmasculine>[Suc X]) \<rbrace>
        while (NEQ r\<^sub>1 r\<^sub>4);
        \<lbrakk>P \<ordmasculine>r\<^sub>2 \<ordmasculine>r\<^sub>3\<rbrakk>
      }
      Q: True
    COEND"
  unfolding com_valid_def
  apply (rule armv8_sound)
  apply simp (* at least 1 thread *)
  unfolding wfs_def
   apply (clarsimp split: prod.splits)
  apply (intro conjI)
  apply (simp add: wellformed_def stable_def reflexive_def transitive_def) (* wf *)
  defer 1 (* interference *)
  defer 1 (* wp *)
  apply (simp add: wellformed_def stable_def reflexive_def transitive_def) (* wf *)
  apply auto[1] (* wf *)
  defer 1 (* interference *)
  defer 1 (* wp *)
  unfolding rg_comp_def
  apply clarsimp
  apply (subgoal_tac "(i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0)")
  apply (elim disjE)
  apply clarsimp
  apply clarsimp
  apply auto[1] (* composition *)
  prefer 2 (* wp for write operation *)

  apply (clarsimp simp: pair_upd1_def pair_upd2_def movI_def addI_def pred_defs stabilize_def split: prod.splits)

  prefer 3 (* wp for read operation *)

  apply (clarsimp simp: NEQ_def ODD_def pair_upd1_def pair_upd2_def movI_def addI_def pred_defs stabilize_def split: prod.splits)
  apply (subgoal_tac "g'b (b r\<^sub>z) = g'c (b r\<^sub>z)")
  apply clarsimp
  apply linarith

  sorry (* interference analysis *)

end