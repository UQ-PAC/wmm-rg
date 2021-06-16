theory Chase_Lev
  imports "../ARMv8_Syntax"
begin

section \<open>Abstract Queue Theory\<close>

record chase_lev = deque :: "nat list"

text \<open>Helper lemma for mod properties\<close>
lemma mod_neq:
  "x > y \<Longrightarrow> x - y < L \<Longrightarrow> (x :: nat) mod L \<noteq> y mod L"
  using mod_eq_dvd_iff_nat by auto

subsection \<open>Generate a list of all numbers from X to Y\<close>

function gen :: "nat \<Rightarrow> nat \<Rightarrow> nat list"
  where "gen X Y = (if X \<ge> Y then [] else [X]@(gen (Suc X) Y))"
  by auto
termination by (relation "measure (\<lambda>(t,b). b - t)") auto
declare gen.simps [simp del]

lemma [simp]:
  "gen X X = []"
  "gen X (Suc X) = [X]"
  "X < Y \<Longrightarrow> gen X Y = X#gen (Suc X) Y"
  "X \<ge> Y \<Longrightarrow> gen X Y = []"
  by (subst gen.simps, auto)+ 

lemma [simp]:
  "gen X (Suc Y) = (if X \<le> Y then (gen X Y)@[Y] else [])"
proof (induct "Y - X" arbitrary: X Y)
  case 0
  then show ?case by (subst gen.simps, auto)
next
  case (Suc Z)
  hence a: "Z = Y - Suc X" "X < Suc Y" by auto
  then show ?case using Suc(1)[OF a(1)] by auto
qed

lemma [simp]:
  "x \<in> set (gen X Y) = (X \<le> x \<and> x < Y)"
proof (induct "Y - X" arbitrary: X Y)
  case 0
  then show ?case by (subst gen.simps) auto
next
  case (Suc Z)
  hence a: "Z = Y - Suc X" "X < Y" by auto
  show ?case using a(2) Suc(1)[OF a(1)] by simp linarith
qed

subsection \<open>Abstract Queue\<close>

definition queue :: "nat \<Rightarrow> (nat,'a) gstate \<Rightarrow> nat list"
  where "queue ptr m \<equiv> map (\<lambda>i. st m (ptr + 3 + (i mod st m (ptr + 2)))) (gen (st m ptr) (st m (ptr + 1)))"

section \<open>Example\<close>

definition steal
  where "steal v = {(A,A'). A = v#A'}"

definition steal_any
  where "steal_any = {(A,A'). \<exists>v. A = v#A'}"

definition put
  where "put v = {(A,A'). A' = A@[v]}"

lemma chase_lev_put:
   "TOP = PTR \<Longrightarrow> BOT = PTR + 1 \<Longrightarrow> LEN = PTR + 2 \<Longrightarrow> BUF = PTR + 3 \<Longrightarrow> 
    (\<forall>a b t. (a,b) \<in> S\<^sup>* \<longrightarrow> (a@t,b@t) \<in> S\<^sup>*) \<Longrightarrow>
    FNBEGIN
      R: =[BOT] \<and> \<le>[TOP] \<and> =[BUF] \<and> =[LEN] \<and> =[(BUF + (\<^sup>1[BOT] mod \<^sup>1[LEN]))] \<and> (\<^sup>1\<^sup>adeque,\<^sup>2\<^sup>adeque) \<in> S\<^sup>*
      G: \<le>[BOT] \<and> =[TOP] \<and> =[LEN]
      I: \<^sup>adeque = \<acute>(queue PTR) \<and> \<^sup>s[TOP] \<le> \<^sup>s[BOT]
      P: \<^sup>rr\<^sub>0 = PTR \<and> V = \<^sup>rr\<^sub>1 \<and> D = \<^sup>adeque \<and> SPACE = (\<^sup>s[BOT] - \<^sup>s[TOP] < \<^sup>s[LEN])
      {
        \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>2 := [r\<^sub>0 + #0];
        \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>3 := [r\<^sub>0 + #1];
        r\<^sub>2 := r\<^sub>3 - r\<^sub>2;
        \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>4 := [r\<^sub>0 + #2];
        if (LE r\<^sub>2 r\<^sub>4) then
          r\<^sub>2 := r\<^sub>3 % r\<^sub>4;
          r\<^sub>2 := r\<^sub>2 + r\<^sub>0;
          r\<^sub>2 := r\<^sub>2 + #3;
          (\<lbrace> \<^sup>rr\<^sub>2 = BUF + (\<^sup>s[BOT] mod \<^sup>s[LEN]) \<and> (\<forall>i. \<^sup>s[TOP] \<le> i \<longrightarrow> \<^sup>s[BOT] - i < \<^sup>s[LEN]) \<rbrace> 
            [r\<^sub>2 + #0] := r\<^sub>1);
          fence;
          r\<^sub>3 := r\<^sub>3 + #1;
          \<lbrace> \<^sup>rr\<^sub>0 = PTR \<and> \<^sup>rr\<^sub>3 = \<^sup>s[BOT]+1 \<and> \<^sup>rr\<^sub>1 = \<^sup>s[BUF + (\<^sup>s[BOT] mod \<^sup>s[LEN])] \<and> (\<forall>i. \<^sup>s[TOP] \<le> i \<longrightarrow> \<^sup>s[BOT] - i < \<^sup>s[LEN]) \<rbrace> 
            [r\<^sub>0 + #1] := r\<^sub>3 :\<^sub>a \<^sup>adeque := \<^sup>adeque@[\<^sup>rr\<^sub>1]
        fi
      }
      Q: (SPACE \<longrightarrow> (D,\<^sup>adeque) \<in> S\<^sup>* O (put V) O S\<^sup>*)
    FNEND"
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q + Wellformedness of R & G *)
  apply (auto simp: step\<^sub>t_def stable_def)[1]
  apply (metis glb_def gstate_rec.select_convs(2) relcomp.relcompI rtrancl_idemp_self_comp)
  apply (auto simp: step\<^sub>t_def stable_def reflexive_def transitive_def)[3]

  (* Guarantees of each atomic action *)
  apply (clarsimp simp: addI_def inv2_def step_def glb_def wp\<^sub>r_def)
  apply (intro conjI; clarsimp simp: queue_def; metis mod_neq)

  (* WP *)

  (* Interference *)

  sorry


lemma chase_lev_steal:
   "TOP = PTR \<Longrightarrow> BOT = PTR + 1 \<Longrightarrow> LEN = PTR + 2 \<Longrightarrow> BUF = PTR + 3 \<Longrightarrow> 
    FNBEGIN
      R: \<le>[TOP] \<and> =[LEN] \<and> (\<^sup>1\<^sup>adeque,\<^sup>2\<^sup>adeque) \<in> S\<^sup>*
      G: =[BOT] \<and> \<le>[TOP] \<and> =[LEN] \<and> (\<^sup>1[TOP] \<le> \<^sup>1[BOT] \<longrightarrow> \<^sup>2[TOP] \<le> \<^sup>2[BOT])
      I: \<^sup>adeque = \<acute>(queue PTR)
      P: \<^sup>rr\<^sub>0 = PTR \<and> A = \<^sup>adeque
      {
        \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>1 := [r\<^sub>0 + #0];
        fence;
        \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>2 := [r\<^sub>0 + #1];
        if (LE r\<^sub>1 r\<^sub>2) 
        then
          \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>2 := [r\<^sub>0 + #2];
          r\<^sub>2 := r\<^sub>1 % r\<^sub>2;
          r\<^sub>2 := r\<^sub>2 + r\<^sub>0;
          cfence;
          (\<lbrace> (\<exists>i. \<^sup>rr\<^sub>1 \<le> i \<and> i \<le> \<^sup>s[TOP] \<and> \<^sup>rr\<^sub>2 = PTR + (i mod \<^sup>s[LEN])) \<rbrace> 
            r\<^sub>2 := [r\<^sub>2 + #3]);
          r\<^sub>3 := r\<^sub>1 + #1;
          (\<lbrace> \<^sup>rr\<^sub>3 = \<^sup>rr\<^sub>1 + 1 \<and> \<^sup>rr\<^sub>0 = TOP \<and> \<^sup>rr\<^sub>1 < \<^sup>s[BOT] \<rbrace> 
            r\<^sub>3 := cas r\<^sub>0 r\<^sub>1 r\<^sub>3, \<^sup>adeque := drop 1 \<^sup>adeque);
          if (Z r\<^sub>3) then r\<^sub>2 := #ABORT fi
        else
          r\<^sub>2 := #EMPTY
        fi
      }
      Q: ( (\<^sup>rr\<^sub>2 \<noteq> EMPTY \<and> \<^sup>rr\<^sub>2 \<noteq> ABORT) \<longrightarrow> (A,\<^sup>adeque) \<in> S\<^sup>* O (steal \<^sup>rr\<^sub>2) O S\<^sup>* )
    FNEND" 
  sorry

lemma chase_lev_take:
   "TOP = BASE \<Longrightarrow> BOT = BASE + 1 \<Longrightarrow> LEN = BASE + 2 \<Longrightarrow> BUF = BASE + 3 \<Longrightarrow> 
    COBEGIN
      R: =[BOT] \<and> \<le>[TOP] \<and> =[LEN]
      G: \<le>[TOP] \<and> =[LEN]
      I: \<^sup>adeque = \<acute>(buffer BASE)
      P: True
      {
        r\<^sub>0 := #BASE;
        r\<^sub>1 := r\<^sub>0 + #1;
        r\<^sub>2 := [r\<^sub>1];
        r\<^sub>2 := r\<^sub>2 - #1;
        [r\<^sub>1] := r\<^sub>2;
        fence;
        r\<^sub>3 := [r\<^sub>0];
        if (LEQ r\<^sub>3 r\<^sub>2) then
          r\<^sub>4 := r\<^sub>0 + #2;
          r\<^sub>4 := [r\<^sub>4];
          r\<^sub>4 := r\<^sub>2 % r\<^sub>4;
          r\<^sub>4 := r\<^sub>4 + #3;
          r\<^sub>4 := r\<^sub>4 + r\<^sub>0;
          if (EQ r\<^sub>3 r\<^sub>2) then
            r\<^sub>5 := r\<^sub>3 + #1;
            (\<lbrace> True \<rbrace> r\<^sub>5 := cas r\<^sub>0 r\<^sub>3 r\<^sub>5, tstate_rec.more);
            if (Z r\<^sub>5) then r\<^sub>4 := #EMPTY fi;
            r\<^sub>2 := r\<^sub>2 + #1;
            [r\<^sub>1] := r\<^sub>2
          fi
        else
          r\<^sub>4 := #EMPTY;
          r\<^sub>2 := r\<^sub>2 + #1;
          [r\<^sub>1] := r\<^sub>2
        fi
      }
      Q: True
    COEND" 
  sorry

