theory Chase_Lev
  imports Example_Lang
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

lemma queue_cong [cong]:
  "st m = st m' \<Longrightarrow> queue b m = queue b m'"
  unfolding queue_def by auto

section \<open>Example\<close>

definition steal
  where "steal v = {(A,A'). A = v#A'}"

definition put
  where "put v = {(A,A'). A' = A@[v]}"

lemma test1[simp]:
  "st (m(l :=\<^sub>s e)) f = (if l = f then e else st m f)"
  "rg (m(l :=\<^sub>s e)) r = rg m r"
  "rg (m(r :=\<^sub>r e)) f = (if f = r then e else rg m f)"
  by (auto simp: st_upd_def rg_upd_def)

lemma test2[simp]:
  "st (m(aux: a)) e = st m e"
  by (auto simp: aux_upd_def)

lemma chase_lev_push:
   "TOP = PTR \<Longrightarrow> BOT = PTR + 1 \<Longrightarrow> LEN = PTR + 2 \<Longrightarrow> BUF = PTR + 3 \<Longrightarrow> 
    FNBEGIN
      R: =[BOT] \<and> \<le>[TOP] \<and> =[BUF] \<and> =[LEN] \<and> =[(BUF + (\<^sup>1[BOT] mod \<^sup>1[LEN]))] \<and> (\<^sup>1\<^sup>adeque,\<^sup>2\<^sup>adeque) \<in> S\<^sup>*
      G: \<le>[BOT] \<and> =[TOP] \<and> =[LEN]
      I: \<^sup>adeque = \<acute>(queue PTR) \<and> \<^sup>s[TOP] \<le> \<^sup>s[BOT]
      P: \<^sup>rr\<^sub>0 = PTR \<and> V = \<^sup>rr\<^sub>1 \<and> A = \<^sup>adeque \<and> SPACE = (\<^sup>s[BOT] - \<^sup>s[TOP] < \<^sup>s[LEN])
      {
        r\<^sub>2 := [r\<^sub>0];
        r\<^sub>3 := [r\<^sub>0 + #1];
        r\<^sub>2 := r\<^sub>3 - r\<^sub>2;
        r\<^sub>4 := [r\<^sub>0 + #2];
        if (LE r\<^sub>2 r\<^sub>4) then
          r\<^sub>2 := r\<^sub>3 % r\<^sub>4;
          r\<^sub>2 := r\<^sub>2 + r\<^sub>0;
          r\<^sub>2 := r\<^sub>2 + #3;
          \<lbrace> \<^sup>rr\<^sub>2 = BUF + (\<^sup>s[BOT] mod \<^sup>s[LEN]) \<and> \<^sup>s[BOT] - \<^sup>s[TOP] < \<^sup>s[LEN] \<rbrace> 
            [r\<^sub>2 + #0] := r\<^sub>1;
          fence;
          r\<^sub>3 := r\<^sub>3 + #1;
          \<lbrace> \<^sup>rr\<^sub>0 = PTR \<and> \<^sup>rr\<^sub>3 = \<^sup>s[BOT]+1 \<and> \<^sup>rr\<^sub>1 = \<^sup>s[BUF + (\<^sup>s[BOT] mod \<^sup>s[LEN])] \<and> \<^sup>s[BOT] - \<^sup>s[TOP] < \<^sup>s[LEN] \<rbrace> 
            [r\<^sub>0 + #1] := r\<^sub>3, \<^sup>adeque := \<^sup>adeque@[\<^sup>rr\<^sub>1]
        fi
      }
      Q: SPACE \<longrightarrow> (A,\<^sup>adeque) \<in> S\<^sup>* O (put V) O S\<^sup>*
    FNEND" 
  apply (clarsimp simp add: local_props_def, intro conjI)
 
  (* Wellformedness *)
  apply (auto simp add: stable_def step\<^sub>t_def glb_def reflexive_def transitive_def)[4]
  apply (meson relcomp.relcompI rtrancl_trans)

  (* Various load operations *)
  apply (auto simp: step_def wp_defs inv2_def)[3]

  (* Write to buffer *)
  apply (auto simp: step_def st_upd_def glb_def aux_upd_def inv2_def set_glb_def wp_defs queue_def addI_def)[1]
  apply (subgoal_tac "st m (Suc PTR) mod st m (Suc (Suc PTR)) \<noteq> x mod st m (Suc (Suc PTR))")
  apply argo
  apply (rule mod_neq; auto)

  (* Update BOT *)
  apply (auto simp: step_def st_upd_def glb_def inv_def set_glb_def inv2_def aux_upd_def o_def wp_defs queue_def addI_def)[1]
  apply (simp add: add.commute group_cancel.add1)  
  
  (* WP Reasoning *)  
  apply (clarsimp simp add: addR_def addI_def modR_def subR_def LE_def rg_upd_def)
  apply (clarsimp simp add: wp_defs rg_upd_def aux_upd_def st_upd_def)
  apply (clarsimp simp add: stabilize_def glb_def set_glb_def)
  apply safe
  apply auto
  unfolding put_def  
  apply (subgoal_tac "(deque (tstate_rec.more m), deque (gstate_rec.more gd)) \<in> S\<^sup>*")
  apply blast
  apply auto[1]
  apply (subgoal_tac "(deque (tstate_rec.more m), deque (gstate_rec.more gd)) \<in> S\<^sup>*")
  apply blast
  apply auto[1]
  done

lemma chase_lev_steal:
   "TOP = PTR \<Longrightarrow> BOT = PTR + 1 \<Longrightarrow> LEN = PTR + 2 \<Longrightarrow> BUF = PTR + 3 \<Longrightarrow> 
    COBEGIN
      R: \<le>[TOP] \<and> =[LEN] \<and> (\<^sup>1\<^sup>adeque,\<^sup>2\<^sup>adeque) \<in> S\<^sup>*
      G: =[BOT] \<and> \<le>[TOP] \<and> =[LEN] \<and> (\<^sup>1[TOP] \<le> \<^sup>1[BOT] \<longrightarrow> \<^sup>2[TOP] \<le> \<^sup>2[BOT])
      I: \<^sup>adeque = \<acute>(queue BASE)
      P: \<^sup>rr\<^sub>0 = PTR \<and> V = \<^sup>rr\<^sub>1 \<and> A = \<^sup>adeque
      {
        r\<^sub>0 := #BASE;
        r\<^sub>1 := [r\<^sub>0];
        fence;
        r\<^sub>2 := r\<^sub>0 + #1;
        r\<^sub>2 := [r\<^sub>2];
        if (LE r\<^sub>1 r\<^sub>2) 
        then
          r\<^sub>2 := r\<^sub>0 + #2;
          r\<^sub>2 := [r\<^sub>2];
          r\<^sub>2 := r\<^sub>1 % r\<^sub>2;
          r\<^sub>2 := r\<^sub>2 + #3;
          r\<^sub>2 := r\<^sub>2 + r\<^sub>0;
          cfence;
          r\<^sub>2 := [r\<^sub>2];
          r\<^sub>3 := r\<^sub>1 + #1;
          (\<lbrace>\<^sup>rr\<^sub>3 = \<^sup>rr\<^sub>1 + 1 \<and> \<^sup>rr\<^sub>0 = TOP \<and> \<^sup>rr\<^sub>1 < \<^sup>s[BOT]\<rbrace> 
            r\<^sub>3 := cas r\<^sub>0 r\<^sub>1 r\<^sub>3 , \<^sup>adeque := (case \<^sup>adeque of x#t \<Rightarrow> t));
          if (Z r\<^sub>3) then r\<^sub>2 := #ABORT else Skip fi
        else
          r\<^sub>2 := #EMPTY
        fi
      }
      Q: (\<^sup>rr\<^sub>2 \<noteq> EMPTY \<and> \<^sup>rr\<^sub>2 \<noteq> ABORT) \<longrightarrow> (A,\<^sup>adeque) \<in> S\<^sup>* O (steal \<^sup>rr\<^sub>2) O S\<^sup>*
    COEND" 
  sorry

lemma chase_lev_take:
   "TOP = BASE \<Longrightarrow> BOT = BASE + 1 \<Longrightarrow> LEN = BASE + 2 \<Longrightarrow> BUF = BASE + 3 \<Longrightarrow> 
    COBEGIN
      R: =[BOT] \<and> \<le>[TOP] \<and> =[LEN]
      G: \<le>[TOP] \<and> =[LEN] \<and> (\<^sup>1[TOP] \<le> \<^sup>1[BOT] \<longrightarrow> \<^sup>2[TOP] \<le> \<^sup>2[BOT])
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

