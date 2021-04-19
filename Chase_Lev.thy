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

definition steal_any
  where "steal_any = {(A,A'). \<exists>v. A = v#A'}"

definition put
  where "put v = {(A,A'). A' = A@[v]}"

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

lemma stabilize_mono:
  "P \<turnstile>\<^sub>p Q \<Longrightarrow> stabilize R P  \<turnstile>\<^sub>p stabilize R Q"
  unfolding stabilize_def pred_defs by auto

lemma pre_mono:
  "P \<turnstile>\<^sub>p Q \<Longrightarrow> wpre a P \<turnstile>\<^sub>p wpre a Q"
  by (cases a) (auto intro: stabilize_mono simp: pred_defs)

lemma chain_mono:
  "P \<turnstile>\<^sub>p Q \<Longrightarrow> chain xs P \<turnstile>\<^sub>p chain xs Q"
  by (induct xs arbitrary: P Q) (auto simp: pre_mono stabilize_mono chain.simps)

lemma chain1_wpre:
  "P \<turnstile>\<^sub>p chain xs (wpre a Q) \<Longrightarrow> P \<turnstile>\<^sub>p chain (a#xs) Q"
  unfolding chain.simps .

lemma chain1_stab:
  "P \<turnstile>\<^sub>p chain xs (stabilize R Q) \<Longrightarrow> P \<turnstile>\<^sub>p chain (env R#xs) Q"
  unfolding chain.simps by auto

lemma chain0:
  "P \<turnstile>\<^sub>p Q \<Longrightarrow> P \<turnstile>\<^sub>p  chain [] Q"
  unfolding chain.simps .

lemma trans_flip: "\<And>a b c. b \<turnstile>\<^sub>p c \<Longrightarrow> a \<turnstile>\<^sub>p b \<Longrightarrow> a \<turnstile>\<^sub>p c"
  by (auto simp: pred_defs)

lemma chain1_full:
  assumes "Q' \<turnstile>\<^sub>p wpre a P"
  assumes "Q'' \<turnstile>\<^sub>p chain xs Q'"
  shows "Q'' \<turnstile>\<^sub>p chain (a#xs) P"
  apply (rule chain1_wpre)
  apply (rule trans_flip)
  apply (rule chain_mono)
  apply (rule trans_flip)
  apply (rule pre_mono)
  using assms by auto

lemma chain_extend:
  "P \<turnstile>\<^sub>p chain xs (Q \<and>\<^sub>p X) \<Longrightarrow> P \<turnstile>\<^sub>p chain xs Q"
  using chain_mono[of "Q \<and>\<^sub>p X" Q] by (auto simp: pred_defs)

lemma chain_rewrite:
  "X \<turnstile>\<^sub>p Q \<Longrightarrow> P \<turnstile>\<^sub>p chain xs X \<Longrightarrow> P \<turnstile>\<^sub>p chain xs Q"
  using chain_mono unfolding pred_defs by blast

definition str where
  "str R P \<equiv> if stabilize R P = P then P else True\<^sub>p"

lemma str_mono:
  "Q \<turnstile>\<^sub>p P \<Longrightarrow> Q \<turnstile>\<^sub>p str R P"
  unfolding str_def by (auto simp: pred_defs)

subsection \<open>Trivial Cases\<close>

named_theorems trivial_thms
declare subset_UNIV [trivial_thms]

lemma [trivial_thms]: "stabilize R True\<^sub>p = True\<^sub>p"
  unfolding stabilize_def by simp

lemma [trivial_thms]: "wpre a True\<^sub>p = True\<^sub>p"
  by (cases a) (auto simp:)

lemma [trivial_thms]:
  "chain xs True\<^sub>p = True\<^sub>p"
  by (induct xs) (auto simp: trivial_thms chain.simps)

lemma stabilize_univ:
  "True\<^sub>p \<turnstile>\<^sub>p stabilize R True\<^sub>p"
  unfolding stabilize_def by auto

lemma stabilize_str:
  "str R P \<turnstile>\<^sub>p stabilize R (str R P)"
  unfolding str_def stabilize_def by simp

lemma stabilize_trivial:
  "\<forall>m m'. P m \<longrightarrow> R (glb m, glb m') \<longrightarrow> rg m' = rg m \<longrightarrow> P m' \<Longrightarrow> str R P \<turnstile>\<^sub>p stabilize R P"
  apply (subgoal_tac "str R (P \<and>\<^sub>p True\<^sub>p) \<turnstile>\<^sub>p stabilize R (P)")
  apply simp
  sorry

method stabilize_trivial_tac = (rule order_antisym; clarsimp)

method pre_tac =
  (match conclusion in "Q \<subseteq> pre \<alpha> UNIV" for \<alpha> S Q \<Rightarrow> \<open>succeed\<close>, rule pre_univ) |
  (match conclusion in "Q \<subseteq> pre \<alpha> (str R P)" for \<alpha> S Q R P \<Rightarrow> \<open>succeed\<close>, pre_str_tac) |
  (match conclusion in "Q \<subseteq> pre \<alpha> P" for Q \<alpha> S P \<Rightarrow> \<open>succeed\<close>, pre_expand)

method str_tac = 
  (match conclusion in "Q \<turnstile>\<^sub>p stabilize R True\<^sub>p" for Q R \<Rightarrow> \<open>succeed\<close>, rule stabilize_univ) |
  (match conclusion in "Q \<turnstile>\<^sub>p stabilize R (str R P)" for Q R P \<Rightarrow> \<open>succeed\<close>, rule stabilize_str) |
  (rule stabilize_trivial, solves \<open>stabilize_trivial_tac\<close>) 


(*
method solver =
  (match conclusion in "Q \<turnstile>\<^sub>p chain R [] P" for Q R P \<Rightarrow> \<open>rule chain0, (simp )?\<close>) |
  (match conclusion in "Q \<turnstile>\<^sub>p chain R xs P" for Q R xs P \<Rightarrow> 
    \<open>rule chain1_full, solves \<open>pre_tac\<close>, solver\<close>) 
*)

named_theorems break

lemma [break]: "stabilize R (P \<and>\<^sub>p Q) = (stabilize R P \<and>\<^sub>p stabilize R Q)"
  unfolding stabilize_def by auto

lemma [break]: "wpre a (P \<and>\<^sub>p Q) = (wpre a P \<and>\<^sub>p wpre a Q)"
  by (cases a, auto)

lemma [break]: "(P \<turnstile>\<^sub>p Q \<and>\<^sub>p Q') = ((P \<turnstile>\<^sub>p Q) \<and> (P \<turnstile>\<^sub>p Q'))"
  by (auto simp: pred_defs)

lemma [break]: "(P \<turnstile>\<^sub>p chain a (Q \<and>\<^sub>p Q')) = ((P \<turnstile>\<^sub>p chain a Q) \<and> (P \<turnstile>\<^sub>p chain a Q'))"
  sorry

declare wpre.simps [simp del]

method breakdown = 
  (simp add: wp_def break; intro conjI)

method pre_expand = 
  ((simp add: pre_defs guar_def
        del: Orderings.order_top_class.top.extremum
      split: iden.splits if_splits splits prod.splits)?; (rule subset_refl)?)

method pre_str_tac =
  (rule pre_str, solves \<open>pre_expand\<close>) | 
  (rule pre_str_mod, pre_expand)

method pre_tac =
  (match conclusion in "Q \<subseteq> pre \<alpha> S UNIV" for \<alpha> S Q \<Rightarrow> \<open>succeed\<close>, rule pre_univ) |
  (match conclusion in "Q \<subseteq> pre \<alpha> S (str R P)" for \<alpha> S Q R P \<Rightarrow> \<open>succeed\<close>, pre_str_tac) |
  (match conclusion in "Q \<subseteq> pre \<alpha> S P" for Q \<alpha> S P \<Rightarrow> \<open>succeed\<close>, pre_expand)

method solver =
  (match conclusion in "Q \<turnstile>\<^sub>p chain [] P" for Q P \<Rightarrow> \<open>rule chain0, (rule str_mono)?, (simp only: trivial_thms)?\<close>) |
  (match conclusion in "Q \<turnstile>\<^sub>p chain xs P" for Q xs P \<Rightarrow> 
    \<open>rule chain1_full, solves \<open>str_tac\<close>, solves \<open>pre_tac\<close>, solver\<close>) 

lemma ir_str:
  "str R (wpre (ir r e) Q) \<turnstile>\<^sub>p wpre (ir r e) (str R Q)"
  unfolding str_def pred_defs
proof (clarsimp simp: wpre.simps)
  fix m assume b: "stabilize R Q = Q" "stabilize R (\<lambda>m. Q (m(r :=\<^sub>r ev (rg m) e))) \<noteq>
         (\<lambda>m. Q (m(r :=\<^sub>r ev (rg m) e)))"
  hence a: "(\<lambda>m. \<forall>g. R (glb m, g) \<longrightarrow> Q (set_glb m g)) = Q" by (auto simp: stabilize_def)
  have "(\<lambda>m. \<forall>g. R (glb m, g) \<longrightarrow> Q (set_glb m g)) o (\<lambda>m. m(r :=\<^sub>r ev (rg m) e)) = 
         (\<lambda>m. Q (m(r :=\<^sub>r ev (rg m) e)))"
    unfolding a by auto
  hence "(\<lambda>m. \<forall>g. R (glb (m(r :=\<^sub>r ev (rg m) e)), g) \<longrightarrow> Q (set_glb (m(r :=\<^sub>r ev (rg m) e)) g)) = 
         (\<lambda>m. Q (m(r :=\<^sub>r ev (rg m) e)))"
    by (auto simp: o_def)
  hence "stabilize R (\<lambda>m. Q (m(r :=\<^sub>r ev (rg m) e))) = (\<lambda>m. Q (m(r :=\<^sub>r ev (rg m) e)))"
    unfolding stabilize_def
    by (auto simp: set_glb_def rg_upd_def)
  thus "Q (m(r :=\<^sub>r ev (rg m) e))" using b by simp
qed

lemma cm_str:
  "str R (wpre (cm b) Q) \<turnstile>\<^sub>p wpre (cm b) (str R Q)"
  unfolding str_def pred_defs
proof (clarsimp simp: wpre.simps)
  fix m assume b: "stabilize R Q = Q" "stabilize R (\<lambda>m. ev\<^sub>B (rg m) b \<longrightarrow> Q m) \<noteq>
         (\<lambda>m. ev\<^sub>B (rg m) b \<longrightarrow> Q m)"
  have "\<forall>m'. (\<lambda>m. \<forall>g. R (glb m, g) \<longrightarrow> Q (set_glb m g)) m' = Q m'" 
    by (metis (full_types) b(1) stabilize_def) 
  hence "\<forall>m. ((\<lambda>m. ev\<^sub>B (rg m) b) \<longrightarrow>\<^sub>p (\<lambda>m'. \<forall>g. R (glb m', g) \<longrightarrow> Q (set_glb m' g))) m = 
         (\<lambda>m. ev\<^sub>B (rg m) b \<longrightarrow> Q m) m" by simp
  hence "stabilize R (\<lambda>m. ev\<^sub>B (rg m) b \<longrightarrow> Q m) = (\<lambda>m. ev\<^sub>B (rg m) b \<longrightarrow> Q m)"
    unfolding stabilize_def apply (auto simp: set_glb_def glb_def) 
    by meson
  thus "Q m" using b(2) by auto
qed

lemma st_str:
  "\<forall>m m'. wpre (sr v x e a) Q m \<longrightarrow> R (glb m, glb m') \<longrightarrow> rg m' = rg m \<longrightarrow> wpre (sr v x e a) Q m' \<Longrightarrow>
    str R (wpre (sr v x e a) Q) \<turnstile>\<^sub>p wpre (sr v x e a) (str R Q)"
  unfolding str_def pred_defs
  sorry

lemma ld_str:
  "\<forall>m m'. wpre (ld v x e a) Q m \<longrightarrow> R (glb m, glb m') \<longrightarrow> rg m' = rg m \<longrightarrow> wpre (ld v x e a) Q m' \<Longrightarrow>
    str R (wpre (ld v x e a) Q) \<turnstile>\<^sub>p wpre (ld v x e a) (str R Q)"
  unfolding str_def pred_defs
  sorry


lemma env_str:
  "str R Q \<turnstile>\<^sub>p wpre (env R) (str R Q)"
  sorry


lemma chase_lev_put:
   "TOP = PTR \<Longrightarrow> BOT = PTR + 1 \<Longrightarrow> LEN = PTR + 2 \<Longrightarrow> BUF = PTR + 3 \<Longrightarrow> 
    (\<forall>a b t. (a,b) \<in> S\<^sup>* \<longrightarrow> (a@t,b@t) \<in> S\<^sup>*) \<Longrightarrow>
    FNBEGIN
      R: =[BOT] \<and> \<le>[TOP] \<and> =[BUF] \<and> =[LEN] \<and> =[(BUF + (\<^sup>1[BOT] mod \<^sup>1[LEN]))] \<and> (\<^sup>1\<^sup>adeque,\<^sup>2\<^sup>adeque) \<in> S\<^sup>*
      G: \<le>[BOT] \<and> =[TOP] \<and> =[LEN]
      I: \<^sup>adeque = \<acute>(queue PTR) \<and> \<^sup>s[TOP] \<le> \<^sup>s[BOT]
      P: \<^sup>rr\<^sub>0 = PTR \<and> V = \<^sup>rr\<^sub>1 \<and> A = \<^sup>adeque \<and> SPACE = (\<^sup>s[BOT] - \<^sup>s[TOP] < \<^sup>s[LEN])
      {
        \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>2 := [r\<^sub>0 + #0];
        \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>3 := [r\<^sub>0 + #1];
        r\<^sub>2 := r\<^sub>3 - r\<^sub>2;
        \<lbrace> \<^sup>rr\<^sub>0 = PTR \<rbrace> r\<^sub>4 := [r\<^sub>0 + #2];
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
  prefer 10

  apply (simp add: break, intro conjI; simp only: append.simps chain_singleI' chain_singleI chain_lastI)

  apply (rule chain1_full)
  apply (blast)
  apply (simp add: wpre.simps)
  apply (simp add: break, intro conjI)
  sorry

  apply (rule chain1_full)
  apply (simp add: wpre.simps)
  apply (rule stabilize_trivial)
  apply (auto simp: glb_def aux_upd_def o_def st_upd_def)[1]
  apply (meson relcomp.relcompI transitive_closure_trans(3))

  apply (rule chain1_full)
  apply (rule ir_str)
  apply (simp add: wpre.simps rg_upd_def addI_def)

  apply (rule chain1_full)
  apply (rule st_str)
  apply (auto simp: glb_def aux_upd_def o_def st_upd_def wpre.simps)[1]
  apply (meson relcomp.relcompI transitive_closure_trans(3))
  apply (auto simp add: wpre.simps rg_upd_def st_upd_def aux_upd_def addI_def)[1]

  apply (rule chain1_full)
  apply (rule env_str)

  apply (rule chain1_full)
  apply (rule ir_str)
  apply (simp add: wpre.simps rg_upd_def addI_def addR_def)

  apply (rule chain1_full)
  apply (rule ir_str)
  apply (simp add: wpre.simps rg_upd_def addI_def modR_def)

  apply (rule chain1_full)
  apply (rule ir_str)
  apply (simp add: wpre.simps rg_upd_def addI_def modR_def)

  apply (rule chain1_full)
  apply (rule cm_str)
  apply (simp add: wpre.simps rg_upd_def addI_def modR_def LE_def)

  apply (rule chain1_full)
  apply (rule ld_str)
  apply (auto simp: glb_def aux_upd_def rg_upd_def o_def st_upd_def wpre.simps)[1]
  apply (meson relcomp.relcompI transitive_closure_trans(3))

  apply (rule chain1_full)
  apply (rule env_str)

  apply (rule chain1_full)
  apply (rule ir_str)
  apply (simp add: wpre.simps rg_upd_def addI_def modR_def subR_def)
  
  apply (rule chain1_full)
  apply (rule ld_str)
  apply (auto simp: glb_def aux_upd_def rg_upd_def o_def st_upd_def wpre.simps)[1]
  apply (meson relcomp.relcompI transitive_closure_trans(3))
  
  apply (rule chain1_full)
  apply (rule env_str)

  apply (rule chain1_full)
  apply (rule ld_str)
  apply (auto simp: glb_def aux_upd_def rg_upd_def o_def st_upd_def wpre.simps)[1]
  apply (subgoal_tac "st m (Suc (rg m r\<^sub>0)) - st m (rg m r\<^sub>0) < st m (Suc (Suc (rg m r\<^sub>0)))")
  apply auto[1]

  defer 1
  apply (meson relcomp.relcompI transitive_closure_trans(3))
  apply (simp add: wpre.simps rg_upd_def addI_def modR_def subR_def)

  apply (rule chain1_full)
  apply (rule env_str)

  apply (clarsimp simp add: chain.simps str_def pred_defs wpre.simps put_def split: if_splits)
  
  sorry
 
  (* Wellformedness *)
  apply (auto simp add: stable_def step\<^sub>t_def glb_def reflexive_def transitive_def)[4]
  apply (meson relcomp.relcompI rtrancl_trans)

  (* Various load operations *)
  apply (auto simp: step_def wpre.simps wp_defs inv2_def)[3]

  (* Write to buffer *)
  apply (auto simp: step_def st_upd_def glb_def wpre.simps aux_upd_def inv2_def set_glb_def wp_defs entail_def queue_def addI_def)[1]
  apply (subgoal_tac "st m (Suc PTR) mod st m (Suc (Suc PTR)) \<noteq> x mod st m (Suc (Suc PTR))")
  apply argo
  apply (rule mod_neq; auto)

  (* Update BOT *)
  apply (auto simp: step_def st_upd_def glb_def inv_def wpre.simps set_glb_def inv2_def aux_upd_def o_def entail_def wp_defs queue_def addI_def)[1]
  

  (* WP Reasoning *)  
  apply (clarsimp simp add: addR_def addI_def modR_def subR_def LE_def rg_upd_def)
  apply (clarsimp simp add: wp_defs rg_upd_def aux_upd_def st_upd_def)

  apply (rule stabilize_rw)
  apply (rule stabilize_rw)
  apply (rule stabilize_rw)


  sorry

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
          \<lbrace> (\<exists>i. \<^sup>rr\<^sub>1 \<le> i \<and> i \<le> \<^sup>s[TOP] \<and> \<^sup>rr\<^sub>2 = PTR + (i mod \<^sup>s[LEN])) \<rbrace> 
            r\<^sub>2 := [r\<^sub>2 + #3];
          r\<^sub>3 := r\<^sub>1 + #1;
          \<lbrace> \<^sup>rr\<^sub>3 = \<^sup>rr\<^sub>1 + 1 \<and> \<^sup>rr\<^sub>0 = TOP \<and> \<^sup>rr\<^sub>1 < \<^sup>s[BOT] \<rbrace> 
            r\<^sub>3 := cas r\<^sub>0 r\<^sub>1 r\<^sub>3, \<^sup>adeque := drop 1 \<^sup>adeque;
          if (Z r\<^sub>3) then r\<^sub>2 := #ABORT fi
        else
          r\<^sub>2 := #EMPTY
        fi
      }
      Q: (\<^sup>rr\<^sub>2 \<noteq> EMPTY \<and> \<^sup>rr\<^sub>2 \<noteq> ABORT) \<longrightarrow> (A,\<^sup>adeque) \<in> S\<^sup>* O (steal \<^sup>rr\<^sub>2) O S\<^sup>*
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

