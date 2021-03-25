theory Refine
  imports Soundness
begin

text \<open>
It may be desirable to demonstrate a logic judgement over an abstract program, with
incomplete but sound behaviour.
This extension to the soundness proof demonstrates the rely/guarantee validity
property over the real execution given an abstract implementation.
\<close>

locale refine = soundness +
  fixes act_ref :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes ref_vc: "act_ref \<alpha> \<beta> \<Longrightarrow> vc \<alpha> \<subseteq> vc \<beta>"
  assumes ref_beh: "act_ref \<alpha> \<beta> \<Longrightarrow> beh \<beta> \<subseteq> beh \<alpha>"
  assumes ref_re: "act_ref \<gamma>\<^sub>1 \<gamma>\<^sub>2 \<Longrightarrow> act_ref \<beta> \<alpha> \<Longrightarrow> act_ref \<beta>\<langle>\<gamma>\<^sub>1\<rangle> \<alpha>\<langle>\<gamma>\<^sub>2\<rangle>"

context refine
begin

fun lang_ref
  where 
    "lang_ref Nil Nil = True" |
    "lang_ref (Basic \<alpha>) (Basic \<beta>) = act_ref \<alpha> \<beta>" |
    "lang_ref (c\<^sub>1 ; c\<^sub>2) (c\<^sub>3 ; c\<^sub>4) = (lang_ref c\<^sub>1 c\<^sub>3 \<and> lang_ref c\<^sub>2 c\<^sub>4)" |
    "lang_ref (c\<^sub>1 \<sqinter> c\<^sub>2) (c\<^sub>3 \<sqinter> c\<^sub>4) = (lang_ref c\<^sub>1 c\<^sub>3 \<and> lang_ref c\<^sub>2 c\<^sub>4)" |
    "lang_ref (c\<^sub>1* ) (c\<^sub>2* ) = (lang_ref c\<^sub>1 c\<^sub>2)" |
    "lang_ref _ _ = False"

lemma lang_ref_Nil:
  assumes "lang_ref c Nil"
  shows "c = Nil"
  using assms by (case_tac "(c,Nil)" rule: lang_ref.cases; auto)

lemma lang_ref_sil:
  assumes "lang_ref c\<^sub>1 c\<^sub>2" "c\<^sub>2 \<leadsto> c\<^sub>2'" 
  obtains c\<^sub>1' where "c\<^sub>1 \<leadsto> c\<^sub>1'" "lang_ref c\<^sub>1' c\<^sub>2'"
  using assms
proof (induct c\<^sub>1 c\<^sub>2 arbitrary: c\<^sub>2' rule: lang_ref.induct)
  case (3 c\<^sub>1 c\<^sub>2 c\<^sub>3 c\<^sub>4)
  show ?case using 3(5,4,3,2,1) lang_ref_Nil by cases force+ 
next
  case (4 c\<^sub>1 c\<^sub>2 c\<^sub>3 c\<^sub>4)
  show ?case using 4(5,4,3,2,1) by cases force+
next
  case (5 c\<^sub>1 c\<^sub>2)
  show ?case using 5(4,3,2,1) by cases force+
qed auto

lemma fwd_ref:
  assumes "lang_ref c\<^sub>1 c\<^sub>2" "act_ref \<beta> \<alpha>"
  shows "act_ref \<beta>\<llangle>c\<^sub>1\<rrangle> \<alpha>\<llangle>c\<^sub>2\<rrangle>"
  using assms
proof (induct c\<^sub>1 c\<^sub>2 arbitrary: \<alpha> \<beta> rule: lang_ref.induct)
  case (2 \<gamma>\<^sub>1 \<gamma>\<^sub>2)
  then show ?case using ref_re by force
next
  case (3 c\<^sub>1 c\<^sub>2 c\<^sub>3 c\<^sub>4)
  then show ?case by (smt lang_ref.simps(3) fwd_com.simps(3))
qed auto

lemma lang_ref_prg:
  assumes "lang_ref c\<^sub>1 c\<^sub>2" "c\<^sub>2 \<mapsto>[r,\<alpha>] c\<^sub>2'" 
  obtains c\<^sub>1' \<beta> r' where "c\<^sub>1 \<mapsto>[r',\<beta>] c\<^sub>1'" "lang_ref c\<^sub>1' c\<^sub>2'" "act_ref \<beta>\<llangle>r'\<rrangle> \<alpha>\<llangle>r\<rrangle>"
  using assms 
proof (induct c\<^sub>1 c\<^sub>2 arbitrary: c\<^sub>2' \<alpha> r rule: lang_ref.induct)
  case (2 \<alpha>'' \<beta>)
  then show ?case by fastforce
next
  case (3 c\<^sub>1 c\<^sub>2 c\<^sub>3 c\<^sub>4)
  show ?case using 3(5)
  proof (cases)
    case (seq c\<^sub>3')
    then show ?thesis using 3(1)[OF _ _ seq(2)] 3(3,4) by fastforce
  next
    case (ooo r' c\<^sub>4')
    show ?thesis
    proof (rule 3(2)[OF _ _ ooo(3)], goal_cases)
      case (1 r'' \<beta> c\<^sub>2')
      hence "act_ref \<beta>\<llangle>c\<^sub>1 ; r''\<rrangle> \<alpha>\<llangle>c\<^sub>3 ; r'\<rrangle>" 
        using fwd_ref[OF _ 1(3), of c\<^sub>1] 3(4) by auto
      then show ?case using 3(3) 3(4,5) 1 ooo by (meson lang_ref.simps(3) semantics.ooo)
    next
      case 2
      then show ?case using 3 by auto
    qed
  qed
qed auto

lemma refine_sound_transitions:
  assumes "t \<in> transitions" "fst (t ! 0) = c\<^sub>2" "R,G \<turnstile> P {c\<^sub>1} Q" "pre P t" "rely R t"
  assumes "lang_ref c\<^sub>1 c\<^sub>2"
  shows "post Q t \<and> gurn G t"
  using assms
proof (induct arbitrary: c\<^sub>1 c\<^sub>2 P rule: transitions.induct)
  case (one s)
  thus ?case using lang_ref_Nil by force
next
  case (env s s' t)
  then obtain P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c\<^sub>1} Q" by (metis g_stable_preE) 
  thus ?case using env by (auto simp: stable_def)
next
  case (prg s s' t)
  then obtain \<alpha> r where \<alpha>: "c\<^sub>2 \<mapsto>[r,\<alpha>] (fst s')" "(snd s,snd s') \<in> eval \<alpha>\<llangle>r\<rrangle>" by auto
  then obtain \<beta> r' c\<^sub>1' where \<beta>: 
      "c\<^sub>1 \<mapsto>[r',\<beta>] c\<^sub>1'" "lang_ref c\<^sub>1' (fst s')" "vc \<beta>\<llangle>r'\<rrangle> \<subseteq> vc \<alpha>\<llangle>r\<rrangle>" "beh \<alpha>\<llangle>r\<rrangle> \<subseteq> beh \<beta>\<llangle>r'\<rrangle>" 
    using lang_ref_prg ref_vc ref_beh prg(8) by metis
  then obtain P' M where p: "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>\<llangle>r'\<rrangle>} M" "R,G \<turnstile> M {c\<^sub>1'} Q"
    using g_stepI[OF prg(5) \<beta>(1)] by metis
  hence "rely R (s' # t)" "pre M (s' # t)" "(snd s, snd s') \<in> G\<^sup>="
    using prg(6,7) \<alpha>(2) \<beta>(3,4) unfolding eval_def atomic_rule_def wp_def by auto blast+
  thus ?case using prg p(3) \<beta>(2) by auto
next
  case (sil s s' t)
  then obtain c\<^sub>1' where "c\<^sub>1 \<leadsto> c\<^sub>1'" "lang_ref c\<^sub>1' (fst s')" 
    using lang_ref_sil by (metis nth_Cons_0)
  then show ?case using sil by auto
qed

theorem refine_sound:
  assumes "R,G \<turnstile> P { c\<^sub>1 } Q"
  assumes "lang_ref c\<^sub>1 c\<^sub>2"
  shows "\<Turnstile> c\<^sub>2 SAT [P, R, G, Q]"
  using assms refine_sound_transitions 
  by (auto simp: validity_def)

end

end