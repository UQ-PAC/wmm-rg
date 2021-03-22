theory Refine
  imports Soundness
begin

text \<open>
It may be desirable to demonstrate a logic judgement over an abstract program, with
incomplete but sound behaviour.
This extension to the soundness proof demonstrates the rely/guarantee validity
property over the real execution given an abstract implementation.
\<close>

definition act_ref
  where "act_ref \<alpha> \<beta> \<equiv> vc \<alpha> \<subseteq> vc \<beta> \<and> beh \<beta> \<subseteq> beh \<alpha> \<and> snd (snd \<alpha>) = snd (snd \<beta>)"

locale refine = soundness +
  assumes fwd_act_ref: "\<And>(\<gamma> :: ('a,'b) basic) \<beta> \<alpha>. act_ref \<beta> \<alpha> \<Longrightarrow> \<gamma> \<hookleftarrow> \<alpha>\<langle>\<gamma>\<rangle> \<Longrightarrow> \<gamma> \<hookleftarrow> \<beta>\<langle>\<gamma>\<rangle> \<and> act_ref \<beta>\<langle>\<gamma>\<rangle> \<alpha>\<langle>\<gamma>\<rangle>"

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

lemma lang_ref_fwd_eq:
  assumes "lang_ref c\<^sub>1 c\<^sub>2" "\<alpha>' < c\<^sub>2 <\<^sub>c \<alpha>"
  shows "\<alpha>' < c\<^sub>1 <\<^sub>c \<alpha>"
  using assms
proof (induct c\<^sub>1 c\<^sub>2 arbitrary: \<alpha> \<alpha>' rule: lang_ref.induct)
  case (2 \<alpha> \<beta>)
  then show ?case by (auto simp: act_ref_def)
next
  case (3 c\<^sub>1 c\<^sub>2 c\<^sub>3 c\<^sub>4)
  then show ?case by (meson lang_ref.simps(3) reorder_com.simps(3))
qed auto

lemma fwd_ref:
  "\<alpha>' < c <\<^sub>c \<alpha> \<Longrightarrow> act_ref \<beta> \<alpha> \<Longrightarrow> \<exists>\<beta>'. \<beta>' < c <\<^sub>c \<beta> \<and> act_ref \<beta>' \<alpha>'"
proof (induct c arbitrary: \<alpha> \<alpha>' \<beta>)
  case (Basic \<gamma>)
  then show ?case using fwd_act_ref by auto
next
  case (Seq c1 c2)
  then show ?case by (smt reorder_com.simps(3))
qed auto

lemma lang_ref_fwd_ref:
  assumes "lang_ref c\<^sub>1 c\<^sub>2" "\<alpha>' < c\<^sub>2 <\<^sub>c \<alpha>" "act_ref \<beta> \<alpha>"
  obtains \<beta>' where "\<beta>' < c\<^sub>1 <\<^sub>c \<beta>" "act_ref \<beta>' \<alpha>'"
  using assms fwd_ref lang_ref_fwd_eq by blast

lemma lang_ref_prg:
  assumes "lang_ref c\<^sub>1 c\<^sub>2" "c\<^sub>2 \<mapsto>[\<alpha>,r,\<alpha>'] c\<^sub>2'" 
  obtains c\<^sub>1' \<beta> r' \<beta>' where "c\<^sub>1 \<mapsto>[\<beta>,r',\<beta>'] c\<^sub>1'" "lang_ref c\<^sub>1' c\<^sub>2'" "act_ref \<beta> \<alpha>"
  using assms 
proof (induct c\<^sub>1 c\<^sub>2 arbitrary: c\<^sub>2' \<alpha> r \<alpha>' rule: lang_ref.induct)
  case (2 \<alpha>'' \<beta>)
  then show ?case by fastforce
next
  case (3 c\<^sub>1 c\<^sub>2 c\<^sub>3 c\<^sub>4)
  show ?case using 3(5)
  proof (cases)
    case (seq c\<^sub>3')
    then show ?thesis using 3(1)[OF _ _ seq(2)] 3(3,4) by fastforce
  next
    case (ooo \<alpha>'' c c\<^sub>4')
    show ?thesis
    proof (rule 3(2)[OF _ _ ooo(3)], goal_cases)
      case (1 \<beta> r' \<beta>' c\<^sub>1')
      obtain \<beta>' where "\<beta>' < c\<^sub>1 <\<^sub>c \<beta>" "act_ref \<beta>' \<alpha>" 
        using lang_ref_fwd_ref[OF _ ooo(4) 1(3), of c\<^sub>1] 3(4) by auto
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
  then obtain \<alpha> r \<alpha>' where \<alpha>: "c\<^sub>2 \<mapsto>[\<alpha>,r,\<alpha>'] (fst s')" "(snd s,snd s') \<in> eval \<alpha>" by auto
  then obtain \<beta> r' \<beta>' c\<^sub>1' where \<beta>: 
      "c\<^sub>1 \<mapsto>[\<beta>,r',\<beta>'] c\<^sub>1'" "lang_ref c\<^sub>1' (fst s')" "vc \<beta> \<subseteq> vc \<alpha>" "beh \<alpha> \<subseteq> beh \<beta>" 
    using lang_ref_prg act_ref_def prg(8) by metis
  then obtain P' M where p: "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>} M" "R,G \<turnstile> M {c\<^sub>1'} Q"
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