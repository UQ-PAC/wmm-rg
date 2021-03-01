theory Lang_WP
  imports Trace_WP
begin

chapter \<open>Language Weakest-Precondition Reasoning\<close>

locale lang_wp = trace_wp

context lang_wp
begin

text \<open>Rule for a basic instruction as a pending operation\<close>
definition lang_basic :: "'s rel \<Rightarrow> 's rel \<Rightarrow> ('a,'s) assert \<Rightarrow> 'a \<Rightarrow> ('a,'s) assert \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>A _ {_} _" [20, 20, 20, 20] 20)
  where "R,G \<turnstile>\<^sub>A A {\<alpha>} B \<equiv> undefined"

definition wf\<^sub>A
  where "wf\<^sub>A R A \<equiv> wf_assert A \<and> stable R \<lceil>A\<rceil>"

definition inter\<^sub>s
  where "inter\<^sub>s c\<^sub>1 c\<^sub>2 \<equiv> undefined"

text \<open>Establish the rules of the logic, similar to standard Hoare-logic\<close>
inductive lang_rules :: "('s) rel \<Rightarrow> 's rel \<Rightarrow> ('a,'s) assert \<Rightarrow> 'a Stmt \<Rightarrow> ('a,'s) assert \<Rightarrow> bool"
  ("_,_ \<turnstile>\<^sub>s _ {_} _" [20,0,0,0,20] 20)
where
  skip[intro]:   "wf\<^sub>A R P \<Longrightarrow> R,G \<turnstile>\<^sub>s P { Skip } P" |
  seq[intro]:    "inter\<^sub>s c\<^sub>1 c\<^sub>2 \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>s Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c\<^sub>1 ;; c\<^sub>2 } M" |
  choice[intro]: "R,G \<turnstile>\<^sub>s P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c\<^sub>1 \<sqinter> c\<^sub>2 } Q" |
  loop[intro]:   "inter\<^sub>s c c \<Longrightarrow> wf\<^sub>A R P \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c } P \<Longrightarrow> R,G \<turnstile>\<^sub>s P { c* } P" |
  basic[intro]:  "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<Longrightarrow> R,G \<turnstile>\<^sub>s P { Basic \<alpha> } Q" |
  conseq: "R,G \<turnstile>\<^sub>s P { c } Q \<Longrightarrow> P' \<turnstile> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> Q \<turnstile> Q' \<Longrightarrow> R',G \<turnstile>\<^sub>s P' { c } Q'"

lemma wf_lang_to_trace [intro]:
  "wf\<^sub>A R A \<Longrightarrow> wf\<^sub>t [] R A"
  by (auto simp: wf\<^sub>A_def wf\<^sub>t_def)

lemma
  "R,G \<turnstile>\<^sub>t []; P { t } Q \<Longrightarrow> preserve_trace t' P \<Longrightarrow> R,G \<turnstile>\<^sub>t t'; P { t } Q"
proof (induct R G "[] :: 'a list" P t Q rule: trace_rules.induct)
  case (nil R P G)
  then show ?case
    using wf\<^sub>t_def
    by auto
next
  case (con R G P \<alpha> Q t\<^sub>2 Q')
  then show ?case sorry
next
  case (rw P P' Q' Q R G t\<^sub>2)
  then show ?case sorry
qed

lemma stmt_to_traces:
  "R,G \<turnstile>\<^sub>s P { c } Q \<Longrightarrow> \<forall>t \<in> traces c. R,G \<turnstile>\<^sub>t []; P { t } Q"
proof (induct rule: lang_rules.induct)
  case (skip P R G)
  then show ?case by auto 
next
  case (seq c\<^sub>1 c\<^sub>2 R G P Q M)
  then show ?case
    apply (clarsimp simp add: cat_def)
    apply (rule seqI)
    apply blast
    sorry (* Need to show that the pre-trace works here *)
next
  case (choice R G P c\<^sub>1 Q c\<^sub>2)
  then show ?case by auto
next
  case (loop c R P G)
  show ?case
  proof clarsimp
    fix t assume "t \<in> rep (traces c)"
    hence "rep\<^sub>i (traces c) t" by (auto simp: rep_def)
    thus "R,G \<turnstile>\<^sub>t []; P {t} P"
    proof (induct "traces c" t rule: rep\<^sub>i.induct)
      case (n)
      then show ?case using loop(2) by fast
    next
      case (s t\<^sub>1 t\<^sub>2)
      hence a: "t\<^sub>1 \<in> traces (c*)" by (auto simp: rep_def)
      show ?case using loop s (* Need the seq composition from above *)
        sorry (*using inter_loop[OF loop(1) s(3) a] s(2) loop(4) s(3) by blast*)
    qed
  qed
next
  case (basic R G P \<alpha> Q)
  then show ?case sorry
next
  case (conseq R G P c Q P' R' Q')
  thus ?case
    apply clarsimp
    apply (rule rw)
    apply blast
    apply blast
    sorry (* Need a RW on the rely as well, shouldn't be tough *)
qed

theorem lang_sound:
  "R,G \<turnstile>\<^sub>s P { c } Q \<Longrightarrow> \<forall>t \<in> traces c. \<forall>t' \<in> \<lbrakk>t\<rbrakk>. m \<in> \<lceil>P\<rceil> \<longrightarrow> valid m R G t' \<lceil>Q\<rceil>"
  using stmt_to_traces trace_to_commits by blast

end

end