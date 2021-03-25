theory Global_Rules
  imports Local_Rules Interference
begin

chapter \<open>Global Rules\<close>

text \<open>Define the rely/guarantee rules for a concurrent program.\<close>

locale global_rules = interference + local_rules

context global_rules
begin

section \<open>Global Rules\<close>

text \<open>Establish the rules of the logic, similar to standard Hoare-logic\<close>
inductive rules :: "('b,'c) rpred \<Rightarrow> ('b,'c) rpred \<Rightarrow> ('b \<times> 'c tree) set \<Rightarrow> ('a,'b,'c) com \<Rightarrow> ('b \<times> 'c tree) set \<Rightarrow> bool" 
  ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
where
  thread[intro]: "R,G \<turnstile>\<^sub>l P { c } Q \<Longrightarrow> inter R G c \<Longrightarrow> R,G \<turnstile> leaf P { c } leaf Q" |
  par[intro]:    "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                  R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> left P\<^sub>1 \<inter> right P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (left Q\<^sub>1 \<inter> right Q\<^sub>2)" |
  conseq[intro]: "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                  R',G' \<turnstile> P' { c } Q'"  |
  frame[intro]:  "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' (any M :: ('b \<times> 'c tree) set) \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> R \<inter> R',G \<turnstile> (P \<inter> any M) {c} (Q \<inter> any M)"

subsection \<open>Properties\<close>

lemma g_parE [elim]:
  assumes "R,G \<turnstile> P { c\<^sub>1 || c\<^sub>2 } Q"
  obtains R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where 
    "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2"
    "P \<subseteq> left P\<^sub>1 \<inter> right P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "left Q\<^sub>1 \<inter> right Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
  using assms
proof (induct R G P "c\<^sub>1 || c\<^sub>2" Q)
  case (thread R G P Q)
  then show ?case by blast
next
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2)
  show ?case using par(7)[OF par(1,3)] par(5,6) by blast
next
  case (conseq R G P Q P' R' G' Q')
  show ?case
  proof (rule conseq(2), goal_cases)
    case (1 R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2)
    then show ?case using conseq(3,4,5,6) conseq(7)[OF 1(1,2)] by blast
  qed (*  
next
  case (frame R G P Q R' M)
  show ?case
  proof (rule frame(2), goal_cases)
    case (1 R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2)
    hence a: "R\<^sub>1 \<inter> R',G\<^sub>1 \<turnstile> P\<^sub>1 \<inter> M {c\<^sub>1} Q\<^sub>1 \<inter> M" "R\<^sub>2 \<inter> R',G\<^sub>2 \<turnstile> P\<^sub>2 \<inter> M {c\<^sub>2} Q\<^sub>2 \<inter> M"
      using rules.frame frame(3,4) by auto
    show ?case using 1(3,4,5,6,7,8) frame(4) frame(5)[OF a] by blast
  qed *)
qed

lemma leaf_mono[intro]:
  "P \<subseteq> Q \<Longrightarrow> leaf P \<subseteq> leaf Q"
  unfolding leaf_def by auto

lemma left_mono[intro]:
  "P \<subseteq> Q \<Longrightarrow> left P \<subseteq> left Q"
  unfolding left_def by auto

lemma right_mono[intro]:
  "P \<subseteq> Q \<Longrightarrow> right P \<subseteq> right Q"
  unfolding right_def by auto

lemma leaf_stable[intro]:
  "stable R P \<Longrightarrow> stable R (leaf P)"
  unfolding leaf_def stable_def by auto

lemma left_stable[intro]:
  "stable R P \<Longrightarrow> stable R (left P)"
  unfolding left_def stable_def by auto

lemma right_stable[intro]:
  "stable R P \<Longrightarrow> stable R (right P)"
  unfolding right_def stable_def by auto

lemma g_nilE [elim!]:
  assumes "R,G \<turnstile> P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms 
proof (induct R G P "Nil :: ('a,'b,'c) com" Q)
  case (thread R G P Q)
  then show ?case using leaf_mono leaf_stable by blast 
next
  case (conseq R G P Q P' R' G' Q')
  then show ?case by blast
qed

lemma g_stable_preE:
  assumes "R,G \<turnstile> P {c} Q"
  obtains P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c} Q"
  using assms 
proof (induct)
  case (thread R G P c Q)
  then show ?case using stable_preE by (metis rules.thread leaf_stable leaf_mono) 
next 
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case
  proof (rule par(2), rule par(4), goal_cases)
    case (1 P1 P2)
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> left P1 \<inter> right P2 {c\<^sub>1 || c\<^sub>2} left Q\<^sub>1 \<inter> right Q\<^sub>2"
      using rules.par par(5,6) by simp
    thus ?case using par(7)[of "left P1 \<inter> right P2"] 
      using 1 left_stable right_stable right_mono left_mono 
      by (metis inf_mono stable_conjI)
  qed 
qed blast+

end

end