theory Global_Rules
  imports Local_Rules Interference
begin

chapter \<open>Global Rules\<close>

text \<open>Define the rely/guarantee rules for a concurrent program.\<close>

locale global_rules = local_rules + interference

context global_rules
begin

section \<open>Global Rules\<close>

text \<open>Establish the rules of the logic, similar to standard Hoare-logic\<close>
inductive rules :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> 'a com \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
where
  thread[intro]: "R,G \<turnstile>\<^sub>l P { c } Q \<Longrightarrow> inter R G c \<Longrightarrow> R,G \<turnstile> P { c } Q" |
  par[intro]:    "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                  R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (Q\<^sub>1 \<inter> Q\<^sub>2)" |
  conseq[intro]: "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                  R',G' \<turnstile> P' { c } Q'" |
  frame[intro]:  "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' M \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> R \<inter> R',G \<turnstile> P \<inter> M {c} Q \<inter> M"

subsection \<open>Properties\<close>

lemma g_parE [elim]:
  assumes "R,G \<turnstile> P { c\<^sub>1 || c\<^sub>2 } Q"
  obtains R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2 where 
    "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1" "R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2"
    "P \<subseteq> P\<^sub>1 \<inter> P\<^sub>2" "R \<subseteq> R\<^sub>1 \<inter> R\<^sub>2" "G\<^sub>1 \<union> G\<^sub>2 \<subseteq> G" "Q\<^sub>1 \<inter> Q\<^sub>2 \<subseteq> Q" "G\<^sub>1 \<subseteq> R\<^sub>2" "G\<^sub>2 \<subseteq> R\<^sub>1"
  using assms
proof (induct R G P "c\<^sub>1 || c\<^sub>2" Q)
  case (thread R G P Q)
  then show ?case using parE by fast
next
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2)
  show ?case using par(7)[OF par(1,3)] par(5,6) by blast
next
  case (conseq R G P Q P' R' G' Q')
  show ?case
  proof (rule conseq(2), goal_cases)
    case (1 R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2)
    then show ?case using conseq(3,4,5,6) conseq(7)[OF 1(1,2)] by blast
  qed  
next
  case (frame R G P Q R' M)
  show ?case
  proof (rule frame(2), goal_cases)
    case (1 R\<^sub>1 G\<^sub>1 P\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 Q\<^sub>2)
    hence a: "R\<^sub>1 \<inter> R',G\<^sub>1 \<turnstile> P\<^sub>1 \<inter> M {c\<^sub>1} Q\<^sub>1 \<inter> M" "R\<^sub>2 \<inter> R',G\<^sub>2 \<turnstile> P\<^sub>2 \<inter> M {c\<^sub>2} Q\<^sub>2 \<inter> M"
      using rules.frame frame(3,4) by auto
    show ?case using 1(3,4,5,6,7,8) frame(4) frame(5)[OF a] by blast
  qed
qed

lemma g_nilE [elim!]:
  assumes "R,G \<turnstile> P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms by (induct R G P "Nil :: 'a com" Q) blast+

lemma g_stable_preE:
  assumes "R,G \<turnstile> P {c} Q"
  obtains P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c} Q"
  using assms 
proof (induct)
  case (thread R G P c Q)
  then show ?case using stable_preE by (metis rules.thread) 
next
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  show ?case
  proof (rule par(2), rule par(4), goal_cases)
    case (1 P1 P2)
    hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P1 \<inter> P2 {c\<^sub>1 || c\<^sub>2} Q\<^sub>1 \<inter> Q\<^sub>2"
      using rules.par par(5,6) by simp
    thus ?case using par(7)[of "P1 \<inter> P2"] using 1 by auto
  qed 
qed blast+

end

end