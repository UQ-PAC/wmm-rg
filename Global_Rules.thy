theory Global_Rules
  imports Local_Rules Interference
begin

chapter \<open>Global Rules\<close>

text \<open>Define the rely/guarantee rules for a concurrent program.\<close>

locale global_rules = interference

context global_rules
begin

section \<open>Global Rules\<close>

text \<open>Establish the rules of the logic, similar to standard Hoare-logic\<close>
inductive rules :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b set \<Rightarrow> ('a,'b) com \<Rightarrow> 'b set \<Rightarrow> bool" 
  ("_,_ \<turnstile> _ {_} _" [20,0,0,0,20] 20)
where
  thread[intro]: "R,G \<turnstile>\<^sub>l P { c } Q \<Longrightarrow> inter R G c \<Longrightarrow> R,G \<turnstile> P { c } Q" |
  par[intro]:    "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                  R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (Q\<^sub>1 \<inter> Q\<^sub>2)" |
  conseq[intro]: "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                  R',G' \<turnstile> P' { c } Q'"  |
  frame[intro]:  "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' M \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> R \<inter> R',G \<turnstile> (P \<inter> M) {c} (Q \<inter> M)" |
  aux[intro]: "R,G \<turnstile> P { c } Q \<Longrightarrow> aux\<^sub>R r R,aux\<^sub>G r G \<turnstile> aux\<^sub>P r P { aux\<^sub>c r c } aux\<^sub>P r Q"

subsection \<open>Properties\<close>

lemma g_nilE [elim!]:
  assumes "R,G \<turnstile> P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms 
proof (induct R G P "Nil :: ('a,'b) com" Q) 
  case (aux R G P c Q r)
  thus ?case using aux\<^sub>P_mono aux_stable aux\<^sub>c_nilE by metis
qed blast+

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
    thus ?case using par(7)[of "P1 \<inter> P2"] 
      using 1 by (metis inf_mono stable_conjI)
  qed 
next
  case (aux R G P c Q r)
  thus ?case by (metis rules.aux aux\<^sub>P_mono aux_stable)
qed blast+

end

end