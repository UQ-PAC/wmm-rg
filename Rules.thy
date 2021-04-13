theory Rules
  imports Interference Syntactic_Refine
begin

chapter \<open>Rules\<close>

text \<open>Define the rely/guarantee rules for a concurrent program.\<close>

locale rules = interference

context rules
begin

section \<open>Global Rules\<close>

text \<open>Establish the rules of the logic, similar to standard Hoare-logic\<close>
inductive rules :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b set \<Rightarrow> ('a,'b) com \<Rightarrow> 'b set \<Rightarrow> bool" 
  ("_,_ \<turnstile> _ {_} _" [65,0,0,0,65] 65)
  where
  basic[intro]:  "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<Longrightarrow> R,G \<turnstile> P { Basic \<alpha> } Q" |
  nil[intro]:    "stable R P \<Longrightarrow> R,G \<turnstile> P { Nil } P" |
  seq[intro]:    "R,G \<turnstile> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile> Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 ;; c\<^sub>2 } M" |
  ord[intro]:    "R,G \<turnstile> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile> Q { c\<^sub>2 } M \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 \<cdot> c\<^sub>2 } M" |
  choice[intro]: "R,G \<turnstile> P { c\<^sub>1 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>2 } Q \<Longrightarrow> R,G \<turnstile> P { c\<^sub>1 \<sqinter> c\<^sub>2 } Q" |
  seqset[intro]: "\<forall>s \<in> S. R,G \<turnstile> P { seq2com s } Q \<Longrightarrow> R,G \<turnstile> P { \<Sqinter> S } Q" |
  loop[intro]:   "stable R P \<Longrightarrow> R,G \<turnstile> P { c } P \<Longrightarrow> R,G \<turnstile> P { c* } P" |
  state[intro]:  "R,G \<turnstile> P { c } Q \<Longrightarrow> inter R G c \<Longrightarrow> 
                  thr\<^sub>R op R,thr\<^sub>G op G \<turnstile> thr\<^sub>P op l P { State l op c } thr\<^sub>Q op Q" |
  thread[intro]: "R,G \<turnstile> P { c } Q \<Longrightarrow> inter R G c \<Longrightarrow> 
                  thr\<^sub>R op R,thr\<^sub>G op G \<turnstile> thr\<^sub>A op P { Thread op c } thr\<^sub>Q op Q" |
  par[intro]:    "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1 { c\<^sub>1 } Q\<^sub>1 \<Longrightarrow> R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2 { c\<^sub>2 } Q\<^sub>2 \<Longrightarrow> G\<^sub>2 \<subseteq> R\<^sub>1 \<Longrightarrow> G\<^sub>1 \<subseteq> R\<^sub>2 \<Longrightarrow> 
                  R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1 \<inter> P\<^sub>2 { c\<^sub>1 || c\<^sub>2 } (Q\<^sub>1 \<inter> Q\<^sub>2)" |
  conseq[intro]: "R,G \<turnstile> P { c } Q \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> 
                  R',G' \<turnstile> P' { c } Q'"  |
  inv[intro]:    "R,G \<turnstile> P {c} Q \<Longrightarrow> stable R' I \<Longrightarrow> G \<subseteq> R' \<Longrightarrow> R \<inter> R',G \<turnstile> (P \<inter> I) {c} (Q \<inter> I)" |
  refine[intro]: "R,G \<turnstile> P {c} Q \<Longrightarrow> refine c c' \<Longrightarrow> R,G \<turnstile> P {c'} Q" |
  aux[intro]:    "R,G \<turnstile> P {c} Q \<Longrightarrow> aux\<^sub>C r c c' \<Longrightarrow> aux\<^sub>R r R,aux\<^sub>G r G \<turnstile> aux\<^sub>P r P {c'} aux\<^sub>P r Q"

subsection \<open>Properties\<close>

lemma nilE [elim!]:
  assumes "R,G \<turnstile> P {Nil} Q"
  obtains M where "stable R M" "P \<subseteq> M" "M \<subseteq> Q"
  using assms 
proof (induct R G P "Nil :: ('a,'b) com" Q)
  case (refine R G P c\<^sub>1 Q)
  thus ?case by auto
next
  case (aux R G P c Q r)
  thus ?case using aux\<^sub>P_mono aux_stable by blast
qed blast+

lemma basicE [elim!]:
  assumes "R,G \<turnstile> P {Basic \<beta>} Q"
  obtains P' Q' where "P \<subseteq> P'" "R,G \<turnstile>\<^sub>A P' {\<beta>} Q'" "Q' \<subseteq> Q"
  using assms 
proof (induct R G P "Basic \<beta> :: ('a,'b) com" Q arbitrary: \<beta>)
  case (basic R G P Q)
  then show ?case by auto
next
  case (conseq R G P Q P' R' G' Q')
  then show ?case using order.trans atomic_conseqI by metis
next
  case (inv R G P Q R' I)
  show ?case 
  proof (rule inv(2), goal_cases)
    case (1 P' Q')
    thus ?case using inv(3,4) inv(5)[of "P' \<inter> I" "Q' \<inter> I"] atomic_invI by blast
  qed
next
  case (refine R G P c Q)
  then obtain \<alpha> where a: "c = Basic \<alpha>" "refine\<^sub>\<alpha> \<alpha> \<beta>" by (auto)
  show ?case 
  proof (rule refine(2)[OF a(1)], goal_cases)
    case (1 P' Q')
    then show ?case using refine(4) a(2) atomic_refineI by metis
  qed
next
  case (aux R G P c Q r)
  then obtain \<alpha> where a: "c = Basic \<alpha>" "aux\<^sub>\<alpha> r \<alpha> \<beta>" by (auto)
  show ?case
  proof (rule aux(2)[OF a(1)], goal_cases)
    case (1 P' Q')
    then show ?case using aux(4) a(2) atomic_auxI aux\<^sub>P_mono by metis
  qed
qed

lemma seqE [elim]:
  assumes "R,G \<turnstile> P {c\<^sub>1 ;; c\<^sub>2} Q"
  obtains M  where "R,G \<turnstile> P {c\<^sub>1} M" "R,G \<turnstile> M {c\<^sub>2} Q"
  using assms 
  by (induct R G P "c\<^sub>1 ;; c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+ 

lemma ordE [elim]:
  assumes "R,G \<turnstile> P {c\<^sub>1 \<cdot> c\<^sub>2} Q"
  obtains M  where "R,G \<turnstile> P {c\<^sub>1} M" "R,G \<turnstile> M {c\<^sub>2} Q"
  using assms by (induct R G P "c\<^sub>1 \<cdot> c\<^sub>2" Q arbitrary: c\<^sub>1 c\<^sub>2) blast+

text \<open>It is always possible to rephrase a judgement in terms of a stable precondition\<close>
lemma stable_preE:
  assumes "R,G \<turnstile> P {c} Q"
  shows "\<exists>P'. P \<subseteq> P' \<and> stable R P' \<and> R,G \<turnstile> P' {c} Q"
  using assms 
proof (induct)
  case (state R G P c Q op l)
  then show ?case by (metis thr_stable thr_mono rules.state)
next 
  case (thread R G P c Q op)
  then show ?case by (metis thr_stable' thr_mono' rules.thread)
next 
  case (par R\<^sub>1 G\<^sub>1 P\<^sub>1 c\<^sub>1 Q\<^sub>1 R\<^sub>2 G\<^sub>2 P\<^sub>2 c\<^sub>2 Q\<^sub>2)
  obtain P\<^sub>1' where 1: "P\<^sub>1 \<subseteq> P\<^sub>1'" "stable R\<^sub>1 P\<^sub>1'" "R\<^sub>1,G\<^sub>1 \<turnstile> P\<^sub>1' {c\<^sub>1} Q\<^sub>1" using par by auto
  obtain P\<^sub>2' where 2: "P\<^sub>2 \<subseteq> P\<^sub>2'" "stable R\<^sub>2 P\<^sub>2'" "R\<^sub>2,G\<^sub>2 \<turnstile> P\<^sub>2' {c\<^sub>2} Q\<^sub>2" using par by auto
  hence "R\<^sub>1 \<inter> R\<^sub>2,G\<^sub>1 \<union> G\<^sub>2 \<turnstile> P\<^sub>1' \<inter> P\<^sub>2' {c\<^sub>1 || c\<^sub>2} Q\<^sub>1 \<inter> Q\<^sub>2" using 1 2 rules.par par(5,6) by simp
  thus ?case using 1 2 stable_conjI by blast
next
  case (basic R G P \<alpha> Q)
  then show ?case using atomic_rule_def by fast
next
  case (choice R G P c\<^sub>1 Q c\<^sub>2)
  obtain P\<^sub>1 where 1: "P \<subseteq> P\<^sub>1" "stable R P\<^sub>1" "R,G \<turnstile> P\<^sub>1 {c\<^sub>1} Q" using choice by auto
  obtain P\<^sub>2 where 2: "P \<subseteq> P\<^sub>2" "stable R P\<^sub>2" "R,G \<turnstile> P\<^sub>2 {c\<^sub>2} Q" using choice by auto
  have "stable R (P\<^sub>1 \<inter> P\<^sub>2)" using 1 2 by auto
  thus ?case using 1 2 by blast
next
  case (seqset S R G P Q)
  hence "\<exists>P\<^sub>s. \<forall>s\<in>S. P \<subseteq> P\<^sub>s s \<and> stable R (P\<^sub>s s) \<and> (R,G \<turnstile> P\<^sub>s s {seq2com s} Q)"
    by metis
  then obtain P\<^sub>s where s: "\<forall>s\<in>S. P \<subseteq> P\<^sub>s s \<and> stable R (P\<^sub>s s) \<and> (R,G \<turnstile> P\<^sub>s s {seq2com s} Q)"
    by blast
  hence "stable R (\<Inter>s\<in>S. P\<^sub>s s)" by (auto simp: stable_def)
  moreover have "P \<subseteq> (\<Inter>s\<in>S. P\<^sub>s s)" using s by auto
  ultimately show ?case using s seqset.hyps(1) by blast
next
  case (conseq R G P c Q P' R' G' Q')
  then show ?case by (meson order_refl rules.conseq stable_conseqI subset_trans)
next
  case (inv R G P c Q R' I)
  then obtain P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c} Q" by auto
  then show ?case using inv rules.inv by blast
next
  case (aux R G P c Q r c')
  thus ?case using aux\<^sub>P_mono aux_stable by (metis rules.aux)
qed blast+

lemma false_seqI [intro]:
  "\<forall>\<beta> \<in> set s. guar\<^sub>\<alpha> \<beta> G \<Longrightarrow> R,G \<turnstile> {} {seq2com s} {}"
  by (induct s) auto

lemma falseI:
  shows "local c \<Longrightarrow> \<forall>\<beta> \<in> basics c. guar\<^sub>\<alpha> \<beta> G \<Longrightarrow> UNIV,G \<turnstile> {} { c } {}"
proof (induct c)
  case (Basic x)
  thus ?case by (intro basic) (auto simp: atomic_rule_def guar_def wp_def)
next
  case (SeqChoice x)
  thus ?case by (intro ballI seqset false_seqI) auto
qed auto

end

end