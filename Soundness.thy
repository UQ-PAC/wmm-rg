theory Soundness
  imports Transition_Rules
begin

chapter \<open>Soundness\<close>

context rules
begin

section \<open>Soundness Definition\<close>

text \<open>All traces that start with a program c\<close>
fun cp :: "('a,'b) com \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where "cp c t = (t \<in> transitions \<and> fst (t ! 0) = c)"

text \<open>All traces that satisfy a precondition in their first state\<close>
fun pre :: "'b pred \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where 
    "pre P (s#t) = (snd s \<in> P)" | 
    "pre P [] = True"

text \<open>All traces that satisfy a postcondition in their final state given termination\<close>
fun post :: "'b pred \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where 
    "post Q [s] = (fst s = Nil \<longrightarrow> snd s \<in> Q)" | 
    "post Q (s#t) = post Q t" | 
    "post Q [] = True"

text \<open>All traces where program steps satisfy a guarantee\<close>
fun gurn :: "'b rpred \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where
    "gurn G (s#s'#t) = (gurn G (s'#t) \<and> (s -c\<rightarrow> s' \<longrightarrow> (snd s,snd s') \<in> G\<^sup>=))" |
    "gurn G _ = True"

text \<open>All traces where environment steps satisfy a rely\<close>
fun rely :: "'b rpred \<Rightarrow> ('a,'b) config list \<Rightarrow> bool"
  where
    "rely R (s#s'#t) = (rely R (s'#t) \<and> (s -e\<rightarrow> s' \<longrightarrow> (snd s, snd s') \<in> R))" |
    "rely R _ = True"

text \<open>Validity of the rely/guarantee judgements\<close>
definition validity :: "('a,'b) com \<Rightarrow> 'b set \<Rightarrow> ('b) rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b set \<Rightarrow> bool" 
  ("\<Turnstile> _ SAT [_, _, _, _]" [60,0,0,0,0] 45) 
  where "\<Turnstile> c SAT [P, R, G, Q] \<equiv> \<forall>t. cp c t \<and> pre P t \<and> rely R t \<longrightarrow> post Q t \<and> gurn G t"

section \<open>Soundness Proof\<close>

text \<open>All transitions that start with a program with a logic judgement and satisfy
      the precondition and environment rely should conform to the guarantee and
      establish the postcondition if they terminate\<close>
lemma sound_transitions:
  assumes "t \<in> transitions" "fst (t ! 0) = c" "R,G \<turnstile> P {c} Q" "pre P t" "rely R t"
  shows "post Q t \<and> gurn G t"
  using assms
proof (induct arbitrary: c P rule: transitions.induct)
  case (env s s' t)
  then obtain P' where "P \<subseteq> P'" "stable R P'" "R,G \<turnstile> P' {c} Q" by (metis stable_preE) 
  thus ?case using env by (auto simp: stable_def)
next
  case (prg s s' t)
  hence reach: "P \<noteq> {}" by auto
  then obtain g where \<alpha>: "c \<mapsto>[g] (fst s')" "(snd s,snd s') \<in> g" using prg by auto
  then obtain M v where p: "P \<subseteq> wp v g M" "guar v g G" "R,G \<turnstile> M {fst s'} Q"
    using gexecute_ruleI[OF prg(5) \<alpha>(1) reach] by metis
  hence "rely R (s' # t)" "pre M (s' # t)" "(snd s, snd s') \<in> G\<^sup>="
    using prg \<alpha>(2) by (auto simp: wp_def guar_def)
  thus ?case using prg p(3) by auto
qed force+

theorem sound:
  assumes "R,G \<turnstile> P { c } Q"
  shows "\<Turnstile> c SAT [P, R, G, Q]"
  using sound_transitions[OF _ _ assms] 
  by (auto simp: validity_def)

end

end