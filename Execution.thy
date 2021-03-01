theory Execution
  imports Trace
begin

section \<open>Execution\<close>

text \<open>
Given a trace and evaluation property for actions, define the execution of a trace.
\<close>

locale execution =
  fixes eval :: "'a \<Rightarrow> 's rel" 
  assumes eval_det: "(m,m') \<in> eval \<alpha> \<Longrightarrow> (m,m'') \<in> eval \<alpha> \<Longrightarrow> m' = m''"

context execution
begin

inductive trace_mem
  where 
    [intro]: "trace_mem m [] m" | 
    [intro]: "(m'', m) \<in> eval \<alpha> \<Longrightarrow> trace_mem m t m' \<Longrightarrow> trace_mem m'' (\<alpha>#t) m'"

definition ev :: "'a Stmt \<Rightarrow> 's \<Rightarrow> 'a Trace \<Rightarrow> 'a Stmt  \<Rightarrow> 's \<Rightarrow> bool"
  ("\<langle>_,_\<rangle> \<rightarrow>_\<^sup>* \<langle>_,_\<rangle>" [50,40,40] 70)
  where "\<langle>c,m\<rangle> \<rightarrow>t\<^sup>* \<langle>c',m'\<rangle> \<equiv> trace_mem m t m' \<and> c \<mapsto>t\<^sup>* c'"

lemma trace_mem_det:
  assumes "trace_mem m t m'" "trace_mem m t m''"
  shows "m' = m''"
  using assms
proof (induct arbitrary: m'')
  case (1 m)
  then show ?case by (auto elim: trace_mem.cases)
next
  case (2 m''' m \<alpha> t m')
  hence a: "(m''', m) \<in> eval \<alpha>" "trace_mem m t m'" "\<forall>m''. trace_mem m t m'' \<longrightarrow> m' = m''"
    by blast+    
  show ?case using 2(4)
  proof (cases rule: trace_mem.cases)
    case (2 m'''')
    show ?thesis using eval_det[OF 2(1) a(1)] a(3) 2(2) by blast
  qed
qed

lemma ev_det:
  assumes "\<langle>c,m\<rangle> \<rightarrow>t\<^sup>* \<langle>c',m'\<rangle>"
  assumes "\<langle>c,m\<rangle> \<rightarrow>t\<^sup>* \<langle>c'',m''\<rangle>"
  shows "m'' = m'"
  using assms trace_mem_det unfolding ev_def
  by auto

end

end