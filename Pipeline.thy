theory Pipeline
  imports Trace
begin

text \<open>
Describe the conditions under which an action may be committed to global memory:
  - ca_sq: As the very next action to execute in the trace.
  - ca_re: As some later action in the trace that is reorderable with all those prior.
\<close>
inductive_set commit_action :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a list \<times> 'a \<times> 'a \<times> 'a list) set"
  and commit_action_abv :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" ("_,_ \<turnstile> _ \<midarrow>_,_\<leadsto> _" [60,40,40] 60)
  for re :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and fw :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "re,fw \<turnstile> t \<midarrow>\<beta>',\<beta>\<leadsto> t' \<equiv> (t, \<beta>', \<beta>, t') \<in> commit_action re fw"
  | ca_sq[intro]: "re,fw \<turnstile> \<alpha>#t \<midarrow>\<alpha>, \<alpha>\<leadsto> t" 
  | ca_re[intro]: "re,fw \<turnstile> t \<midarrow>\<beta>,\<beta>'\<leadsto> t' \<Longrightarrow> re \<alpha> (fw \<beta>' \<alpha>) \<Longrightarrow> re,fw \<turnstile> \<alpha>#t \<midarrow>\<beta>,fw \<beta>' \<alpha>\<leadsto> \<alpha>#t'"

text \<open>
Select a series of actions to commit from a trace.
\<close>
inductive_set commit_trace :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a list \<times> 'a list \<times> 'a list) set"
  and commit_trace_abv :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_,_ \<turnstile> _ \<midarrow>_\<leadsto>* _" [50,40,40] 70)
  for re :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and fw :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where
  "re,fw \<turnstile> t \<midarrow>c\<leadsto>* t' \<equiv> (t, c, t') \<in> commit_trace re fw"
  | ct_nil[intro]: "re,fw \<turnstile> t \<midarrow>[]\<leadsto>* t"
  | ct_act[intro]: "re,fw \<turnstile> t \<midarrow>\<alpha>,\<alpha>'\<leadsto> t' \<Longrightarrow> re,fw \<turnstile> t' \<midarrow>ct\<leadsto>* t'' \<Longrightarrow> re,fw \<turnstile> t \<midarrow>\<alpha>'#ct\<leadsto>* t''"

text \<open>
Collect all commit traces for a program trace.
\<close>
definition pipelined :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> ('a list) set"
  where "pipelined re fw t = {p. re,fw \<turnstile> t \<midarrow>p\<leadsto>* []}"


text \<open>
Support alternative memory models via a reordering relation
and forwarding transformation.
\<close>
locale memory_model =
  fixes re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100)
  and fwd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

context memory_model
begin

abbreviation full_reorder ("_ < _ < _" 100)
  where "\<beta>' < \<alpha> < \<beta> \<equiv> \<beta>' = fwd \<beta> \<alpha> \<and> \<alpha> \<hookleftarrow> fwd \<beta> \<alpha>"

fun fwdall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a" ("_\<langle>_\<rangle>" [1000,0] 1000)
  where 
    "\<alpha>\<langle>[]\<rangle> = \<alpha>" |
    "\<alpha>\<langle>\<beta>#t\<rangle> = fwd \<alpha>\<langle>t\<rangle> \<beta>"

abbreviation caction :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<midarrow>_,_\<leadsto> _" [60,40,40] 60)
  where "caction \<equiv> commit_action_abv re fwd"

abbreviation ctrace :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<midarrow>_\<leadsto>* _" [50,40,40] 70)
  where "ctrace \<equiv> commit_trace_abv re fwd"

abbreviation pipelined_abv :: "'a list \<Rightarrow> ('a list) set" ("\<lbrakk>_\<rbrakk>" 70)
  where "pipelined_abv \<equiv> pipelined re fwd"

text \<open>Extend the reordering relation to reorder an action with an entire program trace\<close>
fun reorder_trace ("_ \<lless> _ \<lless> _" [100,0,100] 50)
  where 
    "reorder_trace a [] b = (a = b)" |
    "reorder_trace a (c#t) b = (\<exists>a'. ( a <  c <  a') \<and> (a' \<lless> t \<lless> b))"

lemma [simp]:
  "\<alpha>' \<lless> t @ s \<lless> \<alpha> = (\<exists>\<alpha>''. (\<alpha>' \<lless> t \<lless> \<alpha>'') \<and> \<alpha>'' \<lless> s \<lless> \<alpha>)"
  by (induct t arbitrary: s \<alpha> \<alpha>') auto

lemma reorder_trace_fwdall [simp]:
  assumes "\<alpha> \<lless> pre \<lless> \<gamma>"
  shows "\<gamma>\<langle>pre\<rangle> = \<alpha>"
  using assms by (induct pre arbitrary: \<gamma> \<alpha>) auto

text \<open>
Given a program trace that executes an action, it is possible to break the trace
into a pre and post trace surrounding the original form of the action, such that
these pre and post traces for the resulting trace and the action can reorder
with the pre trace. 

This is a central property that the FM 2019 proof took a long time to demonstrate.
Given the pipeline semantics, its practically free.
\<close>
lemma commit_actionE [elim]:
  assumes "t \<midarrow>\<alpha>,\<alpha>'\<leadsto> t'"
  obtains pre post where "t = pre @ (\<alpha> # post)" "t' = pre @ post" "\<alpha>' \<lless> pre \<lless> \<alpha>"
  using assms
proof (induct)
  case (ca_sq \<alpha> t)
  thus ?case by fastforce
next
  case (ca_re t \<beta> \<beta>' t' \<alpha>)
  show ?case
  proof (rule ca_re(2), goal_cases)
    case (1 pre post)
    thus ?case using ca_re(1,3) by (intro ca_re(4)[of "\<alpha>#pre"]) auto
  qed
qed

end

end