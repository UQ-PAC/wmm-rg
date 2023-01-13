theory Semantics
  imports Atomics (* CaptureReasoning *)

begin

chapter \<open>Small Step Semantics\<close>

text \<open>
Define the small step semantics for the While language, with weak memory model behaviours.
Also introduces a notion of configuration, that couples programs and memory states,
with transitions for the program and the environment.
\<close>

type_synonym ('a,'b) config = "('a,'b) com \<times> 'b"

text \<open>
To simplify the identification of reordered instructions, we instrument the semantics with
bookkeeping data structures to track how the reordering relation has been applied.
\<close>
datatype ('a,'b) log =
  Reorder "('a,'b) basic" "('a,'b) wmm" "('a,'b) com" |
  Scope

type_synonym ('a,'b) bookkeeping = "('a,'b) log list"

text \<open> Locale semantics fixes the types 'a and 'b state; 
        parameters exists_act and exists_state  are used as dummies to do so \<close>

locale semantics =
  fixes exists_act :: "'a"
  fixes exists_state :: "'b::state"

context semantics
begin

text \<open> (w \<alpha>' \<beta> \<alpha>) is an abstract reordering relation that evaluates to true if
          \<alpha> can reorder over \<beta> to become \<alpha>' under WMM w; it is carried around 
          as a subscript to reordering relation _ < _ < _  \<close>

text \<open> wellformedness condition on the reordering semantics
        (allows us to deduce some information on forwarded instructions of which we otherwise
         don't know anyting) \<close>

definition wlf 
  where  "wlf w \<equiv> \<forall> \<alpha>' \<beta> \<alpha>. w \<alpha>' \<beta> \<alpha> \<longrightarrow> (\<forall> G. guar\<^sub>\<alpha> \<alpha> G \<longrightarrow> guar\<^sub>\<alpha> \<alpha>' G)"

text \<open>Extend a reordering relation recursively over a program\<close>
fun reorder_com :: "('a,'b) basic \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) wmm \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  ("_ < _ <\<^sub>_ _" [100,0,0,100] 100)
  where
    "\<alpha>' < Nil <\<^sub>c \<alpha> = (\<alpha>' = \<alpha>)" |
    "\<alpha>' < Basic \<beta> <\<^sub>w \<alpha> = (w \<alpha>' \<beta> \<alpha>)" |
    "\<alpha>' < c\<^sub>1 ;\<^sub>w c\<^sub>2 <\<^sub>c \<alpha> = (\<exists>\<alpha>\<^sub>n. \<alpha>' < c\<^sub>1 <\<^sub>c \<alpha>\<^sub>n \<and> \<alpha>\<^sub>n < c\<^sub>2 <\<^sub>c \<alpha>)" |
    "_ < _ <\<^sub>c _ = False"


section \<open>Program Transition Definitions\<close>

text \<open>Small step semantics for a local execution step\<close>
inductive lexecute :: "('a,'b) com \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) bookkeeping \<Rightarrow> ('a,'b) com \<Rightarrow> bool"
  ("_ \<mapsto>[_,_] _" [71,0,0,71] 70)
  where
  act[intro]: "Basic \<alpha> \<mapsto>[\<alpha>,[]] Nil" |
  ino[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r] c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;\<^sub>w c\<^sub>2 \<mapsto>[\<alpha>',r] c\<^sub>1' ;\<^sub>w c\<^sub>2" |
  ooo[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r] c\<^sub>1' \<Longrightarrow> \<alpha>'' < c\<^sub>2 <\<^sub>w \<alpha>' \<Longrightarrow> 
                                      c\<^sub>2 ;\<^sub>w c\<^sub>1 \<mapsto>[\<alpha>'',(Reorder \<alpha>' w c\<^sub>2) # r] c\<^sub>2 ;\<^sub>w c\<^sub>1'" |
  cap[intro]: "c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> poppableBasic s s' \<alpha>' \<Longrightarrow> 
                           Capture s c \<mapsto>[popbasic s s' \<alpha>', Scope # r] Capture s' c'" |
  inter1[intro]: "c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> (\<triangle>c) \<mapsto>[\<alpha>',r] (\<triangle>c')"     
                   (*interrupt can terminate c\<^sub>1 at any time (with a silent step, see below) *) 
inductive_cases lexecuteE[elim]: "c \<mapsto>[\<alpha>',p] c'"

fun beforeReord :: "('a,'b) basic \<Rightarrow> ('a,'b) bookkeeping \<Rightarrow> ('a,'b) basic set"
  where
  "beforeReord \<alpha>' [] = {\<alpha>'}" |
  "beforeReord \<alpha>' (Scope#rs) = \<Union>{beforeReord (pushbasic s s' \<alpha>') rs | s s'. True}" |
  "beforeReord \<alpha>' ((Reorder \<alpha> w c\<^sub>2)#rs) =  (beforeReord \<alpha> rs)"


text \<open>Small step semantics for a global execution step\<close>
inductive gexecute :: "('a,'b) com \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) com \<Rightarrow> bool"
  ("_ \<mapsto>[_] _" [71,0,71] 70)
  where
  thr[intro]: "c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> Thread c \<mapsto>[beh \<alpha>'] Thread c'" |
  par1[intro]: "c\<^sub>1 \<mapsto>[g] c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>[g] c\<^sub>1' || c\<^sub>2" |
  par2[intro]: "c\<^sub>2 \<mapsto>[g] c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>[g] c\<^sub>1 || c\<^sub>2'"
inductive_cases gexecuteE[elim]: "c \<mapsto>[g] c'"


text \<open>Small step semantics for a silent step\<close>
inductive silent :: "('a,'b) com \<Rightarrow> ('a,'b) com \<Rightarrow> bool"
  ("_ \<leadsto> _" [71,71] 70)
  where
  seq1[intro]:    "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;\<^sub>w c\<^sub>2 \<leadsto> c\<^sub>1' ;\<^sub>w c\<^sub>2" |
  seq2[intro]:    "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 ;\<^sub>w c\<^sub>2 \<leadsto> c\<^sub>1 ;\<^sub>w c\<^sub>2'" |
  seqE1[intro]:   "Nil ;\<^sub>w c\<^sub>1 \<leadsto> c\<^sub>1" |
  seqE2[intro]:   "c\<^sub>1 ;\<^sub>w Nil \<leadsto> c\<^sub>1" |
  pick[intro]:    "Choice S \<leadsto> S l" |
  loop1[intro]:   "c*\<^sub>w \<leadsto> Nil" |
  loop2[intro]:   "c*\<^sub>w \<leadsto> c ;\<^sub>w c*\<^sub>w" |
  par1[intro]:    "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1' || c\<^sub>2" |
  par2[intro]:    "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1 || c\<^sub>2'" |
  parE1[intro]:   "Nil || c \<leadsto> c" |
  parE2[intro]:   "c || Nil \<leadsto> c" |
  thr[intro]:     "c \<leadsto> c' \<Longrightarrow> Thread c \<leadsto> Thread c'" |
  thrE[intro]:    "Thread Nil \<leadsto> Nil"  |
  capE[intro]:    "Capture k Nil \<leadsto> Nil" |
  capS[intro]:    "c \<leadsto> c' \<Longrightarrow> Capture k c \<leadsto> Capture k c'" |
  intr1[intro]:   "c \<leadsto> c' \<Longrightarrow>  (\<triangle>c) \<leadsto> (\<triangle>c')" |
  intrE[intro]:    "(\<triangle> c) \<leadsto> Nil" 

inductive_cases silentE[elim]: "c\<^sub>1 \<leadsto> c\<^sub>1'"

text \<open>A local execution step implies the program has changed\<close>
lemma execute_neq:
  assumes "c \<mapsto>[\<alpha>'',r] c'"
  shows "c \<noteq> c'"
  using assms by (induct) auto 

lemma [simp]:
  "c \<mapsto>[\<alpha>'',r] c = False"
  using execute_neq by blast

text \<open>A global execution step implies the program has changed\<close>
lemma gexecute_neq:
  assumes "c \<mapsto>[g] c'"
  shows "c \<noteq> c'"
  using assms by (induct) auto

lemma [simp]:
  "c \<mapsto>[g] c = False"
  using gexecute_neq by blast

text \<open>An execution step will not introduce parallelism\<close>
lemma local_execute:
  "c \<mapsto>[\<alpha>'',r] c' \<Longrightarrow> local c \<Longrightarrow> local c'"
 by (induct rule: lexecute.induct) (auto) 

text \<open>A silent step will not introduce parallelism\<close>
lemma local_silent:
  "c \<leadsto> c' \<Longrightarrow> local c \<Longrightarrow> local c'"  
  by (induct rule: silent.induct) (auto simp add: local_execute)

section \<open>Transition Definitions\<close>

text \<open>These transitions are over configurations of (program,state)\<close>

text \<open>Environment Transition\<close>
abbreviation env_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -e\<rightarrow> _" [81,81] 80)
  where "s -e\<rightarrow> s' \<equiv> fst s = fst s'"

text \<open>Program Execution Transition\<close>
abbreviation exec_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -\<alpha>\<rightarrow> _" [81,81] 80)
  where "s -\<alpha>\<rightarrow> s' \<equiv> \<exists>g. fst s \<mapsto>[g] (fst s') \<and> (snd s,snd s') \<in> g"

text \<open>Program Silent Transition\<close>
abbreviation sil_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -s\<rightarrow> _" [81,81] 80)
  where "s -s\<rightarrow> s' \<equiv> fst s \<leadsto> fst s' \<and> snd s = snd s'"

text \<open>Program Transition\<close>
abbreviation com_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -c\<rightarrow> _" [81,81] 80)
  where "s -c\<rightarrow> s' \<equiv> s -\<alpha>\<rightarrow> s' \<or> s -s\<rightarrow> s'"

text \<open>Collect of all possible transitions\<close>
inductive_set transitions :: "('a,'b) config list set"
  where
    one[intro]: "[s] \<in> transitions" |
    env[intro]: "s -e\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    prg[intro]: "s -\<alpha>\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    sil[intro]: "s -s\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions"
inductive_cases transitionsE[elim]: "t \<in> transitions"


section \<open>Observable atomics\<close>

(*non-deterministic in that a step might be taken or not and hence an event observed or not;

   for global operations (thread, par) obs_traces are collected per thread (w/o interspersing)
   which still allows to determine the overall observed events as union over all obs_traces *)

inductive obs_trace
  where
    "obs_trace [] c" |
    "c \<leadsto> c' \<Longrightarrow> obs_trace t c' \<Longrightarrow> obs_trace t c" |
    "c \<mapsto>[\<alpha>,r] c' \<Longrightarrow> obs_trace t c' \<Longrightarrow> obs_trace (\<alpha>#t) c" |
    "obs_trace t c \<Longrightarrow> obs_trace t (Thread c)" |
    "obs_trace t c \<Longrightarrow> obs_trace t (c || c2)" |
    "obs_trace t c \<Longrightarrow> obs_trace t (c2 || c)"
 
definition obs
  where "obs c \<equiv> {\<alpha>. \<exists>t. \<alpha> \<in> set t \<and> obs_trace t c}"

lemma obs_exec:
  assumes "c \<mapsto>[\<alpha>',r] c'"
  shows "obs c \<supseteq> obs c'"
  unfolding obs_def using assms obs_trace.intros(3) 
  by (smt (verit, best) Collect_mono set_subset_Cons subsetD)

lemma obs_sil:
  assumes "c \<leadsto> c'"
  shows "obs c \<supseteq> obs c'"
  unfolding obs_def using assms obs_trace.intros(2) by auto

lemma obs_act:
  assumes "c \<mapsto>[\<alpha>',r] c'"
  shows "\<alpha>' \<in> obs c"
  using assms unfolding obs_def 
  by clarsimp (meson list.set_intros(1) obs_trace.intros(1,3))

lemma obs_nil [simp]:
  "obs Nil = {}"
  by (auto simp: obs_def elim: obs_trace.cases)

lemma obs_seq: 
  assumes "c\<^sub>1 ;\<^sub>w c\<^sub>2 \<mapsto>[\<alpha>',r] c\<^sub>1' ;\<^sub>w c\<^sub>2"
  shows "\<alpha>' \<in> obs (c\<^sub>1 ;\<^sub>w c\<^sub>2)"
  using assms obs_act by auto 

lemma obs_seq2:
  assumes "c\<^sub>1 ;\<^sub>w c\<^sub>2 \<mapsto>[\<alpha>',r] c\<^sub>1 ;\<^sub>w c\<^sub>2'"
  shows "\<alpha>' \<in> obs (c\<^sub>1 ;\<^sub>w c\<^sub>2)"
  using assms obs_act by auto 

lemma obs_trace_NilE [elim!]:
  assumes "obs_trace t com.Nil"
  obtains "t = []"
  using assms
  by (induct t "Nil ::  ('a, 'b) com") auto

lemma obs_trace_BasicE [elim!]:
  assumes "obs_trace t (Basic \<alpha>)"
  obtains "t = [\<alpha>]" | "t = []"
  using assms
  by (induct t "Basic \<alpha>") auto

lemma obs_basic [simp]:
  "obs (Basic \<alpha>) = {\<alpha>}"
  unfolding obs_def apply (auto)
  apply (intro exI conjI)
  prefer 2
  apply (rule obs_trace.intros(3))
    apply (rule act)
  apply (rule obs_trace.intros(1))
  apply auto
  done


lemma obs_trace_ThreadE:
  assumes "obs_trace t (Thread c)" 
  shows "obs_trace t c"
  using assms
proof (induct t "Thread c" arbitrary: c)
  case 1
  then show ?case by (auto intro: obs_trace.intros)
next
  case (2 c' t)
  show ?case using 2(1)
  proof (cases rule: silentE, blast; clarsimp)
    fix c'' assume a: "Thread c \<leadsto> Thread c''" "c' = Thread c''" "c \<leadsto> c''"
    hence "obs_trace t c''" using 2 by auto
    thus "obs_trace t c" using a by (auto intro: obs_trace.intros)
  next
    assume "c' = Nil"
    hence "t = []" using 2 by auto
    thus "obs_trace t Nil" by (auto intro: obs_trace.intros)
  qed
next
  case (3 \<alpha> r c' t)
  then show ?case by auto
qed

lemma obs_trace_ParE:
  assumes "obs_trace t (c\<^sub>1 || c\<^sub>2)"
  obtains "obs_trace t c\<^sub>1" | "obs_trace t c\<^sub>2"
  using assms
proof (induct t "c\<^sub>1 || c\<^sub>2" arbitrary: c\<^sub>1 c\<^sub>2)
  case 1
  then show ?case by (auto intro: obs_trace.intros)
next
  case (2 c' t)
  show ?case using 2(1)
  proof (cases rule: silent.cases)
    case (par1 c\<^sub>1')
    then show ?thesis using 2 obs_trace.intros(2) by auto
  next
    case (par2 c\<^sub>2')
    then show ?thesis using 2 obs_trace.intros(2) by auto
  next
    case parE1
    then show ?thesis using 2 obs_trace.intros(2) by auto
  next
    case parE2
    then show ?thesis using 2 obs_trace.intros(2) by auto
  qed
qed (auto intro: obs_trace.intros)

lemma obs_thread [simp]:
  "obs (Thread c) = obs c"
  unfolding obs_def using obs_trace_ThreadE
  by (auto intro: obs_trace.intros)

lemma obs_par [simp]:
  "obs (c\<^sub>1 || c\<^sub>2) = obs c\<^sub>1 \<union> obs c\<^sub>2"
  unfolding obs_def using obs_trace_ParE
  by (auto intro: obs_trace.intros) blast

lemma obs_gex:
  assumes "c \<mapsto>[g] c'"
  shows "obs c \<supseteq> obs c'"
  unfolding obs_def using assms obs_sil obs_exec
    obs_thread obs_par obs_def by (induct) auto 


lemma obsE:
  assumes "obs_trace (\<alpha>#t) c"
  obtains c' r where "c \<mapsto>[\<alpha>,r] c'" "obs_trace t c'"
  using assms 
proof (induct rule:obs_trace.induct)
  case (1 c)
  then show ?case sorry
next
  case (2 c c' t)
  then show ?case sorry
next
  case (3 c \<alpha> r c' t)
  then show ?case sorry
next
  case (4 t c)
  then show ?case sorry
next
  case (5 t c c2)
  then show ?case sorry
next
  case (6 t c c2)
  then show ?case using obs_trace_ParE sorry
qed 

(* these don't hold:
lemma obs_seq3:
  "obs(c1 ;\<^sub>w c2) = obs(c\<^sub>1) \<union> obs(c\<^sub>2) \<union> {\<alpha>'. \<alpha> \<in> obs(c\<^sub>2) \<and> \<alpha>' < c\<^sub>1 <\<^sub>w \<alpha>}" sorry

lemma obs_choice:
  "obs(Choice S) = obs(S l)" unfolding obs_def sorry

lemma obs_loop:
  "obs(c*\<^sub>w) = obs(c) \<union> {\<alpha>'. \<alpha> \<in> obs(c) \<and> \<alpha>' < c <\<^sub>w \<alpha>}" sorry

these might hold:
lemma obs_capture:
  " \<alpha> \<in> obs(c) \<Longrightarrow> (popbasic s s' \<alpha>) \<in> obs(Capture s c)" sorry

lemma obs_inter:
  "obs(\<triangle> c) = obs(c)" sorry
*)


end

end