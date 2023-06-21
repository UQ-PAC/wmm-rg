theory Semantics
  imports Atomics (* CaptureReasoning *)

begin

chapter \<open>Small Step Semantics\<close>

text \<open>
Define the small step semantics for the While language, with weak memory model behaviours.
Also introduces a notion of configuration, that couples programs and memory states,
with transitions for the program and the environment.
\<close>

type_synonym ('a,'b,'c) config = "('a,'b,'c) com \<times> 'b"

text \<open>
To simplify the identification of reordered instructions, we instrument the semantics with
bookkeeping data structures to track how the reordering relation has been applied.
\<close>
datatype ('a,'b,'c) log =
  Reorder "('a,'b) basic" "('a,'b) wmm" "('a,'b,'c) com" |
  Scope

type_synonym ('a,'b,'c) bookkeeping = "('a,'b,'c) log list"

text \<open> Locale semantics fixes the types 'a and 'b state; 
        parameters exists_act and exists_state  are used as dummies to do so \<close>

locale sem_exists =
  fixes exists_act :: "'a"

locale semantics = pstate push + sem_exists exists_act
  for exists_act :: "'a"
  and push :: "'b \<Rightarrow> 'c \<Rightarrow> 'b"  

context semantics
begin

text \<open> (w \<alpha>' \<beta> \<alpha>) is an abstract reordering relation that evaluates to true if
          \<alpha> can reorder over \<beta> to become \<alpha>' under WMM w; it is carried around 
          as a subscript to reordering relation _ < _ < _  \<close>

text \<open>Extend a reordering relation recursively over a program\<close>
fun reorder_com :: "('a,'b) basic \<Rightarrow> ('a,'b,'c) com \<Rightarrow> ('a,'b) wmm \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  ("_ < _ <\<^sub>_ _" [100,0,0,100] 100)
  where
    "\<alpha>' < Nil <\<^sub>c \<alpha> = (\<alpha>' = \<alpha>)" |
    "\<alpha>' < Basic \<beta> <\<^sub>w \<alpha> = (w \<alpha>' \<beta> \<alpha>)" |
    "\<alpha>' < c\<^sub>1 ;\<^sub>w c\<^sub>2 <\<^sub>c \<alpha> = (\<exists>\<alpha>\<^sub>n. \<alpha>' < c\<^sub>1 <\<^sub>c \<alpha>\<^sub>n \<and> \<alpha>\<^sub>n < c\<^sub>2 <\<^sub>c \<alpha>)" |
    "_ < _ <\<^sub>c _ = False"

section \<open>Program Transition Definitions\<close>

text \<open>Small step semantics for a local execution step\<close>
inductive lexecute :: "('a,'b,'c) com \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b,'c) bookkeeping \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool"
  ("_ \<mapsto>[_,_] _" [71,0,0,71] 70)
  where
  act[intro]: "Basic \<alpha> \<mapsto>[\<alpha>,[]] Nil" |
  ino[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r] c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;\<^sub>w c\<^sub>2 \<mapsto>[\<alpha>',r] c\<^sub>1' ;\<^sub>w c\<^sub>2" |
  ooo[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r] c\<^sub>1' \<Longrightarrow> \<alpha>'' < c\<^sub>2 <\<^sub>w \<alpha>' \<Longrightarrow> 
                                      c\<^sub>2 ;\<^sub>w c\<^sub>1 \<mapsto>[\<alpha>'',(Reorder \<alpha>' w c\<^sub>2) # r] c\<^sub>2 ;\<^sub>w c\<^sub>1'" |
  cap[intro]: "c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> Capture s c \<mapsto>[popbasic s s' \<alpha>', Scope # r] Capture s' c'" |
  inter1[intro]: "c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> (\<triangle>c) \<mapsto>[\<alpha>',r] (\<triangle>c')"     
                   (*interrupt can terminate c\<^sub>1 at any time (with a silent step, see below) *) 
inductive_cases lexecuteE[elim]: "c \<mapsto>[\<alpha>',p] c'"

text \<open>Small step semantics for a global execution step\<close>
inductive gexecute :: "('a,'b,'c) com \<Rightarrow> 'b rel \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool"
  ("_ \<mapsto>[_] _" [71,0,71] 70)
  where
  thr[intro]: "c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> Thread c \<mapsto>[beh \<alpha>'] Thread c'" |
  par1[intro]: "c\<^sub>1 \<mapsto>[g] c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>[g] c\<^sub>1' || c\<^sub>2" |
  par2[intro]: "c\<^sub>2 \<mapsto>[g] c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>[g] c\<^sub>1 || c\<^sub>2'"
inductive_cases gexecuteE[elim]: "c \<mapsto>[g] c'"

text \<open>Small step semantics for a silent step\<close>
inductive silent :: "('a,'b,'c) com \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool"
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
abbreviation env_tran :: "('a,'b,'c) config \<Rightarrow> ('a,'b,'c) config \<Rightarrow> bool" ("_ -e\<rightarrow> _" [81,81] 80)
  where "s -e\<rightarrow> s' \<equiv> fst s = fst s'"

text \<open>Program Execution Transition\<close>
abbreviation exec_tran :: "('a,'b,'c) config \<Rightarrow> ('a,'b,'c) config \<Rightarrow> bool" ("_ -\<alpha>\<rightarrow> _" [81,81] 80)
  where "s -\<alpha>\<rightarrow> s' \<equiv> \<exists>g. fst s \<mapsto>[g] (fst s') \<and> (snd s,snd s') \<in> g"

text \<open>Program Silent Transition\<close>
abbreviation sil_tran :: "('a,'b,'c) config \<Rightarrow> ('a,'b,'c) config \<Rightarrow> bool" ("_ -s\<rightarrow> _" [81,81] 80)
  where "s -s\<rightarrow> s' \<equiv> fst s \<leadsto> fst s' \<and> snd s = snd s'"

text \<open>Program Transition\<close>
abbreviation com_tran :: "('a,'b,'c) config \<Rightarrow> ('a,'b,'c) config \<Rightarrow> bool" ("_ -c\<rightarrow> _" [81,81] 80)
  where "s -c\<rightarrow> s' \<equiv> s -\<alpha>\<rightarrow> s' \<or> s -s\<rightarrow> s'"

text \<open>Collect of all possible transitions\<close>
inductive_set transitions :: "('a,'b,'c) config list set"
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

inductive obs_trace :: "('a,'b) basic list \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool"
  where
     1:  "obs_trace [] c" |
     2:  "c \<leadsto> c' \<Longrightarrow> obs_trace t c' \<Longrightarrow> obs_trace t c" |
     3:  "c \<mapsto>[\<alpha>,r] c' \<Longrightarrow> obs_trace t c' \<Longrightarrow> obs_trace (\<alpha>#t) c" |
     4:  "obs_trace t c \<Longrightarrow> obs_trace t (Thread c)" |
     5:  "obs_trace t c \<Longrightarrow> obs_trace t (c || c2)" |
     6:  "obs_trace t c \<Longrightarrow> obs_trace t (c2 || c)"


definition obs :: "('a,'b,'c) com \<Rightarrow> ('a,'b) basic set"
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

lemma obs_seq3:
  assumes "c \<mapsto>[\<alpha>',r] c'"
  shows "\<alpha>' \<in> obs (c ;\<^sub>w c\<^sub>2)"
  using assms lexecute.intros(2) obs_def obs_act obs_seq 
  by meson


lemma obs_trace_NilE [elim!]:
  assumes "obs_trace t com.Nil"
  obtains "t = []"
  using assms
  by (induct t "Nil ::  ('a,'b,'c) com") auto

lemma obs_trace_BasicE [elim!]:
  assumes "obs_trace t (Basic \<alpha>)"
  obtains "t = [\<alpha>]" | "t = []"
  using assms
  by (induct t "Basic \<alpha> ::  ('a,'b,'c) com") auto

lemma obs_basic [simp]:
  "obs (Basic \<alpha>) = {\<alpha>}"
  unfolding obs_def apply (auto)
  apply (intro exI conjI)
  prefer 2
  apply (rule obs_trace.intros(3))
    apply (rule lexecute.act)
  apply (rule obs_trace.intros(1))
  apply auto
  done

(*
lemma obsTrace_actE:
  assumes "obs_trace t c" "t \<noteq> []"
  obtains \<alpha> r c' where "\<alpha> \<in> set t" "c \<mapsto>[\<alpha>,r] c'"
  using assms 
proof (induct t)
  case Nil
  then show ?case using obs_trace.intros by blast
next
  case (Cons a t)
  then show ?case using assms Cons sorry

qed
*)
(*
   (\<And>\<alpha> r c'. \<alpha> \<in> set t \<Longrightarrow> c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> thesis) \<Longrightarrow> obs_trace t c \<Longrightarrow> t \<noteq> [] \<Longrightarrow> thesis
    ?\<alpha> \<in> set (a # t) \<Longrightarrow> c \<mapsto>[\<alpha>',?r] ?c' \<Longrightarrow> thesis
    obs_trace (a # t) c
    a # t \<noteq> []

goal (1 subgoal):
 1. \<And>a t. ((\<And>\<alpha> r c'. \<alpha> \<in> set t \<Longrightarrow> c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> thesis) \<Longrightarrow> obs_trace t c \<Longrightarrow> t \<noteq> [] \<Longrightarrow> thesis)
 \<Longrightarrow> (\<And>\<alpha> r c'. \<alpha> \<in> set (a # t) \<Longrightarrow> c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> thesis) \<Longrightarrow> obs_trace (a # t) c \<Longrightarrow> a # t \<noteq> [] 
 \<Longrightarrow> thesis
*)
(*
lemma obs_actE:
  assumes "\<alpha>' \<in> obs c" "obs c \<noteq> {}"
  obtains \<alpha> r c' where "c \<mapsto>[\<alpha>',r] c'"
  using assms obsTrace_actE obs_def obs_trace.intros(1)
  by (smt (verit, best) empty_Collect_eq empty_set equals0D)
*)
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


inductive_set local_trace :: "(('a,'b,'c) com \<times> ('a,'b) basic list \<times> ('a,'b,'c) com) set"
  and local_trace_abv :: "('a,'b,'c) com \<Rightarrow> ('a,'b) basic list \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool" ("_ \<mapsto>\<^sub>l\<^sup>*_ _" [50,40,40] 70)
  where
  "local_trace_abv c t c' \<equiv> (c, t, c') \<in> local_trace"
  | noStep[intro]: "c \<mapsto>\<^sub>l\<^sup>*[] c" 
  | silStep[intro]: "c\<^sub>1 \<leadsto> c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sub>l\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sub>l\<^sup>*t c\<^sub>3"
  | lexStep[intro]: "c\<^sub>1 \<mapsto>[\<alpha>,r] c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sub>l\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sub>l\<^sup>*\<alpha>#t c\<^sub>3"
  | trStep[intro]:  "c\<^sub>1 \<mapsto>\<^sub>l\<^sup>*t c\<^sub>2 \<Longrightarrow> (Thread c\<^sub>1) \<mapsto>\<^sub>l\<^sup>*t c\<^sub>2" 
  | parLStep[intro]:  "c\<^sub>1 \<mapsto>\<^sub>l\<^sup>*t c\<^sub>2  \<Longrightarrow> (c\<^sub>1 || c) \<mapsto>\<^sub>l\<^sup>*t (c\<^sub>2 || c)"
  | parRStep[intro]:  "c\<^sub>1 \<mapsto>\<^sub>l\<^sup>*t c\<^sub>2  \<Longrightarrow> (c || c\<^sub>1) \<mapsto>\<^sub>l\<^sup>*t (c || c\<^sub>2)"



lemma localTr_obsTrace:
  assumes "c \<mapsto>\<^sub>l\<^sup>*t c'"
  shows "obs_trace t c"
  using assms 
proof (induct arbitrary: "c'")
  case (noStep c)
  then show ?case using obs_trace.intros(1)[of "c"] by simp
next
  case (silStep c\<^sub>1 c\<^sub>2 t c\<^sub>3)
  then show ?case using obs_trace.intros(2)[of "c\<^sub>1""c\<^sub>2""t"] by simp 
next
  case (lexStep c\<^sub>1 \<alpha> r c\<^sub>2 t c\<^sub>3)
  then show ?case using obs_trace.intros(3)[of "c\<^sub>1""\<alpha>""r""c\<^sub>2""t"] by simp
next
  case (trStep c\<^sub>1 t c\<^sub>2)
  then show ?case using obs_trace.intros(4)[of "t""c\<^sub>1"] by simp
next
  case (parLStep c\<^sub>1 t c\<^sub>2 c)
  then show ?case using obs_trace.intros(5)[of "t""c\<^sub>1""c"] by simp
next
  case (parRStep c\<^sub>1 t c\<^sub>2 c)
  then show ?case using obs_trace.intros(6)[of "t""c\<^sub>1""c"] by simp
qed




lemma obsTrace_localTr:
  assumes "obs_trace t c"
  obtains c' where "c \<mapsto>\<^sub>l\<^sup>*t c'"
  using assms 
proof (induct)
  case (1 c)                 (* Nil *)
  then show ?case by blast
next
  case (2 c c' t)            (*  \<leadsto> *)
  then show ?case by blast
next
  case (3 c \<alpha> r c' t)        (* c \<mapsto>[\<alpha>,r] c' *)
  then show ?case 
  proof -
    have a0:"obs_trace (\<alpha> # t) c" 
      using 3 obs_trace.intros(3)[of "c""\<alpha>""r""c'""t"] by simp
    then show ?thesis
      using local_trace.lexStep[of "c" "\<alpha>""r""c'""t""c''"] 3 3(4)[of "c''"] by blast
  qed
next
  case (4 t c)                (* Thread c *) 
  then show ?case using obs_trace.intros(4)[of "t" "c"] 4(3)[of "c'"] 
                  local_trace.trStep[of "c""t""c'"] 4(3)[of "c''"] by auto
next
  case (5 t c c2)             (* c || c2 \<mapsto>\<^sub>l\<^sup>*t c' *)
  then show ?case using obs_trace.intros(5)[of "t""c""c''"] 5(3)[of "c''"] by auto
next
  case (6 t c c2)             (* c2 || c \<mapsto>\<^sub>l\<^sup>*t c' *)
  then show ?case using obs_trace.intros(6)[of "t""c""c''"] 6(3)[of "c''"] by auto
qed

end

end