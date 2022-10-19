theory Semantics
  imports Atomics CaptureReasoning

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

locale semantics =
  fixes exists_act :: "'a"
  fixes exists_state :: "'b::state"

context semantics
begin

text \<open> (w \<alpha>' \<beta> \<alpha>) is an abstract reordering relation that evaluates to true if
          \<alpha> can reorder over \<beta> to become \<alpha>' under WMM w; it is carried around 
          as a subscript to reordering relation _ < _ < _  \<close>

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
  ooo[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r] c\<^sub>1' \<Longrightarrow> \<alpha>'' < c\<^sub>2 <\<^sub>w \<alpha>' \<Longrightarrow> c\<^sub>2 ;\<^sub>w c\<^sub>1 \<mapsto>[\<alpha>'',(Reorder \<alpha>' w c\<^sub>2) # r] c\<^sub>2 ;\<^sub>w c\<^sub>1'" |
  cap[intro]: "c \<mapsto>[\<alpha>',r] c' \<Longrightarrow> Capture s c \<mapsto>[popbasic s s' \<alpha>',Scope#r] Capture s' c'"  
inductive_cases lexecuteE[elim]: "c \<mapsto>[\<alpha>',p] c'"

(*
lemma lexecute_triple: "c \<mapsto>[\<alpha>',r,\<alpha>] c' \<Longrightarrow> \<alpha>' = \<alpha>\<llangle>r\<rrangle>"
by (induct rule: lexecute.induct) auto
*)

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
  capS[intro]:    "c \<leadsto> c' \<Longrightarrow> Capture k c \<leadsto> Capture k c'" 
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


lemma basics_lexec:
  assumes "lexecute c \<alpha> r c'" shows "(beforeReord \<alpha> r) \<inter> (basics c) \<noteq> {}"
  using assms
proof (induct)
  case (act \<alpha>)
  then show ?case by auto
next
  case (ino c\<^sub>1 \<alpha>' r c\<^sub>1' w c\<^sub>2)
  then show ?case by auto
next
  case (ooo c\<^sub>1 \<alpha>' r c\<^sub>1' \<alpha>'' c\<^sub>2 w)
  then have a0:"c\<^sub>2 ;\<^sub>w c\<^sub>1 \<mapsto>[\<alpha>'',(Reorder \<alpha>' w c\<^sub>2) # r] c\<^sub>2 ;\<^sub>w c\<^sub>1'" by auto
  then show ?case using ooo  by auto
next
  case (cap c \<alpha>' r c' s s')
  assume a2:" beforeReord \<alpha>' r \<inter> basics c \<noteq> {}" 
  have p: "poppable s (vc \<alpha>')" sorry 
  have p2:"poppable_rel s s' (beh \<alpha>')" sorry
  have a0:"pushpred s (poppred' s (vc \<alpha>')) = vc \<alpha>'" using p by (meson poppable_push_poppred')
  have a1:"pushrel s s' (poprel' s s' (beh \<alpha>')) = beh \<alpha>'" using p2 poppable_push_poprel' by blast 
  have a3:"beforeReord \<alpha>' r \<subseteq> \<Union> {beforeReord (pushbasic sa s'a (popbasic s s' \<alpha>')) r |sa s'a. True}" 
    using a0 a1
    by (metis (mono_tags, lifting) Sup_upper fst_conv mem_Collect_eq p2 prod.exhaust_sel snd_conv) 
  show ?case using cap unfolding beforeReord.simps basics_simps a3 
    by (smt (verit, best) Union_disjoint a0 mem_Collect_eq p2 prod.exhaust_sel prod.sel(1) snd_conv)
qed

text \<open>A silent step will not introduce parallelism\<close>
lemma local_silent:
  "c \<leadsto> c' \<Longrightarrow> local c \<Longrightarrow> local c'"  
  by (induct rule: silent.induct) (auto simp add: local_execute)

text \<open>An execution step will not introduce new basics\<close>
lemma basics_exec:
  assumes "c \<mapsto>[\<alpha>'',r] c'" 
  shows "basics c \<supseteq> basics c'"
  using assms by induct (auto, blast)

text \<open>A silent step will not introduce new basics\<close>
lemma basics_silent:
  assumes "c \<leadsto> c'" 
  shows "basics c \<supseteq> basics c'"
  using assms by induct (auto, blast)

text \<open>A global execution step will not introduce new basics\<close>

lemma basics_par: 
  assumes "gexecute c g c'" 
  shows "basics c\<^sub>1 \<subseteq> basics (c\<^sub>1 || c\<^sub>2)" 
        "basics c\<^sub>2 \<subseteq> basics (c\<^sub>1 || c\<^sub>2)" 
  using assms by simp+

lemma basics_gexec:
  assumes "c \<mapsto>[g] c'" 
  shows "basics c \<supseteq> basics c'"
  using assms using basics_exec basics_par by (induct) auto


section \<open>Transition Definitions\<close>

text \<open>These transitions are over configurations of (program,state)\<close>

text \<open>Environment Transition\<close>
abbreviation env_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -e\<rightarrow> _" [81,81] 80)
  where "s -e\<rightarrow> s' \<equiv> fst s = fst s'"

text \<open>Program Execution Transition\<close>
abbreviation exec_tran :: "('a,'b) config \<Rightarrow> ('a,'b) config \<Rightarrow> bool" ("_ -\<alpha>\<rightarrow> _" [81,81] 80)
  where "s -\<alpha>\<rightarrow> s' \<equiv> \<exists>g. fst s \<mapsto>[g] (fst s') \<and> (snd s,snd s') \<in> g"

(* does the mem-state stay the same over a Capture step? *)
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
end

end