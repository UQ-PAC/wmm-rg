theory Semantics
  imports Reordering CaptureReasoning
begin

chapter \<open>Small Step Semantics\<close>

text \<open>
Define the small step semantics for the While language, with weak memory model behaviours.
Also introduces a notion of configuration, that couples programs and memory states,
with transitions for the program and the environment.
\<close>

type_synonym ('a,'b) config = "('a,'b) com \<times> 'b"

locale semantics = reordering 

context semantics
begin

section \<open>Program Transition Definitions\<close>


(* this is a hack to keep bookkeeping information for which states were popped from a Capture
transition. *)
abbreviation Capture2 where
"Capture2 s s' c \<equiv> Capture s' (Capture s c)"

text \<open>
Semantics that collects reordering effects.
Given c \<mapsto>[r,\<alpha>'] c', this corresponds to c \<mapsto>\<alpha><r> c', such that
r should be the program \<alpha>' has to reorder with in c to execute and 
\<alpha> should be \<alpha>' forwarded across r.\<close>
inductive lexecute :: "('a,'b) com \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) com \<Rightarrow> bool"
  ("_ \<mapsto>[_,_,_] _" [71,0,0,0,71] 70)
  where
  act[intro]: "Basic \<alpha> \<mapsto>[\<alpha>,Nil,\<alpha>] Nil" |
  ino[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r,\<alpha>] c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<mapsto>[\<alpha>',r,\<alpha>] c\<^sub>1' ;; c\<^sub>2" |
  ord[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r,\<alpha>] c\<^sub>1' \<Longrightarrow> c\<^sub>1 \<cdot> c\<^sub>2 \<mapsto>[\<alpha>',r,\<alpha>] c\<^sub>1' \<cdot> c\<^sub>2" |
  ooo[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r,\<alpha>] c\<^sub>1' \<Longrightarrow> \<alpha>'' < c\<^sub>2 <\<^sub>c \<alpha>' \<Longrightarrow> c\<^sub>2 ;; c\<^sub>1 \<mapsto>[\<alpha>'',c\<^sub>2 ;; r ,\<alpha>] c\<^sub>2 ;; c\<^sub>1'"
  (* | cap[intro]: "c \<mapsto>[\<alpha>',r,\<alpha>] c' \<Longrightarrow> Capture s c \<mapsto>[popbasic' s s' \<alpha>',Capture2 s s' r,\<alpha>] Capture s' c'" *)
(*   cap[intro]: "c\<^sub>1 \<mapsto>[r,\<alpha>] c\<^sub>1' \<Longrightarrow> 
    Capture s c\<^sub>1 \<mapsto>[Nil,
      (tag \<alpha>\<llangle>r\<rrangle>, {m. merge m s \<in> vc \<alpha>\<llangle>r\<rrangle>}, {(m,m'). (merge m s, merge m' s') \<in> beh \<alpha>\<llangle>r\<rrangle>})] 
    Capture s' c\<^sub>1'" *)
  (* | capNil[intro]: "c\<^sub>1 \<mapsto>[r,\<alpha>] c\<^sub>1' \<Longrightarrow> Capture s c\<^sub>1 \<mapsto>[f r,capBasic \<alpha>\<llangle>r\<rrangle> s s'] Capture s' c\<^sub>1'"  *)
inductive_cases lexecuteE[elim]: "c \<mapsto>[\<alpha>',p,\<alpha>] c'"
(* 
DONE: replace the [r,\<alpha>] with a triple [\<alpha>',r,\<alpha>] which will allow the r to hold
"Capture s r", i.e., [\<alpha>', Capture s r, \<alpha>]. 
Then, the \<alpha>' is the one which describes the effects which are
visible from that local execution step. *)


lemma lexecute_triple: "c \<mapsto>[\<alpha>',r,\<alpha>] c' \<Longrightarrow> \<alpha>' = \<alpha>\<llangle>r\<rrangle>"
by (induct rule: lexecute.induct) auto


inductive gexecute :: "('a,'b) com \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) com \<Rightarrow> bool"
  ("_ \<mapsto>[_] _" [71,0,71] 70)
  where
  thr[intro]: "c \<mapsto>[\<alpha>',r,\<alpha>] c' \<Longrightarrow> Thread c \<mapsto>[beh \<alpha>'] Thread c'" |
  par1[intro]: "c\<^sub>1 \<mapsto>[g] c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>[g] c\<^sub>1' || c\<^sub>2" |
  par2[intro]: "c\<^sub>2 \<mapsto>[g] c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<mapsto>[g] c\<^sub>1 || c\<^sub>2'"
inductive_cases gexecuteE[elim]: "c \<mapsto>[g] c'"

text \<open>Small step semantics for a silent step\<close>
inductive silent :: "('a,'b) com \<Rightarrow> ('a,'b) com \<Rightarrow> bool"
  ("_ \<leadsto> _" [71,71] 70)
  where
  seq1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<leadsto> c\<^sub>1' ;; c\<^sub>2" |
  ord1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 \<cdot> c\<^sub>2 \<leadsto> c\<^sub>1' \<cdot> c\<^sub>2" |
  seq2[intro]:  "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<leadsto> c\<^sub>1 ;; c\<^sub>2'" |
  seqE1[intro]: "Nil ;; c\<^sub>1 \<leadsto> c\<^sub>1" |
  seqE2[intro]: "c\<^sub>1 ;; Nil \<leadsto> c\<^sub>1" |
  ordE[intro]:  "Nil \<cdot> c\<^sub>1 \<leadsto> c\<^sub>1" |
  bigc[intro]:  "s \<in> S \<Longrightarrow> (\<Sqinter> S) \<leadsto> seq2com s" |
  left[intro]:  "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>1" |
  right[intro]: "c\<^sub>1 \<sqinter> c\<^sub>2 \<leadsto> c\<^sub>2" |
  loop1[intro]: "c* \<leadsto> Nil" |
  loop2[intro]: "c* \<leadsto> c ;; c*" |
  par1[intro]:  "c\<^sub>1 \<leadsto> c\<^sub>1' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1' || c\<^sub>2" |
  par2[intro]:  "c\<^sub>2 \<leadsto> c\<^sub>2' \<Longrightarrow> c\<^sub>1 || c\<^sub>2 \<leadsto> c\<^sub>1 || c\<^sub>2'" |
  parE1[intro]: "Nil || c \<leadsto> c" |
  parE2[intro]: "c || Nil \<leadsto> c" |
  thr[intro]:   "c \<leadsto> c' \<Longrightarrow> Thread c \<leadsto> Thread c'" |
  thrE[intro]:  "Thread Nil \<leadsto> Nil"  |
  capE[intro]: "Capture k Nil \<leadsto> Nil" |
  capS[intro]:  "c \<leadsto> c' \<Longrightarrow> Capture k c \<leadsto> Capture k c'" |
  capStep[intro]: "c \<mapsto>[\<alpha>',r,\<alpha>] c' \<Longrightarrow> Capture s c \<leadsto> Basic (popbasic' s s' \<alpha>') \<cdot> (Capture s' c')" 
inductive_cases silentE[elim]: "c\<^sub>1 \<leadsto> c\<^sub>1'"

thm silent.cases
thm silentE

text \<open>An execution step implies the program has changed\<close>
lemma execute_neq:
  assumes "c \<mapsto>[\<alpha>'',r,\<alpha>'] c'"
  shows "c \<noteq> c'"
  using assms by (induct) auto

lemma [simp]:
  "c \<mapsto>[\<alpha>'',r,\<alpha>'] c = False"
  using execute_neq by blast

lemma gexecute_neq:
  assumes "c \<mapsto>[g] c'"
  shows "c \<noteq> c'"
  using assms by (induct) auto

lemma [simp]:
  "c \<mapsto>[g] c = False"
  using gexecute_neq by blast

lemma [intro]:
  "local (seq2com s)"
  by (induct s) auto

text \<open>An execution step will not introduce parallelism\<close>
lemma local_execute:
  "c \<mapsto>[\<alpha>'',r,\<alpha>'] c' \<Longrightarrow> local c \<Longrightarrow> local c'"
  by (induct rule: lexecute.induct) auto

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

lemma [simp]:
  "basics (seq2com s) = set s"
  by (induct s) auto

lemma basics_exec:
  assumes "c \<mapsto>[\<alpha>'',r,\<alpha>] c'" shows "basics c \<supseteq> basics c'"
  using assms by induct auto

(* lemma basics_silent:
  assumes "c \<leadsto> c'" shows "basics c \<supseteq> basics c'"
  using assms basics_exec by (induct) auto    *)

(*--from winter2021 --------------------------*)
(*
lemma popBasic:
 "basics (Basic (popbasic \<beta>)) = {\<beta>}"
  sorry


lemma popbasicBasic:
  assumes "basics c \<supseteq> basics c'"
  shows "popbasic ` basics c' \<supseteq> popbasic ` basics c"
  using 

lemma basics_silentCap1:
  assumes "Capture k c \<leadsto> Capture k c'"
  shows "basics c \<supseteq> basics c'"
  using basics_exec basics.elims

lemma basics_silentCap2:
  assumes "Capture s c \<leadsto> Basic (popbasic' s s' \<alpha>') \<cdot> (Capture s' c')"
  shows "basics c \<supseteq> basics c'"
  sorry

lemma basics_silent:
  assumes "c \<leadsto> c'" shows "basics c \<supseteq> basics c'"
  using assms basics_exec basics_silentCap1 basics_silentCap2
  by (simp add: capS)
*)

lemma basics_lexec:
  assumes "lexecute c \<alpha>' r \<alpha> c'" 
  shows "basics c \<supseteq> basics c'"
  using assms by (induct) auto

lemma basics_gex: 
  assumes "gexecute c g c'" shows "basics c \<supseteq> basics c'"
  using assms basics_lexec by (induct) auto 

lemma basics_lexec_prefix:
  assumes "lexecute c \<alpha>' r \<alpha> c'" shows "basics c \<supseteq> insert \<alpha> (basics r)"
  using assms by (induct) auto
(*----------------------------*)

fun seqonly :: "('a,'b) com \<Rightarrow> bool" where
  "seqonly Nil = True" |
  "seqonly (Basic _) = True" |
  "seqonly (Seq c1 c2) = (seqonly c1 \<and> seqonly c2)" |
  "seqonly (Ord c1 c2) = (seqonly c1 \<and> seqonly c2)" |
  "seqonly _ = False"



(* lemma seqonly_popcom [simp]: "seqonly (popcom c) = seqonly c"
by induct auto *)

lemma seqonly_reorder_com [simp]: "\<alpha>' < c <\<^sub>c \<alpha> \<Longrightarrow> seqonly c"
by (induct rule: reorder_com.induct) auto

(* lemma seqonly_lexecute [simp]: "c \<mapsto>[r,\<alpha>] c' \<Longrightarrow> seqonly r"
by (induct rule: lexecute.induct) auto *)

(* lemma popbasic_pushcom:
  assumes "seqonly r"
  shows "popbasic ` basics (pushcom s r) = basics r"
using assms
proof (induct r)
  case (Basic \<alpha>)
  have "popbasic ` {pushbasic s \<alpha>} = {\<alpha>}" by simp
  thus ?case by simp
qed (auto simp add: image_Un) *)

(* lemma basics_exec_prefix:
  assumes "c \<mapsto>[r,\<alpha>] c'" shows "basics c \<supseteq> insert \<alpha> (basics r)"
  using assms
proof (induct rule: lexecute.induct)
  case (cap c s r \<alpha> c' s')
  hence "seqonly r" using seqonly_lexecute by fastforce
  hence "popbasic ` basics (pushcom s r) = basics r"
    by (rule popbasic_pushcom)
  hence "basics r \<subseteq> popbasic ` basics c"
    using cap(2) image_mono by fastforce
  moreover have "\<alpha> \<in> popbasic ` basics c"
    using cap(2) image_iff by fastforce
  ultimately show ?case by simp
qed auto *)


end

end