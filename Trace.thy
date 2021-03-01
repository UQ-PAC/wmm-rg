theory Trace
  imports Semantics
begin        

section \<open>Trace\<close>

text \<open>
Given the small-step semantics for a language,
define the possible traces that a program may generate.
\<close>

inductive rep\<^sub>i
  where 
    n[intro]: "rep\<^sub>i s []" | 
    s[intro]: "rep\<^sub>i s t\<^sub>1 \<Longrightarrow> t\<^sub>2 \<in> s \<Longrightarrow> rep\<^sub>i s (t\<^sub>2 @ t\<^sub>1)"

inductive inter\<^sub>i
  where 
    e[intro]: "inter\<^sub>i [] [] []" | 
    l[intro]: "inter\<^sub>i l\<^sub>1 l\<^sub>2 t \<Longrightarrow> inter\<^sub>i (x#l\<^sub>1) l\<^sub>2 (x#t)" |
    r[intro]: "inter\<^sub>i l\<^sub>1 l\<^sub>2 t \<Longrightarrow> inter\<^sub>i l\<^sub>1 (x#l\<^sub>2) (x#t)"

type_synonym 'b Trace = "'b list"

inductive_set trace :: "('a Stmt \<times> 'a Trace \<times> 'a Stmt) set"
  and trace_abv :: "'a Stmt \<Rightarrow> 'a Trace \<Rightarrow> 'a Stmt \<Rightarrow> bool" ("_ \<mapsto>_\<^sup>* _" [50,40,40] 70)
  where
  "trace_abv P t P' \<equiv> (P, t, P') \<in> trace"
  | lift[intro]:    "c \<mapsto>[]\<^sup>* c"
  | rewrite[intro]: "c\<^sub>1 \<leadsto> c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>t\<^sup>* c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>t\<^sup>* c\<^sub>3"
  | prepend[intro]: "c\<^sub>1 \<mapsto>\<^sub>\<alpha> c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>t\<^sup>* c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<alpha>#t\<^sup>* c\<^sub>3"

section \<open>Properties\<close>

lemma inter\<^sub>i_I1 [intro]:
  shows "inter\<^sub>i [] l l"
  by (induct l) auto

lemma inter\<^sub>i_I2 [intro]:
  shows "inter\<^sub>i l [] l"
  by (induct l) auto

lemma interE [elim]:
  assumes "inter\<^sub>i t\<^sub>1 t\<^sub>2 []"
  obtains "t\<^sub>1 = []" "t\<^sub>2 = []"
  using assms 
  by (induct t\<^sub>1 t\<^sub>2 "[] :: 'a list" rule: inter\<^sub>i.induct) auto

lemma inter\<^sub>i_E2 [elim]:
  assumes "inter\<^sub>i [] t t'"
  obtains "t = t'"
  using assms
  by (induct "[] :: 'a list" t t' rule: inter\<^sub>i.induct) auto

subsection \<open>Trace Properties\<close>

lemma trace_concat [intro]:
  assumes "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* P\<^sub>2"
  assumes "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* P\<^sub>3"
  shows "P\<^sub>1 \<mapsto>t\<^sub>1@t\<^sub>2\<^sup>* P\<^sub>3"
  using assms by induct auto

lemma trace_pre [intro]:
  assumes "P\<^sub>1 \<mapsto>[x]\<^sup>* P\<^sub>2"
  assumes "P\<^sub>2 \<mapsto>t\<^sup>* P\<^sub>3"
  shows "P\<^sub>1 \<mapsto>x#t\<^sup>* P\<^sub>3"
  using trace_concat[OF assms] by auto

lemma trace_concatE [elim]:
  assumes "P\<^sub>1 \<mapsto>t\<^sub>1@t\<^sub>2\<^sup>* P\<^sub>3"
  obtains P\<^sub>2 where "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* P\<^sub>2" "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* P\<^sub>3"
  using assms
proof (induct P\<^sub>1 "t\<^sub>1 @t\<^sub>2" P\<^sub>3 arbitrary: t\<^sub>1 t\<^sub>2)
  case (prepend c\<^sub>1 \<alpha> c\<^sub>2 t c\<^sub>3)
  then show ?case by (cases t\<^sub>1) auto
qed blast+

lemma trace_preE [elim]:
  assumes "P\<^sub>1 \<mapsto>x#t\<^sub>2\<^sup>* P\<^sub>3"
  obtains P\<^sub>2 where "P\<^sub>1 \<mapsto>[x]\<^sup>* P\<^sub>2" "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* P\<^sub>3"
  using assms by (metis append_Cons append_Nil trace_concatE)

lemma trace_par [intro]:
  assumes "c\<^sub>1 \<mapsto>t\<^sup>* c\<^sub>1'"
  shows "c\<^sub>1 || c\<^sub>2 \<mapsto>t\<^sup>* c\<^sub>1' || c\<^sub>2" "c\<^sub>2 || c\<^sub>1 \<mapsto>t\<^sup>* c\<^sub>2 || c\<^sub>1'"
  using assms by induct auto

lemma trace_seq [intro]:
  assumes "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* P\<^sub>2"
  shows "P\<^sub>1 ;; P\<^sub>3 \<mapsto>t\<^sub>1\<^sup>* P\<^sub>2 ;; P\<^sub>3"
  using assms by induct blast+

subsection \<open>Trace Elimination\<close>

subsubsection \<open>Skip Properties\<close>

lemma trace_skipE [elim]:
  assumes "Skip \<mapsto>t\<^sup>* P"
  obtains "P = Skip" "t = []"
  using assms by (induct "Skip :: 'a Stmt" t P rule: trace.induct) blast+

subsubsection \<open>Act Properties\<close>

lemma trace_actE [elim]:
  assumes "Basic \<alpha> \<mapsto>t\<^sup>* P"
  obtains "t = [\<alpha>]" "P = Skip" | "t = []" "P = Basic \<alpha>"
  using assms by (induct "Basic \<alpha>" t P) blast+

subsubsection \<open>Seq Properties\<close>

lemma trace_seqE [elim]:
  assumes "P\<^sub>1 ;; P\<^sub>2 \<mapsto>t\<^sup>* P\<^sub>3"
  obtains t\<^sub>1 t\<^sub>2 P\<^sub>1' P\<^sub>2' where "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* P\<^sub>1'" "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* P\<^sub>2'" "t = t\<^sub>1@t\<^sub>2" "P\<^sub>1' ;; P\<^sub>2' \<mapsto>[]\<^sup>* P\<^sub>3"
  using assms 
proof (induct "P\<^sub>1 ;; P\<^sub>2" t P\<^sub>3 arbitrary: P\<^sub>1 P\<^sub>2)
  case lift
  then show ?case by blast
next
  case (rewrite c\<^sub>2 t c\<^sub>3)
  then show ?case 
  proof (cases )
    case (seq c\<^sub>1')
    then show ?thesis using rewrite by blast
  next
    case seqE
    then show ?thesis using rewrite by force
  qed
next
  case (prepend \<alpha> c\<^sub>2 t c\<^sub>3)
  then show ?case
  proof (cases)
    case (seq c\<^sub>1')
    then show ?thesis 
      using prepend(2,4) prepend(3)[OF seq(1)] 
      by (metis Cons_eq_appendI trace.prepend)
  qed
qed

lemma traces_seq_skipI [intro]:
  shows "Skip ;; Skip \<mapsto>[]\<^sup>* Skip"
  by auto

lemma traces_seq_skipE [elim]:
  assumes "c\<^sub>1 ;; c\<^sub>2 \<mapsto>[]\<^sup>* Skip"
  obtains "c\<^sub>1 \<mapsto>[]\<^sup>* Skip" "c\<^sub>2 \<mapsto>[]\<^sup>* Skip"
  using assms
  by (induct "c\<^sub>1 ;; c\<^sub>2" "[] :: 'a Trace" "Skip :: 'a Stmt" arbitrary: c\<^sub>1 c\<^sub>2 rule: trace.induct)
      blast+

lemma trace_seq_fullE [elim]:
  assumes "P\<^sub>1 ;; P\<^sub>2 \<mapsto>t\<^sup>* Skip"
  obtains t\<^sub>1 t\<^sub>2 where "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* Skip" "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* Skip" "t = t\<^sub>1@t\<^sub>2"
  using assms 
proof (cases rule: trace_seqE)
  case (1 t\<^sub>1 t\<^sub>2 P\<^sub>1' P\<^sub>2')
  then show ?thesis using traces_seq_skipE[OF 1(4)] that trace_concat by fastforce
qed

lemma traces_seq_fullI [intro]:
  assumes "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* Skip" "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* Skip"
  shows "P\<^sub>1 ;; P\<^sub>2 \<mapsto>t\<^sub>1@t\<^sub>2\<^sup>* Skip"
  using assms by blast

subsubsection \<open>Choice Properties\<close>

lemma trace_choiceE [elim]:
  assumes "P\<^sub>1 \<sqinter> P\<^sub>2 \<mapsto>t\<^sup>* P\<^sub>3"
  obtains "P\<^sub>1 \<mapsto>t\<^sup>* P\<^sub>3" | "P\<^sub>2 \<mapsto>t\<^sup>* P\<^sub>3" | "P\<^sub>3 = P\<^sub>1 \<sqinter> P\<^sub>2" "t = []"
  using assms by (induct "P\<^sub>1 \<sqinter> P\<^sub>2" t P\<^sub>3) blast+

subsubsection \<open>Loop Properties\<close>

lemma trace_loopE [elim]:
  assumes "P\<^sub>1* \<mapsto>t\<^sup>* P\<^sub>3"
  obtains n where "unroll n P\<^sub>1 \<mapsto>t\<^sup>* P\<^sub>3" | "P\<^sub>3 = (P\<^sub>1*)" "t = []"
  using assms by (induct "P\<^sub>1*" t P\<^sub>3) blast+

lemma trace_loop_zeroI [intro]:
  "c* \<mapsto>[]\<^sup>* Skip"
proof 
  show "c* \<leadsto> unroll 0 c" by blast
next
  show "unroll 0 c \<mapsto>[]\<^sup>* Skip" by auto
qed

lemma trace_loop_sucI [intro]:
  "c* \<mapsto>t\<^sub>1\<^sup>* Skip \<Longrightarrow> c \<mapsto>t\<^sub>2\<^sup>* Skip \<Longrightarrow> c* \<mapsto>t\<^sub>2@t\<^sub>1\<^sup>* Skip"
proof -
  assume a: "c* \<mapsto>t\<^sub>1\<^sup>* Skip" "c \<mapsto>t\<^sub>2\<^sup>* Skip"
  then obtain n where "unroll n c \<mapsto>t\<^sub>1\<^sup>* Skip" by blast
  then have "unroll (Suc n) c \<mapsto>t\<^sub>2@t\<^sub>1\<^sup>* Skip" using a(2) by auto
  thus ?thesis by blast
qed

lemma trace_loop_fullE [elim]:
  assumes "P\<^sub>1* \<mapsto>t\<^sup>* Skip"
  obtains n where "unroll n P\<^sub>1 \<mapsto>t\<^sup>* Skip"
  using assms by auto

subsubsection \<open>Parallel Properties\<close>

lemma trace_parE [elim]:
  assumes "P\<^sub>1 || P\<^sub>2 \<mapsto>t\<^sup>* P\<^sub>3"
  obtains t\<^sub>1 t\<^sub>2 P\<^sub>1' P\<^sub>2' where "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* P\<^sub>1'" "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* P\<^sub>2'" "inter\<^sub>i t\<^sub>1 t\<^sub>2 t" "P\<^sub>1' || P\<^sub>2' \<mapsto>[]\<^sup>* P\<^sub>3"
  using assms 
proof (induct "P\<^sub>1 || P\<^sub>2" t P\<^sub>3 arbitrary: P\<^sub>1 P\<^sub>2)
  case (rewrite c\<^sub>2 t c\<^sub>3)
  then show ?case
  proof (cases rule: rw_parE)
    case par1E
    then show ?thesis using rewrite(1,2) rewrite(4)[of "[]"] by blast
  next
    case par2E
    then show ?thesis using rewrite(1,2) rewrite(4)[of t] by blast
  qed blast+
qed blast+

lemma trace_parI [intro]:
  assumes "inter\<^sub>i t\<^sub>1 t\<^sub>2 t" "c\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* c\<^sub>1'" "c\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* c\<^sub>2'" 
  shows "c\<^sub>1 || c\<^sub>2 \<mapsto>t\<^sup>* c\<^sub>1' || c\<^sub>2'"
  using assms
proof (induct arbitrary: c\<^sub>1 c\<^sub>2)
  case e
  then show ?case by (metis (no_types, lifting) Nil_is_append_conv trace_par trace_concat)
next
  case (l l\<^sub>1 l\<^sub>2 t x)
  then obtain c where "c\<^sub>1 \<mapsto>[x]\<^sup>* c" "c \<mapsto>l\<^sub>1\<^sup>* c\<^sub>1'" by blast
  thus ?case using l by auto
next
  case (r l\<^sub>1 l\<^sub>2 t x)
  then obtain c where "c\<^sub>2 \<mapsto>[x]\<^sup>* c" "c \<mapsto>l\<^sub>2\<^sup>* c\<^sub>2'" by blast
  thus ?case using r by auto
qed

lemma traces_par_skipI [intro]:
  shows "Skip || Skip \<mapsto>[]\<^sup>* Skip"
  by auto

lemma traces_par_skipE [elim]:
  assumes "c\<^sub>1 || c\<^sub>2 \<mapsto>[]\<^sup>* Skip"
  obtains "c\<^sub>1 \<mapsto>[]\<^sup>* Skip" "c\<^sub>2 \<mapsto>[]\<^sup>* Skip"
  using assms
  by (induct "c\<^sub>1 || c\<^sub>2" "[] :: 'a Trace" "Skip :: 'a Stmt" arbitrary: c\<^sub>1 c\<^sub>2 rule: trace.induct)
      blast+

lemma trace_par_fullE [elim]:
  assumes "P\<^sub>1 || P\<^sub>2 \<mapsto>t\<^sup>* Skip"
  obtains t\<^sub>1 t\<^sub>2 where "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* Skip" "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* Skip" "inter\<^sub>i t\<^sub>1 t\<^sub>2 t"
  using assms
proof (cases rule: trace_parE)
  case (1 t\<^sub>1 t\<^sub>2 P\<^sub>1' P\<^sub>2')
  thus ?thesis using trace_concat that by (elim traces_par_skipE) force
qed

lemma traces_par_fullI [intro]:
  assumes "P\<^sub>1 \<mapsto>t\<^sub>1\<^sup>* Skip" "P\<^sub>2 \<mapsto>t\<^sub>2\<^sup>* Skip" "inter\<^sub>i t\<^sub>1 t\<^sub>2 t"
  shows "P\<^sub>1 || P\<^sub>2 \<mapsto>t\<^sup>* Skip"
proof -
  have "P\<^sub>1 || P\<^sub>2 \<mapsto>t\<^sup>* Skip || Skip" using assms by auto
  thus ?thesis using traces_par_skipI trace_concat append_Nil2 by force
qed

subsection \<open>Properties over sets of traces\<close>

definition traces
  where "traces c\<^sub>1 = {t. c\<^sub>1 \<mapsto>t\<^sup>* Skip}"

definition cat
  where "cat s\<^sub>1 s\<^sub>2 \<equiv> {t\<^sub>1 @ t\<^sub>2 |t\<^sub>1 t\<^sub>2. t\<^sub>1 \<in> s\<^sub>1 \<and> t\<^sub>2 \<in> s\<^sub>2}"

definition rep
  where "rep s \<equiv> Collect (rep\<^sub>i s)"

definition inter
  where "inter s\<^sub>1 s\<^sub>2 = {t. \<exists>t\<^sub>1 t\<^sub>2. t\<^sub>1 \<in> s\<^sub>1 \<and> t\<^sub>2 \<in> s\<^sub>2 \<and> inter\<^sub>i t\<^sub>1 t\<^sub>2 t}"

subsection \<open>Trace Lemmas\<close>

lemma traces_skip [simp]:
  "traces Skip = {[]}"
  by (auto simp: traces_def)

lemma traces_act [simp]:
  "traces (Basic \<alpha>) = {[\<alpha>]}"
  by (auto simp: traces_def)

lemma traces_seq [simp]:
  "traces (c\<^sub>1 ;; c\<^sub>2) = cat (traces c\<^sub>1) (traces c\<^sub>2)"
  unfolding cat_def traces_def by blast

lemma traces_choice [simp]:
  "traces (c\<^sub>1 \<sqinter> c\<^sub>2) = traces c\<^sub>1 \<union> traces c\<^sub>2"
  by (auto simp: traces_def)

lemma traces_par [simp]:
  "traces (c\<^sub>1 || c\<^sub>2) = inter (traces c\<^sub>1) (traces c\<^sub>2)"
  unfolding traces_def inter_def by blast

lemma traces_loop [simp]:
  "traces (c*) = rep (traces c)"
  unfolding traces_def rep_def
proof (auto)
  fix x assume "c* \<mapsto>x\<^sup>* Skip"
  then obtain n where "unroll n c \<mapsto>x\<^sup>* Skip" by auto
  thus "rep\<^sub>i {t. c \<mapsto>t\<^sup>* Skip} x" by (induct n arbitrary: x) auto
next
  fix x
  show "rep\<^sub>i {t. c \<mapsto>t\<^sup>* Skip} x \<Longrightarrow> c* \<mapsto>x\<^sup>* Skip"
    by (induct "{t. c \<mapsto>t\<^sup>* Skip}" x rule: rep\<^sub>i.induct) auto
qed

end