theory Atomics
  imports Syntax
begin

chapter \<open>Atomic Actions\<close>

text \<open>
Describe concepts the logic must know about atomic instructions. 
\<close>

section \<open>Helper Definitions\<close>

type_synonym ('b) pred = "('b) set"
type_synonym ('b) rpred = "('b) rel"

text \<open>Stability of a predicate across an environment step\<close>
definition stable :: "('b) rpred \<Rightarrow> ('b) pred \<Rightarrow> bool"
  where "stable R P \<equiv> \<forall>m m'. m \<in> P \<longrightarrow> (m,m') \<in> R \<longrightarrow> m' \<in> P"

text \<open>Weakest precondition for a precondition and postrelation\<close>
definition wp 
  where "wp pre post Q \<equiv> pre \<inter> {m. (\<forall>m'. (m,m') \<in> post \<longrightarrow> m' \<in> Q)}"

definition guar
  where "guar pre post G \<equiv> {(m,m'). m \<in> pre \<and> (m,m') \<in> post} \<subseteq> G"

subsection \<open>Helper Lemmas\<close>

lemma stable_conseqI [intro]:
  assumes "stable R' P" "R \<subseteq> R'" 
  shows "stable R P"
  using assms rtrancl_mono unfolding stable_def by blast

lemma stable_conjI [intro]:
  assumes "stable R P" "stable R' P'"
  shows "stable (R \<inter> R') (P \<inter> P')"
  using assms by (auto simp: stable_def)

lemma stable_transitive:
  assumes "(m,m') \<in> R\<^sup>*" "m \<in> P" "stable R P"
  shows "m' \<in> P"
  using assms by (induct rule: rtrancl.induct) (auto simp: stable_def)

lemma stable_wp\<^sub>tI:
  "stable R P \<Longrightarrow> P \<subseteq> wp UNIV (R\<^sup>*) P"
  unfolding wp_def using stable_transitive by fast

lemma [intro]:
  "stable R {}"
  by (auto simp: stable_def)

section \<open>Atomic Properties\<close>

text \<open>Weakest precondition of a basic instruction, based on the locale's 
      verification conditions and behaviours.\<close>
abbreviation wp\<^sub>\<alpha> :: "('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where "wp\<^sub>\<alpha> \<alpha> Q \<equiv> wp (vc \<alpha>) (beh \<alpha>) Q"

text \<open>Weakest precondition of a program, only covering basic instructions, environment steps and 
      sequential composition as these are sufficient for the logic's checks.\<close>
fun wp\<^sub>c :: "('a,'b) com \<Rightarrow> 'b pred \<Rightarrow> 'b pred"
  where 
    "wp\<^sub>c (Basic \<alpha>) Q = wp\<^sub>\<alpha> \<alpha> Q" |
    "wp\<^sub>c (Seq c\<^sub>1 c\<^sub>2) Q = wp\<^sub>c c\<^sub>1 (wp\<^sub>c c\<^sub>2 Q)" |
    "wp\<^sub>c _ Q = undefined"

text \<open>Refinement relation between two programs, in terms of their weakest precondition calculation.\<close>
definition refine :: "('a,'b) com \<Rightarrow> ('a,'b) com \<Rightarrow> bool" (infix "\<sqsubseteq>" 60)
  where "c \<sqsubseteq> c' \<equiv> \<forall>Q. wp\<^sub>c c Q \<subseteq> wp\<^sub>c c' Q"

text \<open>Merge the verification condition and behaviour to define evaluation\<close>
definition eval :: "('a,'b) basic \<Rightarrow> 'b rel"
  where "eval \<alpha> \<equiv> {(m,m'). m \<in> vc \<alpha> \<longrightarrow> (m,m') \<in> beh \<alpha>}"

text \<open>Specification check, ensuring an instruction conforms to a relation\<close>
abbreviation guar\<^sub>\<alpha> :: "('a,'b) basic \<Rightarrow> 'b rpred \<Rightarrow> bool"
  where "guar\<^sub>\<alpha> \<alpha> G \<equiv> guar (vc \<alpha>) (beh \<alpha>) G"

section \<open>Atomic Rule\<close>

text \<open>Rule for an atomic operation\<close>
definition atomic_rule :: "'b rpred \<Rightarrow> 'b rpred \<Rightarrow> 'b pred \<Rightarrow> ('a,'b) basic \<Rightarrow> 'b pred \<Rightarrow> bool" 
  ("_,_ \<turnstile>\<^sub>A _ {_} _" [40,0,0,0,40] 40)
  where "R,G \<turnstile>\<^sub>A P {\<alpha>} Q \<equiv> P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q \<and> guar\<^sub>\<alpha> \<alpha> G \<and> stable R P \<and> stable R Q"

subsection \<open>Derived Properties\<close>

text \<open>Re-establish an atomic judgement over a stronger stable precondition\<close>
lemma atomic_pre:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "P' \<subseteq> P" "stable R P'"
  shows "R,G \<turnstile>\<^sub>A P' {\<alpha>} Q"
  using assms unfolding atomic_rule_def by fast

text \<open>Strengthen the rely and weaken the guarantee for an atomic judgement\<close>
lemma atomic_conseqI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "R' \<subseteq> R" "G \<subseteq> G'"
  shows "R',G' \<turnstile>\<^sub>A P {\<alpha>} Q"
  using assms unfolding atomic_rule_def guar_def by blast

text \<open>Atomic judgements over the same instruction can be combined\<close>
lemma actomic_conjI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P\<^sub>1 {\<alpha>} Q\<^sub>1" "R,G  \<turnstile>\<^sub>A P\<^sub>2 {\<alpha>} Q\<^sub>2"
  shows "R,G \<turnstile>\<^sub>A P\<^sub>1 \<inter> P\<^sub>2 {\<alpha>} Q\<^sub>1 \<inter> Q\<^sub>2"
  using assms unfolding atomic_rule_def wp_def stable_def by fast

text \<open>Add an invariant across an atomic judgement\<close>
lemma atomic_invI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q"
  assumes "stable R\<^sub>2 I" "G \<subseteq> R\<^sub>2"
  shows "R \<inter> R\<^sub>2,G \<turnstile>\<^sub>A P \<inter> I {\<alpha>} Q \<inter> I"
  unfolding atomic_rule_def
proof (safe, goal_cases)
  case (1 m)
  hence "{(m,m'). m \<in> P \<inter> vc \<alpha> \<and> (m,m') \<in> beh \<alpha>} \<subseteq> R\<^sub>2\<^sup>=" "m \<in> vc \<alpha>"
    using assms(1,3) by (auto simp: wp_def guar_def atomic_rule_def)
  hence "m \<in> wp\<^sub>\<alpha> \<alpha> I" using assms(2) 1 by (auto simp: wp_def stable_def)
  moreover have "m \<in> wp\<^sub>\<alpha> \<alpha> Q" using 1 assms(1) by (auto simp: atomic_rule_def wp_def)
  ultimately show ?case by (auto simp: wp_def)
qed (insert assms, auto simp: atomic_rule_def wp_def)

lemma atomic_falseI [intro]:
  assumes "guar\<^sub>\<alpha> \<beta> G"
  shows "R,G \<turnstile>\<^sub>A {} {\<beta>} {}"
  using assms unfolding atomic_rule_def by auto

section \<open>State Expansion\<close>

definition expand\<^sub>P
  where "expand\<^sub>P m P \<equiv> \<Union> (m ` P)"

definition expand\<^sub>G
  where "expand\<^sub>G m r G \<equiv> {(c,c'). \<exists>(b,b')\<in> G. c \<in> m b \<and> c' \<in> m b' \<and> r c c'}"

definition expand\<^sub>R
  where "expand\<^sub>R m R \<equiv> {(c,c'). \<exists>(b,b')\<in> R. c \<in> m b \<and> c' \<in> m b'}"

definition valid_expand
  where "valid_expand m r \<equiv> 
          (\<forall>b b' c. c \<in> m b' \<longrightarrow> c \<in> m b \<longrightarrow> b = b') \<and> 
          (\<forall>a b c. r a b \<longrightarrow> a \<in> m c \<longrightarrow> b \<in> m c \<longrightarrow> a = b)"

lemma expand_stable:
  assumes "stable R P" "valid_expand m r"
  shows "stable (expand\<^sub>R m R) (expand\<^sub>P m P)"
  using assms unfolding stable_def valid_expand_def expand\<^sub>P_def expand\<^sub>R_def
  by fastforce

lemma expand_wp\<^sub>\<alpha>:
  assumes "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" "valid_expand m r"
  assumes \<alpha>: "vc \<alpha>' = expand\<^sub>P m (vc \<alpha>)" "beh \<alpha>' = expand\<^sub>G m r (beh \<alpha>)"
  shows "expand\<^sub>P m P \<subseteq> wp\<^sub>\<alpha> \<alpha>' (expand\<^sub>P m Q)"
  using assms(1,2) unfolding wp_def valid_expand_def expand\<^sub>P_def expand\<^sub>G_def \<alpha>
  by fastforce

lemma expand_guar:
  assumes "guar\<^sub>\<alpha> \<alpha> G" "valid_expand m r"
  assumes \<alpha>: "vc \<alpha>' = expand\<^sub>P m (vc \<alpha>)" "beh \<alpha>' = expand\<^sub>G m r (beh \<alpha>)"
  shows "guar\<^sub>\<alpha> \<alpha>' (expand\<^sub>G m r G)"
  using assms(1,2,3) unfolding valid_expand_def expand\<^sub>G_def \<alpha> expand\<^sub>P_def guar_def
  by blast

text \<open>Expand the state of an atomic judgement\<close>
lemma atomic_expandI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha> :: ('b,'a) basic} Q"
  assumes "valid_expand m r"
  assumes \<alpha>: "vc \<alpha>' = expand\<^sub>P m (vc \<alpha>)" "beh \<alpha>' = expand\<^sub>G m r (beh \<alpha>)" 
  shows "expand\<^sub>R m R,expand\<^sub>G m r G \<turnstile>\<^sub>A expand\<^sub>P m P {\<alpha>' :: ('b,'c) basic} expand\<^sub>P m Q"
  unfolding atomic_rule_def
proof (safe)
  show "stable (expand\<^sub>R m R) (expand\<^sub>P m P)" 
    using assms(1,2) expand_stable unfolding atomic_rule_def by blast
next
  show "stable (expand\<^sub>R m R) (expand\<^sub>P m Q)" 
    using assms(1,2) expand_stable unfolding atomic_rule_def by blast
next
  fix x assume "x \<in> expand\<^sub>P m P"
  thus "x \<in> wp\<^sub>\<alpha> \<alpha>' (expand\<^sub>P m Q)"
    using assms(1,2) \<alpha> expand_wp\<^sub>\<alpha> unfolding atomic_rule_def by blast
next
  show "guar\<^sub>\<alpha> \<alpha>' (expand\<^sub>G m r G)"
    using assms(1,2) \<alpha> expand_guar unfolding atomic_rule_def by blast
qed

section \<open>Auxiliary State\<close>

definition aux\<^sub>P
  where "aux\<^sub>P r P \<equiv> {m. \<exists>m'. (m,m') \<in> r\<^sup>= \<and> m' \<in> P}"

definition aux\<^sub>R
  where "aux\<^sub>R r R \<equiv> {(m,m'). \<forall>n. (m,n) \<in> r\<^sup>= \<longrightarrow> (\<exists>n'. (m',n') \<in> r\<^sup>= \<and> (n,n') \<in> R)}"

definition aux\<^sub>G
  where "aux\<^sub>G r R \<equiv> {(m,m'). \<exists>n n'. (m,n) \<in> r\<^sup>= \<and> (m',n') \<in> r\<^sup>= \<and> (n,n') \<in> R}"

lemma aux\<^sub>P_mono [intro]:
  "P \<subseteq> Q \<Longrightarrow> aux\<^sub>P a P \<subseteq> aux\<^sub>P a Q"
  unfolding aux\<^sub>P_def by auto

lemma aux\<^sub>R_mono [intro]:
  "P \<subseteq> Q \<Longrightarrow> aux\<^sub>R a P \<subseteq> aux\<^sub>R a Q"
  unfolding aux\<^sub>R_def by fast

lemma aux\<^sub>P_self [intro]:
  "P \<subseteq> aux\<^sub>P r P"
  unfolding aux\<^sub>P_def by auto

lemma aux\<^sub>G_self [intro]:
  "R \<subseteq> aux\<^sub>G r R"
  unfolding aux\<^sub>G_def by auto

lemma aux_stable [intro]:
  assumes "stable R P" 
  shows "stable (aux\<^sub>R r R) (aux\<^sub>P r P)"
  unfolding stable_def aux\<^sub>R_def aux\<^sub>P_def
proof (clarsimp, goal_cases)
  case (1 m n p)
  then obtain n' where a: "(p, n') \<in> r\<^sup>=" "(n, n') \<in> R" by auto
  hence "n' \<in> P" using 1 assms by (auto simp: stable_def)
  then show ?case using a(1) by auto
qed

abbreviation aux\<^sub>\<alpha>
  where "aux\<^sub>\<alpha> r \<alpha> \<equiv> (tag \<alpha>, aux\<^sub>P r (vc \<alpha>), aux\<^sub>R r (beh \<alpha>))"

lemma aux_wp [intro]:
  assumes "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q"
  shows "aux\<^sub>P r P \<subseteq> wp\<^sub>\<alpha> (aux\<^sub>\<alpha> r \<alpha>) (aux\<^sub>P r Q)"
  unfolding wp_def aux\<^sub>P_def
proof (clarsimp, (intro conjI; clarsimp), goal_cases)
  case (1 n m')
  then show ?case using assms by (auto simp: wp_def aux\<^sub>P_def)
next
  case (2 n m n')
  then show ?case using assms(1) unfolding aux\<^sub>R_def wp_def by blast
qed

lemma aux_guar [intro]:
  assumes "guar\<^sub>\<alpha> \<alpha> G" 
  shows "guar\<^sub>\<alpha> (aux\<^sub>\<alpha> r \<alpha>) (aux\<^sub>G r G)"
  unfolding wp_def aux\<^sub>G_def aux\<^sub>P_def aux\<^sub>R_def guar_def
proof (clarsimp, goal_cases)
  case (1 m m' n)
  then obtain n' where a: "(m', n') \<in> r\<^sup>=" "(n, n') \<in> beh \<alpha>" by auto
  hence "(n,n') \<in> G" using assms 1 by (auto simp: guar_def)
  thus ?case using a(1) 1(3) sorry
qed

lemma atomic_auxI [intro]:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" 
  shows "aux\<^sub>R r R,aux\<^sub>G r G \<turnstile>\<^sub>A aux\<^sub>P r P {aux\<^sub>\<alpha> r \<alpha>} aux\<^sub>P r Q"
  unfolding atomic_rule_def
proof (intro conjI)
  show "stable (aux\<^sub>R r R) (aux\<^sub>P r P)" using assms(1) by (auto simp: atomic_rule_def)
next
  show "stable (aux\<^sub>R r R) (aux\<^sub>P r Q)" using assms(1) by (auto simp: atomic_rule_def)
next
  have "guar\<^sub>\<alpha> \<alpha> G" using assms(1) by (auto simp: atomic_rule_def)
  thus "guar\<^sub>\<alpha> (aux\<^sub>\<alpha> r \<alpha>) (aux\<^sub>G r G)" using aux_guar by blast
next
  have "P \<subseteq> wp\<^sub>\<alpha> \<alpha> Q" using assms(1) by (auto simp: atomic_rule_def)
  thus "aux\<^sub>P r P \<subseteq> wp\<^sub>\<alpha> (aux\<^sub>\<alpha> r \<alpha>) (aux\<^sub>P r Q)" using aux_wp by blast
qed


(*
fun aux\<^sub>c
  where
    "aux\<^sub>c r Nil = Nil" |
    "aux\<^sub>c r (Basic \<alpha>) = (Basic (aux\<^sub>\<alpha> r \<alpha>))" |
    "aux\<^sub>c r (c\<^sub>1 ; c\<^sub>2) = (aux\<^sub>c r c\<^sub>1 ; aux\<^sub>c r c\<^sub>2)" |
    "aux\<^sub>c r (c\<^sub>1 \<cdot> c\<^sub>2) = (aux\<^sub>c r c\<^sub>1 \<cdot> aux\<^sub>c r c\<^sub>2)" |
    "aux\<^sub>c r (c\<^sub>1 \<sqinter> c\<^sub>2)  = (aux\<^sub>c r c\<^sub>1 \<sqinter> aux\<^sub>c r c\<^sub>2)" |
    "aux\<^sub>c r (Loop c) = Loop (aux\<^sub>c r c)" |
    "aux\<^sub>c r (BigChoice S\<^sub>1) = (BigChoice ((map (aux\<^sub>\<alpha> r)) ` S\<^sub>1))" |
    "aux\<^sub>c r (Dec b m c) = (Dec b m (aux\<^sub>c r c))" |
    "aux\<^sub>c r (c\<^sub>1 || c\<^sub>2) = (aux\<^sub>c r c\<^sub>1 || aux\<^sub>c r c\<^sub>2)"

lemma aux\<^sub>c_nilE [elim!]:
  assumes "aux\<^sub>c r c = Nil"
  obtains "c = Nil"
  using assms
  by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_basicE [elim!]:
  assumes "aux\<^sub>c r c = Basic \<alpha>"
  obtains \<beta> where "c = Basic \<beta>" "\<alpha> = aux\<^sub>\<alpha> r \<beta>"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_seqE [elim!]:
  assumes "aux\<^sub>c r c = c\<^sub>1 ; c\<^sub>2"
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' ; c\<^sub>2'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" "aux\<^sub>c r c\<^sub>2' = c\<^sub>2"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_ordE [elim!]:
  assumes "aux\<^sub>c r c = c\<^sub>1 \<cdot> c\<^sub>2"
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' \<cdot> c\<^sub>2'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" "aux\<^sub>c r c\<^sub>2' = c\<^sub>2"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_choiceE [elim!]:
  assumes "aux\<^sub>c r c = c\<^sub>1 \<sqinter> c\<^sub>2"
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' \<sqinter> c\<^sub>2'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" "aux\<^sub>c r c\<^sub>2' = c\<^sub>2"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_loopE [elim!]:
  assumes "aux\<^sub>c r c = Loop c\<^sub>1"
  obtains c\<^sub>1' where "c = Loop c\<^sub>1'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" 
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux_local [intro]:
  assumes "local c" 
  shows "local (aux\<^sub>c r c)"
  using assms by (induct c rule: local.induct) auto
*)

(*
lemma aux\<^sub>c_seqE2 [elim!]:
  assumes "c\<^sub>1 ; c\<^sub>2 = aux\<^sub>c r c "
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' ; c\<^sub>2'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" "aux\<^sub>c r c\<^sub>2' = c\<^sub>2"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_ordE [elim!]:
  assumes "c\<^sub>1 \<cdot> c\<^sub>2 = aux\<^sub>c r c"
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' \<cdot> c\<^sub>2'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" "aux\<^sub>c r c\<^sub>2' = c\<^sub>2"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_parE [elim!]:
  assumes "c\<^sub>1 || c\<^sub>2 = aux\<^sub>c r c"
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' || c\<^sub>2'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" "aux\<^sub>c r c\<^sub>2' = c\<^sub>2"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_choiceE [elim!]:
  assumes "c\<^sub>1 \<sqinter> c\<^sub>2 = aux\<^sub>c r c"
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' \<sqinter> c\<^sub>2'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" "aux\<^sub>c r c\<^sub>2' = c\<^sub>2"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_loopE [elim!]:
  assumes "Loop c\<^sub>1 = aux\<^sub>c r c"
  obtains c\<^sub>1' where "c = Loop c\<^sub>1'" "aux\<^sub>c r c\<^sub>1' = c\<^sub>1" 
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma aux\<^sub>c_bigchoiceE [elim!]:
  assumes "(\<Sqinter> S) = aux\<^sub>c r c"
  obtains S' where "c = \<Sqinter> S'" "S = (map (aux\<^sub>\<alpha> r)) ` S'" 
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma [simp]:
  "seq2com (map (aux\<^sub>\<alpha> r) x) = aux\<^sub>c r (seq2com x)"
proof (induct x)
case Nil
  then show ?case by auto
next
  case (Cons a x)
  then show ?case  by auto
qed

lemma aux_rewriteE:
  assumes "aux\<^sub>c r c \<leadsto> c\<^sub>a"
  obtains c' where "c \<leadsto> c'" "aux\<^sub>c r c' = c\<^sub>a"
  using assms
  by (induct "aux\<^sub>c r c" c\<^sub>a arbitrary: r c) (auto; force)+

lemma aux\<^sub>c_basicE [elim!]:
  assumes "Basic \<alpha> = aux\<^sub>c r c"
  obtains \<beta> where "c = Basic \<beta>" "\<alpha> = aux\<^sub>\<alpha> r \<beta>"
  using assms by (cases "(r,c)" rule: aux\<^sub>c.cases) auto

lemma [simp]:
  "(aux\<^sub>\<alpha> r \<beta>)\<langle>tag x\<rangle> = aux\<^sub>\<alpha> r \<beta>\<langle>tag x\<rangle>"
  
  sorry

lemma [simp]:
  "(aux\<^sub>\<alpha> r \<beta>)\<llangle>aux\<^sub>c r p\<rrangle> = aux\<^sub>\<alpha> r \<beta>\<llangle>p\<rrangle>"
  by (induct p arbitrary: \<beta>) auto

lemma aux_re:
  assumes "\<alpha>' < aux\<^sub>c r c <\<^sub>c aux\<^sub>\<alpha> r \<alpha>"
  obtains \<beta> where "\<beta> < c <\<^sub>c \<alpha>" "\<alpha>' = aux\<^sub>\<alpha> r \<beta>"
  using assms
proof (induct c arbitrary: \<alpha>' \<alpha>)
  case Nil
  then show ?case by auto
next
  case (Basic x)
  hence "tag x \<hookleftarrow> tag (\<alpha>)\<langle>tag x\<rangle>" by auto
  moreover have "\<alpha>' = aux\<^sub>\<alpha> r \<alpha>\<langle>tag x\<rangle>" using Basic(2) by auto
  ultimately show ?case using Basic(1) by auto
next
  case (Seq c1 c2)
  then obtain \<beta> where b: "\<alpha>' < aux\<^sub>c r c1 <\<^sub>c \<beta>" "\<beta> < aux\<^sub>c r c2 <\<^sub>c aux\<^sub>\<alpha> r \<alpha>" by auto
  show ?case 
  proof (rule Seq(2)[OF _ b(2)])
    fix \<beta>' assume c: "\<beta>' < c2 <\<^sub>c \<alpha>" "\<beta> = aux\<^sub>\<alpha> r \<beta>'"
    hence a: "\<alpha>' < aux\<^sub>c r c1 <\<^sub>c aux\<^sub>\<alpha> r \<beta>'" using b by auto
    show ?thesis apply (rule Seq(1)[OF _a]) using c(1) Seq(3) reorder_com.simps(3) by blast 
  qed
next
  case (Ord c1 c2)
  then obtain \<beta> where b: "\<alpha>' < aux\<^sub>c r c1 <\<^sub>c \<beta>" "\<beta> < aux\<^sub>c r c2 <\<^sub>c aux\<^sub>\<alpha> r \<alpha>" by auto
  show ?case 
  proof (rule Ord(2)[OF _ b(2)])
    fix \<beta>' assume c: "\<beta>' < c2 <\<^sub>c \<alpha>" "\<beta> = aux\<^sub>\<alpha> r \<beta>'"
    hence a: "\<alpha>' < aux\<^sub>c r c1 <\<^sub>c aux\<^sub>\<alpha> r \<beta>'" using b by auto
    show ?thesis apply (rule Ord(1)[OF _a]) using c(1) Ord(3) reorder_com.simps(4) by blast 
  qed
qed auto

lemma aux_execE:
  assumes "aux\<^sub>c r c \<mapsto>[p,\<alpha>] c\<^sub>a"
  obtains c' p' \<beta> where "c \<mapsto>[p',\<beta>] c'" "aux\<^sub>c r c' = c\<^sub>a" "\<alpha> = aux\<^sub>\<alpha> r \<beta>" "aux\<^sub>c r p' = p"
  using assms
proof (induct "aux\<^sub>c r c" p \<alpha> c\<^sub>a arbitrary: r c)
  case (act \<alpha>)
  then show ?case apply auto by force
next
  case (seq c\<^sub>1 r' \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case apply auto by force
next
  case (ord c\<^sub>1 r \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case apply auto by force
next
  case (ooo c\<^sub>2 r' \<alpha> c\<^sub>2' \<alpha>' c\<^sub>1)
  then obtain c\<^sub>1' c' where s: "c = c\<^sub>1' ; c'" "c\<^sub>1 = aux\<^sub>c r c\<^sub>1'" "aux\<^sub>c r c' = c\<^sub>2" by auto

  
  show ?case 
  proof (rule ooo(2)[of r c'], goal_cases)
    case 1
    then show ?case using s by auto
  next
    case (2 p' \<beta> c'')
    hence re: "\<alpha>' < aux\<^sub>c r (c\<^sub>1' ; p') <\<^sub>c aux\<^sub>\<alpha> r \<beta>" using ooo(3) s by auto
    then obtain \<beta>' where b: "\<beta>' < c\<^sub>1' ; p' <\<^sub>c \<beta>" using aux_re by blast

    show ?case 
      apply (rule ooo(5)[of "c\<^sub>1' ; p'" \<beta> "c\<^sub>1' ; c''"])
      using s 2 b apply auto
      apply (rule execute.ooo[of _ _ _ _ \<beta>'], simp)
      by auto
  qed 
next
  case (par1 c\<^sub>1 r' \<alpha> c\<^sub>1' c\<^sub>2)
  then show ?case apply auto by force
next
  case (par2 c\<^sub>2 r' \<alpha> c\<^sub>2' c\<^sub>1)
  then show ?case apply auto by force
qed *)

end