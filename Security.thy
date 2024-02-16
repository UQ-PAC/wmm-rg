theory Security
  imports Soundness
begin

locale security  = rules  

type_synonym ('a,'b) Trace = "('a,'b) basic list" 

context security
begin

(* parameter S equals low equivalence: to be instantiated once I have L, \<Gamma> *)

inductive_set trace :: "(('a,'b,'c) com \<times> ('a,'b) Trace \<times> ('a,'b,'c) com) set"
  and trace_abv :: "('a,'b,'c) com \<Rightarrow> ('a,'b) Trace \<Rightarrow> ('a,'b,'c) com \<Rightarrow> bool" ("_ \<mapsto>\<^sup>*_ _" [50,40,40] 70)
  where
  "trace_abv P t P' \<equiv> (P, t, P') \<in> trace"
  | none[intro]: "c \<mapsto>\<^sup>*[] c" 
  | sil[intro]: "c\<^sub>1 \<leadsto> c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sup>*t c\<^sub>3"
  | gex[intro]: "c\<^sub>1 \<mapsto>[g] c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sup>*g#t c\<^sub>3"

lemma trace_concat [intro]:
  assumes "P\<^sub>1 \<mapsto>\<^sup>*t\<^sub>1 P\<^sub>2"
  assumes "P\<^sub>2 \<mapsto>\<^sup>*t\<^sub>2 P\<^sub>3"
  shows "P\<^sub>1 \<mapsto>\<^sup>*t\<^sub>1@t\<^sub>2 P\<^sub>3"
  using assms by induct fastforce+

lemma trace_concatE [elim]:
  assumes "P\<^sub>1 \<mapsto>\<^sup>*t\<^sub>1@t\<^sub>2 P\<^sub>3"
  obtains P\<^sub>2 where "P\<^sub>1 \<mapsto>\<^sup>*t\<^sub>1 P\<^sub>2" "P\<^sub>2 \<mapsto>\<^sup>*t\<^sub>2 P\<^sub>3"
  using assms 
proof (induct P\<^sub>1 "t\<^sub>1@t\<^sub>2" P\<^sub>3 arbitrary: t\<^sub>1 t\<^sub>2)
  case (gex c\<^sub>1 g c\<^sub>2 t c\<^sub>3)
  then show ?case by (cases t\<^sub>1) auto  
qed auto

lemma trace_preE [elim]: 
  assumes "P\<^sub>1 \<mapsto>\<^sup>*x#t P\<^sub>3"
  obtains P\<^sub>2 where "P\<^sub>1 \<mapsto>\<^sup>*[x] P\<^sub>2" "P\<^sub>2 \<mapsto>\<^sup>*t P\<^sub>3"
  using assms by (metis append.simps(1) append.simps(2) trace_concatE)

lemma trace_rule_nil: 
  assumes "c \<mapsto>\<^sup>*[] c'"
  assumes "R,G \<turnstile> P {c} Q"
  shows "R,G \<turnstile> P {c'} Q"
  using assms by (induct c "[] :: ('a,'b) Trace" c') blast+

lemma trace_rule: 
  assumes "c \<mapsto>\<^sup>*[\<alpha>] c'"
  assumes "R,G \<turnstile> P {c} Q"
  assumes "P \<noteq> {}"
  shows "\<exists> M. \<alpha> \<in> obs c  \<and> P \<subseteq> wp\<^sub>\<alpha> \<alpha> M \<and> R,G \<turnstile> M {c'} Q"
  using assms 
proof (induct c "[\<alpha>]" c' arbitrary: P) 
  case (sil c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case using obs_sil rewrite_ruleI 
    by (meson subsetD)
next
  case (gex c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then obtain  M where "P \<subseteq> wp\<^sub>\<alpha> \<alpha> M" "guar\<^sub>\<alpha> \<alpha> G"  "R,G \<turnstile> M {c\<^sub>2} Q" "\<alpha> \<in> obs c\<^sub>1"
    using gexecute_ruleI[OF gex(3,1,4)] by blast
  then show ?case 
    using trace_rule_nil[of c\<^sub>2 c\<^sub>3 R G M Q] gex(2) by blast
qed

inductive trace_mem :: "'m \<Rightarrow> ('a,'m) Trace  \<Rightarrow> 'm \<Rightarrow> bool" 
  where
    [intro]: "trace_mem m [] m" |
    [intro]: "(m'', m) \<in> beh g \<Longrightarrow> trace_mem m t m' \<Longrightarrow> trace_mem m'' (g#t) m'"

definition ev :: "('a,'b,'c) com \<Rightarrow> 'b \<Rightarrow> ('a,'b) Trace \<Rightarrow> ('a,'b,'c) com \<Rightarrow> 'b \<Rightarrow> bool"
  ("\<langle>_,_\<rangle> \<rightarrow>\<^sup>*_ \<langle>_,_\<rangle>" [50,40,40] 70)
  where "\<langle>c,m\<rangle> \<rightarrow>\<^sup>*t \<langle>c',m'\<rangle> \<equiv> trace_mem m t m' \<and> c \<mapsto>\<^sup>*t c'"

text \<open> Noninterference over all traces \<close>

definition secure :: "('a,'b,'c) com \<Rightarrow> 'b set \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) Trace rel \<Rightarrow> bool"
  where "secure c P S T \<equiv> \<forall>m\<^sub>1 m\<^sub>2 c\<^sub>1 t m\<^sub>1'. 
        m\<^sub>1 \<in> P \<longrightarrow> m\<^sub>2 \<in> P \<longrightarrow> (m\<^sub>1,m\<^sub>2) \<in> S \<longrightarrow> \<langle>c,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1,m\<^sub>1'\<rangle> \<longrightarrow> 
        (\<exists>m\<^sub>2' c\<^sub>2 t'. (t,t') \<in> T \<and> \<langle>c,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2,m\<^sub>2'\<rangle>) \<and> 
        (\<forall>m\<^sub>2' c\<^sub>2 t'. (t,t') \<in> T \<longrightarrow> \<langle>c,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2,m\<^sub>2'\<rangle> \<longrightarrow> (m\<^sub>1',m\<^sub>2') \<in> S)"  

fun trace_rel
  where 
    "trace_rel [] [] T = True" |
    "trace_rel (a#t) (b#s) T = ( (a,b) \<in> T \<and> trace_rel t s T)" |
    "trace_rel _ _ _ = False"

lemma [simp]:
  "trace_rel [] s T = (s = [])"
  by (cases s ; auto)

lemma [simp]:
  "trace_rel (a#t) s T = (\<exists>b tr. s = b#tr \<and> (a,b) \<in> T \<and> trace_rel t tr T)"
  by (cases s; auto)

text \<open>Low-equivalence structure for a basic operation\<close>
definition le_basic :: "('a,'b) basic \<Rightarrow> ('a,'b) basic  \<Rightarrow> 'b rel \<Rightarrow> bool"
  where
  "le_basic \<alpha> \<beta> R\<^sub>m \<equiv> \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1' m\<^sub>2'. 
      m\<^sub>1 \<in> vc \<alpha> \<longrightarrow> m\<^sub>2 \<in> vc \<beta> \<longrightarrow> (m\<^sub>1,m\<^sub>2) \<in> R\<^sub>m \<longrightarrow> (m\<^sub>1,m\<^sub>1') \<in> beh \<alpha> \<longrightarrow> (m\<^sub>2,m\<^sub>2') \<in> beh \<beta> \<longrightarrow> (m\<^sub>1',m\<^sub>2') \<in> R\<^sub>m"

text \<open>Low-equivalence structure for a command\<close>
definition le_com :: "('a,'b,'c) com rel \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) basic rel \<Rightarrow> bool"
  where 
  "le_com R\<^sub>c R\<^sub>m R\<^sub>\<alpha> \<equiv> \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1' c\<^sub>1 c\<^sub>2 \<alpha> c\<^sub>1'. (c\<^sub>1, c\<^sub>2) \<in> R\<^sub>c \<longrightarrow> c\<^sub>1 \<mapsto>\<^sup>*[\<alpha>] c\<^sub>1' \<longrightarrow> (m\<^sub>1, m\<^sub>2) \<in> R\<^sub>m \<longrightarrow> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha> \<longrightarrow>
      m\<^sub>1 \<in> vc \<alpha> \<longrightarrow> (\<exists>\<beta> c\<^sub>2' m\<^sub>2'. c\<^sub>2 \<mapsto>\<^sup>*[\<beta>] c\<^sub>2' \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta> \<and> (\<alpha>,\<beta>) \<in> R\<^sub>\<alpha> \<and> (c\<^sub>1', c\<^sub>2') \<in> R\<^sub>c \<and> (m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m)"


lemma bisim_exists:
  assumes "R,G \<turnstile> P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile> P\<^sub>2 {c\<^sub>2} Q"
  assumes "(m\<^sub>1,m\<^sub>2) \<in> R\<^sub>m"
  assumes "\<langle>c\<^sub>1,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1',m\<^sub>1'\<rangle>"
  assumes "m\<^sub>1 \<in> P\<^sub>1"
  assumes "m\<^sub>2 \<in> P\<^sub>2"
  assumes "(c\<^sub>1,c\<^sub>2) \<in> R\<^sub>c"

  assumes "le_com R\<^sub>c R\<^sub>m R\<^sub>\<alpha>"
  obtains c\<^sub>2' m\<^sub>2' t' where "\<langle>c\<^sub>2,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2',m\<^sub>2'\<rangle>" "trace_rel t t' R\<^sub>\<alpha>"
  using assms(1-7) unfolding ev_def
proof safe
  assume "trace_mem m\<^sub>1 t m\<^sub>1'" 
    "R,G \<turnstile> P\<^sub>1 {c\<^sub>1} Q" "R,G \<turnstile> P\<^sub>2 {c\<^sub>2} Q" "(m\<^sub>1,m\<^sub>2) \<in> R\<^sub>m" "c\<^sub>1 \<mapsto>\<^sup>*t c\<^sub>1'" "m\<^sub>1 \<in> P\<^sub>1" "m\<^sub>2 \<in> P\<^sub>2"  "(c\<^sub>1,c\<^sub>2) \<in> R\<^sub>c"
  hence "\<exists>m\<^sub>2' c\<^sub>2' t'. (trace_mem m\<^sub>2 t' m\<^sub>2' \<and> c\<^sub>2 \<mapsto>\<^sup>*t' c\<^sub>2' \<and> trace_rel t t' R\<^sub>\<alpha>)"
  proof (induct m\<^sub>1 t m\<^sub>1' arbitrary: P\<^sub>1 P\<^sub>2 m\<^sub>2 c\<^sub>2 c\<^sub>1 rule: trace_mem.induct)
    case (1 m)
    then show ?case by simp blast
  next
    case (2 m\<^sub>1 m\<^sub>1' \<alpha> t m\<^sub>1'')
    then obtain c' where \<alpha>: "c\<^sub>1 \<mapsto>\<^sup>*[\<alpha>] c'" "c' \<mapsto>\<^sup>*t c\<^sub>1'" by auto
    then obtain P\<^sub>1' where itm1: "R,G \<turnstile> P\<^sub>1' {c'} Q" "P\<^sub>1 \<subseteq> wp\<^sub>\<alpha> \<alpha> P\<^sub>1'"  
      using trace_rule[OF \<alpha>(1) 2(4)] 2(8) by (metis empty_iff)
    hence m1': "m\<^sub>1' \<in> P\<^sub>1'" using 2(1,8) unfolding wp_def by blast
    have m1: "m\<^sub>1 \<in> vc \<alpha>" using itm1 2 by (simp add: subset_eq wp_def) 

    obtain \<beta> c\<^sub>2' m\<^sub>2' where \<beta>: "c\<^sub>2 \<mapsto>\<^sup>*[\<beta>] c\<^sub>2'" "(m\<^sub>1',m\<^sub>2') \<in> R\<^sub>m" "(c',c\<^sub>2') \<in> R\<^sub>c" "(m\<^sub>2,m\<^sub>2') \<in> beh \<beta>" "(\<alpha>,\<beta>) \<in> R\<^sub>\<alpha>"
      using 2(1,6,10) m1 \<alpha>(1) assms(8) unfolding le_com_def by blast
    then obtain P\<^sub>2' where itm2: "R,G \<turnstile> P\<^sub>2' {c\<^sub>2'} Q" "P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<beta> P\<^sub>2'"  
      using trace_rule[OF \<beta>(1) 2(5)] 2(9) by (metis empty_iff)
    hence m2': "m\<^sub>2' \<in> P\<^sub>2'" using itm2 2(1,9) \<beta> unfolding wp_def by blast
    have m2: "m\<^sub>2 \<in> vc \<beta>" using itm2 2 by (simp add: subset_eq wp_def) 

    hence itm4: "\<exists>m\<^sub>2'' c\<^sub>2'' t'. (trace_mem m\<^sub>2' t' m\<^sub>2'' \<and> c\<^sub>2' \<mapsto>\<^sup>*t' c\<^sub>2'' \<and> trace_rel t t' R\<^sub>\<alpha>)"
      using 2(3)[OF itm1(1) itm2(1) \<beta>(2) \<alpha>(2) m1' m2' \<beta>(3)] by blast

    then show ?case using \<beta>(1,3,4,5) 
      by (smt (verit) append_Cons security.trace_concat security_axioms self_append_conv2 trace_mem.intros(2) trace_rel.simps(2)) 
  qed
  thus ?thesis using that by (meson ev_def)
qed


lemma bisim_all:
  assumes "R,G \<turnstile> P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile> P\<^sub>2 {c\<^sub>2} Q"
  assumes "(m\<^sub>1,m\<^sub>2) \<in> R\<^sub>m"
  assumes "\<langle>c\<^sub>1,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1',m\<^sub>1'\<rangle>"
  assumes "\<langle>c\<^sub>2,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2',m\<^sub>2'\<rangle>"
  assumes "m\<^sub>1 \<in> P\<^sub>1"
  assumes "m\<^sub>2 \<in> P\<^sub>2"
  assumes "trace_rel t t' R\<^sub>\<alpha>"

  assumes basic: "R\<^sub>\<alpha> \<subseteq> {(\<alpha>,\<beta>). le_basic \<alpha> \<beta> R\<^sub>m}"
  shows "(m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m"
  using assms(1-8) unfolding ev_def
proof safe
  assume "trace_mem m\<^sub>1 t m\<^sub>1'" "trace_mem m\<^sub>2 t' m\<^sub>2'" 
    "R,G \<turnstile> P\<^sub>1 {c\<^sub>1} Q" "R,G \<turnstile> P\<^sub>2 {c\<^sub>2} Q" "(m\<^sub>1,m\<^sub>2) \<in> R\<^sub>m" "c\<^sub>1 \<mapsto>\<^sup>*t c\<^sub>1'" "c\<^sub>2 \<mapsto>\<^sup>*t' c\<^sub>2'" "m\<^sub>1 \<in> P\<^sub>1" "m\<^sub>2 \<in> P\<^sub>2"
    "trace_rel t t' R\<^sub>\<alpha>" 
  hence "(m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m"
  proof (induct m\<^sub>1 t m\<^sub>1' arbitrary: t' P\<^sub>1 P\<^sub>2 m\<^sub>2 c\<^sub>1 c\<^sub>2 rule: trace_mem.induct)
    case (1 m)
    then show ?case using 1 by (auto elim: trace_mem.cases)
  next
    case (2 m\<^sub>1 m\<^sub>1'' \<alpha> t m\<^sub>1')
    then obtain \<beta> tr where t: "t' = \<beta>#tr" "(\<alpha>, \<beta>) \<in> R\<^sub>\<alpha>" "trace_rel t tr R\<^sub>\<alpha>" by auto
    then obtain c\<^sub>1'' where itm1: "c\<^sub>1 \<mapsto>\<^sup>*[\<alpha>] c\<^sub>1''" "c\<^sub>1'' \<mapsto>\<^sup>*t c\<^sub>1'" using 2 by auto
    then obtain c\<^sub>2'' where itm2: "c\<^sub>2 \<mapsto>\<^sup>*[\<beta>] c\<^sub>2''" "c\<^sub>2'' \<mapsto>\<^sup>*tr c\<^sub>2'" using 2 t by blast 
    then obtain m\<^sub>2'' where itm3: "(m\<^sub>2, m\<^sub>2'') \<in> beh \<beta>" "trace_mem m\<^sub>2'' tr m\<^sub>2'"
      using 2(4) t by (metis list.distinct(1) list.inject trace_mem.cases)  

    obtain P\<^sub>1' where itm4: "R,G \<turnstile> P\<^sub>1' {c\<^sub>1''} Q" "P\<^sub>1 \<subseteq> wp\<^sub>\<alpha> \<alpha> P\<^sub>1'"  
      using trace_rule[OF itm1(1) 2(5)] 2(10) by blast
    then obtain P\<^sub>2' where itm5: "R,G \<turnstile> P\<^sub>2' {c\<^sub>2''} Q" "P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<beta> P\<^sub>2'"  
      using trace_rule[OF itm2(1) 2(6)] 2(11) by blast

    have m1: "m\<^sub>1 \<in> vc \<alpha>" using itm4 2 by (simp add: subset_eq wp_def) 
    have m2: "m\<^sub>2 \<in> vc \<beta>" using itm5 2 by (simp add: subset_eq wp_def) 

    have a: "(m\<^sub>1'', m\<^sub>2'') \<in> R\<^sub>m" using basic t(2) 2(1,7) itm3(1) m1 m2 unfolding le_basic_def
      by blast
    have b: "m\<^sub>1'' \<in> P\<^sub>1'" "m\<^sub>2'' \<in> P\<^sub>2'" 
      using itm4(2) itm5(2) 2(10,11) itm3(1) 2(1) sp_def sp_wp by fastforce+
    show ?case using 2(3)[OF itm3(2) itm4(1) itm5(1) a itm1(2) itm2(2) b t(3)] .
  qed
  thus ?thesis .
qed

theorem secure_bisim_dyn:
  assumes "R,G \<turnstile> P { c } Q"
  assumes "(c,c) \<in> R\<^sub>c"
  assumes "le_com R\<^sub>c R\<^sub>m R\<^sub>\<alpha>"
  assumes "R\<^sub>\<alpha> \<subseteq> {(\<alpha>, \<beta>). le_basic \<alpha> \<beta> R\<^sub>m}"
  shows "secure c P R\<^sub>m {(t,t'). trace_rel t t' R\<^sub>\<alpha>}"
  unfolding secure_def
proof (intro allI impI conjI)
  fix m\<^sub>1 m\<^sub>2 c\<^sub>1 t m\<^sub>1'
  assume a: "m\<^sub>1 \<in> P" "m\<^sub>2 \<in> P" "(m\<^sub>1, m\<^sub>2) \<in> R\<^sub>m" "\<langle>c,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1,m\<^sub>1'\<rangle>"
  show "(\<exists>m\<^sub>2' c\<^sub>2 t'.
           (t, t') \<in> {(t, t'). trace_rel t t' R\<^sub>\<alpha>} \<and>
           \<langle>c,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2,m\<^sub>2'\<rangle>)"
    using bisim_exists[OF assms(1) assms(1) a(3,4,1,2) assms(2,3)] by fastforce
next
  fix m\<^sub>1 m\<^sub>2 c\<^sub>1 t m\<^sub>1' m\<^sub>2' c\<^sub>2 t'
  assume a: "m\<^sub>1 \<in> P" "m\<^sub>2 \<in> P" "(m\<^sub>1, m\<^sub>2) \<in> R\<^sub>m" "\<langle>c,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1,m\<^sub>1'\<rangle>" 
            "(t, t') \<in> {(t, t'). trace_rel t t' R\<^sub>\<alpha>}" " \<langle>c,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2,m\<^sub>2'\<rangle>"
  thus "(m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m" using bisim_all assms(1,4) by blast
qed

section \<open>Dynamic Property from Static Property\<close>

inductive prog_rel :: "('a,'b,'c) com \<Rightarrow> ('a,'b,'c) com \<Rightarrow> ('a,'b) basic set \<Rightarrow> ('a,'b) wmm set \<Rightarrow> 'c rel \<Rightarrow> bool"
  where
    "prog_rel Nil Nil S W F" |
    "\<alpha> \<in> S \<Longrightarrow> prog_rel (Basic \<alpha>) (Basic \<alpha>) S W F" |
    "w \<in> W \<Longrightarrow> prog_rel c\<^sub>1 c\<^sub>1' S W F \<Longrightarrow> prog_rel c\<^sub>2 c\<^sub>2' S W F \<Longrightarrow>
      prog_rel (c\<^sub>1 ;\<^sub>w c\<^sub>2) (c\<^sub>1' ;\<^sub>w c\<^sub>2') S W F" |
    "\<forall>f. prog_rel (C f) (C' f) S W F \<Longrightarrow> prog_rel (Choice C) (Choice C') S W F" |
    "w \<in> W \<Longrightarrow> prog_rel c c' S W F \<Longrightarrow> prog_rel (Loop c w) (Loop c' w) S W F" |
    "prog_rel c\<^sub>1 c\<^sub>1' S W F \<Longrightarrow> prog_rel c\<^sub>2 c\<^sub>2' S W F \<Longrightarrow> prog_rel (c\<^sub>1 || c\<^sub>2) (c\<^sub>1' || c\<^sub>2') S W F" |
    "(s,s') \<in> F \<Longrightarrow> prog_rel c c' S W F \<Longrightarrow> prog_rel (Capture s c) (Capture s' c') S W F" |
    "prog_rel c\<^sub>1 c\<^sub>2 S W F \<Longrightarrow> prog_rel (Interrupt c\<^sub>1) (Interrupt c\<^sub>2) S W F" |
    "prog_rel c\<^sub>1 c\<^sub>2 S W F \<Longrightarrow> prog_rel (Thread c\<^sub>1) (Thread c\<^sub>2) S W F"

inductive_cases sec_pres_NilE [elim!]: "prog_rel Nil c' S W F"
inductive_cases sec_pres_BasicE [elim!]: "prog_rel (Basic \<alpha>) c' S W F"
inductive_cases sec_pres_SeqE [elim!]: "prog_rel (c\<^sub>1 ;\<^sub>w c\<^sub>2) c' S W F"
inductive_cases sec_pres_ChoiceE [elim!]: "prog_rel (Choice C) c' S W F"
inductive_cases sec_pres_LoopE [elim!]: "prog_rel (Loop c w) c' S W F"
inductive_cases sec_pres_CaptureE [elim!]: "prog_rel (Capture s c) c' S W F"
inductive_cases sec_pres_ParallelE [elim!]: "prog_rel (c || c'') c' S W F"
inductive_cases sec_pres_InterruptE [elim!]: "prog_rel (Interrupt c) c' S W F"
inductive_cases sec_pres_ThreadE [elim!]: "prog_rel (Thread c) c' S W F"

lemma re_stable:
  assumes "\<beta>' < c <\<^sub>w \<beta>"
  assumes "prog_rel c c' S W F"
  shows "\<beta>' < c' <\<^sub>w \<beta>" 
  using assms
proof (induct \<beta>' c w \<beta> arbitrary: c' rule: reorder_com.induct)
  case (1 \<alpha>' c \<alpha>)
  hence "c' = Nil" by auto
  then show ?case using 1(1) by auto
next
  case (2 \<alpha>' \<beta> w \<alpha>)
  hence "c' = Basic \<beta>" by auto
  then show ?case using 2(1) by auto
next
  case (3 \<alpha>' c\<^sub>1 w c\<^sub>2 c \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "\<alpha>' < c\<^sub>1  <\<^sub>c \<alpha>''" "\<alpha>'' < c\<^sub>2  <\<^sub>c \<alpha>" by auto
  obtain c\<^sub>1' c\<^sub>2' where c: "c' = c\<^sub>1' ;\<^sub>w c\<^sub>2'" "prog_rel c\<^sub>1 c\<^sub>1' S W F" "prog_rel c\<^sub>2 c\<^sub>2' S W F"
    using 3(4) by clarsimp
  show ?case using 3(2)[OF \<alpha>(2) c(3)] 3(1)[OF \<alpha>(1) c(2)] unfolding c reorder_com.simps by blast
qed auto

definition pop_stable
  where "pop_stable R\<^sub>\<alpha> R\<^sub>f \<equiv> \<forall>(\<alpha>, \<beta>s) \<in> R\<^sub>\<alpha>. \<forall>(s\<^sub>1, s\<^sub>2) \<in> R\<^sub>f. \<forall>s\<^sub>1'. \<exists>\<beta>s'. 
          ((tag \<alpha>, poppred' s\<^sub>1 (vc \<alpha>), poprel' s\<^sub>1 s\<^sub>1' (beh \<alpha>)), \<beta>s') \<in> R\<^sub>\<alpha> \<and>
          (\<forall>\<beta>\<in>\<beta>s'. \<exists>\<beta>p\<in>\<beta>s. \<exists>s\<^sub>2'. \<beta> = (tag \<beta>p, poppred' s\<^sub>2 (vc \<beta>p), poprel' s\<^sub>2 s\<^sub>2' (beh \<beta>p)) \<and>
                     (s\<^sub>1', s\<^sub>2') \<in> R\<^sub>f)"

definition re_stable
  where "re_stable S R\<^sub>\<alpha> W \<equiv> \<forall>(\<alpha>, \<beta>s) \<in> R\<^sub>\<alpha>. \<forall>w \<in> W. \<forall>\<gamma> \<in> S. \<forall>\<alpha>'.  w \<alpha>' \<gamma> \<alpha> \<longrightarrow> 
                            (\<exists>\<beta>s'. (\<alpha>',\<beta>s') \<in> R\<^sub>\<alpha> \<and> (\<forall>\<beta>\<in>\<beta>s'. \<exists>\<beta>p\<in>\<beta>s. w \<beta> \<gamma> \<beta>p))"

lemma re_stable_com:
  assumes "\<alpha>' < c <\<^sub>w \<alpha>"
  assumes "(\<alpha>, \<beta>s) \<in> R\<^sub>\<alpha>"
  assumes "w\<in>W"
  assumes "re_stable S R\<^sub>\<alpha> W"
  obtains \<beta>s' where "(\<alpha>',\<beta>s') \<in> R\<^sub>\<alpha>" "\<forall>\<beta>\<in>\<beta>s'. \<exists>\<beta>p\<in>\<beta>s. \<beta> < c <\<^sub>w \<beta>p"
  using assms(1,2,3)
proof (induct \<alpha>' c w \<alpha> arbitrary: \<beta>s rule: reorder_com.induct)
  case (1 \<alpha>' c \<alpha>)
  then show ?case by auto
next
  case (2 \<alpha>' \<beta> w \<alpha>)
  then show ?case using assms(4) unfolding re_stable_def
    sorry (*by (smt (verit, best) case_prodD reorder_com.simps(2))*)
next
  case (3 \<alpha>' c\<^sub>1 w c\<^sub>2 c \<alpha>)
  then obtain \<alpha>'' where \<alpha>: "\<alpha>' < c\<^sub>1  <\<^sub>c \<alpha>''" "\<alpha>'' < c\<^sub>2  <\<^sub>c \<alpha>" by auto
  show ?case
  proof (rule 3(2)[OF _ \<alpha>(2) 3(5,6)], goal_cases a)
    case (a \<beta>s')
    show ?case
    proof (rule 3(1)[OF _ \<alpha>(1) a(1) 3(6)], goal_cases b)
      case (b \<beta>s'')
      then show ?case using 3(3) a(2) by fastforce
    qed
  qed
qed auto

lemma lexec_prog_rel:
  assumes "lexecute c\<^sub>1 \<alpha> r c\<^sub>1'"
  assumes "prog_rel c\<^sub>1 c\<^sub>2 S W R\<^sub>f" 

  assumes basic: "\<forall>\<alpha> \<in> S. (\<alpha>,{\<alpha>}) \<in> R\<^sub>\<alpha>"
  assumes frame: "pop_stable R\<^sub>\<alpha> R\<^sub>f"
  assumes re: "re_stable S R\<^sub>\<alpha> W"

  obtains \<beta>s where "(\<alpha>,\<beta>s) \<in> R\<^sub>\<alpha>" "\<forall>\<beta> \<in> \<beta>s. (\<exists>c\<^sub>2' r'. lexecute c\<^sub>2 \<beta> r' c\<^sub>2' \<and> prog_rel c\<^sub>1' c\<^sub>2' S W R\<^sub>f)" 
  using assms(1-2)
proof (induct arbitrary: c\<^sub>2)
  case (act \<alpha>)
  hence c: "c\<^sub>2 = Basic \<alpha>" "\<alpha> \<in> S" by auto
  thus ?case using act(1) c prog_rel.intros(1) basic by blast    
next
  case (ino c\<^sub>1 \<alpha>' r c\<^sub>1' w c\<^sub>2)
  thus ?case by clarsimp (metis lexecute.ino prog_rel.intros(3))
next
  case (ooo c\<^sub>1 \<alpha> r c\<^sub>1' \<alpha>' c\<^sub>2' w)
  show ?case using ooo(5)
  proof (cases rule: prog_rel.cases)
    case (3 c\<^sub>1'' c\<^sub>2'')
    show ?thesis
    proof (rule ooo(2)[OF _ 3(4)])
      fix \<beta>s assume a: "(\<alpha>,\<beta>s) \<in> R\<^sub>\<alpha>" "\<forall>\<beta>\<in>\<beta>s. \<exists>c\<^sub>2' r'. c\<^sub>2'' \<mapsto>[\<beta>,r'] c\<^sub>2' \<and> prog_rel c\<^sub>1' c\<^sub>2' S W R\<^sub>f"
      obtain \<beta>s' where \<beta>: "\<forall>\<beta> \<in> \<beta>s'. \<exists>\<beta>p \<in> \<beta>s. \<beta> < c\<^sub>2' <\<^sub>w \<beta>p" "(\<alpha>',\<beta>s') \<in> R\<^sub>\<alpha>"
        using ooo(3) a(1) 3(2) re_stable_com[OF _ _ _ re] by metis

      have "\<forall>\<beta>\<in>\<beta>s'. \<exists>c\<^sub>2''' r'. c\<^sub>2 \<mapsto>[\<beta>,r'] c\<^sub>2''' \<and> prog_rel (c\<^sub>2' ;\<^sub>w c\<^sub>1' ) c\<^sub>2''' S W R\<^sub>f"
        using a(2) \<beta> 3 by (meson lexecute.ooo prog_rel.intros(3) re_stable)
      thus ?thesis using ooo(4) \<beta>(2) by blast
    qed
  qed
next
  case (cap c \<alpha> r c' s\<^sub>1 s\<^sub>1')
  show ?case using cap(4)
  proof (cases rule: prog_rel.cases)
    case (7 s\<^sub>2 c'')
    show ?thesis
    proof (rule cap(2)[OF _ 7(3)])
      fix \<beta>s assume a: "(\<alpha>, \<beta>s) \<in> R\<^sub>\<alpha>" "\<forall>\<beta>\<in>\<beta>s. \<exists>c\<^sub>2' r'. c'' \<mapsto>[\<beta>,r'] c\<^sub>2' \<and> prog_rel c' c\<^sub>2' S W R\<^sub>f"
      obtain \<beta>s' where b:
        "((tag \<alpha>, poppred' s\<^sub>1 (vc \<alpha>), poprel' s\<^sub>1 s\<^sub>1' (beh \<alpha>)), \<beta>s') \<in> R\<^sub>\<alpha>" 
        "\<forall>\<beta>\<in>\<beta>s'. \<exists>\<beta>p \<in> \<beta>s. \<exists>s\<^sub>2'. \<beta> = (tag \<beta>p, poppred' s\<^sub>2 (vc \<beta>p), poprel' s\<^sub>2 s\<^sub>2' (beh \<beta>p)) \<and> (s\<^sub>1',s\<^sub>2') \<in> R\<^sub>f"
        using a(1) 7(2) frame unfolding pop_stable_def by blast
      have "\<forall>\<beta>\<in>\<beta>s'. \<exists>c\<^sub>2' r'. Capture s\<^sub>2 c'' \<mapsto>[\<beta>,r'] c\<^sub>2' \<and> prog_rel (Capture s\<^sub>1' c') c\<^sub>2' S W R\<^sub>f"
      proof (intro ballI)
        fix \<beta> assume "\<beta> \<in> \<beta>s'"
        then obtain \<beta>p s\<^sub>2' where c: "\<beta>p \<in> \<beta>s" "\<beta> = (tag \<beta>p, poppred' s\<^sub>2 (vc \<beta>p), poprel' s\<^sub>2 s\<^sub>2' (beh \<beta>p))" "(s\<^sub>1',s\<^sub>2') \<in> R\<^sub>f"
          using b by blast
        then obtain c\<^sub>2' r' where d: "c'' \<mapsto>[\<beta>p,r'] c\<^sub>2'" "prog_rel c' c\<^sub>2' S W R\<^sub>f"
          using a by fast
        hence "Capture s\<^sub>2 c'' \<mapsto>[\<beta>,Scope # r'] Capture s\<^sub>2' c\<^sub>2'" unfolding c using lexecute.cap by blast

        thus "\<exists>c\<^sub>2' r'. Capture s\<^sub>2 c'' \<mapsto>[\<beta>,r'] c\<^sub>2' \<and> prog_rel (Capture s\<^sub>1' c') c\<^sub>2' S W R\<^sub>f"
          using prog_rel.intros d(2) c(3) by auto
      qed
      thus ?thesis using cap(3)[OF b(1)] 7(1) by blast
    qed
  qed
next
  case (inter1 c \<alpha>' r c')
  thus ?case by clarsimp (meson lexecute.inter1 prog_rel.intros(8))
qed

lemma gexec_prog_rel:
  assumes "c\<^sub>1 \<mapsto>[\<alpha>] c\<^sub>1'"
  assumes "prog_rel c\<^sub>1 c\<^sub>2 S W R\<^sub>f"

  assumes basic: "\<forall>\<alpha> \<in> S. (\<alpha>,{\<alpha>}) \<in> R\<^sub>\<alpha>" "pop_stable R\<^sub>\<alpha> R\<^sub>f" "re_stable S R\<^sub>\<alpha> W"

  obtains \<beta>s where "(\<alpha>,\<beta>s) \<in> R\<^sub>\<alpha>" "\<forall>\<beta> \<in> \<beta>s. (\<exists>c\<^sub>2'. c\<^sub>2 \<mapsto>[\<beta>] c\<^sub>2' \<and> prog_rel c\<^sub>1' c\<^sub>2' S W R\<^sub>f)" 
  using assms(1-2)
proof (induct arbitrary: c\<^sub>2)
  case (thr c \<alpha>' r c')
  show ?case using thr(3)
  proof (cases rule: prog_rel.cases)
    case (9 c\<^sub>2)
    then show ?thesis 
       using lexec_prog_rel[OF _ _ basic] 
       using gexecute.thr prog_rel.intros(9) thr(1,2) 
       by metis
  qed
next
  case (par1 c\<^sub>1 g c\<^sub>1' c\<^sub>2)
  then show ?case by clarsimp (metis gexecute.par1 prog_rel.intros(6))
next
  case (par2 c\<^sub>2 g c\<^sub>2' c\<^sub>1)
  then show ?case by clarsimp (metis gexecute.par2 prog_rel.intros(6))
qed

lemma rw_prog_rel:
  assumes "c\<^sub>1 \<leadsto> c\<^sub>1'"
  assumes "prog_rel c\<^sub>1 c\<^sub>2 S W R\<^sub>f"
  obtains c\<^sub>2' where "c\<^sub>2 \<leadsto> c\<^sub>2'" "prog_rel c\<^sub>1' c\<^sub>2' S W R\<^sub>f"
  using assms
proof (induct arbitrary: c\<^sub>2)
  case (seq1 c\<^sub>1 c\<^sub>1' w c\<^sub>2)
  then show ?case by clarsimp (meson prog_rel.intros(3) silent.seq1)
next
  case (seq2 c\<^sub>2 c\<^sub>2' c\<^sub>1 w)
  then show ?case by clarsimp (meson prog_rel.intros(3) silent.seq2)
next
  case (seqE1 w c\<^sub>1)
  then show ?case by clarsimp (meson silent.intros)
next
  case (seqE2 c\<^sub>1 w)
  then show ?case by clarsimp (meson silent.intros)
next
  case (pick S l)
  then show ?case by clarsimp (meson silent.intros)
next
  case (loop1 c w)
  then show ?case by clarsimp (meson prog_rel.intros silent.intros)
next
  case (loop2 c w)
  then show ?case by clarsimp (meson prog_rel.intros silent.intros)
next
  case (par1 c\<^sub>1 c\<^sub>1' c\<^sub>2)
  then show ?case by clarsimp (meson prog_rel.intros(6) silent.par1) 
next
  case (par2 c\<^sub>2 c\<^sub>2' c\<^sub>1)
  then show ?case by clarsimp (meson prog_rel.intros(6) silent.par2) 
next
  case (parE1 c)
  then show ?case by clarsimp (meson silent.intros)
next
  case (parE2 c)
  then show ?case by clarsimp (meson silent.intros)
next
  case (thr c c')
  then show ?case by clarsimp (meson prog_rel.intros silent.intros)
next
  case thrE
  then show ?case by clarsimp (meson prog_rel.intros silent.intros)
next
  case (capE k)
  then show ?case by clarsimp (meson prog_rel.intros silent.intros)
next
  case (capS c c' k)
  then show ?case by clarsimp (meson prog_rel.intros silent.capS) 
next
  case (intr1 c c')
  then show ?case by clarsimp (meson prog_rel.intros silent.intros) 
next
  case (intrE c)
  then show ?case by clarsimp (meson prog_rel.intros silent.intros) 
qed

lemma rwstar_prog_rel:
  assumes "c\<^sub>1 \<mapsto>\<^sup>*[] c\<^sub>1'"
  assumes "prog_rel c\<^sub>1 c\<^sub>2 S W R\<^sub>f"
  obtains g' c\<^sub>2' r' where "c\<^sub>2 \<mapsto>\<^sup>*[] c\<^sub>2'" "prog_rel c\<^sub>1' c\<^sub>2' S W R\<^sub>f"
  using assms
proof (induct c\<^sub>1 "[] :: ('a,'b) Trace" c\<^sub>1' arbitrary: c\<^sub>2)
  case (none c)
  then show ?case by blast
next
  case (sil c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case by (meson rw_prog_rel trace.sil)
qed 

lemma gstar_prog_rel:
  assumes "c\<^sub>1 \<mapsto>\<^sup>*[\<alpha>] c\<^sub>1'"
  assumes "prog_rel c\<^sub>1 c\<^sub>2 S W R\<^sub>f"  

  assumes basic: "\<forall>\<alpha> \<in> S. (\<alpha>,{\<alpha>}) \<in> R\<^sub>\<alpha>" "pop_stable R\<^sub>\<alpha> R\<^sub>f" "re_stable S R\<^sub>\<alpha> W"

  obtains \<beta>s where "(\<alpha>,\<beta>s) \<in> R\<^sub>\<alpha>" "\<forall>\<beta> \<in> \<beta>s. (\<exists>c\<^sub>2'. c\<^sub>2 \<mapsto>\<^sup>*[\<beta>] c\<^sub>2' \<and> prog_rel c\<^sub>1' c\<^sub>2' S W R\<^sub>f)" 
  using assms(1,2)
proof (induct c\<^sub>1 "[\<alpha>]" c\<^sub>1' arbitrary: c\<^sub>2) 
  case (sil c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case using rw_prog_rel by (metis trace.sil)
next
  case (gex c\<^sub>1 c\<^sub>2' c\<^sub>3)
  show ?case 
    using gexec_prog_rel[OF gex(1,4) basic] 
    using rwstar_prog_rel[OF gex(2)] gex(3)
    by (metis trace.gex)
qed

definition flatten
  where "flatten R = {(\<alpha>,\<beta>). \<exists>s. (\<alpha>,s) \<in> R \<and> \<beta> \<in> s}"

lemma le_comI:
  assumes basic: "\<forall>\<alpha> \<in> S. (\<alpha>,{\<alpha>}) \<in> R\<^sub>\<alpha>" "pop_stable R\<^sub>\<alpha> R\<^sub>f" "re_stable S R\<^sub>\<alpha> W"
  assumes prog: "\<forall>(\<alpha>,\<beta>s) \<in> R\<^sub>\<alpha>. \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'. (m\<^sub>1, m\<^sub>2) \<in> R\<^sub>m \<longrightarrow> m\<^sub>1 \<in> vc \<alpha> \<longrightarrow> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha> \<longrightarrow> 
                                  (\<exists>\<beta> m\<^sub>2'. (m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta> \<and> \<beta> \<in> \<beta>s)"

  shows "le_com ({(c\<^sub>1,c\<^sub>2). prog_rel c\<^sub>1 c\<^sub>2 S W R\<^sub>f}) R\<^sub>m (flatten R\<^sub>\<alpha>)"
  unfolding le_com_def
proof (intro allI impI)
  fix m\<^sub>1 m\<^sub>2 m\<^sub>1' c\<^sub>1 c\<^sub>2 \<alpha> c\<^sub>1' 
  assume a: "(c\<^sub>1, c\<^sub>2) \<in> {(c\<^sub>1, c\<^sub>2). prog_rel c\<^sub>1 c\<^sub>2 S W R\<^sub>f}" "c\<^sub>1 \<mapsto>\<^sup>*[\<alpha>] c\<^sub>1'" 
  assume m: "(m\<^sub>1, m\<^sub>2) \<in> R\<^sub>m" "(m\<^sub>1, m\<^sub>1') \<in> beh \<alpha>" "m\<^sub>1 \<in> vc \<alpha>"
  obtain \<beta>s where "(\<alpha>,\<beta>s) \<in> R\<^sub>\<alpha>" "\<forall>\<beta> \<in> \<beta>s. (\<exists>c\<^sub>2'. c\<^sub>2 \<mapsto>\<^sup>*[\<beta>] c\<^sub>2' \<and> prog_rel c\<^sub>1' c\<^sub>2' S W R\<^sub>f)" 
    using a gstar_prog_rel[OF _ _  basic] by blast
  thus "\<exists>\<beta> c\<^sub>2' m\<^sub>2'. c\<^sub>2 \<mapsto>\<^sup>*[\<beta>] c\<^sub>2' \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta> \<and> (\<alpha>, \<beta>) \<in> (flatten R\<^sub>\<alpha>) \<and>
          (c\<^sub>1', c\<^sub>2') \<in> {(c\<^sub>1, c\<^sub>2). prog_rel c\<^sub>1 c\<^sub>2 S W R\<^sub>f} \<and> (m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m"
    using prog m unfolding flatten_def 
    by (smt (verit, del_insts) case_prod_conv mem_Collect_eq)
qed

theorem secure_bisim:
  assumes "R,G \<turnstile> P { c } Q"
  assumes basic: "\<forall>\<alpha> \<in> S. (\<alpha>,{\<alpha>}) \<in> R\<^sub>\<alpha>" 
  assumes frame: "pop_stable R\<^sub>\<alpha> R\<^sub>f"
  assumes re: "re_stable S R\<^sub>\<alpha> W"
  assumes prog: "\<forall>(\<alpha>,\<beta>s) \<in> R\<^sub>\<alpha>. \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'. (m\<^sub>1, m\<^sub>2) \<in> R\<^sub>m \<longrightarrow> m\<^sub>1 \<in> vc \<alpha> \<longrightarrow> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha> \<longrightarrow> 
                                  (\<exists>\<beta> m\<^sub>2'. (m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta> \<and> \<beta> \<in> \<beta>s)"
  assumes pr: "prog_rel c c S W R\<^sub>f"
  assumes sec: "(flatten R\<^sub>\<alpha>) \<subseteq> {(\<alpha>, \<beta>). le_basic \<alpha> \<beta> R\<^sub>m}"
  shows "secure c P R\<^sub>m {(t,t'). trace_rel t t' (flatten R\<^sub>\<alpha>)}"
  using assms(1)
  apply (rule secure_bisim_dyn)
    prefer 2
  using basic frame re prog
  apply (rule le_comI)
   apply simp
  using pr
   apply simp
  using basic sec by blast

end

end