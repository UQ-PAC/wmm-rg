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
  "le_basic \<alpha> \<beta> R\<^sub>m \<equiv> \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'. 
      m\<^sub>1 \<in> vc \<alpha> \<longrightarrow> m\<^sub>2 \<in> vc \<beta> \<longrightarrow> (m\<^sub>1,m\<^sub>2) \<in> R\<^sub>m \<longrightarrow> (m\<^sub>1,m\<^sub>1') \<in> beh \<alpha> \<longrightarrow> 
      (\<exists>m\<^sub>2'. (m\<^sub>2,m\<^sub>2') \<in> beh \<beta>) \<and> (\<forall>m\<^sub>2'. (m\<^sub>2,m\<^sub>2') \<in> beh \<beta> \<longrightarrow> (m\<^sub>1',m\<^sub>2') \<in> R\<^sub>m)"

text \<open>Low-equivalence structure for a command\<close>
definition le_com :: "('a,'b,'c) com rel \<Rightarrow> ('a,'b) basic rel \<Rightarrow> bool"
  where 
  "le_com S R \<equiv> \<forall>c\<^sub>1 c\<^sub>2 \<alpha> c\<^sub>1'. (c\<^sub>1, c\<^sub>2) \<in> S \<longrightarrow> c\<^sub>1 \<mapsto>\<^sup>*[\<alpha>] c\<^sub>1' \<longrightarrow>
      (\<exists>\<beta> c\<^sub>2'. c\<^sub>2 \<mapsto>\<^sup>*[\<beta>] c\<^sub>2' \<and> (\<alpha>,\<beta>) \<in> R \<and> (c\<^sub>1', c\<^sub>2') \<in> S)"

lemma bisim_exists:
  assumes "R,G \<turnstile> P\<^sub>1 {c\<^sub>1} Q"
  assumes "R,G \<turnstile> P\<^sub>2 {c\<^sub>2} Q"
  assumes "(m\<^sub>1,m\<^sub>2) \<in> R\<^sub>m"
  assumes "\<langle>c\<^sub>1,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1',m\<^sub>1'\<rangle>"
  assumes "m\<^sub>1 \<in> P\<^sub>1"
  assumes "m\<^sub>2 \<in> P\<^sub>2"
  assumes "(c\<^sub>1,c\<^sub>2) \<in> R\<^sub>c"

  assumes com: "le_com R\<^sub>c R\<^sub>\<alpha>"
  assumes basic: "R\<^sub>\<alpha> \<subseteq> {(\<alpha>,\<beta>). le_basic \<alpha> \<beta> R\<^sub>m}"
  obtains c\<^sub>2' m\<^sub>2' t' where "\<langle>c\<^sub>2,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2',m\<^sub>2'\<rangle>" "trace_rel t t' R\<^sub>\<alpha>"
  using assms(1-7) unfolding ev_def
proof safe
  assume "trace_mem m\<^sub>1 t m\<^sub>1'" 
    "R,G \<turnstile> P\<^sub>1 {c\<^sub>1} Q" "R,G \<turnstile> P\<^sub>2 {c\<^sub>2} Q" "(m\<^sub>1,m\<^sub>2) \<in> R\<^sub>m" "c\<^sub>1 \<mapsto>\<^sup>*t c\<^sub>1'" "m\<^sub>1 \<in> P\<^sub>1" "m\<^sub>2 \<in> P\<^sub>2" "(c\<^sub>1,c\<^sub>2) \<in> R\<^sub>c"
  hence "\<exists>m\<^sub>2' c\<^sub>2' t'. (trace_mem m\<^sub>2 t' m\<^sub>2' \<and> c\<^sub>2 \<mapsto>\<^sup>*t' c\<^sub>2' \<and> trace_rel t t' R\<^sub>\<alpha>) "
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

    then obtain \<beta> c\<^sub>2' where \<beta>: "c\<^sub>2 \<mapsto>\<^sup>*[\<beta>] c\<^sub>2'" "(\<alpha>,\<beta>) \<in> R\<^sub>\<alpha>" "(c', c\<^sub>2') \<in> R\<^sub>c"
      using com 2(10) \<alpha> unfolding le_com_def by blast
    then obtain P\<^sub>2' where itm2: "R,G \<turnstile> P\<^sub>2' {c\<^sub>2'} Q" "P\<^sub>2 \<subseteq> wp\<^sub>\<alpha> \<beta> P\<^sub>2'"  
      using trace_rule[OF \<beta>(1) 2(5)] 2(9) by (metis empty_iff)
    have m2: "m\<^sub>2 \<in> vc \<beta>" using itm2 2 by (simp add: subset_eq wp_def) 

    then obtain m\<^sub>2' where itm3: "(m\<^sub>2,m\<^sub>2') \<in> beh \<beta>" "(m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m"
      using m1 \<beta> basic 2(1,6) unfolding le_basic_def by blast
    hence m2': "m\<^sub>2' \<in> P\<^sub>2'" using itm2 2(1,9) unfolding wp_def by blast

    hence itm4: "\<exists>m\<^sub>2'' c\<^sub>2'' t'. (trace_mem m\<^sub>2' t' m\<^sub>2'' \<and> c\<^sub>2' \<mapsto>\<^sup>*t' c\<^sub>2'' \<and> trace_rel t t' R\<^sub>\<alpha>)"
      using 2(3)[OF itm1(1) itm2(1) itm3(2) \<alpha>(2) m1' m2' \<beta>(3)] by blast

    then show ?case using itm3(1) \<beta>(1,2) 
      by (smt (verit) append_Cons trace_concat  self_append_conv2 trace_mem.intros(2) trace_rel.simps(2))
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

theorem secure_bisim:
  assumes "R,G \<turnstile> P { c } Q"
  assumes "refl R\<^sub>c"
  assumes "le_com R\<^sub>c R\<^sub>\<alpha>"
  assumes "R\<^sub>\<alpha> \<subseteq> {(\<alpha>, \<beta>). le_basic \<alpha> \<beta> R\<^sub>m}"
  shows "secure c P R\<^sub>m {(t,t'). trace_rel t t' R\<^sub>\<alpha>}"
  unfolding secure_def
proof (intro allI impI conjI)
  fix m\<^sub>1 m\<^sub>2 c\<^sub>1 t m\<^sub>1'
  assume a: "m\<^sub>1 \<in> P" "m\<^sub>2 \<in> P" "(m\<^sub>1, m\<^sub>2) \<in> R\<^sub>m" "\<langle>c,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1,m\<^sub>1'\<rangle>"
  show "(\<exists>m\<^sub>2' c\<^sub>2 t'.
           (t, t') \<in> {(t, t'). trace_rel t t' R\<^sub>\<alpha>} \<and>
           \<langle>c,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2,m\<^sub>2'\<rangle>)"
    using bisim_exists[OF assms(1) assms(1) a(3,4,1,2) _ assms(3,4)]
    using assms(2) reflD by fastforce 
next
  fix m\<^sub>1 m\<^sub>2 c\<^sub>1 t m\<^sub>1' m\<^sub>2' c\<^sub>2 t'
  assume a: "m\<^sub>1 \<in> P" "m\<^sub>2 \<in> P" "(m\<^sub>1, m\<^sub>2) \<in> R\<^sub>m" "\<langle>c,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1,m\<^sub>1'\<rangle>" 
            "(t, t') \<in> {(t, t'). trace_rel t t' R\<^sub>\<alpha>}" " \<langle>c,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t' \<langle>c\<^sub>2,m\<^sub>2'\<rangle>"
  thus "(m\<^sub>1', m\<^sub>2') \<in> R\<^sub>m" using bisim_all assms(1,4) by blast
qed

end

end