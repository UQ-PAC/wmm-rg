theory Security
  imports Soundness
begin

locale security = rules 

type_synonym ('a,'b) Trace = "('b \<times> 'b) set list" 

context security
begin

inductive_set trace :: "(('a,'b) com \<times> ('a,'b) Trace \<times> ('a,'b) com) set"
  and trace_abv :: "('a,'b) com \<Rightarrow> ('a,'b) Trace \<Rightarrow> ('a,'b) com \<Rightarrow> bool" ("_ \<mapsto>\<^sup>*_ _" [50,40,40] 70)
  where
  "trace_abv P t P' \<equiv> (P, t, P') \<in> trace"
  | none[intro]: "c \<mapsto>\<^sup>*[] c" 
  | sil[intro]: "c\<^sub>1 \<leadsto> c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sup>*t c\<^sub>3"
  | gex[intro]: "c\<^sub>1 \<mapsto>[g] c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sup>*g#t c\<^sub>3"

inductive trace_mem :: "'m \<Rightarrow> 'm rel list  \<Rightarrow> 'm \<Rightarrow> bool" 
  where
    [intro]: "trace_mem m [] m" |
    [intro]: "(m'', m) \<in> g \<Longrightarrow> trace_mem m t m' \<Longrightarrow> trace_mem m'' (g#t) m'"

definition ev :: "('a,'b) com \<Rightarrow> 'b \<Rightarrow> ('a,'b) Trace \<Rightarrow> ('a,'b) com \<Rightarrow> 'b \<Rightarrow> bool"
  ("\<langle>_,_\<rangle> \<rightarrow>\<^sup>*_ \<langle>_,_\<rangle>" [50,40,40] 70)
  where "\<langle>c,m\<rangle> \<rightarrow>\<^sup>*t \<langle>c',m'\<rangle> \<equiv> trace_mem m t m' \<and> c \<mapsto>\<^sup>*t c'"

text \<open> Noninterference over all basic commands \<close>

definition sec_pres :: "('a,'b) com \<Rightarrow> 'b rel \<Rightarrow> bool"
  where 
  "sec_pres c S \<equiv> \<forall>\<alpha> r m\<^sub>1 m\<^sub>2 m\<^sub>1'. 
     ((beforeReord \<alpha> r) \<inter> (basics c) \<noteq> {}) \<longrightarrow> m\<^sub>1 \<in> vc \<alpha> \<longrightarrow> (m\<^sub>1,m\<^sub>2) \<in> S \<longrightarrow> 
                             (m\<^sub>1,m\<^sub>1') \<in> beh \<alpha> \<longrightarrow> (\<exists>m\<^sub>2'. (m\<^sub>2,m\<^sub>2') \<in> beh \<alpha> \<and> (m\<^sub>1',m\<^sub>2') \<in> S)"

text \<open> Noninterference over all traces \<close>

definition secure :: "('a,'b) com \<Rightarrow> 'b set \<Rightarrow> 'b rel \<Rightarrow> bool"
  where "secure c P S \<equiv> \<forall>m\<^sub>1 m\<^sub>2 c\<^sub>1 t m\<^sub>1'. 
        m\<^sub>1 \<in> P \<longrightarrow> \<langle>c,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1,m\<^sub>1'\<rangle> \<longrightarrow> (m\<^sub>1,m\<^sub>2) \<in> S \<longrightarrow>
        (\<exists>m\<^sub>2' c\<^sub>2. \<langle>c,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>2,m\<^sub>2'\<rangle> \<and> (m\<^sub>1',m\<^sub>2') \<in> S)"  

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
  assumes "c \<mapsto>\<^sup>*[g] c'"
  assumes "R,G \<turnstile> P {c} Q"
  shows "\<exists>\<alpha> r M. (beforeReord \<alpha> r) \<inter> (basics c) \<noteq> {} \<and> 
              g = beh \<alpha> \<and> P \<subseteq> wp\<^sub>\<alpha> \<alpha> M \<and> guar\<^sub>\<alpha> \<alpha>  G \<and> R,G \<turnstile> M {c'} Q"
  using assms 
proof (induct c "[g]" c' arbitrary: P) 
  case (sil c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case using basics_silent rewrite_ruleI 
    by (smt (verit, ccfv_SIG) inf.absorb_iff1 inf_bot_right inf_left_commute)
next
  case (gex c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case using basics_lexec trace_rule_nil gexecute_ruleI[OF gex(3,1)]
    by (metis beforeReord.simps(3) fst_conv snd_conv basics_gexecute)
qed 


lemma bisim_exists:
  assumes "sec_pres c S"
  assumes "R,G \<turnstile> P {c} Q"
  assumes "(m\<^sub>1,m\<^sub>2) \<in> S"
  assumes "\<langle>c,m\<^sub>1\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>1,m\<^sub>1'\<rangle>"
  assumes "m\<^sub>1 \<in> P"
  obtains c\<^sub>2 m\<^sub>2' where "\<langle>c,m\<^sub>2\<rangle> \<rightarrow>\<^sup>*t \<langle>c\<^sub>2,m\<^sub>2'\<rangle>" "(m\<^sub>1', m\<^sub>2') \<in> S"
  using assms unfolding ev_def
proof safe
  assume "trace_mem m\<^sub>1 t m\<^sub>1'" "sec_pres c S" 
    "R,G \<turnstile> P {c} Q" "(m\<^sub>1,m\<^sub>2) \<in> S" "c \<mapsto>\<^sup>*t c\<^sub>1" "m\<^sub>1 \<in> P"
  hence "\<exists>m\<^sub>2' c\<^sub>2. (trace_mem m\<^sub>2 t m\<^sub>2' \<and> c \<mapsto>\<^sup>*t c\<^sub>2) \<and> (m\<^sub>1',m\<^sub>2') \<in> S"
  proof (induct m\<^sub>1 t m\<^sub>1' arbitrary: P m\<^sub>2 c rule: trace_mem.induct)
    case (1 m)
    then show ?case by blast
  next
    case (2 m\<^sub>1 m\<^sub>1' g t m\<^sub>1'')
    then obtain c' where itm1: "c \<mapsto>\<^sup>*[g] c'" "c' \<mapsto>\<^sup>*t c\<^sub>1" by auto
    then obtain P' \<alpha> r where itm2: "R,G \<turnstile> P' {c'} Q" "(beforeReord \<alpha> r) \<inter> basics c \<noteq> {}" 
      "g = beh \<alpha>" "P \<subseteq> wp\<^sub>\<alpha> \<alpha> P'"  using trace_rule[OF itm1(1) 2(5)] by blast
    hence itm6: "m\<^sub>1' \<in> P'" using 2(1,8) unfolding wp_def by blast                       
    then obtain m\<^sub>2' where itm3: "(m\<^sub>2,m\<^sub>2') \<in> g" "(m\<^sub>1',m\<^sub>2') \<in> S" using 2(1,4,6,8) itm2(2,3,4) 
      unfolding sec_pres_def wp_def by blast 
    hence itm4: "sec_pres c' S" 
      using 2(4) itm1 basics_gexecute unfolding sec_pres_def by (metis beforeReord.simps(3) itm2(2)) 
    hence itm5: "\<exists>m\<^sub>2'' c\<^sub>2. (trace_mem m\<^sub>2' t m\<^sub>2'' \<and> c' \<mapsto>\<^sup>*t c\<^sub>2) \<and> (m\<^sub>1'', m\<^sub>2'') \<in> S"
      using 2(3)[OF itm4 itm2(1) itm3(2) itm1(2) itm6] by blast
    then show ?case using "2.prems"(4) itm3(1) by blast
   qed
   thus ?thesis using that by (meson security.ev_def)
 qed

theorem secure_bisim:
  assumes "R,G \<turnstile> P { c } Q"
  assumes "sec_pres c S"
  shows "secure c P S"
  using bisim_exists[OF assms(2) assms(1)] unfolding secure_def by metis

end

end