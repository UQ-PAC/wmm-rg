theory Security
  imports Soundness
begin

locale security = rules 

type_synonym ('a,'b) Trace = "('b \<times> 'b) set list" 
type_synonym ('a,'b) LTrace = "('b set \<times> ('b \<times> 'b) set) list" 

context security
begin

inductive_set trace :: "(('a,'b) com \<times> ('a,'b) Trace \<times> ('a,'b) com) set"
  and trace_abv :: "('a,'b) com \<Rightarrow> ('a,'b) Trace \<Rightarrow> ('a,'b) com \<Rightarrow> bool" ("_ \<mapsto>\<^sup>*_ _" [50,40,40] 70)
  where
  "trace_abv P t P' \<equiv> (P, t, P') \<in> trace"
  | none[intro]: "c \<mapsto>\<^sup>*[] c" 
  | sil[intro]: "c\<^sub>1 \<leadsto> c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sup>*t c\<^sub>3"
  | gex[intro]: "c\<^sub>1 \<mapsto>[g] c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sup>*g#t c\<^sub>3"

inductive trace_mem :: "'m \<Rightarrow> 'm rel list  \<Rightarrow> 'm \<Rightarrow> bool" (*m rel = m X m set*)
  where
    [intro]: "trace_mem m [] m" |
    [intro]: "(m'', m) \<in> g \<Longrightarrow> trace_mem m t m' \<Longrightarrow> trace_mem m'' (g#t) m'"

definition ev :: "('a,'b) com \<Rightarrow> 'b \<Rightarrow> ('a,'b) Trace \<Rightarrow> ('a,'b) com \<Rightarrow> 'b \<Rightarrow> bool"
  ("\<langle>_,_\<rangle> \<rightarrow>\<^sup>*_ \<langle>_,_\<rangle>" [50,40,40] 70)
  where "\<langle>c,m\<rangle> \<rightarrow>\<^sup>*t \<langle>c',m'\<rangle> \<equiv> trace_mem m t m' \<and> c \<mapsto>\<^sup>*t c'"

text \<open> trace as list of local steps in order to collect vc + beh \<close>

inductive_set local_trace :: "(('a,'b) com \<times> ('a,'b) LTrace \<times> ('a,'b) com) set"
  and local_trace_abv :: "('a,'b) com \<Rightarrow> ('a,'b) LTrace \<Rightarrow> ('a,'b) com \<Rightarrow> bool" 
                                                                       ("_ \<mapsto>\<^sup>l\<^sup>*_ _" [50,40,40] 70)
  where
  "local_trace_abv P t P' \<equiv> (P, t, P') \<in> local_trace"
  | none[intro]: "c \<mapsto>\<^sup>l\<^sup>*[] c" 
  | sil[intro]: "c\<^sub>1 \<leadsto> c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sup>l\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sup>l\<^sup>*t c\<^sub>3"
  | gex[intro]: "c\<^sub>1 \<mapsto>[\<alpha>',r,\<alpha>] c\<^sub>2 \<Longrightarrow> c\<^sub>2 \<mapsto>\<^sup>l\<^sup>*t c\<^sub>3 \<Longrightarrow> c\<^sub>1 \<mapsto>\<^sup>l\<^sup>*(strip_tag \<alpha>')#t c\<^sub>3"


(*non-interference over all basic commands *)
definition tag_basic
  where "tag_basic a \<alpha> \<equiv>  (tag a, \<alpha>)"

definition sec_pres :: "('a,'b) com \<Rightarrow> 'b rel \<Rightarrow> bool"
  where "sec_pres c S \<equiv> \<forall>\<alpha> r m\<^sub>1 m\<^sub>2 m\<^sub>1'. (strip_tag \<alpha>) \<in> obs_basics c \<longrightarrow> 
                m\<^sub>1 \<in> (vc \<alpha>\<llangle>r\<rrangle>) \<longrightarrow> (m\<^sub>1,m\<^sub>2) \<in> S \<longrightarrow> (m\<^sub>1,m\<^sub>1') \<in> beh \<alpha>\<llangle>r\<rrangle> \<longrightarrow> 
                               (\<exists>m\<^sub>2'. (m\<^sub>2,m\<^sub>2') \<in> beh \<alpha>\<llangle>r\<rrangle> \<and> (m\<^sub>1',m\<^sub>2') \<in> S)"

(* non-interference over all traces *)

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

lemma basics_exec_step:
  assumes "c \<mapsto>[\<alpha>'',r,\<alpha>] c'" 
  shows "\<alpha> \<in> basics c"
  using assms by induct auto

(*
lemma obs_basics_silent: 
  assumes "P\<^sub>1 \<leadsto> P\<^sub>2"
  shows "obs_basics P\<^sub>1 \<supseteq> obs_basics P\<^sub>2"
  using assms basics_exec 
proof (induct)
  case (capS c c' k)
  then show ?case
    apply simp 
    by blast
next
  case (capStep c \<alpha>' r \<alpha> c' s s')
  have \<alpha>: "\<alpha>' = \<alpha>\<llangle>r\<rrangle>" using capStep lexecute_triple by auto
  hence " basics c' \<subseteq>  basics c" using capStep by auto
  hence " obs_basics c' \<subseteq>  obs_basics c" using capStep sledgehammer
  hence "\<Union> (observable ` basics c') \<subseteq> \<Union> (observable ` basics c)" 
  moreover have "\<exists>x\<in>basics c. popbasic' s s' \<alpha>' \<in> observable x"
    unfolding overapprox_def 
      
      sorry
  ultimately show ?case by simp
qed auto
*)


(*

lemma helpCap: 
  assumes  "c \<mapsto>[\<alpha>',r,\<alpha>] c'" 
  assumes  "c \<mapsto>[\<alpha>',r,\<alpha>] c' \<Longrightarrow> basics c' \<subseteq> basics c"
  shows "obs_basics (Basic (popbasic' s s' \<alpha>') \<cdot> Capture s' c') \<subseteq> obs_basics (Capture s c)" 
  using assms apply auto
proof -
  have a0:"\<exists>x\<in>obs_basics c. (poppred' s (vc \<alpha>'), poprel' s s' (beh \<alpha>')) \<in> observable x"
  

     sorry

(*
"\<exists>x\<in>obs_basics c. (poppred' s (vc \<alpha>'), poprel' s s' (beh \<alpha>')) \<in> observable x"
"\<And>a b aa ba. (aa, ba) \<in> obs_basics c' \<Longrightarrow> (a, b) \<in> observable (aa, ba) \<Longrightarrow> 
                                           \<exists>x\<in>obs_basics c. (a, b) \<in> observable x"
*)


lemma helpS: 
  assumes "s \<in> S"
  shows  "obs_basics (seq2com s) \<subseteq> (\<Union>s\<in>S. strip_tag_set (set s))"
  sorry


lemma basics_silent:
  assumes "c \<leadsto> c'"
  shows "obs_basics c \<supseteq> obs_basics c'"
  using assms basics_exec 
proof (induct)
next 
  case (bigc s S)
  then show ?case by (simp add: helpS) 
next
  case (capS c c' k)
  then show ?case apply simp by blast
next
  case (capStep c \<alpha>' r \<alpha> c' s s')
  have a0: "\<alpha>' = \<alpha>\<llangle>r\<rrangle>" using capStep lexecute_triple by auto
  hence a1: "basics c' \<subseteq>  basics c" using capStep by auto
(*  have a2: "popbasic' s s' \<alpha>' \<in> popbasic ` basics c" sorry
  have a3: "popbasic ` basics c' \<subseteq> popbasic ` basics c" sorry  *)
  show ?case using helpCap using capStep.hyps using a1 by presburger
qed auto
*)

text \<open>Identify all observable operations in a trace\<close>

definition obs_atomics :: "('a,'b) com \<Rightarrow> ('b set \<times> 'b rel) set" 
  where "obs_atomics c \<equiv> { \<alpha> | \<alpha> t c' . c \<mapsto>\<^sup>l\<^sup>*t c' \<and> \<alpha> \<in> set t }"


definition obs_atomics' :: "('a,'b) com \<Rightarrow> ('b set \<times> 'b rel) set" 
  where "obs_atomics c \<equiv> { \<alpha> | \<alpha> t c' . c \<mapsto>\<^sup>*t c' \<and> \<alpha> \<in> reorder_trace t c }"



lemma basics_silent:
  assumes "c \<leadsto> c'"
  shows "obs_atomics c \<supseteq> obs_atomics c'"  sorry



lemma obs_basics_lexec:
  assumes "lexecute c \<alpha>' r \<alpha> c'" 
  shows "obs_basics c \<supseteq> obs_basics c'"
  using assms by (induct) auto

lemma obs_basics_gex: 
  assumes "gexecute c g c'" shows "obs_basics c \<supseteq> obs_basics c'"
  using assms obs_basics_lexec by (induct) auto 


lemma trace_basics: 
  assumes "P\<^sub>1 \<mapsto>\<^sup>*t P\<^sub>2"
  shows "obs_basics P\<^sub>1 \<supseteq> obs_basics P\<^sub>2"
  using assms basics_silent obs_basics_gex by induct blast+

lemma basic_par_subset: (*Nick help with name please*)
  assumes "gexecute c g c'" 
  shows "basics c\<^sub>1 \<subseteq> basics (c\<^sub>1 || c\<^sub>2)" 
        "basics c\<^sub>2 \<subseteq> basics (c\<^sub>1 || c\<^sub>2)" 
  using assms by simp+

(* ---not used:
lemma something1: (*Nick help with name please*)
  assumes "gexecute c g c'" 
  shows "\<exists>r \<alpha>. \<alpha> \<in> basics c \<and> g = beh \<alpha>\<llangle>r\<rrangle>"
  using assms proof induct
  case (thr c r \<alpha> c')
  then show ?case using basics.simps(8) basics_lexec_prefix by blast
qed auto

lemma something2: (*Nick help with name please*)
  assumes "c \<mapsto>\<^sup>*[g] c'"
  shows "\<exists>r \<alpha>. \<alpha> \<in> basics c \<and> g = beh \<alpha>\<llangle>r\<rrangle>" 
  using assms 
proof (induct c "[g]" c')
  case (sil c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case using basics_silent by blast
next
  case (gex c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case using something1 by force
qed
*)


lemma trace_rule_nil: 
  assumes "c \<mapsto>\<^sup>*[] c'"
  assumes "R,G \<turnstile> P {c} Q"
  shows "R,G \<turnstile> P {c'} Q"
  using assms by (induct c "[] :: ('a,'b) Trace" c') blast+

lemma trace_rule: 
  assumes "c \<mapsto>\<^sup>*[g] c'"
  assumes "R,G \<turnstile> P {c} Q"
  shows "\<exists>\<alpha> r M. (strip_tag \<alpha>) \<in> obs_basics c \<and> g = beh \<alpha>\<llangle>r\<rrangle> \<and> P \<subseteq> wp\<^sub>\<alpha> \<alpha>\<llangle>r\<rrangle> M \<and> guar\<^sub>\<alpha> \<alpha>\<llangle>r\<rrangle>  G \<and> R,G \<turnstile> M {c'} Q"
  using assms 
proof (induct c "[g]" c' arbitrary: P) 
  case (sil c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case using basics_silent rewrite_ruleI
    by (metis (no_types, hide_lams) insert_subset subsetI subset_antisym)
next
  case (gex c\<^sub>1 c\<^sub>2 c\<^sub>3)
  then show ?case using trace_rule_nil gexecute_ruleI[OF gex(3,1)] sorry (*by fast *) 
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
    then obtain P' r \<alpha> where itm2: "R,G \<turnstile> P' {c'} Q" "(strip_tag \<alpha>) \<in> obs_basics c" 
      "g = beh \<alpha>\<llangle>r\<rrangle>" "P \<subseteq> wp\<^sub>\<alpha> \<alpha>\<llangle>r\<rrangle> P'"  using trace_rule[OF itm1(1) 2(5)] by blast
    hence itm6: "m\<^sub>1' \<in> P'" using 2(1,8) unfolding wp_def by blast                       
    then obtain m\<^sub>2' where itm3: "(m\<^sub>2,m\<^sub>2') \<in> g" "(m\<^sub>1',m\<^sub>2') \<in> S" using 2(1,4,6,8) itm2(2,3,4) 
      unfolding sec_pres_def wp_def by blast 
    hence itm4: "sec_pres c' S" 
      using 2(4) itm1 trace_basics unfolding sec_pres_def by blast 
    hence itm5: "\<exists>m\<^sub>2'' c\<^sub>2. (trace_mem m\<^sub>2' t m\<^sub>2'' \<and> c' \<mapsto>\<^sup>*t c\<^sub>2) \<and> (m\<^sub>1'', m\<^sub>2'') \<in> S"
      using 2(3)[OF itm4 itm2(1) itm3(2) itm1(2) itm6] by blast
    then show ?case using "2.prems"(4) itm3(1) by blast
   qed
   thus ?thesis using that by (meson security.ev_def security_axioms) (*Could it be nicer?*)
 qed

theorem secure_bisim:
  assumes "R,G \<turnstile> P { c } Q"
  assumes "sec_pres c S"
  shows "secure c P S"
  using bisim_exists[OF assms(2) assms(1)] unfolding secure_def by metis

end

end