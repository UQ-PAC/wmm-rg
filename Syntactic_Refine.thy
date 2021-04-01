theory Syntactic_Refine
  imports Semantics
begin

text \<open>
Needed some concepts to modify the basic actions in a program.
Series of definitions to compare two programs, mostly to eliminate references to auxiliary state
or 'refine' by relating the behaviours of the basic actions.
\<close>

fun seq_rel
  where 
    "seq_rel T [] [] = True" |
    "seq_rel T (\<alpha>#t) (\<beta>#s) = (T \<alpha> \<beta> \<and> seq_rel T t s)" |
    "seq_rel T _ _ = False"

definition seq_set_rel
  where "seq_set_rel T S S' \<equiv> (\<forall>s' \<in> S'. \<exists>s \<in> S. seq_rel T s s')"

inductive syntax_rel
  where
    "syntax_rel I T Nil Nil" |
    "T \<alpha> \<beta> \<Longrightarrow> syntax_rel I T (Basic \<alpha>) (Basic \<beta>)" |
    "syntax_rel I T c\<^sub>1 c\<^sub>1' \<Longrightarrow> syntax_rel I T c\<^sub>2 c\<^sub>2' \<Longrightarrow> syntax_rel I T (Seq c\<^sub>1 c\<^sub>2) (Seq c\<^sub>1' c\<^sub>2')" |
    "syntax_rel I T c\<^sub>1 c\<^sub>1' \<Longrightarrow> syntax_rel I T c\<^sub>2 c\<^sub>2' \<Longrightarrow> syntax_rel I T (Ord c\<^sub>1 c\<^sub>2) (Ord c\<^sub>1' c\<^sub>2')" |
    "syntax_rel I T c\<^sub>1 c\<^sub>1' \<Longrightarrow> syntax_rel I T c\<^sub>2 c\<^sub>2' \<Longrightarrow> syntax_rel I T (Choice c\<^sub>1 c\<^sub>2) (Choice c\<^sub>1' c\<^sub>2')" |
    "syntax_rel I T c\<^sub>1 c\<^sub>1' \<Longrightarrow> syntax_rel I T c\<^sub>2 c\<^sub>2' \<Longrightarrow> syntax_rel I T (Parallel c\<^sub>1 c\<^sub>2) (Parallel c\<^sub>1' c\<^sub>2')" |
    "syntax_rel I T c c' \<Longrightarrow> syntax_rel I T (Loop c) (Loop c')" |
    "I op \<Longrightarrow> syntax_rel I T c c' \<Longrightarrow> syntax_rel I T (Thread op c) (Thread op c')" |
    "I op \<Longrightarrow> syntax_rel I T c c' \<Longrightarrow> syntax_rel I T (State l op c) (State l op c')" |
    "seq_set_rel T S S' \<Longrightarrow> syntax_rel I T (SeqChoice S) (SeqChoice S')"

inductive_cases syntax_relE[elim]: "syntax_rel I T c c'"
declare syntax_rel.intros [intro]

lemma [elim!]:
  assumes "syntax_rel I T  c (c\<^sub>1 ; c\<^sub>2)"
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' ; c\<^sub>2'" "syntax_rel I T  c\<^sub>1' c\<^sub>1" "syntax_rel I T  c\<^sub>2' c\<^sub>2"
  using assms by (cases rule: syntax_relE, blast, auto)

lemma [elim!]:
  assumes "syntax_rel I T  c (c\<^sub>1 \<cdot> c\<^sub>2)"
  obtains c\<^sub>1' c\<^sub>2' where "c = c\<^sub>1' \<cdot> c\<^sub>2'" "syntax_rel I T  c\<^sub>1' c\<^sub>1" "syntax_rel I T  c\<^sub>2' c\<^sub>2"
  using assms by (cases rule: syntax_relE, blast, auto)

lemma seq_rel [intro]:
  assumes "seq_rel T s s'"
  shows "syntax_rel I T (seq2com s) (seq2com s')"
  using assms by (induct T s s' rule: seq_rel.induct) auto

lemma wp_conseqI:
  assumes "P \<subseteq> wp v b Q" "b' \<subseteq> b" "v \<subseteq> v'" 
  shows "P \<subseteq> wp v' b' Q"
  using assms by (auto simp: wp_def) blast

lemma guar_conseqI:
  assumes "guar v b G" "b' \<subseteq> b"
  shows "guar v b' G"
  using assms by (auto simp: guar_def)

context semantics
begin

definition refine\<^sub>\<alpha>
  where "refine\<^sub>\<alpha> \<alpha> \<beta> \<equiv> tag \<alpha> = tag \<beta> \<and> vc \<alpha> = vc \<beta> \<and> (\<forall>r. beh \<alpha>\<llangle>r\<rrangle> \<supseteq> beh \<beta>\<llangle>r\<rrangle>)"

definition refine\<^sub>I
  where "refine\<^sub>I x = True"

abbreviation refine
  where "refine c\<^sub>1 c\<^sub>2 \<equiv> syntax_rel refine\<^sub>I refine\<^sub>\<alpha> c\<^sub>1 c\<^sub>2"

definition aux\<^sub>\<alpha>
  where "aux\<^sub>\<alpha> r \<alpha> \<beta> \<equiv> tag \<alpha> = tag \<beta> \<and> aux\<^sub>P r (vc \<alpha>) = vc \<beta> \<and> (\<forall>c. aux\<^sub>R r (beh \<alpha>\<llangle>c\<rrangle>) \<supseteq> beh \<beta>\<llangle>c\<rrangle>)"

definition aux\<^sub>I
  where "aux\<^sub>I r op \<equiv> (\<forall>a l n l'. ((op a l, op n l') \<in> r\<^sup>=) = ((a,n) \<in> r\<^sup>= \<and> (l,l') \<in> r\<^sup>=)) \<and> 
                     (\<forall>m l n. (op m l,n) \<in> r\<^sup>= \<longrightarrow> n = op n l)"

abbreviation aux\<^sub>C
  where "aux\<^sub>C r c\<^sub>1 c\<^sub>2 \<equiv> syntax_rel (aux\<^sub>I r) (aux\<^sub>\<alpha> r) c\<^sub>1 c\<^sub>2"

lemma atomic_refineI:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "refine\<^sub>\<alpha> \<alpha> \<beta>"
  shows "R,G \<turnstile>\<^sub>A P {\<beta>} Q"
  using assms unfolding atomic_rule_def refine\<^sub>\<alpha>_def wp_def guar_def
  apply (intro conjI)
  prefer 3
  apply simp
  prefer 3
  apply simp
  apply (subgoal_tac "beh \<beta>\<llangle>Nil\<rrangle> \<subseteq> beh \<alpha>\<llangle>Nil\<rrangle>")
  apply auto[1]
  apply blast
  apply (subgoal_tac "beh \<beta>\<llangle>Nil\<rrangle> \<subseteq> beh \<alpha>\<llangle>Nil\<rrangle>")
  apply auto[1]
  by blast

lemma atomic_auxI:
  assumes "R,G \<turnstile>\<^sub>A P {\<alpha>} Q" "aux\<^sub>\<alpha> r \<alpha> \<beta>"
  shows "aux\<^sub>R r R,aux\<^sub>G r G \<turnstile>\<^sub>A aux\<^sub>P r P {\<beta>} aux\<^sub>P r Q"
  using assms unfolding atomic_rule_def aux\<^sub>\<alpha>_def
  apply (subgoal_tac "beh \<beta>\<llangle>Nil\<rrangle> \<subseteq> aux\<^sub>R r (beh \<alpha>\<llangle>Nil\<rrangle>)")
  defer 1
  apply blast
  apply (intro conjI)
  apply (subgoal_tac "aux\<^sub>P r P \<subseteq> wp (aux\<^sub>P r (vc \<alpha>)) (aux\<^sub>R r (beh \<alpha>)) (aux\<^sub>P r Q)")
  defer 1
  using aux_wp apply blast
  prefer 4
  apply (rule wp_conseqI)
  apply blast
  apply auto[1]
  apply blast
  apply (subgoal_tac "guar (aux\<^sub>P r (vc \<alpha>)) (aux\<^sub>R r (beh \<alpha>)) (aux\<^sub>G r G)")
  defer 1
  using aux_guar apply blast
  prefer 3
  apply (rule guar_conseqI)
  apply auto[2]
  using aux_stable apply blast
  using aux_stable by blast

lemma syntax_rel_silent:
  assumes "syntax_rel I T c\<^sub>1 c\<^sub>2" "c\<^sub>2 \<leadsto> c\<^sub>2'"
  shows "\<exists>c\<^sub>1'. c\<^sub>1 \<leadsto> c\<^sub>1' \<and> syntax_rel I T c\<^sub>1' c\<^sub>2'"
  using assms(2,1)
proof (induct arbitrary: c\<^sub>1)
  case (bigc s S)
  then show ?case by (cases rule: syntax_relE, blast) (auto simp: seq_set_rel_def)
qed (cases rule: syntax_relE, blast, auto; force)+

lemma syntax_rel_re:
  assumes "\<alpha>' < r <\<^sub>c \<alpha>" "syntax_rel I T r' r" "tag \<alpha> = tag \<beta>" "\<forall>\<alpha> \<beta>. T \<alpha> \<beta> \<longrightarrow> tag \<alpha> = tag \<beta>"
  shows "\<exists>\<beta>'. \<beta>' < r' <\<^sub>c \<beta> \<and> tag \<alpha>' = tag \<beta>'"
  using assms(1,2,3)
proof (induct \<alpha>' r \<alpha> arbitrary: r' \<beta> rule: reorder_com.induct)
  case (1 \<alpha>' \<alpha>)
  then show ?case by fastforce
next
  case (2 \<alpha>' \<beta>' \<alpha>)
  then show ?case
    apply (cases rule: syntax_relE, blast; simp)
    using assms(4) tag_fwd by (intro conjI) metis+
next
  case (3 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then show ?case by clarsimp (metis eq_fst_iff)
next
  case (4 \<alpha>' c\<^sub>1 c\<^sub>2 \<alpha>)
  then show ?case by clarsimp (metis eq_fst_iff)
qed auto

lemma syntax_rel_local:
  assumes "syntax_rel I T c\<^sub>1 c\<^sub>2" "c\<^sub>2 \<mapsto>[r,\<alpha>] c\<^sub>2'" "\<forall>\<alpha> \<beta>. T \<alpha> \<beta> \<longrightarrow> tag \<alpha> = tag \<beta>"
  shows "\<exists>c\<^sub>1' r' \<beta>. c\<^sub>1 \<mapsto>[r',\<beta>] c\<^sub>1' \<and> syntax_rel I T c\<^sub>1' c\<^sub>2' \<and> syntax_rel I T r' r \<and> T \<beta> \<alpha>"
  using assms(2,1)
proof (induct arbitrary: c\<^sub>1)
  case (ooo c\<^sub>1'' r \<alpha> c\<^sub>1' \<alpha>' c\<^sub>2)
  then obtain c\<^sub>3 c\<^sub>4 where c: "c\<^sub>1 = c\<^sub>3 ; c\<^sub>4" "syntax_rel I T c\<^sub>3 c\<^sub>2" "syntax_rel I T c\<^sub>4 c\<^sub>1''"
    by auto
  then obtain c\<^sub>5 r' \<beta> where b: "c\<^sub>4 \<mapsto>[r',\<beta>] c\<^sub>5" "syntax_rel I T c\<^sub>5 c\<^sub>1'" "T \<beta> \<alpha>" "syntax_rel I T r' r"
    using ooo(2) by blast
  hence "syntax_rel I T (c\<^sub>3 ; c\<^sub>5) (c\<^sub>2 ; c\<^sub>1')" using c(2) by auto
  moreover have r: "syntax_rel I T (c\<^sub>3; r') (c\<^sub>2 ; r)" using b c by auto 
  moreover have "c\<^sub>1 \<mapsto>[c\<^sub>3 ; r',\<beta>] c\<^sub>3 ; c\<^sub>5"
  proof -
    have d: "tag \<alpha> = tag \<beta>" using b(3) assms(3) by metis
    obtain \<beta>' where d: "\<beta>' < c\<^sub>3 ; r' <\<^sub>c \<beta>"
      using syntax_rel_re[OF ooo(3) calculation(2) d assms(3)]
      by force
    show ?thesis unfolding c(1) using b(1) d by (rule lexecute.ooo)
  qed    
  ultimately show ?case using b(3) by metis
qed (cases rule: syntax_relE, blast; simp; fast)+

lemma ref_tag:
  "\<forall>\<alpha> \<beta>. refine\<^sub>\<alpha> \<alpha> \<beta> \<longrightarrow> tag \<alpha> = tag \<beta>"
  by (auto simp: refine\<^sub>\<alpha>_def)

lemma aux_tag:
  "\<forall>\<alpha> \<beta>. aux\<^sub>\<alpha> r \<alpha> \<beta> \<longrightarrow> tag \<alpha> = tag \<beta>"
  by (auto simp: aux\<^sub>\<alpha>_def)

lemma refine_fwd [simp]:
  "refine r' r \<Longrightarrow> \<beta>\<llangle>r'\<rrangle> = \<beta>\<llangle>r\<rrangle>"
proof (induct "refine\<^sub>I :: 'b merge \<Rightarrow> bool" refine\<^sub>\<alpha> r' r arbitrary: \<beta> rule: syntax_rel.induct)
  case (2 \<alpha> \<beta>)
  then show ?case by (auto simp: refine\<^sub>\<alpha>_def)
qed auto

lemma aux_fwd [simp]:
  "aux\<^sub>C a r' r \<Longrightarrow> \<beta>\<llangle>r'\<rrangle> = \<beta>\<llangle>r\<rrangle>"
proof (induct "aux\<^sub>I a" "aux\<^sub>\<alpha> a" r' r arbitrary: \<beta> rule: syntax_rel.induct)
  case (2 \<alpha> \<beta>)
  then show ?case by (auto simp: aux\<^sub>\<alpha>_def)
qed auto

lemma refine_global:
  assumes "refine c\<^sub>1 c\<^sub>2" "c\<^sub>2 \<mapsto>[g] c\<^sub>2'"
  shows "\<exists>c\<^sub>1' g'. g' \<supseteq> g \<and> c\<^sub>1 \<mapsto>[g'] c\<^sub>1' \<and> refine c\<^sub>1' c\<^sub>2'"
  using assms(2,1)
proof (induct arbitrary: c\<^sub>1)
  case (thr c r \<alpha> c' l op l')
  then obtain c\<^sub>2 where c: "c\<^sub>1 = State l op c\<^sub>2" "refine c\<^sub>2 c" by auto
  obtain c\<^sub>2' r' \<beta> where b: "c\<^sub>2 \<mapsto>[r',\<beta>] c\<^sub>2'" "refine c\<^sub>2' c'" "refine\<^sub>\<alpha> \<beta> \<alpha>" "refine r' r"
    using syntax_rel_local[OF c(2) thr(1) ref_tag] by auto
  hence d: "beh \<beta>\<llangle>r'\<rrangle> \<supseteq> beh \<alpha>\<llangle>r\<rrangle>" by (auto simp: refine\<^sub>\<alpha>_def)
  hence "(thr2glb op l l' (beh \<beta>\<llangle>r'\<rrangle>)) \<supseteq> thr2glb op l l' (beh \<alpha>\<llangle>r\<rrangle>)"
    using d unfolding thr2glb_def by blast
  moreover have "refine (State l' op c\<^sub>2') (State l' op c')"
    using b(2) by (auto simp: refine\<^sub>I_def)
  moreover have "c\<^sub>1 \<mapsto>[thr2glb op l l' (beh \<beta>\<llangle>r'\<rrangle>)] State l' op c\<^sub>2'" 
    unfolding c(1) using b(1) by auto
  ultimately show ?case by metis
next
  case (par1 c\<^sub>3 g c\<^sub>1' c\<^sub>2)
  then show ?case by (cases rule: syntax_relE, blast; simp) (meson gexecute.par1 syntax_rel.intros(6))
next
  case (par2 c\<^sub>2 g c\<^sub>2' c\<^sub>1)
  then show ?case by (cases rule: syntax_relE, blast; simp) (meson gexecute.par2 syntax_rel.intros(6))
qed

lemma aux_thr2glb:
  assumes "P \<subseteq> aux\<^sub>R r Q" "aux\<^sub>I r op"
  shows "thr2glb op l l' P \<subseteq> aux\<^sub>R r (thr2glb op l l' Q)"
  unfolding thr2glb_def aux\<^sub>R_def
proof (clarify, goal_cases)
  case (1 m m' n)
  hence "\<forall>n''. (op m l, n'') \<in> r\<^sup>= \<longrightarrow> (\<exists>n'. (op m' l', n') \<in> r\<^sup>= \<and> (n'', n') \<in> Q)"
    using assms(1) unfolding aux\<^sub>R_def by auto
  moreover have "(op m l, op n l) \<in> r\<^sup>=" using assms(2) 1(2) unfolding aux\<^sub>I_def by blast
  ultimately obtain n' where n: "(op m' l', n') \<in> r\<^sup>=" "(op n l, n') \<in> Q" by auto
  hence "n' = op n' l'" using assms(2) unfolding aux\<^sub>I_def by blast
  hence m: "(op m' l', op n' l') \<in> r\<^sup>="  "(op n l, op n' l') \<in> Q" using n by auto
  hence "( m' ,  n' ) \<in> r\<^sup>=" using assms(2) unfolding aux\<^sub>I_def by blast
  then show ?case using m(2) by blast
qed

lemma aux_global:
  assumes "aux\<^sub>C r c\<^sub>1 c\<^sub>2" "c\<^sub>2 \<mapsto>[g] c\<^sub>2'"
  shows "\<exists>c\<^sub>1' g'. aux\<^sub>R r g' \<supseteq> g \<and> c\<^sub>1 \<mapsto>[g'] c\<^sub>1' \<and> aux\<^sub>C r c\<^sub>1' c\<^sub>2'"
  using assms(2,1)
proof (induct arbitrary: c\<^sub>1)
  case (thr c r' \<alpha> c' l op l')
  then obtain c\<^sub>2 where c: "c\<^sub>1 = State l op c\<^sub>2" "aux\<^sub>C r c\<^sub>2 c" "aux\<^sub>I r op" by auto
  obtain c\<^sub>2' r'' \<beta> where b: "c\<^sub>2 \<mapsto>[r'',\<beta>] c\<^sub>2'" "aux\<^sub>C r c\<^sub>2' c'" "aux\<^sub>\<alpha> r \<beta> \<alpha>" "aux\<^sub>C r r'' r'"
    using syntax_rel_local[OF c(2) thr(1) aux_tag] by auto
  hence d: "aux\<^sub>R r (beh \<beta>\<llangle>r''\<rrangle>) \<supseteq> beh \<alpha>\<llangle>r'\<rrangle>" by (auto simp: aux\<^sub>\<alpha>_def)
  hence "aux\<^sub>R r (thr2glb op l l' (beh \<beta>\<llangle>r''\<rrangle>)) \<supseteq> thr2glb op l l' (beh \<alpha>\<llangle>r'\<rrangle>)"
    using c(3) aux_thr2glb by metis
  moreover have "aux\<^sub>C r (State l' op c\<^sub>2') (State l' op c')"
    using b(2) c(3) by auto
  moreover have "c\<^sub>1 \<mapsto>[thr2glb op l l' (beh \<beta>\<llangle>r''\<rrangle>)] State l' op c\<^sub>2'" 
    unfolding c(1) using b(1) by auto
  ultimately show ?case by metis
next
  case (par1 c\<^sub>3 g c\<^sub>1' c\<^sub>2)
  then show ?case by (cases rule: syntax_relE, blast; simp) (meson gexecute.par1 syntax_rel.intros(6))
next
  case (par2 c\<^sub>2 g c\<^sub>2' c\<^sub>1)
  then show ?case by (cases rule: syntax_relE, blast; simp) (meson gexecute.par2 syntax_rel.intros(6))
qed

end

end