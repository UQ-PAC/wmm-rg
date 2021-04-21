theory SimAsm_Rules
  imports SimAsm
begin

section \<open>Wellformedness\<close>

definition glb
  where "glb m \<equiv> \<lambda>v. m (Glb v)"

definition rg
  where "rg m \<equiv> \<lambda>v. m (Reg v)"

type_synonym ('v,'g) gstate = "'g \<Rightarrow> 'v"
type_synonym ('v,'g) grel = "('v,'g) gstate rel"
type_synonym ('v,'g,'r) trel = "('v,'g,'r) state rel"
type_synonym ('v,'g,'r) trans = "('v,'g,'r) state set \<Rightarrow> ('v,'g,'r) state set"
type_synonym ('v,'r,'a) rtrans = "('v,'r,'a) trel \<Rightarrow> ('v,'r,'a) trel"

text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step\<^sub>t :: "('v,'g) grel \<Rightarrow> ('v,'g,'r) trel"
  where "step\<^sub>t R \<equiv> {(m,m'). (glb m, glb m') \<in> R \<and> rg m = rg m'}"

text \<open>Define stability in terms of a relational predicate that preserves the thread state\<close>
abbreviation stable\<^sub>t
  where "stable\<^sub>t R P \<equiv> stable (step\<^sub>t R) P"

definition stabilize
  where "stabilize R P \<equiv> {m. \<forall>m'. (glb m,glb m') \<in> R \<longrightarrow> rg m = rg m' \<longrightarrow> m' \<in> P}"

definition reflexive
  where "reflexive R \<equiv> \<forall>m. (m,m) \<in> R"

definition transitive
  where "transitive R \<equiv> \<forall>m m' m''. (m,m') \<in> R \<longrightarrow> (m',m'') \<in> R \<longrightarrow> (m,m'') \<in> R"

text \<open>Couple all wellformedness conditions into a single definition\<close>
abbreviation wellformed :: "('v,'a) grel \<Rightarrow> ('v,'a) grel \<Rightarrow> bool"
  where "wellformed R G \<equiv> reflexive R \<and> transitive R \<and> reflexive G" 

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G"
  shows "stable\<^sub>t R (stabilize R Q)"
  unfolding stable_def step\<^sub>t_def
proof (clarsimp)
  fix m m'
  assume a: "m \<in> stabilize R Q" "(glb m, glb m') \<in> R" "rg m = rg m'"
  have "\<forall>g''. (glb m',g'') \<in> R \<longrightarrow> (glb m,g'') \<in> R"
    using assms a(2) unfolding transitive_def by blast
  thus "m' \<in> stabilize R Q" using a(1,3) by (auto simp: stabilize_def)
qed

text \<open>The conjunction of two stable predicates is stable\<close>
lemma stable\<^sub>t_conj [intro]:
  assumes "stable\<^sub>t R P" "stable\<^sub>t R Q"
  shows "stable\<^sub>t R (P \<inter> Q)"
  using assms by (auto simp: stable_def)

text \<open>Elimination rule to ignore the stabilization process\<close>
lemma stabilizeE:
  assumes "m \<in> stabilize R P"
  assumes "reflexive R"
  obtains "m \<in> P"
proof -
  have "\<forall>g. (glb m, glb g) \<in> R \<longrightarrow> rg m = rg g \<longrightarrow> g \<in> P" "(glb m, glb m) \<in>  R"
    using assms by (auto simp: reflexive_def stabilize_def)
  thus ?thesis using that by auto
qed

text \<open>Stabilization preserves entailment\<close>
lemma stabilize_entail [intro!]:
  assumes "reflexive R"
  assumes "P \<subseteq> Q"
  shows "stabilize R P \<subseteq> Q"
  using assms by (auto elim: stabilizeE)

section \<open>Predicate Transformations\<close>

named_theorems wp_defs

text \<open>Transform a predicate based on an sub-operation\<close>
fun wp\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) trans" 
  where 
    "wp\<^sub>i (assign r e) Q = {m. (m (r := ev m e)) \<in> Q}" |
    "wp\<^sub>i (cmp b) Q =  {m. ev\<^sub>B m b \<longrightarrow> m \<in> Q}" | 
    "wp\<^sub>i _ Q = Q"

definition assert
  where "assert b \<equiv> {m. b}"

text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "('v,'g) grel \<Rightarrow> ('v,'g,'r) lang \<Rightarrow> ('v,'g,'r) trans"
  where
    "wp R Skip Q = Q" |
    "wp R (Op v a) Q = stabilize R (v \<inter> wp\<^sub>i a Q)" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = (wp\<^sub>i (cmp b) (wp R c\<^sub>1 Q) \<inter> wp\<^sub>i (cmp (Neg b)) (wp R c\<^sub>2 Q))" |
    "wp R (While b I c) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp\<^sub>i (cmp b) (wp R c (stabilize R I)) \<inter> wp\<^sub>i (cmp (Neg b)) Q))"

text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "('v,'r,'a) trans \<Rightarrow> ('v,'r,'a) rtrans"
  where "wp\<^sub>r f G \<equiv> {(m,m'). m' \<in> f {m'. (m,m') \<in> G}}"
declare wp\<^sub>r_def [wp_defs]

subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar
  where "guar f G \<equiv> {m. (m,m) \<in> (wp\<^sub>r f G)}"

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c (Op v a) G = (v \<subseteq> guar (wp\<^sub>i a) G)" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If _ c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While _ _ c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c _ _ = False"

text \<open>Correctness of the guarantee check\<close>
lemma com_guar:
  "wellformed R G \<Longrightarrow> guar\<^sub>c c G \<Longrightarrow> \<forall>\<beta>\<in>basics c. guar\<^sub>\<alpha> \<beta> G"
proof (induct c)
  case (Basic x)
  then show ?case apply (cases "tag x") apply (auto simp: guar_def wp\<^sub>r_def) sorry
qed auto

end