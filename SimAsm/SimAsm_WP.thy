theory SimAsm_WP
  imports SimAsm
begin

section \<open>Wellformedness\<close>

definition stabilize
  where "stabilize R P \<equiv> {m. \<forall>m'. (glb m,glb m') \<in> R \<longrightarrow> rg m = rg m' \<longrightarrow> m' \<in> P}"

definition reflexive
  where "reflexive R \<equiv> \<forall>m. (m,m) \<in> R"

definition transitive
  where "transitive R \<equiv> \<forall>m m' m''. (m,m') \<in> R \<longrightarrow> (m',m'') \<in> R \<longrightarrow> (m,m'') \<in> R"

definition assert
  where "assert b \<equiv> {m. b}"

text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step\<^sub>t :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) trel"
  where "step\<^sub>t R \<equiv> {(m,m'). (glb m, glb m') \<in> R \<and> rg m = rg m'}"

text \<open>Lift a relational predicate\<close>
definition step :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) trel"
  where "step R \<equiv> {(m,m'). (glb m, glb m') \<in> R}"

text \<open>Define stability in terms of a relational predicate that preserves the thread state\<close>
abbreviation stable\<^sub>t
  where "stable\<^sub>t R P \<equiv> stable (step\<^sub>t R) P"

text \<open>Couple all wellformedness conditions into a single definition\<close>
abbreviation wellformed :: "('v,'g,'a) grel \<Rightarrow> ('v,'g,'a) grel \<Rightarrow> bool"
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
lemma stabilize_entail :
  assumes "m \<in> stabilize R P" 
  assumes "reflexive R"
  assumes "P \<subseteq> Q"
  shows "m \<in> stabilize R Q"
  using assms by (auto simp: stabilize_def)

section \<open>Predicate Transformations\<close>

text \<open>Transform a predicate based on an sub-operation\<close>
fun wp\<^sub>i :: "('v::truth,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) trans" 
  where 
    "wp\<^sub>i (assign r e) Q = {m. (m (r :=\<^sub>s eval m e)) \<in> Q}" |
    "wp\<^sub>i (cmp b) Q =  {m. holds (eval m b) \<longrightarrow> m \<in> Q}" | 
    "wp\<^sub>i _ Q = Q"

text \<open>Transform a predicate based on an auxiliary state update\<close>
fun wp\<^sub>a :: "('v,'g,'r,'a) auxfn \<Rightarrow> ('v,'g,'r,'a) trans"
  where "wp\<^sub>a a Q = {m. m(aux: a) \<in> Q}"

text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "('v::truth,'g,'a) grel \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) trans"
  where
    "wp R Skip Q = Q" |
    "wp R (Op v a f) Q = stabilize R (v \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2) Q = stabilize R (wp\<^sub>i (cmp b) (wp R c\<^sub>1 Q) \<inter> wp\<^sub>i (ncmp b) (wp R c\<^sub>2 Q))" |
    "wp R (While b I c) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp\<^sub>i (cmp b) (wp R c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" |
    "wp R (DoWhile I c b) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp R c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"

text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "('v,'g,'r,'a) trans \<Rightarrow> ('v,'g,'r,'a) rtrans"
  where "wp\<^sub>r f G \<equiv> {(m,m'). m' \<in> f {m'. (m,m') \<in> G}}"

subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar
  where "guar f G \<equiv> {m. (m,m) \<in> (wp\<^sub>r f G)}"

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c Skip G = True" |
    "guar\<^sub>c (Op v a f) G = (v \<subseteq> guar (wp\<^sub>i a o wp\<^sub>a f) (step G))" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If _ c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (While _ _ c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c (DoWhile _ c _) G = (guar\<^sub>c c G)"

section \<open>Locale Interpretation\<close>

definition reorder_inst :: "('v::truth,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) opbasic \<Rightarrow> bool"
  where "reorder_inst a b c \<equiv> (a = fwd\<^sub>s c (fst b) \<and> re\<^sub>a (fst b) (fst a))"

abbreviation Seqw (infixr ";;" 80)
  where "Seqw c c' \<equiv> com.Seq c reorder_inst c'"

abbreviation Iterw ("_*" [90] 90)
  where "Iterw c \<equiv> com.Loop c reorder_inst"

text \<open>Convert the language into the abstract language expected by the underlying logic\<close> 
fun lift\<^sub>c :: "('v::truth,'g,'r,'a) lang \<Rightarrow> (('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) com"
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Op v a f) = Basic (\<lfloor>v,a,f\<rfloor>)" |
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) = lift\<^sub>c c\<^sub>1 ;; lift\<^sub>c c\<^sub>2" |
    "lift\<^sub>c (If b c\<^sub>1 c\<^sub>2) = 
       Choice (\<lambda>s. if holds (eval s b) then Basic (\<lfloor>cmp b\<rfloor>) ;; lift\<^sub>c c\<^sub>1
                   else Basic (\<lfloor>ncmp b\<rfloor>) ;; lift\<^sub>c c\<^sub>2)" |
    "lift\<^sub>c (While b I c) = (Basic (\<lfloor>cmp b\<rfloor>)  ;; lift\<^sub>c c)* ;; Basic (\<lfloor>ncmp b\<rfloor>)" | 
    "lift\<^sub>c (DoWhile I c b) = (lift\<^sub>c c ;; Basic (\<lfloor>cmp b\<rfloor>))* ;; lift\<^sub>c c ;; Basic (\<lfloor>ncmp b\<rfloor>)" 

interpretation rules by (unfold_locales)

text \<open>Extract the instruction from an abstract operation\<close>
abbreviation inst :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r) op"
  where "inst a \<equiv> fst (tag a)"

abbreviation aux :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) auxfn"
  where "aux a \<equiv> snd (tag a)"

definition wfbasic :: "('v::truth,'g,'r,'a) opbasic \<Rightarrow> bool"
  where "wfbasic \<beta> \<equiv> beh \<beta> = beh\<^sub>a (inst \<beta>, aux \<beta>)"

lemma opbasicE:
  obtains (assign) x e f v b where  "(basic ) = ((assign x e,f), v, b)" |
          (cmp) g f v b where "(basic ) = ((cmp g,f), v, b)" |
          (fence) f v b where "(basic ) = ((full_fence,f), v, b)" |
          (nop) f v b where "(basic ) = ((nop,f), v, b)" 
  by (cases basic, case_tac a, case_tac aa; clarsimp)

lemma [simp]:
  "wr (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = wr (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)

lemma [simp]:
  "barriers (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = barriers (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)

lemma [simp]:
  "rd (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = (if wr (inst \<beta>) \<inter> rd (inst \<alpha>) \<noteq> {} then rd (inst \<alpha>) - wr (inst \<beta>) \<union> rd (inst \<beta>) else rd (inst \<alpha>))"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto)

lemma vc_fwd\<^sub>s[simp]:
  "vc (fwd\<^sub>s \<alpha> \<beta>) = vc \<alpha>"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma beh_fwd\<^sub>s [simp]:
  "beh (fwd\<^sub>s \<alpha> \<beta>) = ( beh\<^sub>a (fwd\<^sub>i (inst \<alpha>) (fst \<beta>), (aux \<alpha>)) )"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: wfbasic_def Let_def split: if_splits)

lemma aux_fwd\<^sub>s [simp]:
  "aux (fwd\<^sub>s \<alpha> \<beta>) = aux \<alpha>"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma inst_fwd\<^sub>s [simp]:
  "inst (fwd\<^sub>s \<alpha> (assign x e, f)) = subst\<^sub>i (inst \<alpha>) x e"
  by (cases \<alpha> rule: opbasicE; auto simp: Let_def split: if_splits)

text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

end