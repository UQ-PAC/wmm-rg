theory SimAsm_WP
  imports SimAsm
begin

section \<open>Wellformedness\<close>

definition stabilize
  where "stabilize R P \<equiv> {m. \<forall>m'. (glb\<^sub>tTree m,glb\<^sub>tTree m') \<in> R \<longrightarrow> rg\<^sub>t m = rg\<^sub>t m' \<longrightarrow> m' \<in> P}"

definition reflexive
  where "reflexive R \<equiv> \<forall>m. (m,m) \<in> R"

definition transitive
  where "transitive R \<equiv> \<forall>m m' m''. (m,m') \<in> R \<longrightarrow> (m',m'') \<in> R \<longrightarrow> (m,m'') \<in> R"

definition assert
  where "assert b \<equiv> {m. b}"


text \<open>Lift a relational predicate\<close>
definition step :: "('v,'g,'a) grelTree \<Rightarrow> ('v,'g,'r,'a) trelTree"
  where "step R \<equiv> {(t,t'). (glb\<^sub>tTree t, glb\<^sub>tTree t') \<in> R}"


text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step\<^sub>t :: "('v,'g,'a) grelTree \<Rightarrow> ('v,'g,'r,'a) trelTree"
  where "step\<^sub>t R \<equiv> {(t,t'). (glb\<^sub>tTree t, glb\<^sub>tTree t') \<in> R \<and> rg\<^sub>t t = rg\<^sub>t t'}"


text \<open>Define stability in terms of a relational predicate that preserves the thread state\<close>
abbreviation stable\<^sub>t
  where "stable\<^sub>t R P \<equiv> stable (step\<^sub>t R) P"

text \<open>Couple all wellformedness conditions into a single definition\<close>
abbreviation wellformed :: "('v,'g,'a) grelTree \<Rightarrow> ('v,'g,'a) grelTree \<Rightarrow> bool"
  where "wellformed R G \<equiv> reflexive R \<and> transitive R \<and> reflexive G" 

text \<open>Show that a stabilized predicate is stable\<close>
lemma stabilize_stable [intro]:
  assumes wf: "wellformed R G"
  shows "stable\<^sub>t R (stabilize R Q)"
  unfolding stable_def step\<^sub>t_def
proof (clarsimp)
  fix m m'
  assume a: "m \<in> stabilize R Q" "(glb\<^sub>tTree m, glb\<^sub>tTree m') \<in> R" "rg\<^sub>t m = rg\<^sub>t m'"
  have "\<forall>g''. (glb\<^sub>tTree m',g'') \<in> R \<longrightarrow> (glb\<^sub>tTree m,g'') \<in> R"
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
  assumes "t \<in> stabilize R P"
  assumes "reflexive R"
  obtains "t \<in> P"
proof -
  have "\<forall>g. (glb\<^sub>tTree t, glb\<^sub>tTree g) \<in> R \<longrightarrow> rg\<^sub>t t = rg\<^sub>t g \<longrightarrow> g \<in> P" 
       "(glb\<^sub>tTree t, glb\<^sub>tTree t) \<in>  R"
    using assms by (auto simp: reflexive_def stabilize_def)
  thus ?thesis using that by auto
qed

text \<open>Stabilization preserves entailment\<close>
lemma stabilize_entail :
  assumes "t \<in> stabilize R P" 
  assumes "reflexive R"
  assumes "P \<subseteq> Q"
  shows "t \<in> stabilize R Q"
  using assms by (auto simp: stabilize_def)



section \<open>Predicate Transformations\<close>

(* define (spec c) = \<triangle>(Capture s c) *)

(* define wp\<^sub>i(spec c)Q *)
text \<open>Transform a predicate based on an sub-operation\<close>
fun wp\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) transTree" 
  where 
    "wp\<^sub>i (assign r e) Q = {t. (t (r :=\<^sub>t ev\<^sub>E t e)) \<in> Q}" |
    "wp\<^sub>i (cmp b) Q =  {t. ev\<^sub>B t b \<longrightarrow> t \<in> Q}" | 
    "wp\<^sub>i (leak c e) Q = {t. (t (c :=\<^sub>b ev\<^sub>E t e)) \<in> Q}" |
    "wp\<^sub>i _ Q = Q"

text \<open>Transform a predicate based on an auxiliary state update\<close>
fun wp\<^sub>a :: "('v,'g,'r,'a) auxfn \<Rightarrow> ('v,'g,'r,'a) transTree"
  where "wp\<^sub>a a Q = {t. t(aux\<^sub>t: a) \<in> Q}"


fun wp\<^sub>i\<^sub>s :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) transTree"
  where 
    "wp\<^sub>i\<^sub>s (leak c e) Q = {t. (t (c :=\<^sub>b ev\<^sub>E t e)) \<in> Q}" |
    "wp\<^sub>i\<^sub>s full_fence Q = UNIV"  |
    "wp\<^sub>i\<^sub>s c Q = wp\<^sub>i c Q"

fun wp\<^sub>s :: "('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) transTree"
  where 
    "wp\<^sub>s (Seq c\<^sub>1 c\<^sub>2) Q = wp\<^sub>s R c\<^sub>1 (wp\<^sub>s R c\<^sub>2 Q)" |
    "wp\<^sub>s R (If b c\<^sub>1 c\<^sub>2 c\<^sub>3) Q = 


fun po :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) predTree"
  where
    "po (assign r e) = UNIV"




(* extend wp R (If...)Q by adding wp\<^sub>i (spec c\<^sub>1; c\<^sub>3) Q *)
text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "('v,'g,'a) grelTree \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) transTree"
  where
    "wp R Skip Q = Q" |
    "wp R (Op (po a) a f) Q = stabilize R ((po a) \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
(*    "wp R (If b c\<^sub>1 c\<^sub>2 c\<^sub>3) Q = stabilize R (wp\<^sub>i (cmp b) (wp R c\<^sub>1 Q) \<inter> wp\<^sub>i (ncmp b) (wp R c\<^sub>2 Q))"|*) 
    "wp R (If b c\<^sub>1 c\<^sub>2 c\<^sub>3) Q = 
                 (merge (wp\<^sub>s c\<^sub>2 (wp R c\<^sub>3 Q)) (stabilize R (wp\<^sub>i (cmp b) (wp R c\<^sub>1 (wp R c\<^sub>3 Q)))))
                \<inter> (merge (wp\<^sub>s c\<^sub>1 (wp R c\<^sub>3 Q))   (stabilize R (wp\<^sub>i (ncmp b) (wp R c\<^sub>2 (wp R c\<^sub>3 Q)))))" |
    "wp R (While b I c) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp\<^sub>i (cmp b) (wp R c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" |
    "wp R (DoWhile I c b) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp R c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"

text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "('v,'g,'r,'a) transTree \<Rightarrow> ('v,'g,'r,'a) rtransTree"
  where "wp\<^sub>r f G \<equiv> {(t,t'). t' \<in> f {t'. (t,t') \<in> G}}"

subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar
  where "guar f G \<equiv> {t. (t,t) \<in> (wp\<^sub>r f G)}"

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

definition w 
  where "w \<alpha>' \<beta> \<alpha> \<equiv> (re\<^sub>s \<beta> \<alpha> \<and> (\<alpha>'=fwd\<^sub>s \<alpha> (fst \<beta>)))"

text \<open>Convert the language into the abstract language expected by the underlying logic
      this relates the syntax to its semantics \<close> 
fun lift\<^sub>c :: "('v,'g,'r,'a) lang \<Rightarrow> (('v,'g,'r,'a) auxop, ('v,'g,'r,'a) stateTree) com" 
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Op v a f) = Basic (\<lfloor>v,a,f\<rfloor>)" |
    "lift\<^sub>c (lang.Seq c\<^sub>1 c\<^sub>2) = (com.Seq (lift\<^sub>c c\<^sub>1) w (lift\<^sub>c c\<^sub>2))" |   (* lang.seq no wmm *)
    "lift\<^sub>c (If b c\<^sub>1 c\<^sub>2 c\<^sub>3) = (Choice (\<lambda> state. if (ev\<^sub>B state b)       
                                 then (com.Seq (Basic (\<lfloor>cmp b\<rfloor>)) w (lift\<^sub>c c\<^sub>1)) 
                                 else (com.Seq (Basic (\<lfloor>ncmp b\<rfloor>)) w (lift\<^sub>c c\<^sub>2))))" |
    "lift\<^sub>c (While b I c) = (((Basic (\<lfloor>cmp b\<rfloor>)) ;\<^sub>w (lift\<^sub>c c))*\<^sub>w) ;\<^sub>w (Basic (\<lfloor>ncmp b\<rfloor>))" | 
    "lift\<^sub>c (DoWhile I c b) = ((((lift\<^sub>c c) ;\<^sub>w (Basic (\<lfloor>cmp b\<rfloor>)))*\<^sub>w) ;\<^sub>w (lift\<^sub>c c)) ;\<^sub>w (Basic (\<lfloor>ncmp b\<rfloor>))" 


(* TODO:
  in lift\<^sub>c we have to model how lang maps to its semantics;
  to model speculative execution, we have to match
     (If b c\<^sub>1 c\<^sub>2) ---> (spec c\<^sub>2; c\<^sub>3); [b]; c\<^sub>1 ; c\<^sub>3 \choice (spec c\<^sub>1; c\<^sub>3); [\<not>b]; c\<^sub>2 ; c\<^sub>3
  or            ---> \<triangle>(Capture s c\<^sub>2;c\<^sub>3) ;\<^sub>s\<^sub>c [b] ; c\<^sub>1 \choice \<triangle>(Capture s c\<^sub>1;c\<^sub>3) ;\<^sub>s\<^sub>c [\<not>b] ; c\<^sub>2
 
c\<^sub>3 probably not needed since it sits in the postcondition!

      (If b c\<^sub>1 c\<^sub>2) ---> (spec c\<^sub>2; c\<^sub>3); [b]; c\<^sub>1 ; c\<^sub>3 \choice (spec c\<^sub>1; c\<^sub>3); [\<not>b]; c\<^sub>2 ; c\<^sub>3
                   --->   

  where c\<^sub>3 is the rest of the program after the If command; (and similarly for loops!)
  hence we need another parameter ('v,'g,'r,'a) lang which models the remaining program c\<^sub>3

  fun lift\<^sub>c :: "('v,'g,'r,'a) lang \<Rightarrow> ('v,'g,'r,'a) lang \<Rightarrow> (('v,'g,'r,'a) auxop, ('v,'g,'r,'a) stateTree) com" 

*)

(* these two dummy parameters used in the interpretation of locale rules, locale semantics resp.,
    and help to instantiate the types of auxop and state*)

abbreviation "someAuxOp ::('v,'g,'r,'a) auxop  \<equiv> undefined"
abbreviation "someState ::('v,'g,'r,'a) stateTree \<equiv> undefined" (* add a push instance *)

print_locale rules 
print_locale semantics

interpretation rules "someAuxOp" "someState"  
  done
  


term obs 
term lift\<^sub>c 
term lexecute



(* TODO: try using local_trace (from semantics.thy) instead of obs_trace *)

text \<open>Correctness of the guarantee check\<close>
lemma com_guar:
  "wellformed R G \<Longrightarrow> guar\<^sub>c c G \<Longrightarrow>  \<forall>\<beta> \<in> obs (lift\<^sub>c c). guar\<^sub>\<alpha> \<beta> (step G)"
proof (induct c)
  case Skip
  then show ?case by auto
next
  case (Op pred op aux)
  then show ?case 
    apply (cases op) using Op  
    by (auto simp: liftg_def guar_def wp\<^sub>r_def) 
next
  case (Seq c1 c2)
  then show ?case 
  proof -
    have a0:"guar\<^sub>c c1 G" "guar\<^sub>c c2 G" using Seq(4) by auto+
    then have a1:"\<forall>\<beta>\<in>obs (lift\<^sub>c c1). guar\<^sub>\<alpha> \<beta> (step G)" 
      using Seq by blast
    then have a2:"\<forall>\<beta>\<in>obs (lift\<^sub>c c2). guar\<^sub>\<alpha> \<beta> (step G)" 
      using Seq a0(2) by blast
    then show ?thesis using Seq a1 
      sorry
  qed
next
  case (If x1 c1 c2)
  then show ?case 
    apply (auto simp: guar_def reflexive_def liftl_def step_def If) 
    sorry    
next
  case (While x1 x2 c)
  then show ?case 
    apply (auto simp: guar_def reflexive_def liftl_def step_def While)
    sorry
next
  case (DoWhile x1 c x3)
  then show ?case 
    apply (auto simp: guar_def reflexive_def liftl_def step_def)
    sorry
qed

(*
  case (Op pred op aux)
  then show ?case  
    apply (cases op) using Op  
       by (auto simp: liftg_def guar_def wp\<^sub>r_def) 
qed (auto simp: guar_def reflexive_def liftl_def step_def) 
*)

text \<open>Extract the instruction from an abstract operation \<close>
(* tag (opbasic) = (op \<times> auxfn) *)
abbreviation inst :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r) op"
  where "inst a \<equiv> fst (tag a)"

abbreviation aux :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) auxfn"
  where "aux a \<equiv> snd (tag a)"

text \<open>A basic is well-formed if its behaviour agrees with the behaviour
      of its instruction and auxiliary composed.\<close>
(* beh \<beta> = snd (snd \<beta>) *)
definition wfbasic :: "('v,'g,'r,'a) opbasic \<Rightarrow> bool"
  where "wfbasic \<beta> \<equiv> beh \<beta> = beh\<^sub>a (inst \<beta>, aux \<beta>)"

(* to give a type falls over as the parameter list does not match *)

fun wfbookkeep_list where                  (*:: "('v,'g,'r,'a) bookkeeping \<Rightarrow> bool list"*) 
  "wfbookkeep_list [] = []" |
  "wfbookkeep_list (Scope # r) = wfbookkeep_list r" |
  "wfbookkeep_list ((Reorder \<alpha>' _ _) # r) = (wfbasic \<alpha>') # (wfbookkeep_list r)"

definition wfbookkeep                      (*:: "('v,'g,'r,'a) opbookkeeping \<Rightarrow> bool" *)
  where "wfbookkeep r \<equiv> fold HOL.eq (wfbookkeep_list r) True"

definition wfcom
  where "wfcom c \<equiv> \<forall>\<beta> \<in> obs c. wfbasic \<beta>"

lemma wfcomI [intro]:
  "wfcom (lift\<^sub>c c)"
proof (induct c)
  case Skip
  then show ?case using obs_nil wfcom_def by force
next
  case (Op x1 x2 x3) 
  then show ?case by (auto simp: wfcom_def wfbasic_def liftg_def liftl_def)
next
  case (Seq c1 c2)
  then show ?case apply (auto simp: wfcom_def wfbasic_def liftg_def liftl_def)
    sorry
next
  case (If x1 c1 c2)
  then show ?case sorry
next
  case (While x1 x2 c)
  then show ?case sorry
next
  case (DoWhile x1 c x3)
  then show ?case sorry
qed
  
(*  by (induct c) (auto simp: wfcom_def wfbasic_def liftg_def liftl_def)
*)


lemma opbasicE:
  obtains (assign) x e f v b where  "(basic ) = ((assign x e,f), v, b)" |
          (cmp) g f v b where "(basic ) = ((cmp g,f), v, b)" |
          (fence) f v b where "(basic ) = ((full_fence,f), v, b)" |
          (nop) f v b where "(basic ) = ((nop,f), v, b)" |
          (leak) e f v b where "(basic ) = ((leak e,f), v, b)" 
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

lemma fwdE:
  assumes "reorder_inst \<alpha>' \<beta> \<alpha>"
  obtains (no_fwd) "inst \<alpha>' = inst \<alpha>" "aux \<alpha>' = aux \<alpha>" "vc \<alpha>' = vc \<alpha>" "wr (inst \<beta>) \<inter> rd (inst \<alpha>) = {}" |
          (fwd) x e f where "tag \<beta> = (assign x e,f)" "x \<in> rd (inst \<alpha>)" "deps\<^sub>E e \<subseteq> locals"
proof (cases "wr (inst \<beta>) \<inter> rd (inst \<alpha>) = {}")
  case True
  then show ?thesis using no_fwd assms    
    apply (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)
    sorry
next
  case False
  then show ?thesis using fwd assms 
    apply (cases \<alpha> rule: opbasicE)
    apply( cases \<beta> rule: opbasicE)
    apply (auto simp: Let_def split: if_splits)
    sorry
qed

lemma fwd_wfbasic:
  assumes "reorder_com \<alpha>' c w \<alpha>" "wfbasic \<alpha>" 
  shows "wfbasic \<alpha>'"
  using assms 
  sorry
(*
proof (induct \<alpha>' \<alpha> rule: reorder_com.induct)
  case (2 \<alpha>' \<beta> \<alpha>)
  then show ?case 
    apply (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def wfbasic_def)
qed auto
*)

lemma [simp]:
  "wfcom (c\<^sub>1 ;\<^sub>w c\<^sub>2) = (wfcom c\<^sub>1 \<and> wfcom c\<^sub>2)"
  apply (auto simp: wfcom_def) 
  sorry

lemma wfcom_silent:
  "silent c c' \<Longrightarrow> wfcom c \<Longrightarrow> wfcom c'"
  using obs_sil by (auto simp: wfcom_def)

lemma wfcom_exec:
  "lexecute c \<alpha> r c' \<Longrightarrow> wfcom c \<Longrightarrow> wfcom c'"
  using obs_exec unfolding wfcom_def by blast


lemma wfcom_exec_prefix:
  "lexecute c \<alpha> r c' \<Longrightarrow> wfcom c \<Longrightarrow> wfbookkeep r \<and> wfbasic \<alpha>"
  using  wfcom_def wfbookkeep_def wfbookkeep_list.simps wfcom_exec fwd_wfbasic 




(* fix up the commands: no ., Choice, Loop, no SeqChoice
fun sim :: "('a,'b) com \<Rightarrow> bool"
  where 
    "sim (c\<^sub>1 || c\<^sub>2) = False" |
    "sim (Thread _) = False" |
    "sim (SeqChoice _) = False" |
    "sim (c\<^sub>1 ;\<^sub>w c\<^sub>2) = (sim c\<^sub>1 \<and> sim c\<^sub>2)" |
    "sim (c\<^sub>1 \<cdot> c\<^sub>2) = False"  |
    "sim (c\<^sub>1 \<sqinter> c\<^sub>2) = (sim c\<^sub>1 \<and> sim c\<^sub>2)" |
    "sim (c loopStar) = (sim c)" |
    "sim _ = True"
*)



text \<open>The language is always thread-local\<close>
lemma sim_lift [intro]:
  "sim (lift\<^sub>c c)"
  apply (induct c) apply auto sorry

text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

end
