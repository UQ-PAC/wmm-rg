theory SimAsm_WP
  imports SimAsm
begin

locale wp = expression st st_upd aux aux_upd locals
  for st :: "'s \<Rightarrow> 'r \<Rightarrow> 'v" 
  and st_upd ("_'((2_/ :=\<^sub>u/ (2_))')" [900,0,0] 901) and aux and aux_upd ("_'((2aux:/ _)')" [900,0] 901)
  and locals :: "'r set" 
  and rg :: "'s \<Rightarrow> 'l"
  and glb :: "'s \<Rightarrow> 'g"
text \<open>The added rg and glb are projections onto the local and global states.\<close>

datatype 'g label = Un 'g | Gl 'g
type_synonym 'a pred = "'a set" 
type_synonym 'a trans = "'a pred \<Rightarrow> 'a pred"
type_synonym 'a rtrans = "'a rel \<Rightarrow> 'a rel"


context wp
begin 

text \<open> Reasoning is performed on "simple" predicates, not on stateTrees, which are 
        later (in the soundness proof) matched to the stateTrees on which the semantics operates \<close>

section \<open>Wellformedness\<close>

text \<open>stabilize R P is effectively the weakest (i.e. largest) precondition
that is guaranteed to arrive at P after R steps. 
This is something like the weakest precondition of the environment steps.\<close>
definition stabilize
  where "stabilize R P \<equiv> {m. \<forall>m'. (glb m,glb m') \<in> R \<longrightarrow> rg m = rg m' \<longrightarrow> m' \<in> P}"

definition reflexive
  where "reflexive R \<equiv> (\<forall>m. (m,m) \<in> R)"

definition transitive
  where "transitive R \<equiv> (\<forall>m m' m''. (m,m') \<in> R \<longrightarrow> (m',m'') \<in> R \<longrightarrow> (m,m'') \<in> R)"

definition assert
  where "assert b \<equiv> {m. b}"


text \<open>Lift a relational predicate\<close>
definition step\<^sub>t :: "'g rel \<Rightarrow> 's rel"
  where "step\<^sub>t R \<equiv> {(m,m'). (glb m, glb m') \<in> R \<and> rg m = rg m'}"


text \<open>Lift a relational predicate and assume it preserves the thread state\<close>
definition step :: "'g rel \<Rightarrow> 's rel"
  where "step R \<equiv> {(t,t'). (glb t, glb t') \<in> R}"


text \<open>Define stability in terms of a relational predicate that preserves the thread state\<close>
abbreviation stable\<^sub>t
  where "stable\<^sub>t R P \<equiv> stable (step\<^sub>t R) P"

text \<open>Couple all wellformedness conditions into a single definition\<close>
abbreviation wellformed :: "'g rel \<Rightarrow> 'g rel \<Rightarrow> bool"
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
    using assms a(2) unfolding transitive_def
    using trans_def by fast
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
  have "\<forall>g. (glb m, glb g) \<in> R \<longrightarrow> rg m = rg g \<longrightarrow> g \<in> P" 
       "(glb m, glb m) \<in>  R"
    using assms by (simp_all add: stabilize_def reflexive_def)
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

(* define (spec c) = \<triangle>(Capture s c)? No, only in the semantics (i.e., the abstract logic) *)

text \<open>Transform a predicate based on an sub-operation\<close>
fun wp\<^sub>i :: "('r,'v) op \<Rightarrow> 's set \<Rightarrow> 's set" 
  where 
    "wp\<^sub>i (assign r e) Q = {s. s (r :=\<^sub>u st_ev\<^sub>E s e) \<in> Q}" |
    "wp\<^sub>i (cmp b) Q =  {s. (st_ev\<^sub>B s b) \<longrightarrow> s \<in> Q}" | 
    "wp\<^sub>i (leak c e) Q = {s. (s (c :=\<^sub>u st_ev\<^sub>E s e)) \<in> Q}" |
    "wp\<^sub>i _ Q = Q"



text \<open>Transform a predicate based on an auxiliary state update\<close>
fun wp\<^sub>a :: "('s,'a) auxfn \<Rightarrow> 's set \<Rightarrow> 's set"
  where "wp\<^sub>a a Q = {t. t(aux: a) \<in> Q}"


text \<open> Transform a predicate over a speculation \<close>
fun wp\<^sub>i\<^sub>s :: "('r,'v) op \<Rightarrow> 's set \<Rightarrow> 's set"          (* wp_spec on ops *)
  where 
    "wp\<^sub>i\<^sub>s full_fence Q = UNIV"  |
    "wp\<^sub>i\<^sub>s c Q = wp\<^sub>i c Q"


fun po :: "('r,'v) op \<Rightarrow> 's set"
  where
    "po (assign r e) = undefined" |
    "po (cmp v) = undefined" |
    "po full_fence = undefined" |
    "po nop = undefined" |
    "po (leak v va) = undefined"

fun wp\<^sub>s :: "('r,'v,'s,'a) lang \<Rightarrow> 's set \<Rightarrow> 's set"     (* wp_spec transformer on lang *)
  where 
    "wp\<^sub>s Skip Q = Q" |
    "wp\<^sub>s (Op v a f) Q = (v \<inter> (po a) \<inter> wp\<^sub>i\<^sub>s a (wp\<^sub>a f Q))" |
    "wp\<^sub>s (Seq c\<^sub>1 c\<^sub>2) Q = wp\<^sub>s c\<^sub>1 (wp\<^sub>s c\<^sub>2 Q)" |
    "wp\<^sub>s (If b c\<^sub>1 c\<^sub>2 c\<^sub>3) Q = (wp\<^sub>s c\<^sub>1 (wp\<^sub>s c\<^sub>3 Q)) \<inter> (wp\<^sub>s c\<^sub>2 (wp\<^sub>s c\<^sub>3 Q))" |
    "wp\<^sub>s (While v va vb) b = undefined" | 
    "wp\<^sub>s (DoWhile v va vb) b = undefined"



fun merge :: "'s set \<Rightarrow> 's set \<Rightarrow> 's set"
  where "merge Q\<^sub>1 Q\<^sub>2 = undefined"

text \<open>Transform a predicate based on a program c within an environment R\<close>
fun wp :: "'g rel \<Rightarrow> ('r,'v,'s,'a) lang \<Rightarrow> 's set \<Rightarrow> 's set"
  where
    "wp R Skip Q = Q" |
    "wp R (Op v a f) Q = stabilize R (v \<inter> (po a) \<inter> wp\<^sub>i a (wp\<^sub>a f Q))" |
    "wp R (Seq c\<^sub>1 c\<^sub>2) Q = wp R c\<^sub>1 (wp R c\<^sub>2 Q)" |
    "wp R (If b c\<^sub>1 c\<^sub>2 c\<^sub>3) Q = 
               (merge (wp\<^sub>s c\<^sub>2  (wp\<^sub>s c\<^sub>3 Q)) (stabilize R (wp\<^sub>i (cmp b) (wp R c\<^sub>1  (wp R c\<^sub>3 Q)))))
               \<inter> (merge (wp\<^sub>s c\<^sub>1  (wp\<^sub>s c\<^sub>3 Q))   (stabilize R (wp\<^sub>i (ncmp b) (wp R c\<^sub>2  (wp R c\<^sub>3 Q)))))" |
    "wp R (While b I c) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp\<^sub>i (cmp b) (wp R c (stabilize R I)) \<inter> wp\<^sub>i (ncmp b) Q))" |
    "wp R (DoWhile I c b) Q = 
      (stabilize R I \<inter> assert (I \<subseteq> wp R c (stabilize R (wp\<^sub>i (cmp b) (stabilize R I) \<inter> wp\<^sub>i (ncmp b) Q))))"


text \<open>Convert a predicate transformer into a relational predicate transformer\<close>
definition wp\<^sub>r :: "'s trans \<Rightarrow> 's rtrans"
  where "wp\<^sub>r f G \<equiv> {(s,s'). s' \<in> f {s'. (s,s') \<in> G}}"


subsection \<open>Guarantee Checks\<close>

text \<open>Convert a predicate transformer into a guarantee check\<close>
abbreviation guar
  where "guar f G \<equiv> {t. (t,t) \<in> (wp\<^sub>r f G)}"

text \<open>Ensure all global operations in a thread conform to its guarantee\<close>
fun guar\<^sub>c
  where 
    "guar\<^sub>c Skip G = True" |
    "guar\<^sub>c (Op v a f) G = ((v \<inter> (po a)) \<subseteq> guar (wp\<^sub>i a o wp\<^sub>a f) (step G))" |
    "guar\<^sub>c (Seq c\<^sub>1 c\<^sub>2) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G)" |
    "guar\<^sub>c (If _ c\<^sub>1 c\<^sub>2 c\<^sub>3) G = (guar\<^sub>c c\<^sub>1 G \<and> guar\<^sub>c c\<^sub>2 G \<and> guar\<^sub>c c\<^sub>3 G)" |
    "guar\<^sub>c (While _ _ c) G = (guar\<^sub>c c G)" |
    "guar\<^sub>c (DoWhile _ c _) G = (guar\<^sub>c c G)"



section \<open>Locale Interpretation\<close>


(*
definition w
  where "w \<alpha>' \<beta> \<alpha> \<equiv> (re\<^sub>s \<beta> \<alpha> \<and> (\<alpha>'=fwd\<^sub>s \<alpha> (fst \<beta>)))"
*)

text \<open> definition for weak memory model which is used as parameter w in sequential composition \<close>

definition sc :: "('r,'v,'s,'a) opbasic \<Rightarrow> ('r,'v,'s,'a) opbasic \<Rightarrow> ('r,'v,'s,'a) opbasic \<Rightarrow> bool"
  where "sc \<alpha>' \<beta> \<alpha>  \<equiv> \<not>(re\<^sub>s \<beta> \<alpha>)"

abbreviation Seqsc (infixr "." 80)                      (* i.e., Seq c sc c' *)
  where "Seqsc c c' \<equiv> com.Seq c sc c'"

abbreviation Itersc ("_**" [90] 90)                       (* i.e., Loop c sc *)
  where "Itersc c \<equiv> com.Loop c sc"


definition reorder_inst :: "('r,'v,'s,'a) opbasic \<Rightarrow> ('r,'v,'s,'a) opbasic \<Rightarrow> ('r,'v,'s,'a) opbasic \<Rightarrow> bool"
  where "reorder_inst \<alpha>' \<beta> \<alpha>  \<equiv> (re\<^sub>s \<beta> \<alpha> \<and> (\<alpha>'=fwd\<^sub>s \<alpha> (fst \<beta>)))"

abbreviation Seqw (infixr ";;" 80)                      (* i.e., Seq c w c' *)
  where "Seqw c c' \<equiv> com.Seq c reorder_inst c'"

abbreviation Iterw ("_*" [90] 90)                       (* i.e., Loop c w *)
  where "Iterw c \<equiv> com.Loop c reorder_inst"


text \<open>Convert the language into the abstract language expected by the underlying logic
      this relates the syntax to its semantics \<close> 
fun lift\<^sub>c :: "('r,'v,'s,'a) lang \<Rightarrow> (('r,'v,'s,'a) auxop, 's) com" 
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Op v a f) = Basic (\<lfloor>v,a,f\<rfloor>)" |
    "lift\<^sub>c (lang.Seq c\<^sub>1 c\<^sub>2) = (lift\<^sub>c c\<^sub>1) ;; (lift\<^sub>c c\<^sub>2)" |  
    "lift\<^sub>c (If b c\<^sub>1 c\<^sub>2 c\<^sub>3) =  (Choice (\<lambda> s. if (st_ev\<^sub>B s b)
                    then Interrupt (\<forall>\<^sub>c((lift\<^sub>c c\<^sub>2) ;; (lift\<^sub>c c\<^sub>3))) . (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>1)) 
                    else Interrupt (\<forall>\<^sub>c((lift\<^sub>c c\<^sub>1) ;; (lift\<^sub>c c\<^sub>3))) . (Basic (\<lfloor>ncmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>2))))" |
(* without speculation:  (Choice (\<lambda> s. if (st_ev\<^sub>B s b)
                                 then (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>1)) 
                                 else (Basic (\<lfloor>ncmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>2))))" | *)
    "lift\<^sub>c (While b I c) = (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c))* ;; Basic (\<lfloor>ncmp b\<rfloor>)" | 
(*    "lift\<^sub>c (While b I c c\<^sub>3) = lift\<^sub>c (If b (Seq c (While b I c c\<^sub>3)) Skip c\<^sub>3)" | *)
(*    "lift\<^sub>c (While b I c) = (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c))* ;; Basic (\<lfloor>ncmp b\<rfloor>)" | *)
    "lift\<^sub>c (DoWhile I c b) = ((lift\<^sub>c c) ;; Basic (\<lfloor>cmp b\<rfloor>))* ;; (lift\<^sub>c c) ;; Basic (\<lfloor>ncmp b\<rfloor>)" 


(* TODO:
  in lift\<^sub>c we have to model how lang maps to its semantics;
  to model speculative execution, we have to match
      lift\<^sub>c (While b I c) = ...
      lift\<^sub>c (DoWhile I c b) = 
*)

(* these two dummy parameters used in the interpretation of locale rules, locale semantics resp.,
    and help to instantiate the types of auxop and state*)

abbreviation "someAuxOp ::('v,'g,'r,'a) auxop  \<equiv> undefined"
abbreviation "someState ::'s \<equiv> undefined" (* add a push instance *)

print_locale rules 
print_locale semantics

interpretation rules  (* No type arity state_rec_ext :: pstate  when "someAuxOp" "someState" *)
  done

term obs 
term lexecute
term lift\<^sub>c 
print_locale rules



text \<open>Extract the instruction from an abstract operation \<close>
(* tag (opbasic) = (op \<times> auxfn) *)
abbreviation inst :: "('r,'v,'s,'a) opbasic \<Rightarrow> ('r,'v) op"
  where "inst a \<equiv> fst (tag a)"

abbreviation auxbasic :: "('r,'v,'s,'a) opbasic \<Rightarrow> ('s,'a) auxfn"
  where "auxbasic a \<equiv> snd (tag a)"

text \<open>A basic is well-formed if its behaviour (i.e., its abstract semantics) agrees with the behaviour
      of its instruction and auxiliary composed (i.e., the concrete semantics of the instantiation).\<close>
(* beh \<beta> = snd (snd \<beta>) *)
definition wfbasic :: "('r,'v,'s,'a) opbasic \<Rightarrow> bool"
  where "wfbasic \<beta> \<equiv> beh \<beta> = beh\<^sub>a (inst \<beta>, auxbasic \<beta>)"


lemma opbasicE:
    obtains (assign) x e f v b where  "(basic ) = ((assign x e,f), v, b)" |
          (cmp) g f v b where "(basic ) = ((cmp g,f), v, b)" |
          (fence) f v b where "(basic ) = ((full_fence,f), v, b)" |
          (nop) f v b where "(basic ) = ((nop,f), v, b)" |
          (leak) c e f v b where "(basic ) = ((leak c e,f), v, b)" 
  by (cases basic, case_tac a, case_tac aa; clarsimp) 

lemma [simp]:
  "wr (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = wr (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)

lemma [simp]:
  "barriers (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = barriers (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)

lemma [simp]:
"rd (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = (if wr (inst \<beta>) \<inter> rd (inst \<alpha>) \<noteq> {} 
                                  then rd (inst \<alpha>) - wr (inst \<beta>) \<union> rd (inst \<beta>) else rd (inst \<alpha>))"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto)

lemma vc_fwd\<^sub>s[simp]:
  "vc (fwd\<^sub>s \<alpha> \<beta>) = vc \<alpha>"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma beh_fwd\<^sub>s [simp]:
  "beh (fwd\<^sub>s \<alpha> \<beta>) = ( beh\<^sub>a (fwd\<^sub>i (inst \<alpha>) (fst \<beta>), (auxbasic \<alpha>)) )"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: wfbasic_def Let_def split: if_splits) 

lemma aux_fwd\<^sub>s [simp]:
  "auxbasic (fwd\<^sub>s \<alpha> \<beta>) = auxbasic \<alpha>"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma inst_fwd\<^sub>s [simp]:
  "inst (fwd\<^sub>s \<alpha> (assign x e, f)) = subst\<^sub>i (inst \<alpha>) x e"
  by (cases \<alpha> rule: opbasicE; auto simp: Let_def split: if_splits)


text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

end (* of context *)

end


(* old stuff, not needed for Nick's new soundness proof:



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

text \<open>The language is always thread-local\<close>
lemma sim_lift [intro]:
  "sim (lift\<^sub>c c)"
  apply (induct c) apply auto sorry
*)
*)
