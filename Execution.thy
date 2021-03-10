theory Execution
  imports Semantics
begin

chapter \<open>Execution Behaviour\<close>

text \<open>Compose two state transitions\<close>
definition comp (infixr "\<otimes>" 60)
  where "comp a b \<equiv> {(m,m'). \<exists>m''. (m,m'') \<in> a \<and> (m'',m') \<in> b}"

text \<open>Stabilisation of a predicate under an environment step\<close>
definition st
  where "st R P \<equiv> {m. \<forall>m'. (m,m') \<in> R\<^sup>* \<longrightarrow> m' \<in> P}"

locale execution = semantics +
  fixes eval :: "'a \<Rightarrow> 's rel" 

context execution
begin

(* P and Q are configurations containing (program,state)  *)

section \<open>Transition Definitions\<close>

text \<open>Environment Transition\<close>
abbreviation etran ("_ -e\<rightarrow> _" [81,81] 80)
  where "etran P Q \<equiv> (fst P) = (fst Q)"

text \<open>Program Execution Transition\<close>
abbreviation ctran ("_ -\<alpha>\<rightarrow> _" [81,81] 80)
  where "ctran P Q \<equiv> (\<exists>\<alpha>. ((fst P) \<mapsto>\<^sub>\<alpha> (fst Q)) \<and> (snd P,snd Q) \<in> eval \<alpha>)"

text \<open>Program Silent Transition\<close>
abbreviation stran ("_ -s\<rightarrow> _" [81,81] 80)
  where "stran P Q \<equiv> (((fst P) \<leadsto> (fst Q)) \<and> (snd P) = (snd Q))"

text \<open>Program Transition\<close>
abbreviation atran ("_ -c\<rightarrow> _" [81,81] 80)
  where "atran P Q \<equiv> (P -\<alpha>\<rightarrow> Q \<or> P -s\<rightarrow> Q)"

(* transitions are list of configurations
   [s] is a singleton list *)

text \<open>Collect of all possible transitions\<close>
inductive_set transitions
  where 
    one[intro]: "[s] \<in> transitions" |
    env[intro]: "s -e\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    prg[intro]: "s -\<alpha>\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions" |
    sil[intro]: "s -s\<rightarrow> s' \<Longrightarrow> s'#t \<in> transitions \<Longrightarrow> s#s'#t \<in> transitions"
inductive_cases transitionsE[elim]: "t \<in> transitions"

text \<open>Ensure there is no parallelism within a program\<close>
fun local_only
  where 
    "local_only (c\<^sub>1 || c\<^sub>2) = False" |
    "local_only (c\<^sub>1 ; c\<^sub>2) = (local_only c\<^sub>1 \<and> local_only c\<^sub>2)" |    
    "local_only (c\<^sub>1 \<sqinter> c\<^sub>2) = (local_only c\<^sub>1 \<and> local_only c\<^sub>2)" |  
    "local_only (c*) = (local_only c)" |    
    "local_only _ = True"

section \<open>Predicate Manipulations\<close>

text \<open>Weakest Precondition, based on evaluation of an instruction\<close>
definition wp
  where "wp a P \<equiv> {m. \<forall>m'. (m,m') \<in> eval a \<longrightarrow> m' \<in> P}"

(*guar check*)
text \<open>Specification Precondition, ensuring an instruction conforms to a relation\<close>
definition spec
  where "spec \<alpha> G \<equiv> {m. \<forall>m\<^sub>1. (m,m\<^sub>1) \<in> eval \<alpha> \<longrightarrow> (m,m\<^sub>1) \<in> G}"

end

end