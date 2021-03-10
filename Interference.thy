theory Interference
  imports Execution
begin

locale interference = execution re fwd eval
  for re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100)
  and fwd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<langle>_\<rangle>" [1000,0] 1000)
  and eval :: "'a \<Rightarrow> 's rel"

context interference
begin

section \<open>Interference Definitions\<close>


(* the following to points are changed *)
(* the outer R\<^sup>*s are not necessary for the proof but
    maybe R\<^sup>* \<otimes> eval \<beta> \<otimes> R\<^sup>* \<otimes> eval \<alpha> \<otimes> R\<^sup>* is more general than eval \<beta> \<otimes> R\<^sup>* \<otimes> eval \<alpha> ? *)
(* with (X \<beta> \<inter> wp \<beta> (st R (X \<alpha>)) \<subseteq> (X \<beta> \<inter> wp \<beta> (X \<alpha>)  the below form is stricter but easier to prove *)

(* X stands for ctx (mapping from stmt/prog to pred; it's abstract here an can include guar or more stuff), 
   st R P = wp(R,P)  *)

(* introduce also in condition 2 a leading R* on both sides to include stability check 
    on \<beta> and \<alpha> on both sides; it should be a weaker condition; and omit trailing R* in RHS, i.e.
          (R\<^sup>* \<otimes> eval \<alpha>\<langle>\<beta>\<rangle> \<otimes> R\<^sup>* \<otimes> eval \<beta> \<subseteq> R\<^sup>* \<otimes> eval \<beta> \<otimes> R\<^sup>* \<otimes> eval \<alpha>)     *)

text \<open>Independence of two instructions \<beta> and \<alpha> under environment R, 
      such that the early execution of \<alpha> is assumed to be possible and 
      cannot invalidate sequential reasoning\<close>
definition inter\<^sub>a
  where "inter\<^sub>a R G X \<beta> \<alpha> \<equiv> 
          (X \<beta> \<inter> wp \<beta> (X \<alpha>) \<subseteq> X \<alpha>\<langle>\<beta>\<rangle> \<inter> wp \<alpha>\<langle>\<beta>\<rangle> (st R (X \<beta>)) \<and> 
          (eval \<alpha>\<langle>\<beta>\<rangle> \<otimes> R\<^sup>* \<otimes> eval \<beta> \<subseteq> R\<^sup>* \<otimes> eval \<beta> \<otimes> R\<^sup>* \<otimes> eval \<alpha> \<otimes> R\<^sup>*)) \<and>
          (X \<alpha>\<langle>\<beta>\<rangle> \<subseteq> spec \<alpha>\<langle>\<beta>\<rangle> G)"


(* inductively expand inter\<^sub>a over programs 
   the various fwds of \<alpha> over multiple steps is captures in \<alpha>\<llangle>c\<^sub>2\<rrangle> 
*)

text \<open>Independence of program c and instruction \<alpha> under environment R,
      such that the early execution of \<alpha> is assumed to be possible and 
      cannot invalidate sequential reasoning\<close>
fun inter\<^sub>c
  where
    "inter\<^sub>c R G X (Basic \<beta>) \<alpha> = inter\<^sub>a R G X \<beta> \<alpha>" |
    "inter\<^sub>c R G X (c\<^sub>1 ; c\<^sub>2) \<alpha> = (inter\<^sub>c R G X c\<^sub>1 \<alpha>\<llangle>c\<^sub>2\<rrangle> \<and> inter\<^sub>c R G X c\<^sub>2 \<alpha>)" |
    "inter\<^sub>c R G X (c\<^sub>1 \<sqinter> c\<^sub>2) \<alpha> = (inter\<^sub>c R G X c\<^sub>1 \<alpha> \<and> inter\<^sub>c R G X c\<^sub>2 \<alpha>)" |
    "inter\<^sub>c R G X (c*) \<alpha> = inter\<^sub>c R G X c \<alpha>" |
    "inter\<^sub>c R G X _ \<alpha> = True"

(* instrumented step c \<mapsto>[\<alpha>,r,\<alpha>'] c'
   \<alpha> = fwd(\<alpha>'); 
   r = "collects" all the steps that \<alpha>' got forwarded over to \<alpha> (in the middle parameter of \<mapsto>)
       for each of these stmts in r non-interference with \<alpha> needs to be proved *)

text \<open>Instrumented version of the semantics that collects the reordering effects\<close>
inductive_set execute_collect :: "('a com \<times> 'a \<times> 'a com \<times> 'a \<times> 'a com) set"
  and execute_collect_abv :: "'a com \<Rightarrow> 'a \<Rightarrow> 'a com \<Rightarrow> 'a \<Rightarrow> 'a com \<Rightarrow> bool"
  ("_ \<mapsto>[_,_,_] _" [71,0,0,0,71] 70)
  where
  "c \<mapsto>[\<alpha>,t,\<gamma>] c' \<equiv> (c, \<alpha>, t, \<gamma>, c') \<in> execute_collect" |
  act[intro]:  "Basic \<alpha> \<mapsto>[\<alpha>,Nil,\<alpha>] Nil" |
  pre[intro]:  "c\<^sub>1 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' \<Longrightarrow> c\<^sub>1 ; c\<^sub>2 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' ; c\<^sub>2" |
  pst[intro]:  "c\<^sub>1 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1' \<Longrightarrow> \<gamma> < c\<^sub>2 <\<^sub>p \<alpha> \<Longrightarrow> c\<^sub>2 ; c\<^sub>1 \<mapsto>[\<gamma>,c\<^sub>2;c,\<alpha>'] c\<^sub>2 ; c\<^sub>1'"
inductive_cases execute_collect[elim]: "c\<^sub>1 \<mapsto>[\<alpha>,c,\<alpha>'] c\<^sub>1'"

(* reordering-valid programs do not loose validity due to reorderings *)

text \<open>Interference property preserved throughout execution\<close>
inductive inter
  where "(\<forall>c' \<alpha> \<alpha>' r. c \<mapsto>[\<alpha>,r,\<alpha>'] c' \<longrightarrow> (inter R G X c' \<and> inter\<^sub>c R G X r \<alpha>')) \<Longrightarrow> 
         (\<forall>c'. c \<leadsto> c' \<longrightarrow> inter R G X c') \<Longrightarrow> inter R G X c"

text \<open>Interference is preserved across a silent step\<close>
lemma inter_silentI [intro]:
  assumes "inter R G X c" "c \<leadsto> c'"
  shows "inter R G X c'"
  using assms 
  by cases auto

text \<open>Interference is preserved across an execution step and prevents interference\<close>
lemma indep_stepI [intro]:
  assumes "inter R G X c" "c \<mapsto>[\<alpha>,r,\<alpha>'] c'"
  shows "inter R G X c' \<and> inter\<^sub>c R G X r \<alpha>'"
  using assms 
  by cases auto

text \<open>Instrumented semantics collects valid reorderings\<close>
lemma collect_reorder:
  assumes "c \<mapsto>[\<alpha>',r,\<alpha>] c'"
  shows "\<alpha>' < r <\<^sub>p \<alpha>"
  using assms by (induct, auto)

text \<open>Convert a normal execution step into an instrumented step\<close>
lemma exec_collect:
  assumes "c \<mapsto>\<^sub>\<alpha> c'" "local_only c"
  shows "\<exists>r \<alpha>'. c \<mapsto>[\<alpha>,r,\<alpha>'] c'"
  using assms by induct auto

end

end