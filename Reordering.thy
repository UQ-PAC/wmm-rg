theory Reordering
  imports Syntax
begin

chapter \<open>Reordering Properties\<close> 

locale reordering =
  fixes re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100)
  and fwd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<langle>_\<rangle>" [1000,0] 1000)

context reordering
begin

text \<open>Combine forwarding and reordering into a single check\<close>
abbreviation reorder_act :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ < _ <\<^sub>a _" [100,0,100] 100)
  where "\<beta>' < \<alpha> <\<^sub>a \<beta> \<equiv> \<beta>' = \<beta>\<langle>\<alpha>\<rangle> \<and> \<alpha> \<hookleftarrow> \<beta>\<langle>\<alpha>\<rangle>"

text \<open>Recursively define reordering of an instruction earlier than a program\<close>
fun reorder_prog :: "'a \<Rightarrow> 'a com \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ < _ <\<^sub>p _" [100,0,100] 100)
  where
    "reorder_prog \<alpha>' Nil \<alpha> = (\<alpha>' = \<alpha>)" |
    "reorder_prog \<alpha>' (Basic \<beta>) \<alpha> = (\<alpha>' < \<beta> <\<^sub>a \<alpha>)" |
    "reorder_prog \<alpha>' (c\<^sub>1 ; c\<^sub>2) \<alpha> = (\<exists>\<alpha>\<^sub>n. \<alpha>' < c\<^sub>1 <\<^sub>p \<alpha>\<^sub>n \<and> \<alpha>\<^sub>n < c\<^sub>2 <\<^sub>p \<alpha>)" |
    "reorder_prog \<alpha>' (c\<^sub>1 \<sqinter> c\<^sub>2) \<alpha> = (\<alpha>' < c\<^sub>1 <\<^sub>p \<alpha> \<and> \<alpha>' < c\<^sub>2 <\<^sub>p \<alpha>)" |
    "reorder_prog \<alpha>' (Loop c) \<alpha> = (\<alpha>' = \<alpha> \<and> \<alpha> < c <\<^sub>p \<alpha>)" |
    "reorder_prog _ _ _ = False"

text \<open>Recursively define forwarding of an instruction across a program \<close>
fun fwd_prog :: "'a \<Rightarrow> 'a com \<Rightarrow> 'a"
  ("_\<llangle>_\<rrangle>" [1000,0] 1000)
  where
    "fwd_prog \<alpha> (Basic \<beta>) = \<alpha>\<langle>\<beta>\<rangle>" |
    "fwd_prog \<alpha> (c\<^sub>1 ; c\<^sub>2) = fwd_prog (fwd_prog \<alpha> c\<^sub>2) c\<^sub>1" |
    "fwd_prog \<alpha> (c\<^sub>1 \<sqinter> c\<^sub>2) = fwd_prog \<alpha> c\<^sub>1" |
    "fwd_prog \<alpha> _  = \<alpha>"

text \<open>Relationship between program reordering and program forwarding\<close>
lemma fwd_prog [simp]:
  assumes "\<alpha>' < c <\<^sub>p \<alpha>"
  shows "\<alpha>\<llangle>c\<rrangle> = \<alpha>'"
  using assms by (induct c arbitrary: \<alpha>' \<alpha>) auto

end

end