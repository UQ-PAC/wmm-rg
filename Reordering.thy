theory Reordering
  imports Syntax
begin

chapter \<open>Reordering Properties\<close> 

text \<open>
Assume an externally provided reordering and forwarding functions, to define the memory model.
The ideas here are derived from Colvin & Smith.
From these definitions we can recursively define reordering and forwarding over programs.
\<close>

locale reordering =
  fixes fwd :: "('a,'b) basic \<Rightarrow> 'b \<Rightarrow> ('a,'b) basic"
  and re :: "'b \<Rightarrow> 'b \<Rightarrow> bool" 

context reordering
begin

abbreviation re_abv (infix "\<hookleftarrow>" 100)
  where "\<alpha> \<hookleftarrow> \<beta> \<equiv> re (id \<alpha>) (id \<beta>)"

abbreviation fwd_abv ("_\<langle>_\<rangle>" [1000,0] 1000)
  where "\<alpha>\<langle>\<beta>\<rangle> \<equiv> fwd (\<alpha>) (id \<beta>)"

text \<open>Combine forwarding and reordering into a single definition\<close>
abbreviation reorder_inst :: "('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  ("_ < _ <\<^sub>a _" [100,0,100] 100)
  where "\<beta>' < \<alpha> <\<^sub>a \<beta> \<equiv> \<beta>' = \<beta>\<langle>\<alpha>\<rangle> \<and> \<alpha> \<hookleftarrow> \<beta>\<langle>\<alpha>\<rangle>"

text \<open>Recursively define reordering of an instruction earlier than a program\<close>
fun reorder_com :: "('a,'b) basic \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  ("_ < _ <\<^sub>c _" [100,0,100] 100)
  where
    "\<alpha>' < Nil <\<^sub>c \<alpha> = (\<alpha>' = \<alpha>)" |
    "\<alpha>' < Basic \<beta> <\<^sub>c \<alpha> = (\<alpha>' < \<beta> <\<^sub>a \<alpha>)" |
    "\<alpha>' < c\<^sub>1 ; c\<^sub>2 <\<^sub>c \<alpha> = (\<exists>\<alpha>\<^sub>n. \<alpha>' < c\<^sub>1 <\<^sub>c \<alpha>\<^sub>n \<and> \<alpha>\<^sub>n < c\<^sub>2 <\<^sub>c \<alpha>)" |
    "_ < _ <\<^sub>c _ = False"

text \<open>Recursively define forwarding of an instruction across a program\<close>
fun fwd_com :: "('a,'b) basic \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) basic"
  ("_\<llangle>_\<rrangle>" [1000,0] 1000)
  where
    "\<alpha>\<llangle>Basic \<beta>\<rrangle> = \<alpha>\<langle>\<beta>\<rangle>" |
    "\<alpha>\<llangle>c\<^sub>1 ; c\<^sub>2\<rrangle> = \<alpha>\<llangle>c\<^sub>2\<rrangle>\<llangle>c\<^sub>1\<rrangle>" |
    "\<alpha>\<llangle>c\<^sub>1 \<sqinter> c\<^sub>2\<rrangle> = \<alpha>\<llangle>c\<^sub>1\<rrangle>" |
    "\<alpha>\<llangle>_\<rrangle>  = \<alpha>"

text \<open>Relationship between program reordering and program forwarding\<close>
lemma fwd_com [simp]:
  assumes "\<alpha>' < c <\<^sub>c \<alpha>"
  shows "\<alpha>\<llangle>c\<rrangle> = \<alpha>'"
  using assms by (induct c arbitrary: \<alpha>' \<alpha>) auto

end

end