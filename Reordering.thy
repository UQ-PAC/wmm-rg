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
  fixes fwd :: "('a,'b::state) basic \<Rightarrow> 'a \<Rightarrow> ('a,'b) basic" ("_\<langle>_\<rangle>" [1000,0] 1000)
  and re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100)
  assumes tag_fwd: "tag a = tag b \<Longrightarrow> tag a\<langle>c\<rangle> = tag b\<langle>c\<rangle>"

context reordering
begin

text \<open>Combine forwarding and reordering into a single definition\<close>
abbreviation reorder_inst :: "('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  ("_ < _ <\<^sub>a _" [100,0,100] 100)
  where "\<beta>' < \<alpha> <\<^sub>a \<beta> \<equiv> \<beta>' = \<beta>\<langle>tag \<alpha>\<rangle> \<and> tag \<alpha> \<hookleftarrow> (tag \<beta>\<langle>tag \<alpha>\<rangle>)"

text \<open>Recursively define forwarding of an instruction across a program\<close>
fun fwd_com :: "('a,'b) basic \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) basic"
  ("_\<llangle>_\<rrangle>" [1000,0] 1000)
  where
    "\<alpha>\<llangle>Nil\<rrangle> = \<alpha>" |
    "\<alpha>\<llangle>Basic \<beta>\<rrangle> = \<alpha>\<langle>tag \<beta>\<rangle>" |            
    "\<alpha>\<llangle>c\<^sub>1 ;; c\<^sub>2\<rrangle> = \<alpha>\<llangle>c\<^sub>2\<rrangle>\<llangle>c\<^sub>1\<rrangle>" |
    "\<alpha>\<llangle>c\<^sub>1 \<cdot> c\<^sub>2\<rrangle> = \<alpha>\<llangle>c\<^sub>2\<rrangle>\<llangle>c\<^sub>1\<rrangle>" |
    "\<alpha>\<llangle>_\<rrangle> = \<alpha>"
(* TODO: we should define \<alpha>\<llangle>Capture s r\<rrangle> = unpush s \<alpha>\<llangle>r\<rrangle> or similar with a specific s. *)

text \<open>Recursively define reordering of an instruction earlier than a program\<close>
fun reorder_com :: "('a,'b) basic \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) basic \<Rightarrow> bool"
  ("_ < _ <\<^sub>c _" [100,0,100] 100)
  where
    "\<alpha>' < Nil <\<^sub>c \<alpha> = (\<alpha>' = \<alpha>)" |
    "\<alpha>' < Basic \<beta> <\<^sub>c \<alpha> = (\<alpha>' < \<beta> <\<^sub>a \<alpha>)" |
    "\<alpha>' < c\<^sub>1 ;; c\<^sub>2 <\<^sub>c \<alpha> = (\<exists>\<alpha>\<^sub>n. \<alpha>' < c\<^sub>1 <\<^sub>c \<alpha>\<^sub>n \<and> \<alpha>\<^sub>n < c\<^sub>2 <\<^sub>c \<alpha>)" |
    "\<alpha>' < c\<^sub>1 \<cdot> c\<^sub>2 <\<^sub>c \<alpha> = (\<exists>\<alpha>\<^sub>n. \<alpha>' < c\<^sub>1 <\<^sub>c \<alpha>\<^sub>n \<and> \<alpha>\<^sub>n < c\<^sub>2 <\<^sub>c \<alpha>)" |
    "_ < _ <\<^sub>c _ = False"

fun reorder_list :: "('a,'b) basic \<Rightarrow> ('a,'b) basic list \<Rightarrow> ('a,'b) basic \<Rightarrow> bool" 
  ("_ < _ <<\<^sub>c _" [100,0,100] 100)
  where
    "\<alpha>' < [] <<\<^sub>c \<alpha> = (\<alpha>' = \<alpha>)" |
    "\<alpha>' < (x#xs) <<\<^sub>c \<alpha> = (\<exists>\<alpha>\<^sub>n. \<alpha>' < x <\<^sub>a \<alpha>\<^sub>n \<and> \<alpha>\<^sub>n < xs <<\<^sub>c \<alpha>)"

fun list_to_com :: "('a,'b) basic list \<Rightarrow> ('a,'b) com" where
"list_to_com [] = Nil" |
"list_to_com (x#xs) = Basic x ;; list_to_com xs" 

lemma "\<alpha>' < list_to_com bs <\<^sub>c \<alpha> = \<alpha>' < bs <<\<^sub>c \<alpha>"
by (induct bs arbitrary: \<alpha>' \<alpha>, auto)


text \<open>Relationship between program reordering and program forwarding\<close>
lemma fwd_com [simp]:
  assumes "\<alpha>' < c <\<^sub>c \<alpha>"
  shows "\<alpha>\<llangle>c\<rrangle> = \<alpha>'"
  using assms by (induct c arbitrary: \<alpha>' \<alpha>) auto

lemma fwd_com2 [simp]:
  assumes "\<alpha>' < c <<\<^sub>c \<alpha>"
  shows "\<alpha>\<llangle>list_to_com c\<rrangle> = \<alpha>'"
  using assms by (induct c arbitrary: \<alpha>' \<alpha>) auto


end

end