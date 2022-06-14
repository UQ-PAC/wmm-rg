theory Syntax
  imports Main State
begin

chapter \<open>While Language Syntax\<close>

(* a basic step is an action, a verification condition, and a behaviour set.  *)
(* note that iterated product types are right-associated. *)
type_synonym ('a,'b) basic = "('a \<times> 'b set \<times> 'b rel)"
type_synonym ('a,'b) seq = "('a,'b) basic list"

abbreviation tag :: "('a,'b) basic \<Rightarrow> 'a"
  where "tag \<equiv> fst"

abbreviation vc :: "('a,'b) basic \<Rightarrow> 'b set"
  where "vc \<alpha> \<equiv> fst (snd \<alpha>)"

abbreviation beh :: "('a,'b) basic \<Rightarrow> 'b rel"
  where "beh \<alpha> \<equiv> snd (snd \<alpha>)"

text \<open>
A While language with non-deterministic choice, iteration and parallel composition.
Also includes special commands for environment steps, which is useful for describing
refinement properties. These have no evaluation semantics or rules however.
\<close>
datatype ('a,'b) com =
  Nil
  | Basic "('a,'b) basic"
  | Seq "('a,'b) com" "('a,'b) com" (infixr ";;" 80)
  | Ord "('a,'b) com" "('a,'b) com" (infixr "\<cdot>" 80)
  | SeqChoice "('a,'b) seq set" ("\<Sqinter> _" 150)
  | Choice "('a,'b) com" "('a,'b) com" (infixr "\<sqinter>" 150)
  | Loop "('a,'b) com" ("_*" [100] 150)
  | Parallel "('a,'b) com" "('a,'b) com"  (infixr "||" 150)
  | Thread "('a,'b) com"
  | Capture 'b "('a,'b) com"
  (* | CaptureAll "('a,'b) com" *)


text \<open>Ensure there is no parallelism within a program\<close>
fun local :: "('a,'b) com \<Rightarrow> bool"
  where 
    "local (c\<^sub>1 || c\<^sub>2) = False" |
    "local (Thread _) = False" |
    "local (c\<^sub>1 ;; c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |
    "local (c\<^sub>1 \<cdot> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |
    "local (c\<^sub>1 \<sqinter> c\<^sub>2) = (local c\<^sub>1 \<and> local c\<^sub>2)" |  
    "local (c*) = (local c)" |    
    "local (Capture k c) = local c" |
    (* "local (CaptureAll c) = local c" | *)
    "local _ = True"


class state =
  (* takes key, initial outer state, then returns inner state *)
  fixes push :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  (* takes key, initial outer state, final outer state, and returns final inner state. *)
  fixes popl :: "'a \<Rightarrow> 'a"
  fixes popr :: "'a \<Rightarrow> 'a"
  assumes popl_push [simp]: "popl (push a b) = a"
  assumes popr_push [simp]: "popr (push a b) = b"
  assumes push_intro: "\<exists>m. m' = push m s"

lemma push_intro_fun: 
  "\<exists>f. m' = push (f m' s) s"
using push_intro
by fast


fun uncapPred :: "('b::state) \<Rightarrow> 'b set \<Rightarrow> 'b set" where
"uncapPred s P = {push m s |m. m \<in> P}"

lemma uncapPred_intro:
  "\<exists>P'. P = uncapPred s P'"
proof 
  have "m = push (SOME x. m = push x s) s" for m
    using push_intro[of m s] someI_ex
    by fast
  thus "P = uncapPred s {SOME x. m = push x s |m. m \<in> P}"
    by auto
qed

fun capPred :: "('b::state) set \<Rightarrow> 'b set" where
"capPred P = {popl m |m. m \<in> P}"


fun capBeh :: "('b::state) \<Rightarrow> 'b rel \<Rightarrow> 'b rel" where
"capBeh s b = {(popl m,popl m') |m m'. (m,m') \<in> b}" 

fun uncapBeh :: "('b::state) \<Rightarrow> 'b rel \<Rightarrow> 'b rel" where
"uncapBeh s b = {(push m s,push m' s) |m m'. (m,m') \<in> b}" 


(* captures and hides the local effects of a basic. 
goes from local to global.  *)
fun capBasic :: "('b::state) \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic" where
"capBasic s \<alpha> = (tag \<alpha>, capPred (vc \<alpha>), capBeh s (beh \<alpha>))"

(* uncaptures and makes visible the effects of a basic. 
goes from global to local context. *)
fun uncapBasic :: "('b::state) \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic" where
"uncapBasic s \<alpha> = (tag \<alpha>, uncapPred s (vc \<alpha>), uncapBeh s (beh \<alpha>))"

fun capRely :: "('b::state) rel \<Rightarrow> 'b rel" where
"capRely R = {(popl m, popl m') |m m'. (m,m') \<in> R}"

fun uncapRely :: "('b::state) rel \<Rightarrow> 'b rel" where
"uncapRely R = {(push m s, push m' s) |m m' s. (m,m') \<in> R}"


fun uncapGuar :: "('b::state) rel \<Rightarrow> 'b rel" where
"uncapGuar G = {(push m s, push m' s') |m m' s s'. (m,m') \<in> G}"

fun capGuar :: "('b::state) rel \<Rightarrow> 'b rel" where
"capGuar G = {(popl m, popl m') |m m'. (m,m') \<in> G}"

lemma cap_uncapBeh: "capBeh s (uncapBeh s b) = b"
by (auto, metis popl_push)

lemma cap_uncapPred: "capPred (uncapPred s P) = P"
by (auto, metis popl_push)

lemma cap_uncapBasic: "capBasic s (uncapBasic s \<alpha>) = \<alpha>"
using cap_uncapPred[of s "vc \<alpha>"] cap_uncapBeh[of s "beh \<alpha>"]
by simp

lemma uncap_capGuar: "uncapGuar (capGuar G) = G"
by auto (metis (full_types) popr_push push_intro)+

lemma capPred_mono: "P \<subseteq> P' \<Longrightarrow> capPred P \<subseteq> capPred P'"
by auto

lemma uncapGuar_mono: "G \<subseteq> G' \<Longrightarrow> uncapGuar G \<subseteq> uncapGuar G'"
by auto

lemma uncapGuar_inter: "uncapGuar (G \<inter> G') = uncapGuar G \<inter> uncapGuar G'"
by auto (metis (full_types) popr_push push_intro)

lemma stable_uncap: "stable (uncapRely R) (uncapPred s P) \<Longrightarrow> stable R P"
unfolding stable_def
by (auto, metis popl_push)



(* captures the effect of a command *)
fun capCom :: "('b::state) \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) com" where
    "capCom k (Basic \<beta>) = Basic (capBasic k \<beta>)" |
    "capCom k (Seq c\<^sub>1 c\<^sub>2) = Seq (capCom k c\<^sub>1) (capCom k c\<^sub>2)" |
    "capCom k (Ord c\<^sub>1 c\<^sub>2) = Ord  (capCom k c\<^sub>1) (capCom k c\<^sub>2)" |
    "capCom k (Choice c\<^sub>1 c\<^sub>2) = Choice  (capCom k c\<^sub>1) (capCom k c\<^sub>2)" |
    "capCom k (SeqChoice S) = SeqChoice (map (uncapBasic k) ` S)" |
    "capCom k (Parallel c\<^sub>1 c\<^sub>2) = Parallel (capCom k c\<^sub>1) (capCom k c\<^sub>2)" |
    "capCom k (Loop c) = Loop (capCom k c)" |
    "capCom k (Thread c) = Thread (capCom k c)" |
    (* "capCom k (Capture s c) = uncapBasic s ` capCom k c" | *)
    "capCom k (Capture k' c) = Capture k (capCom k' c)" |
    "capCom _ Nil = Nil"

fun uncapCom :: "('b::state) \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) com" where
    "uncapCom k (Basic \<beta>) = Basic (uncapBasic k \<beta>)" |
    "uncapCom k (Seq c\<^sub>1 c\<^sub>2) = Seq (uncapCom k c\<^sub>1) (uncapCom k c\<^sub>2)" |
    "uncapCom k (Ord c\<^sub>1 c\<^sub>2) = Ord  (uncapCom k c\<^sub>1) (uncapCom k c\<^sub>2)" |
    "uncapCom k (Choice c\<^sub>1 c\<^sub>2) = Choice  (uncapCom k c\<^sub>1) (uncapCom k c\<^sub>2)" |
    "uncapCom k (SeqChoice S) = SeqChoice (map (uncapBasic k) ` S)" |
    "uncapCom k (Parallel c\<^sub>1 c\<^sub>2) = Parallel (uncapCom k c\<^sub>1) (uncapCom k c\<^sub>2)" |
    "uncapCom k (Loop c) = Loop (uncapCom k c)" |
    "uncapCom k (Thread c) = Thread (uncapCom k c)" |
    (* "capCom k (Capture s c) = uncapBasic s ` capCom k c" | *)
    "uncapCom k (Capture k' c) = Capture k' (uncapCom k' c)" |
    "uncapCom _ Nil = Nil"
    (* "basics (CaptureAll c) = basics c" | *)


definition thr\<^sub>\<alpha> :: "'b merge \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic" where
"thr\<^sub>\<alpha> op l l' \<alpha> \<equiv> (tag \<alpha>, thr\<^sub>P op l (vc \<alpha>), thr2glb op l l' (beh \<alpha>))"

(* fun thr\<^sub>c :: "'b merge \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) com" where
"thr\<^sub>c op l l' (Basic \<beta>) = Basic (thr\<^sub>\<alpha> op l l' \<beta>)" |
"thr\<^sub>c op l l' (Seq c\<^sub>1 c\<^sub>2) = Seq (thr\<^sub>c op l l' c\<^sub>1) (thr\<^sub>c op l l' c\<^sub>2)" |
"thr\<^sub>c op l l' (Ord c\<^sub>1 c\<^sub>2) = Ord (thr\<^sub>c op l l' c\<^sub>1) (thr\<^sub>c op l l' c\<^sub>2)" |
"thr\<^sub>c op l l' (Choice c\<^sub>1 c\<^sub>2) = Choice (thr\<^sub>c op l l' c\<^sub>1) (thr\<^sub>c op l l' c\<^sub>2)" |
"thr\<^sub>c op l l' (SeqChoice S) = SeqChoice (map (thr\<^sub>\<alpha> op l l') ` S)" |
"thr\<^sub>c op l l' (Parallel c\<^sub>1 c\<^sub>2) = Parallel (thr\<^sub>c op l l' c\<^sub>1) (thr\<^sub>c op l l' c\<^sub>2)" |
"thr\<^sub>c op l l' (Loop c) = Loop (thr\<^sub>c op l l' c)" |
"thr\<^sub>c op l l' (Thread c) = Thread (thr\<^sub>c op l l' c)" |
"thr\<^sub>c op l l' (Capture op2 k k' c) = Capture op l l' (thr\<^sub>c op2 k k' c)" |
"thr\<^sub>c op l l' Nil = Nil" *)
(* "basics (CaptureAll c) = basics c" | *)

text \<open>Identify all operations in a program\<close>
fun basics :: "('a,'b::state) com \<Rightarrow> ('a,'b) basic set"
  where
    "basics (Basic \<beta>) = {\<beta>}" |
    "basics (Seq c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Ord c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Choice c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (SeqChoice S) = (\<Union>s \<in> S. set s)" |
    "basics (Parallel c\<^sub>1 c\<^sub>2) = basics c\<^sub>1 \<union> basics c\<^sub>2" |
    "basics (Loop c) = basics c" |
    "basics (Thread c) = basics c" |
    (* "basics (Capture s c) = uncapBasic s ` basics c" | *)
    "basics (Capture k c) = capBasic k ` basics c" |
    (* "basics (CaptureAll c) = basics c" | *)
    "basics _ = {}"

fun seqonly :: "('a,'b) com \<Rightarrow> bool" where
"seqonly Nil = True" |
"seqonly (Basic _) = True" |
"seqonly (Seq c1 c2) = (seqonly c1 \<and> seqonly c2)" |
"seqonly (Ord c1 c2) = (seqonly c1 \<and> seqonly c2)" |
"seqonly _ = False"


(* lemma basics_thr\<^sub>c: "basics (thr\<^sub>c op l l' c) = thr\<^sub>\<alpha> op l l' ` basics c"
by (induct c arbitrary: op l l') auto *)

text \<open>Shorthand for an environment step\<close>
abbreviation Env :: "'b rel \<Rightarrow> ('a,'b) com"
  where "Env R \<equiv> Basic (undefined,UNIV,R\<^sup>*)"

text \<open>Convert a sequence to a command\<close>
fun seq2com :: "('a,'b) seq \<Rightarrow> ('a,'b) com"
  where "seq2com [] = Nil" | "seq2com (\<alpha>#t) = Basic \<alpha> \<cdot> seq2com t"

end