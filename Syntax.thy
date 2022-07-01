theory Syntax
  imports Main Push_State
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


text \<open>Functions to support Capture operations.\<close>

abbreviation (input) uncapPred where
"uncapPred s P \<equiv> pushpred s P"

abbreviation (input) capPred where
"capPred P \<equiv> poppred P"

abbreviation (input) capBeh where
"capBeh B \<equiv> poprel B" 

abbreviation (input) uncapBeh where
"uncapBeh s B \<equiv> pushrel s B" 

abbreviation (input) capRely where
"capRely R \<equiv> poprel R"

abbreviation (input) uncapRely where
"uncapRely R \<equiv> pushrelSame R"

abbreviation (input) capGuar where
"capGuar G \<equiv> poprel G"

abbreviation (input) uncapGuar where
"uncapGuar G \<equiv> pushrelAll G"

(* captures and hides the local effects of a basic. 
goes from local to global.  *)
abbreviation popbasic' where
"popbasic' s s' \<alpha> \<equiv> (tag \<alpha>, poppred' s (vc \<alpha>), poprel' s s' (beh \<alpha>))"

abbreviation popbasic where
"popbasic \<alpha> \<equiv> (tag \<alpha>, poppred (vc \<alpha>), poprel (beh \<alpha>))"

(* uncaptures and makes visible the effects of a basic. 
goes from global to local context. *)
abbreviation pushbasic where
"pushbasic s s' \<alpha> \<equiv> (tag \<alpha>, pushpred s (vc \<alpha>), pushrel s s' (beh \<alpha>))"

(* captures the effect of a command *)
(* fun popcom :: "('a,'b::state) com \<Rightarrow> ('a,'b) com" where
    "popcom (Basic \<beta>) = Basic (popbasic \<beta>)" |
    "popcom (Seq c\<^sub>1 c\<^sub>2) = Seq (popcom c\<^sub>1) (popcom c\<^sub>2)" |
    "popcom (Ord c\<^sub>1 c\<^sub>2) = Ord  (popcom c\<^sub>1) (popcom c\<^sub>2)" |
    "popcom (Choice c\<^sub>1 c\<^sub>2) = Choice  (popcom c\<^sub>1) (popcom c\<^sub>2)" |
    "popcom (SeqChoice S) = SeqChoice (map (popbasic) ` S)" |
    "popcom (Parallel c\<^sub>1 c\<^sub>2) = Parallel (popcom c\<^sub>1) (popcom c\<^sub>2)" |
    "popcom (Loop c) = Loop (popcom c)" |
    "popcom (Thread c) = Thread (popcom c)" |
    (* "popcom k (Capture s c) = pushbasic s ` popcom k c" | *)
    "popcom (Capture k' c) = c" |
    "popcom Nil = Nil" *)

(* fun pushcom :: "('b::state) \<Rightarrow> ('a,'b) com \<Rightarrow> ('a,'b) com" where
    "pushcom k (Basic \<beta>) = Basic (pushbasic k \<beta>)" |
    "pushcom k (Seq c\<^sub>1 c\<^sub>2) = Seq (pushcom k c\<^sub>1) (pushcom k c\<^sub>2)" |
    "pushcom k (Ord c\<^sub>1 c\<^sub>2) = Ord  (pushcom k c\<^sub>1) (pushcom k c\<^sub>2)" |
    "pushcom k (Choice c\<^sub>1 c\<^sub>2) = Choice  (pushcom k c\<^sub>1) (pushcom k c\<^sub>2)" |
    "pushcom k (SeqChoice S) = SeqChoice (map (pushbasic k) ` S)" |
    "pushcom k (Parallel c\<^sub>1 c\<^sub>2) = Parallel (pushcom k c\<^sub>1) (pushcom k c\<^sub>2)" |
    "pushcom k (Loop c) = Loop (pushcom k c)" |
    "pushcom k (Thread c) = Thread (pushcom k c)" |
    (* "popcom k (Capture s c) = pushbasic s ` popcom k c" | *)
    "pushcom k (Capture k' c) = Capture k' (pushcom k' c)" |
    "pushcom _ Nil = Nil"
    (* "basics (CaptureAll c) = basics c" | *) *)


(* definition thr\<^sub>\<alpha> :: "'b merge \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a,'b) basic \<Rightarrow> ('a,'b) basic" where
"thr\<^sub>\<alpha> op l l' \<alpha> \<equiv> (tag \<alpha>, thr\<^sub>P op l (vc \<alpha>), thr2glb op l l' (beh \<alpha>))"
 *)
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
    (* "basics (Capture s c) = pushbasic s ` basics c" | *)
    "basics (Capture k c) = popbasic ` basics c" |
    (* "basics (CaptureAll c) = basics c" | *)
    "basics _ = {}"


(* lemma basics_thr\<^sub>c: "basics (thr\<^sub>c op l l' c) = thr\<^sub>\<alpha> op l l' ` basics c"
by (induct c arbitrary: op l l') auto *)

text \<open>Shorthand for an environment step\<close>
abbreviation Env :: "'b rel \<Rightarrow> ('a,'b) com"
  where "Env R \<equiv> Basic (undefined,UNIV,R\<^sup>*)"

text \<open>Convert a sequence to a command\<close>
fun seq2com :: "('a,'b) seq \<Rightarrow> ('a,'b) com"
  where "seq2com [] = Nil" | "seq2com (\<alpha>#t) = Basic \<alpha> \<cdot> seq2com t"

end