theory SimAsm_StateStack
  imports Main 
begin

section \<open>State Stacks\<close>

text \<open> 
The ('var,'val) stack type is a list of stack frames, with the deepest stack frame last. 
Each frame has:
 - a mapping for variables to optional values, and
 - a set of variables which are captured within the frame. 
This describes a notion of "scoping" which is similar to a call stack. 

Moreover, the capturing set can be used to represent different "types" of frames, 
such as function calls with local variables, speculative execution, and thread-local frames. 

To facilitate this, we create an abstract subtype ('var,'val) tstack (for "total stack") 
which adds constraints onto the stack type such that it is a well-formed state (in the sense
of the state locale and var map). 

Specifically, tstack constrains the stack to be non-empty and totally defined at its last level.
That is, the last level must capture everything and all its values are non-none.
\<close>

record ('var,'val) frame =
  frame_st :: "'var \<Rightarrow> 'val option" 
  frame_cap :: "'var set" 


  
(* lemma Quotient_frame [quot_map]: *)
(* assumes Q1: "Quotient R1 Abs1 Rep1 T1" *)
(* and Q2: "Quotient R2 Abs2 Rep2 T2" *)
(* shows "Quotient (poly_mapping_rel R1 R2) (map_poly_mapping Rep1 Abs2) (map_poly_mapping *)
(* Abs1 Rep2) (poly_mapping_rel T1 T2)" *)
(* sorry  *)
  
setup_lifting type_definition_frame_ext
copy_bnf ('a,'b,'c) frame_ext
print_quot_maps
  
type_synonym ('var,'val,'a) stack = "('var, 'val,'a) frame_scheme list" 

definition emptyFrame :: "'var set \<Rightarrow> ('var,'val) frame" where
  "emptyFrame cap \<equiv> \<lparr> frame_st = (\<lambda>v. None),
                  frame_cap = cap \<rparr>"            (* is cap set as parameter *)

definition Is_tstack :: "('var,'val,'a) stack \<Rightarrow> bool" where 
  "Is_tstack t \<equiv> t \<noteq> [] \<and> frame_cap (last t) = UNIV \<and> (\<forall>v. frame_st (last t) v \<noteq> None)"

lemma Is_tstack_ConsI [intro]: "Is_tstack xs \<Longrightarrow> Is_tstack (x#xs)" 
unfolding Is_tstack_def  
by auto

lemma Is_tstack_ConsE [intro]: "xs \<noteq> [] \<Longrightarrow> Is_tstack (x#xs) \<Longrightarrow> Is_tstack xs" 
unfolding Is_tstack_def  
by auto                          

lemma Is_tstack_snocE [intro]: "Is_tstack (xs @ [x]) \<Longrightarrow> Is_tstack [x]"
unfolding Is_tstack_def  
by auto                          


lemma Is_tstack_NilE [elim!,dest!]: "Is_tstack [] \<Longrightarrow> False" 
unfolding Is_tstack_def
by auto  

lemma Is_tstackE [elim,dest]:
  assumes "Is_tstack s"  
  shows "s \<noteq> []" "x \<in> frame_cap (last s)" "frame_st (last s) v \<noteq> None" 
using assms
unfolding Is_tstack_def
by auto

lemma Is_tstack_notcap [intro]: 
  assumes "v \<notin> frame_cap x" "Is_tstack (x#xs)"
  shows "Is_tstack xs" 
proof - 
  have "xs \<noteq> []" using assms unfolding Is_tstack_def by auto
  thus ?thesis using assms unfolding Is_tstack_def by simp
qed

lemma Is_tstack_baseNone [intro]: "frame_st s v = None \<Longrightarrow> Is_tstack [s] \<Longrightarrow> False"
  unfolding Is_tstack_def
  by (metis last_ConsL)  

typedef ('var,'val,'a) tstack = "{t :: ('var,'val,'a) stack. Is_tstack t}"
unfolding Is_tstack_def
proof (standard, clarify, intro conjI allI)
  fix x a
  let ?f = "\<lparr>frame_st = \<lambda>_. Some x, frame_cap = UNIV, \<dots> = a\<rparr> :: ('var,'val,'a) frame_scheme" 
  have last: "last [?f] = ?f" using last_ConsL by fast
  show "[?f] \<noteq> []" by fast
  show "frame_st (last [?f]) v \<noteq> None" for v
    unfolding last select_convs(1) by simp
  show "frame_cap (last [?f]) = UNIV"
    unfolding last select_convs(2) by simp
qed

setup_lifting type_definition_tstack    

(* declare Abs_tstack_inverse[intro] *)
find_theorems Abs_tstack

abbreviation RepAbs_tstack where 
  "RepAbs_tstack s \<equiv> Rep_tstack (Abs_tstack s)"

lemma RepAbs_id [intro,simp]:
  "Is_tstack s \<Longrightarrow> RepAbs_tstack s = s" 
by (auto intro: Abs_tstack_inverse)

lemma Rep_tstackI [intro!]:
  shows 
    "Rep_tstack s \<noteq> []" 
    "x \<in> frame_cap (last (Rep_tstack s))" 
    "frame_st (last (Rep_tstack s)) v \<noteq> None" 
by (induct s) (auto simp add: Abs_tstack_inverse)

lemma Is_tstack_induct [case_names Base Frame Is_tstack]:
assumes "\<And>x. Is_tstack [x] \<Longrightarrow> P [x]"
assumes "\<And>x xs. P xs \<Longrightarrow> Is_tstack xs \<Longrightarrow> P (x#xs)"
assumes "Is_tstack s"
shows "P s"
using assms
proof (induct s)
  case (Cons a s)
  thus ?case 
  by (cases s) (auto intro: assms)
qed auto

lemma tstack_induct [case_names Base Frame]: 
assumes "\<And>x. Is_tstack [x] \<Longrightarrow> P (Abs_tstack [x])"
assumes "\<And>x xs. P (Abs_tstack xs) \<Longrightarrow> Is_tstack xs \<Longrightarrow> P (Abs_tstack (x#xs))"
shows "P s"
proof (induct s)
  case (Abs_tstack y)
  thus ?case 
  using assms
  proof (induct rule: Is_tstack_induct)
    case (Is_tstack)
    thus ?case using Abs_tstack by auto
  qed auto
qed 

lemma Is_tstack_snoc: "Is_tstack xs \<Longrightarrow> Is_tstack (butlast xs @ [last xs])"
unfolding Is_tstack_def by simp

lemma Is_tstack_snoc_moreupd: "Is_tstack xs \<Longrightarrow> Is_tstack (butlast xs @ [last xs\<lparr> more := any \<rparr>])"
unfolding Is_tstack_def by simp


fun lookup :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> 'val" where 
  "lookup [] v = undefined" |
  "lookup (f#fs) v = (if v \<in> frame_cap f then (case (frame_st f v) of None \<Rightarrow> lookup fs v | Some x \<Rightarrow> x) else lookup fs v)"
(* it is important that lookup ignores values from frames where v is not captured. *)
  
fun update :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val,'a) stack" where 
  "update [] _ _ = undefined" |
  "update (f#fs) v x = (if (v \<in> frame_cap f) then (f\<lparr>frame_st := (frame_st f)(v \<mapsto> x)\<rparr>)#fs else f#update fs v x)"

lift_definition tlookup :: "('var,'val,'a) tstack \<Rightarrow> 'var \<Rightarrow> 'val" 
  is "\<lambda>fs v. lookup (Rep_tstack fs) v".
  
lift_definition tupdate :: "('var,'val,'a) tstack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val,'a) tstack"
  is "\<lambda>fs v x. Abs_tstack (update (Rep_tstack fs) v x)".

lift_definition taux :: "('var,'val,'a) tstack \<Rightarrow> 'a" is
  "\<lambda>s. more (last (Rep_tstack s))".

definition auxupd :: "('var,'val,'a) stack \<Rightarrow> (('var,'val,'a) stack \<Rightarrow> 'a) \<Rightarrow> ('var,'val,'a) stack" where 
  "auxupd s f = butlast s @ [(last s)\<lparr> more := f s \<rparr>]"
  
lift_definition tauxupd :: "('var,'val,'a) tstack \<Rightarrow> (('var,'val,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('var,'val,'a) tstack" 
  is "\<lambda>s f. Abs_tstack (auxupd (Rep_tstack s) (\<lambda>tstack. f (Abs_tstack tstack)))".

lemma [intro!, simp]: "Is_tstack (Rep_tstack s)" 
using Rep_tstack by auto

lemma Is_tstack_update: 
  assumes "Is_tstack s"
  shows "Is_tstack (update s v x)" 
proof (induct s rule: Is_tstack_induct)
  case (Base x)
  then show ?case unfolding Is_tstack_def by simp
qed (auto simp add: assms)

lemma Is_tstack_update2 [intro!,simp]: "Is_tstack (update (Rep_tstack fs) v x)" 
by (simp add: Is_tstack_update)

lemma Is_tstack_upd_len: "Is_tstack s \<Longrightarrow> length (update s v x) = length s" 
proof (induct s)
  case (Cons a s)
  then show ?case
  proof (cases "v \<in> frame_cap a")
    case False
    have "Is_tstack s"
    using False Cons.prems by (rule Is_tstack_notcap)
    then show ?thesis 
      by (simp add: False Cons)
  qed auto  
qed auto

lemma Is_tstack_auxupd [intro]: 
assumes "Is_tstack s" 
shows "Is_tstack (auxupd s f)"
apply (induct s rule: Is_tstack_induct)
using assms unfolding Is_tstack_def auxupd_def by auto
  

find_theorems lookup
thm ext

lemma lookup_fun_upd: 
  assumes "Is_tstack s"
  shows "lookup (update (s) var val) = (lookup s)(var := val)" 
using assms
proof (intro ext; induct s)
  case (Cons a s)
  then show ?case
  proof (cases "var \<in> frame_cap a")
    case False
    hence "Is_tstack s" 
      using Is_tstack_notcap Cons.prems by auto
    thus ?thesis
      using Cons by (cases "frame_st a x") auto
  qed auto
qed auto

lemma lookup_update2:
  assumes "Is_tstack s"
  shows  "lookup (update (s) var val) var2 = (if var2 = var then val else lookup (s) var2)"
using lookup_fun_upd assms
by fastforce
  
find_theorems Abs_tstack
  
thm type_definition_tstack
term more 

lemma aux_update [simp]: 
  shows "Is_tstack s \<Longrightarrow> more (last (update s v x)) = more (last s)"
proof (induct s)
  case (Cons a s)
  then show ?case 
  proof (cases "v \<in> frame_cap a")
    case False
    have s: "Is_tstack s"
      using False Cons.prems by (rule Is_tstack_notcap)
    hence "s \<noteq> []" by auto
    moreover hence "update s v x \<noteq> []"
      using Is_tstack_upd_len s length_0_conv by metis 
    moreover have "more (last (update s v x)) = more (last (s))"
      using Cons s by simp
    ultimately show ?thesis by simp    
  qed auto
qed auto

lemma aux_tupdate [simp]:
  shows "more (last (Rep_tstack (tupdate s v x))) = more (last (Rep_tstack s))"
proof (induct s rule: tstack_induct)
  case (Base s)
  hence "Is_tstack (update [s] v x)" by (rule Is_tstack_update)
  thus ?case unfolding tupdate_def using Base by auto
next
  case (Frame x xs)
  hence "Is_tstack (x#xs)" by auto
  thus ?case unfolding tupdate_def using Frame 
    by (simp_all add: Is_tstackE(1) Is_tstack_ConsI Is_tstack_update aux_update)
qed

lemma auxupd_Cons:
  "xs \<noteq> [] \<Longrightarrow> auxupd (x#xs) f = x # auxupd xs (\<lambda>xs. f (x#xs))"
unfolding auxupd_def 
by auto



lemma tauxupd_id [simp]: 
  "tauxupd s taux = s"
unfolding tauxupd_def taux_def auxupd_def
using Rep_tstackI(1)[of s]
by (induct s) (auto simp add: Abs_tstack_inverse)

lemma taux_tupd [simp]: 
  "taux (tupdate s v x) = taux s" 
unfolding taux_def tupdate_def
proof (induct s rule: tstack_induct)
  case (Base x)
  then show ?case
    using RepAbs_id[OF Base] RepAbs_id[OF Is_tstack_update[OF Base]] aux_update 
    by auto
next
  case (Frame x xs)
  then show ?case
  using aux_update by fastforce
qed  

lemma tlookup_tauxupd [simp]:
  "tlookup (tauxupd s f) v = tlookup s v" 
unfolding tlookup_def tauxupd_def
proof (induct s arbitrary: f v rule: tstack_induct)
  case (Base x)
  then show ?case unfolding auxupd_def by (simp add: Is_tstack_def)
next
  case (Frame x xs)
  hence "xs \<noteq> []" by auto
  with Frame have 1: "Is_tstack (x#xs)" by auto
  with Frame have 2: "Is_tstack (auxupd (xs) (\<lambda>x. f (Abs_tstack x)))" by auto
  with 1 have 3: "Is_tstack (auxupd (x # xs) (\<lambda>x. f (Abs_tstack x)))" by auto
  note Is_tstack = \<open>Is_tstack xs\<close> 1 2 3 
  
  have "lookup (auxupd xs (\<lambda>xx. f (Abs_tstack (x#RepAbs_tstack xx)))) v = lookup xs v"
    using Is_tstack Frame(1)[of "\<lambda>y. f (Abs_tstack (x#(Rep_tstack y)))"]
    by (simp add: Is_tstack_auxupd)
  hence "lookup ( (auxupd xs (\<lambda>xx. f (Abs_tstack (x#xx))))) v = lookup ( xs) v"
    by (simp add: Is_tstack(1) auxupd_def)

  hence "lookup (x # auxupd xs (\<lambda>y. f (Abs_tstack (x#y)))) v = lookup (x # xs) v" 
    by (cases "frame_st x v") auto
  hence "lookup (auxupd (x # xs) (\<lambda>x. f (Abs_tstack x))) v = lookup (x # xs) v"
    using \<open>xs \<noteq> []\<close> auxupd_Cons by (simp add: auxupd_def)
  then show ?case using Is_tstack by simp
qed


lift_definition tstack_push :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v) frame \<Rightarrow> ('r,'v,'a) tstack"
is
  "\<lambda>stack frame. Abs_tstack (\<lparr>frame_st = frame_st frame, frame_cap = frame_cap frame, \<dots> = undefined \<rparr> # Rep_tstack stack)"
  .

lift_definition tstack_top :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) frame_scheme"
is
  "\<lambda>stack. hd (Rep_tstack stack)".

definition tstack_base_st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v" where
"tstack_base_st ts = the \<circ> frame_st (last (Rep_tstack ts))"

definition tstack_len :: "('r,'v,'a) tstack \<Rightarrow> nat" where
"tstack_len ts = length (Rep_tstack ts)"

lift_definition tstack_upper :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) frame_scheme list" is
"\<lambda>ts. butlast (Rep_tstack ts)".
  

(*
interpretation stack: state
  "tlookup"
  tupdate
  "taux" 
  "tauxupd"
(*  "id"  *)
proof (unfold_locales, goal_cases)
  case (1 s var val var2)
  have "lookup (update (Rep_tstack s) var val) var2 = (if var2 = var then val else lookup (Rep_tstack s) var2)" 
    using lookup_update2[of "Rep_tstack s"] by simp
  moreover have "Rep_tstack (Abs_tstack (update (Rep_tstack s) var val)) = update (Rep_tstack s) var val" 
    using Abs_tstack_inverse Is_tstack_update by blast
  ultimately show ?case 
  unfolding tlookup_def tupdate_def by simp
next                                          
  case (2 s v x)
  then show ?case 
  proof (induct s rule: tstack_induct)
    case (Base x')
    hence "RepAbs_tstack [x'] = [x']" by auto
    moreover have "Is_tstack (update [x'] v x)" using Is_tstack_update[OF Base].
    moreover hence "RepAbs_tstack (update [x'] v x) = update [x'] v x" by auto
    ultimately show ?case 
      unfolding taux_def tupdate_def using Base 
      by auto
  qed simp
next
  case (3 s f)
  then show ?case 
  proof (induct s rule: tstack_induct)
    case (Base x)
    hence auxupd: "Is_tstack (auxupd [x] (\<lambda>x. f (Abs_tstack x)))" by auto
    have "more (last (auxupd [x] (\<lambda>x. f (Abs_tstack x)))) = f (Abs_tstack [x])"
      unfolding auxupd_def by auto
    then show ?case
      unfolding taux_def tauxupd_def by (simp add: Base auxupd)
  next
    case (Frame x xs)
    hence "Is_tstack (x#xs)" by auto
    moreover hence "RepAbs_tstack (x#xs) = x#xs" by auto
    moreover have "Is_tstack (auxupd (x#xs) (\<lambda>x. f (Abs_tstack x)))" using Frame by auto
    ultimately show ?case unfolding taux_def tauxupd_def auxupd_def by auto
  qed
next
  case (4 s f v)
  then show ?case by simp
qed 
*)


end

