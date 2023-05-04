theory SimAsm_StateStack
  imports Main State2
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

type_synonym ('var,'val,'a) stack = "('var, 'val,'a) frame_scheme list" 

definition Is_tstack :: "('var,'val,'a) stack \<Rightarrow> bool" where 
  "Is_tstack t \<equiv> t \<noteq> [] \<and> frame_cap (last t) = UNIV \<and> (\<forall>v. frame_st (last t) v \<noteq> None)"

lemma Is_tstack_ConsI [intro]: "Is_tstack xs \<Longrightarrow> Is_tstack (x#xs)" 
  unfolding Is_tstack_def  
  by auto

lemma Is_tstack_ConsE [intro]: "xs \<noteq> [] \<Longrightarrow> Is_tstack (x#xs) \<Longrightarrow> Is_tstack xs" 
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

(* declare Abs_tstack_inverse[intro] *)

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


fun lookup :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> 'val" where 
  "lookup [] v = undefined" |
  "lookup (f#fs) v = (if v \<in> frame_cap f then (case (frame_st f v) of None \<Rightarrow> lookup fs v | Some x \<Rightarrow> x) else lookup fs v)"
(* it is important that lookup ignores values from frames where v is not captured. *)
  
fun update :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val,'a) stack" where 
  "update [] _ _ = undefined" |
  "update (f#fs) v x = (if (v \<in> frame_cap f) then (f\<lparr>frame_st := (frame_st f)(v \<mapsto> x)\<rparr>)#fs else f#update fs v x)"

definition tlookup :: "('var,'val,'a) tstack \<Rightarrow> 'var \<Rightarrow> 'val" where 
  "tlookup fs v = lookup (Rep_tstack fs) v"
  
definition tupdate :: "('var,'val,'a) tstack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val,'a) tstack" where 
  "tupdate fs v x = Abs_tstack (update (Rep_tstack fs) v x)"

definition taux :: "('var,'val,'a) tstack \<Rightarrow> 'a" where 
  "taux s = more (last (Rep_tstack s))"

definition auxupd where 
  "auxupd s f = butlast s @ [(last s)\<lparr> more := f s \<rparr>]"
  
definition tauxupd :: "('var,'val,'a) tstack \<Rightarrow> (('var,'val,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('var,'val,'a) tstack" where 
  "tauxupd s f = Abs_tstack (auxupd (Rep_tstack s) (\<lambda>x. f (Abs_tstack x)))"

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

lemma aux_update: 
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

lemma auxupd_Cons [simp]:
  "Is_tstack xs \<Longrightarrow> auxupd (x#xs) f = x # auxupd xs f"
unfolding auxupd_def 
apply auto 
sledgehammr
(* OH NO DOES NOT WORK WITH CONS DUE TO PARAM OF F*)


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


interpretation stack: state
  "tlookup"
  tupdate
  "taux" 
  "tauxupd"
  "id" 
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
  next
    case (Frame x xs)
    then show ?case
    by (metis Abs_tstack_inverse CollectI Is_tstack_ConsI Is_tstack_update aux_update id_apply taux_def tupdate_def)
  qed
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
  then show ?case 
  proof (induct s rule: tstack_induct)
    case (Base x)
    moreover hence "Is_tstack (auxupd [x] (\<lambda>x. f (Abs_tstack x)))" by auto
    ultimately show ?case 
    proof (cases "frame_st x v")
      case None
      hence False using Base by blast
      then show ?thesis by simp 
    next
      case (Some a)
      then show ?thesis 
        unfolding tlookup_def tauxupd_def 
        using Base Is_tstack_auxupd 
        by (auto simp add: Is_tstack_def auxupd_def)
    qed
  next
    case (Frame x xs)
    moreover hence 1: "Is_tstack (x#xs)" by auto  
    moreover hence 2: "Is_tstack (auxupd (x # xs) (\<lambda>x. f (Abs_tstack x)))" by auto
    moreover have 3: "lookup ( (auxupd ( xs) (\<lambda>x. f (Abs_tstack x)))) v = lookup ( xs) v"
      using 1 2 Frame unfolding tlookup_def tauxupd_def
      by (simp add: Is_tstack_auxupd)
    moreover hence " lookup ( (auxupd ( (x # xs)) (\<lambda>x. f (Abs_tstack x)))) v = lookup ( (x # xs)) v" 
    apply (cases "frame_st x v")
    apply auto
    apply auto
    using Frame(1) 1 2
    
    
    

  qed 
qed 

thm list.induct

end

