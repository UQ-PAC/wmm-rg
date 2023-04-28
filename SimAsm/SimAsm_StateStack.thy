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

type_synonym ('var,'val) stack = "('var, 'val) frame list" 

abbreviation Pred_tstack :: "('var,'val) stack \<Rightarrow> bool" where 
  "Pred_tstack t \<equiv> t \<noteq> [] \<and> (\<forall>v. frame_st (last t) v \<noteq> None) \<and> frame_cap (last t) = UNIV"

typedef ('var,'val) tstack = "{t :: ('var,'val) stack. Pred_tstack t}"
proof (standard, clarify, intro conjI allI)
  fix x
  let ?f = "\<lparr>frame_st = \<lambda>_. Some x, frame_cap = UNIV\<rparr> :: ('var,'val) frame" 
  have last: "last [?f] = ?f" using last_ConsL by fast
  show "[?f] \<noteq> []" by fast
  show "frame_st (last [?f]) v \<noteq> None" for v
    unfolding last select_convs(1) by simp
  show "frame_cap (last [?f]) = UNIV"
    unfolding last select_convs(2) by simp
qed

abbreviation Is_tstack where 
  "Is_tstack fs \<equiv> Pred_tstack (Rep_tstack fs)"

fun lookup :: "('var,'val) stack \<Rightarrow> 'var \<Rightarrow> 'val" where 
  "lookup [] v = undefined" |
  "lookup (f#fs) v = (if v \<in> frame_cap f then (case (frame_st f v) of None \<Rightarrow> lookup fs v | Some x \<Rightarrow> x) else lookup fs v)"
(* it is important that lookup ignores values from frames where v is not captured. *)
  
fun update :: "('var,'val) stack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val) stack" where 
  "update [] _ _ = undefined" |
  "update (f#fs) v x = (if (v \<in> frame_cap f) then (f\<lparr>frame_st := (frame_st f)(v \<mapsto> x)\<rparr>)#fs else f#update fs v x)"

definition tlookup :: "('var,'val) tstack \<Rightarrow> 'var \<Rightarrow> 'val" where 
  "tlookup fs v = lookup (Rep_tstack fs) v"

lemma Pred_tstack_Cons: "Pred_tstack xs \<Longrightarrow> Pred_tstack (x#xs)" 
  by auto
  
definition tupdate :: "('var,'val) tstack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val) tstack" where 
  "tupdate fs v x = Abs_tstack (update (Rep_tstack fs) v x)"

lemma [intro!, simp]: "Is_tstack x" 
  by induct (simp add: Abs_tstack_inverse)

lemma Pred_tstack_update [intro!,simp]: "Pred_tstack (update (Rep_tstack fs) v x)" 
apply (induct fs; simp only: Abs_tstack_inverse)
proof (goal_cases)
  case (1 y)
  then show ?case 
  proof (induct y rule: list.induct)
    case (Cons x1 x2)
    then show ?case by (cases x2) auto
  qed auto
qed

find_theorems lookup
thm lookup.simps

lemma lookup_fun_upd: 
  assumes "Pred_tstack s"
  shows "lookup (update (s) var val) = (lookup s)(var := val)" 
using assms
proof (induct s)
  case (Cons a s)
  then show ?case 
  proof (cases "var \<in> frame_cap a")
    case False
    then show ?thesis 
    apply (simp only: update.simps)
    apply standard
    apply auto
    apply (case_tac "frame_st a x")
    apply auto
    apply (metis Cons.hyps Cons.prems fun_upd_other last.simps)
    apply (metis Cons.hyps Cons.prems fun_upd_same iso_tuple_UNIV_I last.simps)
    by (metis Cons.hyps Cons.prems UNIV_I fun_upd_other last.simps) (* TODO: clean cases *)
  qed auto
qed auto

lemma lookup_update2:
  assumes "Pred_tstack s"
  shows  "lookup (update (s) var val) var2 = (if var2 = var then val else lookup (s) var2)"
using lookup_fun_upd assms
by fastforce
  
find_theorems Abs_tstack
  
thm type_definition_tstack
  
interpretation stack: state
  "tlookup"
  tupdate
  "\<lambda>x. ()" 
  "\<lambda>x y. x"
  "\<lambda>x. ()" 
proof (unfold_locales, goal_cases)
  case (1 s var val var2)
  have "Pred_tstack (Rep_tstack s)" by simp
  hence "lookup (update (Rep_tstack s) var val) var2 = (if var2 = var then val else lookup (Rep_tstack s) var2)" 
    using lookup_update2[of "Rep_tstack s"] by simp 
  moreover have "Rep_tstack (Abs_tstack (update (Rep_tstack s) var val)) = update (Rep_tstack s) var val" 
    using Abs_tstack_inverse Pred_tstack_update by blast
  ultimately show ?case 
    unfolding tlookup_def tupdate_def by simp
qed (metis (full_types) unit.exhaust)+

  
end

