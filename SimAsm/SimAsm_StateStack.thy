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
  
type_synonym ('var,'val,'a) stack = "('var, 'val,'a option) frame_scheme list"

definition emptyFrame :: "'var set \<Rightarrow> ('var,'val,'a option) frame_scheme" where
  "emptyFrame cap \<equiv> \<lparr> frame_st = (\<lambda>v. None),
                      frame_cap = cap,
                      \<dots> = None \<rparr>"            (* is cap set as parameter *)

definition Is_tstack :: "('var,'val,'a) stack \<Rightarrow> bool" where 
  "Is_tstack t \<equiv> t \<noteq> [] \<and> frame_cap (last t) = UNIV \<and> (\<forall>v. frame_st (last t) v \<noteq> None) \<and> more (last t) \<noteq> None"

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
  let ?f = "\<lparr>frame_st = \<lambda>_. Some x, frame_cap = UNIV, \<dots> = Some a\<rparr> :: ('var,'val,'a option) frame_scheme"
  have last: "last [?f] = ?f" using last_ConsL by fast
  show "[?f] \<noteq> []" by fast
  show "frame_st (last [?f]) v \<noteq> None" for v
    unfolding last select_convs(1) by simp
  show "frame_cap (last [?f]) = UNIV"
    unfolding last select_convs(2) by simp
  show "more (last [?f]) \<noteq> None"
    unfolding last by simp
qed

setup_lifting type_definition_tstack

(*
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
*)

lemma Is_tstack_induct [consumes 1, case_names Base Frame]:
  assumes "Is_tstack s"
  assumes "\<And>x. frame_cap x = UNIV \<Longrightarrow> (\<forall>v. frame_st x v \<noteq> None) \<Longrightarrow> more x \<noteq> None \<Longrightarrow> P [x]"
  assumes "\<And>x xs. P xs \<Longrightarrow> Is_tstack xs \<Longrightarrow> P (x#xs)"
  shows "P s"
  using assms
proof (induct s)
  case (Cons a s)
  thus ?case by (cases s) (auto intro: assms simp: Is_tstack_def)
qed auto

(*
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
qed *)

lemma Is_tstack_snoc: "Is_tstack xs \<Longrightarrow> Is_tstack (butlast xs @ [last xs])"
unfolding Is_tstack_def by simp

lemma Is_tstack_snoc_moreupd: "Is_tstack xs \<Longrightarrow> Is_tstack (butlast xs @ [last xs\<lparr> more := Some any \<rparr>])"
unfolding Is_tstack_def by simp


fun lookup :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> 'val" where 
  "lookup [] v = undefined" |
  "lookup (f#fs) v = (if v \<in> frame_cap f then (case (frame_st f v) of None \<Rightarrow> lookup fs v | Some x \<Rightarrow> x) else lookup fs v)"
(* it is important that lookup ignores values from frames where v is not captured. *)
  
fun update :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val,'a) stack" where 
  "update [] _ _ = undefined" |
  "update (f#fs) v x = (if (v \<in> frame_cap f) then (f\<lparr>frame_st := (frame_st f)(v \<mapsto> x)\<rparr>)#fs else f#update fs v x)"

fun aux :: "('var,'val,'a) stack \<Rightarrow> 'a"
  where
    "aux [] = undefined" |
    "aux (h#ts) = (case more h of None \<Rightarrow> aux ts | Some v \<Rightarrow> v)"

definition auxupd :: "('var,'val,'a) stack \<Rightarrow> (('var,'val,'a) stack \<Rightarrow> 'a) \<Rightarrow> ('var,'val,'a) stack" where 
  "auxupd s f \<equiv> case s of h#t \<Rightarrow> (h\<lparr> more := Some (f s)\<rparr>)#t | _ \<Rightarrow> []"

definition captured :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> bool"
  where "captured s v \<equiv> \<exists>frame \<in> set (butlast s). v \<in> frame_cap frame"

definition base_st :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> 'val"
  where "base_st s \<equiv> the \<circ> frame_st (last s)"

definition base_aux :: "('var,'val,'a) stack \<Rightarrow> 'a"
  where "base_aux s \<equiv> the (more (last s))"

lemma [elim!]:
  assumes "update xs x e = []"
  obtains "xs = []"
  using assms by (case_tac xs; auto split: if_splits)

lemma Is_tstack_update: 
  assumes "Is_tstack s"
  shows "Is_tstack (update s v x)" 
  using assms by (induct s rule: Is_tstack_induct) (auto simp: Is_tstack_def)

lemma length_update:
  "Is_tstack s \<Longrightarrow> length (update s v x) = length s"
  by (induct rule: Is_tstack_induct) auto

lemma aux_update:
  "Is_tstack s \<Longrightarrow> aux (update s v x) = aux s"
  by (induct rule: Is_tstack_induct) (auto split: option.splits)

lemma lookup_update:
  "Is_tstack s \<Longrightarrow> lookup (update s v e) = (lookup s)(v := e)"
  by (induct rule: Is_tstack_induct) (auto split: if_splits option.splits simp: fun_eq_iff)

lemma captured_update:
  "Is_tstack s \<Longrightarrow> captured (update s v e) = captured s"
  by (induct rule: Is_tstack_induct) (auto simp: fun_eq_iff captured_def)

lemma base_st_update:
  "Is_tstack s \<Longrightarrow> base_st (update s v e) = (if captured s v then base_st s else (base_st s)(v := e))"
  by (induct rule: Is_tstack_induct) (auto simp: base_st_def fun_eq_iff captured_def)

lemma base_aux_update:
  "Is_tstack s \<Longrightarrow> base_aux (update s v e) = base_aux s"
  by (induct rule: Is_tstack_induct) (auto simp: base_aux_def)

lemma Is_tstack_auxupd:
  assumes "Is_tstack s"
  shows "Is_tstack (auxupd s f)"
  using assms by (induct s rule: Is_tstack_induct) (auto simp: Is_tstack_def auxupd_def)

lemma length_auxupd:
  "Is_tstack s \<Longrightarrow> length (auxupd s f) = length s"
  by (induct rule: Is_tstack_induct) (auto simp: auxupd_def)

lemma lookup_auxupd:
  "Is_tstack s \<Longrightarrow> lookup (auxupd s f) = lookup s"
  by (induct rule: Is_tstack_induct) (auto simp: auxupd_def)

lemma aux_auxupd:
  "Is_tstack s \<Longrightarrow> aux (auxupd s f) = f s"
  by (induct rule: Is_tstack_induct) (auto simp: auxupd_def)

lemma auxupd_aux:
  "Is_tstack t \<Longrightarrow> auxupd t aux = t"
  apply (induct rule: Is_tstack_induct) apply (auto simp: auxupd_def)
  proof (goal_cases)
    case (1 x xs)
    then show ?case apply (induct xs)
    apply auto
    using surjective[of x]
    sorry (* XXX: this feels obvious *)
  qed

lemma captured_auxupd:
  "Is_tstack s \<Longrightarrow> captured (auxupd s f) = captured s"
  by (induct rule: Is_tstack_induct) (auto simp: fun_eq_iff captured_def auxupd_def)

lemma base_st_auxupd:
  "Is_tstack s \<Longrightarrow> base_st (auxupd s f) = base_st s"
  by (induct rule: Is_tstack_induct) (auto simp: base_st_def auxupd_def)

lemma base_aux_auxupd:
  "Is_tstack s \<Longrightarrow> base_aux (auxupd s f) = (if length s = 1 then f s else base_aux s)"
  by (induct rule: Is_tstack_induct) (auto simp: base_aux_def auxupd_def fun_eq_iff)

lemma Is_tstack_auxupd_eq:
  "Is_tstack list \<Longrightarrow> (\<And>x. Is_tstack x \<Longrightarrow> fun1 x = fun2 x) \<Longrightarrow> auxupd list fun1 = auxupd list fun2"
  by (induct list) (auto simp: auxupd_def)

lemma base_st_lookup:
  "Is_tstack y \<Longrightarrow> length y = 1 \<Longrightarrow> base_st y = lookup y"
proof (induct rule: Is_tstack_induct)
  case (Base x)
  then show ?case by (auto simp: base_st_def fun_eq_iff split: option.splits)
     (simp add: option.the_def)
next
  case (Frame x xs)
  then show ?case by (auto simp: base_st_def fun_eq_iff split: option.splits)
qed

lemma base_aux_aux:
  "Is_tstack y \<Longrightarrow> length y = Suc 0 \<Longrightarrow> base_aux y = aux y"
  by (induct rule: Is_tstack_induct) (auto simp: base_aux_def fun_eq_iff split: option.splits)

lift_definition tlookup :: "('var,'val,'a) tstack \<Rightarrow> 'var \<Rightarrow> 'val" is "lookup" .
lift_definition tcaptured :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> bool" is "captured" .
lift_definition taux :: "('var,'val,'a) tstack \<Rightarrow> 'a" is "aux" .
lift_definition tstack_len :: "('r,'v,'a) tstack \<Rightarrow> nat" is "length" .
lift_definition tbase_st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v" is "base_st" .
lift_definition tbase_aux :: "('var,'val,'a) tstack \<Rightarrow> 'a" is "base_aux" .

lift_definition tupdate :: "('var,'val,'a) tstack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val,'a) tstack" is "update"
  using Is_tstack_update by force

lift_definition tauxupd :: "('var,'val,'a) tstack \<Rightarrow> (('var,'val,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('var,'val,'a) tstack" is "auxupd"
  by (intro conjI Is_tstack_auxupd_eq Is_tstack_auxupd) blast+

lift_definition tstack_push :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a option) frame_scheme \<Rightarrow> ('r,'v,'a) tstack"
  is "\<lambda>stack frame. (\<lparr>frame_st = frame_st frame, frame_cap = frame_cap frame, \<dots> = more frame \<rparr> # stack)"
  by (auto)

abbreviation capped :: "('r,'v,'a) tstack \<Rightarrow> 'r set" where
  "capped ts \<equiv> Collect (tcaptured ts)"

definition tstack_upper :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a option) frame_scheme list"
  where "tstack_upper ts = butlast (Rep_tstack ts)"

text \<open>
The number of frames within the tstack naturally tells us whether that state
is speculative or sequential.
\<close>

abbreviation ts_is_seq where
  "ts_is_seq ts \<equiv> tstack_len ts = 1"

abbreviation ts_is_spec where
  "ts_is_spec ts \<equiv> \<not> ts_is_seq ts"

subsection \<open>@{term tupdate} Properties\<close>

lemma tlength_tupdate [simp]:
  "tstack_len (tupdate s v x) = tstack_len s"
  by (transfer) (auto simp: length_update)

lemma taux_tupdate [simp]:
  "taux (tupdate s v x) = taux s"
  by (transfer) (auto simp: aux_update)

lemma tlookup_tupdate [simp]:
  "tlookup (tupdate s v e) = (tlookup s)(v := e)"
  by (transfer) (auto simp: lookup_update)

lemma tcaptured_tupdate [simp]:
  "tcaptured (tupdate x v e) = tcaptured x"
  by (transfer) (auto simp: captured_update)

lemma tbase_st_tupdate [simp]:
  "tbase_st (tupdate s v e) = (if tcaptured s v then tbase_st s else (tbase_st s)(v := e))"
  by (transfer) (auto simp: base_st_update)

lemma tbase_aux_tupdate [simp]:
  "tbase_aux (tupdate s v e) = tbase_aux s"
  by (transfer) (auto simp: base_aux_update)

lemma tauxupd_taux [simp]:
  "tauxupd t taux = t"
by transfer (simp add: auxupd_aux)

subsection \<open>@{term tauxupd} Properties\<close>

lemma tlength_tauxupd [simp]:
  "tstack_len (tauxupd s f) = tstack_len s"
  by (transfer) (auto simp: length_auxupd)

lemma tlookup_tauxupd [simp]:
  "tlookup (tauxupd s f) = tlookup s"
  by (transfer) (auto simp: lookup_auxupd)

lemma taux_tauxupd [simp]:
  "taux (tauxupd s f) = f s"
  by (transfer) (auto simp: aux_auxupd)

lemma tcaptured_tauxupd [simp]:
  "tcaptured (tauxupd x f) = tcaptured x"
  by (transfer) (auto simp: captured_auxupd)

lemma tbase_st_tauxupd [simp]:
  "tbase_st (tauxupd s f) = tbase_st s"
  by (transfer) (auto simp: base_st_auxupd)

lemma tbase_aux_tauxupd [simp]:
  "tbase_aux (tauxupd s f) = (if tstack_len s = 1 then f s else tbase_aux s)"
  by (transfer) (auto simp: base_aux_auxupd)

subsection \<open>@{term tstack_push} Properties\<close>

lemma tlength_tpush [simp]:
  "tstack_len (tstack_push m s) = Suc (tstack_len m)"
  by transfer auto

lemma tlookup_tpush [simp]:
  "tlookup (tstack_push m s) = (\<lambda>x. if x \<in> frame_cap s \<and> frame_st s x \<noteq> None then the (frame_st s x) else tlookup m x)"
  by transfer (simp add: fun_eq_iff split: option.splits)

lemma taux_tpush [simp]:
  "taux (tstack_push m s) = (case more s of Some v \<Rightarrow> v | _ \<Rightarrow> taux m)"
  by transfer simp

lemma tcaptured_tpush [simp]:
  "tcaptured (tstack_push x s) = (\<lambda>v. v \<in> frame_cap s \<or> tcaptured x v)"
  by (transfer)  (auto simp: captured_def fun_eq_iff)

lemma tbase_st_tpush [simp]:
  "tbase_st (tstack_push m s) = tbase_st m"
  by transfer (auto simp: base_st_def)

lemma tbase_aux_tpush [simp]:
  "tbase_aux (tstack_push m s) = tbase_aux m"
  by transfer (auto simp: base_aux_def)

lemma tpush_eq [elim!]:
  assumes "tstack_push mb sb = tstack_push m s"
  obtains "mb = m" "frame_st sb = frame_st s" "frame_cap sb = frame_cap s"
  using assms by transfer auto
  
subsection \<open>@{term tstack_len} Properties\<close>

lemma tbase_st_tlookup [simp]:
  "tstack_len y = 1 \<Longrightarrow> tbase_st y = tlookup y"
  by transfer (auto simp: base_st_lookup)

lemma tbase_aux_taux [simp]:
  "tstack_len y = 1 \<Longrightarrow> tbase_aux y = taux y"
  by transfer (auto simp: base_aux_aux)

lemma [intro, simp]:
  "tstack_len x > 0"
  by transfer auto

lemma [simp]:
  "(tstack_len m = 0) = False"
  by transfer auto

lemma is_spec_push:
  "ts_is_spec x \<Longrightarrow> \<exists>m s. x = tstack_push m s"
  by transfer ((case_tac x; auto), insert surjective, blast)

lemma butlast_length_eq:
  "m \<noteq> [] \<Longrightarrow> m' \<noteq> [] \<Longrightarrow> butlast m = butlast m' \<Longrightarrow> length m = length m'"
proof (induct m arbitrary: m')
  case Nil
  then show ?case by auto
next
  case (Cons a m)
  then obtain b n where m: "m'=b#n" by (cases m') auto
  hence "(a = b \<and> butlast m = butlast n \<and> n \<noteq> [] \<and> m \<noteq> []) \<or> (n = [] \<and> m = [])"
    using Cons(4) by (auto split: if_splits)
  thus ?case using Cons(1) by (auto simp: m)
qed

lemma tstack_upper_len_eq:
  "tstack_upper m = tstack_upper m' \<Longrightarrow> tstack_len m = tstack_len m'"
  unfolding tstack_upper_def by transfer (blast intro: butlast_length_eq)

subsection \<open>@{term emptyFrame} Properties\<close>

lemma cap_emptyFrame [simp]:
  "frame_cap (emptyFrame w) = w"
  by (auto simp: emptyFrame_def)

lemma st_emptyFrame [simp]:
  "frame_st (emptyFrame w) = (\<lambda>v. None)"
  by (auto simp: emptyFrame_def)

lemma more_emptyFrame [simp]:
  "more (emptyFrame w) = None"
  by (auto simp: emptyFrame_def)


(*
lemma ts_upper_of_seq [elim]: \<open>ts_is_seq m \<Longrightarrow> (tstack_upper m = [])\<close>
unfolding  tstack_upper_def tstack_len_def 
by (simp_all only: id_def) (simp_all add: butlast_conv_take Rep_tstackI(1) le_Suc_eq)

lemma ts_is_seq_of_ts_upper [intro]: \<open>(tstack_upper m = []) \<Longrightarrow> ts_is_seq m\<close>
unfolding  tstack_upper_def tstack_len_def 
by (simp_all only: id_def) (simp_all add: butlast_conv_take Rep_tstackI(1) le_Suc_eq)
*)

(*
lemma length_butlast:
  assumes "length m = 1" "butlast m = butlast m'"
  shows "length m' = 1 \<or> length m' = 0"
  using assms by (cases m; cases m'; auto split: if_splits)

lemma ts_is_seq_upper:
  assumes "ts_is_seq m" "tstack_upper m = tstack_upper m'"
  shows "ts_is_seq m'"
  using assms using length_butlast Rep_tstack
  unfolding  tstack_len_def tstack_upper_def Is_tstack_def
  by auto *)


(*
lemma [intro!, simp]: "Is_tstack (Rep_tstack s)" 
  using Rep_tstack by auto
*)
(*
lemma Is_tstack_update2 [intro!,simp]: "Is_tstack (update (Rep_tstack fs) v x)" 
  by (simp add: Is_tstack_update)
*)

(*
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

lemma aux_tauxupd [simp]:
  shows "more (last (Rep_tstack (tauxupd s f))) = f s"
proof (induct s rule: tstack_induct)
  case (Base s)
  hence "Is_tstack (auxupd [s] (\<lambda>tstack. f (Abs_tstack tstack)))" by auto
  thus ?case unfolding tauxupd_def auxupd_def using Base by auto
next
  case (Frame x xs)
  hence "Is_tstack (x#xs)" by auto
  thus ?case unfolding tauxupd_def auxupd_def using Frame
  by (auto simp add: Is_tstack_ConsI Is_tstack_snoc_moreupd)
qed *)


(*
lemma tauxupd_id [simp]: 
  "tauxupd s taux = s"
  by transfer (auto simp: auxupd_def split: list.splits)
*)

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

