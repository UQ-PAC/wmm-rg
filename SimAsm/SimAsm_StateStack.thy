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
(*   *)
  
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
  "update [] _ _ = []" |
  "update (f#fs) v x = (if (v \<in> frame_cap f) then (f\<lparr>frame_st := (frame_st f)(v \<mapsto> x)\<rparr>)#fs else f#update fs v x)"

fun aux :: "('var,'val,'a) stack \<Rightarrow> 'a"
  where
    "aux [] = undefined" |
    "aux (h#ts) = (case more h of None \<Rightarrow> aux ts | Some v \<Rightarrow> v)"

fun wf_transition :: "('var,'val,'a) stack \<Rightarrow> ('var,'val,'a) stack \<Rightarrow> bool"
  where
    "wf_transition (f#fs) (s#ss) = (butlast fs = butlast ss \<and> length fs = length ss)" |
    "wf_transition [] [] = True" |
    "wf_transition _ _ = False"

definition auxupd :: "('var,'val,'a) stack \<Rightarrow> (('var,'val,'a) stack \<Rightarrow> 'a) \<Rightarrow> ('var,'val,'a) stack" where 
  "auxupd s f \<equiv> case s of h#t \<Rightarrow> (h\<lparr> more := Some (f s)\<rparr>)#t | _ \<Rightarrow> []"


definition captured :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> bool"
  where "captured s v \<equiv> \<exists>frame \<in> set (butlast s). v \<in> frame_cap frame"

definition topcap :: "('var,'val,'a) stack \<Rightarrow> 'var \<Rightarrow> bool"
  where "topcap s v \<equiv> case s of h#_#t \<Rightarrow> v \<in> frame_cap h | _ \<Rightarrow> False"

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
  by (induct rule: Is_tstack_induct) (auto simp: fun_eq_iff captured_def split: list.splits)

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
lift_definition ttopcap :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> bool" is "topcap" .
lift_definition taux :: "('var,'val,'a) tstack \<Rightarrow> 'a" is "aux" .
lift_definition tstack_len :: "('r,'v,'a) tstack \<Rightarrow> nat" is "length" .
lift_definition tbase_st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v" is "base_st" .
lift_definition tbase_aux :: "('var,'val,'a) tstack \<Rightarrow> 'a" is "base_aux" .
(*lift_definition twf_transition :: "('var,'val,'a) tstack \<Rightarrow> ('var,'val,'a) tstack \<Rightarrow> bool" is "wf_transition" . *)

lift_definition tupdate :: "('var,'val,'a) tstack \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> ('var,'val,'a) tstack" is "update"
  using Is_tstack_update by force

lift_definition tauxupd :: "('var,'val,'a) tstack \<Rightarrow> (('var,'val,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('var,'val,'a) tstack" is "auxupd"
  by (intro conjI Is_tstack_auxupd_eq Is_tstack_auxupd) blast+

lift_definition tstack_push :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a option) frame_scheme \<Rightarrow> ('r,'v,'a) tstack"
  is "\<lambda>stack frame. (\<lparr>frame_st = frame_st frame, frame_cap = frame_cap frame, \<dots> = more frame \<rparr> # stack)"
  by (auto)

abbreviation capped :: "('r,'v,'a) tstack \<Rightarrow> 'r set" where
  "capped ts \<equiv> Collect (tcaptured ts)"

abbreviation topcapped :: "('r,'v,'a) tstack \<Rightarrow> 'r set" where
  "topcapped ts \<equiv> Collect (ttopcap ts)"

definition tstack_upper :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a option) frame_scheme list"
  where "tstack_upper ts = butlast (Rep_tstack ts)"

definition tstack_mid :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a option) frame_scheme list"
  where "tstack_mid ts = (case Rep_tstack ts of h#t \<Rightarrow> butlast t | _ \<Rightarrow> [])"

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
  by (transfer) (auto simp: captured_def fun_eq_iff split: list.splits)

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

lemma  butlast_captured:
"Is_tstack m \<Longrightarrow>
       Is_tstack m' \<Longrightarrow>
       butlast m = butlast m' \<Longrightarrow>
       Collect (captured m) = Collect (captured m')"
proof (induct arbitrary: m' rule: Is_tstack_induct)
  case (Base x)
  then show ?case by (cases m'; auto split: if_splits simp: captured_def)
next
  case (Frame x xs)
  then show ?case by (cases m'; auto split: if_splits simp: captured_def)
qed

lemma  butlast_topcap:
  "Is_tstack m \<Longrightarrow>
       Is_tstack m' \<Longrightarrow>
       butlast m = butlast m' \<Longrightarrow>
       Collect (topcap m) = Collect (topcap m')"
  by (auto split: if_splits list.splits simp: topcap_def)

lemma tstack_upper_captured_eq:
  "tstack_upper m = tstack_upper m' \<Longrightarrow> capped m = capped m'"
  unfolding tstack_upper_def apply transfer using butlast_captured by auto

lemma tstack_upper_topcapped_eq:
  "tstack_upper m = tstack_upper m' \<Longrightarrow> topcapped m = topcapped m'"
  unfolding tstack_upper_def apply transfer using butlast_topcap by auto

fun written
  where 
    "written (a#b#c) v = ( (frame_st a v \<noteq> None \<and> v \<in> frame_cap a) \<or> written (b#c) v)" |
    "written _ v = False"

fun auxwritten
  where 
    "auxwritten (a#b#c) = (more a \<noteq> None \<or> auxwritten (b#c))" |
    "auxwritten _ = False"

lift_definition twritten ::  "('b, 'c, 'd) tstack \<Rightarrow> 'b \<Rightarrow> bool"  is "written" .
lift_definition tauxwritten ::  "('b, 'c, 'd) tstack \<Rightarrow> bool"  is "auxwritten" .

lemma upper_written:
  "Is_tstack m \<Longrightarrow>
       Is_tstack m' \<Longrightarrow> butlast m = butlast m' \<Longrightarrow> written m x = written m' x"
proof (induct arbitrary: m' rule: Is_tstack_induct)
  case (Base x)
  then show ?case by (cases m'; auto split: if_splits)
next
  case (Frame x xs)
  then show ?case
    apply (cases m'; auto split: if_splits)
     apply (cases xs)
      apply simp
     apply (metis Is_tstack_ConsE list.exhaust written.simps(1))
     apply (cases xs)
     apply simp
     apply (metis Is_tstack_ConsE list.exhaust written.simps(1))
    done
qed

lemma tupper_written:
  "tstack_upper m = tstack_upper m' \<Longrightarrow> twritten m x = twritten m' x"
  unfolding tstack_upper_def
  apply transfer
  using upper_written .

(* MOVE *)
lemma [intro]:
  assumes "tstack_upper m = tstack_upper m'"
  shows "tstack_upper (tstack_push m s) = tstack_upper (tstack_push m' s)"
  using assms unfolding tstack_upper_def by transfer auto

lemma [simp]:
  "tstack_len m = 1 \<Longrightarrow> tstack_upper m = []"
  unfolding tstack_upper_def by transfer (case_tac m; simp)

lemma [simp]:
  "tstack_len x = Suc 0 \<Longrightarrow> tcaptured x v = False"
  by transfer (case_tac x; auto simp: captured_def)

lemma [intro]:
  "ttopcap x x11 \<Longrightarrow> tcaptured x x11"
  by transfer (case_tac x; auto simp: captured_def topcap_def split: list.splits)

lemma [simp]:
  "ttopcap (tauxupd x f) = ttopcap x"
  apply transfer
  unfolding topcap_def auxupd_def
  by (auto split: list.splits simp: fun_eq_iff)

lemma [simp]:
  "ttopcap (tupdate x  y e) = ttopcap x"
  apply transfer
  unfolding topcap_def auxupd_def
  by (auto split: list.splits simp: fun_eq_iff)

lemma upper_mid:
  "tstack_upper a = tstack_upper b \<Longrightarrow>
           tstack_mid a = tstack_mid b"
  by (auto simp: tstack_upper_def tstack_mid_def split: list.splits if_splits)

lemma tstack_mid_tauxupd [simp]:
  "tstack_mid (tauxupd x f) = tstack_mid x"
  unfolding tstack_mid_def
  by transfer (auto simp: fun_eq_iff auxupd_def split: list.splits)

lemma tstack_mid_tupdate_base[simp]:
  "tstack_len x = Suc 0 \<Longrightarrow> tstack_mid (tupdate x y e) = tstack_mid x"
  unfolding tstack_mid_def
  by transfer (auto split: list.splits)

lemma stack_mid_update_nocap:
  "Is_tstack (x21 # x22) \<Longrightarrow>
       \<not> captured (x21 # x22) y \<Longrightarrow>
       butlast (update x22 y e) = butlast x22"
proof (induct "x21 # x22" arbitrary: x21 x22 rule: Is_tstack_induct)
  case (Base x)
  then show ?case by auto
next
  case (Frame x xs)
  then show ?case by (cases xs; auto simp: captured_def)
qed

lemma tstack_mid_tupdate_nocap[simp]:
  "\<not>tcaptured x y \<Longrightarrow> tstack_mid (tupdate x y e) = tstack_mid x"
  unfolding tstack_mid_def
  apply transfer 
  apply (auto split: list.splits)
  using stack_mid_update_nocap by force

lemma tstack_mid_tupdate_topcap[simp]:
  "ttopcap x y \<Longrightarrow> tstack_mid (tupdate x y e) = tstack_mid x"
  unfolding tstack_mid_def
  by transfer (auto split: list.splits simp: topcap_def)


lemma [simp]:
  "tstack_mid (tstack_push m s) = tstack_upper m"
  unfolding tstack_mid_def tstack_upper_def
  apply transfer
  apply (auto split: list.splits)
  done

lemma [simp]:
  "ttopcap (tstack_push m (emptyFrame w)) x = (x \<in> w)"
  by transfer
   (auto simp: topcap_def split: list.splits)

lemma [elim!]:
  assumes "[] = tstack_upper b"
  obtains "tstack_len b = 1"
  using assms unfolding tstack_upper_def apply (transfer)
  apply (case_tac b; auto split: if_splits)
  done


end

