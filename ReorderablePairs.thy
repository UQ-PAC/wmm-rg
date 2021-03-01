theory ReorderablePairs
  imports Pipeline Execution
begin

locale reorderable_pairs = execution eval + memory_model re fwd
  for eval :: "'a \<Rightarrow> 's rel"
  and re :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<hookleftarrow>" 100) 
  and fwd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

context reorderable_pairs
begin

(* Forwarding only weakens *)
lemma fwd_weaken [intro]:
  "d \<hookleftarrow> fwd \<beta>\<langle>f\<rangle> d \<Longrightarrow> d \<hookleftarrow> fwd (fwd \<beta> a)\<langle>f\<rangle> d"
  sorry

definition fwdll
  where "fwdll s f \<equiv> map (\<lambda>\<alpha>. \<alpha>\<langle>f\<rangle>) s"

definition unordered
  where "unordered t \<equiv> {\<alpha>. (\<forall>\<gamma> \<in> set t. \<alpha> \<hookleftarrow> fwd \<gamma> \<alpha>)}"

definition inter\<^sub>a
  where "inter\<^sub>a \<alpha> \<equiv> \<lambda>(I,t,\<beta>).
    (if \<alpha> \<notin> unordered (t@[\<beta>]) \<or> (\<alpha> \<in> unordered (t@[\<beta>]) \<and> \<beta> \<noteq> fwd \<beta> \<alpha>) then {(I,\<alpha>#t,\<beta>)} else {}) \<union>
    (if \<alpha> \<in> unordered (t@[\<beta>]) then {(I \<union> {(\<alpha>,\<beta>)},map (\<lambda>\<beta>. fwd \<beta> \<alpha>) t,fwd \<beta> \<alpha>)} else {})"

lemma inter\<^sub>aE:
  assumes "(I',t',\<beta>') \<in> inter\<^sub>a \<alpha> (I,t,\<beta>)"
  obtains (ino) "\<alpha> \<notin> unordered (t@[\<beta>])" "I' = I" "t' = \<alpha>#t" "\<beta>' = \<beta>" |
          (ooo) "\<alpha> \<in> unordered (t@[\<beta>])" "I' = I \<union> {(\<alpha>,\<beta>)}" "t' = map (\<lambda>\<beta>. fwd \<beta> \<alpha>) t" "\<beta>' = fwd \<beta> \<alpha>" |
          (fwd) "\<alpha> \<in> unordered (t@[\<beta>])" "\<beta> \<noteq> fwd \<beta> \<alpha>" "I' = I" "t' = \<alpha>#t" "\<beta>' = \<beta>"
  using assms by (auto simp: inter\<^sub>a_def split: if_splits)

lemma inter\<^sub>aI_ino:
  assumes "\<alpha> \<notin> unordered (t@[\<beta>])"
  shows "(I,\<alpha>#t,\<beta>) \<in> inter\<^sub>a \<alpha> (I,t,\<beta>)"
  using assms by (auto simp: inter\<^sub>a_def split: if_splits)

lemma inter\<^sub>aI_ooo:
  assumes "\<alpha> \<in> unordered (t@[\<beta>])"
  shows "(I \<union> {(\<alpha>,\<beta>)},map (\<lambda>\<beta>. fwd \<beta> \<alpha>) t,fwd \<beta> \<alpha>) \<in> inter\<^sub>a \<alpha> (I,t,\<beta>)"
  using assms by (auto simp: inter\<^sub>a_def split: if_splits)

lemma inter\<^sub>aI_fwd:
  assumes "\<alpha> \<in> unordered (t@[\<beta>])" "\<beta> \<noteq> fwd \<beta> \<alpha>"
  shows "(I,\<alpha>#t,\<beta>) \<in> inter\<^sub>a \<alpha> (I,t,\<beta>)"
  using assms by (auto simp: inter\<^sub>a_def split: if_splits)

lemma inter\<^sub>aI:
  shows "\<exists>I' t'. (I',t',\<beta>) \<in> inter\<^sub>a \<alpha> (I,t,\<beta>)"
  apply (cases "\<alpha> \<in> unordered (t@[\<beta>])")
  apply (cases "fwd \<beta> \<alpha> = \<beta>")
  using inter\<^sub>aI_ooo apply metis
  using inter\<^sub>aI_fwd apply metis
  using inter\<^sub>aI_ino by metis

lemma inter\<^sub>a_I:
  assumes "(I'',t'',\<alpha>'') \<in> inter\<^sub>a \<beta> (I',t',\<alpha>')" 
  shows "I'' \<supseteq> I'"
  using assms by (cases rule: inter\<^sub>aE) auto

lemma inter\<^sub>a_t:
  assumes "(I',t',\<alpha>') \<in> inter\<^sub>a \<beta> (I,t,\<alpha>)" 
  shows "\<forall>f d. d \<hookleftarrow> fwd \<beta>\<langle>f\<rangle> d \<longrightarrow> d \<in> unordered (fwdll (t@[\<alpha>]) f) \<longrightarrow> d \<in> unordered (fwdll (t'@[\<alpha>']) f)" 
  using assms
  by (cases rule: inter\<^sub>aE) (auto simp: unordered_def fwdll_def)

fun inter_trace_rec
  where 
    "inter_trace_rec [] S = S" |
    "inter_trace_rec (\<alpha>#t) S = \<Union> (inter\<^sub>a \<alpha> ` (inter_trace_rec t S))"

lemma inter_trace_recI:
  assumes "(I\<^sub>1, t\<^sub>1, \<alpha>\<^sub>1) \<in> inter_trace_rec t S"
  assumes "(I\<^sub>2, t\<^sub>2, \<alpha>\<^sub>2) \<in> inter\<^sub>a \<beta> (I\<^sub>1, t\<^sub>1, \<alpha>\<^sub>1)"
  shows "(I\<^sub>2, t\<^sub>2, \<alpha>\<^sub>2) \<in> inter_trace_rec (\<beta>#t) S"
  using assms by (auto split: prod.splits)

definition inter_trace
  where "inter_trace t \<beta> \<equiv> \<Union> (fst ` inter_trace_rec t {({},[],\<beta>)})"

fun zipper
  where
    "zipper t [] = {}" |
    "zipper t (\<alpha>#s) = (zipper (t@[\<alpha>]) s \<union> inter_trace t \<alpha>)"

definition inter
  where "inter t \<equiv> zipper [] t"

lemma inter_trace_drop:
  "inter_trace t \<alpha> \<subseteq> inter_trace (\<beta> # t) \<alpha>"
  unfolding inter_trace_def
  apply clarsimp
proof -
  fix a b \<alpha>' I' t' assume a: "(a, b) \<in> I'" "(I',t',\<alpha>') \<in> inter_trace_rec t {({}, [], \<alpha>)}"
  moreover obtain \<alpha>'' I'' t'' where b: "(I'',t'',\<alpha>'') \<in> inter\<^sub>a \<beta> (I',t',\<alpha>')" 
    using inter\<^sub>aI by blast
  hence "(a, b) \<in> I''" using a inter\<^sub>a_I by blast
  thus "\<exists>x\<in>inter_trace_rec t {({}, [], \<alpha>)}. \<exists>x\<in>inter\<^sub>a \<beta> x. (a, b) \<in> fst x"
    using b a(2) by force
qed

(*
section \<open>Interference Check\<close>

definition unordered
  where "unordered t \<beta> \<equiv> {\<alpha>. \<alpha> \<hookleftarrow> fwd \<beta> \<alpha> \<and> (\<forall>\<gamma> \<in> set t. \<alpha> \<hookleftarrow> fwd \<gamma> \<alpha>)}"

lemma [elim!]:
  assumes "s \<lhd> \<beta> \<lhd> (\<alpha>#t)"
  obtains \<alpha>' s' where "s = \<alpha>'#s'" "\<alpha>' < \<beta> < \<alpha>" "s' \<lhd> \<beta> \<lhd> t"
  using assms
  by (induct s \<beta> "\<alpha>#t" rule: reorder_pipe.induct) auto

lemma [elim!]:
  assumes "t' \<lhd> \<beta> \<lhd>  t"
  obtains "\<forall>\<alpha> \<in> set t. \<beta> \<hookleftarrow> fwd \<alpha> \<beta>" "t' = map (\<lambda>\<alpha>. fwd \<alpha> \<beta>) t"
  using assms by (induct rule: reorder_pipe.induct) auto

lemma other_way:
  assumes "\<forall>\<alpha> \<in> set t. \<beta> \<hookleftarrow> fwd \<alpha> \<beta>" "t' = map (\<lambda>\<alpha>. fwd \<alpha> \<beta>) t"
  shows "t' \<lhd> \<beta> \<lhd>  t"
  using assms
  by (induct t arbitrary: t') auto

lemma reorder_trace [simp]:
  "t' \<lhd> \<beta> \<lhd>  t = ((\<forall>\<alpha> \<in> set t. \<beta> \<hookleftarrow> fwd \<alpha> \<beta>) \<and> t' = map (\<lambda>\<alpha>. fwd \<alpha> \<beta>) t)"
  apply (intro iffI)
  apply blast
  using other_way by auto

definition inter\<^sub>a
  where "inter\<^sub>a R \<alpha> \<equiv> \<lambda>(I,t,\<beta>).
    (if \<alpha> \<notin> unordered t \<beta> then {(I,\<alpha>#t,\<beta>)} else {}) \<union>
    (if \<alpha> \<in> unordered t \<beta> then {(I \<and> order_indep R \<alpha> \<beta>,map (\<lambda>\<beta>. fwd \<beta> \<alpha>) t,fwd \<beta> \<alpha>)} else {}) \<union>
    (if \<alpha> \<in> unordered t \<beta> \<and> \<beta> \<noteq> fwd \<beta> \<alpha> then {(I,\<alpha>#t,\<beta>)} else {})"

lemma inter\<^sub>aE:
  assumes "(I',t',\<beta>') \<in> inter\<^sub>a R \<alpha> (I,t,\<beta>)"
  obtains (ino) "\<alpha> \<notin> unordered t \<beta>" "I' = I" "t' = \<alpha>#t" "\<beta>' = \<beta>" |
          (ooo) "\<alpha> \<in> unordered t \<beta>" "I' = (I \<and> order_indep R \<alpha> \<beta>)" "t' = map (\<lambda>\<beta>. fwd \<beta> \<alpha>) t" "\<beta>' = fwd \<beta> \<alpha>" |
          (fwd) "\<alpha> \<in> unordered t \<beta>" "\<beta> \<noteq> fwd \<beta> \<alpha>" "I' = I" "t' = \<alpha>#t" "\<beta>' = \<beta>"
  using assms by (auto simp: inter\<^sub>a_def split: if_splits)

lemma inter\<^sub>aI_ino:
  assumes "\<alpha> \<notin> unordered t \<beta>"
  shows "(I,\<alpha>#t,\<beta>) \<in> inter\<^sub>a R \<alpha> (I,t,\<beta>)"
  using assms by (auto simp: inter\<^sub>a_def split: if_splits)

lemma inter\<^sub>aI_ooo:
  assumes "\<alpha> \<in> unordered t \<beta>"
  shows "(I \<and> order_indep R \<alpha> \<beta>,map (\<lambda>\<beta>. fwd \<beta> \<alpha>) t,fwd \<beta> \<alpha>) \<in> inter\<^sub>a R \<alpha> (I,t,\<beta>)"
  using assms by (auto simp: inter\<^sub>a_def split: if_splits)

lemma inter\<^sub>aI_fwd:
  assumes "\<alpha> \<in> unordered t \<beta>" "\<beta> \<noteq> fwd \<beta> \<alpha>"
  shows "(I,\<alpha>#t,\<beta>) \<in> inter\<^sub>a R \<alpha> (I,t,\<beta>)"
  using assms by (auto simp: inter\<^sub>a_def split: if_splits)

lemma inter\<^sub>aI:
  shows "\<exists>\<beta>' I' t'. (I',t',\<beta>') \<in> inter\<^sub>a R \<alpha> (I,t,\<beta>)"
  by (cases "\<alpha> \<in> unordered t \<beta>") (auto intro: inter\<^sub>aI_ino inter\<^sub>aI_ooo)

lemma inter\<^sub>aI':
  shows "\<exists>I' t'. (I',t',\<beta>) \<in> inter\<^sub>a R \<alpha> (I,t,\<beta>)"
  apply (cases "\<alpha> \<in> unordered t \<beta>")
  apply (cases "fwd \<beta> \<alpha> = \<beta>")
  using inter\<^sub>aI_ooo apply metis
  using inter\<^sub>aI_fwd apply metis
  using inter\<^sub>aI_ino by metis

lemma t [intro]:
  "d \<hookleftarrow> fwd \<beta> d \<Longrightarrow> d \<hookleftarrow> fwd (fwd \<beta> a) d"
  sorry

fun inter_trace_rec
  where 
    "inter_trace_rec R [] S = S" |
    "inter_trace_rec R (\<alpha>#t) S = \<Union> (inter\<^sub>a R \<alpha> ` (inter_trace_rec R t S))"

definition inter_trace
  where "inter_trace R t \<beta> \<equiv> \<forall>x \<in> inter_trace_rec R t {(True,[],\<beta>)}. fst x"

fun inter_all
  where
    "inter_all R t [] = True" |
    "inter_all R t (\<alpha>#s) = (inter_all R (t@[\<alpha>]) s \<and> inter_trace R t \<alpha>)"

definition inter
  where "inter R t \<equiv> inter_all R [] t"

lemma inter_trace_recI:
  assumes "(I\<^sub>1, t\<^sub>1, \<alpha>\<^sub>1) \<in> inter_trace_rec R t S"
  assumes "(I\<^sub>2, t\<^sub>2, \<alpha>\<^sub>2) \<in> inter\<^sub>a R \<beta> (I\<^sub>1, t\<^sub>1, \<alpha>\<^sub>1)"
  shows "(I\<^sub>2, t\<^sub>2, \<alpha>\<^sub>2) \<in> inter_trace_rec R (\<beta>#t) S"
  using assms by (auto split: prod.splits)

lemma inter\<^sub>a_I:
  assumes "(I'',t'',\<alpha>'') \<in> inter\<^sub>a R \<beta> (I',t',\<alpha>')" 
  shows "I'' \<longrightarrow> I'"
  using assms by (cases rule: inter\<^sub>aE) auto

lemma inter\<^sub>a_t:
  assumes "(I',t',\<alpha>') \<in> inter\<^sub>a R \<beta> (I,t,\<alpha>)" 
  shows "\<forall>d. d \<hookleftarrow> fwd \<beta> d \<longrightarrow> d \<in> unordered t \<alpha> \<longrightarrow> d \<in> unordered t' \<alpha>'" 
  using assms
  by (cases rule: inter\<^sub>aE) (auto simp: unordered_def)

definition fwdll
  where "fwdll s f \<equiv> map (\<lambda>\<alpha>. \<alpha>\<langle>f\<rangle>) s"

lemma inter\<^sub>a_t':
  assumes "(I',t',\<alpha>') \<in> inter\<^sub>a R \<beta> (I,t,\<alpha>)" 
  shows "\<forall>f d. d \<hookleftarrow> fwd \<beta>\<langle>f\<rangle> d \<longrightarrow> d \<in> unordered (fwdll t f) \<alpha>\<langle>f\<rangle> \<longrightarrow> d \<in> unordered (fwdll t' f) \<alpha>'\<langle>f\<rangle>" 
  using assms
  by (cases rule: inter\<^sub>aE) (auto simp: unordered_def fwdll_def)
  
  (* Something about the order indep. of forwarding *)

lemma inter_trace_drop:
  assumes "inter_trace R (\<beta> # t) \<alpha>"
  shows "inter_trace R t \<alpha>"
  unfolding inter_trace_def
  apply (intro ballI)
  apply (auto split: prod.splits)
proof -
  fix \<alpha>' I' t' assume "(I',t',\<alpha>') \<in> inter_trace_rec R t {(True, [], \<alpha>)}"
  moreover obtain \<alpha>'' I'' t'' where a: "(I'',t'',\<alpha>'') \<in> inter\<^sub>a R \<beta> (I',t',\<alpha>')" 
    using inter\<^sub>aI by blast
  ultimately have "(I'',t'',\<alpha>'') \<in> inter_trace_rec R (\<beta>#t) {(True, [], \<alpha>)}"
    apply (intro inter_trace_recI)
    by simp+
  hence "I''" using assms apply (auto simp: inter_trace_def split: prod.splits) by force
  thus "I'" using inter\<^sub>a_I a by blast
qed

fun naive
  where 
    "naive R [] \<alpha> = (True,\<alpha>)" | 
    "naive R (\<beta>#t) \<alpha> = (case naive R t \<alpha> of (I,\<alpha>') \<Rightarrow> (I \<and> order_indep R \<beta> \<alpha>', fwd \<alpha>' \<beta>))"

lemma naive_fwd:
  shows "snd (naive R t \<alpha>) = \<alpha>\<langle>t\<rangle>"
  by (induct t) (auto split: prod.splits)

lemma naive_inter_trace_rec:
  assumes "\<alpha>' \<lless> t \<lless> \<alpha>"
  shows "(fst (naive R t \<alpha>),[],\<alpha>') \<in> inter_trace_rec R t {(True,[],\<alpha>)}"
  using assms
proof (induct t arbitrary: \<alpha> \<alpha>')
  case Nil
  then show ?case by auto
next
  case (Cons \<beta> t)
  obtain \<alpha>'' where r: "\<alpha>' < \<beta> < \<alpha>''" "\<alpha>'' \<lless> t \<lless> \<alpha>" using Cons(2) by auto
  hence u: "\<beta> \<in> unordered [] \<alpha>''" unfolding unordered_def by auto
  have s: "snd (naive R t \<alpha>) = \<alpha>''" using naive_fwd by (simp add: local.r(2))

  hence "(fst (naive R t \<alpha>), [],\<alpha>'') \<in> inter_trace_rec R t {(True,[],\<alpha>)}"
    using r Cons by blast

  then show ?case
    apply (rule inter_trace_recI)
    using inter\<^sub>aI_ooo[OF u, of "(fst (naive R t \<alpha>))" R]
    apply (auto split: prod.splits)
    using s r by simp
qed

lemma to_naive:
  assumes "inter_trace R t \<alpha>" "\<alpha>' \<lless> t \<lless> \<alpha>"
  shows "naive R t \<alpha> = (True, \<alpha>')"
  using assms
proof (induct t arbitrary: \<alpha> \<alpha>')
  case Nil
  then show ?case by auto
next
  case (Cons \<beta> t)
  hence "(fst (naive R (\<beta> # t) \<alpha>), [], \<alpha>') \<in> inter_trace_rec R (\<beta> # t) {(True,[],\<alpha>)}"
    using naive_inter_trace_rec by blast
  hence "fst (naive R (\<beta> # t) \<alpha>)"
    using Cons(2) unfolding inter_trace_def by force
  hence o: "order_indep R \<beta> \<alpha>\<langle>t\<rangle>"
    apply (simp split: prod.splits)
    by (metis naive_fwd snd_conv)

  hence i: "inter_trace R t \<alpha>" using  Cons inter_trace_drop by auto
  obtain \<alpha>'' where r: "\<alpha>' < \<beta> < \<alpha>''" "\<alpha>'' \<lless> t \<lless> \<alpha>" using Cons(3) by auto
  hence "naive R t \<alpha> = (True, \<alpha>'')" using Cons i by auto
  then show ?case using r o by (simp split: prod.splits)
qed

lemma inter_trace_indep:
  assumes "inter_trace R (\<beta> # t) \<alpha>" "\<alpha>' \<lless> \<beta> # t \<lless> \<alpha>"
  shows "order_indep R \<beta> \<alpha>\<langle>t\<rangle>"
  using assms
proof -
  have "naive R (\<beta> # t) \<alpha> = (True, \<alpha>')"
    using assms to_naive by blast
  thus "order_indep R \<beta> \<alpha>\<langle>t\<rangle>" 
    using naive_fwd by (simp split: prod.splits) (metis snd_conv)
qed

lemma rec_append:
  "inter_trace_rec R (pre@post) S = inter_trace_rec R pre (inter_trace_rec R post S)"
  by (induct pre) auto

definition nop
  where "nop R x \<equiv> (\<forall>\<alpha> \<beta>. (\<forall>\<gamma>. \<gamma> = fwd \<gamma> \<beta>) \<longrightarrow> \<alpha> \<hookleftarrow> fwd \<beta> \<alpha> \<longrightarrow> \<alpha> \<hookleftarrow> fwd x \<alpha>) \<and> (\<forall>\<alpha>. order_indep R x \<alpha> \<and> fwd \<alpha> x = \<alpha>)"

(* d is store, \<alpha> is load, x is cfence *)
(* \<Rightarrow> d\<langle>f\<rangle> = d *)
(* so we only consider fwding on \<alpha>, no big issue *)
lemma issue:
  assumes "x \<hookleftarrow> fwd (fwd \<alpha> d)\<langle>f\<rangle> x"
  assumes "x \<hookleftarrow> fwd d\<langle>f\<rangle> x"
  assumes "d \<hookleftarrow> fwd \<alpha> d"
  shows "x \<hookleftarrow> fwd \<alpha>\<langle>f\<rangle> x \<or> nop R x"
  sorry

lemma [simp]:
  "\<alpha>''\<langle>f @ [d]\<rangle> = (fwd \<alpha>'' d)\<langle>f\<rangle>"
  by (induct f) auto

(*
  What is the value we want to pass to nop to express the idea that
  we already have the dependencies of the ctrl fence captured?
  Trouble occurs when \<alpha> is a store, so it can be \<alpha>.
  That is actually d in the issue definition.
  But the real issue is that using d in that location is a little confusing,
  as \<alpha> can change throughout execution.
*)

lemma test':
  assumes "(I',t',\<beta>') \<in> inter_trace_rec R p {(I,t,\<beta>)}" "\<alpha>' \<lless> p \<lless> \<alpha>"
  obtains I'' t'' where 
    "(I'',t'',\<beta>') \<in> inter_trace_rec R (p@[\<alpha>]) {(I,t,\<beta>)}" 
    "I'' \<longrightarrow> I'"
    "\<forall>f d. d \<hookleftarrow> fwd \<alpha>'\<langle>f\<rangle> d \<longrightarrow> d \<in> unordered (fwdll t' f) \<beta>'\<langle>f\<rangle> \<longrightarrow> (d \<in> unordered (fwdll t'' f) \<beta>'\<langle>f\<rangle> \<or> nop R d)" 
  using assms
proof (induct p arbitrary: I' t' \<beta>' \<alpha>')
  case Nil
  then show ?case
    using inter\<^sub>aI'[of \<beta> R \<alpha> I t]
    apply auto
    using inter\<^sub>a_t'
    apply simp
    using inter\<^sub>a_I inter\<^sub>a_t'
    by (metis (full_types))
next
  case (Cons d p)
  obtain \<alpha>'' where r: "\<alpha>' < d < \<alpha>''" "\<alpha>'' \<lless> p \<lless> \<alpha>" using Cons by auto
  obtain I'' t'' \<beta>'' where i:
      "(I'',t'',\<beta>'') \<in> inter_trace_rec R p {(I, t, \<beta>)}"
      "(I', t', \<beta>') \<in> inter\<^sub>a R d (I'',t'',\<beta>'')"
    using Cons(3) by auto


  show ?case
  proof (rule Cons(1)[OF _ i(1) r(2)], goal_cases)
    case (1 I''' t''')
    show ?case using i(2)
    proof (cases rule: inter\<^sub>aE)
      case ino
      obtain J s where b: "(J,s,\<beta>'') \<in> inter\<^sub>a R d (I''', t''', \<beta>'')" "J \<longrightarrow> I'''"
        using inter\<^sub>aI' inter\<^sub>a_I by blast 
      hence c: "(J,s,\<beta>'') \<in> inter_trace_rec R ((d # p) @ [\<alpha>]) {(I, t, \<beta>)}" 
        using inter_trace_recI[OF 1(1)] by auto
      have "\<forall>f d. d \<hookleftarrow> fwd \<alpha>'\<langle>f\<rangle> d \<longrightarrow> d \<in> unordered (fwdll t' f) \<beta>'\<langle>f\<rangle> \<longrightarrow> (d \<in> unordered (fwdll s f) \<beta>'\<langle>f\<rangle> \<or> nop R d)"
        apply (intro allI impI)
        apply (subgoal_tac "d \<in> unordered (fwdll t'' f) \<beta>''\<langle>f\<rangle>")
        defer 1
        apply (auto simp: unordered_def ino fwdll_def)[1]
        apply (subgoal_tac "(d \<in> unordered (fwdll t''' f) \<beta>''\<langle>f\<rangle> \<or> nop R d)")
        unfolding ino
        apply (subgoal_tac "da \<hookleftarrow> fwd d\<langle>f\<rangle> da")
        defer 1
        apply (auto simp: unordered_def ino fwdll_def)[1]
        defer 1
        using inter\<^sub>a_t'[OF b(1)]  unfolding ino
        apply blast
        apply (subgoal_tac "da \<hookleftarrow> fwd d\<langle>f\<rangle> da")
        defer 1
        apply (auto simp: unordered_def fwdll_def ino)[1]
        apply (subgoal_tac "da \<hookleftarrow> fwd \<alpha>''\<langle>f\<rangle> da \<or> nop R da")
        defer 1
        apply (rule issue)
        
        apply (subgoal_tac "da \<hookleftarrow> fwd (fwd \<alpha>'' d)\<langle>f\<rangle> da")
        prefer 2
        using r(1) apply blast
        apply simp
        apply simp
        using r(1) apply simp
        using 1(3) by blast

      then show ?thesis using c Cons(2) 1(2) ino b(2) by blast
    next
      case ooo
      have t: "\<And>f. \<forall>d. d \<hookleftarrow> fwd \<alpha>''\<langle>f\<rangle> d \<longrightarrow>
          d \<in> unordered (fwdll t'' f)
                \<beta>''\<langle>f\<rangle> \<longrightarrow>
          d \<in> unordered (fwdll t''' f)
                \<beta>''\<langle>f\<rangle> \<or>
          nop R d "
        using 1(3) by auto

      consider (unord) "d \<in> unordered t''' \<beta>''" | (indep) "nop R d " "d \<notin> unordered t''' \<beta>''" 
        using t[of "[]"] r(1) ooo unfolding fwdll_def by auto
      thus ?thesis
      proof (cases)
        case unord
        hence b: "(I''' \<and> order_indep R d \<beta>'',map (\<lambda>\<beta>. fwd \<beta> d) t''',fwd \<beta>'' d) \<in> inter\<^sub>a R d (I''', t''', \<beta>'')"
          using inter\<^sub>aI_ooo by auto
        hence c: "(I''' \<and> order_indep R d \<beta>'',map (\<lambda>\<beta>. fwd \<beta> d) t''',\<beta>') \<in> inter_trace_rec R ((d # p) @ [\<alpha>]) {(I, t, \<beta>)}" 
          using inter_trace_recI[OF 1(1)] ooo by auto
        have "\<forall>f da. da \<hookleftarrow> fwd \<alpha>''\<langle>f@[d]\<rangle> da \<longrightarrow> da \<in> unordered (fwdll t'' (f@[d])) \<beta>''\<langle>f@[d]\<rangle> \<longrightarrow>
                     da \<in> unordered (fwdll t''' (f@[d])) \<beta>''\<langle>f@[d]\<rangle> \<or> nop R da "
          using t by blast

        hence "\<forall>f da. da \<hookleftarrow> fwd \<alpha>'\<langle>f\<rangle> da \<longrightarrow> da \<in> unordered (fwdll t' f) \<beta>'\<langle>f\<rangle> \<longrightarrow> da \<in> unordered
              (fwdll (map (\<lambda>\<beta>. fwd \<beta> d) t''') f) \<beta>'\<langle>f\<rangle> \<or> nop R da "
          unfolding ooo fwdll_def
          using r(1)
          apply simp
          unfolding o_def
          by blast

        then show ?thesis using Cons(2)[OF c] 1(2) ooo by blast
      next
        case indep
        hence b: "(I''',d#t''',\<beta>') \<in> inter\<^sub>a R d (I''', t''', \<beta>'')" 
          using inter\<^sub>aI_ino ooo unfolding nop_def by auto 
        hence c: "(I''',d#t''',\<beta>') \<in> inter_trace_rec R ((d # p) @ [\<alpha>]) {(I, t, \<beta>)}" 
          using inter_trace_recI[OF 1(1)] ooo by auto
        have i: "I''' \<longrightarrow> I'" using 1(2) indep ooo by (auto simp: nop_def)

        have s: "\<alpha>' = \<alpha>''" "map (\<lambda>\<beta>. fwd \<beta> d) t'' = t''" "fwd \<beta>'' d = \<beta>''" using r(1) indep by (auto simp: nop_def)
        have u: "\<forall>f da. da \<hookleftarrow> fwd \<alpha>'\<langle>f\<rangle> da \<longrightarrow> da \<in> unordered (fwdll t' f) \<beta>'\<langle>f\<rangle> \<longrightarrow> 
                        da \<in> unordered (fwdll (d # t''') f) \<beta>'\<langle>f\<rangle> \<or> nop R da"
          using r  1(3) indep unfolding s ooo
        proof (intro allI impI)
          fix f da
          assume a: "da \<hookleftarrow> fwd \<alpha>''\<langle>f\<rangle> da" "da \<in> unordered (fwdll t'' f) \<beta>''\<langle>f\<rangle>"
          hence b: "da \<in> unordered (fwdll t''' f) \<beta>''\<langle>f\<rangle> \<or> nop R da"
            using 1(3) by auto
          moreover have "da \<hookleftarrow> fwd d\<langle>f\<rangle> da"
            using indep unfolding nop_def
            sorry 
              (* Trouble is that we need to show \<alpha> is reorderable, but here we talk in terms of \<alpha>'' *)
              (* \<alpha>'' has fewer reordering constraints, so the fact that it can exec ooo means nothing to \<alpha> *)
              (* so we either show that \<alpha> = \<alpha>'' (due to fwding constraints) or 
                 we change the inductive definition to consider \<alpha>' *)
          ultimately show "da \<in> unordered (fwdll (d # t''') f) \<beta>''\<langle>f\<rangle> \<or> nop R da"
            by (auto simp: unordered_def fwdll_def)
        qed

        show ?thesis using Cons(2)[OF c i u] .
      qed

    next
      case fwd
      obtain J s where b: "(J,s,\<beta>'') \<in> inter\<^sub>a R d (I''', t''', \<beta>'')" "J \<longrightarrow> I'''"
        using inter\<^sub>aI' inter\<^sub>a_I by blast 
      hence c: "(J,s,\<beta>'') \<in> inter_trace_rec R ((d # p) @ [\<alpha>]) {(I, t, \<beta>)}" 
        using inter_trace_recI[OF 1(1)] by auto
      have "\<forall>f d. d \<hookleftarrow> fwd \<alpha>'\<langle>f\<rangle> d \<longrightarrow> d \<in> unordered (fwdll t' f) \<beta>'\<langle>f\<rangle> \<longrightarrow> (d \<in> unordered (fwdll s f) \<beta>'\<langle>f\<rangle> \<or> nop R d \<alpha>)"
        apply (intro allI impI)
        apply (subgoal_tac "d \<in> unordered (fwdll t'' f) \<beta>''\<langle>f\<rangle>")
        defer 1
        apply (auto simp: unordered_def fwd fwdll_def)[1]
        apply (subgoal_tac "(d \<in> unordered (fwdll t''' f) \<beta>''\<langle>f\<rangle> \<or> nop R d)")
        unfolding fwd
        apply (subgoal_tac "da \<hookleftarrow> fwd d\<langle>f\<rangle> da")
        defer 1
        apply (auto simp: unordered_def fwd fwdll_def)[1]
        defer 1
        using inter\<^sub>a_t'[OF b(1)]  unfolding fwd
        apply blast
        apply (subgoal_tac "da \<hookleftarrow> fwd d\<langle>f\<rangle> da")
        defer 1
        apply (auto simp: unordered_def fwdll_def fwd)[1]
        apply (subgoal_tac "da \<hookleftarrow> fwd \<alpha>''\<langle>f\<rangle> da \<or> nop R da")
        defer 1
        apply (rule issue)
        prefer 4
        using 1(3) apply blast
        apply (subgoal_tac "da \<hookleftarrow> fwd (fwd \<alpha>'' d)\<langle>f\<rangle> da")
        prefer 2
        using r(1) apply blast
        apply simp
        apply simp
        using r(1) apply simp
        done

      then show ?thesis using c Cons(2) 1(2) fwd b(2) by blast
    qed
  qed
qed

lemma test:
  assumes "(\<gamma>,I,t) \<in> inter_trace_rec R (pre) S" "\<alpha>' \<lless> pre \<lless> \<alpha>"
  obtains \<gamma>' I' t' where "(\<gamma>',I',t') \<in> inter_trace_rec R (pre@[\<alpha>]) S" "I' \<longrightarrow> I"
  sorry

(*
  if S blocks \<alpha>,
    produces a new S with \<alpha> constraint
    not a problem though as this won't block anything in pre
  if S does not block \<alpha>,
    then you just get the same (\<gamma>,I,t) but with a stronger I and potential forwarding
  
*)

lemma inter_trace_extract:
  assumes "inter_trace R (pre@[\<alpha>]@t) \<beta>" "\<alpha>' \<lless> pre \<lless> \<alpha>"
  shows "inter_trace R (pre@t) \<beta>"
  using assms
  unfolding inter_trace_def
  using test rec_append
  by (smt case_prodI2 old.prod.case)
  

lemma inter_trace_extract:
  assumes "inter_trace R (pre@[\<alpha>]@t) \<beta>" "\<alpha>' \<lless> pre \<lless> \<alpha>"
  shows "inter_trace R (pre@t) \<beta>"
  using assms
proof (induct pre arbitrary: \<alpha>')
  case Nil
  then show ?case using inter_trace_drop by auto
next
  case (Cons \<gamma> pre')
  hence i: "inter_trace R (pre' @ [\<alpha>] @ t) \<beta>" using inter_trace_drop by auto
  obtain \<alpha>'' where r: "\<alpha>' < \<gamma> < \<alpha>''" "\<alpha>'' \<lless> pre' \<lless> \<alpha>" using Cons(3) by auto
  hence i: "inter_trace R (pre' @ t) \<beta>"
    using Cons(1) i by simp 


  show ?case
  proof (auto simp: inter_trace_def split: prod.splits)
    fix \<beta>' I' t' \<beta>'' I'' t''
    assume rec: "(\<beta>', I', t') \<in> inter_trace_rec R (pre' @ t) {(\<beta>,True,[])}"
    assume act: "(\<beta>'', I'', t'') \<in> inter_act R \<gamma> \<beta>' I' t'"

    obtain J s where "(\<beta>',J,s) \<in> inter_trace_rec R (pre' @ [\<alpha>] @ t) {(\<beta>,True,[])}"
      using rec
      sorry

    hence "\<forall>(x,y,z) \<in> inter_act R \<gamma> \<beta>' I' t'. y"
      using Cons(2)
      unfolding inter_trace_def
      apply (auto split: prod.splits)
      sorry

    (*
      Need order_indep given \<gamma> \<beta>', given \<gamma> isn't ordered relative
      to t' @ [\<beta>'].
      
    *)

    hence ord: "(t'' @ [\<beta>'']) \<lhd> \<gamma> \<lhd> (t' @ [\<beta>']) \<longrightarrow> order_indep R \<gamma> \<beta>'"
      unfolding inter_act_def by auto

    have I: "I'" using i rec by (auto simp: inter_trace_def)

    show "I''" using act
    proof (cases rule: inter_actE)
      case ino
      then show ?thesis using I by auto
    next
      case ooo
      then show ?thesis
        using I ord
        by simp
    next
      case (fwd t'' \<alpha>'')
      then show ?thesis using I by auto
    qed
  qed
qed
*)

(*

lemma inter_all_split [simp]:
  "inter_all R t (pre @ post) = (inter_all R t pre \<and> inter_all R (t@pre) post)"
  by (induct pre arbitrary: t) auto

lemma inter_all_trace:
  assumes "inter_all R t (pre @ \<alpha> # post)"
  shows "inter_trace R (t@pre) \<alpha>"
  using assms by auto

lemma inter_all_drop:
  assumes "inter_all R (pre@[\<alpha>]@t) post" "\<alpha>' \<lless> pre \<lless> \<alpha>"
  shows "inter_all R (pre@t) post"
  using assms
proof (induct R "pre@[\<alpha>]@t" post arbitrary: pre \<alpha> t rule: inter_all.induct)
  case (1 R)
  then show ?case by auto
next
  case (2 R \<beta> s)
  show ?case
    using 2(1)[of pre \<alpha> "t@[\<beta>]"] 2(2,3) 
    apply simp
    using inter_trace_extract by auto
qed

lemma inter_all_drop':
  assumes "inter_all R t (pre @ \<alpha> # post)" "\<alpha>' \<lless> t@pre \<lless> \<alpha>"
  shows "inter_all R t (pre @ post)"
proof -
  have s: "inter_all R t pre" "inter_trace R (t@pre) \<alpha>" "inter_all R (t@pre@[\<alpha>]) post"
    using assms(1) by auto
  have "inter_all R (t@pre) post" using s(3) inter_all_drop[where ?t="[]"] assms by auto
  thus ?thesis using s by auto
qed

*)




end

end