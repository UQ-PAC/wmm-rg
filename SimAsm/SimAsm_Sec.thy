theory SimAsm_Sec
  imports SimAsm_Rules "HOL-Algebra.Lattice" "../Security"
begin

fun drop_gamma :: "('r,'v \<times> ('s :: bounded_lattice),'a)varmap' \<Rightarrow> ('r,'v,'a)varmap'"
  where "drop_gamma v = \<lparr> varmap_st = fst o varmap_st v, \<dots> = varmap_rec.more v \<rparr>"

fun sec_aux :: "(('r,'v,'a)varmap' \<Rightarrow> 'b) \<Rightarrow> ('r,'v \<times> ('s :: bounded_lattice),'a)varmap' \<Rightarrow> 'b"
  where "sec_aux auxfn = auxfn o drop_gamma"

fun sec_vc :: "('r,'v,'a) varmap' set \<Rightarrow> ('r,'v \<times> ('s :: bounded_lattice),'a)varmap' set"
  where "sec_vc pred = {ts. drop_gamma ts \<in> pred}"

fun join :: "('s :: bounded_lattice) list \<Rightarrow> 's"
  where 
    "join [] = bot" | 
    "join (a#as) = (sup a (join as))"

fun sec_exp :: "('r,'v) exp \<Rightarrow> ('r,'v \<times> ('s :: bounded_lattice)) exp"
  where
    "sec_exp (Var r) = (Var r)" |
    "sec_exp (Val v) = (Val (v,bot))" |
    "sec_exp (Exp f args) = 
      Exp (\<lambda>vals. (f (map fst vals), join (map snd vals))) (map sec_exp args)"

fun sec_bexp :: "('r,'v) bexp \<Rightarrow> ('r,'v \<times> ('s :: bounded_lattice)) bexp"
  where
    "sec_bexp (Neg e) = Neg (sec_bexp e)" |
    "sec_bexp (Exp\<^sub>B f args) = Exp\<^sub>B (\<lambda>vals. (f (map fst vals))) (map sec_exp args)"

fun low_bexp :: "('r,'v) bexp \<Rightarrow> ('r,'v \<times> ('s :: bounded_lattice),'a)lvarmap' set"
  where "low_bexp b = {s. \<forall>v \<in> deps\<^sub>B b. snd (varmap_st s (Ul v)) = bot}"

fun low_exp :: "('r,'v) exp \<Rightarrow> ('r,'v \<times> ('s :: bounded_lattice),'a)lvarmap' set"
  where "low_exp b = {s. \<forall>v \<in> deps\<^sub>E b. snd (varmap_st s (Ul v)) = bot}"

fun sec_op_vc
  where
    "sec_op_vc v (cmp b) = (sec_vc v \<inter> low_bexp b)" |
    "sec_op_vc v (leak r e) = (sec_vc v \<inter> low_exp e)" |
    "sec_op_vc v _ = (sec_vc v)"

fun sec_op
  where
    "sec_op (cmp b) = (cmp (sec_bexp b))" |
    "sec_op (assign x e) = (assign x (sec_exp e))" |
    "sec_op (leak r e) = (leak r (sec_exp e))" |
    "sec_op nop = nop" |
    "sec_op full_fence = full_fence"

fun sec_lang :: "('r,'v,('r,'v,'a)varmap',('r,'v,'a)lvarmap','a) lang \<Rightarrow> 
                    ('r,'v \<times> ('s :: bounded_lattice),('r,'v \<times> ('s :: bounded_lattice),'a)varmap',('r,'v \<times> ('s :: bounded_lattice),'a)lvarmap','a) lang" where
  "sec_lang (Skip) = Skip " |
  "sec_lang (Op pred op auxfn) = Op (sec_op_vc pred op) (sec_op op) (sec_aux auxfn)" |
  "sec_lang (SimAsm.lang.Seq a b) = SimAsm.lang.Seq (sec_lang a) (sec_lang b) " |
  "sec_lang (If v b t f) = If (sec_op_vc v (cmp b)) (sec_bexp b) (sec_lang t) (sec_lang f)" |
  "sec_lang (While v b Imix Ispec c) = While (sec_op_vc v (cmp b)) (sec_bexp b) (sec_vc Imix) (sec_vc Ispec) (sec_lang c) "

text \<open>Written variables are preserved across @{term sec_lang} transform\<close>
lemma [simp]:
  "wr\<^sub>l (sec_lang c) = wr\<^sub>l c"
proof (induct c)
  case (Op x1 x2 x3)
  then show ?case by (cases x2) auto
qed auto

text \<open>Leaked variables are preserved across @{term sec_lang} transform\<close>
lemma [simp]:
  "lk\<^sub>l (sec_lang c) = lk\<^sub>l c"
proof (induct c)
  case (Op x1 x2 x3)
  then show ?case by (cases x2) auto
qed auto

lemma eq_ev\<^sub>E_sec_exp:
  "\<forall>v\<in>deps\<^sub>E b. fst (y v) = fst (x v) \<Longrightarrow> fst (ev\<^sub>E y (sec_exp b)) = fst (ev\<^sub>E x (sec_exp b))"
proof (induct b)
  case (Var x)
  then show ?case by auto
next
  case (Val x)
  then show ?case by auto
next
  case (Exp x1a x2a)
  then show ?case by (simp add: o_def) (metis (mono_tags, lifting) map_eq_conv)
qed

lemma join_bot[simp]:
  "(join l = bot) = (\<forall>v \<in> set l. v = bot)"
  by (induct l) auto

lemma bot_expE:
  assumes "snd (ev\<^sub>E x (sec_exp e)) = bot"
  obtains "\<forall>v \<in> deps\<^sub>E e. snd (x v) = bot"
  using assms by (induct e) auto

lemma eq_ev\<^sub>B_sec_exp:
  "\<forall>v\<in>deps\<^sub>B b. fst (y v) = fst (x v) \<Longrightarrow> ev\<^sub>B y (sec_bexp b) = ev\<^sub>B x (sec_bexp b)"
proof (induct b)
  case (Neg b)
  then show ?case by simp
next
  case (Exp\<^sub>B x1a x2)
  then show ?case 
    by (simp add: o_def) (metis (mono_tags, lifting) map_eq_conv eq_ev\<^sub>E_sec_exp)
qed

definition ts_pred_of_lvm_pred :: "('r,'v,'a) lvarmap' pred \<Rightarrow> ('r,'v,'a) tstack pred" 
  where "ts_pred_of_lvm_pred P = {ts | ts. mk_lvarmap (tstack_base ts) (vm_of_ts ts) \<in> P }"

locale simasm_sec_rules = 
  simasm_rules locals rg glb +
  security 
    where exists_act = "undefined :: ('r,'v \<times> 's,'a) auxopSt"
    and push = "tstack_push :: ('r,'v \<times> 's,'a) tstack \<Rightarrow> ('r,'v \<times> 's,'a option) frame_scheme \<Rightarrow> ('r,'v \<times> 's,'a) tstack"
  for locals :: "'r set"
  and rg :: "('r, 'v \<times> ('s :: bounded_lattice), 'a) varmap_rec_scheme \<Rightarrow> 'local \<Rightarrow> 'v \<times> 's"
  and glb :: "('r, 'v \<times> 's, 'a) varmap_rec_scheme \<Rightarrow> 'global \<Rightarrow> 'v \<times> 's"

context simasm_sec_rules
begin

definition frame_leq :: "('r, 'v \<times> 's, 'a option) frame_scheme rel"
  where "frame_leq \<equiv> {(f,s). frame_cap f = frame_cap s \<and> 
                              (\<forall>v. (frame_st f v \<noteq> None) = (frame_st s v \<noteq> None)) \<and>
                              (\<forall>v v' r c c'. frame_st f r = Some (v,c) \<and> frame_st s r = Some (v',c') \<longrightarrow>
                                          c = bot \<or> c' = bot \<longrightarrow> v = v')}"

text \<open>The invariant security policy, demanding equivalent values given a bot classification\<close>
definition sec_inv :: "('r,'v \<times> 's,'a) tstack rel"
  where "sec_inv = {(s,s'). frame_rel frame_leq s s' \<and> tstack_len s = tstack_len s' }"

lemma sec_inv_lookup_helper:
  assumes "Is_tstack s" "Is_tstack s'" "set (zip s s') \<subseteq> frame_leq" "length s = length s'"
  shows "snd (lookup s r) = bot \<or> snd (lookup s' r) = bot \<longrightarrow> fst (lookup s r) = fst (lookup s' r)"
  using assms
proof (induct arbitrary: s' rule: Is_tstack_induct)
  case (Base x)
  then obtain z where s: "s' = [z]" "(x,z) \<in> frame_leq" by (cases s'; auto)
  then obtain c v c' v' where l: "frame_st x r = Some (v,c)" "frame_st z r = Some (v',c')"
    using Base by (auto simp: Is_tstack_def split: if_splits option.splits) fastforce
  then show ?case using s by (auto simp: frame_leq_def)
next
  case (Frame x xs)
  then obtain z zs where s: "s' = z#zs" "(x,z) \<in> frame_leq" "Is_tstack zs"
                          "set (zip xs zs) \<subseteq> frame_leq" "length xs = length zs"
    by (cases s'; auto simp: Is_tstack_def split: if_splits)
  show ?case
  proof (cases "r \<in> frame_cap x \<and> (\<exists>v. frame_st x r = Some v)")
    case True
    then obtain c v c' v' where l: "frame_st x r = Some (v,c)" "frame_st z r = Some (v',c')"
      using s(2) by (auto simp: frame_leq_def split: if_splits option.splits) blast
    then show ?thesis using s(1,2) True by (auto simp: frame_leq_def)
  next
    case False
    hence l: "lookup (x # xs) r = lookup xs r" "lookup (z # zs) r = lookup zs r"
      using s(2) by (auto simp: frame_leq_def split: option.splits) blast
    show ?thesis unfolding l s(1) using s(3,4,5) by (rule Frame)
  qed
qed

lemma sec_inv_lookup:
  assumes "(s,s') \<in> sec_inv"
  shows "\<forall>v. snd (tlookup s v) = bot \<or> snd (tlookup s' v) = bot \<longrightarrow> 
          fst (tlookup s v) = fst (tlookup s' v)"
  using assms unfolding sec_inv_def
  apply clarsimp
  apply transfer
  using sec_inv_lookup_helper by blast

lemma sec_inv_tauxupdI:
  assumes "(a,b) \<in> sec_inv"
  shows "(tauxupd a f, tauxupd b f') \<in> sec_inv"
  using assms unfolding sec_inv_def
  apply simp
  apply transfer
  apply (auto simp: auxupd_def split: if_splits list.splits)
  apply (auto simp: frame_leq_def)
  done

lemma frame_leq_auxupdl:
  "(a, b) \<in> frame_leq \<Longrightarrow> (a\<lparr>frame.more := e\<rparr>, b) \<in> frame_leq"
  unfolding frame_leq_def by force

lemma frame_leq_auxupdr:
  "(a, b) \<in> frame_leq \<Longrightarrow> (a, b\<lparr>frame.more := e\<rparr>) \<in> frame_leq"
  unfolding frame_leq_def by force

lemma sec_inv_tauxupdlI:
  assumes "(a,b) \<in> sec_inv"
  shows "(tauxupd a f, b) \<in> sec_inv"
  using assms unfolding sec_inv_def
  apply simp
  apply transfer
  apply (auto simp: auxupd_def split: if_splits list.splits)
  apply (case_tac b)
  apply (auto intro: frame_leq_auxupdl)
  done

lemma sec_inv_tauxupdrI:
  assumes "(a,b) \<in> sec_inv"
  shows "(a, tauxupd b f') \<in> sec_inv"
  using assms unfolding sec_inv_def
  apply simp
  apply transfer
  apply (auto simp: auxupd_def split: if_splits list.splits)
  apply (case_tac a)
  apply (auto intro: frame_leq_auxupdr)
  done


lemma frame_leq_update:
  assumes "(a,b) \<in> frame_leq"
  assumes "(snd e = bot \<or> snd e' = bot) \<longrightarrow> fst e = fst e'"
  shows "(a\<lparr>frame_st := (frame_st a)(x \<mapsto> e)\<rparr>, b\<lparr>frame_st := (frame_st b)(x \<mapsto> e')\<rparr>) \<in> frame_leq"
  using assms 
  unfolding frame_leq_def
  by auto

lemma sec_inv_tupdate_helper:
  assumes "Is_tstack a" "Is_tstack b"
  assumes "set (zip a b) \<subseteq> frame_leq" 
  assumes "length a = length b"
  assumes "(snd e = bot \<or> snd e' = bot) \<longrightarrow> fst e = fst e'"
  shows "set (zip (update a x e) (update b x e')) \<subseteq> frame_leq"
  using assms(1,2,3,4)
proof (induct arbitrary: b rule: Is_tstack_induct)
  case (Base x)
  then show ?case using assms(5) by (cases b; auto intro!: frame_leq_update)
next
  case (Frame a xs)
  obtain z zs where z: "b = z#zs" "Is_tstack zs" "set (zip xs zs) \<subseteq> frame_leq" 
                    "length xs = length zs" "(a,z) \<in> frame_leq"
    using Frame by (cases b; auto simp: Is_tstack_def split: if_splits)
  moreover have "frame_cap z = frame_cap a"
    using z by (auto simp: frame_leq_def)
  ultimately show ?case
    using Frame(1) by (cases "x \<in> frame_cap a"; auto intro: frame_leq_update[OF _ assms(5)])
qed

lemma sec_inv_tupdateI:
  assumes "(a,b) \<in> sec_inv"
  assumes "(snd e = bot \<or> snd e' = bot) \<longrightarrow> fst e = fst e'"
  shows "(tupdate a x e, tupdate b x e') \<in> sec_inv"
  using assms unfolding sec_inv_def
  apply simp
  apply transfer
  using sec_inv_tupdate_helper by auto

lemma [simp]:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> sec_inv"
  shows "tstack_len m\<^sub>2 = tstack_len m\<^sub>1"
  using assms unfolding sec_inv_def by (auto)

lemma set_zip_sym:
  assumes "(a,b) \<in> set (zip l l')"
  shows "(b,a) \<in> set (zip l' l)"
  using assms
proof (induct l arbitrary: l')
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by (cases l') auto
qed

lemma frame_leq_sym:
  assumes "(s\<^sub>1,s\<^sub>2) \<in> frame_leq"
  shows "(s\<^sub>2,s\<^sub>1) \<in> frame_leq"
  using assms unfolding frame_leq_def by blast

lemma sec_inv_sym:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> sec_inv"
  shows "(m\<^sub>2, m\<^sub>1) \<in> sec_inv"
  using assms unfolding sec_inv_def
  apply auto
  apply transfer
  apply (auto)
  apply (drule set_zip_sym)
  using frame_leq_sym by blast

lemma sec_inv_push:
  "(tstack_push m\<^sub>1 s\<^sub>1, tstack_push m\<^sub>2 s\<^sub>2) \<in> sec_inv =
    ( (m\<^sub>1,m\<^sub>2) \<in> sec_inv \<and> (s\<^sub>1,s\<^sub>2) \<in> frame_leq )"
  unfolding sec_inv_def
  apply transfer
  apply clarsimp
  by blast

section \<open>Properties over atomic actions\<close>

subsection \<open>Full Security\<close>

text \<open>A secure atomic action guarantees progress and preserves low equivalence\<close>
definition atom_sec
  where "atom_sec \<equiv> {lift\<^sub>b v (sec_op op) f | v op f. 
          \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'. (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh (lift\<^sub>b v (sec_op op) f)  \<longrightarrow>
          (m\<^sub>1 \<in> vc (lift\<^sub>b v (sec_op op) f) \<longrightarrow> (\<exists>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh (lift\<^sub>b v (sec_op op) f))) \<and> 
          (\<forall>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh (lift\<^sub>b v (sec_op op) f) \<longrightarrow> (m\<^sub>1', m\<^sub>2') \<in> sec_inv)}"

lemma sec_inv_exp1:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> sec_inv"
  assumes "snd (ev\<^sub>E (tlookup m\<^sub>1) (sec_exp e)) = bot"
  shows "fst (ev\<^sub>E (tlookup m\<^sub>1) (sec_exp e)) = fst (ev\<^sub>E (tlookup m\<^sub>2) (sec_exp e))"
  apply (rule eq_ev\<^sub>E_sec_exp)
  using assms sec_inv_lookup by (auto elim!: bot_expE)

lemma sec_inv_exp2:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> sec_inv"
  assumes "snd (ev\<^sub>E (tlookup m\<^sub>2) (sec_exp e)) = bot"
  shows "fst (ev\<^sub>E (tlookup m\<^sub>1) (sec_exp e)) = fst (ev\<^sub>E (tlookup m\<^sub>2) (sec_exp e))"
  using sec_inv_sym sec_inv_exp1 assms by force

lemma sec_inv_bexp1:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> sec_inv"
  assumes "\<forall>v\<in>deps\<^sub>B e. snd (tlookup m\<^sub>1 v) = bot"
  shows " (ev\<^sub>B (tlookup m\<^sub>1) (sec_bexp e)) = (ev\<^sub>B (tlookup m\<^sub>2) (sec_bexp e))"
  apply (rule eq_ev\<^sub>B_sec_exp)
  using assms sec_inv_lookup by (auto elim!: bot_expE) 

lemma atom_sec_detfI:
  assumes "\<forall>m m\<^sub>1. (m,m\<^sub>1) \<in> beh (lift\<^sub>b v (sec_op op) f) = (m\<^sub>1 = s m)"
  assumes "\<forall>m\<^sub>1 m\<^sub>2. (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<longrightarrow> (s m\<^sub>1, s m\<^sub>2) \<in> sec_inv"
  shows "(lift\<^sub>b v (sec_op op) f) \<in> atom_sec"
  using assms unfolding atom_sec_def
  apply (auto simp del: lift\<^sub>b.simps)
  by (rule exI)+ auto

lemma atom_sec_idI:
  assumes "\<And>m m\<^sub>1. (m,m\<^sub>1) \<in> beh (lift\<^sub>b v (sec_op op) f) \<Longrightarrow> m\<^sub>1 = tauxupd m s \<or> m\<^sub>1 = m"
  assumes "\<forall>m\<^sub>1 m\<^sub>1' m\<^sub>2. m\<^sub>1 \<in> vc (lift\<^sub>b v (sec_op op) f) \<and> (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh (lift\<^sub>b v (sec_op op) f) \<longrightarrow> (\<exists>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh (lift\<^sub>b v (sec_op op) f))"
  shows "(lift\<^sub>b v (sec_op op) f) \<in> atom_sec"
  using assms(2) unfolding atom_sec_def  
  apply (auto simp del: lift\<^sub>b.simps)
  apply (rule exI)+
  apply (intro allI impI conjI)
   apply blast
   apply blast
  apply (elim conjE)
  apply (drule assms(1))+
  apply (auto intro: sec_inv_tauxupdlI sec_inv_tauxupdrI sec_inv_tauxupdI)
  done  

lemma cmp_atom:
  assumes "lift\<^sub>b (op_vc (cmp (sec_bexp c1)) (sec_op_vc x1 (cmp c1))) (sec_op (cmp c1)) taux = \<alpha>"
  shows "\<alpha> \<in> atom_sec"
  unfolding sym[OF assms[simplified sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps]] 
  apply (rule atom_sec_idI) 
   apply auto[1]
  apply simp
  apply clarify
  apply (elim disjE)
  apply (rule exI)
   apply (intro conjI disjI1 relcompI)
     apply clarsimp
   apply (intro conjI disjI1 relcompI)
  apply simp
  using sec_inv_bexp1 apply blast
    apply force
   apply force
  apply (rule exI)
  apply (intro conjI disjI2)
   apply simp
  by auto

lemma ncmp_atom:
  assumes "lift\<^sub>b (op_vc (ncmp (sec_bexp c1)) (sec_op_vc x1 (ncmp c1))) (sec_op (ncmp c1)) taux = \<alpha>"
  shows "\<alpha> \<in> atom_sec"
  unfolding sym[OF assms[simplified sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps]] 
  apply (rule atom_sec_idI) 
   apply auto[1]
  apply simp
  apply clarify
  apply (elim disjE)
  apply (rule exI)
   apply (intro conjI disjI1 relcompI)
     apply clarsimp
   apply (intro conjI disjI1 relcompI)
  apply simp
  using sec_inv_bexp1[where ?e="Neg e" for e] apply simp 
    apply force
   apply force
  apply (rule exI)
  apply (intro conjI disjI2)
   apply simp
  by auto

subsection \<open>Atom Simulation Relation\<close>

definition atom_leq 
  where "atom_leq \<equiv> {(\<alpha>,\<beta>s). 
          \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'. (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha>  \<longrightarrow> m\<^sub>1 \<in> vc \<alpha> \<longrightarrow>
          (\<exists>m\<^sub>2' \<beta>. \<beta> \<in> \<beta>s \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta>) \<and> 
          (\<forall>m\<^sub>2' \<beta>. \<beta> \<in> \<beta>s \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta> \<longrightarrow> (m\<^sub>1', m\<^sub>2') \<in> sec_inv)} \<inter>
          {(\<alpha>,\<beta>s). \<forall>\<beta>\<in>\<beta>s. \<forall>(m,m') \<in> beh \<beta>. tstack_len m = tstack_len m'} \<inter>
          {(\<alpha>,\<beta>s). \<forall>\<beta>\<in>\<beta>s. tag \<beta> = tag \<alpha>}"

lemma [simp]:
  "(a, b) \<in> beh (lift\<^sub>b v op f) \<Longrightarrow> tstack_len a = tstack_len b"
  by (cases op) (auto simp: liftg_def)

lemma mem_pairI:
  assumes "F a b"
  shows "(a,b) \<in> {(a,b). F a b}"
  using assms by auto

lemma atom_sec_leq:
  "\<forall>\<alpha> \<in> atom_sec. (\<alpha>,{\<alpha>}) \<in> atom_leq"
proof (intro ballI)
  fix \<alpha> assume "\<alpha> \<in> atom_sec"
  then obtain v op f where \<alpha>: "\<alpha> = lift\<^sub>b v op f"
    "\<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'. (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh (lift\<^sub>b v op f) \<and> m\<^sub>1 \<in> vc (lift\<^sub>b v op f) \<longrightarrow>
            (\<exists>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh (lift\<^sub>b v op f))"
    "\<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1' m\<^sub>2'. (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh (lift\<^sub>b v op f) \<and> (m\<^sub>2, m\<^sub>2') \<in> beh (lift\<^sub>b v op f) \<longrightarrow>
            (m\<^sub>1', m\<^sub>2') \<in> sec_inv"
    unfolding atom_sec_def by blast
  show "(\<alpha>,{\<alpha>}) \<in> atom_leq" unfolding \<alpha>(1) atom_leq_def
    apply (intro allI impI conjI mem_pairI IntI)
    using \<alpha>(2) apply fast
    using \<alpha>(3) apply blast
    by auto
qed


lemma atom_leq_sound:
  "flatten atom_leq \<subseteq> {(\<alpha>, \<beta>). le_basic \<alpha> \<beta> sec_inv}"
  unfolding flatten_def atom_leq_def le_basic_def by blast

section \<open>Reordering Implications\<close>

text \<open>
Need to show reordering / forwarding won't produce an insecure operation.
As the command may feature many reordering relations, we need to identify them
all and prove this property for each.
\<close>
lemma re_stable_full:
  assumes "(\<alpha>, \<beta>s) \<in> atom_leq"
  assumes "w \<in> {sc, reorder_inst}"
  assumes "w \<alpha>' \<gamma> \<alpha>"
  assumes "\<gamma> \<in> atom_sec"
  shows "\<exists>\<beta>s'. (\<alpha>', \<beta>s') \<in> atom_leq \<and> (\<forall>\<beta>\<in>\<beta>s'. \<exists>\<beta>p\<in>\<beta>s. w \<beta> \<gamma> \<beta>p)"
proof -
  have w: "w = reorder_inst" using assms(2,3) by (auto simp: sc_def)

  show ?thesis
  proof (cases "\<exists>x e. fst (tag \<gamma>) = assign x e")
    case True
    then obtain x e f where t: "tag \<gamma> = (assign x e,f)" by (cases \<gamma>, auto)
    have "\<exists>v op f. \<gamma> = lift\<^sub>b v (sec_op op) f" using assms(4) unfolding atom_sec_def by auto
    then obtain s where sec: "e = sec_exp s" using t 
      by auto (case_tac "op"; auto simp: liftg_def)

    hence a: "\<And>\<alpha>' \<alpha>. w \<alpha>' \<gamma> \<alpha> = (\<alpha>' = fwd\<^sub>s \<alpha> (assign x e,f) \<and> re\<^sub>i (assign x e) (fst (tag \<alpha>)))"
      using t unfolding w reorder_inst_def by (cases \<gamma>; auto)
    hence \<alpha>: "\<alpha>' = fwd\<^sub>s \<alpha> (assign x e,f)" "re\<^sub>i (assign x e) (fst (tag \<alpha>))"
      using assms(3) by blast+
    let ?bs = "{fwd\<^sub>s \<alpha> (assign x e,f) | \<alpha>. \<alpha> \<in> \<beta>s}"
    have b: "\<And>\<beta>. \<beta> \<in> \<beta>s \<Longrightarrow> tag \<beta> = tag \<alpha>" using assms(1) unfolding atom_leq_def by blast

    have c: "\<forall>\<beta>\<in>?bs. \<exists>\<beta>p\<in>\<beta>s. w \<beta> \<gamma> \<beta>p" unfolding a
    proof (rule ballI)
      fix \<beta>' assume "\<beta>' \<in> {fwd\<^sub>s \<alpha> (assign x e, f) |\<alpha>. \<alpha> \<in> \<beta>s}"
      then obtain \<beta> where c: "\<beta>' = fwd\<^sub>s \<beta> (assign x e, f)" "\<beta> \<in> \<beta>s" by auto
      have "re\<^sub>i (assign x e) (fst (tag \<beta>))" using c(2) \<alpha>(2) b by simp
      thus "\<exists>\<beta>p\<in>\<beta>s. \<beta>' = fwd\<^sub>s \<beta>p (assign x e, f) \<and> re\<^sub>i (assign x e) (fst (tag \<beta>p))"
        using c by blast
    qed

    have "(\<alpha>', ?bs) \<in> {(\<alpha>, \<beta>s). \<forall>\<beta>\<in>\<beta>s. tag \<beta> = tag \<alpha>}"
    proof (intro mem_pairI ballI)
      fix \<beta>' assume "\<beta>' \<in> ?bs"
      then obtain \<beta> where c: "\<beta>' = fwd\<^sub>s \<beta> (assign x e, f)" "\<beta> \<in> \<beta>s" by auto
      hence "tag \<beta> = tag \<alpha>" using b by auto
      thus "tag \<beta>' = tag \<alpha>'" unfolding c \<alpha> by (cases \<alpha>; cases \<beta>; auto)
    qed
    moreover have "(\<alpha>', ?bs) \<in> {(\<alpha>, \<beta>s). \<forall>\<beta>\<in>\<beta>s. \<forall>(m, m')\<in>beh \<beta>. tstack_len m = tstack_len m'}"
    proof (intro mem_pairI ballI)
      fix \<beta>' p assume a: "\<beta>' \<in> ?bs" "p \<in> beh \<beta>'"
      then obtain \<beta> where c: "\<beta>' = fwd\<^sub>s \<beta> (assign x e, f)" "\<beta> \<in> \<beta>s" by auto
      hence b: "beh \<beta>' = fwd_rel (beh \<beta>) x e"
        unfolding c by (cases \<beta>; auto)
      moreover have "\<forall>(m,m') \<in> beh \<beta>. tstack_len m = tstack_len m'"
        using assms(1) atom_leq_def c(2) by fastforce
      ultimately show "case p of (m, m') \<Rightarrow> tstack_len m = tstack_len m'"
        unfolding fwd_rel_def using a(2) by auto
    qed
    moreover have "(\<alpha>', ?bs) \<in> {(\<alpha>, \<beta>s). \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'.
           (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha> \<longrightarrow>
           m\<^sub>1 \<in> vc \<alpha> \<longrightarrow> (\<exists>m\<^sub>2' \<beta>. \<beta> \<in> \<beta>s \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta>)}"
    proof (intro mem_pairI ballI impI allI, elim conjE)
      fix m\<^sub>1 m\<^sub>2 m\<^sub>1' assume a: "(m\<^sub>1, m\<^sub>2) \<in> sec_inv" "(m\<^sub>1, m\<^sub>1') \<in> beh \<alpha>'" "m\<^sub>1 \<in> vc \<alpha>'" 
      have c: "beh \<alpha>' = fwd_rel (beh \<alpha>) x e" using \<alpha> by (cases \<alpha>; auto)
      have d: "vc \<alpha>' = fwd_vc (vc \<alpha>) x e" using \<alpha> by (cases \<alpha>; auto)
      then obtain m' where m:
          "(tupdate m\<^sub>1 x (ev\<^sub>E (tlookup m\<^sub>1) e), m') \<in> beh \<alpha>" "m\<^sub>1' = tupdate m' x (tlookup m\<^sub>1 x)"
          "tupdate m\<^sub>1 x (ev\<^sub>E (tlookup m\<^sub>1) e) \<in> vc \<alpha>"
        using a c by (auto simp: fwd_rel_def fwd_vc_def)
      moreover have "(tupdate m\<^sub>1 x (ev\<^sub>E (tlookup m\<^sub>1) e), tupdate m\<^sub>2 x (ev\<^sub>E (tlookup m\<^sub>2) e)) \<in> sec_inv"
        using a(1) apply (rule sec_inv_tupdateI)
        unfolding sec using a(1) sec_inv_exp1 sec_inv_exp2 by blast
      then obtain \<beta> m\<^sub>2' where \<beta>: "\<beta> \<in> \<beta>s" "(tupdate m\<^sub>2 x (ev\<^sub>E (tlookup m\<^sub>2) e), m\<^sub>2') \<in> beh \<beta>"
        using assms(1) m unfolding atom_leq_def by blast
      hence "(m\<^sub>2, tupdate m\<^sub>2' x (tlookup m\<^sub>2 x)) \<in> beh (fwd\<^sub>s \<beta> (assign x e, f))"
        by (cases \<beta>; auto simp: fwd_rel_def)
      thus "\<exists>m\<^sub>2' \<beta>. \<beta> \<in> {fwd\<^sub>s \<alpha> (assign x e, f) |\<alpha>. \<alpha> \<in> \<beta>s} \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta>"
        using \<beta>(1) by blast
    qed
    moreover have "(\<alpha>', ?bs) \<in> {(\<alpha>, \<beta>s). \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1' m\<^sub>2' \<beta>.
           (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<longrightarrow> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha> \<longrightarrow> m\<^sub>1 \<in> vc \<alpha> \<longrightarrow> \<beta> \<in> \<beta>s \<longrightarrow> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta> \<longrightarrow>
            (m\<^sub>1', m\<^sub>2') \<in> sec_inv}"
    proof (intro mem_pairI ballI impI allI)
      fix m\<^sub>1 m\<^sub>2 m\<^sub>1' m\<^sub>2' \<beta>' assume a: "(m\<^sub>1, m\<^sub>2) \<in> sec_inv" "(m\<^sub>1, m\<^sub>1') \<in> beh \<alpha>'" "m\<^sub>1 \<in> vc \<alpha>'" 
          "\<beta>' \<in> {fwd\<^sub>s \<alpha> (assign x e, f) |\<alpha>. \<alpha> \<in> \<beta>s}" "(m\<^sub>2, m\<^sub>2') \<in> beh \<beta>'"
      then obtain \<beta> where \<beta>: "\<beta> \<in> \<beta>s" "\<beta>' = fwd\<^sub>s \<beta> (assign x e, f)" by auto
      hence b: "beh \<beta>' = fwd_rel (beh \<beta>) x e" by (cases \<beta>; auto)
      have c: "beh \<alpha>' = fwd_rel (beh \<alpha>) x e" using \<alpha> by (cases \<alpha>; auto)
      have d: "vc \<alpha>' = fwd_vc (vc \<alpha>) x e" using \<alpha> by (cases \<alpha>; auto)

      have s: "\<And>m\<^sub>1 m\<^sub>2 m\<^sub>1' m\<^sub>2'. (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<Longrightarrow> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha> \<Longrightarrow> m\<^sub>1 \<in> vc \<alpha> \<Longrightarrow> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta> \<Longrightarrow> (m\<^sub>1', m\<^sub>2') \<in> sec_inv"
        using \<beta> assms(1) unfolding atom_leq_def by blast

      show "(m\<^sub>1', m\<^sub>2') \<in> sec_inv" using a(1,2,3,5) unfolding b c d fwd_rel_def fwd_vc_def
        apply auto
        apply (rule sec_inv_tupdateI)
         apply (rule s)
            defer 1
        apply blast
        apply blast
        apply blast
        using sec_inv_lookup apply blast
        apply (rule sec_inv_tupdateI)
         apply blast
        unfolding sec
        using sec_inv_exp1 sec_inv_exp2 by blast
    qed
    ultimately have "(\<alpha>', ?bs) \<in> atom_leq" unfolding atom_leq_def by blast
    then show ?thesis using c by blast
  next
    case False
    hence a: "\<forall>\<alpha>' \<alpha>. w \<alpha>' \<gamma> \<alpha> = (\<alpha>' = \<alpha> \<and> re\<^sub>i (fst (tag \<gamma>)) (fst (tag \<alpha>)))" 
      unfolding w reorder_inst_def by (cases \<gamma>; auto; case_tac a; simp)
    moreover have "\<forall>\<beta> \<in> \<beta>s. tag \<beta> = tag \<alpha>" using assms(1) unfolding atom_leq_def by blast
    moreover have "\<alpha>' = \<alpha>" "re\<^sub>i (fst (tag \<gamma>)) (fst (tag \<alpha>))" using assms(3) a by auto
    ultimately show ?thesis using assms(1) by metis
  qed
qed

lemma re_stableI:
  "re_stable atom_sec atom_leq {sc, reorder_inst}"
  unfolding re_stable_def using re_stable_full by blast

section \<open>Low Equivalent Frames\<close>

text \<open>
Define a low equivalence relation from stack frames that exist within program commands.
Effectively forces their shapes to align and follows standard low equivalence for defined values.
\<close>

lemma refl_frame_leq:
  shows "refl frame_leq"
  by (rule reflI) (auto simp: frame_leq_def)

lemma atom_frame_leq_full:
  assumes "(\<alpha>, \<beta>s) \<in> atom_leq" "(s\<^sub>1, s\<^sub>2) \<in> frame_leq"
  shows "\<exists>\<beta>s'. ((tag \<alpha>, poppred' s\<^sub>1 (vc \<alpha>), poprel' s\<^sub>1 s\<^sub>1' (beh \<alpha>)), \<beta>s') \<in> atom_leq \<and>
                (\<forall>\<beta>\<in>\<beta>s'. \<exists>\<beta>p\<in>\<beta>s. \<exists>s\<^sub>2'.
                     \<beta> = (tag \<beta>p, poppred' s\<^sub>2 (vc \<beta>p), poprel' s\<^sub>2 s\<^sub>2' (beh \<beta>p)) \<and>
                     (s\<^sub>1', s\<^sub>2') \<in> frame_leq)"
proof -
  let ?bs = "{(tag \<beta>, poppred' s\<^sub>2 (vc \<beta>), poprel' s\<^sub>2 s\<^sub>2' (beh \<beta>))| \<beta> s\<^sub>2'. \<beta> \<in> \<beta>s \<and> (s\<^sub>1', s\<^sub>2') \<in> frame_leq}"
  have "\<forall>\<beta>\<in>?bs. \<exists>\<beta>p\<in>\<beta>s. \<exists>s\<^sub>2'. \<beta> = (tag \<beta>p, poppred' s\<^sub>2 (vc \<beta>p), poprel' s\<^sub>2 s\<^sub>2' (beh \<beta>p)) \<and> (s\<^sub>1', s\<^sub>2') \<in> frame_leq"
    by blast
  moreover have "((tag \<alpha>, poppred' s\<^sub>1 (vc \<alpha>), poprel' s\<^sub>1 s\<^sub>1' (beh \<alpha>)), ?bs) \<in> atom_leq" (is "(?a,?bs) \<in> atom_leq")
    unfolding atom_leq_def
  proof (intro mem_pairI IntI conjI ballI allI impI; (elim conjE)?)
    fix m\<^sub>1 m\<^sub>2 m\<^sub>1' m\<^sub>2' \<beta>'
    assume a: "(m\<^sub>1, m\<^sub>2) \<in> sec_inv" "\<beta>' \<in> ?bs" "(m\<^sub>2, m\<^sub>2') \<in> beh \<beta>'" "(m\<^sub>1, m\<^sub>1')\<in> beh ?a" "m\<^sub>1 \<in> vc ?a" 
    then obtain \<beta> s\<^sub>2' where b: "\<beta> \<in> \<beta>s" "\<beta>' = (tag \<beta>, poppred' s\<^sub>2 (vc \<beta>), poprel' s\<^sub>2 s\<^sub>2' (beh \<beta>))" "(s\<^sub>1', s\<^sub>2') \<in> frame_leq"
      using a(1) by auto
    have "(tstack_push m\<^sub>1 s\<^sub>1, tstack_push m\<^sub>2 s\<^sub>2) \<in> sec_inv" using a assms(2) sec_inv_push by auto
    moreover have "(tstack_push m\<^sub>2 s\<^sub>2, tstack_push m\<^sub>2' s\<^sub>2') \<in> beh \<beta>" 
                  "(tstack_push m\<^sub>1 s\<^sub>1, tstack_push m\<^sub>1' s\<^sub>1') \<in> beh \<alpha>" "tstack_push m\<^sub>1 s\<^sub>1 \<in> vc \<alpha>" 
      using a(3,4,5) b(2) unfolding poprel'_def poppred'_def by auto
    ultimately have "(tstack_push m\<^sub>1' s\<^sub>1', tstack_push m\<^sub>2' s\<^sub>2') \<in> sec_inv" 
      using assms(1) b(1) unfolding atom_leq_def by blast
    thus "(m\<^sub>1', m\<^sub>2') \<in> sec_inv" using sec_inv_push by auto
  next
    fix m\<^sub>1 m\<^sub>2 m\<^sub>1'  
    assume a: "(m\<^sub>1, m\<^sub>2) \<in> sec_inv" "(m\<^sub>1, m\<^sub>1')\<in> beh ?a" "m\<^sub>1 \<in> vc ?a" 
    have "(tstack_push m\<^sub>1 s\<^sub>1, tstack_push m\<^sub>2 s\<^sub>2) \<in> sec_inv" using a assms(2) sec_inv_push by auto
    moreover have "(tstack_push m\<^sub>1 s\<^sub>1, tstack_push m\<^sub>1' s\<^sub>1') \<in> beh \<alpha>" "tstack_push m\<^sub>1 s\<^sub>1 \<in> vc \<alpha>" 
      using a unfolding poprel'_def poppred'_def by auto
    ultimately obtain \<beta> m\<^sub>2' where b: "\<beta> \<in> \<beta>s" "(tstack_push m\<^sub>2 s\<^sub>2, m\<^sub>2') \<in> beh \<beta>" 
        "tstack_len (tstack_push m\<^sub>2 s\<^sub>2) = tstack_len m\<^sub>2'" "(tstack_push m\<^sub>1' s\<^sub>1', m\<^sub>2') \<in> sec_inv"
      using assms(1) unfolding atom_leq_def by blast
    obtain m s where m: "m\<^sub>2' = tstack_push m s" using b(3)
      by transfer (case_tac m\<^sub>2'; auto simp: Is_tstack_def split: if_splits) 
    hence "(s\<^sub>1',s) \<in> frame_leq" using b(4) sec_inv_push  by auto
    hence "(tag \<beta>, poppred' s\<^sub>2 (vc \<beta>), poprel' s\<^sub>2 s (beh \<beta>)) \<in> ?bs" (is "?b \<in> ?bs")
      using b(1) by blast
    moreover have "(m\<^sub>2, m) \<in> beh ?b" using b(2) by (auto simp: m poppred'_def poprel'_def)
    ultimately show "\<exists>m\<^sub>2' \<beta>. \<beta> \<in> ?bs \<and> (m\<^sub>2, m\<^sub>2') \<in> beh \<beta>" by fastforce
  next
    fix p \<beta>' assume a: "\<beta>' \<in> ?bs" "p \<in> beh \<beta>'"
    then obtain \<beta> s\<^sub>2' where b: "\<beta> \<in> \<beta>s" "\<beta>' = (tag \<beta>, poppred' s\<^sub>2 (vc \<beta>), poprel' s\<^sub>2 s\<^sub>2' (beh \<beta>))" "(s\<^sub>1', s\<^sub>2') \<in> frame_leq"
      by auto
    hence "\<forall>(m,m') \<in> beh \<beta>. tstack_len m = tstack_len m'" using assms(1) by (auto simp: atom_leq_def)
    thus "case p of (m, m') \<Rightarrow> tstack_len m = tstack_len m'"
      using a(2) unfolding b(2) by (auto simp: poprel'_def)
  qed (insert assms(1); auto simp: atom_leq_def)
  ultimately show ?thesis by blast
qed

lemma atom_frame_leq:
  "pop_stable atom_leq frame_leq"
  unfolding pop_stable_def using atom_frame_leq_full by blast

section \<open>Final Security Theorem\<close>

lemma atom_assertI:
  "(lift\<^sub>b (op_vc (sec_op op) (sec_op_vc v op)) (sec_op op) (f \<circ> drop_gamma \<circ> vm_of_ts)) \<in> atom_sec"
proof (cases op)
  case (assign x e)
  let ?f = "\<lambda>m. tauxupd (tupdate m x (ev\<^sub>E (tlookup m) (sec_exp e))) (f \<circ> drop_gamma \<circ> vm_of_ts)"
  show ?thesis
    apply (rule atom_sec_detfI[where ?s="?f"])
    by (auto simp add: sec_inv_exp1 sec_inv_exp2 assign relcomp_unfold liftg_def
               intro!: sec_inv_tauxupdI sec_inv_tupdateI)    
next
  case (cmp b)
  show ?thesis
    apply (rule atom_sec_idI)
    apply (auto simp: cmp)[1]
    unfolding cmp sec_op.simps op_vc.simps sec_op_vc.simps lift\<^sub>b.simps
    apply clarsimp
    apply (erule disjE)
     apply (intro exI disjI1 relcompI conjI)
    using sec_inv_bexp1 by auto
next
  case (leak x e)
  let ?f = "\<lambda>m. tauxupd (tupdate m x (ev\<^sub>E (tlookup m) (sec_exp e))) (f \<circ> drop_gamma \<circ> vm_of_ts)"
  show ?thesis
    apply (rule atom_sec_detfI[where ?s="?f"])
    by (auto simp add: sec_inv_exp1 sec_inv_exp2 leak relcomp_unfold liftg_def
               intro!: sec_inv_tauxupdI sec_inv_tupdateI)    
next
  case full_fence
  show ?thesis by (rule atom_sec_idI) (auto simp: full_fence)    
next
  case nop
  show ?thesis by (rule atom_sec_idI) (auto simp: nop liftg_def)    
qed

lemma prog_rel_secI:
  assumes "prog_rel r r atom_sec {sc, reorder_inst} frame_leq"
  shows "prog_rel
     (lift\<^sub>c (ts_lang_of_vm_lang (sec_lang c)) r w)
     (lift\<^sub>c (ts_lang_of_vm_lang (sec_lang c)) r w)
     atom_sec {sc, reorder_inst} frame_leq"
  using assms
proof (induct c arbitrary: r w)
  case Skip
  then show ?case by (auto intro: prog_rel.intros)
next
  case (Op v op f)
  then show ?case by (auto intro!: prog_rel.intros atom_assertI)
next
  case (Seq c1 c2)
  then show ?case by (auto intro: prog_rel.intros)
next
  case (If x1 x2 c1 c2)
  show ?case
    unfolding sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps
    apply (intro prog_rel.intros)
    apply (split if_splits)
    unfolding sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps liftspec.simps
    apply (intro allI impI conjI prog_rel.intros; simp)
    using refl_frame_leq apply (auto dest: reflD)[1]
    using If apply blast
    using If apply blast
    using cmp_atom apply simp
    using If apply blast
    using refl_frame_leq apply (auto dest: reflD)[1]
    using If apply blast
    using If apply blast
    using ncmp_atom apply simp
    using If by blast
next
  case (While x1 x2 x3 x4 c)
  show ?case
    unfolding sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps liftspec.simps
    apply (intro prog_rel.intros; simp?)
    using refl_frame_leq apply (auto dest: reflD)[1]
    using While apply blast
    using cmp_atom apply simp
    apply (rule While(1))
    apply (intro prog_rel.intros; simp?)
    using While apply blast
    using While apply blast
    using refl_frame_leq apply (auto dest: reflD)[1]
    using While apply blast
    using While apply blast
    using While apply blast
    using ncmp_atom apply simp
    done
qed

theorem secure:
  assumes wf: "wellformed' R G" "id_on (wr\<^sub>l c) (step G) \<subseteq> step\<^sub>t R \<inter> step G"
  assumes g: "guarl (wr\<^sub>l c) (sec_lang c) G"
  assumes P: "P \<subseteq> [wp R (sec_lang c) (UNIV,UNIV)]\<^sub>;" (is "P \<subseteq> [wp R ?c ?Q]\<^sub>;")
  assumes l: "lk\<^sub>l c \<inter> wr\<^sub>l c = {}"

  shows "secure (lift\<^sub>c (ts_lang_of_vm_lang ?c) Nil (wr\<^sub>l c)) (seq_pred_of_vm_pred P) sec_inv 
        {(t,t'). trace_rel t t' (flatten atom_leq)}"
proof -
  have st: "stable\<^sub>t R [?Q]\<^sub>;" "stable\<^sub>L R [?Q]\<^sub>s" by (auto simp: stable\<^sub>L_def stable_def)
  have r: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) (wr\<^sub>l c) \<turnstile> 
          spec_pred_of_lvm_pred [?Q]\<^sub>s (wr\<^sub>l c) {com.Nil} spec_pred_of_lvm_pred [?Q]\<^sub>s (wr\<^sub>l c)"
    using st(2) wf by auto

  have "R,G \<turnstile> wp R ?c ?Q {?c,Nil,wr\<^sub>l c} ?Q" 
    using com_wp[where ?c="sec_lang c" for c, OF r st g _ _ wf] l by auto
  hence "R,G \<turnstile>\<^sub>; [wp R ?c ?Q]\<^sub>; {?c,Nil,wr\<^sub>l c} [?Q]\<^sub>;" by blast
  hence "R,G \<turnstile>\<^sub>; P {?c,Nil,wr\<^sub>l c} [?Q]\<^sub>;" 
    using P by (meson equalityD2 rules.conseq seq_mono)

  thus ?thesis
  proof (rule secure_bisim)
    show "\<forall>\<alpha>\<in>atom_sec. (\<alpha>, {\<alpha>}) \<in> atom_leq" using atom_sec_leq .
  next 
    show "flatten atom_leq \<subseteq> {(\<alpha>, \<beta>). le_basic \<alpha> \<beta> sec_inv}" using atom_leq_sound .
  next
    show "\<forall>(\<alpha>, \<beta>s)\<in>atom_leq.
       \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'.
          (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<longrightarrow>
          m\<^sub>1 \<in> vc \<alpha> \<longrightarrow>
          (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha> \<longrightarrow>
          (\<exists>\<beta> m\<^sub>2'.
              (m\<^sub>1', m\<^sub>2') \<in> sec_inv \<and>
              (m\<^sub>2, m\<^sub>2') \<in> beh \<beta> \<and> \<beta> \<in> \<beta>s)" unfolding atom_leq_def by blast
  next
    have "prog_rel Nil Nil atom_sec {sc, reorder_inst} frame_leq" 
      by (auto intro: prog_rel.intros)
    thus "prog_rel
            (lift\<^sub>c (ts_lang_of_vm_lang (sec_lang c)) com.Nil (wr\<^sub>l c))
            (lift\<^sub>c (ts_lang_of_vm_lang (sec_lang c)) com.Nil (wr\<^sub>l c))
            atom_sec {sc, reorder_inst} frame_leq" 
      by (rule prog_rel_secI)
  next
    show "pop_stable atom_leq frame_leq" using atom_frame_leq .
  next
    show "re_stable atom_sec atom_leq {sc, reorder_inst}" using re_stableI .
  qed
qed
  
end

end