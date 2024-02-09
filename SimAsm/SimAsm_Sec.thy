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
  "sec_lang (If b t f) = If (sec_bexp b) (sec_lang t) (sec_lang f)" |
  "sec_lang (While b Imix Ispec c) = While (sec_bexp b) (sec_vc Imix) (sec_vc Ispec) (sec_lang c) "

locale simasm_sec_rules = 
  simasm_rules locals rg glb +
  security 
    where exists_act = "undefined :: ('r,'v \<times> 's,'a) auxopSt"
    and push = "tstack_push :: ('r,'v \<times> 's,'a) tstack \<Rightarrow> ('r,'v \<times> 's,'a option) frame_scheme \<Rightarrow> ('r,'v \<times> 's,'a) tstack"
  for locals :: "'r set"
  and rg :: "('r, 'v \<times> ('s :: bounded_lattice), 'a) varmap_rec_scheme \<Rightarrow> 'local \<Rightarrow> 'v \<times> 's"
  and glb :: "('r, 'v \<times> 's, 'a) varmap_rec_scheme \<Rightarrow> 'global \<Rightarrow> 'v \<times> 's"

lemma basic_simps [simp]:
  "basic Nil \<alpha> = False"
  "basic (Basic \<beta>) \<alpha> = (\<beta> = \<alpha>)"
  "basic (com.Seq c\<^sub>1 r c\<^sub>2) \<alpha> = (basic c\<^sub>1 \<alpha> \<or> basic c\<^sub>2 \<alpha>)"
  "basic (\<Sqinter>s. f s) \<alpha> = (\<exists>s. basic (f s) \<alpha>)"
  "basic (c*\<^sub>w) \<alpha> = basic c \<alpha>"
  "basic (Capture k c) \<alpha> = basic c \<alpha>"
  "basic (Interrupt c) \<alpha> = basic c \<alpha>"
  "basic (Thread c) \<alpha> = basic c \<alpha>"
  "basic (c\<^sub>1 || c\<^sub>2) \<alpha> = (basic c\<^sub>1 \<alpha> \<or> basic c\<^sub>2 \<alpha>)"
  apply (auto simp: basics_def elim: basic.cases  intro: basic.intros)
    done

context simasm_sec_rules
begin

lemma basic_rw:
  assumes "c \<leadsto> c'"
  assumes "basic c' \<alpha>"
  shows "basic c \<alpha>"
  using assms by induct auto

lemma basic_lexec:
  assumes "lexecute c \<beta> r c'"
  assumes "basic c' \<alpha>"
  shows "basic c \<alpha>"
  using assms by induct auto

text \<open>The invariant security policy, demanding equivalent values given a bot classification\<close>
definition sec_inv :: "('r,'v \<times> 's,'a) tstack rel"
  where "sec_inv = {(s,s'). 
    (\<forall>v. snd (tlookup s v) = bot \<or> snd (tlookup s' v) = bot \<longrightarrow> fst (tlookup s v) = fst (tlookup s' v)) \<and> 
    tstack_len s = tstack_len s'}"

definition atom_sec
  where "atom_sec \<alpha> \<equiv> \<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'. m\<^sub>1 \<in> vc \<alpha> \<and> (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha>  \<longrightarrow>
         (\<exists>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh \<alpha>) \<and> (\<forall>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh \<alpha> \<longrightarrow> (m\<^sub>1', m\<^sub>2') \<in> sec_inv)"

lemma atom_sec:
  assumes "atom_sec \<alpha>"
  shows "\<forall>m\<^sub>1 m\<^sub>2 m\<^sub>1'. m\<^sub>1 \<in> vc \<alpha> \<and> (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha>  \<longrightarrow>
         (\<exists>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh \<alpha>) \<and> (\<forall>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh \<alpha> \<longrightarrow> (m\<^sub>1', m\<^sub>2') \<in> sec_inv)"
  using assms unfolding atom_sec_def by blast

lemma atom_sec_re:
  "\<alpha>'' < c <\<^sub>w \<alpha>' \<Longrightarrow> atom_sec \<alpha>' \<Longrightarrow> atom_sec \<alpha>''"
  sorry (* Need to place limits on w based on lang and then show reordering won't break sec *)

lemma atom_sec_pop:
  "atom_sec \<alpha>' \<Longrightarrow> atom_sec (tag \<alpha>', poppred' s (vc \<alpha>'), poprel' s s' (beh \<alpha>'))"
  sorry (* Need to show stack manipulations won't break sec *)

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

lemma atom_sec_detfI:
  assumes "\<forall>m m\<^sub>1. (m,m\<^sub>1) \<in> beh \<alpha> = (m\<^sub>1 = f m)"
  assumes "\<forall>m\<^sub>1 m\<^sub>2. m\<^sub>1 \<in> vc \<alpha> \<and> (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<longrightarrow> (f m\<^sub>1, f m\<^sub>2) \<in> sec_inv"
  shows "atom_sec \<alpha>"
  using assms unfolding atom_sec_def 
  by presburger

lemma atom_sec_idI:
  assumes "\<forall>m m\<^sub>1. (m,m\<^sub>1) \<in> beh \<alpha> \<longrightarrow> tlookup m\<^sub>1 = tlookup m \<and> tstack_len m\<^sub>1 = tstack_len m"
  assumes "\<forall>m\<^sub>1 m\<^sub>1' m\<^sub>2. m\<^sub>1 \<in> vc \<alpha> \<and> (m\<^sub>1, m\<^sub>2) \<in> sec_inv \<and> (m\<^sub>1, m\<^sub>1') \<in> beh \<alpha> \<longrightarrow> (\<exists>m\<^sub>2'. (m\<^sub>2, m\<^sub>2') \<in> beh \<alpha>)"
  shows "atom_sec \<alpha>"
  using assms unfolding atom_sec_def apply auto 
  unfolding sec_inv_def apply auto
  done

lemma sec_inv_tauxupdI:
  assumes "(a,b) \<in> sec_inv"
  shows "(tauxupd a f, tauxupd b f) \<in> sec_inv"
  using assms unfolding sec_inv_def by force

lemma sec_inv_tupdateI:
  assumes "(a,b) \<in> sec_inv"
  assumes "(snd e = bot \<or> snd e' = bot) \<longrightarrow> fst e = fst e'"
  shows "(tupdate a x e, tupdate b x e') \<in> sec_inv"
  using assms unfolding sec_inv_def by auto

lemma [simp]:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> sec_inv"
  shows "tstack_len m\<^sub>2 = tstack_len m\<^sub>1"
  using assms unfolding sec_inv_def by (auto)

lemma sec_inv_sym:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> sec_inv"
  shows "(m\<^sub>2, m\<^sub>1) \<in> sec_inv"
  using assms unfolding sec_inv_def by (auto)

lemma sec_inv_exp1:
  assumes "(m\<^sub>1, m\<^sub>2) \<in> sec_inv"
  assumes "snd (ev\<^sub>E (tlookup m\<^sub>1) (sec_exp e)) = bot"
  shows "fst (ev\<^sub>E (tlookup m\<^sub>1) (sec_exp e)) = fst (ev\<^sub>E (tlookup m\<^sub>2) (sec_exp e))"
  apply (rule eq_ev\<^sub>E_sec_exp)
  using assms unfolding sec_inv_def by (auto elim!: bot_expE)

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
  using assms unfolding sec_inv_def by (auto elim!: bot_expE)


lemma atom_sec_lang:
  assumes "\<forall>\<alpha>. basic r \<alpha> \<longrightarrow> atom_sec \<alpha>"
  assumes "basic (lift\<^sub>c (ts_lang_of_vm_lang (sec_lang c)) r w) \<alpha>"
  shows "atom_sec \<alpha>"
  using assms
proof (induct c arbitrary: w r \<alpha>)
  case Skip
  then show ?case by (auto)
next
  case (Op pred op auxfn)
  show ?case 
  proof (cases op)
    case (assign x e)
    show ?thesis
      unfolding sym[OF Op(2)[simplified sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps]] 
      apply (intro atom_sec_detfI allI impI)
       apply (auto simp: liftg_def assign)[1]
      by (blast intro: sec_inv_tauxupdI sec_inv_tupdateI sec_inv_exp2 sec_inv_exp1)+
  next
    case (cmp x2)
    show ?thesis
      unfolding sym[OF Op(2)[simplified sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps]] 
      apply (rule atom_sec_idI; clarsimp simp: liftg_def cmp relcomp_unfold)
      by (auto simp: sec_inv_bexp1)
  next
    case (leak x31 x32)
    show ?thesis 
      unfolding sym[OF Op(2)[simplified sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps]] 
      apply (intro atom_sec_detfI allI impI)
       apply (auto simp: liftg_def leak)[1]
      by (blast intro: sec_inv_tauxupdI sec_inv_tupdateI sec_inv_exp2 sec_inv_exp1)+
  next
    case full_fence
    show ?thesis 
      unfolding sym[OF Op(2)[simplified sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps]] 
      by (rule atom_sec_idI) (clarsimp simp: liftg_def full_fence)+
  next
    case nop
    show ?thesis 
      unfolding sym[OF Op(2)[simplified sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps]] 
      by (rule atom_sec_idI) (clarsimp simp: liftg_def nop)+
  qed
next
  case (Seq c1 c2)    
  show ?case using Seq(4)
    unfolding sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps
    apply (elim disjE)
     prefer 2
    using Seq(2,3) apply blast
    apply (rule Seq(1))
    prefer 2
    apply blast
    apply (intro allI impI)
    apply (rule Seq(2))
    apply (rule Seq(3))
    by blast
next
  case (If x1 c1 c2)
  show ?case using If(4)
    unfolding sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps
    apply (elim exE)
    apply (split if_splits)
    unfolding sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps liftspec.simps
    apply (elim disjE)
    apply (rule If(2))
    apply (rule If(3))
        apply blast
    using If(3) apply blast
    defer 1
    apply (rule If(1))
    apply (rule If(3))
        apply blast
apply (elim disjE)
    apply (rule If(1))
    apply (rule If(3))
apply blast
    using If(3) apply blast
    defer 1
    apply (rule If(2))
    apply (rule If(3))
    apply blast
    sorry (* Need to attach a VC to the guard in an If *)
next
  case (While x1 x2 x3 c)
  show ?case using While(3)
    unfolding sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps liftspec.simps
    apply (elim disjE)
    using While(2) apply blast
    defer 1
         apply (rule While(1))
    prefer 2
          apply blast
         apply (intro allI impI)
    unfolding sec_lang.simps ts_lang_of_vm_lang.simps lift\<^sub>c.simps basic_simps liftspec.simps
    apply (elim disjE)
         apply (rule While(1))
         apply (rule While(2))
          apply blast
    using While(2) apply blast
apply (rule While(1))
         apply (rule While(2))
          apply blast
apply (rule While(1))
         apply (rule While(2))
          apply blast
    using While(2) apply blast
    sorry (* Need to attach a VC to the guard in a While *)
qed

text \<open>
Given we have @{term atom_sec} for all statically know atomic operations,
we should also know @{term atom_sec} for all observable atomic operations\<close>
lemma atom_sec_lexec:
  assumes "lexecute c \<alpha> r c'" 
  assumes "\<forall>\<alpha>. basic c \<alpha> \<longrightarrow> atom_sec \<alpha>"
  shows "atom_sec \<alpha>"
  using assms
proof (induct)
  case (ooo c\<^sub>1 \<alpha>' r c\<^sub>1' \<alpha>'' c\<^sub>2 w)
  then show ?case using atom_sec_re by simp
next
  case (cap c \<alpha>' r c' s s')
  then show ?case using atom_sec_pop by simp
qed simp+

text \<open>Extend atom_sec_lexec to a trace of observable atomic operations\<close>
lemma atom_sec_trace:
  assumes "obs_trace t c" "\<alpha> \<in> set t" "\<forall>\<alpha>. basic c \<alpha> \<longrightarrow> atom_sec \<alpha>"
  shows "atom_sec \<alpha>"
  using assms
proof (induct )
  case (2 c c' t)
  then show ?case using basic_rw by fast
next
  case (3 c \<beta> r c' t)
  then show ?case using basic_lexec atom_sec_lexec by (cases "\<alpha> =\<beta>") auto
qed simp+

text \<open>Show introduced verification conditions will preserve the security policy\<close>
lemma sec_pres:
  "sec_pres (lift\<^sub>c (ts_lang_of_vm_lang (sec_lang c)) Nil w) sec_inv" (is "sec_pres ?c sec_inv")
proof -
  have "\<forall>\<alpha>. basic ?c \<alpha> \<longrightarrow> atom_sec \<alpha>" using atom_sec_lang by force
  hence "\<forall>\<alpha> \<in> obs ?c. atom_sec \<alpha>" using atom_sec_trace unfolding obs_def by blast
  thus ?thesis unfolding sec_pres_def using atom_sec by blast
qed

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

text \<open>Final security proof, given wellformed RG specification and @{term wp} result\<close>
lemma secure:
  assumes wf: "wellformed' R G" "id_on (wr\<^sub>l c) (step G) \<subseteq> step\<^sub>t R \<inter> step G"
  assumes g: "guarl (wr\<^sub>l c) (sec_lang c) G"
  assumes P: "P \<subseteq> [wp R (sec_lang c) (UNIV,UNIV)]\<^sub>;" (is "P \<subseteq> [wp R ?c ?Q]\<^sub>;")
  assumes l: "lk\<^sub>l c \<inter> wr\<^sub>l c = {}"
  shows "secure (lift\<^sub>c (ts_lang_of_vm_lang ?c) Nil (wr\<^sub>l c)) (seq_pred_of_vm_pred P) sec_inv"
proof -
  have st: "stable\<^sub>t R [?Q]\<^sub>;" "stable\<^sub>L R [?Q]\<^sub>s" by (auto simp: stable\<^sub>L_def stable_def)
  have r: "base_rel_rely (step\<^sub>t R),base_rel_guar (step G) (wr\<^sub>l c) \<turnstile> 
          spec_pred_of_lvm_pred [?Q]\<^sub>s (wr\<^sub>l c) {com.Nil} spec_pred_of_lvm_pred [?Q]\<^sub>s (wr\<^sub>l c)"
    using st(2) wf by auto

  have "R,G \<turnstile> wp R ?c ?Q {?c,Nil,wr\<^sub>l c} ?Q" 
    using com_wp[where ?c="sec_lang c" for c, OF r st g _ _ wf] l by auto
  hence "R,G \<turnstile>\<^sub>; [wp R ?c ?Q]\<^sub>; {?c,Nil,wr\<^sub>l c} [?Q]\<^sub>;" 
    by blast
  hence j: "R,G \<turnstile>\<^sub>; P {?c,Nil,wr\<^sub>l c} [?Q]\<^sub>;" 
    using P by (meson equalityD2 rules.conseq seq_mono)
  have s: "sec_pres (lift\<^sub>c (ts_lang_of_vm_lang ?c) Nil (wr\<^sub>l c)) sec_inv"
    using sec_pres by blast

  show ?thesis using secure_bisim j s by blast
qed
  
end

end