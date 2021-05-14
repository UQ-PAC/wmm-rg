theory PetersonLitmus
  imports "../SimAsm_Syntax" 
begin

datatype globals = X | Y | T
record aux = S :: bool

(*
definition Rtest
  where "Rtest = \<llangle>((\<^sup>1\<lbrakk>X\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk> \<and> (\<^sup>2\<lbrakk>T\<rbrakk> = \<^sup>1\<lbrakk>T\<rbrakk> \<or> (\<^sup>1\<lbrakk>T\<rbrakk> \<and> \<not> \<^sup>2\<lbrakk>T\<rbrakk> \<and> (\<^sup>1\<lbrakk>X\<rbrakk> \<longrightarrow> \<not>\<^sup>2\<^sup>aS))))\<rrangle>"

lemma reg_assign [simp]:
  "((\<lambda>v. (v = n \<longrightarrow> st m' e) \<and> (v \<noteq> n \<longrightarrow> st m' (Reg v))) = (\<lambda>v. st x (Reg v))) = 
   (st x (Reg n) = st m' e \<and> (\<forall>v. v \<noteq> n \<longrightarrow> st x (Reg v) = st m' (Reg v)))"
  apply auto
  apply metis
  apply metis
  apply metis
  apply metis
  done

lemma reg_assign' [simp]:
  "((\<lambda>v. ((v::nat) = 0 \<longrightarrow> st m' e) \<and> (0 < v \<longrightarrow> st m' (Reg v))) = (\<lambda>v. st x (Reg v))) = 
   (st x (Reg 0) = st m' e \<and> (\<forall>v. 0 < v \<longrightarrow> st x (Reg v) = st m' (Reg v)))"
proof -
  have "((\<lambda>v. ((v::nat) = 0 \<longrightarrow> st m' e) \<and> (0 < v \<longrightarrow> st m' (Reg v))) = (\<lambda>v. st x (Reg v))) = 
        ((\<lambda>v. (v = 0 \<longrightarrow> st m' e) \<and> (v \<noteq> 0 \<longrightarrow> st m' (Reg v))) = (\<lambda>v. st x (Reg v)))"
    by auto
  also have "... = (st x (Reg 0) = st m' e \<and> (\<forall>v. v \<noteq> 0 \<longrightarrow> st x (Reg v) = st m' (Reg v)))"
    using reg_assign[of 0 m' e x] by blast
  also have "... = (st x (Reg 0) = st m' e \<and> (\<forall>v. 0 < v \<longrightarrow> st x (Reg v) = st m' (Reg v)))"
    by simp
  finally show ?thesis .
qed

lemma
  "stable\<^sub>t Rtest P \<Longrightarrow>
   sp (sp P (\<^bold>r(0 :: nat) := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<and> \<^sup>0\<lbrakk>Y\<rbrakk>)) Rtest) (\<^bold>r1 := \<lbrakk>T\<rbrakk>) Rtest \<subseteq> 
   sp (sp P (\<^bold>r1 := \<lbrakk>T\<rbrakk>) Rtest) (\<^bold>r0 := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<and> \<^sup>0\<lbrakk>Y\<rbrakk>)) Rtest"
  apply (clarsimp simp: step\<^sub>t_def aux_upd_def glb_def rg_def Rtest_def st_upd_def)
  apply (rename_tac m\<^sub>3 m\<^sub>2 m\<^sub>1)
  apply (intro exI conjI impI)
  apply (subgoal_tac "m\<^sub>2 (Reg 0 :=\<^sub>s st m\<^sub>1 (Reg 0)) \<in> P")
  apply (thin_tac "m\<^sub>1 \<in> P")
  apply blast
  defer 1
  prefer 4
  apply (subgoal_tac "st (m\<^sub>3(Glb Y :=\<^sub>s st m\<^sub>1 (Glb Y), Reg 0 :=\<^sub>s st m\<^sub>1 (Reg 0))) (Reg (Suc 0)) = 
                      st (m\<^sub>2(Reg 0 :=\<^sub>s st m\<^sub>1 (Reg 0))) (Glb T)")
  apply blast
  apply (clarsimp simp: st_upd_def)+

  apply (subgoal_tac "(m\<^sub>1, m\<^sub>2\<lparr>st := (st m\<^sub>2)(Reg 0 := st m\<^sub>1 (Reg 0))\<rparr>) \<in> {(m, m').
         (st m (Glb X) \<longrightarrow> S (state_rec.more m') \<longrightarrow> S (state_rec.more m)) \<and>
         st m (Glb X) = st m' (Glb X) \<and>
         (st m' (Glb T) = st m (Glb T) \<or>
          st m (Glb T) \<and>
          \<not> st m' (Glb T) \<and> (st m (Glb X) \<longrightarrow> \<not> S (state_rec.more m'))) \<and>
         (\<lambda>v. st m (Reg v)) = (\<lambda>v. st m' (Reg v))}") 
  unfolding stable_def apply presburger
  by auto

lemma
  "stable\<^sub>t Rtest P \<Longrightarrow>
   sp (sp P (\<^bold>r1 := \<lbrakk>T\<rbrakk>) Rtest) (\<^bold>r0 := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<and> \<^sup>0\<lbrakk>Y\<rbrakk>)) Rtest \<subseteq>
   sp (sp P (\<^bold>r(0 :: nat) := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<and> \<^sup>0\<lbrakk>Y\<rbrakk>)) Rtest) (\<^bold>r1 := \<lbrakk>T\<rbrakk>) Rtest"
  apply (clarsimp simp: step\<^sub>t_def aux_upd_def glb_def rg_def Rtest_def st_upd_def)
  apply (rename_tac m\<^sub>3 m\<^sub>2 m\<^sub>1)
  apply (intro exI conjI impI)
  apply (subgoal_tac "m\<^sub>2(Reg 1 :=\<^sub>s st m\<^sub>1 (Reg 1), Glb T :=\<^sub>s st m\<^sub>1 (Glb T)) \<in> P")
  apply (thin_tac "m\<^sub>1 \<in> P")
  apply blast
  defer 1
  prefer 5
  apply (subgoal_tac "st (m\<^sub>3(Reg 1 :=\<^sub>s st m\<^sub>1 (Reg 1), Glb T :=\<^sub>s st m\<^sub>1 (Glb T))) (Reg 0) = 
                      st (m\<^sub>2(Reg 1 :=\<^sub>s st m\<^sub>1 (Reg 1), Glb T :=\<^sub>s st m\<^sub>1 (Glb T))) (Glb Y)")
  apply blast
  apply (clarsimp simp: st_upd_def)+
  apply blast
  apply (clarsimp simp: st_upd_def)+

  apply (subgoal_tac "(m\<^sub>1, m\<^sub>2\<lparr>st := (st m\<^sub>2)
             (Reg (Suc 0) := st m\<^sub>1 (Reg (Suc 0)), Glb T := st m\<^sub>1 (Glb T))\<rparr>) \<in> {(m, m').
         (st m (Glb X) \<longrightarrow> S (state_rec.more m') \<longrightarrow> S (state_rec.more m)) \<and>
         st m (Glb X) = st m' (Glb X) \<and>
         (st m' (Glb T) = st m (Glb T) \<or>
          st m (Glb T) \<and>
          \<not> st m' (Glb T) \<and> (st m (Glb X) \<longrightarrow> \<not> S (state_rec.more m'))) \<and>
         (\<lambda>v. st m (Reg v)) = (\<lambda>v. st m' (Reg v))}") 
  unfolding stable_def apply presburger
  apply clarsimp
  by blast
*)

lemma thread0:
  "FNBEGIN
    R: (\<^sup>1\<lbrakk>X\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk> \<and> (\<^sup>2\<lbrakk>T\<rbrakk> = \<^sup>1\<lbrakk>T\<rbrakk> \<or> (\<^sup>1\<lbrakk>T\<rbrakk> \<and> \<not> \<^sup>2\<lbrakk>T\<rbrakk> \<and> (\<^sup>1\<lbrakk>X\<rbrakk> \<longrightarrow> \<not>\<^sup>2\<^sup>aS)))
    G: (\<^sup>1\<lbrakk>Y\<rbrakk> \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk> \<and> (\<^sup>2\<lbrakk>T\<rbrakk> = \<^sup>1\<lbrakk>T\<rbrakk> \<or> (\<not>\<^sup>1\<lbrakk>T\<rbrakk> \<and> \<^sup>2\<lbrakk>T\<rbrakk> \<and> (\<^sup>1\<lbrakk>Y\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS)))
    P: True
    {
      \<lbrakk>X\<rbrakk> := #True;
      fence;
      \<lbrakk>T\<rbrakk> := #True :\<^sub>a \<^sup>aS := True;
      fence;
      \<^bold>r0 := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<and> \<^sup>0\<lbrakk>Y\<rbrakk>);
      \<^bold>r1 := \<lbrakk>T\<rbrakk>
    }
    Q: (\<^sup>0\<lbrakk>X\<rbrakk> \<and> (\<^sup>aS \<longrightarrow> \<^sup>0\<^bold>r(0 :: nat) \<and> \<^sup>0\<^bold>r1))
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q *)
  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  (* Wellformedness of R & G *)
  apply (auto simp: transitive_def reflexive_def)[3]

  (* Guarantees of each atomic action *)
  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  (* WP *)
  apply simp
  apply (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def)
  apply (meson less_numeral_extra(3))

  (* RIF *)
  apply rif_eval
  apply (clarsimp simp: checks_def)
  sorry

lemma thread1:
  "FNBEGIN
    R: (\<^sup>1\<lbrakk>Y\<rbrakk> \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk> \<and> (\<^sup>2\<lbrakk>T\<rbrakk> = \<^sup>1\<lbrakk>T\<rbrakk> \<or> (\<not>\<^sup>1\<lbrakk>T\<rbrakk> \<and> \<^sup>2\<lbrakk>T\<rbrakk> \<and> (\<^sup>1\<lbrakk>Y\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS)))
    G: (\<^sup>1\<lbrakk>X\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk> \<and> (\<^sup>2\<lbrakk>T\<rbrakk> = \<^sup>1\<lbrakk>T\<rbrakk> \<or> (\<^sup>1\<lbrakk>T\<rbrakk> \<and> \<not> \<^sup>2\<lbrakk>T\<rbrakk> \<and> (\<^sup>1\<lbrakk>X\<rbrakk> \<longrightarrow> \<not>\<^sup>2\<^sup>aS)))
    P: True
    {
      \<lbrakk>Y\<rbrakk> := #True;
      fence;
      \<lbrakk>T\<rbrakk> := #False :\<^sub>a \<^sup>aS := False;
      fence;
      \<^bold>r0 := \<lbrakk>X\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<or> \<not>\<^sup>0\<lbrakk>X\<rbrakk>);
      \<^bold>r1 := (!\<lbrakk>T\<rbrakk>)
    }
    Q: (\<^sup>0\<lbrakk>Y\<rbrakk> \<and> (\<not>\<^sup>aS \<longrightarrow> \<^sup>0\<^bold>r(0 :: nat) \<and> \<^sup>0\<^bold>r1))
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q *)
  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  (* Wellformedness of R & G *)
  apply (auto simp: transitive_def reflexive_def)[3]

  (* Guarantees of each atomic action *)
  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  (* WP *)
  apply simp
  apply (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def c_neg_def)
  apply (intro conjI impI)
  prefer 2
  apply (meson less_numeral_extra(3))
  apply auto[1]

  (* RIF *)
  apply rif_eval
  apply (clarsimp simp: checks_def)
  sorry

end