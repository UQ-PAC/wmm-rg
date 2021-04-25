theory PetersonLitmus
  imports "../SimAsm_Syntax" "../SimAsm_Inter"
begin

datatype globals = X | Y | T
record aux = S :: bool

theorem upd_correct:
  assumes "upd2 R (lift\<^sub>c c) P \<subseteq> {p. point.inv p}"
  shows "rif (step\<^sub>t R) (step G) (lift\<^sub>c c)"
  sorry

instance aux_ext :: (equal) equal
  by standard

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

  apply simp
  apply (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def)
  apply (meson less_numeral_extra(3))

  apply (rule upd_correct[where ?P="{}"])

  apply (simp add: upd\<^sub>a_def gen_def liftg_def liftl_def)

  apply (clarsimp simp: aux_upd_def st_upd_def stabilize_def glb_def rg_def)[1]
  sorry

lemma thread1:
  "FNBEGIN
    R: (\<^sup>1\<lbrakk>Y\<rbrakk> \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk> \<and> (\<^sup>2\<lbrakk>T\<rbrakk> = \<^sup>1\<lbrakk>T\<rbrakk> \<or> (\<not>\<^sup>1\<lbrakk>T\<rbrakk> \<and> \<^sup>2\<lbrakk>T\<rbrakk> \<and> (\<^sup>1\<lbrakk>Y\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS)))
    G: (\<^sup>1\<lbrakk>X\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk> \<and> (\<^sup>2\<lbrakk>T\<rbrakk> = \<^sup>1\<lbrakk>T\<rbrakk> \<or> (\<^sup>1\<lbrakk>T\<rbrakk> \<and> \<not> \<^sup>2\<lbrakk>T\<rbrakk> \<and> (\<^sup>1\<lbrakk>X\<rbrakk> \<longrightarrow> \<not>\<^sup>2\<^sup>aS)))
    P: True
    {
      \<lbrakk>Y\<rbrakk> := #True;
      \<lbrakk>T\<rbrakk> := #False :\<^sub>a \<^sup>aS := False;
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

  apply simp
  apply (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def c_neg_def)
  apply (intro conjI impI)
  defer 1
  apply (meson less_numeral_extra(3))
  by auto

end