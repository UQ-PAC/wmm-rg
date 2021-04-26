theory StoreBuffer
  imports "../SimAsm_Syntax"
begin

datatype globals = X | Y
record aux = S :: bool

text \<open>Auxiliary variable S encodes when the first thread will write 1 to r0\<close>

text \<open>Verification of the first thread\<close>
lemma sb0:
  "FNBEGIN
    R: (\<^sup>1\<lbrakk>X\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk>
    G: (\<^sup>2\<lbrakk>Y\<rbrakk> = 1 \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk>
    P: True
    {
      \<lbrakk>X\<rbrakk> := #1;
      fence;
      \<^bold>r0 := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>0\<lbrakk>Y\<rbrakk> = 1)
    }
    Q: (\<^sup>0\<lbrakk>X\<rbrakk> = 1 \<and> (\<^sup>aS \<longrightarrow> \<^sup>0\<^bold>r0 = 1))
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q *)
  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  (* Wellformedness of R & G *)
  apply (auto simp: transitive_def reflexive_def)[3]

  (* Guarantees of each atomic action *)
  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  (* WP reasoning *)
  by simp (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def)

text \<open>Verification of the second thread\<close>
lemma sb1:
  "FNBEGIN
    R: (\<^sup>2\<lbrakk>Y\<rbrakk> = 1 \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk>
    G: (\<^sup>1\<lbrakk>X\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk>
    P: True
    {
      \<lbrakk>Y\<rbrakk> := #1;
      fence;
      \<^bold>r1 := \<lbrakk>X\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>0\<lbrakk>X\<rbrakk> \<noteq> 1)
    }
    Q: (\<^sup>0\<lbrakk>Y\<rbrakk> = 1 \<and> (\<not>\<^sup>aS \<longrightarrow> \<^sup>0\<^bold>r1 = 1))
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q *)
  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  (* Wellformedness of R & G *)
  apply (auto simp: transitive_def reflexive_def)[3]

  (* Guarantees of each atomic action *)
  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  (* WP reasoning *)
  by simp (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def)

text \<open>Show the conjunction of their post-conditions achieves the desired outcome\<close>
lemma Q_rewrite:
  "\<llangle>(\<^sup>0\<lbrakk>X\<rbrakk> = 1 \<and> (\<^sup>aS \<longrightarrow> \<^sup>0\<^bold>r0 = 1)) \<and> (\<^sup>0\<lbrakk>Y\<rbrakk> = 1 \<and> (\<not>\<^sup>aS \<longrightarrow> \<^sup>0\<^bold>r1 = 1))\<rrangle> \<subseteq> \<llangle>\<^sup>0\<^bold>r0 = 1 \<or> \<^sup>0\<^bold>r1 = 1\<rrangle>"
  by auto

end
