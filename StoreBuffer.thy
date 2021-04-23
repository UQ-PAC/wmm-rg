theory StoreBuffer
  imports SimAsm_Syntax
begin

datatype globals = X | Y
record aux = S :: nat 

lemma sb0:
  "FNBEGIN
    R: (\<^sup>1\<^sup>aS \<in> {1,2} \<longrightarrow> \<^sup>2\<^sup>aS \<in> {1,2}) \<and> (\<^sup>1\<^sup>aS = 2 \<longrightarrow> \<^sup>2\<^sup>aS = 2)
    G: (\<^sup>1\<^sup>aS \<in> {1,2} \<longrightarrow> \<^sup>2\<^sup>aS \<in> {1,2}) \<and> (\<^sup>1\<^sup>aS = 1 \<longrightarrow> \<^sup>2\<^sup>aS = 1)
    P: True
    {
      \<lbrakk>X\<rbrakk> := #1;
      fence;
      \<^bold>r0 := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (if \<^sup>aS = 0 then 1 else \<^sup>aS)
    }
    Q: (\<^sup>aS \<in> {1,2} \<and> (\<^sup>aS = 2 \<longrightarrow> \<^sup>0\<^bold>r0 = 1))
  FNEND" 
  unfolding fn_valid.simps
  apply (intro conjI)

  defer 1

  apply (auto simp: reflexive_def transitive_def)[3]

  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]
  
  apply (clarsimp simp: stabilize_def wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  sorry

  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  sorry

lemma sb1:
  "FNBEGIN
    R: True
    G: True
    P: True
    {
      \<lbrakk>Y\<rbrakk> := #1;
      fence;
      \<^bold>r1 := \<lbrakk>X\<rbrakk>
    }
    Q: (\<^sup>0\<^bold>r0 = 1 \<or> \<^sup>0\<^bold>r1 = 1)
  FNEND" 
  sorry

end