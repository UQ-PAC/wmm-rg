theory Peterson
  imports SimAsm_Syntax
begin

datatype globals = flag0 | flag1 | turn
record aux = 
  a0 :: bool 
  a1 :: bool

lemma peterson0:
  "FNBEGIN
    R: \<^sup>1\<lbrakk>flag0\<rbrakk> = \<^sup>2\<lbrakk>flag0\<rbrakk> \<and> (\<^sup>1\<lbrakk>turn\<rbrakk> \<longrightarrow> \<^sup>2\<lbrakk>turn\<rbrakk>)
    G: \<^sup>1\<lbrakk>flag1\<rbrakk> = \<^sup>2\<lbrakk>flag1\<rbrakk> \<and> (\<^sup>1\<lbrakk>turn\<rbrakk> \<longrightarrow> \<^sup>2\<lbrakk>turn\<rbrakk>)
    P: True
    {
      \<lbrakk>flag0\<rbrakk> := #True;
      fence;
      \<lbrakk>turn\<rbrakk> := #True;
      fence;
      do
        \<^bold>r0 := \<lbrakk>flag1\<rbrakk>, \<^sup>aa0 := \<^sup>0\<lbrakk>flag1\<rbrakk>;
        \<^bold>r1 := \<lbrakk>turn\<rbrakk>
      while (\<^bold>r0 && \<^bold>r1);
      Skip;
      \<lbrakk>flag0\<rbrakk> := #False
    }
    Q: True
  FNEND" 
  apply(unfold fn_valid.simps, intro conjI)

  apply (auto simp: step\<^sub>t_def stable_def reflexive_def transitive_def)[4]

  apply (clarsimp simp: aux_upd_def step_def glb_def wp\<^sub>r_def)

  sorry


lemma peterson1:
  "FNBEGIN
    R: True
    G: \<^sup>1\<lbrakk>flag0\<rbrakk> = \<^sup>2\<lbrakk>flag0\<rbrakk> \<and> (\<^sup>1\<lbrakk>turn\<rbrakk> = 0 \<longrightarrow> \<^sup>2\<lbrakk>turn\<rbrakk> = 0)
    P: True
    {
      \<lbrakk>flag1\<rbrakk> := true;
      \<lbrakk>turn\<rbrakk> := #0;
      while (\<lbrakk>flag0\<rbrakk> == true) && (\<lbrakk>turn\<rbrakk> == #0)
      do
        Skip
      od;
      \<^bold>r0 := \<^bold>r2;
      \<lbrakk>flag1\<rbrakk> := false
    }
    Q: True
  FNEND" 
  apply(unfold fn_valid.simps, intro conjI)

  apply (auto simp: step\<^sub>t_def stable_def reflexive_def transitive_def)[4]

  apply (clarsimp simp: step_def glb_def wp\<^sub>r_def)

  apply (simp add: stabilize_def assert_def)

  done


end