theory StoreBuffer
  imports SimAsm_Syntax
begin

datatype globals = X | Y
record aux = S :: nat 

lemma sb0:
  "FNBEGIN
    R: (\<^sup>1\<^sup>aS \<in> {1,2} \<longrightarrow> \<^sup>2\<^sup>aS \<in> {1,2}) \<and> (\<^sup>1\<^sup>aS = \<^sup>2\<^sup>aS \<or> (\<^sup>1\<^sup>aS = 0 \<and> \<^sup>2\<^sup>aS = 2 \<and> \<^sup>2\<lbrakk>Y\<rbrakk> = 1)) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk> \<and> (\<^sup>1\<lbrakk>Y\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<lbrakk>Y\<rbrakk> = 1)
    G: (\<^sup>1\<^sup>aS \<in> {1,2} \<longrightarrow> \<^sup>2\<^sup>aS \<in> {1,2}) \<and> (\<^sup>1\<^sup>aS = \<^sup>2\<^sup>aS \<or> (\<^sup>1\<^sup>aS = 0 \<and> \<^sup>2\<^sup>aS = 1 \<and> \<^sup>2\<lbrakk>X\<rbrakk> = 1)) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk> \<and> (\<^sup>1\<lbrakk>X\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<lbrakk>X\<rbrakk> = 1)
    P: \<^sup>aS = 0 
    {
      \<lbrakk>X\<rbrakk> := #1;
      fence;
      \<lbrace>\<^sup>0\<lbrakk>X\<rbrakk> = 1\<rbrace> \<^bold>r0 := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (if \<^sup>aS = 0 then 1 else \<^sup>aS)
    }
    Q: (\<^sup>aS \<in> {1,2} \<and> (\<^sup>aS = 2 \<longrightarrow> \<^sup>0\<^bold>r0 = 1))
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q *)
  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  (* Wellformedness of R & G *)
  apply (auto simp: reflexive_def)[1]
  apply (clarsimp simp: transitive_def, intro conjI impI; elim disjE; simp)
  apply (auto simp: reflexive_def)[1]

  (* Guarantees of each atomic action *)
  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  (* WP reasoning *)
  apply simp
  apply (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def)
  by presburger

lemma sb1:
  "FNBEGIN
    R: (\<^sup>1\<^sup>aS \<in> {1,2} \<longrightarrow> \<^sup>2\<^sup>aS \<in> {1,2}) \<and> (\<^sup>1\<^sup>aS = \<^sup>2\<^sup>aS \<or> (\<^sup>1\<^sup>aS = 0 \<and> \<^sup>2\<^sup>aS = 1 \<and> \<^sup>2\<lbrakk>X\<rbrakk> = 1)) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk> \<and> (\<^sup>1\<lbrakk>X\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<lbrakk>X\<rbrakk> = 1)
    G: (\<^sup>1\<^sup>aS \<in> {1,2} \<longrightarrow> \<^sup>2\<^sup>aS \<in> {1,2}) \<and> (\<^sup>1\<^sup>aS = \<^sup>2\<^sup>aS \<or> (\<^sup>1\<^sup>aS = 0 \<and> \<^sup>2\<^sup>aS = 2 \<and> \<^sup>2\<lbrakk>Y\<rbrakk> = 1)) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk> \<and> (\<^sup>1\<lbrakk>Y\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<lbrakk>Y\<rbrakk> = 1)
    P: \<^sup>aS = 0 
    {
      \<lbrakk>Y\<rbrakk> := #1;
      fence;
      \<lbrace>\<^sup>0\<lbrakk>Y\<rbrakk> = 1\<rbrace> \<^bold>r1 := \<lbrakk>X\<rbrakk> :\<^sub>a \<^sup>aS := (if \<^sup>aS = 0 then 2 else \<^sup>aS)
    }
    Q: (\<^sup>aS \<in> {1,2} \<and> (\<^sup>aS = 1 \<longrightarrow> \<^sup>0\<^bold>r1 = 1))
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q *)
  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  (* Wellformedness of R & G *)
  apply (auto simp: reflexive_def)[1]
  apply (clarsimp simp: transitive_def, intro conjI impI; elim disjE; simp)
  apply (auto simp: reflexive_def)[1]

  (* Guarantees of each atomic action *)
  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  (* WP reasoning *)
  apply simp
  apply (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def)
  by presburger

lemma Q_rewrite:
  "\<llangle>\<^sup>aS \<in> {1,2} \<and> (\<^sup>aS = 2 \<longrightarrow> \<^sup>0\<^bold>r0 = 1) \<and> \<^sup>aS \<in> {1,2} \<and> (\<^sup>aS = 1 \<longrightarrow> \<^sup>0\<^bold>r1 = 1)\<rrangle> \<subseteq> \<llangle>\<^sup>0\<^bold>r0 = 1 \<or> \<^sup>0\<^bold>r1 = 1\<rrangle>"
  by auto

end