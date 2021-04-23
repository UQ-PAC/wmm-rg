theory StoreBuffer
  imports SimAsm_Syntax
begin

datatype globals = X | Y
datatype stages = INIT | LEFT | RIGHT
record aux = S :: stages

lemma sb0:
  "FNBEGIN
    R: (\<^sup>1\<^sup>aS \<noteq> INIT \<longrightarrow> \<^sup>2\<^sup>aS \<noteq> INIT) \<and> (\<^sup>1\<^sup>aS = \<^sup>2\<^sup>aS \<or> (\<^sup>1\<^sup>aS = INIT \<and> \<^sup>2\<lbrakk>Y\<rbrakk> = 1)) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk> \<and> (\<^sup>1\<lbrakk>Y\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<lbrakk>Y\<rbrakk> = 1)
    G: (\<^sup>1\<^sup>aS \<noteq> INIT \<longrightarrow> \<^sup>2\<^sup>aS \<noteq> INIT) \<and> (\<^sup>1\<^sup>aS = \<^sup>2\<^sup>aS \<or> (\<^sup>1\<^sup>aS = INIT \<and> \<^sup>2\<lbrakk>X\<rbrakk> = 1)) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk> \<and> (\<^sup>1\<lbrakk>X\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<lbrakk>X\<rbrakk> = 1)
    P: \<^sup>aS = INIT
    {
      \<lbrakk>X\<rbrakk> := #1;
      fence;
      \<lbrace>\<^sup>0\<lbrakk>X\<rbrakk> = 1\<rbrace> \<^bold>r0 := \<lbrakk>Y\<rbrakk> :\<^sub>a \<^sup>aS := (if \<^sup>aS = INIT then LEFT else \<^sup>aS)
    }
    Q: (\<^sup>aS \<noteq> INIT \<and> (\<^sup>aS = RIGHT \<longrightarrow> \<^sup>0\<^bold>r0 = 1))
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q *)
  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  (* Wellformedness of R & G *)
  apply (auto simp: reflexive_def)[1]
  apply (clarsimp simp: transitive_def, elim disjE; simp)
  apply (auto simp: reflexive_def)[1]

  (* Guarantees of each atomic action *)
  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  (* WP reasoning *)
  apply simp
  by (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def)

lemma sb1:
  "FNBEGIN
    R: (\<^sup>1\<^sup>aS \<noteq> INIT \<longrightarrow> \<^sup>2\<^sup>aS \<noteq> INIT) \<and> (\<^sup>1\<^sup>aS = \<^sup>2\<^sup>aS \<or> (\<^sup>1\<^sup>aS = INIT \<and> \<^sup>2\<lbrakk>X\<rbrakk> = 1)) \<and> \<^sup>1\<lbrakk>Y\<rbrakk> = \<^sup>2\<lbrakk>Y\<rbrakk> \<and> (\<^sup>1\<lbrakk>X\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<lbrakk>X\<rbrakk> = 1)
    G: (\<^sup>1\<^sup>aS \<noteq> INIT \<longrightarrow> \<^sup>2\<^sup>aS \<noteq> INIT) \<and> (\<^sup>1\<^sup>aS = \<^sup>2\<^sup>aS \<or> (\<^sup>1\<^sup>aS = INIT \<and> \<^sup>2\<lbrakk>Y\<rbrakk> = 1)) \<and> \<^sup>1\<lbrakk>X\<rbrakk> = \<^sup>2\<lbrakk>X\<rbrakk> \<and> (\<^sup>1\<lbrakk>Y\<rbrakk> = 1 \<longrightarrow> \<^sup>2\<lbrakk>Y\<rbrakk> = 1)
    P: \<^sup>aS = INIT 
    {
      \<lbrakk>Y\<rbrakk> := #1;
      fence;
      \<lbrace>\<^sup>0\<lbrakk>Y\<rbrakk> = 1\<rbrace> \<^bold>r1 := \<lbrakk>X\<rbrakk> :\<^sub>a \<^sup>aS := (if \<^sup>aS = INIT then RIGHT else \<^sup>aS)
    }
    Q: (\<^sup>aS \<noteq> INIT \<and> (\<^sup>aS = LEFT \<longrightarrow> \<^sup>0\<^bold>r1 = 1))
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)

  (* Stability of Q *)
  apply (auto simp: glb_def step\<^sub>t_def stable_def)[1]

  (* Wellformedness of R & G *)
  apply (auto simp: reflexive_def)[1]
  apply (clarsimp simp: transitive_def, elim disjE; simp)
  apply (auto simp: reflexive_def)[1]

  (* Guarantees of each atomic action *)
  apply (auto simp: wp\<^sub>r_def st_upd_def step_def glb_def aux_upd_def)[1]

  (* WP reasoning *)
  apply simp
  by (clarsimp simp: stabilize_def st_upd_def glb_def aux_upd_def rg_def)

lemma Q_rewrite:
  "\<llangle>\<^sup>aS \<noteq> INIT \<and> (\<^sup>aS = RIGHT \<longrightarrow> \<^sup>0\<^bold>r0 = 1) \<and> \<^sup>aS \<noteq> INIT \<and> (\<^sup>aS = LEFT \<longrightarrow> \<^sup>0\<^bold>r1 = 1)\<rrangle> \<subseteq> \<llangle>\<^sup>0\<^bold>r0 = 1 \<or> \<^sup>0\<^bold>r1 = 1\<rrangle>"
  by (auto; case_tac "S (state_rec.more x)"; simp)

end