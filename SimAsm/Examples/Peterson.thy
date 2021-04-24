theory Peterson
  imports "../SimAsm_Syntax"
begin

datatype globals = flag0 | flag1 | turn
record aux = S :: bool

text \<open>
S indicates the conditions under which Thread 0 would have to wait.
Mutual exclusion is demonstrated by ensuring Thread 0 requires a false S,
whilst Thread 1 requires a true S.
\<close>

lemma peterson0:
  "FNBEGIN
    R: (\<^sup>1\<lbrakk>flag0\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>flag0\<rbrakk> = \<^sup>2\<lbrakk>flag0\<rbrakk> \<and> (\<^sup>2\<lbrakk>turn\<rbrakk> = \<^sup>1\<lbrakk>turn\<rbrakk> \<or> (\<^sup>1\<lbrakk>turn\<rbrakk> \<and> \<not>\<^sup>2\<lbrakk>turn\<rbrakk> \<and> (\<^sup>1\<lbrakk>flag0\<rbrakk> \<longrightarrow> \<not>\<^sup>2\<^sup>aS)))
    G: (\<^sup>1\<lbrakk>flag1\<rbrakk> \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>flag1\<rbrakk> = \<^sup>2\<lbrakk>flag1\<rbrakk> \<and> (\<^sup>2\<lbrakk>turn\<rbrakk> = \<^sup>1\<lbrakk>turn\<rbrakk> \<or> (\<not>\<^sup>1\<lbrakk>turn\<rbrakk> \<and> \<^sup>2\<lbrakk>turn\<rbrakk> \<and> (\<^sup>1\<lbrakk>flag1\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS)))
    P: True
    {
      \<lbrakk>flag0\<rbrakk> := #True;
      \<lbrakk>turn\<rbrakk> := #True :\<^sub>a \<^sup>aS := True;
      do
        \<^bold>r0 := \<lbrakk>flag1\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<and> \<^sup>0\<lbrakk>flag1\<rbrakk>);
        \<^bold>r1 := \<lbrakk>turn\<rbrakk>
      inv \<lbrace>\<^sup>0\<lbrakk>flag0\<rbrakk> \<and> (\<^sup>aS \<longrightarrow> \<^sup>0\<lbrakk>turn\<rbrakk>)\<rbrace>
      while (\<^bold>r0 && \<^bold>r1);
      \<lbrace>\<not>\<^sup>aS\<rbrace> skip;
      \<lbrakk>flag0\<rbrakk> := #False
    }
    Q: True
  FNEND" 
  apply (unfold fn_valid.simps, intro conjI)
  
  (* Stability of Q + Wellformedness of R & G *)
  apply (auto simp: step\<^sub>t_def stable_def reflexive_def transitive_def)[4]

  (* Guarantees of each atomic action *)
  apply (clarsimp simp: aux_upd_def step_def glb_def wp\<^sub>r_def st_upd_def)

  (* WP reasoning *)
  by (simp add: c_and_def test_def, intro conjI impI; 
      clarsimp simp: stabilize_def st_upd_def glb_def rg_def aux_upd_def; metis)

lemma peterson1:
  "FNBEGIN
    R: (\<^sup>1\<lbrakk>flag1\<rbrakk> \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>flag1\<rbrakk> = \<^sup>2\<lbrakk>flag1\<rbrakk> \<and> (\<^sup>2\<lbrakk>turn\<rbrakk> = \<^sup>1\<lbrakk>turn\<rbrakk> \<or> (\<not>\<^sup>1\<lbrakk>turn\<rbrakk> \<and> \<^sup>2\<lbrakk>turn\<rbrakk> \<and> (\<^sup>1\<lbrakk>flag1\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS)))
    G: (\<^sup>1\<lbrakk>flag0\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>flag0\<rbrakk> = \<^sup>2\<lbrakk>flag0\<rbrakk> \<and> (\<^sup>2\<lbrakk>turn\<rbrakk> = \<^sup>1\<lbrakk>turn\<rbrakk> \<or> (\<^sup>1\<lbrakk>turn\<rbrakk> \<and> \<not>\<^sup>2\<lbrakk>turn\<rbrakk> \<and> (\<^sup>1\<lbrakk>flag0\<rbrakk> \<longrightarrow> \<not>\<^sup>2\<^sup>aS)))
    P: True
    {
      \<lbrakk>flag1\<rbrakk> := #True;
      \<lbrakk>turn\<rbrakk> := #False :\<^sub>a \<^sup>aS := False;
      do
        \<^bold>r0 := \<lbrakk>flag0\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<or> \<not>\<^sup>0\<lbrakk>flag0\<rbrakk>);
        \<^bold>r1 := (!\<lbrakk>turn\<rbrakk>)
      inv \<lbrace>\<^sup>0\<lbrakk>flag1\<rbrakk> \<and> (\<^sup>0\<lbrakk>turn\<rbrakk> \<longrightarrow> \<^sup>aS)\<rbrace>
      while (\<^bold>r0 && \<^bold>r1);
      \<lbrace>\<^sup>aS\<rbrace> skip;
      \<lbrakk>flag1\<rbrakk> := #False
    }
    Q: True
  FNEND" 
  apply(unfold fn_valid.simps, intro conjI)

  (* Stability of Q + Wellformedness of R & G *)
  apply (auto simp: step\<^sub>t_def stable_def reflexive_def transitive_def)[4]

  (* Guarantees of each atomic action *)
  apply (clarsimp simp: aux_upd_def step_def glb_def wp\<^sub>r_def st_upd_def)

  (* WP reasoning *)
  by (simp add: c_and_def c_neg_def test_def, intro conjI impI; 
      clarsimp simp: stabilize_def st_upd_def glb_def rg_def aux_upd_def; metis)

end