theory Peterson
  imports Examples
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
    R: (\<^sup>1\<lbrakk>flag0\<rbrakk> \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>flag0\<rbrakk> = \<^sup>2\<lbrakk>flag0\<rbrakk> \<and> (\<^sup>2\<lbrakk>turn\<rbrakk> = \<^sup>1\<lbrakk>turn\<rbrakk> \<or> (\<^sup>1\<lbrakk>turn\<rbrakk> \<and> \<not>\<^sup>2\<lbrakk>turn\<rbrakk> \<and> (\<^sup>1\<lbrakk>flag0\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS)))
    G: (\<^sup>1\<lbrakk>flag1\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>flag1\<rbrakk> = \<^sup>2\<lbrakk>flag1\<rbrakk> \<and> (\<^sup>2\<lbrakk>turn\<rbrakk> = \<^sup>1\<lbrakk>turn\<rbrakk> \<or> (\<not>\<^sup>1\<lbrakk>turn\<rbrakk> \<and> \<^sup>2\<lbrakk>turn\<rbrakk> \<and> (\<^sup>1\<lbrakk>flag1\<rbrakk> \<longrightarrow> \<not>\<^sup>2\<^sup>aS)))
    P: True
    {
      \<lbrakk>flag0\<rbrakk> := #True;
      fence;
      \<lbrakk>turn\<rbrakk> := #True :\<^sub>a \<^sup>aS := False;
      fence;
      do
        \<^bold>r(0::nat) := \<lbrakk>flag1\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<or> \<not>\<^sup>0\<lbrakk>flag1\<rbrakk>);
        \<^bold>r1 := \<lbrakk>turn\<rbrakk>
      inv \<lbrace>\<^sup>0\<lbrakk>flag0\<rbrakk> \<and> (\<^sup>aS \<or> \<^sup>0\<lbrakk>turn\<rbrakk>)\<rbrace>
      while (\<^bold>r0 && \<^bold>r1);
      fence;
      \<lbrace>\<^sup>aS\<rbrace> skip;
      fence;
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
  apply (simp add: c_and_def test_def)
  apply (intro conjI impI)
  apply (clarsimp simp: stabilize_def st_upd_def glb_def rg_def aux_upd_def)
  apply (clarsimp simp: stabilize_def st_upd_def glb_def rg_def aux_upd_def)
  apply (clarsimp simp: stabilize_def st_upd_def glb_def rg_def aux_upd_def)
  apply (clarsimp simp: stabilize_def st_upd_def glb_def rg_def aux_upd_def)
  apply (metis less_numeral_extra(3))

  (* RIF *)
  apply rif_eval
  apply (clarsimp simp: expand_points_def checks_def, unfold chk_def)
  apply (intro allI conjI impI)
  apply (auto simp: guar_def st_upd_def step_def glb_def aux_upd_def liftg_def)[1]
  apply (rule wp_split[where ?f="\<lambda>a b. b(Glb turn :=\<^sub>s st a (Glb turn), Reg 1 :=\<^sub>s st a (Reg 1))"]; clarsimp simp: step\<^sub>t_def)
  apply (intro conjI impI state_eq; clarsimp simp add: glb_def; metis rg_def)
  by (intro conjI impI state_eq; clarsimp simp add: glb_def)

lemma peterson1:
  "FNBEGIN
    R: (\<^sup>1\<lbrakk>flag1\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS \<longrightarrow> \<^sup>1\<^sup>aS) \<and> \<^sup>1\<lbrakk>flag1\<rbrakk> = \<^sup>2\<lbrakk>flag1\<rbrakk> \<and> (\<^sup>2\<lbrakk>turn\<rbrakk> = \<^sup>1\<lbrakk>turn\<rbrakk> \<or> (\<not>\<^sup>1\<lbrakk>turn\<rbrakk> \<and> \<^sup>2\<lbrakk>turn\<rbrakk> \<and> (\<^sup>1\<lbrakk>flag1\<rbrakk> \<longrightarrow> \<not>\<^sup>2\<^sup>aS)))
    G: (\<^sup>1\<lbrakk>flag0\<rbrakk> \<longrightarrow> \<^sup>1\<^sup>aS \<longrightarrow> \<^sup>2\<^sup>aS) \<and> \<^sup>1\<lbrakk>flag0\<rbrakk> = \<^sup>2\<lbrakk>flag0\<rbrakk> \<and> (\<^sup>2\<lbrakk>turn\<rbrakk> = \<^sup>1\<lbrakk>turn\<rbrakk> \<or> (\<^sup>1\<lbrakk>turn\<rbrakk> \<and> \<not>\<^sup>2\<lbrakk>turn\<rbrakk> \<and> (\<^sup>1\<lbrakk>flag0\<rbrakk> \<longrightarrow> \<^sup>2\<^sup>aS)))
    P: True
    {
      \<lbrakk>flag1\<rbrakk> := #True;
      fence;
      \<lbrakk>turn\<rbrakk> := #False :\<^sub>a \<^sup>aS := True;
      fence;
      do
        \<^bold>r(0::nat) := \<lbrakk>flag0\<rbrakk> :\<^sub>a \<^sup>aS := (\<^sup>aS \<and> \<^sup>0\<lbrakk>flag0\<rbrakk>);
        \<^bold>r1 := (!\<lbrakk>turn\<rbrakk>)
      inv \<lbrace>\<^sup>0\<lbrakk>flag1\<rbrakk> \<and> (\<not>\<^sup>0\<lbrakk>turn\<rbrakk> \<or> \<not>\<^sup>aS)\<rbrace>
      while (\<^bold>r0 && \<^bold>r1);
      fence;
      \<lbrace>\<not>\<^sup>aS\<rbrace> skip;
      fence;
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
  apply (simp add: c_neg_def c_and_def test_def)
  apply (intro conjI impI)
  apply (clarsimp simp: stabilize_def st_upd_def glb_def rg_def aux_upd_def)+
  apply (metis less_numeral_extra(3))

  (* RIF *)
  apply rif_eval
  apply (clarsimp simp: expand_points_def checks_def, unfold chk_def)
  apply (intro allI conjI impI)
  apply (auto simp: guar_def st_upd_def step_def glb_def aux_upd_def liftg_def)[1]
  apply (rule wp_split[where ?f="\<lambda>a b. b(Glb turn :=\<^sub>s st a (Glb turn), Reg 1 :=\<^sub>s st a (Reg 1))"]; clarsimp simp: c_neg_def step\<^sub>t_def)
  apply (intro conjI impI state_eq; clarsimp simp add: glb_def; metis rg_def)
  by (intro conjI impI state_eq; clarsimp simp add: glb_def)

end