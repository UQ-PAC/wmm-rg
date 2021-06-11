theory Examples
  imports "../SimAsm_Syntax"
begin

lemma [simp]:
  "beh (\<lfloor>v,\<alpha>,f\<rfloor>) = beh\<^sub>a (\<alpha>,f)"
  by (auto simp: liftg_def)

lemma [simp]:
  "tag (\<lfloor>v\<^sub>1,\<alpha>,f\<rfloor>) = (\<alpha>,f)"
  by (auto simp: liftg_def)

lemma [simp]:
  "{(m, m'). m' = f m} O {(m, m'). m' = b m} = 
   {(m, m'). m' = b (f m)}"
  by auto

lemma [simp]:
  "st (m(aux: f)) = st m"
  by (auto simp: aux_upd_def)

lemma state_eq [intro]:
  "rg m = rg m' \<Longrightarrow> \<forall>x. st m (Glb x) = st m' (Glb x) \<Longrightarrow> state_rec.more m = state_rec.more m' \<Longrightarrow> m = m'"
  apply (rule state_rec.equality)
  apply (auto simp: rg_def)
proof -
assume a1: "(\<lambda>v. st m (Reg v)) = (\<lambda>v. st m' (Reg v))"
  assume a2: "\<forall>x. st m (Glb x) = st m' (Glb x)"
  assume "state_rec.more m = state_rec.more m'"
  have "\<forall>v. st m v = st m' v"
using a2 a1 by (metis (no_types) var.exhaust)
  then show "st m = st m'"
    by blast
qed

lemma wp_split:
  assumes wf: "transitive R" "reflexive R" 
  assumes re: "reorder_inst \<alpha>' (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) (\<lfloor>UNIV,\<alpha>,f\<^sub>2\<rfloor>)"
  assumes \<alpha>: "\<forall>m\<^sub>1 m\<^sub>2 m\<^sub>3. (m\<^sub>1,m\<^sub>2) \<in> beh \<alpha>' \<longrightarrow> (m\<^sub>2,m\<^sub>3) \<in> step\<^sub>t R \<longrightarrow> ((m\<^sub>1,f m\<^sub>1 m\<^sub>3) \<in> step\<^sub>t R \<and> (f m\<^sub>1 m\<^sub>3,f m\<^sub>2 m\<^sub>3) \<in> beh \<alpha>')"
  assumes \<beta>: "\<forall>m\<^sub>1 m\<^sub>2 m\<^sub>3. (m\<^sub>1,m\<^sub>2) \<in> step\<^sub>t R \<longrightarrow> (m\<^sub>2,m\<^sub>3) \<in> beh (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) \<longrightarrow> ((f m\<^sub>1 m\<^sub>2, f m\<^sub>1 m\<^sub>3) \<in> beh (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) \<and> (f m\<^sub>1 m\<^sub>3,m\<^sub>3) \<in> step\<^sub>t R)"
  assumes e: "\<forall>m\<^sub>1 m\<^sub>2 m\<^sub>3. (m\<^sub>1,m\<^sub>2) \<in> beh \<alpha>' \<longrightarrow> (m\<^sub>2,m\<^sub>3) \<in> beh (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) \<longrightarrow> ((m\<^sub>1,f m\<^sub>1 m\<^sub>3) \<in> beh (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) \<and> (f m\<^sub>1 m\<^sub>3,m\<^sub>3) \<in> beh (\<lfloor>UNIV,\<alpha>,f\<^sub>2\<rfloor>))"
  shows "stabilize R (wp\<^sub>\<alpha> (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) (stabilize R (wp\<^sub>\<alpha> (\<lfloor>UNIV,\<alpha>,f\<^sub>2\<rfloor>) (stabilize R Q)))) \<subseteq> 
         stabilize R (wp\<^sub>\<alpha> \<alpha>' (stabilize R (wp\<^sub>\<alpha> (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) (stabilize R Q))))"
  unfolding stabilize_def wp_def
proof (clarsimp, intro conjI impI allI, goal_cases)
  case (1 m\<^sub>1 m\<^sub>2)
  have "vc \<alpha>' = UNIV" using assms by (auto simp: liftg_def)
  then show ?case by auto
next
  case (2 m\<^sub>1 m\<^sub>2 m\<^sub>3 m\<^sub>4)
  then show ?case by (auto simp: liftg_def)
next
  case (3 m\<^sub>1 m\<^sub>2 m\<^sub>3 m\<^sub>4 m\<^sub>5 m\<^sub>6)
  let ?R = "\<lambda>(m\<^sub>1,m\<^sub>2). (glb m\<^sub>1, glb m\<^sub>2) \<in> R \<and> rg m\<^sub>1 = rg m\<^sub>2"

  have a: "?R (m\<^sub>1, f m\<^sub>2 m\<^sub>4) \<and> (f m\<^sub>2 m\<^sub>4,f m\<^sub>3 m\<^sub>4) \<in> beh \<alpha>'"
  proof -
    have "?R (m\<^sub>1, m\<^sub>2)" using 3 by auto
    moreover have "?R (m\<^sub>2,f m\<^sub>2 m\<^sub>4) \<and> (f m\<^sub>2 m\<^sub>4,f m\<^sub>3 m\<^sub>4) \<in> beh \<alpha>'" 
      using \<alpha> 3 unfolding step\<^sub>t_def by blast
    ultimately show ?thesis using assms(1) unfolding transitive_def by auto
  qed
  have b: "(f m\<^sub>3 m\<^sub>4,f m\<^sub>3 m\<^sub>5) \<in> beh (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) \<and> ?R (f m\<^sub>3 m\<^sub>5, m\<^sub>6)"
  proof -
    have "?R (m\<^sub>5, m\<^sub>6)" using 3 by auto
    moreover have "(f m\<^sub>3 m\<^sub>4,f m\<^sub>3 m\<^sub>5) \<in> beh (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) \<and> ?R (f m\<^sub>3 m\<^sub>5, m\<^sub>5)"
      using \<beta> 3 unfolding step\<^sub>t_def by simp
    ultimately show ?thesis using assms(1) unfolding transitive_def by auto
  qed
  have r: "\<forall>m. ?R (m,m)"
    using assms(2) unfolding reflexive_def by simp
  have "(f m\<^sub>2 m\<^sub>4,f (f m\<^sub>2 m\<^sub>4) (f m\<^sub>3 m\<^sub>5)) \<in> beh (\<lfloor>UNIV,\<beta>,f\<^sub>1\<rfloor>) \<and> (f (f m\<^sub>2 m\<^sub>4) (f m\<^sub>3 m\<^sub>5),(f m\<^sub>3 m\<^sub>5)) \<in> beh (\<lfloor>UNIV,\<alpha>,f\<^sub>2\<rfloor>)"
    using e a b by blast

  thus ?case using 3(1,3) a b r by fastforce
qed

lemma chke_nil_esc' [simp]:
  "chke (\<beta>, {}) (\<lfloor>v,\<alpha>,f\<rfloor>) R G = chk \<beta>  (\<lfloor>v,\<alpha>,f\<rfloor>) R G"
proof -
  have "escape {} (\<lfloor>v,\<alpha>,f\<rfloor>) = { (\<lfloor>v,\<alpha>,f\<rfloor>) } " by (cases \<alpha>; auto simp: liftg_def escape_def) 
  thus ?thesis by (auto simp: chke_def)
qed

lemma a [simp]:
  "{(m, m'). m' = m(x :=\<^sub>s e m)} O {(m, m'). m' = m(aux: f\<^sub>2)} = 
   {(m, m'). m' = m(x :=\<^sub>s e m, aux: f\<^sub>2)}"
  by auto

lemma rg_aux[simp]:
  "rg (m(aux: f)) = rg m"
  by (auto simp: rg_def aux_upd_def)

lemma glb_aux[simp]:
  "glb (m(aux: f)) = (glb m)\<lparr>state_rec.more := f m\<rparr>"
  by (auto simp: aux_upd_def glb_def)

lemma glb_upd[simp]:
  "glb (m(Glb r :=\<^sub>s e)) = (glb m)(r :=\<^sub>s e)"
  by (auto simp: glb_def st_upd_def)

lemma rg_reg_upd[simp]:
  "rg (m(Reg r :=\<^sub>s e)) = (rg m)(r := e)"
  by (auto simp: rg_def st_upd_def)

lemma rg_glb_upd[simp]:
  "rg (m(Glb r :=\<^sub>s e)) = rg m"
  by (auto simp: rg_def st_upd_def)

lemma [simp]:
  "aux (\<lfloor>v,\<alpha>,f\<rfloor>) = f"
  by (auto simp: liftg_def)

lemma [simp]:
  "m(x :=\<^sub>s st m x) = m"
  by (auto simp: st_upd_def)

lemma [simp]:
  "m(x :=\<^sub>s e, x :=\<^sub>s e') = m(x :=\<^sub>s e')"
  by (auto simp: st_upd_def)

lemma [simp]:
  "state_rec.more (glb m) = state_rec.more m"
  by (auto simp: glb_def)

lemma fn_eq1[simp]:
  "(m = m'(x := e)) = (m x = e \<and> (\<forall>y. y \<noteq> x \<longrightarrow> m y = m' y))"
  by auto

lemma fn_eq2[simp]:
  "(m'(x := e) = m) = (m x = e \<and> (\<forall>y. y \<noteq> x \<longrightarrow> m y = m' y))"
  by auto

lemma [simp]:
  "(st m (Glb Z) = st (glb m) Z) = True"
  "(rg m R = st m (Reg R)) = True"
  "(st m\<^sub>1 (Reg R) = rg m\<^sub>1 R) = True"
  by (auto simp: glb_def rg_def)

declare expand_pairs.simps [simp del]

lemma expand_pairs [simp]:
  "expand_pairs p l = (\<lambda>(i,s). (expand_op (l ! i), fset s)) ` fset p"
  unfolding expand_pairs.simps by auto

end