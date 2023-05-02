theory State2
  imports Main 
begin

locale state = 
  fixes st :: "'s \<Rightarrow> 'var \<Rightarrow> 'val"
  fixes st_upd :: "'s \<Rightarrow> 'var \<Rightarrow> 'val \<Rightarrow> 's" ("_'((2_/ :=\<^sub>u/ _)')" [900,0,0] 901)
  fixes aux :: "'sub \<Rightarrow> 'a"
  fixes aux_upd :: "'s \<Rightarrow> ('sub \<Rightarrow> 'a) \<Rightarrow> 's" ("_'((2aux:/ _)')" [900,0] 901)
  fixes aux_extract :: "'s \<Rightarrow> 'sub"
  (* fixes region :: "'var \<Rightarrow> 'region"  *)
  assumes st_upd: "st (st_upd s var val) var2 = (if var2 = var then val else st s var2)"
  (* assumes st_eqI [intro]: "(aux a = aux b) \<Longrightarrow> (\<And> x. st a x = st b x) \<Longrightarrow> a = b" *)
  assumes st_upd_aux [simp]: "aux (aux_extract (st_upd s v x)) = aux (aux_extract s)"
  assumes aux_upd [simp]: "aux (aux_extract (aux_upd s f)) = f (aux_extract s)" 
  assumes aux_upd_st [simp]: "st (m(aux: f)) v = st m v"

  (* assumes st_upd_structure: "s(var :=\<^sub>s val) = t(var :=\<^sub>s val) \<longleftrightarrow> aux_extract (s(var :=\<^sub>s val)) = aux_extract (t(var :=\<^sub>s val))" *)



context state
begin

abbreviation st_eq :: "'s \<Rightarrow> 's \<Rightarrow> prop" ("(_/ =\<^sub>s/ _)" [800, 800] 801) where 
  "st_eq a b \<equiv> (\<And>x. st a x = st b x)"

lemma st_upd_same: "var2 = var \<Longrightarrow> st (st_upd s var val) var2 = val"
  using st_upd by auto

lemma st_upd_diff: "var2 \<noteq> var \<Longrightarrow> st (st_upd s var val) var2 = st s var2"
  using st_upd by auto

lemma st_upd_fun [simp]:
  "st (m(r :=\<^sub>u e)) = (\<lambda>x. (if r = x then e else st m x))"
  using st_upd by auto

lemma st_upd_map:
  "(\<lambda>v. st (t(x :=\<^sub>u e)) v) = (\<lambda>v. st t v)(x := e)"
  by auto

lemma st_upd_twist: "a \<noteq> c \<Longrightarrow> m(a:=\<^sub>ub)(c:=\<^sub>ud) =\<^sub>s m(c:=\<^sub>ud)(a:=\<^sub>ub)"
  by auto

lemma st_upd_region: "region r \<noteq> region r2 \<Longrightarrow> st (m(r :=\<^sub>u e)) r2 = st m r2"
  by auto

lemma aux_exec': 
  assumes "(m\<^sub>1,m\<^sub>2) \<in> P" 
  shows "(m\<^sub>1, m\<^sub>2(aux: f)) \<in> P O {(m,m'). m' = m(aux: f)}"
  using assms by auto


end (* context state *)


interpretation interpreted: state "\<lambda>x a. ()" "\<lambda>s a b. s" "(\<lambda>x. ()) :: unit \<Rightarrow> unit" "\<lambda>s f. s"
  unfolding state_def by auto



end