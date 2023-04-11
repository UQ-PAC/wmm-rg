theory RecordsPlay
  imports SimAsm_Security
begin

datatype color = blue | green

record point =
   x :: int 
   y :: int

record cpoint = point +
   col :: color
  
definition cpt1 :: cpoint 
  where "cpt1 \<equiv> \<lparr> x=1, y=1, col=green \<rparr>"

lemma "point.more cpt1 = \<lparr>col=green\<rparr>" 
  by (simp add: cpt1_def)

(*--from SimAsm_Security.thy--------------------------------------

datatype sec = bool

record ('v, 'a) sec_state_rec = "('v, 'a) state_rec" +
  \<Gamma> :: "'a \<Rightarrow> bool"

-----------------------------------------------------------*)
(* sec_state_rec.defs has make, fields, extend truncate *)

lemma "state_rec.more (sec_state_rec.make s c i g) = \<lparr>\<Gamma> = g\<rparr>"
  by (simp add: sec_state_rec.defs)

lemma "state_rec.extend s val =  \<lparr>st = st s, cap = cap s, initState = initState s, \<dots> = val\<rparr>"
  by (simp add: state_rec.defs)

lemma "sec_state_rec.make s c i g = \<lparr>st=s, cap=c, initState=i, \<Gamma>=g\<rparr>"
  by (simp add: sec_state_rec.defs)

(* fields returns a record fragment containing only the fields of its argument,
    where "field" refers to the extention (after the "+" sign), see sec2_state_rec *)
lemma "sec_state_rec.fields g1 = \<lparr>\<Gamma> = g1\<rparr>"
  by (simp add: sec_state_rec.defs)

(* a record can be extended by more than one field; 
    if we extend more than once then every use of helper functions needs to be specialised
    i.e., types are not inferred  *)

record ('v, 'a) sec2_state_rec = "('v, 'a) sec_state_rec" +
  \<delta> :: "'a \<Rightarrow> bool"
  \<eta> :: "'a \<Rightarrow> bool"

lemma "sec2_state_rec.make s c i g d e = \<lparr>st=s, cap=c, initState=i, \<Gamma>=g, \<delta> = d, \<eta> = e\<rparr>"
  by (simp add: sec2_state_rec.defs)

lemma "sec2_state_rec.fields g1 g2 = \<lparr>\<delta> = g1, \<eta> = g2\<rparr>"
  by (simp add: sec2_state_rec.defs)
 

(* truncate remove additional fields, by putting them into the more part *)
lemma "state_rec.truncate (sec_state_rec.make s c i g) =  \<lparr>st=s, cap=c, initState=i\<rparr>"
  by (simp add: state_rec.defs sec_state_rec.defs)

lemma "state_rec.more (sec_state_rec.truncate (sec_state_rec.make s c i g)) = \<lparr>\<Gamma> = g\<rparr>"
  by (simp add: sec_state_rec.defs)


definition s1 :: "('v,'a) sec_state_rec"
  where "s1 \<equiv>
    \<lparr> st = undefined, 
      cap = {}, 
      initState = undefined,
      \<Gamma> = (\<lambda>v. True)\<rparr>"

lemma "state_rec.more s1 = \<lparr>\<Gamma>=(\<lambda>v. True)\<rparr>"
  by (simp add: s1_def)

lemma "state_rec.more s1 = \<lparr>\<Gamma>=\<Gamma> s1, \<dots>= sec_state_rec.more s1\<rparr>" 
  by (simp add: s1_def)

definition s0 :: "('v,'a) state_rec"
  where "s0 \<equiv>
    \<lparr> st = undefined, 
      cap = {}, 
      initState = undefined\<rparr>"

(* Function extend takes two arguments: a record to be extended and a record
containing the new fields. *)
definition s2:: "('v, 'a) sec_state_rec" where
  "s2 \<equiv> state_rec.extend s0 (sec_state_rec.fields (\<lambda>v. True))"

lemma "sec_state_rec.fields (\<lambda>v. True) = \<lparr>\<Gamma> = (\<lambda>v. True)\<rparr>"
  by (simp add: sec_state_rec.defs)
  