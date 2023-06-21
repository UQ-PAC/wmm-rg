theory SimAsm_Reasoning
  imports SimAsm_WP SimAsm_StateStack
begin


type_synonym ('r,'v,'a) auxopSt = "('r,'v,('r,'v,'a) tstack,'a) auxop"
type_synonym ('r,'v,'a) opbasicSt = "('r,'v,('r,'v,'a) tstack,'a) opbasic" 

section \<open>Locales for reasoning, either with speculation (reasoning_spec) or without (reasoning_WOspec)\<close>

(* We are using unlablled states from here onwards; labelling only occurs in some parts of the
    wp reasoning *)


(*---------------------------------------------------------------------------------------*)

locale reasoning_WOspec = wp_WOspec rg glb + expression st st_upd aux aux_upd locals
  for rg :: "('r,'v,'a) varmap_rec_scheme \<Rightarrow> 'e"
  and glb :: "('r,'v,'a) varmap_rec_scheme \<Rightarrow> 'f" 
  and st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v"
  and st_upd :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> ('r,'v,'a) tstack"
  and aux :: "('r,'v,'a) tstack \<Rightarrow> 'a"
  and aux_upd :: "('r,'v,'a) tstack \<Rightarrow> (('r,'v,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('r,'v,'a) tstack"
  and locals :: "'r set"

print_locale reasoning_WOspec

context reasoning_WOspec
begin

definition reorder_inst :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> bool"
  where "reorder_inst \<alpha>' \<beta> \<alpha>  \<equiv> (re\<^sub>s \<beta> \<alpha> \<and> (\<alpha>'=fwd\<^sub>s \<alpha> (fst \<beta>)))"

abbreviation Seqw (infixr ";;" 80)                      (* i.e., Seq c w c' *)
  where "Seqw c c' \<equiv> com.Seq c reorder_inst c'"

abbreviation Iterw ("_*" [90] 90)                       (* i.e., Loop c w *)
  where "Iterw c \<equiv> com.Loop c reorder_inst"

text \<open>Convert the language into the abstract language expected by the underlying logic
      this relates the syntax to its semantics \<close> 
(*fun lift\<^sub>c :: "('r,'v,('r,'v,'a) varmap','a) lang \<Rightarrow> (('r,'v,'a) auxop', ('r,'v,'a) varmap') com" *)
fun lift\<^sub>c :: "('r,'v,('r,'v,'a) tstack,'a) lang \<Rightarrow> (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v) frame) com" 
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Op v a f) = Basic (liftg v a f)" | 
    "lift\<^sub>c (lang.Seq c\<^sub>1 c\<^sub>2) = (lift\<^sub>c c\<^sub>1) ;; (lift\<^sub>c c\<^sub>2)" |  
    "lift\<^sub>c (If b c\<^sub>1 c\<^sub>2) = (Choice (\<lambda> s. if (s=0)
                                 then (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>1)) 
                                 else (Basic (\<lfloor>ncmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>2))))" | 
    "lift\<^sub>c (While b Imix Ispec c) =  (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c))* ;; Basic (\<lfloor>ncmp b\<rfloor>)" | 
    "lift\<^sub>c (DoWhile Imix Ispec c b) =  (lift\<^sub>c c ;; Basic (\<lfloor>cmp b\<rfloor>))* ;; lift\<^sub>c c ;; Basic (\<lfloor>ncmp b\<rfloor>)" 

text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

end   (* of reasoning_WOspec*)

(*---------------------------------------------------------------------------------------*)

locale reasoning_spec = wp_spec rg glb + expression st st_upd aux aux_upd locals
  for rg :: "('r,'v,'a) varmap_rec_scheme \<Rightarrow> 'e"
  and glb :: "('r,'v,'a) varmap_rec_scheme \<Rightarrow> 'f" 
  and st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v"
  and st_upd :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> ('r,'v,'a) tstack"
  and aux :: "('r,'v,'a) tstack \<Rightarrow> 'a"
  and aux_upd :: "('r,'v,'a) tstack \<Rightarrow> (('r,'v,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('r,'v,'a) tstack"
  and locals :: "'r set" +
  fixes project' :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) varmap'"

print_locale reasoning_spec


context reasoning_spec
begin

text \<open> definition for weak memory model which is used as parameter w in sequential composition \<close>

definition sc :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> bool" 
  where "sc \<alpha>' \<beta> \<alpha>  \<equiv> \<not>(re\<^sub>s \<beta> \<alpha>)"

abbreviation Seqsc (infixr "." 80)                      (* i.e., Seq c sc c' *)
  where "Seqsc c c' \<equiv> com.Seq c sc c'"

abbreviation Itersc ("_**" [90] 90)                       (* i.e., Loop c sc *)
  where "Itersc c \<equiv> com.Loop c sc"


definition reorder_inst :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> bool"
  where "reorder_inst \<alpha>' \<beta> \<alpha>  \<equiv> (re\<^sub>s \<beta> \<alpha> \<and> (\<alpha>'=fwd\<^sub>s \<alpha> (fst \<beta>)))"

abbreviation Seqw (infixr ";;" 80)                      (* i.e., Seq c w c' *)
  where "Seqw c c' \<equiv> com.Seq c reorder_inst c'"

abbreviation Iterw ("_*" [90] 90)                       (* i.e., Loop c w *)
  where "Iterw c \<equiv> com.Loop c reorder_inst"



text \<open>Convert the language into the abstract language expected by the underlying logic
      this relates the syntax to its semantics 
      The conversion carries a command as a second parameter around, which models the "lifted rest", 
       to allow for modelling the speculation of unlimited speculation frames 
       (i.e, speculates over the rest r of the program).
      The "rest" is relative within composed language constructs (e.g., in Seq c1 c2 rest of c1 
       differs from rest of c2) \<close> 


fun lift\<^sub>c :: "('r,'v,('r,'v,'a) tstack,'a) lang \<Rightarrow> (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v) frame) com \<Rightarrow> 
                                                       (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v) frame) com" 
  where
    "lift\<^sub>c Skip r = com.Nil" |
    "lift\<^sub>c (Op v a f) r = Basic (\<lfloor>v,a,f\<rfloor>)" | 
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) r = (lift\<^sub>c c\<^sub>1 (lift\<^sub>c c\<^sub>2 r)) ;; (lift\<^sub>c c\<^sub>2 r)" |  
    "lift\<^sub>c (If b c\<^sub>1 c\<^sub>2) r =  (Choice (\<lambda> s. if (s = 0)
                    then Interrupt (Capture emptyFrame ((lift\<^sub>c c\<^sub>2 r) ;; r)) . (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>1 r)) 
                    else Interrupt (Capture emptyFrame ((lift\<^sub>c c\<^sub>1 r) ;; r)) . (Basic (\<lfloor>ncmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>2 r))))" |
    "lift\<^sub>c (While b Imix Ispec c) r = (Choice (\<lambda> s. if (s = 0)
                    then Interrupt (Capture emptyFrame (r)) . (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c r)) 
                    else Interrupt (Capture emptyFrame ((lift\<^sub>c c r) ;; r)) . (Basic (\<lfloor>ncmp b\<rfloor>))))" |
    "lift\<^sub>c (DoWhile Imix Ispec c b) r = ((lift\<^sub>c c (Basic (\<lfloor>cmp b\<rfloor>) ;; r)) ;; Basic (\<lfloor>cmp b\<rfloor>))* ;; 
                                         (lift\<^sub>c c (Basic (\<lfloor>ncmp b\<rfloor>) ;; r)) ;; Basic (\<lfloor>ncmp b\<rfloor>)" 



text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c r)"
  apply (induct c) 
  sorry

end   (* end of reasoning_spec *)

(*---------------------------------------------------------------------------------------*)

print_locale reasoning_spec

text \<open> The locale reasoning is currently set to reasoning with speculation 
        but it can be set to reasoning without speculation by replacing 
        reasoning_spec --> reasoning_WOspec \<close>

type_synonym ('r,'v,'a) stack_opbasic = "('r,'v,('r,'v,'a) tstack,'a) opbasic"

locale reasoning = reasoning_spec 

print_locale reasoning

context reasoning
begin


text \<open>Extract the instruction from an abstract operation \<close>
(* tag (opbasic) = (op \<times> auxfn) :: "('r,'v,'a) stack_opbasic \<Rightarrow> ('r,'v) op"  *)
abbreviation inst
  where "inst a \<equiv> fst (tag a)"

abbreviation auxbasic (* :: "('r,'v,'a) stack_opbasic \<Rightarrow> (('r,'v,'a) tstack,'a) auxfn" *)
  where "auxbasic a \<equiv> snd (tag a)"

text \<open>A basic is well-formed if its behaviour (i.e., its abstract semantics) agrees with the behaviour
      of its instruction and auxiliary composed (i.e., the concrete semantics of the instantiation).\<close>
(* beh \<beta> = snd (snd \<beta>); type "('r,'v,'a) stack_opbasic \<Rightarrow> bool"*)
definition wfbasic 
  where "wfbasic \<beta> \<equiv> beh \<beta> = (beh\<^sub>a) (inst \<beta>, auxbasic \<beta>)"


lemma opbasicE:
    obtains (assign) x e f v b where  "(basic ) = ((assign x e,f), v, b)" |
          (cmp) g f v b where "(basic ) = ((cmp g,f), v, b)" |
          (fence) f v b where "(basic ) = ((full_fence,f), v, b)" |
          (nop) f v b where "(basic ) = ((nop,f), v, b)" |
          (leak) c e f v b where "(basic ) = ((leak c e,f), v, b)" 
  by (cases basic, case_tac a, case_tac aa; clarsimp) 

lemma [simp]:
  "wr (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = wr (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)

lemma [simp]:
  "barriers (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = barriers (inst \<alpha>)"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto simp: Let_def split: if_splits)

lemma [simp]:
"rd (inst (fwd\<^sub>s \<alpha> (tag \<beta>))) = (if wr (inst \<beta>) \<inter> rd (inst \<alpha>) \<noteq> {} 
                                  then rd (inst \<alpha>) - wr (inst \<beta>) \<union> rd (inst \<beta>) else rd (inst \<alpha>))"
  by (cases \<alpha> rule: opbasicE; cases \<beta> rule: opbasicE; auto)

lemma vc_fwd\<^sub>s[simp]:
  "vc (fwd\<^sub>s \<alpha> \<beta>) = vc \<alpha>"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma beh_fwd\<^sub>s [simp]:
  "beh (fwd\<^sub>s \<alpha> \<beta>) = ( beh\<^sub>a (fwd\<^sub>i (inst \<alpha>) (fst \<beta>), (auxbasic \<alpha>)) )"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: wfbasic_def Let_def split: if_splits) 

lemma aux_fwd\<^sub>s [simp]:
  "auxbasic (fwd\<^sub>s \<alpha> \<beta>) = auxbasic \<alpha>"
  by (cases \<alpha> rule: opbasicE; cases \<beta>; case_tac a; auto simp: Let_def split: if_splits)

lemma inst_fwd\<^sub>s [simp]:
  "inst (fwd\<^sub>s \<alpha> (assign x e, f)) = subst\<^sub>i (inst \<alpha>) x e"
  by (cases \<alpha> rule: opbasicE; auto simp: Let_def split: if_splits)


end  (* end of context reasoning *)

end