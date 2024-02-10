theory SimAsm_Semantics
  imports "../Syntax" SimAsm SimAsm_StateStack
begin

section \<open> Instruction Specification Language: 
           this creates the link between the abstract logic and the SimAsm instantiation \<close>

(* ('a,'b) basic = ('a \<times> 'b set \<times> 'b rel); 'a = (inst \<times> aux);  'b = state *)
(* ('r,'v,'s,'a) auxop = "('r,'v) op \<times> ('s,'a) auxfn *)
type_synonym ('r,'v,'a) auxopSt = "('r,'v,('r,'v,'a) tstack,'a) auxop"
type_synonym ('r,'v,'a) opbasicSt = "(('r,'v,'a) auxopSt, ('r,'v,'a) tstack) basic" 


locale sem_link = expression st st_upd aux aux_upd locals
  for st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v"
  and st_upd :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> ('r,'v,'a) tstack"
  and aux :: "('r,'v,'a) tstack \<Rightarrow> 'a"
  and aux_upd :: "('r,'v,'a) tstack \<Rightarrow> (('r,'v,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('r,'v,'a) tstack"
  and locals :: "'r set"


context sem_link
begin

text \<open>
To instantiate the abstract theory, we must couple each sub-operation with its precondition
and behaviour in a tuple\<close>

fun re\<^sub>s :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> bool"
  where "re\<^sub>s (\<alpha>,_,_) (\<beta>,_,_) = re\<^sub>a \<alpha> \<beta>"

text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) auxopSt \<Rightarrow> ('r,'v,'a) opbasicSt" 
  where 
    "fwd\<^sub>s ((\<alpha>,f),v,b) (assign x e,_) = (let p = (subst\<^sub>i \<alpha> x e, f) in  (p,v, beh\<^sub>a p))" |
    "fwd\<^sub>s ((\<alpha>,f),v,b) (leak c e,_) = ((\<alpha>,f),v,beh\<^sub>a (\<alpha>,f))" |
                                    (* (let p = (subst\<^sub>i \<alpha> c e, f) in  (p,v, beh\<^sub>a p))" | *)
    "fwd\<^sub>s ((\<alpha>,f),v,b) (\<beta>,_) = ((\<alpha>,f),v,beh\<^sub>a (\<alpha>,f))"

text \<open>Lift an operation with specification\<close>
definition liftg :: "('r, 'v, ('r,'v,'a)tstack,'a) pred \<Rightarrow> ('r,'v) op \<Rightarrow> (('r,'v,'a) tstack,'a) auxfn 
                                                                        \<Rightarrow> ('r,'v,'a) opbasicSt" 
  ("\<lfloor>_,_,_\<rfloor>" 100)
  where "liftg v \<alpha> f \<equiv> ((\<alpha>,f), v, beh\<^sub>a (\<alpha>,f))"

text \<open>Lift an operation without specification\<close>
definition liftl :: "('r, 'v, ('r,'v,'a)tstack,'a) pred \<Rightarrow> ('r,'v) op \<Rightarrow> ('r,'v,'a) opbasicSt" 
  ("\<lfloor>_,_\<rfloor>" 100)
  where "liftl v \<alpha> \<equiv> ((\<alpha>,aux), v, beh\<^sub>a (\<alpha>,aux))"

end   (* of locale sem_link *)


section \<open>Locales for reasoning, either with speculation (reasoning_spec) or without (reasoning_WOspec)\<close>

(* We are using unlablled states from here onwards; labelling only occurs in some parts of the
    wp reasoning *)


(*---------------------------------------------------------------------------------------*)

locale semantics_WOspec = sem_link st st_upd aux aux_upd locals
  for st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v"
  and st_upd :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> ('r,'v,'a) tstack"
  and aux :: "('r,'v,'a) tstack \<Rightarrow> 'a"
  and aux_upd :: "('r,'v,'a) tstack \<Rightarrow> (('r,'v,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('r,'v,'a) tstack"
  and locals :: "'r set"


print_locale semantics_WOspec

context semantics_WOspec
begin

definition reorder_inst :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> bool"
  where "reorder_inst \<alpha>' \<beta> \<alpha>  \<equiv> (re\<^sub>s \<beta> \<alpha> \<and> (\<alpha>'=fwd\<^sub>s \<alpha> (fst \<beta>)))"

abbreviation Seqw (infixr ";;" 80)                      (* i.e., Seq c w c' *)
  where "Seqw c c' \<equiv> com.Seq c reorder_inst c'"

abbreviation Iterw ("_*" [90] 90)                       (* i.e., Loop c w *)
  where "Iterw c \<equiv> com.Loop c reorder_inst"

text \<open>Convert the language into the abstract language expected by the underlying logic
      this relates the syntax to its semantics \<close> 

fun lift\<^sub>c :: "('r,'v,('r,'v,'a) tstack,('r,'v,'a) tstack,'a) lang \<Rightarrow> (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v) frame) com"
  where
    "lift\<^sub>c Skip = com.Nil" |
    "lift\<^sub>c (Op v a f) = Basic (liftg v a f)" | 
    "lift\<^sub>c (lang.Seq c\<^sub>1 c\<^sub>2) = (lift\<^sub>c c\<^sub>1) ;; (lift\<^sub>c c\<^sub>2)" |  
    "lift\<^sub>c (If v b c\<^sub>1 c\<^sub>2) = (Choice (\<lambda> s. if (s=0)
                                 then (Basic (\<lfloor>v,cmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>1)) 
                                 else (Basic (\<lfloor>v,ncmp b\<rfloor>) ;; (lift\<^sub>c c\<^sub>2))))" | 
    "lift\<^sub>c (While v b Ispec Imix c) =  (Basic (\<lfloor>v,cmp b\<rfloor>) ;; (lift\<^sub>c c))* ;; Basic (\<lfloor>v,ncmp b\<rfloor>)" (* | 
    "lift\<^sub>c (DoWhile Ispec Imix  c b) =  (lift\<^sub>c c ;; Basic (\<lfloor>cmp b\<rfloor>))* ;; lift\<^sub>c c ;; Basic (\<lfloor>ncmp b\<rfloor>)"  *)

text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local (lift\<^sub>c c)"
  by (induct c) auto

end   (* of semantics_WOspec*)

(*---------------------------------------------------------------------------------------*)

locale semantics_spec = sem_link st st_upd aux aux_upd locals
  for st :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v"
  and st_upd :: "('r,'v,'a) tstack \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> ('r,'v,'a) tstack"
  and aux :: "('r,'v,'a) tstack \<Rightarrow> 'a"
  and aux_upd :: "('r,'v,'a) tstack \<Rightarrow> (('r,'v,'a) tstack \<Rightarrow> 'a) \<Rightarrow> ('r,'v,'a) tstack"
  and locals :: "'r set" 
  (* + fixes project' :: "('r,'v,'a) tstack \<Rightarrow> ('r,'v,'a) varmap'" *)

print_locale semantics_spec


context semantics_spec
begin

text \<open> definition for weak memory model which is used as parameter w in sequential composition \<close>

definition sc :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> bool" 
  where "sc \<alpha>' \<beta> \<alpha>  \<equiv> \<not>(re\<^sub>s \<beta> \<alpha>)"

abbreviation Seqsc (infixr "\<cdot>" 80)                      (* i.e., Seq c sc c' *)
  where "Seqsc c c' \<equiv> com.Seq c sc c'"

abbreviation Itersc ("_**" [90] 90)                       (* i.e., Loop c sc *)
  where "Itersc c \<equiv> com.Loop c sc"


definition reorder_inst :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v,'a) opbasicSt \<Rightarrow> bool"
  where "reorder_inst \<alpha>' \<beta> \<alpha>  \<equiv> (re\<^sub>s \<beta> \<alpha> \<and> (\<alpha>'=fwd\<^sub>s \<alpha> (fst \<beta>)))"

abbreviation Seqw (infixr ";;" 80)                      (* i.e., Seq c w c' *)
  where "Seqw c c' \<equiv> com.Seq c reorder_inst c'"

abbreviation Iterw ("_*" [90] 90)                       (* i.e., Loop c w *)
  where "Iterw c \<equiv> com.Loop c reorder_inst"


text \<open>Lift a basic operation to the speculative semantics\<close>
fun lift\<^sub>b
  where
    (* Block speculative execution at a fence *)
    "lift\<^sub>b v full_fence f = ((full_fence,f), v, beh\<^sub>a (full_fence,f) \<inter> {(m,m'). ts_is_seq m})" |
    (* Ignore guards during speculative execution *)
    "lift\<^sub>b v (cmp g) f = ((cmp g,f), v, (beh\<^sub>a (cmp g,f) \<inter> {(m,m'). ts_is_seq m}) \<union>  {(m,m'). m' = aux_upd m f \<and> ts_is_spec m}) " |
    (* Extend vc with speculative execution implies correct capture setup *)
    "lift\<^sub>b v a f =  liftg (v \<inter> {ts. ts_is_spec ts \<longrightarrow> (wr a \<subseteq> topcapped ts \<and> lk a \<inter> capped ts = {})}) a f"

text \<open>Convert the language into the abstract language expected by the underlying logic
      this relates the syntax to its semantics 
      The conversion carries a command as a second parameter around, which models the "lifted rest", 
       to allow for modelling the speculation of unlimited speculation frames 
       (i.e, speculates over the rest r of the program).
      The "rest" is relative within composed language constructs (e.g., in Seq c1 c2 rest of c1 
       differs from rest of c2) 
      The second parameter carries the write-set of the lang construct, to facilitate building an
        empty frame (and its capture set) required for the semantics of speculation;
        this set equals UNIV - {sidechannels} and should be constant per instantiation
        (note, wrs must include @{term w\<^sub>l} of the rest program r, which is a com not a lang construct which
         precludes to derived it at this level)  \<close> 


fun liftspec :: "'r set \<Rightarrow> (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v,'a option) frame_scheme) com
                        \<Rightarrow> (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v,'a option) frame_scheme) com
                        \<Rightarrow> (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v,'a option) frame_scheme) com"
  where
    "liftspec wrs cs c = (Interrupt (Capture (emptyFrame wrs) (cs))) \<cdot> c"


(* remark: in this lifting, 'r' should only be appended to the command during speculation. *)
(* XXX: more principled usage of 'r'. at which point does it get added to the command? *)

fun lift\<^sub>c :: "('r,'v,('r,'v,'a) tstack,('r,'v,'a) tstack,'a) lang \<Rightarrow> (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v,'a option) frame_scheme) com \<Rightarrow> 'r set \<Rightarrow>
                                                       (('r,'v,'a) auxopSt, ('r,'v,'a) tstack, ('r,'v,'a option) frame_scheme) com"
  where
    "lift\<^sub>c Skip r wrs = com.Nil" |
    "lift\<^sub>c (Op v a f) r wrs = Basic (lift\<^sub>b v a f)" | 
    "lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2) r wrs = (lift\<^sub>c c\<^sub>1 (lift\<^sub>c c\<^sub>2 r wrs) (wrs)) ;; (lift\<^sub>c c\<^sub>2 r wrs)" |
    "lift\<^sub>c (If v b c\<^sub>1 c\<^sub>2) r wrs =  (Choice (\<lambda>s. if s = 0
                    then liftspec wrs (lift\<^sub>c c\<^sub>2 r wrs ;; r) (Basic (lift\<^sub>b v (cmp b) aux) ;; lift\<^sub>c c\<^sub>1 r wrs)
                    else liftspec wrs (lift\<^sub>c c\<^sub>1 r wrs ;; r) (Basic (lift\<^sub>b v (ncmp b) aux) ;; lift\<^sub>c c\<^sub>2 r wrs)))"  |
(*(while b then c); r = (spec(r); [b]; c )\<^emph> ; spec(c; c \<^emph> ; r ); [\<not>b] *)
    "lift\<^sub>c (While v b Ispec Imix c) r wrs =  
           (liftspec wrs r (Basic (lift\<^sub>b v (cmp b) aux) ;; lift\<^sub>c c ((lift\<^sub>c c r wrs)* ;; r) wrs) )* ;;
           liftspec wrs (lift\<^sub>c c r wrs ;; (lift\<^sub>c c r wrs)* ;; r) (Basic (lift\<^sub>b v (ncmp b) aux))" 
(* (do c while b); r = (spec(c; r ); c; [b])\<^emph> ; (spec(c \<^emph> ; c; r ); c; [\<not>b] ) *)
    (*"lift\<^sub>c (DoWhile Ispec Imix c b) r wrs =   
            (liftspec wrs 
              ( lift\<^sub>c c r wrs  ;; r )
              ( lift\<^sub>c c r wrs  ;; Basic (\<lfloor>cmp b\<rfloor>))
            )*
            ;;
            (liftspec wrs
              ((lift\<^sub>c c r wrs)*;; lift\<^sub>c c r wrs ;; r)
              ( lift\<^sub>c c r wrs  ;; Basic (\<lfloor>ncmp b\<rfloor>) ))"  *)

(*
(*(while b then c); r = (spec(r ); [b]; c)\<^emph> ; spec(c; c \<^emph> ; r ); [\<not>b] *)
    "lift\<^sub>c (While b Imix Ispec c) r wrs =  
           (Interrupt (Capture (emptyFrame (wrs)) (r))  \<cdot> (Basic (\<lfloor>cmp b\<rfloor>) ;; (lift\<^sub>c c r wrs)))* ;;
           (Interrupt (Capture (emptyFrame (wrs)) ((lift\<^sub>c c r wrs) ;; (lift\<^sub>c c r wrs)* ;; r )) \<cdot> (Basic (\<lfloor>ncmp b\<rfloor>)))"  |
(* (do c while b); r = (spec(c; r ); c; [b])\<^emph> ; (spec(c \<^emph> ; c; r ); c; [\<not>b]; r ) *)
    "lift\<^sub>c (DoWhile Imix Ispec c b) r wrs =  
           ((Interrupt (Capture (emptyFrame (wrs)) (r))  \<cdot> ((lift\<^sub>c c r wrs) ;; r))  \<cdot>
                                                      ((lift\<^sub>c c r wrs) ;; (Basic (\<lfloor>cmp b\<rfloor>))))* ;;
            (Interrupt (Capture (emptyFrame (wrs)) (r))  \<cdot> ((lift\<^sub>c c r wrs)* ;; (lift\<^sub>c c r wrs) ;; r))  \<cdot>
                                                      ((lift\<^sub>c c r wrs) ;; (Basic (\<lfloor>ncmp b\<rfloor>)) ;; r)" 

*)


text \<open>The language is always thread-local\<close>
lemma local_lift [intro]:
  "local r \<Longrightarrow> local (lift\<^sub>c c r {})"
  apply (induct c arbitrary: r) 
  by auto

end   (* end of semantics_if_spec *)

(*---------------------------------------------------------------------------------------*)

text \<open> The locale reasoning is currently set to reasoning with speculation 
        but it can be set to reasoning without speculation by replacing 
        reasoning_spec --> reasoning_WOspec \<close>


locale semantics = semantics_spec 

print_locale semantics

context semantics
begin


text \<open>Extract the instruction from an abstract operation \<close>
(* tag (opbasic) = (op \<times> auxfn) :: "('r,'v,'a) opbasicSt \<Rightarrow> ('r,'v) op"  *)
abbreviation inst
  where "inst a \<equiv> fst (tag a)"

abbreviation auxbasic (* :: "('r,'v,'a) opbasicSt \<Rightarrow> (('r,'v,'a) tstack,'a) auxfn" *)
  where "auxbasic a \<equiv> snd (tag a)"

text \<open>A basic is well-formed if its behaviour (i.e., its abstract semantics) agrees with the behaviour
      of its instruction and auxiliary composed (i.e., the concrete semantics of the instantiation).\<close>
(* beh \<beta> = snd (snd \<beta>); type "('r,'v,'a) opbasicSt \<Rightarrow> bool"*)
definition wfbasic 
  where "wfbasic \<beta> \<equiv> beh \<beta> = (beh\<^sub>a) (inst \<beta>, auxbasic \<beta>)"


lemma opbasicE:
    obtains (assign) x e f v b where  "(ba ) = ((assign x e,f), v, b)" |
          (cmp) g f v b where "(ba ) = ((cmp g,f), v, b)" |
          (fence) f v b where "(ba ) = ((full_fence,f), v, b)" |
          (nop) f v b where "(ba ) = ((nop,f), v, b)" |
          (leak) c e f v b where "(ba ) = ((leak c e,f), v, b)" 
  by (cases ba, case_tac a, case_tac aa; clarsimp) 

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


end  (* end of context semantics *)

end