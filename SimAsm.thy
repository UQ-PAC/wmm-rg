theory SimAsm
  imports Soundness
begin

section \<open>State\<close>

datatype ('g,'r) var = Reg 'r | Glb 'g
record ('v,'a) state_rec = st :: "'a \<Rightarrow> 'v"

type_synonym ('v,'g,'r,'a) state = "('v,('g,'r) var,'a) state_rec_scheme"
type_synonym ('v,'g,'a) gstate = "('v,'g,'a) state_rec_scheme"

type_synonym ('v,'g,'r,'a) pred = "('v,'g,'r,'a) state set"
type_synonym ('v,'g,'a) gpred = "('v,'g,'a) gstate set"

type_synonym ('v,'g,'r,'a) trel = "('v,'g,'r,'a) state rel"
type_synonym ('v,'g,'a) grel = "('v,'g,'a) gstate rel"

type_synonym ('v,'g,'r,'a) trans = "('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r,'a) pred"
type_synonym ('v,'g,'r,'a) rtrans = "('v,'g,'r,'a) trel \<Rightarrow> ('v,'g,'r,'a) trel"

type_synonym ('v,'g,'r,'a) auxfn = "('v,('g,'r) var,'a) state_rec_scheme \<Rightarrow> 'a"

definition glb
  where "glb m \<equiv> \<lambda>v. m (Glb v)"

definition rg
  where "rg m \<equiv> \<lambda>v. m (Reg v)"

section \<open>Write Operations\<close>

definition st_upd :: "('v,'a,'b) state_rec_scheme \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> ('v,'a,'b) state_rec_scheme"
  where "st_upd m a b = m \<lparr> st := ((st m) (a := b)) \<rparr>"

definition aux_upd :: "('v,'r,'a) state_rec_scheme \<Rightarrow> (('v,'r,'a) state_rec_scheme \<Rightarrow> 'a) \<Rightarrow> ('v,'r,'a) state_rec_scheme"
  where "aux_upd m f \<equiv> m\<lparr>state_rec.more := f m\<rparr>"

nonterminal updbinds and updbind

syntax
  "_updbindm" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"            ("(2_ :=\<^sub>s/ _)")
  "_updbinda" :: "'a \<Rightarrow> updbind"                  ("(2aux:/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "f(x:=\<^sub>sy)" \<rightleftharpoons> "CONST st_upd f x y"
  "f(aux: y)" \<rightleftharpoons> "CONST aux_upd f y"

lemma [simp]:
  "st (m(r :=\<^sub>s e)) q = (if r = q then e else st m q)"
  by (auto simp: st_upd_def)

lemma aux_nop [simp]:
  "m(aux:more) = m"
  by (auto simp: aux_upd_def)

lemma st_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a :=\<^sub>s b))(c :=\<^sub>s d) = (m(c :=\<^sub>s d))(a :=\<^sub>s b)"
  unfolding st_upd_def by (auto intro!: equality fun_upd_twist)

section \<open>Expression Language\<close>

datatype ('v,'g,'r) exp = Var "('g,'r) var" | Val 'v | Exp "'v list \<Rightarrow> 'v" "('v,'g,'r) exp list"

text \<open>Evaluate an expression given a state\<close>
fun ev :: "('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> 'v"
  where 
    "ev m (Var r) = st m r" |
    "ev _ (Val v) = v" |
    "ev m (Exp f rs) = f (map (ev m) rs)"

text \<open>The syntactic dependencies of an expression\<close>
fun deps :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var set"
  where 
    "deps (Var r) = {r}" |
    "deps (Exp _ rs) = \<Union>(deps ` set rs)" |
    "deps _ = {}"

text \<open>Substitute a variable for an expression\<close>
fun subst :: "('v,'g,'r) exp \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) exp"
  where
    "subst (Var r) r' e = (if r = r' then e else Var r)" |
    "subst (Exp f rs) r e = (Exp f (map (\<lambda>x. subst x r e) rs))" |
    "subst e _ _ = e"

datatype ('v,'g,'r) bexp = Neg "('v,'g,'r) bexp" | Exp\<^sub>B "'v list \<Rightarrow> bool" "('v,'g,'r) exp list"

text \<open>Evaluate an expression given a state\<close>
fun ev\<^sub>B :: "('v,'g,'r,'a) state \<Rightarrow> ('v,'g,'r) bexp \<Rightarrow> bool"
  where 
    "ev\<^sub>B m (Neg e) = (\<not> (ev\<^sub>B m e))" |
    "ev\<^sub>B m (Exp\<^sub>B f rs) = f (map (ev m) rs)"

text \<open>The syntactic dependencies of an expression\<close>
fun deps\<^sub>B :: "('v,'g,'r) bexp \<Rightarrow> ('g,'r) var set"
  where 
    "deps\<^sub>B (Neg e) = deps\<^sub>B e" |
    "deps\<^sub>B (Exp\<^sub>B _ rs) = \<Union>(deps ` set rs)"

text \<open>Substitute a variable for an expression\<close>
fun subst\<^sub>B :: "('v,'g,'r) bexp \<Rightarrow> ('g,'r) var \<Rightarrow> ('v,'g,'r) exp \<Rightarrow> ('v,'g,'r) bexp"
  where
    "subst\<^sub>B (Neg b) r e = Neg (subst\<^sub>B b r e)" |
    "subst\<^sub>B (Exp\<^sub>B f rs) r e = (Exp\<^sub>B f (map (\<lambda>x. subst x r e) rs))"

lemma [simp]:
  "ev m (subst e r f) = ev (m(r :=\<^sub>s (ev m f))) e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev m \<circ> (\<lambda>x. subst x r f)) rs = map (ev (m(r :=\<^sub>s ev m f))) rs"
    by auto
  show ?case by simp
qed auto

lemma ev_nop [simp]:
  "r \<notin> deps e \<Longrightarrow> ev (m(r :=\<^sub>s f)) e = ev m e"
proof (induct e)
  case (Exp fn rs)
  hence [simp]: "map (ev (m(r :=\<^sub>s f))) rs = map (ev m) rs" by auto
  show ?case by simp
qed auto

lemma [simp]:
  "ev\<^sub>B m (subst\<^sub>B b r e) = ev\<^sub>B (m(r :=\<^sub>s (ev m e))) b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  have [simp]: "map (ev m \<circ> (\<lambda>x. subst x r e)) rs = map (ev (m(r :=\<^sub>s ev m e))) rs"
    by (auto simp: fun_upd_def)     
  show ?case by simp
qed simp

lemma ev\<^sub>B_nop [simp]:
  "r \<notin> deps\<^sub>B b \<Longrightarrow> ev\<^sub>B (m(r :=\<^sub>s f)) b = ev\<^sub>B m b"
proof (induct b)
  case (Exp\<^sub>B fn rs)
  hence [simp]: "map (ev (m(r :=\<^sub>s f))) rs = map (ev m) rs"
    using ev_nop[of r _ m f] by (auto simp: fun_upd_def) 
  show ?case by simp
qed simp

section \<open>Operations\<close>

datatype ('v,'g,'r) op =
    assign "('g,'r) var" "('v,'g,'r) exp"
  | cmp "('v,'g,'r) bexp"
  | full_fence
  | ctrl_fence
  | nop

abbreviation ncmp
  where "ncmp b \<equiv> cmp (Neg b)"

fun beh\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) state rel"
  where
    "beh\<^sub>i (assign a e) = {(m,m'). m' = m (a :=\<^sub>s ev m e)}" |
    "beh\<^sub>i (cmp b) = {(m,m'). m = m' \<and> ev\<^sub>B m b}" |
    "beh\<^sub>i _ = Id"

text \<open>Variables written by an operation\<close>
fun wr :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var set"
  where 
    "wr (assign y _) = {y}" |
    "wr _ = {}"

text \<open>Variables read by an operation\<close>
fun rd :: "('v,'g,'r) op \<Rightarrow> ('g,'r) var set"
  where
    "rd (assign _ e) = deps e" |
    "rd (cmp b) = deps\<^sub>B b" |
    "rd _ = {}"

text \<open>Variables referenced by an operation\<close>
abbreviation refs
  where "refs a \<equiv> wr a \<union> rd a"

text \<open>Domain of register variables\<close>
abbreviation locals
  where "locals \<equiv> Reg ` UNIV"

text \<open>Instruction Reordering\<close>
text \<open>Only pattern match on first argument due to performance issues\<close>
fun re\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op \<Rightarrow> bool" 
  where
    "re\<^sub>i full_fence \<alpha> = False" |
    "re\<^sub>i (cmp b) \<alpha> = (\<alpha> \<noteq> full_fence \<and> \<alpha> \<noteq> ctrl_fence \<and> wr \<alpha> \<subseteq> locals \<and> rd (cmp b) \<inter> wr \<alpha> = {} \<and> rd (cmp b) \<inter> rd \<alpha> \<subseteq> locals)" |
    "re\<^sub>i ctrl_fence \<alpha> = (\<alpha> \<noteq> full_fence \<and> rd \<alpha> \<subseteq> locals)" |
    "re\<^sub>i \<alpha> \<beta> = (\<beta> \<noteq> full_fence \<and> wr \<alpha> \<inter> wr \<beta> = {} \<and> rd \<alpha> \<inter> wr \<beta> = {} \<and> refs \<alpha> \<inter> refs \<beta> \<subseteq> locals)"

text \<open>Sub-Instruction Forwarding\<close>
fun fwd\<^sub>i :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('v,'g,'r) op" 
  where
    "fwd\<^sub>i (assign r e) (assign r' e') = (assign r (subst e r' e'))" |
    "fwd\<^sub>i (cmp b) (assign r e) = (cmp (subst\<^sub>B b r e))" |
    "fwd\<^sub>i \<alpha> _ = \<alpha>"

definition comp (infix "\<Otimes>" 60)
  where "comp a b \<equiv> {(m,m'). \<exists>m''. (m,m'') \<in> a \<and> (m'',m') \<in> b}"

lemma re_consistent:
  "re\<^sub>i \<alpha> (fwd\<^sub>i \<beta> \<alpha>) \<Longrightarrow> beh\<^sub>i \<alpha> \<Otimes> beh\<^sub>i \<beta> \<supseteq> beh\<^sub>i (fwd\<^sub>i \<beta> \<alpha>) \<Otimes> beh\<^sub>i \<alpha>"
  by (cases \<alpha>; cases \<beta>, auto simp: comp_def intro!: st_upd_twist)

section \<open>Auxiliary State Updates\<close>

text \<open>
We wish to support auxiliary state to support more abstract reasoning about data structures
and concurrency.
This is achieved by allowing arbitrary extensions to the state representation, which
can be updated atomically at any sub-operation.
This auxiliary state cannot influence real execution behaviour by definition.
\<close>
type_synonym ('v,'g,'r,'a) auxop = "('v,'g,'r) op \<times> ('v,'g,'r,'a) auxfn"

fun beh\<^sub>a :: "('v,'g,'r,'a) auxop \<Rightarrow> ('v,'g,'r,'a) state rel"
  where "beh\<^sub>a (\<alpha>,f) = beh\<^sub>i \<alpha> O {(m,m'). m' = m(aux: f)}"

fun re\<^sub>a :: "('v,'g,'r,'a) auxop \<Rightarrow> ('v,'g,'r,'a) auxop \<Rightarrow> bool" 
  where "re\<^sub>a (\<alpha>,f) (\<beta>,f') = re\<^sub>i \<alpha> \<beta>"

fun fwd\<^sub>a :: "('v,'g,'r,'a) auxop \<Rightarrow> ('v,'g,'r,'a) auxop \<Rightarrow> ('v,'g,'r,'a) auxop" 
  where "fwd\<^sub>a (\<alpha>,f) (\<beta>,f') = (fwd\<^sub>i \<alpha> \<beta>,f)"

section \<open>Instruction Specification Language\<close>

text \<open>
To instantiate the abstract theory, we must couple each sub-operation with its precondition
and behaviour in a tuple\<close>
type_synonym ('v,'g,'r,'a) opbasic = "(('v,'g,'r,'a) auxop, ('v,'g,'r,'a) state) basic"
 
text \<open>Duplicate forwarding and reordering behaviour of underlying instruction\<close>
fun fwd\<^sub>s :: "('v,'g,'r,'a) opbasic \<Rightarrow> ('v,'g,'r,'a) auxop \<Rightarrow> ('v,'g,'r,'a) opbasic" 
  where "fwd\<^sub>s (\<alpha>,v,_) \<beta> =  (fwd\<^sub>a \<alpha> \<beta>, v, beh\<^sub>a (fwd\<^sub>a \<alpha> \<beta>))" 

text \<open>Lift an operation with specification\<close>
definition liftg :: "('v,'g,'r,'a) pred \<Rightarrow> ('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) auxfn \<Rightarrow> ('v,'g,'r,'a) opbasic" 
  ("\<lfloor>_,_,_\<rfloor>" 100)
  where "liftg v \<alpha> f \<equiv> ((\<alpha>,f), v, beh\<^sub>a (\<alpha>,f))"

text \<open>Lift an operation without specification\<close>
definition liftl :: "('v,'g,'r) op \<Rightarrow> ('v,'g,'r,'a) opbasic" 
  ("\<lfloor>_\<rfloor>" 100)
  where "liftl \<alpha> \<equiv> ((\<alpha>,state_rec.more), UNIV, beh\<^sub>a (\<alpha>,state_rec.more))"

section \<open>Language Definition\<close>

datatype ('v,'g,'r,'a) lang =
  Skip
  | Op "('v,'g,'r,'a) pred" "('v,'g,'r) op" "('v,'g,'r,'a) auxfn"
  | Seq "('v,'g,'r,'a) lang" "('v,'g,'r,'a) lang"
  | If "('v,'g,'r) bexp" "('v,'g,'r,'a) lang" "('v,'g,'r,'a) lang"
  | While "('v,'g,'r) bexp" "('v,'g,'r,'a) pred" "('v,'g,'r,'a) lang"
  | DoWhile "('v,'g,'r,'a) pred" "('v,'g,'r,'a) lang" "('v,'g,'r) bexp"

end
