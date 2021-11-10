
local
fun delete'(set,mem) = HOLset.delete(set,mem) handle _ => set
in
fun filter_cont ct = 
    HOLset.foldr 
        (fn (ns,set) => 
            case HOLset.find 
                     (fn (vn,vs) => HOLset.member(fvs vs,ns)) set of 
                SOME _ => delete'(set,ns)
              | NONE => set) ct ct
end

fun ex2fsym fsym strl th = 
    let val th' = spec_all th
        val (ct,asl) = (cont th',ant th')
        val (hyp,conc) = dest_imp (concl th')
        val inputvars0 = filter_cont (cont th') 
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) essps 
                                   (List.map (dest_var o (parse_term_with_cont ct)) strl)
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val inputvl = List.map (parse_term_with_cont ct) strl
        val ((n,s),b) = dest_exists conc
        val _ = new_fun fsym (s,List.map dest_var inputvl)
        val fterm = mk_fun fsym inputvl
        val b' = substf ((n,s),fterm) b
    in mk_thm (ct,asl,mk_imp hyp b')
    end


fun new_ax f = 
    let
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end


val _ = new_sort "set" [];
val _ = new_sort "mem" [("A",mk_sort "set" [])];
val _ = new_sort "rel" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "rel" "->"

val set_sort = mk_sort "set" []
fun mem_sort A = mk_sort "mem" [A]
fun rel_sort A B = mk_sort "rel" [A,B]
fun mk_set A = mk_var(A,set_sort)
fun mk_rel R A B = mk_var(R,rel_sort A B)
fun mk_mem a A = mk_var(a,mem_sort A)

val _ = EqSorts := "rel" :: (!EqSorts)
val _ = EqSorts := "mem" :: (!EqSorts)

val _ = new_pred "Holds" [("R",rel_sort (mk_set "A") (mk_set "B")),
                         ("a",mem_sort (mk_set "A")),
                         ("b",mem_sort (mk_set "B"))]

val AX0 = new_ax “?A a:mem(A).T”

fun dest_mem_sort s = 
    let val (sn,tl) = dest_sort s
    in if sn = "mem" then hd tl else raise ERR ("dest_mem_sort.input sort is not a mem sort",[s],[],[])
    end

(*Axiom 1 (Relational comprehension): For any two sets A and B, and any property P that can obtain of an element of A and an element of B, there exists a unique relation φ:A↬B such that φ(x,y) if and only if P obtains of x and y.

*)


 fVarInst : (string * (var list * form)) list -> thm -> thm

entry point.  The variables are the bound variables and the form is the body of the abstraction.  Then after you substitute, you check that the list of arguments is the right length, and then do the beta-reduction to eliminate the bound variables.

fun abstractl l fm = 
    case l of [] => fm
            | h :: t => abstract h (abstractl t fm)
 
fun fVarInst_fm1 (pair as (fvn:string,(vl:(string * sort) list,fm:form))) f0 = 
    case view_form f0 of 
        vfVar(fv0,args) => 
        if fv0 = fvn then if length args = length vl then
                             (* abstractl vl *) fm
                          else raise ERR ("fVarInst.list length differs.",[],[],[f0])
        else f0
      | vQ(q,n,s,b) => mk_quant q n s (fVarInst_fm1 pair b)
      | vConn(co,l) => mk_conn co (List.map (fVarInst_fm1 pair) l)
      | vPred _ => f0

fun subst_form (f0,f) fm = 
    case view_form fm of 

val ifffm = “!a b. P(a,b) <=> Holds(Q:B->A,b,a)”
fun fVarInst_fm1 ifffm f0 = 
    let val (iff,bvs) = strip_forall ifffm 
        val (fV,actu) = dest_dimp iff 



(*

fun fVarInst_fm1 Q l ct f0 = 
    let val Qfvs = fvf Q
        val (orgvs,tms) = List.map fst l
        (*variables in Q to terms which can be constructed from ct*)
        val _ = HOLset.isSubset(List.foldr (fn (t,set) => HOLset.union(fvt t,set)) essps tms,ct) orelse
                raise ERR ("fVarInst_fm1, extra variables.",[],[],[f0])
        val Q' = mk_inst l [] Q
        val _ = HOLset.isSubset(fvf Q',ct)
        val 
*)
fun fVarInst_fm pairl f0 = 
List.foldr (uncurry fVarInst_fm1) f0 pairl

val AX1 = new_ax
“!A B:set.?!R:A->B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)”


val f0 = concl AX1
val fm = “Holds(Q:B->A,b,a)”
val fvn = "P"
val vl = [("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))]
val pair = (fvn,(vl,fm))

fVarInst_fm1 pair f0

want inst 
fVarInst_fm1 pair $ concl AX1
val f0 = “!b:mem(C). Q(b) & (!b:mem(B).Holds(R:A->B,a,b) <=>P(a,b))”



val f0 = “!b:mem(B).P(a,b)”

val f0 = “P(a:mem(A),b:mem(B))”
fun fVarInst_fm l f = 
    case l of 
        [] => f
      | (fvn,(vl,fm)) :: t => 
        let val f' = fVarInst_fm t f
            val 
fun fVarInst l th = 
    case l of 
        [] => th 
      | h :: t =>
        let val (ct,asl,w) = dest_thm th
            val 


(*
inst_thm (mk_inst 
              [(("a",mem_sort $mk_set "A"),mk_var("a",mem_sort $mk_set "A")),
               (("b",mem_sort $mk_set "B"),mk_var("b",mem_sort $mk_set "B"))] [("P",“Holds(Q:A->B,a,b)”)]) (spec_all AX1)
*)


(*must be able to inst the P(a,b) into P0(B(1),B(0))
in the case that 

*)



fun AX1 (f:form) (a0 as (n1,s1),b0 as (n2,s2)) = 
    let val fvs = fvf f
        val a = mk_var a0
        val aset = dest_mem_sort s1
        val b = mk_var b0
        val bset = dest_mem_sort s2
        val _ = HOLset.member(fvs,(n1,s1)) orelse 
                raise ERR ("AX1.first variable not occurs in the input formula",[],[a],[f])
        val _ = HOLset.member(fvs,(n2,s2)) orelse 
                raise ERR ("AX1.second variable not occurs in the input formula",[],[b],[f])
        val rs = rel_sort aset bset
        val rvar = mk_var("R",rs)
        val holdspred = mk_pred "Holds" [rvar,a,b]
        val f0 = mk_dimp holdspred f
        val f1 = mk_uex "R" rs
                (mk_forall n1 s1 
                           (mk_forall n2 s2
                                     f0))
    in
        mk_thm(fvf f1,[],f1)
    end

(*Definition 2.1. A relation φ:A↬B is called a function from A to B if for any x∈A, there exists exactly one y∈B with φ(x,y).*)
val _ = new_pred "isFun" [("R",rel_sort (mk_set "A") (mk_set "B"))]
val _ = new_pred "isInj" [("R",rel_sort (mk_set "A") (mk_set "B"))]
val _ = new_pred "isSurj" [("R",rel_sort (mk_set "A") (mk_set "B"))]
val _ = new_pred "isBij" [("R",rel_sort (mk_set "A") (mk_set "B"))]

val Fun_def = new_ax “!A B R:rel(A,B). isFun(R) <=> !x:mem(A). ?!y:mem(B). Holds(R,x,y)”


(*
val _ = rapf "!A B R:rel(A,B). isFun(R) <=> !x:mem(A). ?!y:mem(B). Holds(R,x,y)";
*)

val _ = new_fun "Eval" (mem_sort (mk_set "B"),[("R",rel_sort (mk_set "A") (mk_set "B")),
                        ("x",mem_sort (mk_set "A"))]) 

val Eval_def = new_ax “!A B Fn:rel(A,B). isFun(Fn) ==>!x y. Holds(Fn,x,y) <=> y = Eval(Fn,x)”

val Inj_def = new_ax “!A B R:rel(A,B). isInj(R) <=> !x1:mem(A) x2:mem(A) y:mem(B). Holds(R,x1,y) & Holds(R,x2,y) ==> x1 = x2”
val Surj_def = new_ax “!A B R:rel(A,B). isSurj(R) <=> !y:mem(B).?x:mem(A). Holds(R,x,y)”

val _ = new_pred "isTab" [("R",rel_sort (mk_set "A") (mk_set "B")),
                          ("p",rel_sort (mk_set "TR") (mk_set "A")),
                          ("q",rel_sort (mk_set "TR") (mk_set "B"))]

val Tab_def = new_ax
“!A B R TR p:TR->A q:TR->B.isTab(R,p,q) <=> 
 (!x y. Holds(R,x,y) <=> ?r. Eval(p,r) = x & Eval(q,r) = y) & !r s. Eval(p,r) = Eval(p,s) & Eval(q,r) = Eval(q,s) ==> r = s”

(*
Axiom 2 (Tabulations): For any relation φ:A↬B, there exists a set |φ| and functions p:|φ|→A and q:|φ|→B such that: (1) for any x∈A and y∈B, we have φ(x,y) if and only if there exists r∈|φ| with p(r)=x and q(r)=y, and (2) for any r∈|φ| and s∈|φ|, if p(r)=p(s) and q(r)=q(s), then r=s.
*)

(*enable not unique sort variables?*)
(*
val _ = new_fun "π1" (rel_sort (mk_set "TR") (mk_set "A"),[("R",rel_sort (mk_set "A") (mk_set "B")),("TR",set_sort)])

val _ = new_fun "π2" (rel_sort (mk_set "TR") (mk_set "B"),[("R",rel_sort (mk_set "A") (mk_set "B")),("TR",set_sort)])
*)

(*how to let the ex2fsym function skip the TR and assign function symbols pi1 pi2?*)
val AX2 = new_ax “!A B R:A->B.?TR p:TR->A q:TR->B. (!x y. Holds(R,x,y) <=> ?r. Eval(p,r) = x & Eval(q,r) = y) & !r s. Eval(p,r) = Eval(p,s) & Eval(q,r) = Eval(q,s) ==> r = s”

(*
Theorem 2.2. There exists a set ∅ which has no elements.

Proof. By Axiom 0, there exists a set A. By Axiom 1, there exists a relation φ:A↬A such that φ(x,y) holds never. Using Axiom 2, let ∅ be a tabulation of φ.  ▮
*)

(*how can we just type the name once? for prove_store*)
(*rw you idiot gives me  ~(~a'' = a'' & b = b)*)

local
val lemma = AX1 “~(a:mem(A) = a) & b:mem(A) = b” (("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "A")))
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma) 
in
val Thm_2_2 = proved_th $ (*val (ct,asl,w) = cg $*)
e0
(strip_assume_tac AX0 >> strip_assume_tac lemma' >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 >>
 qexists_tac ‘TR’ >> strip_tac >> 
 by_tac “!a b. ~Holds(R:A->A,a:mem(A),b:mem(A))” 
 >-- (rpt strip_tac >> pop_assum (K all_tac) >> pop_assum (K all_tac) >>
      once_arw[] >> ccontra_tac >> fs[]) >>
 suffices_tac “Holds(R:A->A,Eval(p:TR->A,a'),Eval(q:TR->A,a':mem(TR)))”
 >-- arw[] >>
 pop_assum (K all_tac) >> arw[] >> qexists_tac ‘a'’ >> rw[])
(form_goal
“?Empty. !a:mem(Empty).F”)
end


(*
 val (ct,asl,w) = cg $
e0
(strip_assume_tac AX0 >> strip_assume_tac lemma' >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 >>
 qexists_tac ‘TR’ >> strip_tac >> 
 by_tac “!a b. ~Holds(R:A->A,a:mem(A),b:mem(A))” 
 >-- (rpt strip_tac >> pop_assum (K all_tac) >> pop_assum (K all_tac) >>
      pop_assum (K all_tac) >> last_x_assum (K all_tac) >> once_arw[] >> rw[]))
(form_goal
“?Empty. !a:mem(Empty).F”)
*)


val _ = store_thm("Thm_2_2",Thm_2_2)

local 
val lemma = AX1 “y = a:mem(A) & z = a” (("y",mem_sort (mk_set "A")),("z",mem_sort (mk_set "A")))
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma) 
in
val Thm_2_3 = proved_th $ 
e0
(strip_assume_tac AX0 >> 
 strip_assume_tac lemma' >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 >>
 qby_tac ‘Holds(R,a,a)’ >--
 (pop_assum (K all_tac) >> pop_assum (K all_tac) >> arw[]) >>
 pop_assum mp_tac >> once_arw[] >> strip_tac  >>
 qexistsl_tac [‘TR’,‘r’] >> 
 strip_tac >> first_x_assum irule >> arw[] >>
 fs[] >>
 once_rw[CONJ_COMM] >> first_x_assum $ (irule o iffLR) >>
 qexists_tac ‘x'’ >> rw[])
(form_goal
“?ONE x:mem(ONE). !x':mem(ONE). x' = x”)
end



val _ = new_fun "1" (set_sort,[])
val ONE = mk_fun "1" []
val _ = new_fun "star" (mem_sort ONE,[])



fun Rel2Pred P (ns as (n,s)) =
    let val onens = ("one0",mem_sort ONE)
        val conj1 = mk_eq (mk_var onens) (mk_var onens)
    in AX1 (mk_conj conj1 P)  (onens,ns)
    end

val Thm_2_4_R_ver = proved_th $
e0
(cheat)
(form_goal
“!A R:1 -> A. ?B i:B->A. !a:mem(A).Holds(R,star,a) <=> ?b. a = Eval(i,b)”)

(*
Theorem 2.4. For any property P of elements of a set A, there exists a set B and an injective function i:B→A such that for a∈A, we have P(a) iff a=i(b) for some b∈B.
*)

fun uex_ex f = 
    let val th0 = iffLR $ uex_def f |> undisch
        val c0 = concl th0
        val ((n,s),b) = dest_exists c0
        val th1 = assume b |> conjE1 
        val th2 = existsI (n,s) (mk_var(n,s)) (concl th1) th1
        val th3 = existsE (n,s) th0 th2
    in disch f th3
    end

(*val P = “a:mem(A) = b”*)
(*P(a#)

 {(A : set), (b : mem(A))}, 
   |- ?!(R : rel(1, A)).
        !(one0 : mem(1))  (a : mem(A)).
          Holds(R#, one0#, a#) <=> one0# = one0# & P(a#): thm

{(A : set), (b : mem(A))}, 
   |- ?(B : set)  (i : rel(B#, A)).
        !(a : mem(A)). P(a#) <=> ?(b : mem(B#)). a# = Eval(i#, b#):

fvar of string
fVar of (string * term list)


!a. P(a)

when specalise a function term, check not inst into an fvar.

P(a)

P(f(a))

a 
*)
val ns = ("a",mem_sort  (mk_set "A"))
fun Thm_2_4 P (ns as (n,s)) = 
    let val l1 = Rel2Pred P ns
        val l1' = dimp_mp_l2r l1 (uex_def $ concl l1)
        val l2 = uex_ex (concl l1) 
        val l1'_cj2 = mp l2 l1
        val f = concl l1'_cj2
        val ((r,rsort),b) = dest_exists f
        val chooseR = assume b
        val codR = el 2 $ snd $ dest_sort rsort
        val insted = specl [codR,mk_var(r,rsort)] Thm_2_4_R_ver
        val insted' = rewr_rule[chooseR] insted
        val exEed = existsE (r,rsort) l1'_cj2 insted'
    in exEed
    end

(*
Theorem 2.5. If |φ| and |φ|′ are two tabulations of the same relation φ:A↬B, then there is a bijection between |φ| and |φ|′.
*)

val Thm_2_5 = proved_th $
e0
(cheat)
(form_goal
“!A B R:A->B T1 p1:T1->A q1:T1->B T2 p2:T2->A q2:T2->B.isTab(R,p1,q1) & isTab(R,p2,q2) ==> ?b:T1 ->T2.isBij(b)”)


(*
Corollary 2.6. If |S| and |S|′ are two tabulations of the same subset S⊆A, then there is a bijection between |S| and |S|′.


The composite of two relations φ:A↬B and ψ:B↬C is defined to be the relation ψφ:A↬C (also written ψ∘φ) such that ψφ(x,z) holds of x∈A and z∈C iff there is a y∈B with φ(x,y) and ψ(y,z). The identity relation idA:A↬A is defined by idA(x,y)⇔x=y.

Theorem 2.7. Composition of relations is associative (χ(ψφ)=(χψ)φ), and identity relations are identities for composition (idB∘φ=φ=φ∘idA). The composite of functions is a function, and the identity relation is a function. The composite of bijections is a bijection, and a relation φ:A↬B is a bijection iff there is a relation ψ:B↬A such that ψφ=idA and φψ=idB.
*)

val _ = new_fun "o" (rel_sort (mk_set "A") (mk_set "C"),
                     [("phi",rel_sort (mk_set "B") (mk_set "C")),
                      ("psi",rel_sort (mk_set "A") (mk_set "B"))])

(*AQ: phi still not parsable, too many phis of different versions.*)
val o_def = new_ax 
“!A B phi:A->B C psi:B->C a:mem(A) c:mem(C). 
(?b. Holds(phi,a,b) & Holds(psi,b,c)) <=> Holds(psi o phi,a,c)”

val _ = new_fun "id" (rel_sort (mk_set "A") (mk_set "A"),
                     [("A",set_sort)])


val Thm_2_7_assoc = proved_th $
e0
(cheat)
(form_goal
“!A B phi:A->B C psi:B->C D chi:C->D. (chi o psi) o phi = chi o psi o phi”)


val Thm_2_7_id = proved_th $
e0
(cheat)
(form_goal
“!A B phi:A->B. phi o id(A) = phi & id(B) o phi = phi”)

val Thm_2_7_bij = proved_th $
e0
(cheat)
(form_goal
 “!A B phi:A->B.isBij(phi) <=> ?psi:B->A. psi o phi = id(A) & phi o psi = id(B)”)

(*val _ = new_fun "*" (set_sort,[("A",set_sort),("B",set_sort)]) *)
(*
For sets A and B, let ⊤:A↬B denote the relation such that ⊤(x,y) holds always. A tabulation of ⊤ is denoted A×B; it is a set equipped with functions p:A×B→A and q:A×B→B such that for any x∈A and y∈B, there exists a unique z∈A×B with p(z)=x and q(z)=y. It is called the cartesian product of A and B.
Theorem 2.8. For any sets A and B, A×B is a product of A and B in the category Set, and a coproduct in the category Rel.
*)

val T_ex = proved_th $
e0
cheat
(form_goal
“!A B. ?T0:A->B. !a b. Holds(T0,a,b)”)

val Cross_ex = proved_th $
e0
(cheat)
(form_goal
 “!A B. ?AxB pi1:AxB ->A pi2:AxB ->B.
  (!x:mem(A) y:mem(B). ?r:mem(AxB).Eval(pi1,r) = x & Eval(pi2,r) = y) &
   !r s. Eval(pi1,r) = Eval(pi1,s) & Eval(pi2,r) = Eval(pi2,s)
  ”)


val Cross_def = 
    Cross_ex |> spec_all |> eqT_intro 
             |> iffRL |> ex2fsym "*" ["A","B"] 
             |> C mp (trueI []) |> gen_all

val pi1_def = 
   Cross_def |> spec_all |> eqT_intro 
             |> iffRL |> ex2fsym "pi1" ["A","B"] 
             |> C mp (trueI []) |> gen_all

val pi2_def = 
   pi1_def |> spec_all |> eqT_intro 
             |> iffRL |> ex2fsym "pi2" ["A","B"] 
             |> C mp (trueI []) |> gen_all

val _ = new_fun "Top" (rel_sort (mk_set "A") (mk_set "B"),
                       [("A",set_sort),("B",set_sort)])

val _ = new_pred "isSetPr" [("p1",rel_sort (mk_set "AxB") (mk_set "A")),
                            ("p2",rel_sort (mk_set "AxB") (mk_set "B"))]

val SetPr_def = new_ax
“!A B AxB p1:AxB->A p2:AxB->B. 
isSetPr(p1,p2) <=>
!X f:X->A g:X->B.isFun(f) & isFun(g) ==> ?!fg: X->AxB.p1 o fg = f & p2 o fg = g”



val _ = new_pred "isRelcP" [("i1",rel_sort (mk_set "A") (mk_set "AuB")),
                            ("i2",rel_sort (mk_set "B") (mk_set "AuB"))]

val RelcoPr_def = new_ax
“!A B AuB i1:A->AuB i2:B->AuB. 
isRelcP(i1,i2) <=>
!X f:A->X g:B->X.?!fg:AuB ->X. fg o i1 = f & fg o i2 = g”

val Thm_2_8_SetPr = proved_th $
e0
(cheat)
(form_goal
“!A B. isSetPr(pi1(A,B),pi2(A,B))”)

val SPa_ex =
let val th0 = rewr_rule[SetPr_def] Thm_2_8_SetPr
    val f = th0 |> spec_all |> concl |> snd o dest_imp
    val th1 = uex_ex f
    val th0' = strip_all_and_imp th0
    val th2 = mp th1 th0' 
in disch_all th2 |> gen_all
end 

(*

val th0 = proved_th $
e0
cheat
(form_goal
“isFun(f) & isFun(g) & isFun(h) ==>
      pi1(A, B) o SPa(f, g) = f & pi2(A, B) o SPa(f, g) = g”)

val th0' = proved_th $
e0
cheat
(form_goal
“!h.isFun(f) & isFun(g) & isFun(h) ==>
      pi1(A, B) o SPa(f, g) = f & pi2(A, B) o SPa(f, g) = g”)

redepth_fconv no_fconv COND_EXISTS_FCONV (concl $ gen_all th0)
 basic_fconv no_fconv COND_EXISTS_FCONV (concl th0)

 basic_fconv no_fconv COND_EXISTS_FCONV (concl $ gen_all th0)
example here.
th0 |> gen_all |> basic_fconv no_fconv COND_EXISTS_FCONV spec_all |> ex2fsym "SPa" ["f","g"] 
*)



val SPa_def = 
    SPa_ex |> spec_all |> ex2fsym "SPa" ["f","g"] 
 

val RelcP_ex = proved_th $
e0
(cheat)
(form_goal
“!A B. ?i1:A->A * B i2:B->A * B.
 !a b ab. Holds(i1,a,ab) <=> a = Eval(pi1(A,B),ab) & 
          Holds(i2,b,ab) <=> b = Eval(pi2(A,B),ab)”)

val tau1_def = 
    RelcP_ex |> spec_all |> eqT_intro 
             |> iffRL |> ex2fsym "tau1" ["A","B"] 
             |> C mp (trueI []) |> gen_all

val tau2_def = 
    tau1_def |> spec_all |> eqT_intro 
             |> iffRL |> ex2fsym "tau2" ["A","B"] 
             |> C mp (trueI []) |> gen_all

val Thm_2_8_RelcP = proved_th $
e0
(cheat)
(form_goal
“!A B. isRelcP(tau1(A,B),tau2(A,B))”)

(*
Theorem 2.9. The category Set has finite limits.

Proof. It remains to construct the equalizer of two functions f,g:A→B. Let S be the subset of A so that x∈S just when f(x)=g(x); then |S|→A is easily shown to be an equalizer of f and g.  ▮
*)

val _ = new_pred "SetEz" [("f",rel_sort (mk_set "A") (mk_set "B")),
                           ("g",rel_sort (mk_set "A") (mk_set "B")),
                           ("e",rel_sort (mk_set "E") (mk_set "A"))]

(*thesetting is considering two categories at the same time, any thing to do for that?, below is ugly, have not tested if some of e or x0 is a function can be proved rather than stated*)

val SetEz_def = new_ax
“!A B f:A->B g:A->B E e:E->A. SetEz(f,g,e) <=>
 isFun(f) & isFun(g) & isFun(e) & !X x:X->A.isFun(x) & f o x = g o x ==> ?!x0:X->E. isFun(x0) & x = e o x0”

val Thm_2_9_Eqlz = proved_th $
e0
(cheat)
(form_goal
“!A B f:A->B g:A->B.isFun(f) & isFun(g) ==> ?E e:E->A.SetEz(f,g,e)”)

(*

Theorem 2.10. For any function f:A→B we have f=me, where m:im(f)↪B is an injection and e:A↠im(f) is a surjection. A set im(f) equipped with such m and e is unique up to bijection and is called the image of f.


*)

val Thm_2_10 = proved_th $
e0
(cheat)
(form_goal
“!A B f:A->B. isFun(f) ==> ?M e:A->M m:M->B. f = m o e & isInj(e) & isSurj(m)”)


(*2.11 left to tomorrow...*)

(*
Axiom 3 (power sets): For any set A, there exists a set PA and a relation ϵ:A↬PA such that for any subset S of A, there exists a unique s∈PA with the property that for any x∈A, we have x∈S iff ϵ(x,s).
*)

(*val _ = new_fun "Pow" (set_sort,[("A",set_sort)]) *)

val AX3 = new_ax 
“!A. ?PA e:A->PA. !S0:1->A.?!s:mem(PA). !x:mem(A). Holds(S0,star,x) <=> 
 Holds(e,x,s)”

(*
Theorem 2.12. For any relation R:B↬A, there exists a unique function fR:B→PA such that R(y,x) if and only if ϵ(x,fR(y)). It follows that Set is a topos (and Rel is a power allegory).
*)

val Pow_def = 
    AX3 |> spec_all |> eqT_intro 
        |> iffRL |> ex2fsym "Pow" ["A"] 
        |> C mp (trueI []) |> gen_all


val eps_def = 
    Pow_def |> spec_all |> eqT_intro 
            |> iffRL |> ex2fsym "eps" ["A"] 
            |> C mp (trueI []) |> gen_all


(*filter cont correct?*)

(*want subset notation, give a ref to tokenizer?*)

(*base change*)

val BC_ex = proved_th $
e0
(cheat)
(form_goal
“!Z Y f:Z->Y. ?BCf:Pow(Y) -> Pow(Z). 
 !ys:mem(Pow(Y)) zs:mem(Pow(Z)). Holds(BCf,ys,zs) <=>
 !z:mem(Z). Holds(eps(Z),z,zs) ==> Holds(eps(Y),Eval(f,z),ys)”)

val BC_def = 
    BC_ex |> spec_all |> eqT_intro 
          |> iffRL |> ex2fsym "BC" ["f"] 
          |> C mp (trueI []) |> gen_all

(*TODO: show BC is a functor Pow(B) ->Pow (A)*)
val InPow_def = 
 let val f = concl $ spec_all eps_def
     val uth = uex_def f
     val th0 = rewr_rule[uth] eps_def
     val th1 = spec_all th0
 in th1 |>  eqT_intro |> iffRL |> ex2fsym "InPow" ["S0"] 
        |> C mp (trueI []) |> gen_all
 end


(*sub*)
fun Pow A = mk_fun "Pow" [A]

(*poset order of P(A)*)
val _ = new_pred "PO"[("S1",mem_sort (Pow (mk_set "A"))),
                       ("S2",mem_sort (Pow (mk_set "A")))]

val PO_def = new_ax
“!A S1:mem(Pow(A)) S2:mem(Pow(A)).
 PO(S1,S2) <=> !a. Holds(eps(A),a,S1) ==> Holds(eps(A),a,S1)”

val Thm_2_11_SEx_ex = proved_th $
e0
cheat
(form_goal
 “!Z Y f:Z->Y. ?Ef:Pow(Z)-> Pow(Y). isFun(Ef) &
  !zs:mem(Pow(Z)) ys:mem(Pow(Y)). PO(Eval(Ef,zs),ys) <=> PO(zs,Eval(BC(f),ys))”)


val Thm_2_11_SAll_ex = proved_th $
e0
cheat
(form_goal
 “!Z Y f:Z->Y. ?Af:Pow(Z)-> Pow(Y). isFun(Af) &
  !ys:mem(Pow(Y)) zs:mem(Pow(Z)). PO(Eval(BC(f),ys),zs) <=> PO(ys,Eval(Af,zs))”)

(*
Definition 2.1. An allegory is a locally posetal 2-category A equipped with an involution (−)o:Aop→A which is the identity on objects, such that

the involution is order preserving and distributes over composition, i.e. (ψϕ)o=ϕoψo,
each hom-poset A(x,y) has binary meets, and

*)

val _ = new_fun "OP" (rel_sort (mk_set "A") (mk_set "B"),
                      [("R",rel_sort (mk_set "A") (mk_set "B"))])

val OP_ex = proved_th $
e0
cheat
(form_goal
“!A B R:A->B. ?R':B->A. !a b. Holds(R,a,b) <=> Holds(R',b,a)”)

val OP_def = 
    OP_ex |> spec_all |> eqT_intro |> iffRL |> ex2fsym "OP" ["R"] 
          |> C mp (trueI []) |> gen_all

val OP_DISTR = proved_th $
e0
cheat
(form_goal
“!A B phi:A->B C psi:B->C. OP(psi o phi) = OP(phi) o OP(psi)”)

(*
If x and y are elements of a poset, then their meet is an element x∧y of the poset such that:

x∧y≤x and x∧y≤y;
if a≤x and a≤y, then a≤x∧y.
*)

val _ = new_pred "Sub" [("R1",rel_sort (mk_set "A") (mk_set "B")),
                        ("R2",rel_sort (mk_set "A") (mk_set "B"))]

val Sub_def = new_ax 
“!A B R1:A->B R2. Sub(R1,R2) <=> !a b. Holds(R1,a,b) ==> Holds(R2,a,b)”


val Meet_ex = proved_th $
e0
(cheat)
(form_goal 
 “!A B R1:A->B R2:A->B. ?M:A->B. !a b. Holds(M,a,b) <=> Holds(R1,a,b) & Holds(R2,a,b)”)


val Meet_def = Meet_ex |> spec_all |> eqT_intro |> iffRL 
                       |> ex2fsym "Meet" ["R1","R2"] 
                       |> C mp (trueI []) |> gen_all

val Meet_property = proved_th $
e0
(cheat)
(form_goal
“!A B R1:A->B R2:A->B. Sub(Meet(R1,R2),R1) & Sub(Meet(R1,R2),R2) &
 !R0. Sub(R0,R1) & Sub(R0,R2) ==> Sub(R0,Meet(R1,R2))”)


val Join_ex = proved_th $
e0
(cheat)
(form_goal 
 “!A B R1:A->B R2:A->B. ?J:A->B. !a b. Holds(J,a,b) <=> Holds(R1,a,b) | Holds(R2,a,b)”)


val Join_def = Join_ex |> spec_all |> eqT_intro |> iffRL 
                       |> ex2fsym "Join" ["R1","R2"] 
                       |> C mp (trueI []) |> gen_all

(*
If x and y are elements of a poset P, then their join (or supremum, abbreviate sup, or least upper bound, abbreviated lub), is an element x∨y of the poset such that:

x≤x∨y and y≤x∨y;
if x≤a and y≤a, then x∨y≤a.

*)

val Join_property = proved_th $
e0
(cheat)
(form_goal
“!A B R1:A->B R2:A->B. Sub(R1,Join(R1,R2)) & Sub(R2,Join(R1,R2)) &
 !R0. Sub(R0,R1) & Sub(R0,R2) ==> Sub(Join(R1,R2),R0)”)

(*the modular law holds: for ϕ:x→y, ψ:y→z, and χ:x→z, we have ψϕ∩χ≤ψ(ϕ∩ψoχ).*)

val MODULAR_LAW = proved_th $
e0
(cheat)
(form_goal
 “!x y phi:x->y z psi:y->z chi:x->z. 
  Sub(Meet(psi o phi,chi),psi o Meet(phi,OP(psi) o chi))”)

(*
A union allegory Is an allegory whose hom-posets have finite joins that are preserved by composition. Thus a union allegory is locally a lattice. If additionally it is locally a distributive lattice, it is called a distributive allegory.
*)

val left_o_pres_Join = proved_th $
e0
cheat
(form_goal
 “!A B R1:A->B R2:A->B R:B->C. R o Join(R1,R2) = Join(R o R1, R o R2)”)


val right_o_pres_Join = proved_th $
e0
cheat
(form_goal
 “!A B R1:A->B R2:A->B R:C->A. Join(R1,R2) o R = Join(R1 o R, R2 o R)”)


(*
A division allegory is a distributive allegory in which composition on one (and therefore the other) side has a right adjoint (left or right division). That is: given r:A→B and s:A→C, there exists s/r:B→C such that

t≤s/r∈hom(B,C)⇔t∘r≤s∈hom(A,C)
*)

val Div_ex = proved_th $
e0
cheat
(form_goal
 “!A B r:A->B C s:A->C. ?sdr:B->C. 
  !t.Sub(t,sdr) <=> Sub(t o r,s)”)

val Thm_2_12 = proved_th $
e0
(cheat)
(form_goal
“!B A R:B->A.?!fR:B->Pow(A).isFun(fR) & !y x.(Holds(R,y,x) <=> Holds(eps(A),x,Eval(fR,y)))”)

(*
Theorem 2.13. For any two sets A and B, there exists a set BA and a function ev:BA×A→B such that for any function f:A→B there exists a unique element sf∈BA such that ev(sf,a)=f(a) for all a∈A. It follows that Set is a cartesian closed category.
*)


val Thm_2_3_5 = proved_th $
e0
cheat
(form_goal
 “!A a:mem(A). ?!R:1->A. isFun(R) & Eval(R,star) = a”)

(*mem as fun*)
val MF_def =
let val f = concl $ spec_all Thm_2_3_5
    val uth = uex_def f
    val th = dimp_mp_l2r (spec_all Thm_2_3_5) uth
in
th |> eqT_intro |> iffRL |> ex2fsym "MF"["a"]
   |> C mp (trueI []) |> gen_all
end

(*
val mem_pair = proved_th $
e0
()
(form_goal
“!A B a:mem(A) b:mem(B).Eval(Spa(MF(a),MF(b)),star)”)
*)

val Thm_2_13 = proved_th $
e0
(cheat)
(form_goal
“!A B.?A2B ev:A2B * A ->B. isFun(ev) & 
 !f:A->B.isFun(f) ==> ?!sf:mem(A2B).!a:mem(A).Eval(ev,Eval(SPa(MF(sf),MF(a)),star)) = Eval(f,a)”)

(*

Theorem 2.14. If R is an equivalence relation on A, then there is a surjective function q:A↠B such that R(x,y) holds iff q(x)=q(y).
*)
val _ = new_pred "ER" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val _ = new_pred "Refl" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val Refl_def = new_ax
 “!A R:A->A. Refl(R) <=> !a. Holds(R,a,a)”
val _ = new_pred "Sym" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val Sym_def = new_ax
 “!A R:A->A. Sym(R) <=> !a1 a2. Holds(R,a1,a2) ==> Holds(R,a2,a1)”

val _ = new_pred "Trans" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val Trans_def = new_ax
 “!A R:A->A. Trans(R) <=> !a1 a2 a3. Holds(R,a1,a2) & Holds(R,a2,a3) ==> Holds(R,a1,a3)”

val ER_def = new_ax
“!A R:A->A. ER(R) <=> Refl(R) & Sym(R) & Trans(R)”

val Thm_2_14 = proved_th $
e0
(cheat)
(form_goal
“!A R:A->A. ER(R) ==> ?B q:A->B. isSurj(q) & !x y.Holds(R,x,y) <=> Eval(q,x) = Eval(q,y)”)

(*
Axiom 4 (Infinity): There exists a set N, containing an element o, and a function s:N→N such that s(n)≠o for any n∈N and s(n)=s(m) only if n=m for any n,m∈N.
*)

val AX4 = new_ax
“?N z:mem(N) s:N->N. isFun(s) & !n:mem(N). ~(Eval(s,n) = z) & 
 !n m. Eval(s,n) = Eval(s,m) <=> n = m”

(*Axiom 5 (Collection): For any set A and any property P which can obtain of an element of A and a set, there exists a set B, function p:B→A, and a B-indexed family of sets M:B↬Y such that (1) P(p(b),Mb) holds for any b∈B, and (2) for any a∈A, if there exists a set X with P(a,X), then a∈im(p).

can not have im(p) as function, since then we have func that takes ar into sets
*)

fun Eval f e = mk_fun "Eval" [f,e] 

(*
val P = “?f:A-> X. Eval(f,a) = x0”
val (n,s) = ("a", mem_sort (mk_set "A"))
val ns = (n,s)
val (sn,ss) = ("X",set_sort)
val S0 = (sn,ss)
 
*)

fun AX5 P (ns as (n,s)) (S0 as(sn,ss)) = 
    let val (sortname,A0) = dest_sort s
        val A = if sortname = "mem" then hd A0
                else raise ERR ("first input not a member.",[],[mk_var ns],[])
        val ct = fvf P
        val B = pvariantt ct (mk_set "B")
        val (Bn,Bs) = dest_var B
        val p = pvariantt ct (mk_rel "p" B (mk_set "A"))
        val (pn,ps) = dest_var p
        val Y = pvariantt ct (mk_set "Y")
        val (Yn,Ys) = dest_var Y
        val M = pvariantt ct (mk_rel "M" B Y)
        val (Mn,Ms) = dest_var M
        val b = pvariantt ct (mk_mem "b" B)
        val (bn,bs) = dest_var b
        val substed = substf (S0,Eval M b) (substf (ns,Eval p b) P)
        val cj1 = mk_forall bn bs substed
        val X = pvariantt ct (mk_set "X")
        val a = pvariantt ct (mk_mem "a" A)
        val (aan,aas) = dest_var a
        val substed' = substf (S0,X) (substf (ns,a) P)
        val b0 = pvariantt ct (mk_mem "b0" B)
        val (b0n,b0s) = dest_var b0
        val concl2 = mk_exists b0n b0s (mk_eq (Eval p b0) a)
        val cj2 = mk_forall aan aas (mk_imp substed' concl2)
        val cjs = mk_conj cj1 cj2
        val f = mk_exists Bn Bs $ mk_exists pn ps $
                          mk_exists Yn Ys $ mk_exists Mn Ms cjs
    in mk_thm(fvf f,[],f) 
    end





(*
!a b c. P(a,b,c) ==> ?d.Q(c,d) does not work

!c a b. P(a,b,c) ==> ?d.Q(c,d)

!c.(?a b.P(a,b,c)) ==> ?d.Q(c,d)


a rule that swaps 

fun form var 

?x. x = y & P(x) <=> P(y)

?x. P(x) /\ x = y 

?x.x = y /\ P(x,z) /\ z = z'

?x.x = y /\ P(x,z) /\ z = z'

1) reorder 2) swap once needed TODO.





*)

(*
1.Have so many axiom schema or even thm schema, is that a reason to have formula variables which takes variable list as input?
2.Algorithm sketch for moving equality to leftmost.
3. COND_EXISTS_FCONV requires the variable to be quantified in the innermost.
4.phi ϕ cannot be read, different versions of phis?
5.have a ref for strings which are parsable, so user can define a symbol for subset?
6.store thm, how to just type the name once and just do two things of 1) create a term of thm with val ... name 2) store it in dict, in one function?
7.new filter_cont
8.truth table proof tool for propositional tautalogy?
9.Look at Isabelle's axiom scheme.
10. if time permits, tokenizer, fixed somehow, but still not pretty.

want a truth table tactic for propositional taut, so all the propositional drules can be solved by it immediately.

rapf "!a:mem(A). (!a:mem(B).P(a)) & P(a)";
val it = !(a' : mem(A)). (!(a : mem(B)). P(a#)) & P(a): form

look a bit to the current file to see if any obvious improvement
Any particularly interesting things to do in the setting of SEAR, maybe defining recursive set using AX5 is one thing to do, as suggested in SEAR nlab, and forcing in SEARC seems interesting but a bit ambitious.
*)
rapf "!a.P(a) & (!a:mem(A).Q(a))"
“!a.P(a) & (!a.Q(a))“”

(*how to use formula variables also for rw? using the bound variable*)


val f =  "!a:set a:mem(A).Holds(R:A->B,a,b)"



val ast = fst $ parse_ast $ lex f

val ns =  aInfix (aId "a", ":", aId "set")

val b = aBinder
      ("!", aInfix (aId "a", ":", aApp ("mem", [aId "A"])),
       aApp
        ("Holds",
         [aInfix (aId "R", ":", aInfix (aId "A", "->", aId "B")), aId "a",
          aId "b"]))

val str = "!"

val env = empty; val n = 0


f you want equation

  !a b…c.  P(a,b,…c) <=> ..a..b..c

then you can use 

  ("P", ([a,b,…,c], ..a..b..c))

how to deal  with P(f(a))?

In which case will we need / should we allow partial application

(*skip if it is premature *)

(* (P(a) ==> P(f(a))) ===> ...*)

fun fVar_Inst (pair as (P,(argl:(string * sort) list,Q))) f = 
    case view_form f of
        vfVar(P0,args0) =>
(*ListPair.map ListPair.foldl*)
(*mk_inst (zip argl args0)ListPair. [] *)
        if P0 = P then
            let val venv = match_tl essps (List.map mk_var argl) args0 emptyvd 
            in inst_form (mk_menv venv emptyfvd) Q
            end
(*if the number of arguments is wrong, or the sorts is wrong, then handle the matching exn by returning f *)
        else f
      | vConn(co,fl) => mk_conn co (List.map (fVar_Inst pair) fl)
      | vQ(q,n,s,b) => mk_quant q n s (fVar_Inst pair b)
      | vPred _ => f

P(a:mem(A),b:mem(B))

Q(c:mem(C),d:mem(D))

(*don;t do the inst above in this function, but need to call other functions to do the inst_sort first*)



val f0 = concl AX1

val P = "P";val argl = [("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))];val Q = “Holds(Q:B->A,b,a)”;

fVar_Inst (P,(argl,Q)) f0


A & B <=> B & A

(A & B) & C <=> A & B & C


rapf "ϕ"; (*0x03D5*)

rapf "!a:mem(A). (!a:mem(B).P(a)) & P(a)";
val pf =
   pQuant
    ("!", "a", psrt ("mem", [pVar ("A", psvar " 0")]),
     pConn
      ("&",
       [pQuant
         ("!", "a", psrt ("mem", [pVar ("B", psvar " 1")]),
          pfVar ("P", [pVar ("a", psrt ("mem", [pVar ("B", psvar " 1")]))])),
        pfVar ("P", [pVar ("a", psvar " 2")])])): pform


below unexpected, should record pAnno info in env


> val f = "!a:mem(A).P(a)";
val f = "!a:mem(A).P(a)": string
> val ast = fst $ parse_ast $ lex f;
val ast =
   aBinder
    ("!", aInfix (aId "a", ":", aApp ("mem", [aId "A"])),
     aApp ("P", [aId "a"])): ast
> val (pf,(env,_)) = ast2pf ast (empty,0);
val env = (?, ?, ?, ?, 2): env
val pf =
   pQuant ("!", "a", psvar " 0", pfVar ("P", [pVar ("a", psvar " 0")])):
   pform
> pdict env;
val it = ([], [], ["(A -> psv  1)"], [], 2):
   string list * string list * string list * string list * int


here 
ast2pt ns (env3,n) 

problematic: 

ns Infix (aId "a", ":", aApp ("mem", [aId "A"])): ast

env3 = ([], [], ["(a -> psv  2)", "(A -> psv  1)"], [], 3):

“!A B:set.?!R:A->B.T”

val f = "!A B:set.?!R:A->B.T"

--

think about later:

 val f = "!A B:set.?!R:A->B.T": string
> val ast = fst $ parse_ast $ lex f;
val ast =
   aBinder
    ("!", aId "A",
     aBinder
      ("!", aInfix (aId "B", ":", aId "set"),
       aBinder
        ("?!", aInfix (aId "R", ":", aInfix (aId "A", "->", aId "B")),
         aId "T"))): ast
> val (pf,(env,_)) = ast2pf ast (empty,0);
val env = (?, ?, ?, ?, 3): env
val pf =
   pQuant
    ("!", "A", psvar " 0",
     pQuant
      ("!", "B", psvar " 1", pQuant ("?!", "R", psvar " 2", pPred ("T", [])))):
   pform
> pdict env;
val it =
   ([], ["( 2 -> rel(pv A : psv  0,pv B : psv  1))", "( 1 -> set)"], [], [],
    3): string list * string list * string list * string list * int
> type_infer_pf env pf;
val it = (?, ?, ?, ?, 6): env
> pdict it;
val it =
   ([],
    ["( 5 -> psv  2)", "( 4 -> psv  1)", "( 3 -> psv  0)",
     "( 2 -> rel(pv A : psv  0,pv B : psv  1))", "( 1 -> set)"], [], [], 6):
   string list * string list * string list * string list * int

the 5 |-> psvar 2, 4 |-> psv 1, useless
----
rapf "!A B:set.?!R:A->B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)"

val f = "y = a:mem(A) & z = a";
val ast = fst $ parse_ast $ lex f;
val (pf,(env,_)) = ast2pf ast (empty,0);
pdict env;

(*trouble here
try:

val t = "a:mem(A)";
val ast = fst $ parse_ast $ lex t;
val (pt,(env,_)) = ast2pt ast (empty,0);

*)


type_infer_pf env pf loops;
dest pf into
val h = pPredf;
       ("=",
        [pVar ("y", psvar " 0"),
         pAnno
          (pVar ("a", psvar " 1"), psrt ("mem", [pVar ("A", psvar " 1")]))]);
val t = [pPred ("=", [pVar ("z", psvar " 2"), pVar ("a", psvar " 1")])];
 type_infer_pf env h loops
val ptl = [pVar ("z", psvar " 2"), pVar ("a", psvar " 1")];
foldr deal with the a first
val pt = pVar ("a", psvar " 1");
val (ps,env) = ps_of_pt pt env;
pdict $ snd ps;
val it =
   ([], ["( 1 -> mem(pv A : psv  1))"],
    ["(z -> psv  2)", "(y -> psv  0)", "(a -> psv  1)"], [], 3):
   string list * string list * string list * string list * int
> pdict env;
val it =
   ([], ["( 1 -> mem(pv A : psv  1))"],
    ["(z -> psv  2)", "(y -> psv  0)", "(a -> psv  1)"], [], 3):
   string list * string list * string list * string list * int

env does not change here

type_infer env pt ps loops where
# val it = pVar ("a", psvar " 1"): pterm
> # val it = psvar " 1": psort
> pdict env;
val it =
   ([], ["( 1 -> mem(pv A : psv  1))"],
    ["(z -> psv  2)", "(y -> psv  0)", "(a -> psv  1)"], [], 3):
   string list * string list * string list * string list * int
