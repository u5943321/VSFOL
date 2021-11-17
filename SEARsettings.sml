fun fVar_Inst1 (pair as (P,(argl:(string * sort) list,Q))) f = 
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
      | vConn(co,fl) => mk_conn co (List.map (fVar_Inst1 pair) fl)
      | vQ(q,n,s,b) => mk_quant q n s (fVar_Inst1 pair b)
      | vPred _ => f


(*in last meeting discussed that :
P(a:mem(A),b:mem(B))

Q(c:mem(C),d:mem(D))

should not be allowed since the sort is incorrect, but if use rw, then can just use fVar to inst form. 
*)

(*ex2fsym should check that the input thm does not contain fvars*)

fun fVar_Instl l f = 
    case l of [] => f
            | pair :: t => fVar_Inst1 pair (fVar_Instl t f)

fun fVar_Inst l th = 
    let val (ct,asl,w) = dest_thm th
        val asl' = List.map (fVar_Instl l) asl
        val w' = fVar_Instl l w
        val vs = bigunion (pair_compare String.compare sort_compare)
                          (List.map fvf (w' :: asl'))
        val newct = HOLset.union(ct,vs)
    in mk_thm (newct,asl',w')
    end


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

(*
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
*)


(*Definition 2.1. A relation φ:A↬B is called a function from A to B if for any x∈A, there exists exactly one y∈B with φ(x,y).*)
val _ = new_pred "isFun" [("R",rel_sort (mk_set "A") (mk_set "B"))]
val _ = new_pred "isInj" [("R",rel_sort (mk_set "A") (mk_set "B"))]
val _ = new_pred "isSurj" [("R",rel_sort (mk_set "A") (mk_set "B"))]
val _ = new_pred "isBij" [("R",rel_sort (mk_set "A") (mk_set "B"))]

val Fun_def = new_ax “!A B R:rel(A,B). isFun(R) <=> !x:mem(A). ?!y:mem(B). Holds(R,x,y)”


val _ = new_fun "Eval" (mem_sort (mk_set "B"),[("R",rel_sort (mk_set "A") (mk_set "B")),
                        ("x",mem_sort (mk_set "A"))]) 

val Eval_def = new_ax “!A B Fn:rel(A,B). isFun(Fn) ==>!x y. Holds(Fn,x,y) <=> y = Eval(Fn,x)”

val Inj_def = new_ax “!A B R:rel(A,B). isInj(R) <=> isFun(R) & !x1:mem(A) x2:mem(A). Eval(R,x1) = Eval(R,x2) ==> x1 = x2”;
val Surj_def = new_ax “!A B R:rel(A,B). isSurj(R) <=> isFun(R) & !y:mem(B).?x:mem(A). Eval(R,x) = y”;
val Bij_def = new_ax “!A B R:A->B. isBij(R) <=> isInj(R) & isSurj(R)”;

val _ = new_pred "isTab" [("R",rel_sort (mk_set "A") (mk_set "B")),
                          ("p",rel_sort (mk_set "TR") (mk_set "A")),
                          ("q",rel_sort (mk_set "TR") (mk_set "B"))]

val Tab_def = new_ax
“!A B R TR p:TR->A q:TR->B.isTab(R,p,q) <=> 
 isFun(p) & isFun(q) & (!x y. Holds(R,x,y) <=> ?r. Eval(p,r) = x & Eval(q,r) = y) & !r s. Eval(p,r) = Eval(p,s) & Eval(q,r) = Eval(q,s) ==> r = s”

(*
Axiom 2 (Tabulations): For any relation φ:A↬B, there exists a set |φ| and functions p:|φ|→A and q:|φ|→B such that: (1) for any x∈A and y∈B, we have φ(x,y) if and only if there exists r∈|φ| with p(r)=x and q(r)=y, and (2) for any r∈|φ| and s∈|φ|, if p(r)=p(s) and q(r)=q(s), then r=s.
*)

(*enable not unique sort variables?*)
(*
val _ = new_fun "π1" (rel_sort (mk_set "TR") (mk_set "A"),[("R",rel_sort (mk_set "A") (mk_set "B")),("TR",set_sort)])

val _ = new_fun "π2" (rel_sort (mk_set "TR") (mk_set "B"),[("R",rel_sort (mk_set "A") (mk_set "B")),("TR",set_sort)])
*)

(*how to let the ex2fsym function skip the TR and assign function symbols pi1 pi2?*)

val AX2 = new_ax “!A B R:A->B.?TR p:TR->A q:TR->B. isFun(p) & isFun(q) & (!x y. Holds(R,x,y) <=> ?r. Eval(p,r) = x & Eval(q,r) = y) & !r s. Eval(p,r) = Eval(p,s) & Eval(q,r) = Eval(q,s) ==> r = s”

(*
Theorem 2.2. There exists a set ∅ which has no elements.

Proof. By Axiom 0, there exists a set A. By Axiom 1, there exists a relation φ:A↬A such that φ(x,y) holds never. Using Axiom 2, let ∅ be a tabulation of φ.  ▮
*)

(*how can we just type the name once? for prove_store*)
(*rw you idiot gives me  ~(~a'' = a'' & b = b)*)


val AX1 = new_ax
“!A B:set.?!R:A->B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)”

(*
val f0 = concl AX1
val fm = “Holds(Q:B->A,b,a)”
val fvn = "P"
val vl = [("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))]
val pair = (fvn,(vl,fm))

val _ = fVar_Inst1 pair f0
*)

val lemma = fVar_Inst [("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "A"))],“~(a:mem(A) = a)”))] (AX1 |> qspecl [‘A’,‘A’])
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma) 
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

(*
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
*)



val _ = store_thm("Thm_2_2",Thm_2_2)

val lemma = fVar_Inst [("P",([("y",mem_sort (mk_set "A")),("z",mem_sort (mk_set "A"))],“y = a0:mem(A) & z = a0”))] (AX1 |> qspecl [‘A’,‘A’])
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma)


val Thm_2_3 = proved_th $ 
e0
(x_choosel_then ["A","a0"] assume_tac AX0 >> 
 strip_assume_tac lemma' >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 >>
 qby_tac ‘Holds(R,a0,a0)’ >--
 (pop_assum (K all_tac) >> pop_assum (K all_tac) >> arw[]) >>
 pop_assum mp_tac >> once_arw[] >> strip_tac  >>
 qexistsl_tac [‘TR’,‘r’] >> 
 strip_tac >> first_x_assum irule >> arw[] >>
 fs[] >>
 once_rw[CONJ_COMM] >> first_x_assum $ (irule o iffLR) >>
 qexists_tac ‘x'’ >> rw[])
(form_goal
“?ONE x:mem(ONE). !x':mem(ONE). x' = x”)


(*
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
*)


val ONE_def = Thm_2_3 |> eqT_intro |> iffRL |> ex2fsym "1" []
                      |> C mp (trueI []) |> gen_all
val dot_def = ONE_def |> eqT_intro |> iffRL |> ex2fsym "dot" []
                      |> C mp (trueI []) |> gen_all

val ONE = mk_fun "1" []

val dot = mk_fun "dot" []
(*
fun Rel2Pred P (ns as (n,s)) =
    let val onens = ("one0",mem_sort ONE)
        val conj1 = mk_eq (mk_var onens) (mk_var onens)
    in AX1 (mk_conj conj1 P)  (onens,ns)
    end
*)
val R_EXT = new_ax “!A B R1:A->B R2. R1 = R2 <=> !a b.Holds(R1,a,b) <=> Holds(R2,a,b)”

val FUN_EXT = proved_th $
e0
cheat
(form_goal “!A B f1:A->B f2. isFun(f1) & isFun(f2) ==>
 (f1 = f2 <=> (!a.Eval(f1,a) = Eval(f2,a)))”)

fun uex_ex f = 
    let val th0 = iffLR $ uex_def f |> undisch
        val c0 = concl th0
        val ((n,s),b) = dest_exists c0
        val th1 = assume b |> conjE1 
        val th2 = existsI (n,s) (mk_var(n,s)) (concl th1) th1
        val th3 = existsE (n,s) th0 th2
    in disch f th3
    end

fun uex2ex_rule th = mp (uex_ex $concl th) th
fun uex_expand th = rewr_rule [uex_def $ concl th] th


(*TODO; make !a.T. in rw*)
(*TODO: tactic for expand uex in goal*)
local 
val lemma = 
(fVar_Inst [("P",([("a",mem_sort (mk_set "A")),("b",mem_sort ONE)],“a = a:mem(A)”))] (AX1 |> qspecl [‘A’,‘1’])) 
val lemma' = uex_expand lemma
in
val Thm_2_3_5 = proved_th $
e0
(strip_tac >> rw[uex_def “?!f:A->1.isFun(f)”,R_EXT] >> 
 strip_assume_tac lemma' >> qexists_tac ‘R’ >> rw[Fun_def] >> strip_tac (* 2 *)
 >-- (strip_tac >> rw[uex_def “?!y:mem(1).Holds(R,x,y)”] >>
      qexists_tac ‘dot’ >> once_rw[dot_def] >>
      arw[] >> strip_tac >> rw[]) >>
 strip_tac >> strip_tac >> rw[GSYM R_EXT] >> first_x_assum irule >>
 strip_tac >> first_x_assum (qspecl_then [‘a’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 pop_assum (K all_tac) >> pop_assum mp_tac >> once_rw[dot_def] >>
 rpt strip_tac >> arw[])
(form_goal
“!A.?!f:A->1. isFun(f)”)
end

val Thm_2_3_5_expand = Thm_2_3_5 |> spec_all |> uex_expand |> gen_all

val To1_def = Thm_2_3_5_expand |> spec_all |> eqT_intro |> iffRL |> ex2fsym "To1" ["A"]
                        |> C mp (trueI []) |> gen_all


val Thm_2_4_R_ver = proved_th $
e0
(rpt strip_tac >> qspecl_then [‘1’,‘A’,‘R’] strip_assume_tac AX2 >>
 qexistsl_tac [‘TR’,‘q’] >>
 once_arw[] >> strip_tac (* 2 *)
 >-- (rw[Inj_def] >> arw[] >> rpt strip_tac >> first_x_assum irule >>
      arw[] >> once_rw[dot_def] >> rw[] (*Eval(p, x1) = Eval(p, x2) as 1 is tml*)) >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘r’ >> arw[]) >>
 qexists_tac ‘b’ >> arw[] >> once_rw[dot_def] >> rw[])
(form_goal
“!A R:1 -> A.?B i:B->A. isInj(i) & !a:mem(A).Holds(R,dot,a) <=> ?b. a = Eval(i,b)”)

(*“?a0:mem(A) ==> (!a:mem(A).P(b)) <=> P(b)” 
think about if this can be proved and behave in the desired way.

*)

local
val l0 = (fVar_Inst [("P",([("a",mem_sort ONE),("b",mem_sort (mk_set "A"))],“a = a:mem(1) & P(b:mem(A))”))] (AX1 |> qspecl [‘1’,‘A’])) |> gen_all
val uth = uex_def “?!R:1->A. !a. Holds(R, dot, a) <=> P(a)”
in
val Rel_Pred1 = proved_th $
e0
(assume_tac l0 >> strip_tac >>
 first_x_assum (qspecl_then [‘A’] assume_tac) >>
 first_assum (fn th => assume_tac (uex_def $ concl th)) >> fs[] >>
 rw[uth] >> qexists_tac ‘R’ >> once_arw[] >> rw[] >> conj_tac (* 2 *)
 >-- (strip_tac >> once_rw[]) >> 
 rpt strip_tac >> first_x_assum irule >> once_rw[dot_def] >> arw[] >>
 rpt strip_tac >> rw[])
(form_goal
“!A. ?!R:1->A.!a:mem(A). Holds(R,dot,a) <=> P(a)”)
end

(*TODO: fs[] with
 a
   1.!(a : set). P(a#) <=> Q(a#)
   2.!(a : set). P(a#)
   ----------------------------------------------------------------------
   Q(a)

loops

rfs[] loops as well, and if cut, then err is:
 ERR
     ("mp.no match", [], [],
      [Conn ("==>", [Pred ("T", []), fVar ("P", [a])]), fVar ("Q", [a])])
   raised
*)

val rfs =  rev_full_simp_tac;

(*
val Pred_Rel1 =
“!A. ?!R:1->A.!a:mem(A). P(a) <=> Holds(R,dot,a)”)
*)


(*
val lemma = fVar_Inst [("P",([("y",mem_sort (mk_set "A")),("z",mem_sort (mk_set "A"))],“y = a0:mem(A) & z = a0”))] (AX1 |> qspecl [‘1’,‘A’])
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma)
*)


(*

 BA(i : rel(B, A))(R : rel(1, A))
   1.!(A : set).
               ?!(R : rel(1, A#)).
                 !(a : mem(A#)). Holds(R#, dot, a#) <=> P(a#)
   2.!(a : mem(A)). Holds(R, dot, a#) <=> P(a#)
   3.isInj(i)
   4.!(a : mem(A)). Holds(R, dot, a#) <=> ?(b : mem(B)). a# = Eval(i, b#)
   ----------------------------------------------------------------------
   T & !(a : mem(A)). P(a#) <=> ?(b : mem(B)). a# = Eval(i, b#)

rfs loops
*)


local
val lemma = mp (uex_ex (concl $ spec_all Rel_Pred1)) (spec_all Rel_Pred1) 
in
val Thm_2_4 = proved_th $
e0
(assume_tac Thm_2_4_R_ver >> strip_tac >>
 strip_assume_tac lemma >>
 first_x_assum (qspecl_then [‘A’,‘R’] strip_assume_tac) >>
 qexistsl_tac [‘B’,‘i’] >> once_arw[] >> pop_assum (assume_tac o GSYM) >>
 (*if instead of GSYM above use fs then loop*)
 rw[] >> strip_tac >> once_arw[] >> once_arw[] >> rw[]
 )
(form_goal
“!A.?B i:B->A. isInj(i) & !a:mem(A).P(a) <=> ?b. a = Eval(i,b)”)
end

(*
Theorem 2.4. For any property P of elements of a set A, there exists a set B and an injective function i:B→A such that for a∈A, we have P(a) iff a=i(b) for some b∈B.
*)

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

(*
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
*)


(*
Theorem 2.5. If |φ| and |φ|′ are two tabulations of the same relation φ:A↬B, then there is a bijection between |φ| and |φ|′.
*)

val Tab_Fun = proved_th $
e0
(rpt strip_tac >> fs[Tab_def])
(form_goal
“!A B R:A->B TR p:TR->A q:TR->B.isTab(R,p,q) ==>
 isFun(p) & isFun(q)”)

val Tab_Eval_Rel = proved_th $
e0
(rpt strip_tac >> fs[Tab_def] >>
 qexists_tac ‘r’ >> arw[]
 )
(form_goal
“!A B R:A->B TR p:TR->A q:TR->B.isTab(R,p,q) ==>
 (!r x y. Eval(p,r) = x & Eval(q,r) = y ==> Holds(R,x,y))”)




val Tab_mem_R = proved_th $
e0
(rpt strip_tac >> fs[Tab_def] >>
 qexists_tac ‘r’ >> rw[])
(form_goal
 “!A B R:A->B TR p q. isTab(R,p:TR->A,q) ==> !r:mem(TR). Holds(R,Eval(p,r),Eval(q,r))”)

val Tab_prop1 = proved_th $
e0
(rpt strip_tac >> fs[Tab_def])
(form_goal 
“!A B R:A->B TR p:TR->A q:TR->B.
 isTab(R,p,q) ==> 
 (!x y. Holds(R,x,y) <=> ?r:mem(TR).Eval(p,r) = x & Eval(q,r) = y)”)


val Tab_prop2 = proved_th $
e0
(rpt strip_tac >> fs[Tab_def] >> first_x_assum irule >> arw[])
(form_goal 
“!A B R:A->B TR p:TR->A q:TR->B.
 isTab(R,p,q) ==> 
 (!r s. Eval(p,r) = Eval(p,s) & Eval(q,r) = Eval(q,s) ==> r = s)”)


(*TODO:
!(x : mem(T1))  (y : mem(T2)). y# = Eval(B0, x#) <=> Holds(B0, x#, y#)

flip = in this

*)

fun eq_sym a = 
    if mem a (!EqSorts) then 
        let val ns0 = srt2ns a
            val v1 = mk_var ns0
            val v2 = pvariantt (HOLset.add(essps,ns0)) v1
            val v1v2 = mk_eq v1 v2
            val v2v1 = mk_eq v2 v1
            val l2r = assume v1v2 |> sym|> disch_all
            val r2l = assume v2v1 |> sym|> disch_all
        in dimpI l2r r2l
        end
    else raise ERR ("eq_sym.input sort: " ^ a ^ " does not have equality",
                    [],[],[])


local
val lemma = fVar_Inst [("P",([("a",mem_sort (mk_set "T1")),("b",mem_sort (mk_set "T2"))],“Eval(p1:T1->A,a) = Eval(p2:T2->A,b) & Eval(q1:T1->B,a) = Eval(q2:T2->B,b)”))] (AX1 |> qspecl [‘T1’,‘T2’])
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma) 
in
val Thm_2_5 = proved_th $
e0
(rpt strip_tac >> x_choose_then "B0" strip_assume_tac lemma' >> 
 qexists_tac ‘B0’ >> rw[Bij_def] >> 
 qby_tac ‘isFun(B0)’ >--
 (rw[Fun_def] >> strip_tac >>
  rw[uex_def “?!y:mem(T2).Holds(B0:T1->T2,x,y)”] >>
  arw[] >> rev_drule Tab_mem_R >> 
  first_x_assum (qspecl_then [‘x’] assume_tac) >>
  drule Tab_prop1 >> fs[] >>
  qexists_tac ‘r’ >> arw[] >> drule Tab_prop2 >>
  rpt strip_tac >> first_x_assum irule >> arw[]) >>
 rw[Inj_def,Surj_def] >> arw[] >> strip_tac (* 2 *)
 >-- (rev_drule Tab_prop2 >> rpt strip_tac >> first_x_assum irule >>
      drule Eval_def >>
      first_assum (qspecl_then [‘x1’,‘Eval(B0,x1)’] assume_tac) >>
      first_x_assum (qspecl_then [‘x2’,‘Eval(B0,x2)’] assume_tac) >>
      first_assum (qspecl_then [‘x1’,‘Eval(B0,x1)’] assume_tac) >>
      first_assum (qspecl_then [‘x2’,‘Eval(B0,x2)’] assume_tac) >> 
      fs[]) >>
 (*Surj*)
 strip_tac >>
 fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
 drule $ GSYM Eval_def >> arw[] >>
 drule Tab_mem_R >> first_x_assum (qspecl_then [‘y’] assume_tac) >>
 rev_drule Tab_prop1 >> fs[] >>
 qexists_tac ‘r’ >> arw[])
(form_goal
“!A B R:A->B T1 p1:T1->A q1:T1->B T2 p2:T2->A q2:T2->B.isTab(R,p1,q1) & isTab(R,p2,q2) ==> ?b:T1 ->T2.isBij(b)”)
end

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

val id_def = new_ax “!A a:mem(A) b. Holds(id(A),a,b) <=> a = b”;

val Thm_2_7_assoc = proved_th $
e0
(rpt strip_tac >> rw[R_EXT,GSYM o_def] >> rpt strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘b''’ >> arw[] >> qexists_tac ‘b'’ >> arw[]) >>
 qexists_tac ‘b''’ >> arw[] >> qexists_tac ‘b'’ >> arw[])
(form_goal
“!A B phi:A->B C psi:B->C D chi:C->D. (chi o psi) o phi = chi o psi o phi”)

(*TODO:
 ?(b' : mem(C)).
               (?(b : mem(B)). Holds(phi, a, b#) & Holds(psi, b#, b'#)) &
               Holds(chi, b'#, b)

this should be simplified by using formula contains formula variables
*)

val Thm_2_7_id = proved_th $
e0
(rpt strip_tac >> rw[R_EXT] >> rpt strip_tac  (* 2 *)
 >-- (rw[GSYM o_def,id_def] >> dimp_tac >> rpt strip_tac
      >-- arw[] >> qexists_tac ‘a’ >> arw[]) >>
 rw[GSYM o_def,id_def] >> dimp_tac >> rpt strip_tac 
 >-- fs[] >> qexists_tac ‘b’ >> arw[])
(form_goal
“!A B phi:A->B. phi o id(A) = phi & id(B) o phi = phi”)

val _ = new_fun "op" (rel_sort (mk_set "B") (mk_set "A"),[("R",rel_sort (mk_set "A") (mk_set "B"))])

val op_def = new_ax “!A B R:A->B a b.Holds(op(R),a,b) <=> Holds(R,b,a)”;


(*

todo
val Bij_R = proved_th $
e0
()
(form_goal
 “!A B R:A->B.isBij(R) <=> 
  !a.?!b.Holds(R,a,b) & !b.?!a.Holds(R,a,b)”)
*)

val Fun_expand = proved_th $
e0
(rpt strip_tac >> rw[Fun_def] >>
 rw[uex_def “?!y:mem(B).Holds(R,x,y)”] >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac (* 2 *)
     >-- (first_x_assum (qspecl_then [‘a’] assume_tac) >> 
          pop_assum strip_assume_tac >> qexists_tac ‘y’ >> arw[]) 
     >-- (first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
          first_assum rev_drule >>
          first_assum (qspecl_then [‘b2’] assume_tac) >>
          first_assum drule >> arw[])) >>
 rpt strip_tac >> last_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 qexists_tac ‘b’ >> arw[] >> rpt strip_tac >> first_x_assum irule >>
 qexists_tac ‘x’ >> arw[])
(form_goal
“!A B R:A->B. isFun(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2) ==> b1 = b2)”)

val Inj_R_expand = proved_th $
e0
(rpt strip_tac >> rw[Inj_def,Fun_expand] >> dimp_tac >> strip_tac (* 2 *)
 >-- (arw[] >> rpt strip_tac (* 3  2T*) >-- rw[] >-- rw[] >>
      first_x_assum irule >> 
      qby_tac ‘isFun(R)’ 
      >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac >-- rw[] >> rw[]) >>
      drule Eval_def >> fs[]) >>
 arw[] >> rpt strip_tac (* 3  2 T*) >-- rw[] >-- rw[] >>
 first_x_assum irule >> qexists_tac ‘Eval(R,x1)’ >> 
 qby_tac ‘isFun(R)’ 
      >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac >-- rw[] >> rw[]) >>
 drule Eval_def >> arw[])
(form_goal
“!A B R:A->B. isInj(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2)==> b1 = b2) &
 (!a1 a2 b. Holds(R,a1,b) & Holds(R,a2,b) ==> a1 = a2)”)

val Surj_R_expand = proved_th $
e0
(rpt strip_tac >> rw[Surj_def,Fun_expand] >> dimp_tac >> strip_tac (* 2 *)
 >-- (arw[] >> rpt strip_tac >-- rw[] >-- rw[] >>
      qby_tac ‘isFun(R)’ 
      >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac >-- rw[] >> rw[]) >>
      drule Eval_def >> arw[] >> 
      fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
      arw[]) >>
 arw[] >>
 qby_tac ‘isFun(R)’ 
 >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac >-- rw[] >> rw[]) >>
 rpt strip_tac >-- rw[] >-- rw[] >>
 drule Eval_def >> fs[] >> 
 fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
 arw[])
(form_goal
 “!A B R:A->B. isSurj(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2)==> b1 = b2) &
 (!b. ?a.Holds(R,a,b))”)

val Bij_R_expand = proved_th $
e0
(rpt strip_tac >> rw[Bij_def,Inj_R_expand,Surj_R_expand] >>
 rpt strip_tac >> dimp_tac >-- (rpt strip_tac >>
 arw[]
 >-- (first_x_assum irule >> qexists_tac ‘a’ >> arw[]) >>
 first_x_assum irule >> qexists_tac ‘b’ >> arw[]) >>
 rpt strip_tac >> arw[] (* 3 *)
 >-- (first_x_assum irule >> qexists_tac ‘a’ >> arw[])
 >-- (first_x_assum irule >> arw[] >> qexists_tac ‘b’ >> arw[]) >>
 first_x_assum irule >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!A B R:A->B. isBij(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2)==> b1 = b2) &
 (!a1 a2 b. Holds(R,a1,b) & Holds(R,a2,b) ==> a1 = a2) &
 (!b. ?a.Holds(R,a,b)) ”)





(*

qby_tac ‘!a. ?b.Holds(phi,a,b) & Holds(psi,b,a) & 
 !b0.Holds(phi,a,b0) & Holds(psi,b0,a) ==> b0 = b’ >-- 
 (rpt strip_tac >> first_x_assum (qspecl_then [‘a’,‘a’] assume_tac) >>
  fs[] >> qexists_tac ‘b'’ >> arw[] >>
  rpt strip_tac >> 
  first_x_assum (qspecl_then [‘b0’,‘b'’] (assume_tac o GSYM)) >>
  arw[] >> qexists_tac ‘a’ >> arw[]) >>
 qby_tac ‘!b. ?a.Holds(phi,a,b) & Holds(psi,b,a) & 
 !a0.Holds(phi,a0,b) & Holds(psi,b,a0) ==> a0 = a’ >--
 (rpt strip_tac >> first_x_assum (qspecl_then [‘b’,‘b’] assume_tac) >>
  fs[] >> qexists_tac ‘b'’ >> arw[] >>
  rpt strip_tac >> 
  first_x_assum (qspecl_then [‘a0’,‘b'’] (assume_tac o GSYM)) >>
  arw[] >> qexists_tac ‘b’ >> arw[]) >>

*)


(*TODO: see why the gen var of a is b', not a'*)
val Thm_2_7_bij = proved_th $
e0
(rpt strip_tac >> rw[Bij_R_expand,id_def,R_EXT] >> dimp_tac >> strip_tac
  (* 2 *)
 >-- (qexists_tac ‘op(phi)’ >> rw[op_def,GSYM o_def] >> rpt strip_tac 
      (* 2 *)
      >-- (dimp_tac >> strip_tac (* 2 *)
           >-- (first_x_assum irule >> qexists_tac ‘b'’ >> arw[]) >>
           arw[] >> last_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
           qexists_tac ‘b'’ >> arw[]) >>
      dimp_tac >> strip_tac (* 2 *)
      >-- (first_x_assum irule >> qexists_tac ‘b'’ >> arw[]) >>
      arw[] >> first_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
      qexists_tac ‘a'’ >> arw[]) >>
 fs[GSYM o_def] >>
 qby_tac ‘!a b. Holds(phi,a,b) <=> Holds(psi,b,a)’ >--
 (rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
  >-- (first_x_assum (qspecl_then [‘a’,‘a’] assume_tac) >> fs[] >>
      qsuff_tac ‘b = b'’ >-- (strip_tac >> arw[]) >>
      first_x_assum (qspecl_then [‘b'’,‘b’] (assume_tac o GSYM)) >>
      fconv_tac (rewr_fconv (eq_sym "mem")) >> arw[] >>
      qexists_tac ‘a’ >> arw[]) >>
  first_x_assum (qspecl_then [‘b’,‘b’] assume_tac) >> fs[] >>
  qsuff_tac ‘a = b'’ >-- (strip_tac >> arw[]) >>
  first_x_assum (qspecl_then [‘b'’,‘a’] (assume_tac o GSYM)) >>
  fconv_tac (rewr_fconv (eq_sym "mem")) >> arw[] >>
  qexists_tac ‘b’ >> arw[])
 >> rpt strip_tac (* 4 *)
 >-- (first_x_assum (qspecl_then [‘a’,‘a’] assume_tac) >> fs[] >>
     qexists_tac ‘b'’ >> arw[])
 >-- (fs[] >> rev_full_simp_tac[] >> 
     first_x_assum (qspecl_then [‘b1’,‘b2’] (assume_tac o GSYM)) >> 
     arw[] >> qexists_tac ‘a’ >> arw[]) 
 >-- (fs[] >> rev_full_simp_tac[] >> 
     first_x_assum (qspecl_then [‘a1’,‘a2’] (assume_tac o GSYM)) >> 
     arw[] >> qexists_tac ‘b’ >> arw[])
 >-- (first_x_assum (qspecl_then [‘b’,‘b’] assume_tac) >> fs[] >>
     qexists_tac ‘b'’ >> arw[])
 )
(form_goal
 “!A B phi:A->B.isBij(phi) <=> ?psi:B->A. psi o phi = id(A) & phi o psi = id(B)”)

(*val _ = new_fun "*" (set_sort,[("A",set_sort),("B",set_sort)]) *)
(*
For sets A and B, let ⊤:A↬B denote the relation such that ⊤(x,y) holds always. A tabulation of ⊤ is denoted A×B; it is a set equipped with functions p:A×B→A and q:A×B→B such that for any x∈A and y∈B, there exists a unique z∈A×B with p(z)=x and q(z)=y. It is called the cartesian product of A and B.
Theorem 2.8. For any sets A and B, A×B is a product of A and B in the category Set, and a coproduct in the category Rel.
*)

local 
val lemma = fVar_Inst [("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],“T”))] (AX1 |> qspecl [‘A’,‘B’])
in
val T_uex = dimp_mp_l2r lemma (uex_def $ concl lemma) |> rewr_rule []
                        |> gen_all
end

val T_ex = proved_th $
e0
(assume_tac T_uex >> 
 rpt strip_tac >> 
 first_x_assum (qspecl_then [‘A’,‘B’] strip_assume_tac) >>
 qexists_tac ‘R’ >> arw[] >> rpt strip_tac >> rw[])
(form_goal
“!A B. ?T0:A->B. !a b. Holds(T0,a,b)”)

val Cross_ex = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘B’] strip_assume_tac T_ex >>
 qspecl_then [‘A’,‘B’,‘T0’] strip_assume_tac AX2 >> 
 qexistsl_tac [‘TR’,‘p’,‘q’] >> fs[] >> rpt strip_tac >> rw[])
(form_goal
 “!A B. ?AxB pi1:AxB ->A pi2:AxB ->B.isFun(pi1) & isFun(pi2) &
  (!x:mem(A) y:mem(B). ?r:mem(AxB).Eval(pi1,r) = x & Eval(pi2,r) = y) &
   !r s. Eval(pi1,r) = Eval(pi1,s) & Eval(pi2,r) = Eval(pi2,s) ==> r = s
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

val _ = new_pred "SetPr" [("p1",rel_sort (mk_set "AxB") (mk_set "A")),
                            ("p2",rel_sort (mk_set "AxB") (mk_set "B"))]

val SetPr_def = new_ax
“!A B AxB p1:AxB->A p2:AxB->B. 
 SetPr(p1,p2) <=>
 !X f:X->A g:X->B.isFun(f) & isFun(g) ==> ?!fg: X->AxB.isFun(fg) & p1 o fg = f & p2 o fg = g”



val _ = new_pred "RelcP" [("i1",rel_sort (mk_set "A") (mk_set "AuB")),
                            ("i2",rel_sort (mk_set "B") (mk_set "AuB"))]

val RelcP_def = new_ax
“!A B AuB i1:A->AuB i2:B->AuB. 
RelcP(i1,i2) <=>
!X f:A->X g:B->X.?!fg:AuB ->X. fg o i1 = f & fg o i2 = g”

(*

TODO
val uex_define_Fun = proved_th $
e0
()
(form_goal “!a. ?!b.P(a,b) ==> ?!f:A->B.isFun(f) & !a. P(a,Eval(f,a))”)

*)

fun Cross A B = mk_fun "*" [A,B]

val pi12_Fun = proved_th $
e0
(strip_tac >> strip_tac >>
 qspecl_then [‘A’,‘B’] strip_assume_tac pi2_def >>
 arw[])
(form_goal
“!A B. isFun(pi1(A,B)) & isFun(pi2(A,B))”)


val Thm_2_7_o_Fun = proved_th $
e0
(rpt strip_tac >> fs[Fun_expand,GSYM o_def] >> rpt strip_tac (* 2 *)
 >-- (last_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
      last_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
      qexistsl_tac [‘b'’,‘b’] >> arw[]) >>
 first_x_assum irule >> 
 qby_tac ‘b' = b’ >--
 (first_x_assum irule >> qexistsl_tac [‘a’] >> arw[]) >>
 fs[] >> qexists_tac ‘b’ >> arw[])
(form_goal
 “!A B f:A->B C g:B->C. isFun(f) & isFun(g) ==> isFun(g o f)”)

val Holds_Eval = proved_th $
e0
(rpt strip_tac >> drule Eval_def >>
 first_x_assum (qspecl_then [‘a’,‘Eval(f,a)’] assume_tac) >> fs[])
(form_goal
“!A B f:A->B. isFun(f) ==> !a.Holds(f,a,Eval(f,a))”)

val o_Eval = proved_th $
e0
(rpt strip_tac >> 
 qby_tac ‘isFun(g o f)’ >-- (irule Thm_2_7_o_Fun >> arw[]) >> 
 drule $ GSYM Eval_def >> arw[] >>
 rw[GSYM o_def] >> qexists_tac ‘Eval(f,a)’ >>
 rev_drule $ GSYM Eval_def >>
 first_x_assum (qspecl_then [‘a’,‘Eval(f,a)’] assume_tac) >> fs[] >>
 qpick_x_assum ‘isFun(g)’ assume_tac >>
 drule Holds_Eval >> arw[])
(form_goal
 “!A B f:A->B C g:B->C a:mem(A). isFun(f) & isFun(g) ==> 
  Eval(g,Eval(f,a)) = Eval(g o f,a)”)


val Thm_2_8_SetPr = proved_th $
e0
(rpt strip_tac >> rw[SetPr_def] >> rpt strip_tac >>
 rw[uex_def “?!fg:X-> A * B.isFun(fg) & pi1(A,B) o fg = f & pi2(A,B) o fg = g”] >>
 strip_assume_tac $
 uex_expand $ 
 fVar_Inst 
 [("P",([("x",mem_sort (mk_set "X")),
        ("ab",mem_sort (Cross (mk_set"A") (mk_set "B")))],
  “Eval(pi1(A,B),ab) = Eval(f:X->A,x) & 
   Eval(pi2(A,B),ab) = Eval(g:X->B,x)”))] (AX1 |> qspecl [‘X’,‘A * B’]) >>
 qexists_tac ‘R’ >> 
 qspecl_then [‘A’,‘B’] strip_assume_tac pi2_def >>
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> 
  rpt strip_tac (* 2 *) >-- 
  (first_x_assum (qspecl_then [‘Eval(f,a)’,‘Eval(g,a)’] assume_tac) >>
   arw[]) >>
  first_x_assum irule >> arw[]) >> arw[] >>
 qby_tac ‘pi1(A, B) o R = f & pi2(A, B) o R = g’ >--
 (arw[R_EXT,GSYM o_def] >> rpt strip_tac (* 2 *) 
  >-- (assume_tac Eval_def >> 
       first_assum (qspecl_then [‘A * B’,‘A’,‘pi1(A,B)’] assume_tac) >>
       first_x_assum drule >>
       first_x_assum (qspecl_then [‘X’,‘A’,‘f’] assume_tac) >>
       first_x_assum drule >> arw[] >>
       dimp_tac >> strip_tac (* 2 *) >-- arw[] >>
       first_x_assum 
        (qspecl_then [‘Eval(f,a)’,‘Eval(g,a)’] strip_assume_tac) >>
       qexists_tac ‘r’ >> arw[]) >>
 assume_tac Eval_def >> 
 first_assum (qspecl_then [‘A * B’,‘B’,‘pi2(A,B)’] assume_tac) >>
 first_x_assum drule >>
 first_x_assum (qspecl_then [‘X’,‘B’,‘g’] assume_tac) >>
 first_x_assum drule >> arw[] >>
 dimp_tac >> strip_tac (* 2 *) >-- arw[] >>
 first_x_assum 
  (qspecl_then [‘Eval(f,a)’,‘Eval(g,a)’] strip_assume_tac) >>
 qexists_tac ‘r’ >> arw[]) >> arw[] 
 (*last subgoal*)
 >>
 rpt strip_tac >> first_x_assum irule >> 
 drule Eval_def >> arw[] >> pop_assum (K all_tac) >>
 rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (once_arw[] >>
     qby_tac ‘Eval(pi1(A, B), Eval(fg', a)) = Eval(pi1(A,B) o fg',a) & 
              Eval(pi2(A, B), Eval(fg', a)) = Eval(pi2(A,B) o fg',a)’
     >-- (strip_tac >> irule o_Eval >> arw[]) >>
     arw[]) >>
 first_x_assum irule >> arw[] >> strip_tac >> 
 fconv_tac (rewr_fconv (eq_sym "mem")) (* 2 *)
 >-- (qpick_x_assum ‘pi2(A, B) o fg' = g’ (assume_tac o GSYM) >>
      once_arw[] >> irule o_Eval >> arw[]) >>
 qpick_x_assum ‘pi1(A, B) o fg' = f’ (assume_tac o GSYM) >>
 once_arw[] >> irule o_Eval >> arw[]
 )
(form_goal
“!A B. SetPr(pi1(A,B),pi2(A,B))”)


val SPa_ex =
let val th0 = rewr_rule[SetPr_def] Thm_2_8_SetPr
    val f = th0 |> spec_all |> concl |> snd o dest_imp
    val th1 = uex_def f
    val th0' = strip_all_and_imp th0
    val th2 = dimp_mp_l2r th0' th1 
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
fVar_Inst [("P",([("a",mem_sort (mk_set "A")),("ab",mem_sort (Cross (mk_set "A") (mk_set "B")))],“a = Eval(pi1(A,B),ab)”))]
(AX1 |> qspecl [‘A’,‘A * B’]) |> uex_expand
|> spec_all |> eqT_intro 
|> iffRL |> ex2fsym "tau1" ["A","B"] 
|> C mp (trueI []) |> gen_all

(*
    RelcP_ex |> spec_all |> eqT_intro 
             |> iffRL |> ex2fsym "tau1" ["A","B"] 
             |> C mp (trueI []) |> gen_all
*)

val tau2_def = 
fVar_Inst [("P",([("b",mem_sort (mk_set "B")),("ab",mem_sort (Cross (mk_set "A") (mk_set "B")))],“b = Eval(pi2(A,B),ab)”))]
(AX1 |> qspecl [‘B’,‘A * B’]) |> uex_expand
|> spec_all |> eqT_intro 
|> iffRL |> ex2fsym "tau2" ["A","B"] 
|> C mp (trueI []) |> gen_all

(*
local
val lemma =
fVar_Inst [("P",([("ab",mem_sort (Cross (mk_set "A") (mk_set "B"))),
("x",mem_sort (mk_set "X"))],
 “Holds(f:A->X,Eval(pi1(A,B),ab),x) & ~(Holds(g:B->X,Eval(pi2(A,B),ab),x))| Holds(g:B->X,Eval(pi2(A,B),ab),x) & ~Holds(f:A->X,Eval(pi1(A,B),ab),x)”))]
(AX1 |> qspecl [‘A * B’,‘X’]) |> uex_expand
in
val Thm_2_8_RelcP = proved_th $
e0
(rpt strip_tac >> rw[RelcP_def] >> rpt strip_tac >>
 uex_tac >> x_choose_then "fg" strip_assume_tac lemma >>
 qexists_tac ‘fg’ >>
 qby_tac ‘fg o tau1(A,B) = f’>--
 (rw[R_EXT] >> rw[tau1_def] >> rw[GSYM o_def] >> rw[tau1_def] >>
  rpt strip_tac >> dimp_tac >> strip_tac >> rev_full_simp_tac[]    )
 )
(form_goal
“!A B. RelcP(op(pi1(A,B)),op(pi2(A,B)))”)
end
*)

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

(*
fVar_Inst [("P",([("a",mem_sort (mk_set "A"))],“Eval(f:A->B,a) = Eval(g:A->B,a)”))] (Thm_2_4 |> qspecl [‘A’])
example of current fvar doing ill-=formed form, f and g


*)
val Inj_Fun = proved_th $
e0
(rw[Inj_def] >> rpt strip_tac >> arw[])
(form_goal
 “!A B f:A->B. isInj(f) ==> isFun(f)”)

val Inj_lcancel = proved_th $
e0
(rpt strip_tac >> fs[Inj_def] >>
 irule $ iffRL FUN_EXT >> arw[] >> strip_tac >> 
 qsuff_tac ‘Eval(m,Eval(f,a)) = Eval(m,Eval(g,a))’ >--
 (strip_tac >> first_x_assum irule >> arw[]) >>
 qby_tac ‘Eval(m, Eval(f, a)) = Eval(m o f,a) &
          Eval(m, Eval(g, a)) = Eval(m o g,a)’
 >-- (strip_tac >> irule o_Eval >> arw[]) >>
 arw[])
(form_goal
 “!A B m:A->B.isInj(m) ==>
  !X f:X->A g:X->A. isFun(f) & isFun(g) & m o f = m o g ==> f = g”)

local
val lemma =
fVar_Inst [("P",([("a",mem_sort (mk_set "A"))],“Eval(f:A->X,a) = Eval(g:A->X,a)”))] (Thm_2_4|> qspecl [‘A’]) |> gen_all
val lemma1 = 
fVar_Inst [("P",([("a0",mem_sort (mk_set "X")),("a0'",mem_sort (mk_set "E"))],“Eval(e:E->A,a0') = Eval(x:X->A,a0)”))] (AX1|> qspecl [‘X’,‘E’])
|> uex_expand
in
val Thm_2_9_Eqlz = proved_th $
e0
(rpt strip_tac >> rw[SetEz_def] >>
 qspecl_then [‘A’,‘B’,‘f’,‘g’]
  (x_choosel_then ["E","e"] strip_assume_tac) lemma >>
 qexistsl_tac [‘E’,‘e’] >> arw[] >> 
 drule Inj_Fun >> arw[] >> rpt strip_tac >>
 rw[uex_def “?!x0:X->E. isFun(x0) & x = e o x0”] >>
 strip_assume_tac lemma1 >>
 qexists_tac ‘R’ >> 
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> rpt strip_tac >--
  (fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
  last_x_assum $ assume_tac o iffLR >>
  first_x_assum irule >> 
  qsuff_tac ‘Eval(f,Eval(x,a)) = Eval(f o x,a) & 
             Eval(g,Eval(x,a)) = Eval(g o x,a)’
  >-- (strip_tac >> fs[]) >>
  strip_tac (* 2 *) >> irule o_Eval >> arw[]) >>
  fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 arw[] >> 
 qby_tac ‘x = e o R’ >--
 (drule Eval_def >> fs[] >>
  qby_tac ‘isFun(e o R)’ >-- (irule Thm_2_7_o_Fun >> arw[]) >>
  irule (iffRL FUN_EXT) >>
  arw[] >> strip_tac >>
  qby_tac ‘Eval(e o R,a) = Eval(e,Eval(R,a))’
  >-- (irule $ GSYM o_Eval >> arw[]) >>
  arw[] >> last_x_assum (qspecl_then [‘a’,‘Eval(R,a)’] assume_tac) >>
  fs[]) >> arw[] >>
 rpt strip_tac >> irule Inj_lcancel >> arw[] >>
 qexistsl_tac [‘A’,‘e’] >> arw[])
(form_goal
“!A B f:A->B g:A->B.isFun(f) & isFun(g) ==> ?E e:E->A.SetEz(f,g,e)”)
end

(*

Theorem 2.10. For any function f:A→B we have f=me, where m:im(f)↪B is an injection and e:A↠im(f) is a surjection. A set im(f) equipped with such m and e is unique up to bijection and is called the image of f.

Proof. Let im(f) be |S| where S is defined by y∈S iff there exists an x∈A with f(x)=y. By definition, we have an injection m:im(f)↪B. And for any x∈A, clearly f(x)∈S, so there is a unique y∈im(f) with m(y)=f(x); we define e(x)=y. It is easy to verify the rest.  ▮

*)

local
val lemma =
fVar_Inst [("P",([("b",mem_sort (mk_set "B"))],“?a:mem(A).Eval(f:A->B,a) = b”))] (Thm_2_4|> qspecl [‘B’]) 
val lemma1 = 
fVar_Inst [("P",([("x",mem_sort (mk_set "A")),("y",mem_sort (mk_set "s"))],“Eval(f:A->B,x) = Eval(m:s->B,y)”))] (AX1|> qspecl [‘A’,‘s’]) |> uex_expand
in
val Thm_2_10 = proved_th $
e0
(rpt strip_tac >> 
 x_choosel_then ["s","m"] strip_assume_tac lemma >>
 x_choose_then "e" strip_assume_tac lemma1 >>
 qexistsl_tac [‘s’,‘e’,‘m’] >> 
 arw[] >>
 qby_tac ‘isFun(e)’ >--
 (rw[Fun_expand] >> arw[] >> rpt strip_tac (* 2 *)
  >-- (last_x_assum $ irule o iffLR >> qexists_tac ‘a’ >> rw[]) >>
  fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 qby_tac ‘isSurj(e)’ >--
 (arw[Surj_def] >> strip_tac >> drule Eval_def >> fs[] >> 
  fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
  arw[] >> qexists_tac ‘y’ >> rw[]) >> arw[] >>
 qby_tac ‘isFun(m o e)’ >-- (irule Thm_2_7_o_Fun >> arw[] >>
 fs[Inj_def]) >>
 irule $ iffRL FUN_EXT >> arw[] >> strip_tac >>
 qpick_x_assum ‘isFun(e)’ assume_tac >> drule Eval_def >> fs[] >>
 last_x_assum (qspecl_then [‘a’,‘Eval(e,a)’] assume_tac) >> fs[] >>
 irule o_Eval >> arw[] >> fs[Inj_def])
(form_goal
“!A B f:A->B. isFun(f) ==> ?M e:A->M m:M->B. f = m o e & isSurj(e) & isInj(m)”)
end

(*TODO: 2.10 unique upto bijection*)


(*2.11 left to tomorrow...*)

(*
Axiom 3 (power sets): For any set A, there exists a set PA and a relation ϵ:A↬PA such that for any subset S of A, there exists a unique s∈PA with the property that for any x∈A, we have x∈S iff ϵ(x,s).
*)

(*val _ = new_fun "Pow" (set_sort,[("A",set_sort)]) *)

val AX3 = new_ax 
“!A. ?PA e:A->PA. !S0:1->A.?!s:mem(PA). !x:mem(A). Holds(S0,dot,x) <=> 
 Holds(e,x,s)”

(*
Theorem 2.12. For any relation R:B↬A, there exists a unique function fR:B→PA such that R(y,x) if and only if ϵ(x,fR(y)). It follows that Set is a topos (and Rel is a power allegory).
*)

val Pow_def = 
    AX3 |> spec_all |> eqT_intro 
        |> iffRL |> ex2fsym "Pow" ["A"] 
        |> C mp (trueI []) |> gen_all


val In_def = 
    Pow_def |> spec_all |> eqT_intro 
            |> iffRL |> ex2fsym "In" ["A"] 
            |> C mp (trueI []) |> gen_all


(*filter cont correct?*)

(*want subset notation, give a ref to tokenizer?*)

(*base change*)

(*
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


here is the commenting out thm 11
*)
(*
Theorem 2.12. For any relation R:B↬A, there exists a unique function fR:B→PA such that R(y,x) if and only if ϵ(x,fR(y)). It follows that Set is a topos (and Rel is a power allegory).
Proof. We simply define fR elementwise; for each y we define fR(y) to be the unique element of PA such that ϵ(x,fR(y)) holds iff R(y,x) holds. Extensionality of functions implies that it is unique.  ▮
*)

fun Pow A = mk_fun "Pow" [A]

val uex_tac:tactic = fn (ct,asl,w) =>
    let val th = uex_def w
        val w' = snd $ dest_dimp $ concl th
    in ([(ct,asl,w')],(sing (dimp_mp_r2l th)))
    end


local 
val lemma = 
fVar_Inst 
[("P",([("star",mem_sort ONE),("a",mem_sort (mk_set "A"))],
“(?a0. a = Eval(s0:A0->A,a0))”))]
(AX1|> qspecl [‘1’,‘A’]) 
|> uex_expand 
in
(*todo: both once_depth_fconv and basic_once_fconv cannot turn the a into dot*)
val In_def_Inj = proved_th $
e0
(rpt strip_tac >> assume_tac In_def >>
 strip_assume_tac lemma >>
 first_x_assum (qspecl_then [‘A’,‘R’] $ strip_assume_tac o uex_expand) >>
 uex_tac >>
 qexists_tac ‘s’ >> 
 qpick_x_assum ‘!a b. Holds(R,a,b) <=> ?a0.b = Eval(s0,a0)’
 (mp_tac o GSYM) >> once_rw[dot_def] >> strip_tac >>
 first_x_assum (qspecl_then [‘dot’] assume_tac) >> arw[] >>
 rev_full_simp_tac[] >> rpt strip_tac >> rw[]
 )
(form_goal
“!A A0 s0:A0->A.isInj(s0) ==>
 ?!s:mem(Pow(A)).!x:mem(A). (?a0.x = Eval(s0,a0)) <=> Holds(In(A),x,s)”)
end

(*In_def_P currently have to be like this because if there is P(a)in the assumption then every arw causes mess, extremely ugly, need to fix this*)
local
val lemma = 
fVar_Inst 
[("P",([("a",mem_sort (mk_set "A"))],
“(?a0. a = Eval(s0:A0->A,a0))”))]
(Thm_2_4 |> qspecl [‘A’]) 
in
val In_def_P = proved_th $
e0
(strip_tac >> uex_tac >> 
 strip_assume_tac $ spec_all Thm_2_4 >>
 drule In_def_Inj >> pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘s’ >> strip_tac (* 2 *)>--
 (strip_tac >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 accept_tac
 (iff_trans (assume “P(a:mem(A)) <=> ?b:mem(B).a = Eval(i:B->A,b)”)
            (assume “(?a0.a = Eval(i:B->A,a0)) <=> Holds(In(A),a,s)”))) >>
 rpt strip_tac >> first_x_assum irule >>
 strip_tac >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 last_x_assum (qspecl_then [‘x’] assume_tac) >>
 accept_tac
 (iff_trans 
  (GSYM $ assume “P(x) <=> ?b.x = Eval(i:B->A,b)”)
  (assume “P(x:mem(A)) <=> Holds(In(A),x,s')”)))
(form_goal
 “!A.?!s:mem(Pow(A)).!a.P(a) <=> Holds(In(A),a,s)”)
end

local
val lemma = 
fVar_Inst 
[("P",([("a",mem_sort (mk_set "A"))],
“Holds(In(A),a,s1)”))]
(In_def_P|> qspecl [‘A’]) |> uex_expand
in
val In_EXT = proved_th $
e0
(rpt strip_tac >> strip_assume_tac lemma >>
 qsuff_tac ‘s1 = s & s2 = s’ >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> rpt strip_tac (*2  *)
 >-- rw[] >> pop_assum (K all_tac) >> arw[])
(form_goal
 “!A s1:mem(Pow(A)) s2. (!x.Holds(In(A),x,s1) <=> Holds(In(A),x,s2)) ==>
 s1 = s2”)
end

local
val lemma = 
fVar_Inst 
[("P",([("y",mem_sort (mk_set "B")),("s",mem_sort (Pow (mk_set "A")))],
“!x.Holds(In(A),x,s) <=> Holds(R:B->A,y,x)”))]
(AX1|> qspecl [‘B’,‘Pow(A)’]) |> uex_expand
val lemma1 = 
fVar_Inst 
[("P",([("x",mem_sort (mk_set "A"))],
“Holds(R:B->A,a,x)”))]
(In_def_P|> qspecl [‘A’]) |> uex_expand
in
val Thm_2_12 = proved_th $
e0
(rpt strip_tac >>
 x_choose_then "fR" strip_assume_tac lemma >>
 uex_tac >> qexists_tac ‘fR’ >>
 qby_tac ‘isFun(fR)’ >-- 
 (arw[Fun_expand] >> rpt strip_tac (* 2 *) >--
  (strip_assume_tac lemma1 >> qexists_tac ‘s’ >> arw[] >>
   strip_tac >> rw[]) >>
  strip_assume_tac lemma1 >> 
  qsuff_tac ‘b1 = s & b2 = s’ >-- (strip_tac >> arw[]) >>
  strip_tac >> first_x_assum irule >> arw[] >> strip_tac >> rw[]) >>
 arw[] >>
 qby_tac
 ‘!y x.Holds(R,y,x) <=> Holds(In(A),x,Eval(fR,y))’ >--
 (drule Eval_def >> fs[] >> rpt strip_tac >>
 last_x_assum (qspecl_then [‘y’,‘Eval(fR,y)’] assume_tac) >>
 fs[]) >> arw[] >> (* TODO, should not need strip_tac, should directly have one conj remaining*) rpt strip_tac >> rw[] >>
 first_x_assum irule >> rpt strip_tac >>
 drule Eval_def >> arw[] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- arw[] >> irule In_EXT >> arw[] >> rpt strip_tac >> rw[])
(form_goal
“!B A R:B->A.?!fR:B->Pow(A).isFun(fR) & !y x.(Holds(R,y,x) <=> Holds(In(A),x,Eval(fR,y)))”)
end


local
val lemma =
(fVar_Inst [("P",([("star",mem_sort ONE),("x",mem_sort (mk_set "A"))],“x = a:mem(A)”))] (AX1 |> qspecl [‘1’,‘A’])) |> uex_expand
in
val Thm_2_3_5_el = proved_th $
e0
(rpt strip_tac >> uex_tac >>
 strip_assume_tac lemma >> qexists_tac ‘R’ >>
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> once_rw[dot_def] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘a’ >> rw[]) >-- arw[]) >>
 arw[] >>
 qby_tac ‘Eval(R,dot) = a’ >--
 (drule Eval_def >> fs[] >>
  last_x_assum (qspecl_then [‘dot’,‘a’] assume_tac) >> fs[]) >>
 arw[] >>
 rpt strip_tac >> first_x_assum irule >>
 rpt strip_tac >> once_rw[dot_def] >> 
 drule Eval_def >> fs[])
(form_goal
 “!A a:mem(A). ?!R:1->A. isFun(R) & Eval(R,dot) = a”)
end

(*mem as fun*)
val MF_def =
let val f = concl $ spec_all Thm_2_3_5_el
    val uth = uex_def f
    val th = dimp_mp_l2r (spec_all Thm_2_3_5_el) uth
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

(*
Theorem 2.13. For any two sets A and B, there exists a set BA and a function ev:BA×A→B such that for any function f:A→B there exists a unique element sf∈BA such that ev(sf,a)=f(a) for all a∈A. It follows that Set is a cartesian closed category.

Proof. We take BA to be a tabulation of the subset of P(A×B) containing only the functions. More precisely, define F⊆P(A×B) such that s∈F iff for every x∈A, there exists a unique y∈B such that ϵ((x,y),s), and let BA=|F|.  ▮
*)

val Pair_ex = pi2_def |> spec_all |> conjE2 |> conjE2 
                      |> conjE1 |> spec_all
val Pair_def = 
    Pair_ex |> spec_all |> eqT_intro 
            |> iffRL |> ex2fsym "Pair" ["x","y"] 
            |> C mp (trueI []) |> gen_all

(*
val Pow_R = proved_th $
e0
()
(form_goal
 “!A B R:A->B. ?!r:mem(Pow(A * B)).
  !x:mem(A * B).”)
*)

val Pair_pi12 = proved_th $
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] strip_assume_tac pi2_def >>
 first_x_assum irule >> rw[Pair_def])
(form_goal
 “!A B ab:mem(A * B). Pair(Eval(pi1(A,B),ab),Eval(pi2(A,B),ab)) = ab”)

(*
fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
“!x:mem(A).?!y:mem(B).Holds(In(A * B),Pair(x,y),s)”))]
(AX1|> qspecl [‘A’,‘B’]) |> uex_expand

therefore not ?R. R(a,b) <=> !P.P(a,b)
*)

local 
val lemma = 
fVar_Inst 
[("P",([("s",mem_sort (Pow (Cross (mk_set "A") (mk_set "B"))))],
“!x:mem(A).?!y:mem(B).Holds(In(A * B),Pair(x,y),s)”))]
(Thm_2_4 |> qspecl [‘Pow(A * B)’])
val lemma1 = 
fVar_Inst 
[("P",([("fa",mem_sort (Cross (mk_set "A2B") (mk_set "A"))),
        ("b",mem_sort (mk_set "B"))],
“Holds(In(A * B),Pair(Eval(pi2(A2B,A),fa),b),Eval(i,Eval(pi1(A2B,A),fa)))”))]
(AX1 |> qspecl [‘A2B * A’,‘B’]) |> uex_expand
val lemma2 = 
fVar_Inst 
[("P",([("ab",mem_sort (Cross (mk_set "A") (mk_set "B")))],
“Holds(f:A->B,Eval(pi1(A,B),ab),Eval(pi2(A,B),ab))”))]
(In_def_P |> qspecl [‘A * B’]) |> uex_expand
in
val Thm_2_13 = proved_th $
e0
(rpt strip_tac >> 
 x_choosel_then ["A2B","i"] strip_assume_tac lemma >>
 x_choose_then "ev" strip_assume_tac lemma1 >> 
 qexistsl_tac [‘A2B’,‘ev’] >> 
 qby_tac ‘isFun(ev)’ >--
 (rw[Fun_expand] >> arw[] >> rpt strip_tac (* 2 *) >--
  (first_x_assum 
    (qspecl_then [‘Eval(i, Eval(pi1(A2B, A), a))’] assume_tac) >>
   qby_tac ‘?b:mem(A2B).Eval(i,Eval(pi1(A2B,A),a)) = Eval(i,b)’ >--
    (qexists_tac ‘Eval(pi1(A2B, A), a)’ >> rw[]) >>
   fs[] >> pop_assum (assume_tac o GSYM) >> arw[] >>
   pop_assum (K all_tac) >> 
   first_x_assum 
    (qspecl_then [‘Eval(pi2(A2B, A), a)’]  
     (strip_assume_tac o uex_expand)) >>
   qexists_tac ‘y’ >> arw[]) >>
  first_x_assum 
    (qspecl_then [‘Eval(i, Eval(pi1(A2B, A), a))’] assume_tac) >>
   qby_tac ‘?b:mem(A2B).Eval(i,Eval(pi1(A2B,A),a)) = Eval(i,b)’ >--
    (qexists_tac ‘Eval(pi1(A2B, A), a)’ >> rw[]) >>
   fs[] >> pop_assum (assume_tac o GSYM) >> arw[] >>
   pop_assum (K all_tac) >> 
   first_x_assum 
    (qspecl_then [‘Eval(pi2(A2B, A), a)’]  
     (strip_assume_tac o uex_expand)) >>
  qsuff_tac ‘b1 = y & b2 = y’ >-- (strip_tac >> arw[]) >>
  strip_tac (* 2 *) >> first_x_assum irule >> arw[]) >> arw[] >>
 (*the 2 conds of fun above has repeated proof*)
 rpt strip_tac >> uex_tac >> 
 x_choose_then "grf" strip_assume_tac $ GSYM lemma2 >>
 last_assum (qspecl_then [‘grf’] assume_tac) >>
 qby_tac ‘!x.?!y.Holds(In(A * B),Pair(x,y),grf)’ >--
 (strip_tac >> uex_tac >> arw[] >> rw[Pair_def] >>
  qpick_x_assum ‘isFun(f)’ assume_tac >>
 (*should diectly from def of fun, just because 2 vers of def of uex*)
  drule $ iffLR Fun_expand >> pop_assum strip_assume_tac >> 
  last_x_assum (qspecl_then [‘x’] strip_assume_tac) >> 
  qexists_tac ‘b’ >> arw[] >> rpt strip_tac >> first_x_assum irule >>
  qexists_tac ‘x’ >> arw[]) >>
 (*TODO: if use fs here, will give !x.T instead of T, that is because quantifiers has no chance to be seen by rw, but is discarded by rw canon*)
  qby_tac ‘?b : mem(A2B). grf = Eval(i, b)’ >--
  (pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >> 
   once_arw[] >> first_x_assum (accept_tac o iffLR)) >>
  pop_assum (x_choose_then "fbar" assume_tac) >>
  qexists_tac ‘fbar’ >> 
  qpick_x_assum ‘isFun(ev)’ assume_tac >> drule Eval_def >>
  fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
  fs[Pair_def] >> rpt strip_tac (* 2 *) >--
  (rev_drule Holds_Eval >> arw[]) >>
  fs[Inj_def] >> first_x_assum irule >> first_x_assum irule >>
  strip_tac >> 
  first_x_assum (qspecl_then [‘Eval(i,sf')’] assume_tac) >>
  (*?(b : mem(A2B)). Eval(i, sf') = Eval(i, b#) should automatically become true , happens twice in this proof, todo, stupid*)
  qby_tac ‘?b.Eval(i,sf') = Eval(i,b)’ >--
  (qexists_tac ‘sf'’ >> rw[]) >> fs[] >>
  pop_assum (assume_tac o GSYM) >> arw[] >>
  pop_assum (K all_tac) >>
  qpick_x_assum ‘isFun(f)’ assume_tac >> drule Eval_def >> fs[] >>
  dimp_tac >> strip_tac (* 2 *) >--
  (*a:A * B \in i(sf') <=> pi2(a) = Eval(f,pi1(a))
    if a in i(sf'), then want pi2(a) = Eval(f,pi1(a))
    from assumtpion 10, (pi1(a),f(pi1(a))) \in i(sf)
known that a = (pi1(a),pi2(a)), sufficitnet to show f(pi1(a)) = pi2(a), but by assumption 11, !a?!b. (a,b)\in i(sf')
*)
  (qpick_x_assum ‘!x:mem(A).?!y:mem(B).Holds(In(A * B),Pair(x,y),Eval(i,sf'))’ assume_tac >> 
   first_x_assum (qspecl_then [‘Eval(pi1(A,B),a)’] $
     strip_assume_tac o uex_expand) >>
   qsuff_tac ‘Eval(pi2(A, B), a) = y & 
              Eval(f, Eval(pi1(A, B), a)) = y’ >--
   (strip_tac >> arw[]) >>
   strip_tac >> first_x_assum irule  (* 2 *)
   >-- arw[Pair_pi12] >>
   (*qpick_x_assum ‘!a.Holds(In(A* B),Pair(a,Eval(f,a)),Eval(i,sf'))’
     assume_tac
     Exception- UNIFY ("terms cannot be unified", [])
    do not know why... *)
   pick_x_assum  “!a.Holds(In(A* B),Pair(a,Eval(f,a)),Eval(i:A2B->Pow(A * B),sf':mem(A2B)))” assume_tac >>
   first_x_assum (qspecl_then [‘Eval(pi1(A,B),a)’] assume_tac) >>
   arw[]) >> 
  once_rw[GSYM Pair_pi12] >> once_arw[] >>
  pick_x_assum  “!a.Holds(In(A* B),Pair(a,Eval(f,a)),Eval(i:A2B->Pow(A * B),sf':mem(A2B)))” assume_tac >>
   first_x_assum (qspecl_then [‘Eval(pi1(A,B),a)’] assume_tac) >>
   arw[])
(form_goal
“!A B.?A2B ev:A2B * A ->B. isFun(ev) & 
 !f:A->B.isFun(f) ==> ?!sf:mem(A2B).!a:mem(A).Eval(ev,Pair(sf,a)) = Eval(f,a)”)
end


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


val Sym_Trans_Rright = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >--
 (qby_tac ‘Holds(R,y,x)’ >-- 
  (fs[Sym_def] >> first_x_assum rev_drule >> arw[]) >>
  fs[Trans_def] >> first_x_assum irule >>
  qexists_tac ‘x’ >> arw[]) >>
 fs[Trans_def] >> first_x_assum irule >>
 qexists_tac ‘y’ >> arw[])
(form_goal
 “!A R:A->A.Sym(R) & Trans(R)==> !x y. Holds(R,x,y) ==>
  (!z.Holds(R,x,z) <=> Holds(R,y,z))”)


(*

Theorem 2.14. If R is an equivalence relation on A, then there is a surjective function q:A↠B such that R(x,y) holds iff q(x)=q(y).

Proof. R induces a function fR:A→PA as above; let B be im(fR) and q the surjective part of the image factorization. If R(x,y) holds, then by symmetry and transitivity, R(x,z)⇔R(y,z) for all z; hence fR(x)=fR(y) and so q(x)=q(y). Conversely, if q(x)=q(y), then fR(x)=fR(y); but y∈fR(y) by reflexivity, hence y∈fR(x) and thus R(x,y) holds.  ▮

*)

(*TODO: spec_tac*)
val Thm_2_14 = proved_th $
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘A’,‘R’] (strip_assume_tac o uex_expand) Thm_2_12 >>
 drule Thm_2_10 >> pop_assum strip_assume_tac >>
 qexistsl_tac [‘M’,‘e’] >> strip_tac >-- arw[] >>
 rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >--
 (qsuff_tac ‘Eval(fR,x) = Eval(fR,y)’ >--
  (arw[] >> fs[Inj_def] >> strip_tac >> first_x_assum irule >>
   qby_tac ‘Eval(m, Eval(e, x)) = Eval(m o e, x) &
            Eval(m, Eval(e, y)) = Eval(m o e, y)’ >--
   (strip_tac >> irule o_Eval >> fs[Surj_def]) >>
   fs[]) >>
  irule In_EXT >> strip_tac >> 
  first_assum (qspecl_then [‘y’,‘x'’] (assume_tac o GSYM)) >>
  first_x_assum (qspecl_then [‘x’,‘x'’] (assume_tac o GSYM)) >>
  arw[] >> 
  qby_tac ‘Sym(R) & Trans(R)’ >-- fs[ER_def] >>
  drule Sym_Trans_Rright >> first_x_assum drule >> arw[]) >>
  arw[] >> 
  qsuff_tac ‘Holds(In(A),y,Eval(fR,y)) & Eval(fR,y) = Eval(fR,x)’ >--
  (strip_tac >> rev_full_simp_tac[] >> fs[]) >>
  strip_tac (* 2 *) >--
  (first_x_assum (irule o iffLR) >> fs[ER_def,Refl_def]) >>
  arw[] >> 
  qby_tac ‘isFun(e) & isFun(m)’ >-- fs[Inj_def,Surj_def] >>
  drule (o_Eval |> strip_all_and_imp |> gen_all |> disch_all |> gen_all
         |> GSYM) >>
  arw[])
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
