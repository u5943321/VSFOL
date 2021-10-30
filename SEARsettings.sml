
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
(*
fun AX1 (f:form) (a,b) = 
    let val fvs = fvf f
        val (n1,s1) = dest_var a
        val aset = dest_mem_sort s1
        val (n2,s2) = dest_var b
        val bset = dest_mem_sort s2
        val _ = HOLset.member(fvs,(n1,s1)) orelse 
                raise ERR ("AX1.first variable not occurs in the input formula",[],[a],[f])
        val _ = HOLset.member(fvs,(n2,s2)) orelse 
                raise ERR ("AX1.second variable not occurs in the input formula",[],[b],[f])
        val rs = rel_sort aset bset
        val rvar = mk_var("R",rs)
        val holdspred = mk_pred "Holds" [rvar,a,b]
        val f0 = mk_dimp holdspred f
        val f1 = mk_exists "R" rs
                (mk_forall n1 s1 
                           (mk_forall n2 s2
                                     f0))
    in
        mk_thm(fvf f1,[],f1)
    end

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
val Fun_def = new_ax “!A B R:rel(A,B). isFun(R) <=> !x:mem(A). ?!y:mem(B). Holds(R,x,y)”

val _ = new_fun "Eval" (mem_sort (mk_set "B"),[("R",rel_sort (mk_set "A") (mk_set "B")),
                        ("x",mem_sort (mk_set "A"))])

val Eval_def = new_ax “!A B Fn:rel(A,B). isFun(Fn) ==>!x y. Holds(Fn,x,y) <=> y = Eval(Fn,x)”

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

Theorem 2.2. There exists a set ∅ which has no elements.

Proof. By Axiom 0, there exists a set A. By Axiom 1, there exists a relation φ:A↬A such that φ(x,y) holds never. Using Axiom 2, let ∅ be a tabulation of φ.  ▮


(*how can we just type the name once? for prove_store*)
(*rw you idiot gives me  ~(~a'' = a'' & b = b)*)

local
val lemma = AX1 “~(a:mem(A) = a) & b:mem(A) = b” (("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "A")))
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma) 
in
val Thm_2_2 = proved_th $ (*val (ct,_,_) = cg $*)
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

val Thm_2_3_5 = proved_th $
e0
()
(form_goal
 “!A.”)

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

Theorem 2.4. For any property P of elements of a set A, there exists a set B and an injective function i:B→A such that for a∈A, we have P(a) iff a=i(b) for some b∈B.

fun uex_ex f = 
    let val th0 = iffLR $ uex_def f |> undisch
        val c0 = concl th0
        val ((n,s),b) = dest_exists c0
        val th1 = assume b |> conjE1 
        val th2 = existsI (n,s) (mk_var(n,s)) (concl th1) th1
        val th3 = existsE (n,s) th0 th2
    in disch f th3
    end

val P = “a:mem(A) = b”
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


existsE l1' 
rewr_rule[Thm_2_4_R_ver] (dimp_mp_l2r l1 (uex_def $ concl l1))

(*
val ast1 =
   aInfix
    (aId "R", ":",
     aApp
      ("rel",
       [aInfix
         (aInfix (aId "A", ":", aApp ("set", [])), ":", aApp ("set", [])),
        aInfix
         (aInfix (aId "A", ":", aApp ("set", [])), ":", aApp ("set", []))])):
   ast


local
val lemma = AX1 “~(a:mem(A) = a)” (("a",mem_sort (mk_set "A")),("a",mem_sort (mk_set "A")))
in
val Thm_2_2 = proved_th $ val (ct,_,_) = cg $
e0
(strip_assume_tac AX0 >> strip_assume_tac lemma (* >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 *))
(form_goal
“?Empty. !a:mem(Empty).F”)
 parse_term_with_cont ct "R"
*)

“Holds(R:rel(A,B),x:mem(A),y:mem(B)) & a:mem(A) = a”


(*how to implement
Axiom 1 (Relational comprehension): For any two sets A and B, and any property P that can obtain of an element of A and an element of B, there exists a unique relation φ:A↬B such that φ(x,y) if and only if P obtains of x and y.
*)
