
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

val AX0 = new_ax “?A a:element(A).T”

fun dest_mem_sort s = 
    let val (sn,tl) = dest_sort s
    in if sn = "mem" then hd tl else raise ERR ("dest_mem_sort.input sort is not a mem sort",[s],[],[])
    end

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

“Holds(R:rel(A,B),x:mem(A),y:mem(B)) & a:mem(A) = a”


(*how to implement
Axiom 1 (Relational comprehension): For any two sets A and B, and any property P that can obtain of an element of A and an element of B, there exists a unique relation φ:A↬B such that φ(x,y) if and only if P obtains of x and y.
*)
