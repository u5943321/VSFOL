val _ = new_sort "ob" [] 
val _ = new_sort "ar" [("A",mk_sort "ob" []),("B",mk_sort "ob" [])]

val ob_sort = mk_sort "ob" [];
fun ar_sort A B = mk_sort "ar" [A,B];

val _ = new_fun "1" (mk_sort "ob" [],[]);
val ONE = mk_fun "1" [];
val _ = new_fun "To1" (mk_sort "ar" [mk_var ("A",ob_sort),ONE],[("A",ob_sort)]);
val _ = new_fun "0" (mk_sort "ob" [],[]);
val ZERO = mk_fun "0" [];
val _ = new_fun "From0" (mk_sort "ar" [ZERO,mk_var ("A",ob_sort)],[("A",ob_sort)]);


val _ = new_fun "*" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun Po A B = mk_fun "*" [A,B];
val _ = new_fun "+" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun coPo A B = mk_fun "+" [A,B];
val _ = new_fun "Exp" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun Exp A B = mk_fun "Exp" [A,B];

fun mk_ob name = mk_var (name,ob_sort);
fun mk_ar name dom cod = mk_var (name,ar_sort dom cod);
val _ = new_fun "Pa" (ar_sort (mk_ob "X") (Po (mk_ob "A") (mk_ob "B")),
 [("f",ar_sort (mk_ob "X") (mk_ob "A")),("g",ar_sort (mk_ob "X") (mk_ob "B"))]);

val _ = new_fun "o" (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])],[("f",mk_sort "ar" [mk_var("B",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])]),("g",mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("B",mk_sort "ob" [])])])


val _ = new_fun "id" 
       (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("A",mk_sort "ob" [])],
        [("A",mk_sort "ob" [])])

val _ = new_sort_infix "ar" "->"

fun new_ax f = 
    let
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end


val idL = new_ax “!B A f:B->A. id(A) o f = f”

val idR = new_ax “!A B f:A->B. f o id(A) = f”

val o_assoc = new_ax “!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f”

val To1_def = new_ax “!X f:X->1. f = To1(X)”;

val From0_def = new_ax “!X f:0->X. f = From0(X)”;

val _ = new_fun "π₁" 
                (ar_sort (Po (mk_ob "A") (mk_ob "B")) 
                         (mk_ob "A"),
                 [("A",ob_sort),("B",ob_sort)])

val _ = new_fun "π₂" 
                (ar_sort (Po (mk_ob "A") (mk_ob "B")) 
                         (mk_ob "B"),
                 [("A",ob_sort),("B",ob_sort)])

val _ = new_fun "Pa" 
                (ar_sort (mk_ob "X") 
                         (Po (mk_ob "A") (mk_ob "B")),
                 [("f",ar_sort (mk_ob "X") (mk_ob "A")),
                  ("g",ar_sort (mk_ob "X") (mk_ob "B"))])

val Pa_def = new_ax “!A X f:X->A B g:X->B fg:X->A * B. (π₁(A,B) o fg = f & π₂(A,B) o fg = g) <=> fg = Pa(f,g)”


val _ = new_fun "τ₁" 
                (ar_sort (mk_ob "A") 
                         (coPo (mk_ob "A") (mk_ob "B")),
                 [("A",ob_sort),("B",ob_sort)])

val _ = new_fun "τ₂" 
                (ar_sort (mk_ob "B")
                         (coPo (mk_ob "A") (mk_ob "B")),
                 [("A",ob_sort),("B",ob_sort)])

val _ = new_fun "coPa" 
                (ar_sort (coPo (mk_ob "A") (mk_ob "B"))
                         (mk_ob "X") ,
                 [("f",ar_sort (mk_ob "A") (mk_ob "X")),
                  ("g",ar_sort (mk_ob "B") (mk_ob "X"))])

val coPa_def = new_ax “!A X f:A->X B g:B->X fg:A + B->X. (fg o τ₁(A,B) = f & fg o τ₂(A,B) = g) <=> fg = coPa(f,g)”;

val _ = new_fun "Eqa" 
                (ar_sort (coPo (mk_ob "A") (mk_ob "B"))
                         (mk_ob "X") ,
                 [("f",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("g",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("e",ar_sort (mk_ob "E") (mk_ob "A"))])


val Eqa_def = new_ax
“!A B f:A->B g:A->B.?E e:E->A. f o e = g o e & !X x:X->A. f o x = g o x ==> (!)”

val eqind_def = read_axiom "!A.!B.!f:A->B.!g:A->B.!E.!e:E->A.iseq(e,f,g)==> f o e = g o e & !X.!x:X->A.f o x = g o x ==> (!x0:X->E.e o x0 = x <=> x0 = eqind(e,f,g,x))"

val eq_ex = read_axiom "!A.!B.!f:A->B.!g:A->B.?E.?e:E->A.iseq(e,f,g)";

val ax1_5 = eq_ex

val coeqind_def = read_axiom "!A.!B.!f:A->B.!g:A->B.!cE.!ce:B->cE.iscoeq(ce,f,g)==> ce o f = ce o g & !X.!x:B->X. x o f = x o g ==> (!x0:cE->X.x0 o ce = x <=> x0 = coeqind(ce,f,g,x))"

val coeq_ex = read_axiom "!A.!B.!f:A->B.!g:A->B.?cE.?ce:B->cE.iscoeq(ce,f,g)"

val ax1_6 = coeq_ex

val tp_def = read_axiom "!A.!B.!A2B.!efs.!p1:efs ->A.!p2:efs ->A2B.!ev:efs->B.isexp(p1,p2,ev)==> ispr(p1,p2) & !X.!AX.!p1':AX->A.!p2':AX->X. ispr(p1',p2') ==> !f:AX->B.!h:X->A2B. ev o pa(p1,p2,p1',h o p2') = f <=> h = tp(p1,p2,ev,p1',p2',f)"

val exp_ex = read_axiom "!A.!B.?A2B efs p1:efs ->A p2:efs ->A2B ev:efs->B.isexp(p1,p2,ev)"

val ax2 = exp_ex

val Nind0_def = read_axiom "!N0 one z0:one -> N0 s0:N0->N0. isN0(z0,s0) ==> is1(one) & !X x0:one -> X t:X -> X x:N0 -> X. x o z0 = x0 & x o s0 = t o x <=> x = Nind0(z0,s0,x0,t)";


val constN_def = read_axiom "!X x0:1->X t:X ->X x:N->X.(x o z = x0 & x o s = t o x) <=> x = Nind(x0,t)"

(*to be edited, switch the ordrr of s0 and z0*)
val ax3 = constN_def

val ax_wp = read_axiom "!A B f: A -> B g:A ->B.(~(f = g)) ==> ?a: 1 -> A. ~(f o a = g o a)";

val ax4 = ax_wp


val ismono_def = read_axiom "!A B f: A -> B. ismono(f) <=> !X g:X -> A h. f o g = f o h ==> h = g"

val ax_el = read_axiom "!X.(~is0(X)) ==> ?x:1->X.T";

val ax6 = ax_el

val ac = read_axiom "!A one a: one -> A B f: A -> B. is1(one) ==> ?g : B -> A. f o g o f = f"

val ax5 = ac

val ismem_def = read_axiom "!A x:1-> A A0 a:A0 -> A. ismem(x,a) <=> ismono(a) & ?x0:1 -> A0. a o x0 = x";

new_pred "ismem0" ([("x",mk_ar_sort (mk_ob "one") (mk_ob "A")),("a",mk_ar_sort (mk_ob "A0") (mk_ob "A"))]);

val ismem0_def = read_axiom "!A one x:one-> A A0 a:A0 -> A. ismem0(x,a) <=> is1(one) & ismono(a) & ?x0:one -> A0. a o x0 = x";

val ax_incfac0 = read_axiom "!A B AB i1:A->AB i2:B->AB one f:one -> AB. iscopr(i1,i2) & is1(one) ==> ismem0(f,i1)| ismem0(f,i2)";

val ax7 = ax_incfac0 

val ax_2el = read_axiom "?X x1: 1 -> X x2: 1 -> X. ~ (x1 = x2)"


val ax8 = ax_2el


val _ = new_fun "*" (mk_ar_sort (mk_ob "X") (mk_ob "two"),[("i1",mk_ar_sort one (mk_ob "two")),("i2",mk_ar_sort one (mk_ob "two")),("a",mk_ar_sort (mk_ob "A") (mk_ob "X"))])

val prsym_def = ex2fsym "*" ["A","B"] (iffRL $ eqT_intro $ spec_all pr_ex)
                        |> C mp (trueI []) |> gen_all

val p1_def = ex2fsym "p1" ["A","B"] (iffRL $ eqT_intro $ spec_all prsym_def)
                        |> C mp (trueI []) |> gen_all

val p2_def = ex2fsym "p2" ["A","B"] (iffRL $ eqT_intro $ spec_all p1_def)
                        |> C mp (trueI []) |> gen_all


val coprsym_def = ex2fsym "+" ["A","B"] (iffRL $ eqT_intro $ spec_all copr_ex)
                        |> C mp (trueI []) |> gen_all

val i1_def = ex2fsym "i1" ["A","B"] (iffRL $ eqT_intro $ spec_all prsym_def)
                        |> C mp (trueI []) |> gen_all

val i2_def = ex2fsym "i2" ["A","B"] (iffRL $ eqT_intro $ spec_all p1_def)
                        |> C mp (trueI []) |> gen_all

val expsym_def = ex2fsym "^" ["A","B"] (iffRL $ eqT_intro $ spec_all exp_ex)
                        |> C mp (trueI []) |> gen_all



fun po A B = mk_fun "*" [A,B]

val _ = new_fun "p1" (ar_sort (po (mk_ob "A") (mk_ob "B")) (mk_ob "A"),[("A",ob_sort),("B",ob_sort)])

val _ = new_fun "p2" (ar_sort (po (mk_ob "A") (mk_ob "B")) (mk_ob "B"),[("A",ob_sort),("B",ob_sort)])


val _ = new_fun "+" (ob_sort,[("A",ob_sort),("B",ob_sort)])

fun copo A B = mk_fun "+" [A,B]

val _ = new_fun "i1" (ar_sort (mk_ob "A") (copo (mk_ob "A") (mk_ob "B")),[("A",ob_sort),("B",ob_sort)])

val _ = new_fun "i2" (ar_sort (mk_ob "B") (copo (mk_ob "A") (mk_ob "B")),[("A",ob_sort),("B",ob_sort)])


val _ = new_fun "exp" (ob_sort,[("A",ob_sort),("B",ob_sort)])

fun exp A B = mk_fun "exp" [A,B]

val _ = new_fun "ev" (ar_sort (po (mk_ob "A") (exp (mk_ob "A") (mk_ob "B"))) (mk_ob "B"),[("A",ob_sort),("B",ob_sort)])




val prod_def = new_ax “!A B. ispr(p1(A,B),p2(A,B))” 

val exp_def = mk_ax 
“!A B.isexp(p1(A,exp(A,B)),p2(A,exp(A,B)),ev(A,B))”


rapf "!B A f:B ->A. id (A) o f = f";
rapf "!A B f: A -> B. f o id(A) = f";
rapf "!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f";





