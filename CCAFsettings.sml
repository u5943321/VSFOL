
val isPr_def = qdefine_psym("isPr",[‘p1:AB->A’,‘p2:AB->B’])
‘!X f:X->A g:X->B.?!fg:X->AB. p1 o fg = f & p2 o fg = g’
|> gen_all



val _ = new_fun "*" (cat_sort,[("A",cat_sort),("B",cat_sort)])
val _ = new_fun "p1" (fun_sort (rastt "A * B") (rastt "A"),[("A",cat_sort),("B",cat_sort)])

val _ = new_fun "p2" (fun_sort (rastt "A * B") (rastt "B"),[("A",cat_sort),("B",cat_sort)])

val Po_def = store_ax("Po_def",
“!A B. isPr(p1(A,B),p2(A,B))”);
val p1_def = Po_def;
val p2_def = Po_def;

val Pa_def0 = p2_def |> rewr_rule[isPr_def] |> spec_all
                    |> qsimple_uex_spec "Pa" [‘f’,‘g’]
                    |> gen_all


val Pa_def = prove_store("Pa_def",
e0
(rpt gen_tac >>
 qsspecl_then [‘f’,‘g’] assume_tac Pa_def0 >> arw[] >>
 qspecl_then [‘A’,‘B’] assume_tac p2_def >>
 fs[isPr_def] >>
 first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qsuff_tac ‘Pa(f,g)= fg’ >-- (strip_tac >> arw[]) >>
 first_x_assum irule >> arw[])
(form_goal
 “∀A B X f:X->A g:X->B.
 (p1(A, B) o Pa(f, g) = f & p2(A, B) o Pa(f, g) = g) &
 !fg' : X -> A * B.
 p1(A, B) o fg' = f & p2(A, B) o fg' = g ==>
 fg' = Pa(f, g)”));


val _ = add_parse 0x1D7D8

val _ = add_parse 120793


val isEq_def = qdefine_psym("isEq",
[‘f:A->B’,‘g:A->B’,‘e:E->A’])
‘isEq(f,g,e) <=> 
      f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0’
|> gen_all

val isEq_ex = store_ax("isEq_ex",“!A B f:A->B g:A->B.?E e:E->A.isEq(f,g,e)”);


val is0_def = 
    qdefine_psym("is0",[‘ZERO’])
                ‘!X.?!f:ZERO ->X. T’ |> gen_all

val _ = new_fun "0" (cat_sort,[]);
val ZERO_def = store_ax("ZERO_def",“is0(0)”);



val ZERO_def = store_ax("ZERO_def",“is0(0)”);


val ZERO_prop = ZERO_def |> rewr_rule [is0_def]
                       |> store_as "ZERO_prop"

val ZERO_prop' = proved_th $
e0
(rw[ZERO_prop])
(form_goal “?!f:0->X.f = f”)

val From0_def0 = 
    ZERO_prop' |> spec_all 
               |> qsimple_uex_spec "From0" [‘X’] |> gen_all


val From0_def = proved_th $
e0
(rpt strip_tac >>
 (strip_assume_tac o uex_expand) ZERO_prop' >>
 qsuff_tac
 ‘f' = f & From0(X) = f’
 >-- (strip_tac >> arw[]) >>
 rpt strip_tac >> first_x_assum irule >> rw[])
(form_goal “∀X f':0->X. f' = From0(X)”)




val isEq_def = qdefine_psym("isEq",[‘f:A->B’,‘g:A->B’,‘e:E->A’])
‘f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0’
|> qgenl [‘A’,‘B’,‘f’,‘g’,‘E’,‘e’] 
|> store_as "isEq_def";


val isEq_ex = store_ax("isEq_ex",“!A B f:A->B g:A->B.?E e:E->A.isEq(f,g,e)”);


val iscoEq_def = qdefine_psym("iscoEq",[‘f:A->B’,‘g:A->B’,‘ce:B->cE’])
‘ce o f = ce o g & 
      !X x:B->X. x o f = x o g ==>
      ?!x0:cE->X. x = x0 o ce’
|> qgenl [‘A’,‘B’,‘f’,‘g’,‘cE’,‘ce’]
|> store_as "iscoEq_def";

val iscoEq_ex = store_ax("iscoEq_ex",“!A B f:A->B g:A->B.?cE ce:B->cE.iscoEq(f,g,ce)”);

val is1_def = qdefine_psym("is1",[‘ONE’])
‘!X.?!f:X->ONE.T’ |> gen_all |> store_as "is1_def";

val _ = new_fun "1" (cat_sort,[])                     

val ONE_def = store_ax("ONE_def",“is1(1)”);


val ONE_prop = ONE_def |> rewr_rule [is1_def]
                       |> store_as "ONE_prop";

val ONE_prop' = proved_th $
e0
(rw[ONE_prop])
(form_goal “?!f:X->1.f = f”)

val To1_def0 = ONE_prop' |> spec_all |> qsimple_uex_spec "To1" [‘X’]

val To1_def = prove_store("To1_def",
e0
(rpt strip_tac >>
 (strip_assume_tac o uex_expand) ONE_prop' >>
 qsuff_tac
 ‘f' = f & To1(X) = f’
 >-- (strip_tac >> arw[]) >>
 rpt strip_tac >> first_x_assum irule >> rw[])
(form_goal “∀X f':X->1. f' = To1(X)”));



val _ = new_fun "Id" 
       (mk_sort "fun" [mk_var("A",mk_sort "cat" []),mk_var("A",mk_sort "cat" [])],
        [("A",mk_sort "cat" [])])



val IdL = store_ax("IdL", “!B A f:B->A. Id(A) o f = f”);

val IdR = store_ax("IdR",“!A B f:A->B. f o Id(A) = f”);

val o_assoc = store_ax("o_assoc",“!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f”);


val _ = new_pred "Iso" [("f",fun_sort (mk_cat "A") (mk_cat "B"))]

val Iso_def = store_ax("Iso_def",
“!A B f:A->B. Iso(f) <=> ?f':B->A. f' o f = Id(A) & f o f' = Id(B)”);


val areIso_def = store_ax("areIso_def",
“!A B. areIso(A,B) <=> ?f:A->B g:B->A. f o g = Id(B) & g o f = Id(A)”)

val ZERO_not_ONE = store_ax("ZERO_not_ONE",
“~(?f:0->1. Iso(f))”)


val _ = new_fun "2" (cat_sort,[])

val _ = new_fun "0f" (fun_sort (rastt "1") (rastt "2"),[])

val _ = new_fun "1f" (fun_sort (rastt "1") (rastt "2"),[])


val isExp_def = qdefine_psym("isExp",[‘ev:A * A2B ->B’])
‘!X f:A * X->B. ?!h:X->A2B. ev o Pa(p1(A,X), h o p2(A,X)) = f’

val _ = new_fun "Exp" (cat_sort,[("A",cat_sort),("B",cat_sort)])

val _ = new_fun "Ev" (fun_sort (rastt "A * Exp(A,B)") (rastt "B"),[("A",cat_sort),("B",cat_sort)])



val Ev_def0 = store_ax("Ev_def0",“!A B. isExp(Ev(A,B))”);

val Ev_def = Ev_def0 |> rewr_rule[isExp_def]

val Tp_def0 = Ev_def |> spec_all 
                     |> qsimple_uex_spec "Tp" [‘f’] 

val Tp_def = proved_th $
e0
(rw[Tp_def0] >> rpt gen_tac >>
 qsspecl_then [‘f’] (strip_assume_tac o uex_expand) Ev_def >>
 qsuff_tac
 ‘Tp(f) = h’
 >-- (strip_tac >> arw[]) >>
 first_x_assum irule >> rw[Tp_def0])
(form_goal
 “∀A B X f:A * X -> B.
 Ev(A, B) o Pa(p1(A, X), Tp(f) o p2(A, X)) = f &
 !h':X -> Exp(A,B).
          Ev(A, B) o Pa(p1(A, X), h' o p2(A, X)) = f ==> h' = Tp(f)”)

val isPb_def =
qdefine_psym("isPb",[‘f:X->H’,‘g:Y->H’,‘p: P ->X’,‘q: P -> Y’])
‘f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v’
|> qgenl [‘X’,‘H’,‘f:X->H’,‘Y’,‘g:Y->H’,‘P’,‘p:P ->X’,‘q: P ->Y’]


val isPb_ex = store_ax("isPb_ex",“!X H f:X->H Y g:Y->H. ?P p:P->X q. isPb(f,g,p,q)”);
