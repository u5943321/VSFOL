
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




val PCC1 = store_ax("PCC1",
“?p:0->1 q:0->1. isPb(0f,1f,p,q)”);



val imp_lemma = proved_th $
e0
(dimp_tac >> strip_tac (* 3 *)
 >-- (cases_on “A” >-- arw[] >> first_x_assum drule >>
      arw[]) >>
 arw[])
(form_goal
 “~ A ==> B <=> B | A”)

val CC2_2 = store_ax("CC2_2",
“!A B f:A->B g:A->B. ~(f = g) ==> ?a:2->A. ~(f o a = g o a)”);


val Thm1 = prove_store("Thm1",
e0
(strip_tac >> cases_on “0f o To1(C) = 1f o To1(C)” 
 >-- (strip_assume_tac PCC1 >> fs[isPb_def] >>
      first_x_assum rev_drule >>
      pop_assum (strip_assume_tac o uex_expand) >>
      qsuff_tac ‘~(?a1 : 2->C. T) ==> is0(C)’
      >-- rw[imp_lemma] >>
      strip_tac >> rw[is0_def] >> strip_tac >> uex_tac >>
      qexists_tac ‘From0(X) o a’ >> rw[] >> rpt strip_tac >>
      ccontra_tac >> drule CC2_2 >> fs[] >>
      qsuff_tac ‘?a1:2->C.T’ >-- (rw[] >>
      first_x_assum accept_tac) >>
      qexists_tac ‘a'’ >> rw[]) >>
 disj2_tac >> drule CC2_2 >> 
 pop_assum strip_assume_tac >> qexists_tac ‘a’ >> rw[])
(form_goal
 “!C. is0(C) | (?a:2->C.T)”) );

val iscoPr_def = qdefine_psym("iscoPr",[‘i1:A->AB’,‘i2:B->AB’])
‘!X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g’
|> qgenl [‘A’,‘B’,‘AB’,‘i1’,‘i2’]
|> store_as "iscoPr_def";



val _ = new_fun "+" (cat_sort,[("A",cat_sort),("B",cat_sort)])
val _ = new_fun "i1" (fun_sort (rastt "A") (rastt "A + B"),[("A",cat_sort),("B",cat_sort)])
val _ = new_fun "i2" (fun_sort (rastt "B") (rastt "A + B"),[("A",cat_sort),("B",cat_sort)])


val i2_def = 
    store_ax("i2_def",
             “!A B.iscoPr(i1(A,B),i2(A,B))”)


val coPa_def0 = i2_def 
                    |> rewr_rule[iscoPr_def] |> spec_all
                    |> qsimple_uex_spec "coPa" [‘f’,‘g’]
                    |> gen_all
                    |> store_as "coPa_def0"


val coPa_def = proved_th $
e0
(rpt gen_tac >>
 qsspecl_then [‘f’,‘g’] assume_tac coPa_def0 >> arw[] >>
 qspecl_then [‘A’,‘B’] assume_tac i2_def >>
 fs[iscoPr_def] >>
 first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qsuff_tac ‘coPa(f,g)= fg’ >-- (strip_tac >> arw[]) >>
 first_x_assum irule >> arw[])
(form_goal
 “∀A B X f:A->X g:B->X.
 (coPa(f, g) o i1(A, B) = f & coPa(f, g) o i2(A, B) = g) &
 !fg' : A + B -> X.
 fg' o i1(A, B) = f & fg' o i2(A, B) = g ==>
 fg' = coPa(f, g)”)


val Mono_def = qdefine_psym("Mono",[‘f:A->B’])
‘!X g:X->A h. f o g = f o h ==> g = h’
|> qgenl[‘A’,‘B’,‘f’] |> store_as "Mono_def";


val post_inv_Mono = prove_store("post_inv_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qby_tac
 ‘i o m o g = i o m o h’ >-- arw[] >>
 rfs[GSYM o_assoc] >> fs[IdL])
(form_goal
 “!A B m:A->B i:B->A. i o m = Id(A) ==> Mono(m)”));


val i12_of_coPa = coPa_def |> spec_all |> conjE1
                           |> gen_all 
                           |> store_as "i12_of_coPa";

val i1_of_coPa = i12_of_coPa |> spec_all |> conjE1
                             |> gen_all 
                             |> store_as "i1_of_coPa";


val i2_of_coPa = i12_of_coPa |> spec_all |> conjE2
                             |> gen_all 
                             |> store_as "i2_of_coPa";
 

val Thm2_1_i1 = prove_store("Thm2_1_i1",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 cases_on “g:X->A = h” >-- arw[] >>
 qsuff_tac ‘?f:B->A.T’
 >-- (strip_tac >> 
      qby_tac ‘coPa(Id(A),f) o i1(A,B) = Id(A)’
      >-- rw[i1_of_coPa] >>
      qby_tac ‘coPa(Id(A),f) o i1(A, B) o g = coPa(Id(A),f) o i1(A, B) o h’
      >-- arw[] >>
      rfs[GSYM o_assoc,IdL]) >>
 drule CC2_2 >> pop_assum strip_assume_tac >>
 qexists_tac ‘g o a o 1f o To1(B)’ >> rw[])
(form_goal
 “!A B. Mono(i1(A,B))”));


val to1_unique = prove_store("to1_unique",
e0
(rpt strip_tac >>
 qspecl_then [‘X’,‘f’] assume_tac To1_def >>
 qspecl_then [‘X’,‘g’] assume_tac To1_def >> 
 arw[])
(form_goal
 “!X f:X->1 g:X->1. f = g”));


val one_to_one_Id = prove_store("one_to_one_Id",
e0
(strip_tac >>
 qspecl_then [‘1’,‘f’,‘Id(1)’] assume_tac to1_unique >>
 first_x_assum accept_tac)
(form_goal
 “!f:1->1. f = Id(1)”))

val from0_unique = prove_store("form0_unique",
e0
(rpt strip_tac >>
 qspecl_then [‘X’,‘f’] assume_tac From0_def >>
 qspecl_then [‘X’,‘g’] assume_tac From0_def >> 
 arw[])
(form_goal
 “!X f:0->X g:0->X. f = g”));


val zero_to_zero_Id = prove_store("zero_to_zero_Id",
e0
(strip_tac >>
 qspecl_then [‘0’,‘f’,‘Id(0)’] assume_tac from0_unique >>
 first_x_assum accept_tac)
(form_goal
 “!f:0->0. f = Id(0)”))


val one_not_to_zero = prove_store("one_not_to_zero",
e0
(strip_tac >> assume_tac ZERO_not_ONE >>
 qsuff_tac ‘?g:0->1. Iso(g)’ >-- arw[] >>
 pop_assum (K all_tac) >>
 rw[Iso_def] >> qexistsl_tac [‘From0(1)’,‘f’] >>
 rw[zero_to_zero_Id,one_to_one_Id])
(form_goal “!f:1->0.F”));


val to0_is0 = prove_store("to0_is0",
e0
(rw[is0_def] >> rpt strip_tac >> uex_tac >>
 qexists_tac ‘From0(X) o f0’ >> rw[] >> rpt strip_tac >>
 ccontra_tac >> drule CC2_2 >> pop_assum strip_assume_tac >>
 qsspecl_then [‘f0 o a o 1f’] assume_tac one_not_to_zero >> 
 first_x_assum accept_tac)
(form_goal
 “!A f0:A->0. is0(A)”));


val Thm2_2 = prove_store("Thm2_2",
e0
(rw[isPb_def] >> rpt strip_tac >> strip_assume_tac PCC1 >>
 fs[isPb_def] >> 
 qsuff_tac ‘?u:P->1 v. 0f o u = 1f o v’
 >-- (strip_tac >> first_x_assum drule >> 
      pop_assum (strip_assume_tac o uex_expand) >>
      qsspecl_then [‘a’] accept_tac to0_is0) >> 
 qexistsl_tac [‘To1(A) o p’,‘To1(B) o q’] >>
 qby_tac 
  ‘coPa(0f o To1(A), 1f o To1(B)) o i1(A, B) o p = 
   coPa(0f o To1(A), 1f o To1(B)) o i2(A, B) o q’ 
 >-- arw[] >>
 fs[GSYM o_assoc,i12_of_coPa])
(form_goal
 “!A B P p:P->A q.isPb(i1(A,B),i2(A,B),p,q) ==> is0(P)”));


val Epi_def = qdefine_psym("Epi",[‘f:A->B’])
‘!X g:B->X h. g o f = h o f ==> g = h’
|> qgenl [‘A’,‘B’,‘f’] |> store_as "Epi_def";


val Epi_def = qdefine_psym("Epi",[‘f:A->B’])
‘!X g:B->X h. g o f = h o f ==> g = h’
|> qgenl [‘A’,‘B’,‘f’] |> store_as "Epi_def";


val isgen_def = qdefine_psym("isgen",[‘G’])
‘!A B f1:A->B f2. ~(f1 = f2) ==> ?g: G -> A. ~(f1 o g = f2 o g)’
|> gen_all


val isPb_def = qdefine_psym("isPb",[‘f:X->Z’,‘g:Y->Z’,‘p: P ->X’,‘q: P -> Y’])
‘ f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v’
|> qgenl [‘X’,‘Z’,‘f:X->Z’,‘Y’,‘g:Y->Z’,‘P’,‘p:P ->X’,‘q: P ->Y’]
|> store_as "isPb_def";


val isPo_def = qdefine_psym("isPo",[‘f:H -> X’,‘g : H -> Y’,‘p : X -> P’,‘ q : Y -> P’])
‘p o f = q o g &
 !A u : X -> A v : Y -> A. 
    u o f = v o g ==> 
    ?!a : P -> A. a o p = u & a o q = v’
|> qgenl [‘H’,‘X’,‘f’,‘Y’,‘g’,‘P’,‘p’,‘q’]


val isPo_ex = store_ax("isPo_ex",“!H X f:H->X Y g:H->Y. ?P p:X->P q:Y->P. isPo(f,g,p,q)”);


val _ = new_fun "E" (cat_sort,[])
val _ = new_fun "ε1" (fun_sort (rastt "2") (rastt "E"),[])
val _ = new_fun "ε2" (fun_sort (rastt "2") (rastt "E"),[])

val E_def = 
store_ax("E_def",“ isPo(coPa(0f,1f),coPa(0f,1f),ε1,ε2)”);


val isPo_expand = isPo_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : P -> A. a o p:X->P = u & a o q:Y->P = v”) |> store_as "isPo_expand";


val Epi_iff_Po_Id = prove_store("Epi_iff_Po_Id",
e0
cheat
(form_goal
 “∀A B f:A->B. Epi(f) ⇔ isPo(f,f,Id(B),Id(B))”));

val iso_Po_Po = prove_store("iso_Po_Po",
e0
(cheat)
(form_goal
 “∀X A f:X->A B g:X->B P1 p1:A->P1 q1:B->P1. isPo(f,g,p1,q1) ⇒
  ∀P2 p2: A-> P2 q2: B -> P2 i:P1->P2 j: P2 -> P1.
  j o i = Id(P1) & i o j = Id(P2) ⇒ isPo(f,g,p2,q2)”));

val Po_equal_Id = prove_store("Po_equal_Id",
e0
(rpt strip_tac >>
 drule $ iffLR isPo_expand >>
 fs[] >>
 first_x_assum (qsspecl_then [‘Id(B)’,‘Id(B)’] assume_tac) >>
 fs[] >> drule iso_Po_Po >> first_x_assum irule >>
 qexistsl_tac [‘a’,‘p’] >>
 arw[] >>
 drule $ iffLR isPo_expand >> fs[] >>
 first_x_assum (qsspecl_then [‘p’,‘p’] assume_tac) >>
 fs[] >> 
 first_assum (qspecl_then [‘p o a’] assume_tac) >>
 first_x_assum (qspecl_then [‘Id(P)’] assume_tac) >>
 rfs[IdL,o_assoc,IdR])
(form_goal “∀A B e:A->B P p:B->P. isPo(e,e,p,p) ⇒
 isPo(e,e,Id(B),Id(B))”));

val _ = add_parse (int_of "𝟚");

(* \ b 2 |-> 𝟚*)

val two_def = 
qdefine_fsym("𝟚",[]) ‘Id(2)’

val e1_ne_e2 = prove_store("e1_ne_e2",
e0
(ccontra_tac >>
 qsuff_tac ‘isPo(coPa(0f,1f),coPa(0f,1f),𝟚,𝟚)’
 >-- rw[GSYM Epi_iff_Po_Id,two_def,CC3] >>
 assume_tac E_def >> rfs[two_def] >>
 drule Po_equal_Id >> first_x_assum accept_tac
 )
(form_goal “~(ε1 = ε2)”));


val dom_def = qdefine_fsym("dom",[‘f:2->A’])
‘f o 0f’ |> gen_all


val cod_def = qdefine_fsym("cod",[‘f:2->A’])
‘f o 1f’ |> gen_all


val e1_e2_same_dom = prove_store("e1_e2_same_dom",
e0
(assume_tac E_def >> fs[isPo_def] >>
 rw[dom_def] >> 
 qsspecl_then [‘0f’,‘1f’] assume_tac i1_of_coPa >>
 qby_tac
 ‘ε1 o coPa(0f, 1f) o i1(1,1) = ε2 o coPa(0f, 1f) o i1(1,1)’
 >-- (rw[GSYM o_assoc] >> arw[]) >>
 rfs[])
(form_goal “dom(ε1) = dom(ε2)”));


val e1_e2_same_cod = prove_store("e1_e2_same_cod",
e0
(assume_tac E_def >> fs[isPo_def] >>
 rw[cod_def] >> 
 qsspecl_then [‘0f’,‘1f’] assume_tac i2_of_coPa >>
 qby_tac
 ‘ε1 o coPa(0f, 1f) o i2(1,1) = ε2 o coPa(0f, 1f) o i2(1,1)’
 >-- (rw[GSYM o_assoc] >> arw[]) >>
 rfs[])
(form_goal “cod(ε1) = cod(ε2)”));

val zero_def = qdefine_fsym("𝟘",[]) ‘0f o To1(2)’
val one_def = qdefine_fsym("𝟙",[]) ‘1f o To1(2)’


val CC2_0 = store_ax("CC2_0",“~(𝟘 = 𝟙) & ~(𝟘 = 𝟚) & ~(𝟙 = 𝟚)”)

val CC2_1 = store_ax ("CC2_1",“ ∀f:2->2. f = 𝟘 | f = 𝟙 | f = 𝟚”);


val Thm3_1 = prove_store("Thm3_1",
e0
(rpt strip_tac >> fs[isgen_def] >>
 assume_tac e1_ne_e2 >> first_x_assum drule >>
 pop_assum strip_assume_tac >> drule CC2_2 >>
 pop_assum (x_choose_then "f" assume_tac) >>
 fs[o_assoc] >>
 qspecl_then [‘g o f’] strip_assume_tac CC2_1 (* 3 *)
 >-- (fs[zero_def] >> 
     fs[GSYM dom_def,GSYM o_assoc,e1_e2_same_dom])
 >-- (fs[one_def] >> 
     fs[GSYM cod_def,GSYM o_assoc,e1_e2_same_cod]) >>
 qexistsl_tac [‘f’,‘g’] >> arw[two_def])
(form_goal
 “!G. isgen(G) ==> ?s:2->G r:G->2. r o s = Id(2)”));


val areIso_def = store_ax("areIso_def",
“!A B. areIso(A,B) <=> ?f:A->B g:B->A. f o g = Id(B) & g o f = Id(A)”)

val distinct_three_lemma = prove_store("distinct_three_lemma",
e0
(rpt strip_tac >>
 first_assum (qspecl_then [‘g1’] strip_assume_tac) >>
 first_assum (qspecl_then [‘g2’] strip_assume_tac) >>
 first_assum (qspecl_then [‘g3’] strip_assume_tac) >> fs[] >>
 first_assum (qspecl_then [‘g’] strip_assume_tac) >> fs[])
(form_goal
 “∀A B f1 f2 f3:A->B. 
  ~(f1 = f2) & ~(f1 = f3) & ~(f2 = f3) &
  (∀f:A->B. f = f1 | f = f2 | f = f3) ⇒ 
  ∀g1 g2 g3:A->B. 
  ~(g1 = g2) & ~(g1 = g3) & ~(g2 = g3) ⇒ 
  ∀g:A->B. g = g1 | g = g2 | g = g3”));


val dflip_tac = 
fconv_tac 
 (basic_once_fconv no_conv (rewr_fconv (eq_sym "fun")))


val Thm3_2 = prove_store("Thm3_2",
e0
(rpt strip_tac >> drule Thm3_1 >> 
 rw[areIso_def] >> 
 pop_assum (x_choosel_then ["f","g"] strip_assume_tac) >>
 qexistsl_tac [‘g’,‘f’] >> arw[] >>
 qby_tac
 ‘~(f o 0f o To1(2) o g = f o 1f o To1(2) o g)’
 >-- (ccontra_tac >>
     qby_tac 
     ‘g o (f o 0f o To1(2) o g) o f = 
      g o (f o 1f o To1(2) o g) o f’ 
     >-- arw[] >>
     rfs[GSYM o_assoc,IdL] >> rfs[o_assoc,IdR] >>
     fs[GSYM one_def,GSYM zero_def,CC2_0]) >>
 qby_tac
 ‘~(f o 0f o To1(2) o g = Id(G))’
 >-- 
 (ccontra_tac >>
  qby_tac 
  ‘g o (f o 0f o To1(2) o g) o f = 
   g o (Id(G)) o f’ 
  >-- arw[] >>
  rfs[GSYM o_assoc,IdL] >> rfs[o_assoc,IdR] >>
  rfs[GSYM two_def,GSYM zero_def,CC2_0,IdL]) >>
 qby_tac
 ‘~(f o 1f o To1(2) o g = Id(G))’
 >-- 
 (ccontra_tac >>
  qby_tac 
  ‘g o (f o 1f o To1(2) o g) o f = 
   g o (Id(G)) o f’ 
  >-- arw[] >>
  rfs[GSYM o_assoc,IdL] >> rfs[o_assoc,IdR] >>
  rfs[GSYM two_def,GSYM one_def,CC2_0,IdL]) >> 
 qsuff_tac ‘~(f o g = f o 1f o To1(2) o g) & 
            ~(f o g = f o 0f o To1(2) o g)’
 >-- (qby_tac ‘∀a: G->G. a = f o 1f o To1(2) o g | 
 a = f o 0f o To1(2) o g | a = Id(G)’ 
     >-- (irule distinct_three_lemma >> arw[] >>
          dflip_tac >> arw[] >> dflip_tac >>
          qexistsl_tac [‘g1’,‘g2’,‘g3’] >> arw[]) >>
     first_x_assum (qspecl_then [‘f o g’] strip_assume_tac)>>
     rfs[]) >>
 strip_tac >> ccontra_tac (* 2 *)
 >-- (qby_tac
     ‘g o (f o g) o f = g o (f o 1f o To1(2) o g) o f’
     >-- arw[] >>
     rfs[GSYM o_assoc,IdL] >> 
     rfs[o_assoc,IdR] >> 
     fs[GSYM CC2_0,GSYM two_def,GSYM one_def]) >>
 qby_tac
 ‘g o (f o g) o f = g o (f o 0f o To1(2) o g) o f’
 >-- arw[] >>
 rfs[GSYM o_assoc,IdL] >> 
 rfs[o_assoc,IdR] >> 
 fs[GSYM CC2_0,GSYM two_def,GSYM zero_def])
(form_goal
 “!G. isgen(G) ⇒ 
  ∀g1 g2 g3:G->G. 
  ~(g1 = g2) & ~(g1 = g3) & ~(g2 = g3) & 
  (!e:G->G. e = g1 | e = g2 | e = g3) ⇒ 
  areIso(G,2)”));


val _ = new_fun "3" (cat_sort,[])

val _ = new_fun "α" (fun_sort (rastt "2") (rastt "3"),[])

val _ = new_fun "β" (fun_sort (rastt "2") (rastt "3"),[])

val _ = new_fun "γ" (fun_sort (rastt "2") (rastt "3"),[])

val CC4_1 = store_ax("CC4_1",
“γ o 0f = α o 0f & γ o 1f = β o 1f”)

val CC4_2 = store_ax("CC4_2",“isPo(1f,0f,α,β)”)

val tri0 = CC4_2 |> rewr_rule[isPo_def]
                 |> conjE2

val tri_uex = proved_th $
e0
(cheat)
(form_goal
 “∀A u:2->A v:2->A.
  ?!a:3->A. 
  (u o 1f = v o 0f & a o α = u & a o β = v) |
  (~(u o 1f = v o 0f) & a = dom(u) o To1(3)) ”)

val tri_def0 = 
tri_uex |> spec_all |> qsimple_uex_spec "tri" [‘u’,‘v’] 

(*isPo_expand |> qsspecl [‘1f’,‘0f’,‘α’,‘β’]*)

val tri_def1 = proved_th $
e0
(cheat)
(form_goal
 “∀A u:2->A v:2->A. 
  u o 1f = v o 0f ⇒
  (tri(u, v) o α = u & tri(u, v) o β = v) &
  (∀a'. a' o α = u & a' o β = v ⇒ a' = tri(u,v))”)
|> rewr_rule[GSYM dom_def,GSYM cod_def]



val tri_def = proved_th $
e0
(cheat)
(form_goal
 “∀A u:2->A v:2->A. 
  dom(v) = cod(u) ⇒
  (tri(u, v) o α = u & tri(u, v) o β = v) &
  (∀a'. a' o α = u & a' o β = v ⇒ a' = tri(u,v))”)
|> rewr_rule[GSYM dom_def,GSYM cod_def]

val oa_def = qdefine_fsym("@",[‘g:2->A’,‘f:2->A’])
‘tri(f,g) o γ’ |> gen_all



val dom_cod_zot = prove_store("dom_cod_zot",
e0
(rw[zero_def,one_def,dom_def,cod_def,o_assoc,
    one_to_one_Id,IdR,two_def,IdL])
(form_goal
 “dom(𝟘) = 0f ∧ cod(𝟘) = 0f ∧ dom(𝟙) = 1f ∧ cod(𝟙) = 1f ∧
  dom(𝟚) = 0f ∧ cod(𝟚) = 1f”));


val zf_ne_of = prove_store("zf_ne_of",
e0
(ccontra_tac >> 
 qby_tac ‘0f o To1(2) = 1f o To1(2)’
 >-- arw[] >>
 fs[GSYM zero_def,GSYM one_def,CC2_0])
(form_goal “~ (0f = 1f)”));



val dom_cod_is_two = prove_store("dom_cod_is_two",
e0
(rpt strip_tac >> 
 qsspecl_then [‘f’] strip_assume_tac CC2_1 >> 
 fs[dom_cod_zot] >-- fs[zf_ne_of] >> fs[GSYM zf_ne_of])
(form_goal
 “∀f:2->2. dom(f) = 0f & cod(f) = 1f ⇒ f = 𝟚”));

val tri_eqns = tri_def |> spec_all |> undisch
                       |> conjE1
                       |> disch_all
                       |> gen_all

val dom_zero_0f = dom_cod_zot |> conjE1  
val cod_zero_0f = dom_cod_zot |> conjE2 |> conjE1 
val dom_one_1f = dom_cod_zot |> conjE2 |> conjE2
                             |> conjE1
val cod_one_1f = dom_cod_zot |> conjE2 |> conjE2
                             |> conjE2 |> conjE1
val dom_two_0f = dom_cod_zot |> conjE2 |> conjE2
                             |> conjE2 |> conjE2
                             |> conjE1
val cod_two_1f = dom_cod_zot |> conjE2 |> conjE2
                             |> conjE2 |> conjE2
                             |> conjE2


val dom_tri21_gamma = prove_store("dom_tri21_gamma",
e0
(rw[dom_def,cod_def,o_assoc,CC4_1] >>
 qsuff_tac
 ‘tri(𝟚, 𝟙) o α = 𝟚 & tri(𝟚, 𝟙) o β = 𝟙’
 >-- (strip_tac >> arw[GSYM o_assoc] >>
     rw[GSYM dom_def,dom_two_0f]) >>
 irule tri_eqns >> rw[dom_cod_zot])
(form_goal “dom(tri(𝟚, 𝟙) o γ) = 0f”));

val cod_tri21_gamma = prove_store("cod_tri21_gamma",
e0
(rw[cod_def,o_assoc,CC4_1] >>
 qsuff_tac
 ‘tri(𝟚, 𝟙) o α = 𝟚 & tri(𝟚, 𝟙) o β = 𝟙’
 >-- (strip_tac >> arw[GSYM o_assoc] >>
     rw[GSYM cod_def,cod_one_1f]) >>
 irule tri_eqns >> rw[dom_cod_zot])
(form_goal “cod(tri(𝟚, 𝟙) o γ) = 1f”));


val oa_one_two_two = prove_store("oa_one_two_two",
e0
(irule dom_cod_is_two >> 
 rw[oa_def,dom_tri21_gamma,cod_tri21_gamma])
(form_goal “𝟙 @ 𝟚 = 𝟚”));


val dom_tri02_gamma = prove_store("dom_tri02_gamma",
e0
(rw[dom_def,cod_def,o_assoc,CC4_1] >>
 qsuff_tac
 ‘tri(𝟘, 𝟚) o α = 𝟘 & tri(𝟘, 𝟚) o β = 𝟚’
 >-- (strip_tac >> arw[GSYM o_assoc] >>
     rw[GSYM dom_def,dom_zero_0f]) >>
 irule tri_eqns >> rw[dom_cod_zot])
(form_goal “dom(tri(𝟘, 𝟚) o γ) = 0f”));

val cod_tri02_gamma = prove_store("cod_tri02_gamma",
e0
(rw[cod_def,o_assoc,CC4_1] >>
 qsuff_tac
 ‘tri(𝟘, 𝟚) o α = 𝟘 & tri(𝟘, 𝟚) o β = 𝟚’
 >-- (strip_tac >> arw[GSYM o_assoc] >>
     rw[GSYM cod_def,cod_two_1f]) >>
 irule tri_eqns >> rw[dom_cod_zot])
(form_goal “cod(tri(𝟘, 𝟚) o γ) = 1f”));


val oa_two_zero_two = prove_store("oa_two_zero_two",
e0
(irule dom_cod_is_two >> 
 rw[oa_def,dom_tri02_gamma,cod_tri02_gamma])
(form_goal “𝟚 @ 𝟘 = 𝟚”));

val Thm4 = conjI oa_one_two_two oa_two_zero_two


val cpsb_def = qdefine_psym("cpsb",[‘g:2->A’,‘f:2->A’])
‘dom(g) = cod(f)’ |> gen_all 

val isid_def = qdefine_psym("isid",[‘f:2->A’])
‘?f0:1->A. f = f0 o To1(2)’ |> gen_all


val dom_one_cod_two = prove_store("dom_one_cod_two",
e0
(rw[dom_cod_zot])
(form_goal
 “dom(𝟙) = cod(𝟚)”));


val dom_two_cod_zero = prove_store("dom_two_cod_zero",
e0
(rw[dom_cod_zot])
(form_goal
 “dom(𝟚) = cod(𝟘)”));

val tri21_ab = prove_store("tri21_ab",
e0
(irule tri_eqns >> rw[dom_cod_zot])
(form_goal “tri(𝟚,𝟙) o α = 𝟚 & tri(𝟚,𝟙) o β = 𝟙”));


val tri02_ab = prove_store("tri02_ab",
e0
(irule tri_eqns >> rw[dom_cod_zot])
(form_goal “tri(𝟘,𝟚) o α = 𝟘 & tri(𝟘,𝟚) o β = 𝟚”));

val tri21_gamma = prove_store("tri21_gamma",
e0
(rw[GSYM oa_def,Thm4])
(form_goal “tri(𝟚, 𝟙) o γ = 𝟚”));


val tri02_gamma = prove_store("tri02_gamma",
e0
(rw[GSYM oa_def,Thm4])
(form_goal “tri(𝟘,𝟚) o γ = 𝟚”));


val Thm5_1 = prove_store("Thm5_1",
e0
(rpt strip_tac >> 
 fs[cpsb_def] >> drule tri_def >>
 rw[oa_def] >> fs[] >> 
 qby_tac
 ‘f o tri(𝟚,𝟙) = tri(f, g)’
 >-- (first_x_assum irule >>
     rw[o_assoc,tri21_ab] >>
     rw[one_def,two_def,IdR] >>
     fs[isid_def,dom_def,cod_def] >> 
     qpick_x_assum ‘g o 0f = f o 1f’
     (assume_tac o GSYM) >> arw[GSYM o_assoc] >>
     qsuff_tac ‘f0 o (To1(2) o 0f) o To1(2) = f0 o To1(2)’ 
     >-- rw[o_assoc] >> 
     rw[one_to_one_Id,IdL]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[o_assoc,tri21_gamma,two_def,IdR])
(form_goal
 “!A g:2->A. isid(g) ==> 
  (!f. cpsb(g,f) ==> g @ f = f)”));


val Thm5_2 = prove_store("Thm5_2",
e0
(rpt strip_tac >> 
 fs[cpsb_def] >> drule tri_def >>
 rw[oa_def] >> fs[] >> 
 qby_tac
 ‘g o tri(𝟘,𝟚) = tri(f, g)’
 >-- (first_x_assum irule >>
     rw[o_assoc,tri02_ab] >>
     rw[one_def,two_def,IdR,zero_def] >>
     fs[isid_def,dom_def,cod_def] >> 
     arw[GSYM o_assoc] >>
     qsuff_tac ‘f0 o (To1(2) o 1f) o To1(2) = f0 o To1(2)’ 
     >-- rw[o_assoc] >> 
     rw[one_to_one_Id,IdL]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[o_assoc,tri02_gamma,two_def,IdR])
(form_goal
 “!A f:2->A. isid(f) ==> 
  (!g. cpsb(g,f) ==> g @ f = g)”));


val _ = add_parse (int_of "¹")
val _ = add_parse (int_of "²")
val _ = add_parse (int_of "³")
val _ = add_parse (int_of "ᵅ") 
val _ = add_parse (int_of "ᵝ")  
val _ = add_parse (int_of "ˠ")  

val Tp0_def = 
qdefine_fsym("Tp0",[‘f:1->Exp(X,Y)’])
‘Ev(X,Y) o Pa(Id(X),f o To1(X))’ |> GSYM
|> gen_all

val Swap_def =
qdefine_fsym("Swap",[‘A’,‘B’])
‘Pa(p2(A,B),p1(A,B))’ |> GSYM |> gen_all


val p12_of_Pa = Pa_def |> spec_all |> conjE1
                       |> gen_all
                       |> store_as "p12_of_Pa";

val Swap_property = proved_th $
e0
(rw[GSYM Swap_def,p12_of_Pa])
(form_goal
 “!A B. p1(B,A) o Swap(A,B) = p2(A,B) & p2(B,A) o Swap(A,B) = p1(A,B)”)


val is_Pa = Pa_def |> spec_all |> conjE2 |> gen_all
                   |> store_as "is_Pa";


val to_P_component = prove_store("to_Pr_component",
e0
(rpt strip_tac >> irule is_Pa >> rw[])
(form_goal
 “!A B X f:X->A * B.  f = Pa(p1(A,B) o f,p2(A,B) o f)”));


val to_P_eq = prove_store("to_P_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f = Pa(p1(A,B) o g,p2(A,B) o g) &
            g = Pa(p1(A,B) o g,p2(A,B) o g)’ >--
 (strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >>
 (irule is_Pa >> arw[]))
(form_goal
 “!A B X f:X->A * B g:X->A * B. p1(A,B) o f = p1(A,B) o g &
 p2(A,B) o f = p2(A,B) o g ==> f = g”));



val Pa_distr = proved_th $
e0
(rpt strip_tac >> irule is_Pa >>
 rw[GSYM o_assoc,p12_of_Pa])
(form_goal
“!A B X a1:X ->A a2:X->B X0 x:X0->X. Pa(a1,a2) o x = 
Pa(a1 o x,a2 o x) ”)


val Swap_Swap_Id = prove_store("Swap_Swap_Id",
e0
(rpt strip_tac >> irule to_P_eq >> rw[GSYM Swap_def,IdR] >>
 rw[Pa_distr,p12_of_Pa])
(form_goal
 “!A B. Swap(B,A) o Swap(A,B) = Id(A * B)”));

val csL_def = qdefine_fsym("csL",[‘cs:2 * 2->A’])
‘cs o Pa(𝟘,𝟚)’ |> gen_all 

val csR_def = qdefine_fsym("csR",[‘cs:2 * 2->A’])
‘cs o Pa(𝟙,𝟚)’ |> gen_all 

val csT_def = qdefine_fsym("csT",[‘cs:2 * 2->A’])
‘cs o Pa(𝟚,𝟘)’ |> gen_all 

val csB_def = qdefine_fsym("csB",[‘cs:2 * 2->A’])
‘cs o Pa(𝟚,𝟙)’ |> gen_all 

val Pt_def = qdefine_fsym("Pt",[‘h:X-> Exp(A,B)’])
‘Ev(A,B) o Pa(p1(A,X), h o p2(A,X))’ |> gen_all 
 
val Ed_def = qdefine_fsym("Ed",[‘f:A->B’,‘X’])
‘Tp(Ev(B,X) o Pa(f o p1(A,Exp(B,X)),p2(A,Exp(B,X))))’ 
|> gen_all

val Er1_def = qdefine_fsym("Er1",[‘A’])
‘Ev(1,A) o Pa(To1(Exp(1,A)),Id(Exp(1,A)))’ |> gen_all

val A1f_def = qdefine_fsym("A1f",[‘A’])
‘Er1(A) o Ed(1f,A)’ |> gen_all


val fun_pres_oa = prove_store("fun_pres_oa",
e0
(cheat)
(form_goal
 “∀A f:2->A g. cpsb(g,f) ⇒
  ∀B k:A->B. k o (g @ f) = (k o g) @ (k o f)”));


val To1_o_To1 = prove_store("To1_o_To1",
e0
(cheat)
(form_goal
 “∀A f:X->A. To1(A) o f = To1(X)”));

val Ev_of_Tp = prove_store("Ev_of_Tp",
e0
(rpt strip_tac >> rw[Tp_def])
(form_goal
 “!A B X f:A * X ->B. 
  Ev(A,B) o Pa(p1(A,X),Tp(f) o p2(A,X)) = f”));


val Ev_of_Tp_el = prove_store("Ev_of_Tp_el",
e0
(rpt strip_tac >>
 assume_tac Ev_of_Tp >> 
 first_x_assum (qspecl_then [‘A’,‘B’,‘X’,‘f’] assume_tac) >>
 qby_tac 
 ‘Pa(a, Tp(f) o x) = Pa(p1(A, X), Tp(f) o p2(A, X)) o Pa(a,x)’ >--
 (irule to_P_eq >> rw[p12_of_Pa] >> 
  rw[p12_of_Pa,GSYM o_assoc] >> rw[o_assoc,p12_of_Pa]) >>
 arw[GSYM o_assoc])
(form_goal
 “!A B X f:A * X ->B P a:P->A x: P ->X. 
  Ev(A,B) o Pa(a, Tp(f) o x) = f o Pa(a,x)”));


val Ev_of_Tp_el' = prove_store("Ev_of_Tp_el'",
e0
(rpt strip_tac >> 
 qby_tac ‘Tp(f) = Tp(f) o Id(P)’ >-- rw[IdR] >>
 once_arw[] >> rw[Ev_of_Tp_el])
(form_goal
“!A B P f:A * P -> B  a:P -> A.
Ev(A, B) o Pa(a, Tp(f)) = f o Pa(a, Id(P))”));


val A1f_of_cs = prove_store("A1f_of_cs",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,dom_def,Pa_distr,
    o_assoc,To1_o_To1,IdL,Ev_of_Tp_el,Ev_of_Tp_el',
    p12_of_Pa,one_to_one_Id,IdR])
(form_goal
 “∀A f:1-> Exp(2,A).
  (Er1(A) o Ed(0f,A)) o f = dom(Pt(f) o Pa(Id(2),To1(2)))”));


val csT_Pt = prove_store("csT_Pt",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,csT_def] >>
 rw[Pa_distr,o_assoc,To1_o_To1,IdL] >>
 rw[Ev_of_Tp_el,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el',Pa_distr,o_assoc,GSYM Swap_def,p12_of_Pa,
    two_def,zero_def] )
(form_goal 
 “∀A f:2-> Exp(2,A). csT(Pt(f)) = 
  (Er1(A) o Ed(0f,A)) o Tp(Pt(f)o Swap(2,2))”));

val csL_Pt = prove_store("csL_Pt",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,csL_def] >>
 rw[Pa_distr,o_assoc,To1_o_To1,IdL] >>
 rw[Ev_of_Tp_el,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el',Pa_distr,o_assoc,GSYM Swap_def,p12_of_Pa,
    two_def,zero_def,IdR] )
(form_goal 
 “∀A f:2-> Exp(2,A). csL(Pt(f)) = 
 (Er1(A) o Ed(0f,A)) o f”));

val csR_Pt = prove_store("csR_Pt",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,csR_def] >>
 rw[Pa_distr,o_assoc,To1_o_To1,IdL] >>
 rw[Ev_of_Tp_el,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el',Pa_distr,o_assoc,GSYM Swap_def,p12_of_Pa,
    two_def,one_def,IdR] )
(form_goal 
 “∀A f:2-> Exp(2,A). csR(Pt(f)) = 
 (Er1(A) o Ed(1f,A)) o f”));


val Thm6_vertical = prove_store("Thm6_vertical",
e0
(rpt strip_tac >> rw[csL_Pt,csR_Pt] >> drule fun_pres_oa >> 
 arw[])
(form_goal
 “∀A s1:2-> Exp(2,A) s2:2-> Exp(2,A). cpsb(s2,s1) ⇒ 
  csL(Pt(s2 @ s1)) = csL(Pt(s2)) @ csL(Pt(s1))  ∧
  csR(Pt(s2 @ s1)) = csR(Pt(s2)) @ csR(Pt(s1))”));


val oa_dom_cod = prove_store("oa_dom_cod",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 fs[cpsb_def] >> rw[oa_def] >>
 drule tri_def >> rw[dom_def,cod_def,o_assoc,CC4_1] >>
 fs[dom_def,cod_def] >>
 arw[GSYM o_assoc])
(form_goal
 “∀A f:2->A g. cpsb(g,f) ⇒ dom(g @ f) = dom(f) ∧ cod(g @ f) = cod(g)”));


val csT_dom = prove_store("csT_dom",
e0
(rw[csT_def,dom_def,Pt_def,o_assoc,Pa_distr,p12_of_Pa,
    two_def,zero_def])
(form_goal
 “∀A s:2->Exp(2,A). csT(Pt(s)) = Pt(dom(s)) o Pa(Id(2),To1(2))”));


val csB_cod = prove_store("csB_cod",
e0
(rw[csB_def,cod_def,Pt_def,o_assoc,Pa_distr,p12_of_Pa,
    two_def,one_def])
(form_goal
 “∀A s:2->Exp(2,A). csB(Pt(s)) = Pt(cod(s)) o Pa(Id(2),To1(2))”));


val Thm6_vertical_full = prove_store("Thm6_vertical_full",
e0
(rpt strip_tac >> rw[csL_Pt,csR_Pt] >> drule fun_pres_oa >> 
 arw[] >>
 rw[csT_dom,csB_cod] >> drule oa_dom_cod >> arw[])
(form_goal
 “∀A s1:2-> Exp(2,A) s2:2-> Exp(2,A). cpsb(s2,s1) ⇒ 
  csL(Pt(s2 @ s1)) = csL(Pt(s2)) @ csL(Pt(s1)) ∧
  csR(Pt(s2 @ s1)) = csR(Pt(s2)) @ csR(Pt(s1)) ∧
  csT(Pt(s2 @ s1)) = csT(Pt(s1)) ∧
  csB(Pt(s2 @ s1)) = csB(Pt(s2))”));


val csL_csT = prove_store("csL_csT",
e0
(rw[csL_def,csT_def,o_assoc,GSYM Swap_def,p12_of_Pa,
    Pa_distr])
(form_goal
 “∀A f: 2 * 2 -> A. csT(f o Swap(2,2)) = csL(f)”));


val csR_csB = prove_store("csR_csB",
e0
(rw[csR_def,csB_def,o_assoc,GSYM Swap_def,p12_of_Pa,
    Pa_distr])
(form_goal
 “∀A f: 2 * 2 -> A. csB(f o Swap(2,2)) = csR(f)”));

val csR_csB' = prove_store("csR_csB'",
e0
(rw[csR_def,csB_def,o_assoc,GSYM Swap_def,p12_of_Pa,
    Pa_distr])
(form_goal
 “∀A f: 2 * 2 -> A. csR(f o Swap(2,2)) = csB(f)”));

val pT_def = qdefine_fsym("pT",[‘h:X->Exp(A,B)’])
‘Pt(h) o Swap(X,A)’ |> gen_all 


val Cr1_iso = prove_store("Cr1_iso",
e0
(strip_tac >> rw[p12_of_Pa,Pa_distr,one_to_one_Id] >>
 flip_tac >> irule is_Pa >> rw[IdL,IdR,To1_def])
(form_goal “∀A. p1(A,1) o Pa(Id(A),To1(A)) = Id(A) & 
                Pa(Id(A),To1(A)) o p1(A,1) = Id(A * 1)”));



val o_Cr1_eq = prove_store("o_Cr1_eq",
e0
(cheat)
(form_goal
 “∀A B.
  (∀f:A->B g. f o p1(A,1) = g o p1(A,1) ⇔ f = g) ∧ 
  (∀f:A * 1->B g. f o Pa(Id(A),To1(A)) = g o Pa(Id(A),To1(A)) ⇔ 
  f = g)”));


val is_Tp = prove_store("is_Tp",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘B’,‘X’,‘f’] (assume_tac o conjE2) Tp_def>>
 first_x_assum irule >> arw[])
(form_goal
 “!A B X f:A * X ->B h:X-> Exp(A,B). 
  Ev(A,B) o Pa(p1(A,X),h o p2(A,X)) = f ==> h = Tp(f)”));

val Ev_eq_eq = prove_store("Ev_eq_eq",
e0
(rpt strip_tac >> 
 qsuff_tac ‘f = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X))) & 
  g = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X)))’
 >-- (rpt strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Tp >> first_x_assum accept_tac) >>
 irule is_Tp >> rw[])
(form_goal
 “!A B X f g. Ev(A,B) o Pa(p1(A,X),f o p2(A,X)) = 
              Ev(A,B) o Pa(p1(A,X),g o p2(A,X)) ==> f = g”));

val Pt_eq_eq = prove_store("Pt_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 irule Ev_eq_eq >> arw[GSYM Pt_def])
(form_goal
 “∀A B X f:X-> Exp(A,B) g. Pt(f) = Pt(g) ⇔f = g”));

val Pt_Tp = prove_store("Pt_Tp",
e0
(rw[Pt_def,Ev_of_Tp])
(form_goal
 “∀A B X f:A * X -> B. Pt(Tp(f)) = f”));

val Tp_Pt = prove_store("Tp_Pt",
e0
(rpt strip_tac >> rw[Pt_def] >> flip_tac >> irule is_Tp >>
 rw[])
(form_goal
 “∀A B X f:X -> Exp(A,B). Tp(Pt(f)) = f”));


val Thm6_0 = prove_store("Thm6_0",
e0
(strip_tac >> 
strip_tac >> strip_tac >> strip_tac >> 
 irule Thm6_vertical >>
 rw[cpsb_def] >> fs[GSYM csL_csT,GSYM csR_csB]  >>
 fs[GSYM pT_def] >> flip_tac >>
 qby_tac ‘Pt(Tp(pT(s1))) = pT(s1)’ >-- rw[Pt_Tp] >>
 qby_tac
 ‘csB(Pt(Tp(pT(s1)))) = csT(Pt(Tp(pT(s2))))’
 >-- arw[Pt_Tp] >>
 pop_assum mp_tac >> pop_assum_list (K all_tac) >>
 strip_tac >> fs[csB_cod,csT_dom] >>
 fs[o_Cr1_eq,Pt_eq_eq])
(form_goal
 “∀A s1:2 -> Exp(2,A) s2. 
  csR(Pt(s1)) = csL(Pt(s2)) ⇒ 
  csL(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csL(Pt(Tp(pT(s2)))) @ csL(Pt(Tp(pT(s1)))) &
  csR(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csR(Pt(Tp(pT(s2)))) @ csR(Pt(Tp(pT(s1))))”));

val Thm6 = Thm6_0 |> rewr_rule[Pt_Tp] |> store_as "Thm6";

val Thm6_0_full = prove_store("Thm6_0",
e0
(strip_tac >> 
strip_tac >> strip_tac >> strip_tac >> 
 irule Thm6_vertical_full >>
 rw[cpsb_def] >> fs[GSYM csL_csT,GSYM csR_csB]  >>
 fs[GSYM pT_def] >> flip_tac >>
 qby_tac ‘Pt(Tp(pT(s1))) = pT(s1)’ >-- rw[Pt_Tp] >>
 qby_tac
 ‘csB(Pt(Tp(pT(s1)))) = csT(Pt(Tp(pT(s2))))’
 >-- arw[Pt_Tp] >>
 pop_assum mp_tac >> pop_assum_list (K all_tac) >>
 strip_tac >> fs[csB_cod,csT_dom] >>
 fs[o_Cr1_eq,Pt_eq_eq])
(form_goal
 “∀A s1:2 -> Exp(2,A) s2. 
  csR(Pt(s1)) = csL(Pt(s2)) ⇒ 
  csL(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csL(Pt(Tp(pT(s2)))) @ csL(Pt(Tp(pT(s1)))) &
  csR(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csR(Pt(Tp(pT(s2)))) @ csR(Pt(Tp(pT(s1))))  & 
  csT(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csT(Pt(Tp(pT(s1)))) & 
  csB(Pt(Tp(pT(s2)) @ Tp(pT(s1)))) = 
  csB(Pt(Tp(pT(s2))))”));

val Thm6_full = Thm6_0_full |> rewr_rule[Pt_Tp] 
                            |> store_as "Thm6_full";

val Pt_def_alt = prove_store("Pt_def_alt",
e0
(rw[pT_def,Swap_Swap_Id,IdR,o_assoc])
(form_goal “∀A B X f:X -> Exp(A,B). 
 Pt(f) = pT(f) o Swap(A,X)”));

val csL_csT_Pt = prove_store("csL_csT_Pt",
e0
(rw[Pt_def_alt,csL_csT])
(form_goal
 “∀A s:2->Exp(2,A).csL(pT(s)) = csT(Pt(s))”));

val csT_csL_pT = prove_store("csT_csL_pT",
e0
(rw[GSYM csL_csT,pT_def])
(form_goal
 “∀A s:2->Exp(2,A).csT(pT(s)) = csL(Pt(s))”));

val csR_csB_Pt = prove_store("csR_csB_Pt",
e0
(rw[Pt_def_alt,csR_csB])
(form_goal
 “∀A s:2->Exp(2,A).csR(pT(s)) = csB(Pt(s))”));

val csB_csR_pT = prove_store("csB_csR_pT",
e0
(rw[GSYM csR_csB,pT_def])
(form_goal
 “∀A s:2->Exp(2,A).csB(pT(s)) = csR(Pt(s))”));

val Thm6_ex_0 = prove_store("Thm6_ex_0",
e0
(rpt strip_tac >> drule Thm6_full >>
 qexists_tac ‘Pt(Tp(pT(s2)) @ Tp(pT(s1)))’ >>
 arw[csL_csT_Pt,csR_csB_Pt,csT_csL_pT,csB_csR_pT])
(form_goal
 “∀A s1:2->Exp(2,A) s2. 
  csR(Pt(s1)) = csL(Pt(s2)) ⇒ 
  ∃s. csL(s) = csT(Pt(s2)) @ csT(Pt(s1)) & 
      csR(s) = csB(Pt(s2)) @ csB(Pt(s1)) &
      csT(s) = csL(Pt(s1)) & 
      csB(s) = csR(Pt(s2))”));

val cs_Swap = prove_store("cs_Swap",
e0
(rw[csT_def,csB_def,csL_def,csR_def,o_assoc,
    GSYM Swap_def,p12_of_Pa,Pa_distr])
(form_goal
 “∀A s: 2 * 2 ->A.
  csT(s o Swap(2, 2)) = csL(s) ∧
  csB(s o Swap(2, 2)) = csR(s) ∧
  csL(s o Swap(2, 2)) = csT(s) ∧
  csR(s o Swap(2, 2)) = csB(s)”));

val Thm6_ex = prove_store("Thm6_ex",
e0
(rpt strip_tac >> drule Thm6_ex_0 >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘s o Swap(2,2)’ >>
 arw[cs_Swap])
(form_goal
 “∀A s1:2->Exp(2,A) s2. 
  csR(Pt(s1)) = csL(Pt(s2)) ⇒ 
  ∃s. csT(s) = csT(Pt(s2)) @ csT(Pt(s1)) & 
      csB(s) = csB(Pt(s2)) @ csB(Pt(s1)) &
      csL(s) = csL(Pt(s1)) & 
      csR(s) = csR(Pt(s2))”));

val Thm6_vertical_ex = prove_store("Thm6_vertical_ex",
e0
(rpt strip_tac >>
 qby_tac ‘cpsb(s2,s1)’ 
 >-- (rw[cpsb_def] >> fs[csB_cod,csT_dom,o_Cr1_eq,Pt_eq_eq])>>
 drule Thm6_vertical_full >>
 qexists_tac ‘Pt(s2 @ s1)’ >> arw[])
(form_goal
 “∀A s1:2->Exp(2,A) s2. 
  csB(Pt(s1)) = csT(Pt(s2)) ⇒ 
  ∃s. csL(s) = csL(Pt(s2)) @ csL(Pt(s1)) & 
      csR(s) = csR(Pt(s2)) @ csR(Pt(s1)) &
      csT(s) = csT(Pt(s1)) & 
      csB(s) = csB(Pt(s2))”));

val cs_vertical_ex = prove_store("cs_vertical_ex",
e0
(rpt strip_tac >>
 qsspecl_then [‘Tp(s1)’,‘Tp(s2)’] assume_tac
 Thm6_vertical_ex >>
 rfs[Pt_Tp] >> qexists_tac ‘s’ >> arw[])
(form_goal
 “∀A s1: 2 * 2 -> A s2: 2 * 2 -> A.
   csB(s1) = csT(s2) ⇒
  ∃s. csL(s) = csL(s2) @ csL(s1) ∧
      csR(s) = csR(s2) @ csR(s1) ∧
      csT(s) = csT(s1) ∧
      csB(s) = csB(s2)
  ”));

val cs_horizontal_ex = prove_store("cs_horizontal_ex",
e0
(rpt strip_tac >>
 qsspecl_then [‘Tp(s1)’,‘Tp(s2)’] assume_tac
 Thm6_ex >>
 rfs[Pt_Tp] >> qexists_tac ‘s’ >> arw[])
(form_goal
 “∀A s1: 2 * 2 -> A s2: 2 * 2 -> A.
   csR(s1) = csL(s2) ⇒
  ∃s. csT(s) = csT(s2) @ csT(s1) ∧
      csB(s) = csB(s2) @ csB(s1) ∧
      csL(s) = csL(s1) ∧
      csR(s) = csR(s2)
  ”));

val id_def = qdefine_fsym("id",[‘a:1->A’])
‘a o To1(2)’ |> gen_all 



val cs_hpara_ex = prove_store("cs_vpara_ex",
e0
(cheat)
(form_goal
 “∀A f:2->A. ∃s: 2 * 2 -> A. 
  csL(s) = id(dom(f)) ∧ csR(s) = id(cod(f)) ∧ 
  csT(s) = f ∧ csB(s) = f”));

val cs_vpara_ex = prove_store("cs_vpara_ex",
e0
(cheat)
(form_goal
 “∀A f:2->A. ∃s: 2 * 2 -> A. 
  csL(s) = f ∧ csR(s) = f ∧ 
  csT(s) = id(dom(f)) ∧ csB(s) = id(cod(f))”));

val cs_lu_ex = prove_store("cs_lu_ex",
e0
(cheat)
(form_goal
 “∀A f:2->A. ∃s: 2 * 2 -> A. 
  csL(s) = f ∧ csR(s) = id(cod(f)) ∧ 
  csT(s) = f ∧ csB(s) = id(cod(f))”));


val cs_rl_ex = prove_store("cs_rl_ex",
e0
(cheat)
(form_goal
 “∀A f:2->A. ∃s: 2 * 2 -> A. 
  csL(s) = id(dom(f)) ∧ csR(s) = f ∧ 
  csT(s) = id(dom(f)) ∧ csB(s) = f”));

val id1 = prove_store("id1",
e0
(rw[id_def,dom_def,cod_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. dom(id(a)) = a ∧ cod(id(a)) = a ”));

val id_isid = prove_store("id_isid",
e0
(rw[isid_def,id_def] >> rpt strip_tac >>
 qexists_tac ‘a’ >> rw[])
(form_goal
 “∀A a:1->A. isid(id(a))”));

val idL = prove_store("idL",
e0
(rpt strip_tac >> qsspecl_then [‘cod(f)’] assume_tac id_isid>>
 drule Thm5_1 >> first_x_assum irule >>
 rw[cpsb_def,id1])
(form_goal “∀A f:2->A. id(cod(f)) @ f = f”));

val idR = prove_store("idR",
e0
(rpt strip_tac >> qsspecl_then [‘dom(f)’] assume_tac id_isid>>
 drule Thm5_2 >> first_x_assum irule >>
 rw[cpsb_def,id1])
(form_goal “∀A f:2->A. f @ id(dom(f)) = f”));

val oa_oa_dom_cod = prove_store("oa_oa_dom_cod",
e0
(rpt gen_tac >> rpt disch_tac >>
 drule $ GSYM oa_dom_cod >>
 rev_drule $ GSYM oa_dom_cod >>
 arw[])
(form_goal
 “∀A f g:2->A f' g'. g @ f = g' @ f' ⇒ cpsb(g,f) ⇒ 
 cpsb(g',f') ⇒ 
 dom(f') = dom(f) ∧ cod(g') = cod(g)”));

val Thm7 = prove_store("Thm7",
e0
(rpt strip_tac >> 
 qsspecl_then [‘f’] 
 (x_choose_then "s1" strip_assume_tac) cs_hpara_ex >>
 qsspecl_then [‘g’]
 (x_choose_then "s2" strip_assume_tac) cs_rl_ex >>
 qsspecl_then [‘f'’]
 (x_choose_then "s3" strip_assume_tac) cs_lu_ex >>
 qsspecl_then [‘g'’]
 (x_choose_then "s4" strip_assume_tac) cs_hpara_ex >>
 qby_tac ‘csR(s1) = csL(s2)’
 >-- fs[cpsb_def] >>
 drule cs_horizontal_ex >>
 pop_assum (x_choose_then "S1" strip_assume_tac) >>
 qby_tac ‘csR(s3) = csL(s4)’
 >-- fs[cpsb_def] >>
 drule cs_horizontal_ex >>
 pop_assum (x_choose_then "S2" strip_assume_tac) >>
 qby_tac ‘csB(S1) = csT(S2)’ >-- arw[] >>
 drule cs_vertical_ex >>
 pop_assum strip_assume_tac >> 
 qexists_tac ‘s’ >> arw[idL,idR] >>
 fs[cpsb_def] >> rw[idL] >>
 rev_drule oa_oa_dom_cod >> rfs[cpsb_def] >>
 rw[idL,idR] >> 
 qpick_x_assum ‘dom(g') = cod(f')’ (assume_tac o GSYM) >>
 arw[idR] >>
 qpick_x_assum ‘dom(f') = dom(f)’ (assume_tac o GSYM) >>
 arw[idR])
(form_goal
 “!A f:2->A g f' g'. 
   cpsb(g,f) & cpsb(g',f') & 
   g @ f = g' @ f' ==>
   ?q: 2* 2->A.
   csT(q) = f & 
   csR(q) = g &
   csL(q) = f' &
   csB(q) = g'  
   ”));

(*former Poa_ab Poa_ab_eqn are tri_def and tri_eqns*)


val cs2_RT_cpsb = prove_store("cs2_RT_cpsb",
e0
(rw[cpsb_def,dom_def,cod_def] >> irule to_P_eq >>
 rw[p12_of_Pa,GSYM o_assoc,one_def,two_def,zero_def] >>
 rw[o_assoc,one_to_one_Id,IdL,IdR])
(form_goal “cpsb(Pa(𝟙, 𝟚),Pa(𝟚, 𝟘))”));

val cs2_BL_cpsb = prove_store("cs2_BL_cpsb",
e0
(rw[cpsb_def,dom_def,cod_def] >> irule to_P_eq >>
 rw[p12_of_Pa,GSYM o_assoc,one_def,two_def,zero_def] >>
 rw[o_assoc,one_to_one_Id,IdL,IdR])
(form_goal “cpsb(Pa(𝟚, 𝟙),Pa(𝟘, 𝟚))”));

val tri_eqns' = rewr_rule[GSYM cpsb_def] tri_eqns 

val o4_middle = prove_store("o4_middle",
e0
(rw[o_assoc])
(form_goal “∀A B C D K f:A->B g:B->C h:C->D j:D->K.
 j o h o g o f = j o (h o g) o f”));

val RT_cs2 = prove_store("RT_cs2",
e0
(assume_tac cs2_RT_cpsb >> rw[oa_def] >>
 irule to_P_eq >> rw[p12_of_Pa] >> strip_tac >> 
 irule dom_cod_is_two >> rw[dom_def,cod_def,o_assoc,CC4_1] >> drule tri_eqns' >> arw[o4_middle] >>
 rw[GSYM o_assoc,p12_of_Pa,one_def,two_def,zero_def,IdL] >>
 rw[o_assoc,one_to_one_Id,IdR])
(form_goal “Pa(𝟙, 𝟚) @ Pa(𝟚, 𝟘) = Pa(𝟚,𝟚)”));


val BL_cs2 = prove_store("BL_cs2",
e0
(assume_tac cs2_BL_cpsb >> rw[oa_def] >>
 irule to_P_eq >> rw[p12_of_Pa] >> strip_tac >> 
 irule dom_cod_is_two >> rw[dom_def,cod_def,o_assoc,CC4_1] >>
 drule tri_eqns' >> 
 arw[o4_middle] >>
 rw[GSYM o_assoc,p12_of_Pa,one_def,two_def,zero_def,IdL] >>
 rw[o_assoc,one_to_one_Id,IdR])
(form_goal “Pa(𝟚, 𝟙) @ Pa(𝟘, 𝟚) = Pa(𝟚,𝟚)”));

val cs_comm = prove_store("cs_comm",
e0
(rpt strip_tac >> 
 rw[csR_def,csT_def,csB_def,csL_def] >>
 assume_tac cs2_BL_cpsb >>
 assume_tac cs2_RT_cpsb >> 
 drule $ GSYM fun_pres_oa >> arw[] >>
 rev_drule $ GSYM fun_pres_oa >> arw[] >>
 rw[BL_cs2,RT_cs2]) 
(form_goal “∀A s: 2 * 2 ->A. csR(s) @ csT(s) = csB(s) @ csL(s)”));

val Thm8 = prove_store("Thm8",
e0
(rpt strip_tac >>
 drule $ iffLR cpsb_def >> rev_drule $ iffLR cpsb_def >>
 qby_tac ‘∃q: 2 * 2 -> A. csT(q) = h & csR(q) = g & 
 csL(q) = h ∧ csB(q) = g’
 >-- (irule Thm7 >> arw[]) >> 
 pop_assum strip_assume_tac >> 
 qby_tac ‘∃p: 2 * 2 -> A. csT(p) = g & csR(p) = f & 
 csL(p) = g ∧ csB(p) = f’
 >-- (irule Thm7 >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘csR(q) = csL(p)’ >-- arw[] >>
 drule cs_horizontal_ex >>
 pop_assum strip_assume_tac >>
 qsspecl_then [‘s’] assume_tac cs_comm >>
 rfs[])
(form_goal
 “∀A f:2->A g h. cpsb(g,h) ∧ cpsb(f,g) ⇒ 
 (f @ g) @ h = f @ g @ h”));

val iso_def = qdefine_psym("iso",[‘f:2->A’])
‘?g:2->A. dom(g) = cod(f) & dom(f) = cod(g) &
 g @ f = dom(f) o To1(2) & f @ g = cod(f) o To1(2)’
|> gen_all


val CC5 = store_ax("CC5",
“∀A B. 
 (∀f:2->A. ∃!g:2->B. R(f,g)) ∧
 (∀f:2->A g:2->B. R(f,g) ⇒ 
  R(id(dom(f)),id(dom(g))) ∧ R(id(cod(f)),id(cod(g)))) ∧
 (∀f:2->A g:2->A h: 2->B. cpsb(g,f) ⇒
  R(g @ f, h) ⇒ ∀f1 g1. R(f,f1) ∧ R(g,g1) ⇒ h = g1 @ f1) ⇒
 ∃cf:A->B. ∀a:2->A b:2->B. R(a,b) ⇔ cf o a = b”)


val one2one_def = qdefine_psym("one2one",[‘f:A->B’]) 
‘∀a1:2->A a2:2->A. f o a1 = f o a2 ⇒ a1 = a2’ 
|> gen_all 

val onto_def = qdefine_psym("onto",[‘f:A->B’])
‘∀b:2->B. ∃a:2->A. b = f o a’ |> gen_all


val fun_ext = prove_store("fun_ext",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 ccontra_tac >> drule CC2_2 >>
 pop_assum strip_assume_tac >>
 rfs[])
(form_goal “∀A B f:A->B g. (∀a:2->A. f o a = g o a) ⇔ f = g”));


val fun_of_id = prove_store("fun_of_id",
e0
(rw[id_def,dom_def,o_assoc,cod_def])
(form_goal “∀A B f:A->B g:2->A. id(dom(f o g)) = f o id(dom(g)) ∧
  id(cod(f o g)) = f o id(cod(g))”));


local
val l = CC5 |> qspecl [‘B’,‘A’] |>
fVar_sInst_th 
“R(b:2->B,a:2->A)”
“b:2->B = f o a:2->A”
in
val Thm9 = prove_store("Thm9",
e0
(rpt strip_tac >> rw[Iso_def] >> 
 assume_tac l >>
 qsuff_tac
 ‘∃cf:B->A. ∀b:2->B a:2->A. b = f o a ⇔ cf o b = a’
 >-- (strip_tac >>
 qexists_tac ‘cf’ >>
 pop_assum (assume_tac o GSYM) >> 
 once_arw[GSYM fun_ext] >> arw[o_assoc,IdL] >>
 dflip_tac >> pop_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum irule >> rpt strip_tac (* 4 *)
 >-- arw[fun_of_id]
 >-- arw[fun_of_id]
 >-- (uex_tac >> fs[onto_def] >>
     first_x_assum (qspecl_then [‘f'’] strip_assume_tac) >>
     qexists_tac ‘a’ >> arw[] >> rpt strip_tac >>
     fs[one2one_def] >> first_x_assum irule >> arw[]) >>
 (fs[] >> 
 qby_tac ‘cpsb(g1,f1)’ 
 >-- (fs[cpsb_def,dom_def,cod_def,o_assoc,one2one_def] >>  
     qsuff_tac ‘g1 o 0f o To1(2) = f1 o 1f o To1(2)’
     >-- (strip_tac >> ccontra_tac >> drule CC2_2 >>
         fs[To1_def,o_assoc]) >>
     first_x_assum irule >> fs[GSYM o_assoc]) >>
 drule $ GSYM fun_pres_oa >> 
 fs[] >> fs[one2one_def] >> first_x_assum irule >> arw[]))
(form_goal
 “∀A B f:A->B. one2one(f) ∧ onto(f) ⇒ Iso(f)”));
end


val Mono_one2one = prove_store("Mono_one2one",
e0
(rw[Mono_def,one2one_def] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal “∀A B f:A->B. Mono(f) ⇒ one2one(f)”));

val isPb_expand = isPb_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : A -> P. p:P->X o a = u & q:P->Y o a = v”) |> store_as "isPb_expand";

val Pb_Mono_Mono = prove_store("Pb_Mono_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 drule $ iffLR isPb_expand >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘f o p o h = g o q o h’ >--
 (strip_tac >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘g' = a & h = a’ >-- 
 (strip_tac >> arw[]) >> strip_tac >> 
 first_x_assum irule >> arw[] >>
 fs[Mono_def] >> first_x_assum irule >> 
 qpick_x_assum ‘f o p = g o q’ (assume_tac o GSYM) >>
 arw[GSYM o_assoc] >> arw[o_assoc]) >>
 arw[GSYM o_assoc])
(form_goal
 “!X Z f:X->Z Y g:Y->Z P p:P->X q:P->Y. 
  isPb(f,g,p,q) ==> Mono(g) ==> Mono(p)”));

val Thm10 = prove_store("Thm10",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac 
 >-- (rfs[o_assoc] >> qexists_tac ‘i0 o ai’ >> rw[]) >>
 qsspecl_then [‘i’,‘j’] strip_assume_tac isPb_ex >>
 qby_tac ‘Iso(p)’
 >-- (irule Thm9 >> 
     drule Pb_Mono_Mono >> first_x_assum drule >> 
     drule Mono_one2one >> arw[] >>
     rw[onto_def] >> strip_tac >>
     drule $ iffLR isPb_def >> fs[] >>
     first_x_assum (qsspecl_then [‘i o b’,‘b’] assume_tac) >>
     fs[] >>
     first_x_assum drule >> 
     pop_assum (assume_tac o uex_expand) >> fs[] >>
     qexists_tac ‘a’ >> arw[]) >>
 fs[Iso_def] >> qexists_tac ‘q o f'’ >> arw[] >>
 drule $ iffLR isPb_def >> pop_assum (assume_tac o GSYM) >>
 arw[GSYM o_assoc] >> arw[o_assoc,IdR])
(form_goal
 “∀I A i:I->A J j:J->A. Mono(i) ∧ Mono(j) ⇒
  ((∃i0:I->J. i = j o i0) ⇔ 
   (∀a:2->A ai:2->I. a = i o ai ⇒ ∃aj:2->J. a = j o aj))”));


val ba_cpsb = prove_store("ba_cpsb",
e0
(rw[cpsb_def] >> assume_tac CC4_2 >> fs[isPo_def,dom_def,cod_def])
(form_goal
 “cpsb(β,α)”));

val oa_ba = prove_store("oa_ba",
e0
(assume_tac ba_cpsb >> rw[oa_def] >> arw[] >>
 fs[cpsb_def] >> drule tri_def >> fs[] >>
 first_x_assum (qspecl_then [‘Id(3)’] assume_tac) >>
 fs[IdL] >> pop_assum (assume_tac o GSYM) >> arw[IdL])
(form_goal “β @ α = γ”));


val tri_ab_Id = prove_store("tri_ab_Id",
e0
(assume_tac ba_cpsb >> fs[cpsb_def] >> drule tri_def >>
 rfs[] >> flip_tac >> first_x_assum irule >>
 rw[IdL])
(form_goal “tri(α,β) = Id(3)”));


val t2tt_cases = prove_store("t2tt_cases",
e0
(cheat)
(form_goal “∀f: 2 -> 2 * 2. 
 f = Pa(𝟚, 𝟘) | f = Pa(𝟙, 𝟚) | f = Pa(𝟘, 𝟚) | f = Pa(𝟚, 𝟙) | 
 f = Pa(𝟚, 𝟚) | 
 f = id(Pa(0f,0f)) | f = id(Pa(1f,0f)) |
 f = id(Pa(0f,1f)) | f = id(Pa(1f,1f))”));
 
val t2tt_dom_cod = prove_store("t2tt_dom_cod",
e0
(cheat)
(form_goal “dom(Pa(𝟚, 𝟘)) = Pa(0f,0f) ∧ dom(Pa(𝟙, 𝟚)) = Pa(1f, 0f) ∧ dom(Pa(𝟚, 𝟙)) = Pa(0f, 1f) ∧ cod(Pa(𝟙, 𝟚)) = Pa(1f, 1f) ∧
 cod(Pa(𝟚,𝟘)) = Pa(1f,0f)”));

val Thm11 = prove_store("Thm11",
e0
(qsuff_tac
 ‘∃P: 3 -> 2 * 2 i. i o P = Id(3) ∧ 
  ∀f:2-> 2 * 2. i o f = α | i o f = β | i o f = γ | i o f = id(dom(α)) | i o f = id(cod(β)) | i o f = id(dom(β))’
 >-- (rpt strip_tac >>
     first_x_assum (qspecl_then [‘P o f’] assume_tac) >>
     rfs[GSYM o_assoc,IdL]) >>
 qsuff_tac ‘∃P:3->2 * 2. P o α = Pa(𝟚,𝟘) ∧ P o β = Pa(𝟙,𝟚) ∧ P o γ = Pa(𝟚,𝟚) ∧ ∃i: 2 * 2 -> 3. csT(i) = α ∧ csR(i) = β ∧ csL(i) = id(dom(α)) ∧ csB(i) = γ’
 >-- (strip_tac >>
     qexistsl_tac [‘P’,‘i’] >> 
     fs[csT_def,csR_def,csL_def,csB_def] >>
     qby_tac ‘i o P = Id(3)’
     >-- (rw[GSYM tri_ab_Id] >>
         assume_tac tri_def >> fs[GSYM cpsb_def] >>
         assume_tac ba_cpsb >> first_x_assum drule >>
         fs[] >> first_x_assum irule >> arw[o_assoc]) >>
     arw[] >> strip_tac >>
     qsspecl_then [‘f’] strip_assume_tac t2tt_cases >>
     fs[] (* 5 *)
     >-- (*𝟚,𝟚 case*) (rw[GSYM RT_cs2] >>
         assume_tac cs2_RT_cpsb >> drule fun_pres_oa >>
         arw[oa_ba])
     >-- (qpick_x_assum ‘i o Pa(𝟚, 𝟘) = α’ (assume_tac o GSYM) >>
         arw[fun_of_id,t2tt_dom_cod]) 
     >-- (qpick_x_assum ‘i o Pa(𝟙, 𝟚) = β’ (assume_tac o GSYM) >>
         arw[fun_of_id,t2tt_dom_cod]) 
     >-- (qpick_x_assum ‘i o Pa(𝟚, 𝟙) = γ’ (assume_tac o GSYM) >>
          assume_tac CC4_1 >> fs[GSYM dom_def] >>
          qpick_x_assum ‘dom(γ) = dom(α)’ (assume_tac o GSYM) >>
          arw[fun_of_id,t2tt_dom_cod]) >>
     qpick_x_assum ‘i o Pa(𝟙, 𝟚) = β’ (assume_tac o GSYM) >>
     arw[fun_of_id,t2tt_dom_cod] >> 
     assume_tac CC4_1 >> fs[GSYM dom_def] >>
     qpick_x_assum ‘dom(γ) = dom(α)’ (assume_tac o GSYM) >>
     arw[fun_of_id,t2tt_dom_cod]) >> 
 qby_tac ‘dom(Pa(𝟙,𝟚)) = cod(Pa(𝟚,𝟘))’ 
 >-- rw[t2tt_dom_cod] >>
 drule tri_def >>
 qexists_tac ‘tri(Pa(𝟚, 𝟘), Pa(𝟙, 𝟚))’ >>
 arw[] >>
 rw[GSYM oa_ba] >> assume_tac ba_cpsb >> drule fun_pres_oa >>
 arw[RT_cs2] >>
 irule Thm7 >> cheat(*trivial*)
     )
(form_goal “∀f:2->3. f = α | f = β | f = γ | f = id(dom(α)) | f = id(cod(β)) | f = id(dom(β))”));


val _ = add_parse (int_of "η")

val cpnt_def = qdefine_fsym("cpnt",
[‘η:A -> Exp(2,B)’,‘a:1->A’])
‘Pt(η o a) o Pa(Id(2),To1(2))’
|> gen_all


val Nt_def = qdefine_psym("Nt",
[‘η:A -> Exp(2,B)’,‘F:A->B’,‘G:A->B’])
‘(∀f:2->A. csL(Pt(η o f)) = F o f ∧ csR(Pt(η o f)) = G o f)’ |> qgenl [‘A’,‘B’,‘F’,‘G’,‘η’]


val all_Nt = prove_store("all_Nt",
e0
(cheat)
(form_goal “∀A B η:A -> Exp(2,B). 
 Nt(η,Er1(B) o  Ed(0f,B) o η, Er1(B) o Ed(1f,B) o η)”));

val ID_def = qdefine_psym("ID",[‘F:A->B’])
‘Tp(F o p2(2,A))’ |> gen_all

val Ec_def = qdefine_fsym("Ec",[‘f:A->B’,‘C’])
‘Tp(f o Ev(C,A))’ |> gen_all


val Rw_def = qdefine_fsym("Rw",[‘H:B->C’,‘η:A->Exp(2,B)’])
‘Ec(H,2) o η’ |> gen_all

val Lw_def = qdefine_fsym("Lw",[‘η:A->Exp(2,B)’,‘H:X->A’])
‘η o H’ |> gen_all


val Ed_Po_Pb = prove_store("Ed_Po_Pb",
e0
(cheat)
(form_goal “∀X Y f:X->Y Z g:X->Z P p:Y->P q:Z->P. isPo(f,g,p,q) ⇒
 ∀A. isPb(Ed(f,A),Ed(g,A),Ed(p,A),Ed(q,A))”));

val Ed_ab_Pb0 = prove_store("Ed_ab_Pb0",
e0
(strip_tac >> irule Ed_Po_Pb >> rw[CC4_2])
(form_goal “∀A.isPb(Ed(1f,A),Ed(0f,A),Ed(α,A),Ed(β,A))”));

(*

until Thm13, missing, need to reread.
*)

(*as reverse of tri...*)


val Ed_ab_Pb = prove_store("Ed_ab_Pb",
e0
(cheat)
(form_goal “∀A.isPb(Er1(A) o Ed(1f,A),Er1(A) o Ed(0f,A),Ed(α,A),Ed(β,A))”));

Ed_ab_Pb |> rewr_rule[isPb_def] |> qspecl [‘B’]
|>conjE2

val irt_uex = proved_th $
e0
cheat
(form_goal
 “∀A B η:A->Exp(2,B) ε:A -> Exp(2,B).
  ?!a:A -> Exp(3,B). 
   (Ed(1f,B) o η = Ed(0f,B) o ε &
    Ed(α,B) o a = η & Ed(β,B) o a = ε) |
   (~(Ed(1f,B) o η = Ed(0f,B) o ε) &
    a = Ed(0f o To1(3),B) o η)”)

val irt_def0 = irt_uex |> spec_all
                       |> qsimple_uex_spec "irt" [‘η’,‘ε’] 

val irt_def = proved_th $
e0
cheat
(form_goal
 “∀A B η:A->Exp(2,B) ε:A -> Exp(2,B).
  Ed(1f,B) o η = Ed(0f,B) o ε ⇒
  (Ed(α,B) o irt(η,ε) = η & Ed(β,B) o irt(η,ε) = ε)  &
  (∀a'. Ed(α,B) o a' = η & Ed(β,B) o a' = ε ⇒
   a' = irt(η,ε))”)
(*cod η = dom ε *)
val vo_def = 
qdefine_fsym("vo",[‘ε:A-> Exp(2,B)’,‘η:A->Exp(2,B)’])
‘Ed(γ, B) o irt(η,ε)’

val ID_def = 
qdefine_fsym("ID",[‘F:A->B’])
‘Tp(F o p2(2,A))’

val Adj_def = qdefine_psym("Adj",
[‘L:X->A’,‘R:A->X’,‘η:X->Exp(2,X)’,‘ε:A->Exp(2,A)’])
‘vo(Lw(ε,L),Rw(L,η))  = ID(L) ∧ 
 vo(Rw(R,ε),Lw(η,R))  = ID(R)’
|> qgenl [‘A’,‘X’,‘L’,‘R’,‘η’,‘ε’]


val UFrom_def = 
qdefine_psym("UFrom",[‘F:D->C’,‘x:1->C’,‘y:1->D’,‘f:2->C’])
‘ dom(f) = F o y ∧ cod(f) = x ∧
 (∀x':1->D f':2-> C. dom(f') = F o x' ∧ cod(f') = x ⇒
 ∃!fh:2->D. f' = f @ (F o fh))’ 
|> qgenl [‘D’,‘C’,‘F’,‘x’,‘y’,‘f’]


val Thm13 = prove_store("Thm13",
e0
(cheat)
(form_goal
 “∀X A F:X->A. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃!x:1->X f:2->A. cod(f) = a ∧ U(x,f)) ⇒
  ∃!G:A->X η ε:A->Exp(2,A). Adj(F,G,η,ε) ∧
   ∀a:1->A. cod(cpnt(ε,a)) = a ∧ U(G o a,cpnt(ε,a))”));


val CC6 = store_ax("CC6",
“?A f:2->A. iso(f) & ~isid(f)”); 
 
val Tp1_def = qdefine_fsym("Tp1",[‘f:A->B’])
‘Tp(f o p1(A,1))’ |> GSYM |> gen_all

val Tp1_Tp0_inv = prove_store("Tp1_Tp0_inv",
e0
(rpt strip_tac >> rw[GSYM Tp1_def,GSYM Tp0_def] >>
 flip_tac >> irule is_Tp >>
 rw[o_assoc,Pa_distr,IdL] >>
 once_rw[To1_def] >> rw[])
(form_goal
 “!X Y f:1-> Exp(X,Y). Tp1(Tp0(f)) = f”));

val Tp0_Tp1_inv = prove_store("Tp0_Tp1_inv",
e0
(rpt strip_tac >> rw[GSYM Tp1_def,GSYM Tp0_def] >>
 rw[Ev_of_Tp_el,o_assoc,p12_of_Pa,IdR])
(form_goal
 “!X Y f:X->Y. Tp0(Tp1(f)) = f”));

val Tp_eq = prove_store("Tp_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (once_rw[GSYM Ev_of_Tp] >> arw[]) >> arw[])
(form_goal
 “!A B X f:A * X ->B g:A * X ->B.Tp(f) = Tp(g) <=> f = g”));

val Tp1_eq_eq = prove_store("Tp1_eq_eq",
e0
(rw[GSYM Tp1_def,Tp_eq,o_Cr1_eq] )
(form_goal “∀A B f:A->B g. Tp1(f) = Tp1(g) ⇔ f = g”));

val id_cod_id = prove_store("id_cod_id",
e0
(rw[id_def,cod_def,o_assoc,To1_def])
(form_goal “∀A g:2->A. id(cod(id(cod(g)))) = id(cod(g))”));

val Thm14 = prove_store("Thm14",
e0
(strip_assume_tac CC6 >> 
 qexistsl_tac [‘Exp(2,A)’,‘Tp1(f)’,‘Tp1(id(dom(f)))’] >>
 qby_tac ‘~(f = id(dom(f)))’ >-- cheat >>
 arw[Tp1_eq_eq] >>
 fs[iso_def] >>
 qsspecl_then [‘f’,‘g’,‘id(dom(f))’,‘id(dom(f))’]
 assume_tac Thm7
 >> rfs[cpsb_def,id1,idL] >>
 qby_tac ‘id(cod(g)) @ id(cod(g)) = 
 id(cod(id(cod(g)))) @ id(cod(g))’ >-- rw[id_cod_id] >>
 fs[idL] >> fs[id_def] >>
 qexists_tac ‘Tp(q)’ >>
 qby_tac ‘dom(Tp(q)) = Tp1(f) &
          cod(Tp(q)) = Tp1(cod(g) o To1(2))’
 >-- (qsspecl_then [‘Tp(q)’] assume_tac csT_dom  >>
 fs[Pt_Tp] >> 
 qpick_x_assum ‘Pt(dom(Tp(q))) o Pa(Id(2), To1(2)) = f’
 (assume_tac o GSYM) >> arw[] >> rw[GSYM Tp1_def] >>
 rw[o_assoc,Cr1_iso,IdR,Tp_Pt] >>
 qsspecl_then [‘Tp(q)’] assume_tac csB_cod >>
 rfs[Pt_Tp] >> arw[GSYM o_assoc] >>
 rw[Cr1_iso,o_assoc,IdR,Tp_Pt]) >>
 qsspecl_then [‘id(cod(g))’,‘f’,‘id(cod(g))’,‘f’]
 assume_tac Thm7 >> rfs[cpsb_def,id1] >>
 qexists_tac ‘Tp(q')’ >>
 qby_tac ‘dom(Tp(q')) = Tp1(cod(g) o To1(2))’
 >-- (qsspecl_then [‘Tp(q')’] assume_tac csT_dom >>
     fs[Pt_Tp] >> 
     qby_tac ‘cod(g) o To1(2) = id(cod(g))’
     >-- rw[id_def,cod_def] >>
     arw[] >>
     qpick_x_assum ‘Pt(dom(Tp(q'))) o Pa(Id(2), To1(2)) = id(cod(g))’ (assume_tac o GSYM) >> arw[] >> 
     rw[Pt_def,o_assoc,p12_of_Pa,Pa_distr,GSYM Tp1_def,
        dom_def,Ev_of_Tp_el,IdL]  >> 
     rw[To1_def] >> 
     irule is_Tp >> rw[o_assoc,Ev_of_Tp_el,To1_def]) >>
 arw[] >>
 qby_tac ‘Tp1(f) = cod(Tp(q'))’
 >-- (rw[GSYM Tp1_def] >> 
     flip_tac >> irule is_Tp >> rw[To1_def] >>
     qsspecl_then [‘Tp(q')’] assume_tac csB_cod >>
     fs[Pt_Tp] >> 
     qpick_x_assum ‘Pt(cod(Tp(q'))) o Pa(Id(2), To1(2)) = f’
     (assume_tac o GSYM) >> arw[] >>
     rw[Pt_def,o_assoc,Pa_distr,p12_of_Pa,IdL,To1_def]) >> 
 arw[] >>
 cheat (*need bunch of lemmas, tedious*)
 )
(form_goal
“?A A1:1->A A2. ~(A1 = A2) &
?f:2->A. dom(f) = A1 & cod(f) = A2 ∧ iso(f)”));

val Thm14' = prove_store("Thm14'",
e0
(strip_assume_tac Thm14 >>
 qexistsl_tac [‘A’,‘A1’,‘A2’,‘f’] >> arw[])
(form_goal “?A A1:1->A A2 f:2->A. ~(A1 = A2) & dom(f) = A1 & cod(f) = A2 ∧ iso(f)”));


val OR_NOT_IMP = prove_store("OR_NOT_IMP",
e0
(cheat)
(form_goal “A | B ⇔ (~A ⇒ B)”));

val id_eq_eq = prove_store("id_eq_eq",
e0
(rw[id_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
qby_tac ‘a o To1(2) o 1f = b o To1(2) o 1f’ 
>-- arw[GSYM o_assoc] >>
fs[one_to_one_Id,IdR])
(form_goal “∀X a:1->X b:1->X. id(a) = id(b) ⇔ a = b”));


val one_oa_id = prove_store("one_oa",
e0
(rw[one_def,GSYM o_assoc] >> rw[GSYM id_def,GSYM cod_def,idL])
(form_goal “∀A f:2->A. (f o 𝟙) @ f = f”));

val o_zero_dom = prove_store("o_zero_dom",
e0
(rw[id_def,dom_def,zero_def,one_to_one_Id,o_assoc])
(form_goal “∀A f:2->A. f o 𝟘 = id(dom(f))”));

val o_one_cod = prove_store("o_zero_cod",
e0
(rw[id_def,cod_def,one_def,one_to_one_Id,o_assoc])
(form_goal “∀A f:2->A. f o 𝟙 = id(cod(f))”));


val l = fVar_sInst_th
“R(b:2->B,c:2->C)”
“(dom(b:2->B) = B0 ∧ ~(cod(b) = B0) ∧ c:2->C = h) |
 (~(dom(b) = B0) ∧ cod(b) = B0 ∧ c = k) |
 (dom(b) = B0 ∧ cod(b) = B0 ∧ c = h o 𝟘) |
 (~(dom(b) = B0) ∧ ~(cod(b) = B0) ∧ c = h o 𝟙)”
(CC5 |> qspecl [‘B’,‘C’])
val Thm15 = prove_store("Thm15",
e0
(rpt strip_tac >>
 x_choosel_then ["C","T1","T2","h"] strip_assume_tac Thm14' >>
 drule $ iffLR iso_def >>
 pop_assum (x_choose_then "k" strip_assume_tac) >>
 ccontra_tac >> fs[Epi_def] >> 
qsuff_tac ‘∃H: B ->C.
 ∀b:2->B. 
 (dom(b) = B0 ∧ ~(cod(b) = B0) ⇒ H o b = h) ∧ 
 (~(dom(b) = B0) ∧ cod(b) = B0 ⇒ H o b = k) ∧ 
 (dom(b) = B0 ∧ cod(b) = B0 ⇒ H o b = h o 𝟘) ∧
 (~(dom(b) = B0) ∧ ~(cod(b) = B0) ⇒ H o b = h o 𝟙)’
>-- (strip_tac >>
     last_x_assum (qsspecl_then [‘H’,‘h o 1f o To1(B)’] assume_tac) >>
     qby_tac ‘H o f = (h o 1f o To1(B)) o f’ 
     >-- (irule $ iffLR fun_ext >> strip_tac >> rw[o_assoc] >>
         qsuff_tac ‘H o f o a = h o 𝟙’
         >-- (strip_tac >> arw[To1_def,one_def]) >>
         first_x_assum (qsspecl_then [‘f o a’] strip_assume_tac) >>
         first_x_assum irule >>
         rw[dom_def,cod_def,o_assoc] >> dflip_tac >> 
         qby_tac ‘∀a0:1->A. ~(B0 = f o a0)’
         >-- (strip_tac >> ccontra_tac >>
             qby_tac ‘∃a0:1->A. B0 = f o a0’
             >-- (qexists_tac ‘a0’ >> arw[]) >>
             rfs[]) >>
         arw[]) >>
     first_x_assum drule >> 
     qby_tac ‘H o id(B0) = h o 1f o To1(B) o id(B0)’
     >-- arw[o_assoc] >>
     qby_tac ‘H o id(B0) = h o 𝟘’
     >-- (first_x_assum (qsspecl_then [‘id(B0)’] strip_assume_tac) >>
         first_x_assum irule >> 
         rw[id_def,dom_def,cod_def,o_assoc,one_to_one_Id,IdR]) >>
     fs[To1_def,GSYM one_def] >> 
     rfs[one_def,zero_def,dom_def,cod_def,GSYM o_assoc] >>
     qby_tac ‘T1 o To1(2) o 1f = T2 o To1(2) o 1f’
     >-- arw[GSYM o_assoc] >> fs[one_to_one_Id,IdR]) >>
 qsuff_tac
 ‘?cf : B->C. 
     !a: 2->B b:2->C.
          dom(a) = B0 & ~(cod(a) = B0) & b = h |
          ~(dom(a) = B0) & cod(a) = B0 & b = k |
          dom(a) = B0 & cod(a) = B0 & b = h o 𝟘 |
          ~(dom(a) = B0) & ~(cod(a) = B0) & b = h o 𝟙 <=> cf o a = b’     
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     strip_tac >> 
     first_x_assum (qspecl_then [‘b’] assume_tac) >>
     cases_on “dom(b:2->B) = B0” >> cases_on “cod(b:2->B) = B0” >> fs[]) >>
 irule l >> strip_tac
 >-- (rpt gen_tac >> 
 cases_on “dom(f':2->B) = B0” >> cases_on “cod(f':2->B) = B0” >>
 arw[] (* 4 *) >>
 strip_tac >> arw[id1,o_zero_dom,o_one_cod]) >>
 strip_tac >-- (strip_tac >> uex_tac >>
 cases_on “dom(f':2->B) = B0” >> cases_on “cod(f':2->B) = B0” >>
 arw[] (* 4 *)
 >-- (qexists_tac ‘h o 𝟘’ >> rpt strip_tac >> arw[])
 >-- (qexists_tac ‘h’ >> rpt strip_tac >> arw[])
 >-- (qexists_tac ‘k’ >> rpt strip_tac >> arw[]) >>
 qexists_tac ‘h o 𝟙’ >> rpt strip_tac >> arw[]) >>
 rpt gen_tac >> strip_tac >> pop_assum mp_tac >> once_rw[cpsb_def] >>
     disch_tac >> 
     qby_tac ‘cod(g @ f') = cod(g) ∧ dom(g @ f') = dom(f')’
     >-- cheat >> 
     qby_tac ‘(h o 𝟙) @ h = h ∧ h @ (h o 𝟘) = h ∧ 
              k @ h = h o 𝟘 ∧ h @ k = h o 𝟙 ∧
              (h o 𝟘) @ k = k ∧ k @ (h o 𝟙) = k ∧ 
              (h o 𝟘) @ h o 𝟘 = (h o 𝟘) ∧
              (h o 𝟙) @ h o 𝟙 = (h o 𝟙)’
     >-- cheat >>
     once_arw[] >>  strip_tac (* 4 *)
     >-- (once_arw[]  >> rw[] >> rpt strip_tac >> arw[]) 
     >-- (once_arw[]  >> rw[] >> rpt strip_tac >> arw[]) 
     >-- (once_arw[]  >> rw[] >> rpt strip_tac >> arw[]) >>
     once_arw[]  >> rw[] >> rpt strip_tac >> arw[])
(form_goal
 “!A B f:A->B. Epi(f) ==> !B0:1->B. ?A0:1->A. B0 = f o A0”))



val is_coPa = coPa_def |> spec_all |> conjE2
                       |> gen_all
                       |> store_as "is_coPa";

val from_coP_component = prove_store("from_coP_component",
 e0
(rpt strip_tac >> irule is_coPa >> rw[])
(form_goal
 “!A B X f:A + B ->X g:A + B->X. f = coPa(f o i1(A,B),f o i2(A,B))”));


val from_coP_eq = prove_store("from_coP_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f = coPa(g o i1(A,B),g o i2(A,B)) &
            g = coPa(g o i1(A,B),g o i2(A,B))’ >--
 (strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >>
 (irule is_coPa >> arw[]))
(form_goal
 “!A B X f:A + B-> X g:A + B->X. f o i1(A,B) = g o i1(A,B) & f o i2(A,B) = g o i2(A,B) ==> f = g”));


val t2t_notid_two = prove_store("t2t_notid_two",
e0
(cheat)
(form_goal “∀f:2->2. ~isid(f) ⇒ f = 𝟚”));

val Thm16 = prove_store("Thm16",
e0
(rpt strip_tac >> 
 qby_tac ‘∃j k. j o i1(A,B) = Id(A) ∧ k o i2(A,B) = Id(B)’
 >-- cheat >>
 pop_assum strip_assume_tac >> 
 qby_tac ‘∀h:A + B -> A + B. 
 (∀f:2->A + B d0:1-> A. dom(f) = i1(A,B) o d0 ⇒ h o f = i1(A,B) o j o f)  ∧ 
 (∀f:2->A + B d0:1-> B. dom(f) = i2(A,B) o d0 ⇒ h o f = i2(A,B) o k o f) ⇒
 h = Id(A + B)’
 >-- (rpt strip_tac >>
     irule from_coP_eq >> rw[IdL] >>
     strip_tac
     >-- (irule $ iffLR fun_ext >>
     rw[o_assoc] >> strip_tac >>
     fs[dom_def] >>
     first_x_assum (qsspecl_then [‘i1(A, B) o a’,‘a o 0f’] assume_tac) >>
     fs[o_assoc] >> 
     qsuff_tac ‘i1(A, B) o (j o i1(A, B)) o a = i1(A, B) o a’ 
     >-- rw[o_assoc] >>
     arw[IdL]) >>
    (irule $ iffLR fun_ext >>
     rw[o_assoc] >> strip_tac >>
     fs[dom_def] >>
     first_x_assum (qsspecl_then [‘i2(A, B) o a’,‘a o 0f’] assume_tac) >>
     fs[o_assoc] >> 
     qsuff_tac ‘i2(A, B) o (k o i2(A, B)) o a = i2(A, B) o a’ 
     >-- rw[o_assoc] >>
     arw[IdL] )) >>
 qby_tac ‘∃l: A + B -> 2. (∀a : 1->A. l o i1(A,B) o a = 0f) ∧ 
                          (∀b:1->B. l o i2(A,B) o b = 1f)’ 
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qby_tac ‘∀p:2->A + B d0:1->B. dom(p) = i2(A,B) o d0 ⇒ 
 ~(∃c0:1->A. cod(p) = i1(A,B) o c0)’
 >-- (rpt strip_tac >>
     ccontra_tac >> pop_assum strip_assume_tac >> 
 cases_on “isid(l:A + B ->2 o p: 2 -> A + B)”    
 >-- (fs[isid_def] >> 
     qby_tac ‘l o p o 1f = l o p o 0f’
     >-- (arw[GSYM o_assoc] >> rw[one_to_one_Id,IdR,o_assoc]) >>
     rfs[dom_def,cod_def,zf_ne_of]) >>
 drule t2t_notid_two >> 
 qby_tac ‘l o p o 1f = 1f ∧ l o p o 0f = 0f’
 >-- (strip_tac >> arw[GSYM o_assoc,two_def,IdL]) >>
 rfs[dom_def,cod_def,zf_ne_of]) >> 
 cheat
 )
(form_goal
 “!A B f:2->A + B. (?f0:2->A. f = i1(A,B) o f0) |
                   (?f0:2->B. f = i2(A,B) o f0)”));

val FSC_def = qdefine_psym("FSC",[‘i:S->A’])
‘Mono(i) & 
 !f:2->A d:1->S c:1->S. dom(f) = i o d & cod(f) = i o c ==> 
 ?f0:2->S. f = i o f0’ 
|> qgenl [‘S’,‘A’,‘i’]

val FSCC_def = qdefine_psym("FSCC",[‘t:1->Cl’])
‘!S A i:S->A. FSC(i) ==> ?!c:A->Cl. isPb(c,t,i,To1(S))’
|> gen_all

val FT_def = qdefine_psym("FT",[‘f:A->B’,‘b:X->B’])
‘∃a:X->A. b = f o a’ |> gen_all


