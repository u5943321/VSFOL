
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
val CC3 = store_ax("CC3", “~Epi(coPa(0f,1f))”);


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
(rpt strip_tac >> rw[isPo_def,IdR] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (uex_tac >> 
     fs[Epi_def] >>
     first_x_assum drule >> arw[] >>
     qexists_tac ‘v’ >> rw[] >>
     rpt strip_tac >> arw[]) >>
 rw[Epi_def] >> rpt strip_tac >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “∀A B f:A->B. Epi(f) ⇔ isPo(f,f,Id(B),Id(B))”));


(*
val iso_Po_Po = prove_store("iso_Po_Po",
e0
(rpt strip_tac >>
 )
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
(form_goal
 “∀A B e:A->B P p:B->P. isPo(e,e,p,p) ⇒
 isPo(e,e,Id(B),Id(B))”));

*)

val _ = add_parse (int_of "𝟚");

(* \ b 2 |-> 𝟚*)

val two_def = 
qdefine_fsym("𝟚",[]) ‘Id(2)’


val eq_Po_Epi_lemma = proved_th $
e0
(rw[isPo_def,Epi_def] >>
 rpt strip_tac >>
 first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum strip_assume_tac >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “∀X A a K e.isPo(a:X->A,a,e:A->K,e) ⇒ Epi(a)”)

val e1_ne_e2 = prove_store("e1_ne_e2",
e0
(ccontra_tac >> assume_tac E_def >> rfs[] >>
 drule eq_Po_Epi_lemma >> fs[CC3])
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
(rpt strip_tac >>
 qcases ‘u o 1f = v o 0f’ >--
 (arw[] >>
 assume_tac CC4_2 >>
 fs[isPo_def] >>
 first_x_assum rev_drule >> arw[]) >>
 uex_tac >> arw[] >>
 qexists_tac ‘dom(u) o To1(3)’ >> rw[])
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
(rpt gen_tac >> strip_tac >>
 assume_tac tri_def0 >> 
 fs[dom_def,cod_def] >>
 qsspecl_then [‘u’,‘v’] assume_tac tri_uex >>
 rfs[] >>
 pop_assum (strip_assume_tac o uex_expand) >>
 rpt strip_tac >>
 qsuff_tac ‘a' = a & tri(u,v) = a’ 
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “∀A u:2->A v:2->A. 
  u o 1f = v o 0f ⇒
  (tri(u, v) o α = u & tri(u, v) o β = v) &
  (∀a'. a' o α = u & a' o β = v ⇒ a' = tri(u,v))”)
|> rewr_rule[GSYM dom_def,GSYM cod_def]



val tri_def = proved_th $
e0
(rpt gen_tac >> strip_tac >>
 irule tri_def1 >> arw[])
(form_goal
 “∀A u:2->A v:2->A. 
  dom(v) = cod(u) ⇒
  (tri(u, v) o α = u & tri(u, v) o β = v) &
  (∀a'. a' o α = u & a' o β = v ⇒ a' = tri(u,v))”)
|> rewr_rule[GSYM dom_def,GSYM cod_def]

val is_tri = proved_th $
e0
(rpt strip_tac >>
 drule tri_def >>
 pop_assum strip_assume_tac >> first_x_assum irule >> arw[])
(form_goal
 “∀A u:2->A v:2->A. 
  dom(v) = cod(u) ⇒
  (∀a'. a' o α = u & a' o β = v ⇒ a' = tri(u,v))”)

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


val to_P_component = prove_store("to_P_component",
e0
(rpt strip_tac >> irule is_Pa >> rw[])
(form_goal
 “!A B X f:X->A * B.  f = Pa(p1(A,B) o f,p2(A,B) o f)”));

val to_P_has_comp = prove_store("to_P_has_comp",
e0
(rpt strip_tac >>
 qexistsl_tac [‘p1(A,B) o f’,‘p2(A,B) o f’] >>
 rw[GSYM to_P_component])
(form_goal
 “!A B X f:X->A * B. ∃a:X->A b:X->B.  
  f = Pa(a,b)”));

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


val dom_o = prove_store("dom_o",
e0
(rw[o_assoc,dom_def])
(form_goal
 “∀A B F:A->B a.dom(F o a) = F o dom(a)”));

val cod_o = prove_store("cod_o",
e0
(rw[o_assoc,cod_def])
(form_goal
 “∀A B F:A->B a.cod(F o a) = F o cod(a)”));


val tri_o = prove_store("tri_o",
e0
(rpt strip_tac >>
 irule is_tri >>
 fs[cpsb_def] >>
 drule tri_eqns  >>
 arw[o_assoc] >> rw[dom_o,cod_o] >>
 arw[])
(form_goal
 “∀A f:2->A g. cpsb(g,f) ⇒
  ∀B k:A->B. k o tri(f, g)  = tri((k o f), (k o g))”));

val fun_pres_oa = prove_store("fun_pres_oa",
e0
(rw[oa_def] >> rpt strip_tac >>
 drule tri_o >> arw[GSYM o_assoc])
(form_goal
 “∀A f:2->A g. cpsb(g,f) ⇒
  ∀B k:A->B. k o (g @ f) = (k o g) @ (k o f)”));


val To1_o_To1 = prove_store("To1_o_To1",
e0
(rw[To1_def])
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


val csB_Pt = prove_store("csB_Pt",
e0
(rpt strip_tac >> 
 rw[Er1_def,Ed_def,Pt_def,csB_def] >>
 rw[Pa_distr,o_assoc,To1_o_To1,IdL] >>
 rw[Ev_of_Tp_el,o_assoc,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el',Pa_distr,o_assoc,GSYM Swap_def,p12_of_Pa,
    two_def,one_def] )
(form_goal 
 “∀A f:2-> Exp(2,A). csB(Pt(f)) = 
  (Er1(A) o Ed(1f,A)) o Tp(Pt(f)o Swap(2,2))”));


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
(rpt strip_tac (* 2 *)
 >-- (dimp_tac >> strip_tac >> arw[] >>
     qby_tac
     ‘(f o p1(A, 1)) o Pa(Id(A),To1(A)) = 
      (g o p1(A, 1)) o Pa(Id(A),To1(A))’
     >-- arw[] >> fs[o_assoc,Cr1_iso,IdR]) >>
 dimp_tac >> strip_tac >> arw[] >>
 qby_tac
 ‘(f o Pa(Id(A), To1(A))) o p1(A,1) =
  (g o Pa(Id(A), To1(A))) o p1(A,1)’ 
 >-- arw[] >> fs[o_assoc,Cr1_iso,IdR])
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
(rpt strip_tac >>
 qexists_tac ‘f o p1(2,2)’ >>
 rw[csL_def,csR_def,o_assoc,id_def,
    cod_def,dom_def,p12_of_Pa,zero_def,one_def] >> 
 rw[csT_def,csB_def,p12_of_Pa,two_def,IdR,o_assoc])
(form_goal
 “∀A f:2->A. ∃s: 2 * 2 -> A. 
  csL(s) = id(dom(f)) ∧ csR(s) = id(cod(f)) ∧ 
  csT(s) = f ∧ csB(s) = f”));

val cs_vpara_ex = prove_store("cs_vpara_ex",
e0
(rpt strip_tac >>
 qexists_tac ‘f o p2(2,2)’ >>
 rw[csL_def,csR_def,o_assoc,id_def,
    cod_def,dom_def,p12_of_Pa,zero_def,one_def] >> 
 rw[csT_def,csB_def,p12_of_Pa,two_def,IdR,o_assoc] >>
 rw[zero_def,one_def])
(form_goal
 “∀A f:2->A. ∃s: 2 * 2 -> A. 
  csL(s) = f ∧ csR(s) = f ∧ 
  csT(s) = id(dom(f)) ∧ csB(s) = id(cod(f))”));

val PCC2 = store_ax("PCC2",
“(∃s:2 * 2 -> 2.
   s o Pa(𝟚,𝟘) = 𝟚 & s o Pa(𝟘,𝟚) = 𝟚 &
   s o Pa(𝟙,𝟚) = 𝟙 & s o Pa(𝟚,𝟙) = 𝟙) & 
 (∃s':2 * 2 -> 2.
   s' o Pa(𝟚,𝟘) = 𝟘 & s' o Pa(𝟘,𝟚) = 𝟘 &
   s' o Pa(𝟙,𝟚) = 𝟚 & s' o Pa(𝟚,𝟙) = 𝟚)”)

(*I think PCC2 in the paper is wrong. should confirm it.*)

val cs_lu_ex = prove_store("cs_lu_ex",
e0
(rpt strip_tac >> 
 strip_assume_tac PCC2 >>
 qexists_tac ‘f o s’ >>
 arw[csL_def,csR_def,o_assoc,id_def,
    cod_def,dom_def,p12_of_Pa,csT_def,csB_def] >>  
 rw[one_def,two_def,IdR])
(form_goal
 “∀A f:2->A. ∃s: 2 * 2 -> A. 
  csL(s) = f ∧ csR(s) = id(cod(f)) ∧ 
  csT(s) = f ∧ csB(s) = id(cod(f))”));


val cs_rl_ex = prove_store("cs_rl_ex",
e0
(rpt strip_tac >> 
 strip_assume_tac PCC2 >>
 qexists_tac ‘f o s'’ >>
 arw[csL_def,csR_def,o_assoc,id_def,
    cod_def,dom_def,p12_of_Pa,csT_def,csB_def] >>  
 rw[zero_def,two_def,IdR])
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

val Pa_has_components = prove_store("Pa_has_components",
e0
(rpt strip_tac >>
 qsspecl_then [‘f’] assume_tac to_P_component >>
 pop_assum (assume_tac o GSYM) >>
 qexistsl_tac [‘p1(A,B) o f’,‘p2(A,B) o f’] >>
 arw[])
(form_goal
 “∀X A B f:X->A * B. ∃a b. f = Pa(a,b) ”));


val Pa_eq_eq = prove_store("Pa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘p1(A,B) o Pa(f1, g1) = p1(A,B) o Pa(f2, g2) &
          p2(A,B) o Pa(f1, g1) = p2(A,B) o Pa(f2, g2)’
 >-- arw[] >>
 fs[p12_of_Pa])
(form_goal
 “!A X f1:X->A f2:X->A B g1:X->B g2:X->B. 
  Pa(f1,g1) = Pa(f2,g2) <=> f1 = f2 & g1 = g2”));


val t2tt_cases = prove_store("t2tt_cases",
e0
(rpt strip_tac >>
 qsspecl_then [‘f’] strip_assume_tac Pa_has_components >>
 arw[Pa_eq_eq,id_def,Pa_distr] >> 
 rw[GSYM zero_def,GSYM one_def] >> 
 qsspecl_then [‘a’] strip_assume_tac CC2_1 >> 
 qsspecl_then [‘b’] strip_assume_tac CC2_1 >> 
 fs[])
(form_goal “∀f: 2 -> 2 * 2. 
 f = Pa(𝟚, 𝟘) | f = Pa(𝟙, 𝟚) | f = Pa(𝟘, 𝟚) | f = Pa(𝟚, 𝟙) | 
 f = Pa(𝟚, 𝟚) | 
 f = id(Pa(0f,0f)) | f = id(Pa(1f,0f)) |
 f = id(Pa(0f,1f)) | f = id(Pa(1f,1f))”));
 
val t2tt_dom_cod = prove_store("t2tt_dom_cod",
e0
(rw[dom_def,one_def,two_def,cod_def,zero_def,Pa_distr] >>
 rw[IdL,IdR] >>
 rw[o_assoc] >> rw[one_to_one_Id,IdR])
(form_goal 
“dom(Pa(𝟚, 𝟘)) = Pa(0f,0f) ∧ dom(Pa(𝟙, 𝟚)) = Pa(1f, 0f) ∧ dom(Pa(𝟚, 𝟙)) = Pa(0f, 1f) ∧ cod(Pa(𝟙, 𝟚)) = Pa(1f, 1f) ∧
 cod(Pa(𝟚,𝟘)) = Pa(1f,0f)”));


val id_cod = prove_store("id_cod",
e0
(rw[cod_def,id_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. cod(id(a)) = a”));


val id_dom = prove_store("id_dom",
e0
(rw[dom_def,id_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. dom(id(a)) = a”));


val cpsb_idL = prove_store("cpsb_idL",
e0
(rpt strip_tac >>
 qsspecl_then [‘f’] assume_tac idL >> 
 fs[cpsb_def] >>
 rfs[id_dom])
(form_goal
 “∀A a:1->A f.cpsb(id(a),f) ⇒ id(a) @ f = f”));


val cpsb_idR = prove_store("cpsb_idR",
e0
(rpt strip_tac >>
 qsspecl_then [‘f’] assume_tac idR >> 
 fs[cpsb_def] >>
 rfs[id_cod])
(form_goal
 “∀A a:1->A f.cpsb(f,id(a)) ⇒ f @ id(a) = f”));



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
 irule Thm7 >> 
 arw[] >> 
 qsuff_tac ‘cpsb(β @ α, id(dom(α)))’ 
 >-- (strip_tac >> arw[] >>
     assume_tac cpsb_idR >> 
     flip_tac >> first_x_assum irule >> arw[]) >>
 rw[cpsb_def] >> rw[id_cod] >>
 drule oa_dom_cod >> arw[])
(form_goal “∀f:2->3. f = α | f = β | f = γ | f = id(dom(α)) | f = id(cod(β)) | f = id(dom(β))”));


val ab_dom_cod = prove_store("ab_dom_cod",
e0
(rw[dom_def,cod_def] >> assume_tac CC4_2 >>
 fs[isPo_def])
(form_goal “dom(β) = cod(α)”));

val cod_a_ne_cod_b = prove_store("cod_a_ne_cod_b",
e0
(ccontra_tac >>
 fs[cod_def] >>
 strip_assume_tac tri02_ab >>
 qby_tac
 ‘tri(𝟘, 𝟚) o α o 1f = tri(𝟘, 𝟚) o  β o 1f’
 >-- arw[] >>
 pop_assum mp_tac >> arw[GSYM o_assoc] >>
 rw[zero_def,two_def,IdL,o_assoc] >>
 rw[one_to_one_Id,IdR] >> rw[zf_ne_of])
(form_goal
 “~(cod(α) = cod(β))”));


val dom_a_ne_dom_b = prove_store("dom_a_ne_dom_b",
e0
(ccontra_tac >>
 fs[dom_def] >>
 strip_assume_tac tri21_ab >>
 qby_tac
 ‘tri(𝟚,𝟙) o α o 0f = tri(𝟚,𝟙) o  β o 0f’
 >-- arw[] >>
 pop_assum mp_tac >> arw[GSYM o_assoc] >> 
 rw[one_def,two_def,IdL,o_assoc] >>
 rw[one_to_one_Id,IdR] >> rw[zf_ne_of])
(form_goal
 “~(dom(α) = dom(β))”));


val dom_a_ne_cod_b = prove_store("dom_a_ne_cod_b",
e0
(ccontra_tac >>
 fs[dom_def,cod_def] >>
 strip_assume_tac tri21_ab >>
 qby_tac
 ‘tri(𝟚,𝟙) o α o 0f = tri(𝟚,𝟙) o  β o 1f’
 >-- arw[] >>
 pop_assum mp_tac >> arw[GSYM o_assoc] >> 
 rw[one_def,two_def,IdL,o_assoc] >>
 rw[one_to_one_Id,IdR] >> rw[zf_ne_of])
(form_goal
 “~(dom(α) = cod(β))”));


val is_gamma = prove_store("is_gamma",
e0
(rpt strip_tac >>
 qsspecl_then [‘f’] strip_assume_tac Thm11 (* 5 *)
 >-- fs[cod_a_ne_cod_b] 
 >-- fs[GSYM dom_a_ne_dom_b]
 >-- (fs[id_dom,id_cod]>>  fs[dom_a_ne_cod_b]) 
 >-- fs[id_dom,id_cod,GSYM dom_a_ne_cod_b] >>
 fs[id_dom,id_cod,GSYM dom_a_ne_cod_b])
(form_goal “∀f:2->3. dom(f) = dom(α) & cod(f) = cod(β) ⇒
 f = γ ”));

val id_cpsb = prove_store("id_cpsb",
e0
(rw[cpsb_def,id_dom,id_cod])
(form_goal “∀A a:1->A. cpsb(id(a),id(a))”));

val oa_2_to_2 = prove_store("oa_2_to_2",
e0
(rw[oa_one_two_two,oa_two_zero_two] >>
 rw[one_def,zero_def,GSYM id_def] >> strip_tac (* 2 *)
 >-- (irule cpsb_idR >> rw[cpsb_def,id_dom,id_cod]) >>
 irule cpsb_idR >> rw[cpsb_def,id_dom,id_cod])
(form_goal “𝟚 @ 𝟘 = 𝟚 & 𝟙 @ 𝟚 = 𝟚 & 
            𝟙 @ 𝟙 = 𝟙 & 𝟘 @ 𝟘 = 𝟘”));

val cpsb_2_to_2 = prove_store("cpsb_2_to_2",
e0
(rw[cpsb_def,dom_cod_zot])
(form_goal “cpsb(𝟚,𝟘) & cpsb(𝟙,𝟚) & cpsb(𝟘,𝟘) & cpsb(𝟙,𝟙)”));


val cs2_arrows = prove_store("cs2_arrows",
e0
(strip_tac >> 
 qsspecl_then [‘f’] strip_assume_tac to_P_has_comp >>
 qsspecl_then [‘a’] strip_assume_tac CC2_1 >>
 qsspecl_then [‘b’] strip_assume_tac CC2_1 >> fs[])
(form_goal
 “∀f:2-> 2 * 2. 
   f = Pa(𝟘,𝟘)| f = Pa(𝟘,𝟙) | f = Pa(𝟙,𝟘) | f = Pa(𝟙,𝟙) |
   f = Pa(𝟘,𝟚)| f = Pa(𝟚,𝟙) | f = Pa(𝟚,𝟘) | f = Pa(𝟙,𝟚) |
   f = Pa(𝟚,𝟚)”));


val dom_cod_Pa02 = prove_store("dom_cod_Pa02",
e0
(rw[dom_def,cod_def,Pa_distr] >>
 rw[GSYM dom_def,GSYM cod_def] >>
 rw[Pa_eq_eq,dom_cod_zot])
(form_goal “dom(Pa(𝟘,𝟚)) = Pa(0f,0f) & 
            cod(Pa(𝟘,𝟚)) = Pa(0f,1f) ”));


val dom_cod_Pa12 = prove_store("dom_cod_Pa12",
e0
(rw[dom_def,cod_def,Pa_distr] >>
 rw[GSYM dom_def,GSYM cod_def] >>
 rw[Pa_eq_eq,dom_cod_zot])
(form_goal “dom(Pa(𝟙,𝟚)) = Pa(1f,0f) & 
            cod(Pa(𝟙,𝟚)) = Pa(1f,1f) ”));

val Pa00_id = prove_store("Pa00_id",
e0
(rw[id_def,Pa_distr,Pa_eq_eq,zero_def])
(form_goal “Pa(𝟘,𝟘) = id(Pa(0f,0f))”));


val Pa10_id = prove_store("Pa10_id",
e0
(rw[id_def,Pa_distr,Pa_eq_eq,zero_def,one_def])
(form_goal “Pa(𝟙,𝟘) = id(Pa(1f,0f))”));


val Pa01_id = prove_store("Pa01_id",
e0
(rw[id_def,Pa_distr,Pa_eq_eq,zero_def,one_def])
(form_goal “Pa(𝟘,𝟙) = id(Pa(0f,1f))”));


val Pa11_id = prove_store("Pa11_id",
e0
(rw[id_def,Pa_distr,Pa_eq_eq,one_def])
(form_goal “Pa(𝟙,𝟙) = id(Pa(1f,1f))”));


val cs_ext = prove_store("cs_ext",
e0
(rpt strip_tac >> 
 qby_tac
 ‘s1 o Pa(𝟚, 𝟚) = s2 o Pa(𝟚, 𝟚)’
 >-- (rw[GSYM RT_cs2] >>
     assume_tac cs2_RT_cpsb >> drule fun_pres_oa >>
     fs[csL_def,csR_def,csT_def,csB_def]) >>
 qby_tac
 ‘s1 o Pa(𝟘, 𝟘) = s2 o Pa(𝟘, 𝟘)’ 
 >-- (fs[csL_def] >> 
     rw[Pa00_id,GSYM dom_cod_Pa02,id_def,dom_def] >>
     arw[GSYM o_assoc]) >>
 qby_tac
 ‘s1 o Pa(𝟙, 𝟘) = s2 o Pa(𝟙, 𝟘)’ 
 >-- (fs[csR_def] >> 
     rw[Pa10_id,GSYM dom_cod_Pa12,id_def,dom_def] >>
     arw[GSYM o_assoc]) >>
 qby_tac
 ‘s1 o Pa(𝟘,𝟙) = s2 o Pa(𝟘,𝟙)’ 
 >-- (fs[csL_def] >> 
     rw[Pa01_id,GSYM dom_cod_Pa02,id_def,cod_def] >>
     arw[GSYM o_assoc]) >>
 qby_tac
 ‘s1 o Pa(𝟙,𝟙) = s2 o Pa(𝟙,𝟙)’ 
 >-- (fs[csR_def] >> 
     rw[Pa11_id,GSYM dom_cod_Pa12,id_def,cod_def] >>
     arw[GSYM o_assoc]) >>
 fs[csL_def,csR_def,csT_def,csB_def] >>
 irule $ iffLR fun_ext >>
 strip_tac >>
 qsspecl_then [‘a’] strip_assume_tac cs2_arrows >>
 fs[])
(form_goal
 “∀s1 s2: 2 * 2 ->A.
  csL(s1) = csL(s2) &
  csR(s1) = csR(s2) &
  csT(s1) = csT(s2) &
  csB(s1) = csB(s2) ⇒ s1 = s2”));

(*lower right corner*)
val lrc_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?lrc:2 * 2 -> 2. 
  csT(lrc) = 𝟘 & csR(lrc) = 𝟚 & 
  csL(lrc) = 𝟘 & csB(lrc) = 𝟚’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘lrc’ >>
     arw[] >> rpt strip_tac >> irule cs_ext >> arw[]) >>
 irule Thm7 >> rw[cpsb_2_to_2])
(form_goal
 “?!lrc:2 * 2 -> 2. 
  csT(lrc) = 𝟘 & csR(lrc) = 𝟚 & 
  csL(lrc) = 𝟘 & csB(lrc) = 𝟚”)
|> qsimple_uex_spec "lr𝟚" [] 


val lr2_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac >> arw[lrc_def] >>
 strip_assume_tac lrc_def>> irule cs_ext >> arw[])
(form_goal 
 “∀f. f = lr𝟚 ⇔ 
      csT(f) = 𝟘 & csR(f) = 𝟚 & 
  csL(f) = 𝟘 & csB(f) = 𝟚”)


(*upper left corner*)
val ulc_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?ulc:2 * 2 -> 2. 
  csT(ulc) = 𝟚 & csR(ulc) = 𝟙 & 
  csL(ulc) = 𝟚 & csB(ulc) = 𝟙’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘ulc’ >>
     arw[] >> rpt strip_tac >> irule cs_ext >> arw[]) >>
 irule Thm7 >> rw[cpsb_2_to_2])
(form_goal
 “?!ulc:2 * 2 -> 2. 
  csT(ulc) = 𝟚 & csR(ulc) = 𝟙 & 
  csL(ulc) = 𝟚 & csB(ulc) = 𝟙”)
|> qsimple_uex_spec "ul𝟚" [] 


val ul2_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac >> arw[ulc_def] >>
 strip_assume_tac ulc_def>> irule cs_ext >> arw[])
(form_goal 
 “∀f. f = ul𝟚 ⇔ 
      csT(f) = 𝟚 & csR(f) = 𝟙 & 
  csL(f) = 𝟚 & csB(f) = 𝟙”)


(*vertial parallel*)
val vp_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?vp:2 * 2 -> 2. 
  csT(vp) = 𝟘 & csR(vp) = 𝟚 & 
  csL(vp) = 𝟚 & csB(vp) = 𝟙’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘vp’ >>
     arw[] >> rpt strip_tac >> irule cs_ext >> arw[]) >>
 irule Thm7 >> rw[cpsb_2_to_2,oa_2_to_2])
(form_goal
 “?!vp:2 * 2 -> 2. 
  csT(vp) = 𝟘 & csR(vp) = 𝟚 & 
  csL(vp) = 𝟚 & csB(vp) = 𝟙”)
|> qsimple_uex_spec "v𝟚" [] 


val v2_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac >> arw[vp_def] >>
 strip_assume_tac vp_def>> irule cs_ext >> arw[])
(form_goal 
 “∀f. f = v𝟚 ⇔ 
  csT(f) = 𝟘 & csR(f) = 𝟚 & 
  csL(f) = 𝟚 & csB(f) = 𝟙”)



(*horizontal parallel*)
val hp_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?hp:2 * 2 -> 2. 
  csT(hp) = 𝟚 & csR(hp) = 𝟙 & 
  csL(hp) = 𝟘 & csB(hp) = 𝟚’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘hp’ >>
     arw[] >> rpt strip_tac >> irule cs_ext >> arw[]) >>
 irule Thm7 >> rw[cpsb_2_to_2,oa_2_to_2])
(form_goal
 “?!hp:2 * 2 -> 2. 
  csT(hp) = 𝟚 & csR(hp) = 𝟙 & 
  csL(hp) = 𝟘 & csB(hp) = 𝟚”)
|> qsimple_uex_spec "h𝟚" [] 


val h2_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac >> arw[hp_def] >>
 strip_assume_tac hp_def>> irule cs_ext >> arw[])
(form_goal 
 “∀f. f = h𝟚 ⇔ 
  csT(f) = 𝟚 & csR(f) = 𝟙 & 
  csL(f) = 𝟘 & csB(f) = 𝟚”)


(*constant zero*)
val cz_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?cz:2 * 2 -> 2. 
  csT(cz) = 𝟘 & csR(cz) = 𝟘 & 
  csL(cz) = 𝟘 & csB(cz) = 𝟘’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘cz’ >>
     arw[] >> rpt strip_tac >> irule cs_ext >> arw[]) >>
 irule Thm7 >> rw[cpsb_2_to_2,oa_2_to_2])
(form_goal
 “?!cz:2 * 2 -> 2. 
  csT(cz) = 𝟘 & csR(cz) = 𝟘 & 
  csL(cz) = 𝟘 & csB(cz) = 𝟘”)
|> qsimple_uex_spec "c𝟘" [] 


val c0_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac >> arw[cz_def] >>
 strip_assume_tac cz_def>> irule cs_ext >> arw[])
(form_goal 
 “∀f. f = c𝟘 ⇔ 
  csT(f) = 𝟘 & csR(f) = 𝟘 & 
  csL(f) = 𝟘 & csB(f) = 𝟘”)



(*constant one*)
val co_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?co:2 * 2 -> 2. 
  csT(co) = 𝟙 & csR(co) = 𝟙 & 
  csL(co) = 𝟙 & csB(co) = 𝟙’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘co’ >>
     arw[] >> rpt strip_tac >> irule cs_ext >> arw[]) >>
 irule Thm7 >> rw[cpsb_2_to_2,oa_2_to_2])
(form_goal
 “?!co:2 * 2 -> 2. 
  csT(co) = 𝟙 & csR(co) = 𝟙 & 
  csL(co) = 𝟙 & csB(co) = 𝟙”)
|> qsimple_uex_spec "c𝟙" [] 


val c1_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac >> arw[co_def] >>
 strip_assume_tac co_def>> irule cs_ext >> arw[])
(form_goal 
 “∀f. f = c𝟙 ⇔ 
  csT(f) = 𝟙 & csR(f) = 𝟙 & 
  csL(f) = 𝟙 & csB(f) = 𝟙”)



val dom_csL_dom_csT = prove_store("dom_csL_dom_csT",
e0
(rpt strip_tac >> rw[dom_def,csL_def,csT_def] >>
 rw[o_assoc,Pa_distr,GSYM dom_def] >>
 rw[dom_cod_zot])
(form_goal
 “∀A cs:2 * 2->A.dom(csL(cs)) = dom(csT(cs))”));

val dom_csR_cod_csT = prove_store("dom_csL_cod_csT",
e0
(rpt strip_tac >> rw[dom_def,csR_def,csT_def,cod_def] >>
 rw[o_assoc,Pa_distr,GSYM dom_def,GSYM cod_def] >>
 rw[dom_cod_zot])
(form_goal
 “∀A cs:2 * 2->A.
  dom(csR(cs)) = cod(csT(cs))”));


val cod_csL_dom_csB = prove_store("cod_csL_dom_csB",
e0
(rpt strip_tac >> rw[dom_def,csL_def,csB_def,cod_def] >>
 rw[o_assoc,Pa_distr,GSYM dom_def,GSYM cod_def] >>
 rw[dom_cod_zot])
(form_goal
 “∀A cs:2 * 2->A.
  cod(csL(cs)) = dom(csB(cs))”));


val cod_csR_cod_csB = prove_store("cod_csR_cod_csB",
e0
(rpt strip_tac >> rw[dom_def,csR_def,csB_def,cod_def] >>
 rw[o_assoc,Pa_distr,GSYM dom_def,GSYM cod_def] >>
 rw[dom_cod_zot])
(form_goal
 “∀A cs:2 * 2->A.
  cod(csR(cs)) = cod(csB(cs))”));

val ne_2_to_2 = prove_store("ne_2_to_2",
e0
(cheat)
(form_goal “~(𝟘 = 𝟚) & ~(𝟚 = 𝟘) & ~(𝟙 = 𝟘) & ~(𝟘 = 𝟙) & 
 ~(𝟙 = 𝟚) & ~(𝟚 = 𝟙)”));

val twotwo2two_cases = prove_store("twotwo2two_cases",
e0
(strip_tac >> 
 rw[lr2_iff,ul2_iff,v2_iff,h2_iff,c0_iff,c1_iff] >>
 qsspecl_then [‘csT(f)’] strip_assume_tac CC2_1 (* 3 *)
 >> (arw[ne_2_to_2] >>
     qsspecl_then [‘f’] assume_tac dom_csL_dom_csT >>
     rfs[dom_cod_zot] >>
     qsspecl_then [‘f’] assume_tac dom_csR_cod_csT >>
     rfs[dom_cod_zot] >> 
     qsspecl_then [‘f’] assume_tac cod_csR_cod_csB >>
     qsspecl_then [‘f’] assume_tac cod_csL_dom_csB >> 
     qsspecl_then [‘csR(f)’] assume_tac CC2_1 >>
     qsspecl_then [‘csL(f)’] assume_tac CC2_1 >>
     qsspecl_then [‘csB(f)’] assume_tac CC2_1 >> 
     fs[ne_2_to_2,dom_cod_zot] >>
     fs[ne_2_to_2,dom_cod_zot,zf_ne_of,GSYM zf_ne_of]))
(form_goal 
“∀f:2 * 2->2. 
 f = lr𝟚 | f = ul𝟚 | f = v𝟚 | f = h𝟚 | f = c𝟘 | f = c𝟙”));

(*see dom_Tp_cs,
two Tp of cs are composible iff the csT of the second is the csB of the first
*)


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

val Tp0_eq_eq = prove_store("Tp0_eq_eq",
e0
(cheat)
(form_goal “∀A B f:1->Exp(A,B) g. Tp0(f) = Tp0(g) ⇔ f = g”));


val dom_Tp_cs = prove_store("dom_Tp_cs",
e0
(rw[dom_def,Tp_def,Tp1_def,csT_def] >>
 rpt strip_tac >> irule $ iffLR Tp0_eq_eq >>
 rw[Tp0_Tp1_inv] >>
 rw[GSYM Tp0_def,o_assoc,Ev_of_Tp_el] >> 
 rw[two_def,zero_def])
(form_goal
 “∀A cs:2 * 2 ->A. 
  dom(Tp(cs)) = Tp1(csT(cs))”));


val cod_Tp_cs = prove_store("cod_Tp_cs",
e0
(rw[cod_def,Tp_def,Tp1_def,csB_def] >>
 rpt strip_tac >> irule $ iffLR Tp0_eq_eq >>
 rw[Tp0_Tp1_inv] >>
 rw[GSYM Tp0_def,o_assoc,Ev_of_Tp_el] >> 
 rw[two_def,one_def])
(form_goal
 “∀A cs:2 * 2 ->A. 
  cod(Tp(cs)) = Tp1(csB(cs))”));


val twotwo2two_Tp_dom_cod =
prove_store("twotwo2two_Tp_dom_cod",
e0
(rw[dom_Tp_cs,Tp0_Tp1_inv,cod_Tp_cs,
    lrc_def,ulc_def,vp_def,hp_def,cz_def,co_def])
(form_goal 
 “Tp0(dom(Tp(lr𝟚))) = 𝟘 & Tp0(cod(Tp(lr𝟚))) = 𝟚 & 
  Tp0(dom(Tp(ul𝟚))) = 𝟚 & Tp0(cod(Tp(ul𝟚))) = 𝟙 &
  Tp0(dom(Tp(v𝟚))) = 𝟘 & Tp0(cod(Tp(v𝟚))) = 𝟙 & 
  Tp0(dom(Tp(h𝟚))) = 𝟚 & Tp0(cod(Tp(h𝟚))) = 𝟚 &
  Tp0(dom(Tp(c𝟙))) = 𝟙 & Tp0(cod(Tp(c𝟙))) = 𝟙 &
  Tp0(dom(Tp(c𝟘))) = 𝟘 & Tp0(cod(Tp(c𝟘))) = 𝟘”));


val Tp0_iff_Tp1 = prove_store("Tp0_iff_Tp1",
e0
(cheat)
(form_goal “∀A B f:1->Exp(A,B) g.Tp0(f) = g ⇔ f = Tp1(g)”));

val to_Exp22_dom_cod = 
 twotwo2two_Tp_dom_cod |> rewr_rule[Tp0_iff_Tp1]
|> store_as "to_Exp22_dom_cod";

val twotwo2two_Tp_cpsb = prove_store("twotwo2two_Tp_cpsb",
e0
(rw[cpsb_def,GSYM Tp0_eq_eq,twotwo2two_Tp_dom_cod])
(form_goal 
 “cpsb(Tp(ul𝟚),Tp(lr𝟚)) & 
  cpsb(Tp(ul𝟚),Tp(h𝟚)) & 
  cpsb(Tp(h𝟚),Tp(lr𝟚)) & 
  cpsb(Tp(c𝟙),Tp(ul𝟚)) & 
  cpsb(Tp(c𝟙),Tp(v𝟚)) &
  cpsb(Tp(v𝟚),Tp(c𝟘)) & 
  cpsb(Tp(lr𝟚),Tp(c𝟘)) & 
  cpsb(Tp(c𝟙),Tp(c𝟙)) & 
  cpsb(Tp(c𝟘),Tp(c𝟘)) &
  cpsb(Tp(h𝟚),Tp(h𝟚))”));


val csT_Pt_oa = prove_store("csT_Pt_oa",
e0
(rpt strip_tac >>
rw[csT_def,Pt_def,o_assoc] >> 
rw[Pa_distr,p12_of_Pa,o_assoc,zero_def] >>
rw[GSYM o_assoc,GSYM dom_def] >>
drule oa_dom_cod >> arw[])
(form_goal
“∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒
 csT(Pt(g1 @ f1)) =  csT(Pt(f1))”));


val csB_Pt_oa = prove_store("csB_Pt_oa",
e0
(rpt strip_tac >>
rw[csB_def,Pt_def,o_assoc] >> 
rw[Pa_distr,p12_of_Pa,o_assoc,one_def] >>
rw[GSYM o_assoc,GSYM cod_def] >>
drule oa_dom_cod >> arw[])
(form_goal
“∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒
 csB(Pt(g1 @ f1)) = csB(Pt(g1))”));

val Pa_cpsb_one = prove_store("Pa_cpsb_one",
e0
(rpt strip_tac >> rw[cpsb_def] >>
 rw[dom_def,cod_def,Pa_distr] >> 
 rw[GSYM dom_def,GSYM cod_def] >> fs[cpsb_def,dom_cod_zot])
(form_goal
 “∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ cpsb(Pa(𝟙,g1),Pa(𝟙,f1))”));


val Pa_cpsb_zero = prove_store("Pa_cpsb_zero",
e0
(rpt strip_tac >> rw[cpsb_def] >>
 rw[dom_def,cod_def,Pa_distr] >> 
 rw[GSYM dom_def,GSYM cod_def] >> fs[cpsb_def,dom_cod_zot])
(form_goal
 “∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ cpsb(Pa(𝟘,g1),Pa(𝟘,f1))”));

val Pa_oa_distr_one = prove_store("Pa_oa_distr_one",
e0
(rpt strip_tac >>
 qby_tac
 ‘Pa(𝟙, g1 @ f1) = Pa(1f o To1(Exp(2,A)),Id(Exp(2,A))) o  g1 @ f1’
 >-- rw[Pa_distr,To1_def,IdL,o_assoc,GSYM one_def] >>
 rev_drule fun_pres_oa >> fs[] >>
 rw[Pa_distr,p12_of_Pa,IdL,To1_def,o_assoc] >>
 rw[one_def])
(form_goal
“∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ 
 Pa(𝟙, g1 @ f1) = Pa(𝟙,g1) @ Pa(𝟙,f1)”));



val Pa_oa_distr_zero = prove_store("Pa_oa_distr_zero",
e0
(rpt strip_tac >>
 qby_tac
 ‘Pa(𝟘, g1 @ f1) = Pa(0f o To1(Exp(2,A)),Id(Exp(2,A))) o  g1 @ f1’
 >-- rw[Pa_distr,To1_def,IdL,o_assoc,GSYM zero_def] >>
 rev_drule fun_pres_oa >> fs[] >>
 rw[Pa_distr,p12_of_Pa,IdL,To1_def,o_assoc] >>
 rw[zero_def])
(form_goal
“∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ 
 Pa(𝟘, g1 @ f1) = Pa(𝟘,g1) @ Pa(𝟘,f1)”));


val csR_Pt_oa = prove_store("csR_Pt_oa",
e0
(rpt strip_tac >>
rw[csR_def,Pt_def,o_assoc] >>  
rw[Pa_distr,p12_of_Pa,o_assoc,two_def,IdR] >>
qby_tac ‘cpsb(Pa(𝟙,g1),Pa(𝟙,f1))’
>-- (drule Pa_cpsb_one >> arw[]) >> 
qby_tac
‘Pa(𝟙, g1 @ f1) = Pa(𝟙,g1) @ Pa(𝟙,f1)’
>-- (drule Pa_oa_distr_one >> arw[]) >>
drule fun_pres_oa >> arw[])
(form_goal “∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ 
 csR(Pt(g1:2->Exp(2,A))) @ csR(Pt(f1)) = csR(Pt(g1 @ f1))”));


val csL_Pt_oa = prove_store("csL_Pt_oa",
e0
(rpt strip_tac >>
rw[csL_def,Pt_def,o_assoc] >>  
rw[Pa_distr,p12_of_Pa,o_assoc,two_def,IdR] >>
qby_tac ‘cpsb(Pa(𝟘,g1),Pa(𝟘,f1))’
>-- (drule Pa_cpsb_zero >> arw[]) >> 
qby_tac
‘Pa(𝟘, g1 @ f1) = Pa(𝟘,g1) @ Pa(𝟘,f1)’
>-- (drule Pa_oa_distr_zero >> arw[]) >>
drule fun_pres_oa >> arw[])
(form_goal “∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ 
 csL(Pt(g1)) @ csL(Pt(f1)) = csL(Pt(g1 @ f1))”));



val twotwo2two_Tp_oa = prove_store("twotwo2two_Tp_oa",
e0
(rpt strip_tac (* 7 *)
 >-- (qby_tac ‘cpsb(Tp(ul𝟚),Tp(lr𝟚))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> rw[vp_def] >>
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,ulc_def,lrc_def,oa_2_to_2])
 >-- (qby_tac ‘cpsb(Tp(ul𝟚),Tp(h𝟚))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> rw[vp_def] >>
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,ulc_def,hp_def,oa_2_to_2])
 >-- (qby_tac ‘cpsb(Tp(h𝟚),Tp(lr𝟚))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> 
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,lrc_def,hp_def,oa_2_to_2])
 >-- (qby_tac ‘cpsb(Tp(c𝟙),Tp(ul𝟚))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> 
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,ulc_def,co_def,oa_2_to_2])
 >-- (qby_tac ‘cpsb(Tp(c𝟙),Tp(v𝟚))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> 
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,vp_def,co_def,oa_2_to_2])
 >-- (qby_tac ‘cpsb(Tp(v𝟚),Tp(c𝟘))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> 
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,vp_def,cz_def,oa_2_to_2]) 
 >-- (qby_tac ‘cpsb(Tp(lr𝟚),Tp(c𝟘))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> 
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,lrc_def,cz_def,oa_2_to_2])
 >-- (qby_tac ‘cpsb(Tp(c𝟙),Tp(c𝟙))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> 
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,co_def,oa_2_to_2])
 >-- (qby_tac ‘cpsb(Tp(c𝟘),Tp(c𝟘))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> 
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,cz_def,oa_2_to_2])
 >-- (qby_tac ‘cpsb(Tp(h𝟚),Tp(h𝟚))’
     >-- rw[twotwo2two_Tp_cpsb] >>
     rw[GSYM Pt_eq_eq,Pt_Tp] >> 
     irule cs_ext >> 
     drule csT_Pt_oa >> 
     drule $ GSYM csR_Pt_oa >>
     drule $ GSYM csL_Pt_oa >>
     drule csB_Pt_oa >> 
     arw[Pt_Tp,hp_def,oa_2_to_2]))
(form_goal
 “Tp(ul𝟚) @ Tp(lr𝟚) = Tp(v𝟚) & 
  Tp(ul𝟚) @ Tp(h𝟚) = Tp(ul𝟚) & 
  Tp(h𝟚) @ Tp(lr𝟚) = Tp(lr𝟚) & 
  Tp(c𝟙) @ Tp(ul𝟚) = Tp(ul𝟚) & 
  Tp(c𝟙) @ Tp(v𝟚) = Tp(v𝟚) &
  Tp(v𝟚) @ Tp(c𝟘) = Tp(v𝟚) & 
  Tp(lr𝟚) @ Tp(c𝟘) = Tp(lr𝟚) & 
  Tp(c𝟙) @ Tp(c𝟙) = Tp(c𝟙) & 
  Tp(c𝟘) @ Tp(c𝟘) = Tp(c𝟘) & 
  Tp(h𝟚) @ Tp(h𝟚) = Tp(h𝟚)”));

val Pt_iff_Tp = prove_store("Pt_iff_Tp",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (irule $ iffLR Pt_eq_eq >> arw[Pt_Tp]) >>
 arw[Pt_Tp])
(form_goal “∀A B C f:A->Exp(B,C) g. 
 Pt(f) = g ⇔ f = Tp(g)”));

val to_Exp22 = prove_store("to_Exp22",
e0
(strip_tac >> 
 qsspecl_then [‘Pt(a)’] assume_tac twotwo2two_cases >> 
 fs[Pt_iff_Tp])
(form_goal 
 “∀a:2->Exp(2,2). 
  a = Tp(lr𝟚) | a = Tp(ul𝟚) | a = Tp(v𝟚) | a = Tp(h𝟚) | 
  a = Tp(c𝟘) | a = Tp(c𝟙)”));

(*CC4_1 CC4_2 ba_cpsb oa_ba
ab_dom_cod cod_a_ne_cod_b dom_a_ne_dom_b
dom_a_ne_cod_b is_gamma  *)

val alpha1_def = qdefine_fsym("α₁",[]) ‘dom(α)’
val alpha2_def = qdefine_fsym("α₂",[]) ‘cod(α)’ 

val beta2_def = qdefine_fsym("β₂",[]) ‘cod(β)’
 
val cpsb_id_dom = prove_store("cpsb_id_dom",
e0
(rw[cpsb_def,id_cod,id_dom] )
(form_goal “∀A a:2->A. cpsb(a,id(dom(a)))”));


val cpsb_id_cod = prove_store("cpsb_id_cod",
e0
(rw[cpsb_def,id_cod,id_dom] )
(form_goal “∀A a:2->A. cpsb(id(cod(a)),a)”));


val three_dom_cod = prove_store("three_dom_cod",
e0
(rw[alpha1_def,alpha2_def,beta2_def] >>
 rw[ab_dom_cod] >> rw[dom_def,cod_def,CC4_1])
(form_goal “dom(α) = α₁ & cod(α) = α₂ & dom(β) = α₂ & cod(β) = β₂ & dom(γ) = α₁ & cod(γ) = β₂”));

val three_cpsb0 = prove_store("three_cpsb0",
e0
(rw[cpsb_id_cod,cpsb_id_dom] >>
 rw[cpsb_def,id_dom,id_cod] >> rw[three_dom_cod])
(form_goal 
 “cpsb(id(cod(β)),β) & cpsb(β,id(dom(β))) &
  cpsb(id(dom(β)),α) & cpsb(α,id(dom(α))) &
  cpsb(β,α) & 
  cpsb(γ,id(dom(α))) & cpsb(id(cod(β)),γ)”));


val three_cpsb = prove_store("three_cpsb",
e0
(rw[alpha2_def,beta2_def,alpha1_def,three_cpsb0] >>
 rw[cpsb_id_cod] >> rw[cpsb_def,three_dom_cod,id_cod])
(form_goal 
 “cpsb(id(β₂),β) & cpsb(β,id(α₂)) &
  cpsb(id(α₂),α) & cpsb(α,id(α₁)) &
  cpsb(β,α) & 
  cpsb(γ,id(α₁)) & cpsb(id(β₂),γ)”));

val three_oa = prove_store("three_oa",
e0
(rw[beta2_def,alpha1_def,alpha2_def,idL,idR,oa_ba] >> 
 rpt strip_tac (* 3 *)
 >-- (irule cpsb_idR >> rw[cpsb_def,id_cod,three_dom_cod])
 >-- (irule cpsb_idR >> rw[cpsb_def,id_cod,three_dom_cod])>>
 irule cpsb_idL >> rw[cpsb_def,id_cod,three_dom_cod,id_dom])
(form_goal
 “id(β₂) @ β = β & β @ id(α₂) = β & 
  id(α₂) @ α = α & α @ id(α₁) = α & 
  β @ α = γ & 
  γ @ id(α₁) = γ & id(β₂) @ γ = γ”));

(*
if 
id(β₂) @ β = β send to 
Tp(c𝟙) @ Tp(ul𝟚) = Tp(ul𝟚) &

or id(β₂) @ β = β 
id(β₂) @ γ = γ


Tp(c𝟙:= id(β2)) @ Tp(v𝟚) = Tp(v𝟚) &




Tp(h𝟚) @ Tp(lr𝟚) = Tp(lr𝟚) &




Tp(ul𝟚) @ Tp(lr𝟚) = Tp(v𝟚) &
Tp(ul𝟚) @ Tp(h𝟚) = Tp(ul𝟚) &
Tp(h𝟚) @ Tp(lr𝟚) = Tp(lr𝟚) &
Tp(c𝟙) @ Tp(ul𝟚) = Tp(ul𝟚) &
Tp(c𝟙) @ Tp(v𝟚) = Tp(v𝟚) &
Tp(v𝟚) @ Tp(c𝟘) = Tp(v𝟚) &
Tp(lr𝟚) @ Tp(c𝟘) = Tp(lr𝟚)
*)

val to_Exp22_ne = prove_store("to_Exp22_ne",
e0
(cheat)
(form_goal
 “~(Tp(lr𝟚) = Tp(ul𝟚)) &
  ~(Tp(lr𝟚) = Tp(v𝟚)) &
  ~(Tp(lr𝟚) = Tp(c𝟙)) & 
  ~(Tp(lr𝟚) = Tp(c𝟘)) &
  ~(Tp(lr𝟚) = Tp(h𝟚)) & 
  ~(Tp(ul𝟚) = Tp(v𝟚)) &
  ~(Tp(ul𝟚) = Tp(c𝟙)) &
  ~(Tp(ul𝟚) = Tp(c𝟘)) &
  ~(Tp(ul𝟚) = Tp(h𝟚)) &
  ~(Tp(v𝟚) = Tp(c𝟙)) &
  ~(Tp(v𝟚) = Tp(c𝟘)) &
  ~(Tp(v𝟚) = Tp(h𝟚)) &
  ~(Tp(c𝟙) = Tp(c𝟘)) &
  ~(Tp(c𝟙) = Tp(h𝟚)) & 
  ~(Tp(c𝟘) = Tp(h𝟚))”));

val unique_eq = prove_store("unique_eq",
e0
(rpt strip_tac >> uex_tac >> qexists_tac ‘f’ >> rw[])
(form_goal “∀A B f:A->B. ?!g. g = f”));



local
val l = 
csT_Pt |> qsspecl [‘id(a:1-> Exp(2,A))’] 
       |> rewr_rule[id_def,Tp_def,Pt_def,Er1_def]
       |> rewr_rule[o_assoc,p12_of_Pa,To1_def,Pa_distr,Ed_def]
       |> rewr_rule[IdL,Ev_of_Tp_el,o_assoc,
                    Pa_distr,p12_of_Pa,To1_def]
       |> rewr_rule[GSYM Swap_def,p12_of_Pa]
       |> rewr_rule[Ev_of_Tp_el',o_assoc,p12_of_Pa,Pa_distr]
       |> rewr_rule[To1_def]
       |> rewr_rule[Tp0_def]
in
val csT_Pt_id = prove_store("csT_Pt_id",
e0
(rw[Pt_def,id_def,o_assoc,To1_def] >>
 rw[l]) 
(form_goal “!A a:1->Exp(2,A).
 csT(Pt(id(a))) = Tp0(a)”));
end


local
val l = 
csB_Pt |> qsspecl [‘id(a:1-> Exp(2,A))’] 
       |> rewr_rule[id_def,Tp_def,Pt_def,Er1_def]
       |> rewr_rule[o_assoc,p12_of_Pa,To1_def,Pa_distr,Ed_def]
       |> rewr_rule[IdL,Ev_of_Tp_el,o_assoc,
                    Pa_distr,p12_of_Pa,To1_def]
       |> rewr_rule[GSYM Swap_def,p12_of_Pa]
       |> rewr_rule[Ev_of_Tp_el',o_assoc,p12_of_Pa,Pa_distr]
       |> rewr_rule[To1_def]
       |> rewr_rule[Tp0_def]
in
val csB_Pt_id = prove_store("csB_Pt_id",
e0
(rw[Pt_def,id_def,o_assoc,To1_def] >>
 rw[l]) 
(form_goal “!A a:1->Exp(2,A).
 csB(Pt(id(a))) = Tp0(a)”));
end


local
val l = 
csR_Pt |> qsspecl [‘id(a:1-> Exp(2,A))’] 
       |> rewr_rule[id_def,Tp_def,Pt_def,Er1_def]
       |> rewr_rule[o_assoc,p12_of_Pa,To1_def,Pa_distr,Ed_def]
       |> rewr_rule[IdL,Ev_of_Tp_el,o_assoc,
                    Pa_distr,p12_of_Pa,To1_def]
       |> rewr_rule[GSYM Swap_def,p12_of_Pa]
       |> rewr_rule[Ev_of_Tp_el',o_assoc,p12_of_Pa,Pa_distr]
       |> rewr_rule[To1_def]
       |> rewr_rule[Tp0_def]
in
val csR_Pt_id = prove_store("csR_Pt_id",
e0
(rw[Pt_def,id_def,o_assoc,To1_def] >>
 rw[l] >> rw[cod_def,GSYM Tp0_def] >>
 rw[Pa_distr,p12_of_Pa,IdL,o_assoc,To1_def] ) 
(form_goal “!A a:1->Exp(2,A).
 csR(Pt(id(a))) = id(cod(Tp0(a)))”));
end


local
val l = 
csL_Pt |> qsspecl [‘id(a:1-> Exp(2,A))’] 
       |> rewr_rule[id_def,Tp_def,Pt_def,Er1_def]
       |> rewr_rule[o_assoc,p12_of_Pa,To1_def,Pa_distr,Ed_def]
       |> rewr_rule[IdL,Ev_of_Tp_el,o_assoc,
                    Pa_distr,p12_of_Pa,To1_def]
       |> rewr_rule[GSYM Swap_def,p12_of_Pa]
       |> rewr_rule[Ev_of_Tp_el',o_assoc,p12_of_Pa,Pa_distr]
       |> rewr_rule[To1_def]
       |> rewr_rule[Tp0_def]
in
val csL_Pt_id = prove_store("csL_Pt_id",
e0
(rw[Pt_def,id_def,o_assoc,To1_def] >>
 rw[l] >> rw[dom_def,GSYM Tp0_def] >>
 rw[Pa_distr,p12_of_Pa,IdL,o_assoc,To1_def] ) 
(form_goal “!A a:1->Exp(2,A).
 csL(Pt(id(a))) = id(dom(Tp0(a)))”));
end


val id_Tp1_cz = prove_store("id_Tp1_cz",
e0
(rw[GSYM Pt_iff_Tp] >> 
 irule cs_ext >> rw[cz_def] >>
 rw[csT_Pt_id,csR_Pt_id,csL_Pt_id,csB_Pt_id] >>
 rw[Tp0_Tp1_inv,id_dom,id_cod] >>
 rw[id_def,dom_def,cod_def,o_assoc] >>
 rw[one_to_one_Id,zero_def,one_def,o_assoc] >>
 qsuff_tac
 ‘0f o (To1(2) o 1f) o To1(2) = 0f o To1(2) &
  0f o (To1(2) o 0f) o To1(2) = 0f o To1(2)’
 >-- rw[o_assoc] >>
 rw[one_to_one_Id,IdL] )
(form_goal “id(Tp1(𝟘)) = Tp(c𝟘)”));


val id_Tp1_co = prove_store("id_Tp1_co",
e0
(rw[GSYM Pt_iff_Tp] >> 
 irule cs_ext >> rw[co_def] >>
 rw[csT_Pt_id,csR_Pt_id,csL_Pt_id,csB_Pt_id] >>
 rw[Tp0_Tp1_inv,id_dom,id_cod] >>
 rw[id_def,dom_def,cod_def,o_assoc] >>
 rw[one_to_one_Id,zero_def,one_def,o_assoc] >>
 qsuff_tac
 ‘1f o (To1(2) o 1f) o To1(2) = 1f o To1(2) &
  1f o (To1(2) o 0f) o To1(2) = 1f o To1(2)’
 >-- rw[o_assoc] >>
 rw[one_to_one_Id,IdL] )
(form_goal “id(Tp1(𝟙)) = Tp(c𝟙)”));


val id_Tp1_hp = prove_store("id_Tp1_hp",
e0
(rw[GSYM Pt_iff_Tp] >> 
 irule cs_ext >> rw[hp_def] >>
 rw[csT_Pt_id,csR_Pt_id,csL_Pt_id,csB_Pt_id] >>
 rw[Tp0_Tp1_inv,id_dom,id_cod] >>
 rw[id_def,dom_def,cod_def,o_assoc] >>
 rw[one_to_one_Id,zero_def,one_def,two_def,o_assoc,IdL])
(form_goal “id(Tp1(𝟚)) = Tp(h𝟚)”));

val oa_id = prove_store("oa_id",
e0
(cheat)
(form_goal “∀A a:1->A. id(a) @ id(a) = id(a) ”));

val three_ne = prove_store("three_ne",
e0
(cheat)
(form_goal 
 “~(α = β) & ~(α = γ) & ~(α = id(α₁)) & ~(α = id(α₂)) &
  ~(α = id(β₂)) &
  ~(β = γ) & ~(β = id(α₁)) & ~(β = id(α₂)) &
  ~(β = id(β₂)) &
  ~(γ = id(α₁)) & ~(γ = id(α₂)) &
  ~(γ = id(β₂)) &
  ~(id(α₁) = id(α₂)) & ~(id(α₁) = id(β₂)) & 
  ~(id(α₂) = id(β₂))”));

val Thm12_Exp22_3 = prove_store("Thm12_Exp22_3",
e0
(qsuff_tac
 ‘?(cf : fun(Exp(2, 2), 3)).
        !(a : fun(2, Exp(2, 2)))  (b : fun(2, 3)).
          a = Tp(lr𝟚) & b = α |
          a = Tp(ul𝟚) & b = β |
          a = Tp(v𝟚) & b = γ |
          a = Tp(c𝟙) & b = id(β₂) |
          a = Tp(c𝟘) & b = id(α₁) | a = Tp(h𝟚) & b = id(α₂) <=>
          cf o a = b’
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> 
     arw[]) >>
 match_mp_tac
 (CC5 |> qspecl [‘Exp(2,2)’,‘3’] 
     |> fVar_sInst_th “R(f:2->Exp(2,2),g:2->3)”
        “(f = Tp(lr𝟚) & g = α) |
         (f = Tp(ul𝟚) & g = β) |
         (f = Tp(v𝟚) & g = γ) |
         (f = Tp(c𝟙) & g = id(β₂)) |
         (f = Tp(c𝟘) & g = id(α₁)) |
         (f = Tp(h𝟚) & g = id(α₂))”) >>
 strip_tac (* 2 *)
 >-- (strip_tac >> 
     qsspecl_then [‘f’] strip_assume_tac to_Exp22 >> 
     arw[to_Exp22_ne,GSYM to_Exp22_ne,unique_eq]) >>
 strip_tac (* 2 *)
 >-- (rpt gen_tac >> strip_tac >> 
     once_arw[to_Exp22_dom_cod] >> 
     once_arw[id_dom,id_cod,
     to_Exp22_ne] >>
     rw[to_Exp22_dom_cod,id_Tp1_hp,id_Tp1_co,to_Exp22_ne,
        GSYM to_Exp22_ne,id_Tp1_cz] (* 3 *)>>
     rw[three_dom_cod]) >> 
 rpt gen_tac >> strip_tac >> strip_tac >> arw[] (* 6 *)
 >> (rpt gen_tac >> rpt strip_tac >> 
     drule $ iffLR cpsb_def >>
     rfs[to_Exp22_dom_cod,
       to_Exp22_ne,GSYM to_Exp22_ne,Tp1_eq_eq,CC2_0,
       GSYM CC2_0,three_oa,three_ne,oa_id,GSYM three_ne](* 8 *)
     >> fs[twotwo2two_Tp_oa,to_Exp22_ne,GSYM to_Exp22_ne](* 3 *)
     >> fs[to_Exp22_dom_cod,
       to_Exp22_ne,GSYM to_Exp22_ne,Tp1_eq_eq,CC2_0,
       GSYM CC2_0,three_oa,three_ne,oa_id,GSYM three_ne]))
(form_goal 
 “∃f:Exp(2,2) -> 3. 
  f o Tp(lr𝟚) = α & f o Tp(ul𝟚) = β & f o Tp(v𝟚) = γ &
  f o Tp(c𝟙) = id(β₂) & f o Tp(c𝟘) = id(α₁) & f o Tp(h𝟚) = id(α₂)”));

val to_3_cases = 
    Thm11 |> rewr_rule[ab_dom_cod]
          |> rewr_rule[GSYM alpha2_def,GSYM alpha1_def,
                       GSYM beta2_def]

val three_ob_ne = prove_store("three_ob_ne",
e0
(cheat)
(form_goal “~(α₁ = α₂) & ~(α₁ = β₂) & ~(α₂ = β₂)”));

val Thm12_Exp22_3 = prove_store("Thm12_Exp22_3",
e0
(qsuff_tac
 ‘?(cf : fun(3, Exp(2, 2))).
        !(a : fun(2, 3))  (b : fun(2, Exp(2, 2))).
          a = α & b = Tp(lr𝟚) |
          a = β & b = Tp(ul𝟚) |
          a = γ & b = Tp(v𝟚) |
          a = id(β₂) & b = Tp(c𝟙) |
          a = id(α₁) & b = Tp(c𝟘) | a = id(α₂) & b = Tp(h𝟚) <=>
          cf o a = b’
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> 
     arw[]) >>
 match_mp_tac
 (CC5 |> qspecl [‘3’,‘Exp(2,2)’] 
     |> fVar_sInst_th “R(f:2->3,g:2->Exp(2,2))”
        “(f = α & g = Tp(lr𝟚)) |
         (f = β & g = Tp(ul𝟚)) |
         (f = γ & g = Tp(v𝟚)) |
         (f = id(β₂) & g = Tp(c𝟙)) |
         (f = id(α₁) & g = Tp(c𝟘)) |
         (f = id(α₂) & g = Tp(h𝟚))”) >>
 strip_tac (* 2 *)
 >-- (strip_tac >> 
     qsspecl_then [‘f’] strip_assume_tac to_3_cases >>  
     arw[three_ne,GSYM three_ne,unique_eq]) >>
 strip_tac (* 2 *)
 >-- (rpt gen_tac >> strip_tac >> 
     once_arw[three_dom_cod] >> 
     once_arw[id_dom,id_cod,three_ne] >>
     rw[three_dom_cod,id_Tp1_hp,id_Tp1_co,three_ne,
        GSYM three_ne,id_Tp1_cz,to_Exp22_dom_cod] (* 3 *)>>
     rw[three_dom_cod]) >> 
 rpt gen_tac >> strip_tac >> strip_tac >> arw[] (* 6 *)
 >>
  (rpt gen_tac >> rpt strip_tac >> 
     drule $ iffLR cpsb_def >> fs[] >>
     rfs[three_dom_cod,
       three_ne,GSYM three_ne,three_oa,oa_id,id_dom,id_cod,
       three_ob_ne,GSYM three_ob_ne,twotwo2two_Tp_oa]))
(form_goal 
 “∃f:3 -> Exp(2,2). 
  f o α = Tp(lr𝟚)  & f o β = Tp(ul𝟚) & f o γ = Tp(v𝟚) &
  f o id(β₂) = Tp(c𝟙) & f o id(α₁) = Tp(c𝟘) & 
  f o id(α₂) = Tp(h𝟚)”));




val Thm12 = prove_store("Thm12",
e0
(rw[areIso_def] >>
)
(form_goal “areIso(Exp(2,2),3)”));


val _ = add_parse (int_of "η");

val cpnt_def = qdefine_fsym("cpnt",
[‘η:A -> Exp(2,B)’,‘a:1->A’])
‘Pt(η o a) o Pa(Id(2),To1(2))’
|> gen_all


val Nt_def = qdefine_psym("Nt",
[‘η:A -> Exp(2,B)’,‘F:A->B’,‘G:A->B’])
‘(∀f:2->A. csL(Pt(η o f)) = F o f ∧ csR(Pt(η o f)) = G o f)’ |> qgenl [‘A’,‘B’,‘F’,‘G’,‘η’]


(*look through the procedure get one more equation.*)
val csL_Pt_Ed = prove_store("csL_Pt_Ed",
e0
(rw[Er1_def,Ed_def] >> 
 rw[o_assoc,Pa_distr,IdL,To1_def] >>
 rw[Ev_of_Tp_el] >> 
 rw[Pa_distr,p12_of_Pa,To1_def,o_assoc] >>
 rpt strip_tac >> rw[GSYM zero_def] >>
 rw[csL_def,Pt_def,o_assoc,p12_of_Pa,Pa_distr,
    two_def,IdR])
(form_goal
 “∀A B η:A->Exp(2,B) f:2->A.
 csL(Pt(η o f)) :2->B = Er1(B) o Ed(0f, B) o η o f”));


(*look through the procedure get one more equation.*)
val csR_Pt_Ed = prove_store("csR_Pt_Ed",
e0
(rw[Er1_def,Ed_def] >> 
 rw[o_assoc,Pa_distr,IdL,To1_def] >>
 rw[Ev_of_Tp_el] >> 
 rw[Pa_distr,p12_of_Pa,To1_def,o_assoc] >>
 rpt strip_tac >> rw[GSYM one_def] >>
 rw[csR_def,Pt_def,o_assoc,p12_of_Pa,Pa_distr,
    two_def,IdR])
(form_goal
 “∀A B η:A->Exp(2,B) f:2->A.
 csR(Pt(η o f)) :2->B = Er1(B) o Ed(1f, B) o η o f”));

val all_Nt = prove_store("all_Nt",
e0
(rpt strip_tac >> rw[Nt_def] >>
 rw[csL_Pt_Ed,csR_Pt_Ed,o_assoc])
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


(*A -> B^C to C -> B ^ A
Pt(f:X -> Exp(A,B)): A * X -> B
pT(f:X -> Exp(A,B)): X * A -> B
Tp(f:A * X -> B) : X -> Exp(A,B)
tP(f:A * X -> B) : A -> Exp(X,B)
TP(f:X->Exp(A,B)): A-> Exp(X,B)
*)




(*
val pT_Tp = prove_store("pT_Tp",
e0
()
(form_goal
 “pT(Tp(f)) = ”));
*)

val Swap_Pa = prove_store("Swap_Pa",
e0
(rpt strip_tac >> 
 rw[GSYM Swap_def,o_assoc,p12_of_Pa,Pa_eq_eq,Pa_distr])
(form_goal
 “∀X A f:X->A B g. Swap(A,B) o Pa(f,g) = Pa(g,f)”));

val TP_def = qdefine_fsym("TP",[‘f:X->Exp(A,B)’])
‘Tp(pT(f))’

val TP_TP_inv = prove_store("TP_TP_inv",
e0
(rpt strip_tac >>
 rw[TP_def,pT_def,Pt_def] >> irule Ev_eq_eq >>
 rw[Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa,Pa_distr,Swap_Pa]  )
(form_goal “∀X A B f:X->Exp(A,B). TP(TP(f)) = f”));


val TP_eq_eq = prove_store("TP_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 once_rw[GSYM TP_TP_inv] >> arw[])
(form_goal “∀X A B f:X->Exp(A,B) g. TP(f) = TP(g) ⇔ f = g”));



val TP_Ed_o = prove_store("TP_Ed_o",
e0
(rpt strip_tac >> irule Ev_eq_eq >>
 rw[o_assoc,TP_def,Ev_of_Tp_el] >> rw[pT_def] >>
 rw[Pt_def] >> rw[o_assoc,p12_of_Pa,Pa_distr,Swap_Pa] >>
 rw[Ed_def,Ev_of_Tp_el] >>  
 rw[Pa_distr,p12_of_Pa,o_assoc] )
(form_goal
 “∀X Y f:X-> Y T u:T -> Exp(Y,A).
   TP(Ed(f, A) o u) = TP(u) o f”));

val Pa_o_split = prove_store("Pa_o_split",
e0
(rpt strip_tac >> irule to_P_eq >>
 rw[p12_of_Pa] >> rw[GSYM o_assoc,p12_of_Pa] >>
 rw[o_assoc,p12_of_Pa])
(form_goal
 “!B X f:B->X Y g:X->Y A.Pa(p1(A,B),g:X->Y o f o p2(A,B)) = 
  Pa(p1(A,X), g o p2(A,X)) o Pa(p1(A,B),f o p2(A,B))”));


val Ed_o = prove_store("Ed_o",
e0
(rw[Ed_def] >> rpt strip_tac >>
 irule Ev_eq_eq >> rw[Ev_of_Tp_el] >>
 rw[o_assoc,p12_of_Pa,Pa_distr] >>
 rw[Pa_o_split] >> rw[GSYM o_assoc,Ev_of_Tp_el] >>
 rw[o_assoc,p12_of_Pa,Pa_distr] >> 
 rw[Ev_of_Tp_el] >> rw[Pa_distr,o_assoc,p12_of_Pa])
(form_goal
 “∀A B f:A->B C g:B->C X. Ed(g o f,X) = 
 Ed(f,X) o Ed(g,X)”));


val Ed_eq = prove_store("Ed_eq",
e0
(rpt strip_tac >> rw[Ed_def] >> arw[])
(form_goal
 “∀A B f:A->B g. f = g ⇒ Ed(f,X) = Ed(g,X)”));


val Ed_Po_Pb = prove_store("Ed_Po_Pb",
e0
(rpt strip_tac >> rw[isPb_def] >> 
 qby_tac
 ‘Ed(f, A) o Ed(p, A) = Ed(g, A) o Ed(q, A)’
 >-- (rw[GSYM Ed_o] >> fs[isPo_def] >>
     irule Ed_eq >> arw[]) >>
 arw[] >> rpt strip_tac >>
 fs[isPo_def] >>
 first_x_assum (qsspecl_then [‘TP(u)’,‘TP(v)’] assume_tac) >>
 qby_tac
 ‘TP(u) o f = TP(v) o g’ 
 >-- (qby_tac
     ‘TP(u) o f = TP(Ed(f, A) o u) &
      TP(v) o g = TP(Ed(g, A) o v)’ 
     >-- arw[GSYM TP_Ed_o] >>
     arw[]) >>
 first_x_assum drule >>
 qsuff_tac
 ‘∀a: A'-> Exp(P,A). 
  (Ed(p, A) o a = u & Ed(q, A) o a = v) ⇔
  TP(a) o p = TP(u) & TP(a) o q = TP(v)’
 >-- (strip_tac >> arw[] >>
     pop_assum (K all_tac) >>
     pop_assum (strip_assume_tac o uex_expand) >>
     uex_tac >> qexists_tac ‘TP(a)’ >>
     rw[TP_TP_inv] >> arw[] >> rpt strip_tac >>
     irule $ iffLR TP_eq_eq >> rw[TP_TP_inv] >>
     first_x_assum irule >> arw[]) >>
 rpt strip_tac >> once_rw[GSYM TP_eq_eq] >>
 rw[TP_Ed_o] >> rw[TP_eq_eq])
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

(*
val Ed_ab_Pb = prove_store("Ed_ab_Pb",
e0
(cheat)
(form_goal “∀A.isPb(Er1(A) o Ed(1f,A),Er1(A) o Ed(0f,A),Ed(α,A),Ed(β,A))”));
not really used
*)

val irt_uex = proved_th $
e0
(rpt strip_tac >>
 qcases ‘Ed(1f, B) o η = Ed(0f, B) o ε’ (* 2 *)
 >-- (arw[] >>
 assume_tac Ed_ab_Pb0 >>
 first_x_assum (qspecl_then [‘B’] assume_tac) >>
 drule $ iffLR isPb_def >>
 pop_assum strip_assume_tac >>
 first_x_assum irule >> arw[]) >> arw[] >>
 uex_tac >> qexists_tac ‘Ed((0f o To1(3)), B) o η’ >>
 rw[])
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
(rpt gen_tac >>
 assume_tac irt_def0 >>
 strip_tac >> fs[] >>
 qsspecl_then [‘η’,‘ε’] assume_tac irt_uex >>
 rfs[] >> 
 pop_assum (strip_assume_tac o uex_expand) >> arw[] >>
 rpt strip_tac >>
 qsuff_tac ‘a' = a & irt(η,ε) = a’
 >-- (strip_tac >> arw[]) >> arw[] >>
 strip_tac >> first_x_assum irule >> arw[])
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

(*
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
*)

val CC6 = store_ax("CC6",
“?A f:2->A. iso(f) & ~isid(f)”); 
 
(*
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
*)

val id_cod_id = prove_store("id_cod_id",
e0
(rw[id_def,cod_def,o_assoc,To1_def])
(form_goal “∀A g:2->A. id(cod(id(cod(g)))) = id(cod(g))”));


val isid_alt = prove_store("isid_alt",
e0
(rw[isid_def] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[id_def,dom_def] >> arw[one_to_one_Id] >>
     qby_tac
     ‘((f0 o To1(2)) o 0f) o To1(2) = 
      f0 o (To1(2) o 0f) o To1(2)’
     >-- rw[o_assoc] >>
     arw[one_to_one_Id,IdL]) >>
 fs[id_def,dom_def] >>
 qexists_tac ‘f o 0f’ >> fs[])
(form_goal
 “!A f:2->A. isid(f) <=> 
   id(dom(f)) = f”)); 



val csB_Pt_Tp0 = prove_store("csB_Pt_Tp0",
e0
(rpt strip_tac >> rw[csB_Pt,GSYM Tp0_def,Er1_def] >>
rw[o_assoc,Ed_def,IdL,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el] >> 
rw[o_assoc,Pa_distr,To1_def,p12_of_Pa] >>
rw[Ev_of_Tp_el'] >> 
rw[o_assoc,Swap_Pa,Pt_def,Pa_distr,p12_of_Pa,cod_def])
(form_goal
“∀A g:2->Exp(2,A). 
 csB(Pt(g)) = Tp0(cod(g))”));


val csT_Pt_Tp0 = prove_store("csT_Pt_Tp0",
e0
(rpt strip_tac >> rw[csT_Pt,GSYM Tp0_def,Er1_def] >>
rw[o_assoc,Ed_def,IdL,Pa_distr,p12_of_Pa] >>
 rw[Ev_of_Tp_el] >> 
rw[o_assoc,Pa_distr,To1_def,p12_of_Pa] >>
rw[Ev_of_Tp_el'] >> 
rw[o_assoc,Swap_Pa,Pt_def,Pa_distr,p12_of_Pa,dom_def])
(form_goal
“∀A g:2->Exp(2,A). 
 csT(Pt(g)) = Tp0(dom(g))”));

(*
val csT_Pt_oa = prove_store("csT_Pt_oa",
e0
(rpt strip_tac >>
rw[csT_def,Pt_def,o_assoc] >> 
rw[Pa_distr,p12_of_Pa,o_assoc,zero_def] >>
rw[GSYM o_assoc,GSYM dom_def] >>
drule oa_dom_cod >> arw[])
(form_goal
“∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒
 csT(Pt(g1 @ f1)) =  csT(Pt(f1))”));


val csB_Pt_oa = prove_store("csB_Pt_oa",
e0
(rpt strip_tac >>
rw[csB_def,Pt_def,o_assoc] >> 
rw[Pa_distr,p12_of_Pa,o_assoc,one_def] >>
rw[GSYM o_assoc,GSYM cod_def] >>
drule oa_dom_cod >> arw[])
(form_goal
“∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒
 csB(Pt(g1 @ f1)) = csB(Pt(g1))”));


val Pa_cpsb_one = prove_store("Pa_cpsb_one",
e0
(rpt strip_tac >> rw[cpsb_def] >>
 rw[dom_def,cod_def,Pa_distr] >> 
 rw[GSYM dom_def,GSYM cod_def] >> fs[cpsb_def,dom_cod_zot])
(form_goal
 “∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ cpsb(Pa(𝟙,g1),Pa(𝟙,f1))”));


val Pa_cpsb_zero = prove_store("Pa_cpsb_zero",
e0
(rpt strip_tac >> rw[cpsb_def] >>
 rw[dom_def,cod_def,Pa_distr] >> 
 rw[GSYM dom_def,GSYM cod_def] >> fs[cpsb_def,dom_cod_zot])
(form_goal
 “∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ cpsb(Pa(𝟘,g1),Pa(𝟘,f1))”));

val Pa_oa_distr_one = prove_store("Pa_oa_distr_one",
e0
(rpt strip_tac >>
 qby_tac
 ‘Pa(𝟙, g1 @ f1) = Pa(1f o To1(Exp(2,A)),Id(Exp(2,A))) o  g1 @ f1’
 >-- rw[Pa_distr,To1_def,IdL,o_assoc,GSYM one_def] >>
 rev_drule fun_pres_oa >> fs[] >>
 rw[Pa_distr,p12_of_Pa,IdL,To1_def,o_assoc] >>
 rw[one_def])
(form_goal
“∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ 
 Pa(𝟙, g1 @ f1) = Pa(𝟙,g1) @ Pa(𝟙,f1)”));



val Pa_oa_distr_zero = prove_store("Pa_oa_distr_zero",
e0
(rpt strip_tac >>
 qby_tac
 ‘Pa(𝟘, g1 @ f1) = Pa(0f o To1(Exp(2,A)),Id(Exp(2,A))) o  g1 @ f1’
 >-- rw[Pa_distr,To1_def,IdL,o_assoc,GSYM zero_def] >>
 rev_drule fun_pres_oa >> fs[] >>
 rw[Pa_distr,p12_of_Pa,IdL,To1_def,o_assoc] >>
 rw[zero_def])
(form_goal
“∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ 
 Pa(𝟘, g1 @ f1) = Pa(𝟘,g1) @ Pa(𝟘,f1)”));


val csR_Pt_oa = prove_store("csR_Pt_oa",
e0
(rpt strip_tac >>
rw[csR_def,Pt_def,o_assoc] >>  
rw[Pa_distr,p12_of_Pa,o_assoc,two_def,IdR] >>
qby_tac ‘cpsb(Pa(𝟙,g1),Pa(𝟙,f1))’
>-- (drule Pa_cpsb_one >> arw[]) >> 
qby_tac
‘Pa(𝟙, g1 @ f1) = Pa(𝟙,g1) @ Pa(𝟙,f1)’
>-- (drule Pa_oa_distr_one >> arw[]) >>
drule fun_pres_oa >> arw[])
(form_goal “∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ 
 csR(Pt(g1:2->Exp(2,A))) @ csR(Pt(f1)) = csR(Pt(g1 @ f1))”));


val csL_Pt_oa = prove_store("csL_Pt_oa",
e0
(rpt strip_tac >>
rw[csL_def,Pt_def,o_assoc] >>  
rw[Pa_distr,p12_of_Pa,o_assoc,two_def,IdR] >>
qby_tac ‘cpsb(Pa(𝟘,g1),Pa(𝟘,f1))’
>-- (drule Pa_cpsb_zero >> arw[]) >> 
qby_tac
‘Pa(𝟘, g1 @ f1) = Pa(𝟘,g1) @ Pa(𝟘,f1)’
>-- (drule Pa_oa_distr_zero >> arw[]) >>
drule fun_pres_oa >> arw[])
(form_goal “∀A f1 g1:2->Exp(2,A).
 cpsb(g1,f1) ⇒ 
 csL(Pt(g1)) @ csL(Pt(f1)) = csL(Pt(g1 @ f1))”));
*)

(*
val cs2_arrows = prove_store("cs2_arrows",
e0
(strip_tac >> 
 qsspecl_then [‘f’] strip_assume_tac to_P_has_comp >>
 qsspecl_then [‘a’] strip_assume_tac CC2_1 >>
 qsspecl_then [‘b’] strip_assume_tac CC2_1 >> fs[])
(form_goal
 “∀f:2-> 2 * 2. 
   f = Pa(𝟘,𝟘)| f = Pa(𝟘,𝟙) | f = Pa(𝟙,𝟘) | f = Pa(𝟙,𝟙) |
   f = Pa(𝟘,𝟚)| f = Pa(𝟚,𝟙) | f = Pa(𝟚,𝟘) | f = Pa(𝟙,𝟚) |
   f = Pa(𝟚,𝟚)”));


val dom_cod_Pa02 = prove_store("dom_cod_Pa02",
e0
(rw[dom_def,cod_def,Pa_distr] >>
 rw[GSYM dom_def,GSYM cod_def] >>
 rw[Pa_eq_eq,dom_cod_zot])
(form_goal “dom(Pa(𝟘,𝟚)) = Pa(0f,0f) & 
            cod(Pa(𝟘,𝟚)) = Pa(0f,1f) ”));


val dom_cod_Pa12 = prove_store("dom_cod_Pa12",
e0
(rw[dom_def,cod_def,Pa_distr] >>
 rw[GSYM dom_def,GSYM cod_def] >>
 rw[Pa_eq_eq,dom_cod_zot])
(form_goal “dom(Pa(𝟙,𝟚)) = Pa(1f,0f) & 
            cod(Pa(𝟙,𝟚)) = Pa(1f,1f) ”));

val Pa00_id = prove_store("Pa00_id",
e0
(rw[id_def,Pa_distr,Pa_eq_eq,zero_def])
(form_goal “Pa(𝟘,𝟘) = id(Pa(0f,0f))”));


val Pa10_id = prove_store("Pa10_id",
e0
(rw[id_def,Pa_distr,Pa_eq_eq,zero_def,one_def])
(form_goal “Pa(𝟙,𝟘) = id(Pa(1f,0f))”));


val Pa01_id = prove_store("Pa01_id",
e0
(rw[id_def,Pa_distr,Pa_eq_eq,zero_def,one_def])
(form_goal “Pa(𝟘,𝟙) = id(Pa(0f,1f))”));


val Pa11_id = prove_store("Pa11_id",
e0
(rw[id_def,Pa_distr,Pa_eq_eq,one_def])
(form_goal “Pa(𝟙,𝟙) = id(Pa(1f,1f))”));


val cs_ext = prove_store("cs_ext",
e0
(rpt strip_tac >> 
 qby_tac
 ‘s1 o Pa(𝟚, 𝟚) = s2 o Pa(𝟚, 𝟚)’
 >-- (rw[GSYM RT_cs2] >>
     assume_tac cs2_RT_cpsb >> drule fun_pres_oa >>
     fs[csL_def,csR_def,csT_def,csB_def]) >>
 qby_tac
 ‘s1 o Pa(𝟘, 𝟘) = s2 o Pa(𝟘, 𝟘)’ 
 >-- (fs[csL_def] >> 
     rw[Pa00_id,GSYM dom_cod_Pa02,id_def,dom_def] >>
     arw[GSYM o_assoc]) >>
 qby_tac
 ‘s1 o Pa(𝟙, 𝟘) = s2 o Pa(𝟙, 𝟘)’ 
 >-- (fs[csR_def] >> 
     rw[Pa10_id,GSYM dom_cod_Pa12,id_def,dom_def] >>
     arw[GSYM o_assoc]) >>
 qby_tac
 ‘s1 o Pa(𝟘,𝟙) = s2 o Pa(𝟘,𝟙)’ 
 >-- (fs[csL_def] >> 
     rw[Pa01_id,GSYM dom_cod_Pa02,id_def,cod_def] >>
     arw[GSYM o_assoc]) >>
 qby_tac
 ‘s1 o Pa(𝟙,𝟙) = s2 o Pa(𝟙,𝟙)’ 
 >-- (fs[csR_def] >> 
     rw[Pa11_id,GSYM dom_cod_Pa12,id_def,cod_def] >>
     arw[GSYM o_assoc]) >>
 fs[csL_def,csR_def,csT_def,csB_def] >>
 irule $ iffLR fun_ext >>
 strip_tac >>
 qsspecl_then [‘a’] strip_assume_tac cs2_arrows >>
 fs[])
(form_goal
 “∀s1 s2: 2 * 2 ->A.
  csL(s1) = csL(s2) &
  csR(s1) = csR(s2) &
  csT(s1) = csT(s2) &
  csB(s1) = csB(s2) ⇒ s1 = s2”));


val Tp0_eq_eq = prove_store("Tp0_eq_eq",
e0
(cheat)
(form_goal “∀A B f:1->Exp(A,B) g. Tp0(f) = Tp0(g) ⇔ f = g”));
*)
(*
val dom_Tp_cs = prove_store("dom_Tp_cs",
e0
(rw[dom_def,Tp_def,Tp1_def,csT_def] >>
 rpt strip_tac >> irule $ iffLR Tp0_eq_eq >>
 rw[Tp0_Tp1_inv] >>
 rw[GSYM Tp0_def,o_assoc,Ev_of_Tp_el] >> 
 rw[two_def,zero_def])
(form_goal
 “∀A cs:2 * 2 ->A. 
  dom(Tp(cs)) = Tp1(csT(cs))”));



val cod_Tp_cs = prove_store("cod_Tp_cs",
e0
(rw[cod_def,Tp_def,Tp1_def,csB_def] >>
 rpt strip_tac >> irule $ iffLR Tp0_eq_eq >>
 rw[Tp0_Tp1_inv] >>
 rw[GSYM Tp0_def,o_assoc,Ev_of_Tp_el] >> 
 rw[two_def,one_def])
(form_goal
 “∀A cs:2 * 2 ->A. 
  cod(Tp(cs)) = Tp1(csB(cs))”));
*)

(*
local
val l = 
csT_Pt |> qsspecl [‘id(a:1-> Exp(2,A))’] 
       |> rewr_rule[id_def,Tp_def,Pt_def,Er1_def]
       |> rewr_rule[o_assoc,p12_of_Pa,To1_def,Pa_distr,Ed_def]
       |> rewr_rule[IdL,Ev_of_Tp_el,o_assoc,
                    Pa_distr,p12_of_Pa,To1_def]
       |> rewr_rule[GSYM Swap_def,p12_of_Pa]
       |> rewr_rule[Ev_of_Tp_el',o_assoc,p12_of_Pa,Pa_distr]
       |> rewr_rule[To1_def]
       |> rewr_rule[Tp0_def]
in
val csT_Pt_id = prove_store("csT_Pt_id",
e0
(rw[Pt_def,id_def,o_assoc,To1_def] >>
 rw[l]) 
(form_goal “!A a:1->Exp(2,A).
 csT(Pt(id(a))) = Tp0(a)”));
end


local
val l = 
csB_Pt |> qsspecl [‘id(a:1-> Exp(2,A))’] 
       |> rewr_rule[id_def,Tp_def,Pt_def,Er1_def]
       |> rewr_rule[o_assoc,p12_of_Pa,To1_def,Pa_distr,Ed_def]
       |> rewr_rule[IdL,Ev_of_Tp_el,o_assoc,
                    Pa_distr,p12_of_Pa,To1_def]
       |> rewr_rule[GSYM Swap_def,p12_of_Pa]
       |> rewr_rule[Ev_of_Tp_el',o_assoc,p12_of_Pa,Pa_distr]
       |> rewr_rule[To1_def]
       |> rewr_rule[Tp0_def]
in
val csB_Pt_id = prove_store("csB_Pt_id",
e0
(rw[Pt_def,id_def,o_assoc,To1_def] >>
 rw[l]) 
(form_goal “!A a:1->Exp(2,A).
 csB(Pt(id(a))) = Tp0(a)”));
end


local
val l = 
csR_Pt |> qsspecl [‘id(a:1-> Exp(2,A))’] 
       |> rewr_rule[id_def,Tp_def,Pt_def,Er1_def]
       |> rewr_rule[o_assoc,p12_of_Pa,To1_def,Pa_distr,Ed_def]
       |> rewr_rule[IdL,Ev_of_Tp_el,o_assoc,
                    Pa_distr,p12_of_Pa,To1_def]
       |> rewr_rule[GSYM Swap_def,p12_of_Pa]
       |> rewr_rule[Ev_of_Tp_el',o_assoc,p12_of_Pa,Pa_distr]
       |> rewr_rule[To1_def]
       |> rewr_rule[Tp0_def]
in
val csR_Pt_id = prove_store("csR_Pt_id",
e0
(rw[Pt_def,id_def,o_assoc,To1_def] >>
 rw[l] >> rw[cod_def,GSYM Tp0_def] >>
 rw[Pa_distr,p12_of_Pa,IdL,o_assoc,To1_def] ) 
(form_goal “!A a:1->Exp(2,A).
 csR(Pt(id(a))) = id(cod(Tp0(a)))”));
end


local
val l = 
csL_Pt |> qsspecl [‘id(a:1-> Exp(2,A))’] 
       |> rewr_rule[id_def,Tp_def,Pt_def,Er1_def]
       |> rewr_rule[o_assoc,p12_of_Pa,To1_def,Pa_distr,Ed_def]
       |> rewr_rule[IdL,Ev_of_Tp_el,o_assoc,
                    Pa_distr,p12_of_Pa,To1_def]
       |> rewr_rule[GSYM Swap_def,p12_of_Pa]
       |> rewr_rule[Ev_of_Tp_el',o_assoc,p12_of_Pa,Pa_distr]
       |> rewr_rule[To1_def]
       |> rewr_rule[Tp0_def]
in
val csL_Pt_id = prove_store("csL_Pt_id",
e0
(rw[Pt_def,id_def,o_assoc,To1_def] >>
 rw[l] >> rw[dom_def,GSYM Tp0_def] >>
 rw[Pa_distr,p12_of_Pa,IdL,o_assoc,To1_def] ) 
(form_goal “!A a:1->Exp(2,A).
 csL(Pt(id(a))) = id(dom(Tp0(a)))”));
end
*)

val Thm14 = prove_store("Thm14",
e0
(strip_assume_tac CC6 >> 
 qexistsl_tac [‘Exp(2,A)’,‘Tp1(f)’,‘Tp1(id(dom(f)))’] >>
 qby_tac ‘~(f = id(dom(f)))’ 
 >-- (flip_tac >> rw[GSYM isid_alt] >> arw[]) >>
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
 arw[] >> rw[GSYM id_def] >>
 strip_tac >-- (* 2 *)
 (irule $ iffLR Pt_eq_eq >>
 irule cs_ext >>
 qby_tac ‘cpsb(Tp(q'),Tp(q))’ >-- 
 (rw[cpsb_def] >> rw[dom_Tp_cs,cod_Tp_cs] >>
 arw[id_def]) >>
 drule csT_Pt_oa >> 
 drule $ GSYM csR_Pt_oa >> arw[Pt_Tp]  >>
 drule $ GSYM csL_Pt_oa >> arw[Pt_Tp] >>
 drule csB_Pt_oa>> arw[Pt_Tp] >>
 rw[csR_Pt_id,csB_Pt_id,csT_Pt_id,csL_Pt_id]  >>
 qby_tac ‘f = Tp0(cod(Tp(q')))’ 
 >-- (qpick_x_assum ‘Tp1(f) = cod(Tp(q'))’ 
     (assume_tac o GSYM) >> 
     arw[Tp0_Tp1_inv]) >> arw[] >>
 rw[GSYM id_def] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 irule cpsb_idL >>
 rw[cpsb_def,id_dom,id_cod]) >>
 irule $ iffLR Pt_eq_eq >> 
 irule cs_ext >> 
 qby_tac ‘cpsb(Tp(q),Tp(q'))’ >-- 
 (rw[cpsb_def] >> rw[dom_Tp_cs,cod_Tp_cs] >>
 arw[id_def]) >>
 rw[csR_Pt_id,csB_Pt_id,csT_Pt_id,csL_Pt_id,Tp0_Tp1_inv] >>
 rw[id_dom,id_cod] >>
 drule csT_Pt_oa >> 
 drule $ GSYM csR_Pt_oa >> arw[Pt_Tp]  >>
 drule $ GSYM csL_Pt_oa >> arw[Pt_Tp] >>
 drule csB_Pt_oa>> arw[Pt_Tp] >> 
 rw[GSYM id_def] >>
 irule cpsb_idL >>
 rw[cpsb_def,id_dom,id_cod])
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
(dimp_tac >> rpt strip_tac (* 2 *)
 >-- arw[] >>
 qcases ‘A’ >> arw[] >>
 first_x_assum drule >> arw[])
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

(*?(cf : fun(B, C)).
               !(a : fun(2, B))  (b : fun(2, C)).
                 dom(a#) = B0 & ~cod(a#) = B0 & b# = h |
                 ~dom(a#) = B0 & cod(a#) = B0 & b# = k |
                 dom(a#) = B0 & cod(a#) = B0 & b# = h o 𝟘 |
                 ~dom(a#) = B0 & ~cod(a#) = B0 & b# = h o 𝟙 <=> cf# o a# = b#

?(cf : fun(B, C)).
               !(a : fun(2, B))  (b : fun(2, C)).
                 dom(a#) = B0 & ~cod(a#) = B0 & b# = h |
                 ~dom(a#) = B0 & cod(a#) = B0 & b# = k |
                 dom(a#) = B0 & cod(a#) = B0 & b# = h o 𝟘 |
                 ~dom(a#) = B0 & ~cod(a#) = B0 & b# = h o 𝟙 <=> cf# o a# = b#

 (k : fun(2, C))(h : fun(2, C))(f : fun(A, B))(T2 : fun(1, C))(T1 :
      fun(1, C))(B0 : fun(1, B))CBA

(k : fun(2, C))(h : fun(2, C))(g : fun(A2, B))(f : fun(A1, B))(T2 :
      fun(1, C))(T1 : fun(1, C))(B0 : fun(1, B))CBA2A1

*)
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
 >-- (fs[GSYM cpsb_def] >>
     drule oa_dom_cod >> arw[]) >>
 qby_tac ‘(h o 𝟙) @ h = h ∧ h @ (h o 𝟘) = h ∧ 
          k @ h = h o 𝟘 ∧ h @ k = h o 𝟙 ∧
          (h o 𝟘) @ k = k ∧ k @ (h o 𝟙) = k ∧ 
          (h o 𝟘) @ h o 𝟘 = (h o 𝟘) ∧
          (h o 𝟙) @ h o 𝟙 = (h o 𝟙)’
 >-- (rw[one_def,zero_def] >>
     rw[GSYM o_assoc] >> rw[GSYM dom_def,GSYM cod_def] >>
     rw[GSYM id_def] >> arw[] >>
     rw[GSYM id_def] >> rpt strip_tac (* 6 *)
     >-- (irule cpsb_idL >> arw[id_dom,cpsb_def]) 
     >-- (irule cpsb_idR >> arw[id_cod,cpsb_def]) 
     >-- (irule cpsb_idL >> arw[id_dom,cpsb_def]) 
     >-- (irule cpsb_idR >> arw[id_cod,cpsb_def]) 
     >-- (irule cpsb_idR >> rw[id_dom,id_cod,cpsb_def]) >>
     irule cpsb_idR >> rw[id_dom,id_cod,cpsb_def]) >>
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

val zero_isid = prove_store("zero_isid",
e0
(rw[zero_def,isid_def] >>
 qexists_tac ‘0f’ >> rw[])
(form_goal “isid(𝟘)”));


val one_isid = prove_store("one_isid",
e0
(rw[one_def,isid_def] >>
 qexists_tac ‘1f’ >> rw[])
(form_goal “isid(𝟙)”));

val t2t_notid_two = prove_store("t2t_notid_two",
e0
(rpt strip_tac >>
 qsspecl_then [‘f’] strip_assume_tac CC2_1 >> 
 fs[zero_isid,one_isid])
(form_goal “∀f:2->2. ~isid(f) ⇒ f = 𝟚”));

val Thm16_init_case = prove_store("Thm16_init_case",
e0
(cheat)
(form_goal
 “!A B f:2->A + B. 
   (∀fa:1->A.F) | (∀fb:2->B.F) ⇒ 
   (?f0:2->A. f = i1(A,B) o f0) |
                   (?f0:2->B. f = i2(A,B) o f0)”));

val Thm15_comment = prove_store("Thm15_comment",
e0
(cheat(*need to reprove, not follow from Thm15, same idea, but need to be proved separetely*) )
(form_goal 
 “∀A B ab:1->A + B. (∃a:1->A. ab = i1(A,B) o a) |
 (∃b. ab = i2(A,B) o b)”));

val id_o = prove_store("id_o",
e0
(rw[id_def,o_assoc])
(form_goal “∀A a:1->A B F:A->B.id(F o a) = F o id(a)”));

val o_cpsb = prove_store("o_cpsb",
e0
(rpt strip_tac >> fs[cpsb_def,dom_o,cod_o])
(form_goal
 “∀A g:2->A f B F:A->B. cpsb(g,f) ⇒ cpsb(F o g,F o f)”));

val Thm16_non_init_case = prove_store("Thm16_non_init_case",
e0
(rpt strip_tac >> 
 qby_tac ‘∃j k. j o i1(A,B) = Id(A) ∧ k o i2(A,B) = Id(B)’
 >-- (qexistsl_tac [‘coPa(Id(A),fa o To1(B))’,
                   ‘coPa(fb o To1(A),Id(B))’] >>
     rw[i12_of_coPa]) >>
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
 qby_tac 
 ‘∃l: A + B -> 2. 
  (∀a : 1->A. l o i1(A,B) o a = 0f) ∧ 
  (∀b:1->B. l o i2(A,B) o b = 1f)’ 
 >-- (qexistsl_tac [‘coPa(0f o To1(A),1f o To1(B))’] >>
     rw[GSYM o_assoc,i12_of_coPa] >>
     rw[o_assoc,one_to_one_Id] >> rw[IdR]) >> 
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
 qby_tac ‘∀p:2->A + B d0:1->A. dom(p) = i1(A,B) o d0 ⇒ 
 ~(∃c0:1->B. cod(p) = i2(A,B) o c0)’ >--
  (qby_tac 
 ‘∃l1: A + B -> 2. 
  (∀a : 1->A. l1 o i1(A,B) o a = 1f) ∧ 
  (∀b:1->B. l1 o i2(A,B) o b = 0f)’ 
 >-- (qexistsl_tac [‘coPa(1f o To1(A),0f o To1(B))’] >>
     rw[GSYM o_assoc,i12_of_coPa] >>
     rw[o_assoc,one_to_one_Id] >> rw[IdR]) >> 
 pop_assum strip_assume_tac >> 
 rpt strip_tac >>
 ccontra_tac >> pop_assum strip_assume_tac >> 
 cases_on “isid(l1:A + B ->2 o p: 2 -> A + B)”    
 >-- (fs[isid_def] >> 
     qby_tac ‘l1 o p o 1f = l1 o p o 0f’
     >-- (arw[GSYM o_assoc] >> rw[one_to_one_Id,IdR,o_assoc]) >>
     rfs[dom_def,cod_def,zf_ne_of]) >>
 drule t2t_notid_two >> 
 qby_tac ‘l1 o p o 1f = 1f ∧ l1 o p o 0f = 0f’
 >-- (strip_tac >> arw[GSYM o_assoc,two_def,IdL]) >>
 rfs[dom_def,cod_def,GSYM zf_ne_of]) >> 
 qsuff_tac
 ‘?(cf : fun(A + B, A + B)).
        !(f : fun(2, A + B))  (g : fun(2, A + B)).
          (?(a : fun(1, A)). dom(f) = i1(A, B) o a & g = i1(A, B) o j o f) |
          (?(b : fun(1, B)). dom(f) = i2(A, B) o b & g = i2(A, B) o k o f) <=>
          cf o f = g’ >--
 (strip_tac >>
 qby_tac ‘cf = Id(A+B)’ >--
 (first_x_assum irule >> rpt strip_tac (* 2 *)
 >-- (first_x_assum (irule o iffLR) >>
     disj1_tac >>
     qexists_tac ‘d0’ >> arw[]) >>
 first_x_assum (irule o iffLR) >>
 disj2_tac >> qexists_tac ‘d0’ >> arw[]) >> fs[IdL] >>
 first_x_assum (qsspecl_then [‘f’,‘f’] assume_tac) >>
 pop_assum mp_tac >> rw[] >>
 strip_tac (* 2 *)
 >-- (disj1_tac >> qexists_tac ‘j o f’ >>
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 disj2_tac >> qexists_tac ‘k o f’ >>
 pop_assum (assume_tac o GSYM) >> arw[]) >>
 match_mp_tac
 (CC5 |> qspecl [‘A + B’,‘A + B’] 
 |> fVar_sInst_th “R(f:2->A + B,g:2->A + B)”
    “(∃a:1->A. dom(f) = i1(A,B) o a &
             g = i1(A,B) o j o f) |
     (∃b:1->B. dom(f) = i2(A,B) o b &
             g = i2(A,B) o k o f)”) >>
 qby_tac ‘Mono(i1(A,B)) & Mono(i2(A,B))’ 
 >-- cheat >> 
 pop_assum strip_assume_tac >> 
 qby_tac
‘!(p : fun(2, A + B))  (d0 : fun(1, A)).
               dom(p) = i1(A, B) o d0 ==>
               ∃c0:1->A. cod(p) = i1(A, B) o c0’
 >-- cheat >> 
 qby_tac
‘!(p : fun(2, A + B))  (d0 : fun(1, B)).
               dom(p) = i2(A, B) o d0 ==>
               ∃c0:1->B. cod(p) = i2(A, B) o c0’
 >-- cheat >> 
 qby_tac
 ‘∀ab:1->A + B a. 
  ab = i1(A,B) o a ⇒
  ∀b. ~(ab = i2(A,B) o b)’ 
 >-- (rpt strip_tac >> ccontra_tac >>
     last_x_assum (qsspecl_then [‘id(ab)’,‘a’] assume_tac)>>
     pop_assum mp_tac >> rw[id_cod,id_dom] >>
     ccontra_tac >>
     first_x_assum drule >>
     qsuff_tac ‘?(c0 : fun(1, B)). ab = i2(A, B) o c0’ 
     >-- arw[] >> qexists_tac ‘b’ >> arw[]) >>
 qby_tac
 ‘∀ab:1->A + B b. 
  ab = i2(A,B) o b ⇒
  ∀a. ~(ab = i1(A,B) o a)’ 
 >-- (rpt strip_tac >> ccontra_tac >>
     last_x_assum (qsspecl_then [‘id(ab)’,‘b’] assume_tac)>>
     pop_assum mp_tac >> rw[id_cod,id_dom] >>
     ccontra_tac >>
     first_x_assum drule >>
     qsuff_tac ‘?(c0 : fun(1, A)). ab = i1(A, B) o c0’ 
     >-- arw[] >> qexists_tac ‘a’ >> arw[]) >>
 strip_tac (* 2 *)
 >-- (strip_tac >>
     qsspecl_then [‘dom(f')’] strip_assume_tac
     Thm15_comment (* 2 *)
     >-- (uex_tac >> qexists_tac ‘i1(A, B) o j o f'’ >>
         rpt strip_tac (* 2 *)
         >-- (disj1_tac >> qexists_tac ‘a’ >>
             arw[]) >> 
         first_x_assum drule >>
         fs[]) >>
     uex_tac >> qexists_tac ‘i2(A,B) o k o f'’ >>
     rpt strip_tac (* 2 *)
     >-- (disj2_tac >> qexists_tac ‘b’ >> arw[]) >>
     first_x_assum drule >> fs[]) >> strip_tac (* 2 *)
 >-- (rw[id_dom,id_cod] >> rpt strip_tac (* 4 *)
     >-- (disj1_tac >> qexists_tac ‘a’ >>
         arw[] >> arw[dom_o,id_o])
     >-- (disj1_tac >> 
         arw[id_o,cod_o] >> 
         first_x_assum 
         (qsspecl_then [‘f'’,‘a’] assume_tac) >>
         first_x_assum drule >> arw[]) 
     >-- (disj2_tac >> qexists_tac ‘b’ >>
         arw[dom_o,id_o]) >>
     disj2_tac >> arw[id_o,cod_o] >>
     first_x_assum irule >> qexists_tac ‘b’ >> arw[]) >>
 qby_tac
 ‘∀a:1->A b:1->B. ~(i1(A,B) o a = i2(A,B) o b)’
 >-- (rpt strip_tac >> ccontra_tac >>
     first_x_assum drule >> 
     first_x_assum (qspecl_then [‘a’] assume_tac) >> fs[])>>
 rpt strip_tac (* 8 *)
 >-- (arw[] >> drule fun_pres_oa >> arw[] >>
     irule fun_pres_oa >>
     irule o_cpsb >> arw[])
 >-- (drule $ iffLR cpsb_def >>
     first_x_assum (qsspecl_then [‘f'’,‘a'’] assume_tac) >>
     first_x_assum drule >> pop_assum strip_assume_tac >>
     qsuff_tac
     ‘i1(A, B) o c0 = i2(A, B) o b’ >--arw[] >>
     qpick_x_assum ‘dom(g) = i2(A, B) o b’
     (assume_tac o GSYM) >> 
     qpick_x_assum ‘!(a : fun(1, A))  (b : fun(1, B)). 
     ~(i1(A, B) o a = i2(A, B) o b)’ (K all_tac) >>
     arw[]) 
 >-- (drule $ iffLR cpsb_def >>
     first_x_assum (qsspecl_then [‘f'’,‘b’] assume_tac) >>
     first_x_assum drule >>
     pop_assum strip_assume_tac >>
     first_x_assum (qsspecl_then [‘a'’,‘c0’] assume_tac) >>
     qsuff_tac
     ‘i1(A, B) o a' = i2(A, B) o c0’ >-- arw[] >>
     pop_assum (K all_tac) >>
     qpick_x_assum ‘dom(g) = i1(A, B) o a'’ 
     (assume_tac o GSYM) >> arw[])
 >-- (drule oa_dom_cod >>fs[] >>
     qpick_x_assum ‘i2(A, B) o b = i1(A, B) o a’
     (assume_tac o GSYM) >> rfs[]) 
 >-- (drule oa_dom_cod >> fs[] >> rfs[]) 
 >-- (drule oa_dom_cod >> fs[] >> rfs[]) 
 >-- (drule $ iffLR cpsb_def >>
     first_x_assum (qsspecl_then [‘f'’,‘b'’] assume_tac) >>
     first_x_assum drule >>
     pop_assum strip_assume_tac >>
     first_x_assum (qsspecl_then [‘a’,‘c0’] assume_tac) >>
     qsuff_tac
     ‘i1(A, B) o a = i2(A, B) o c0’ >-- arw[] >>
     pop_assum (K all_tac) >>
     qpick_x_assum ‘dom(g) = i1(A, B) o a’ 
     (assume_tac o GSYM) >> arw[]) >>
 arw[] >>
 drule fun_pres_oa >> arw[] >>
 irule fun_pres_oa >> irule o_cpsb >> arw[])
(form_goal
 “!A B f:2->A + B fa:1->A fb:1->B.
  (?f0:2->A. f = i1(A,B) o f0) |
  (?f0:2->B. f = i2(A,B) o f0)”));



val Thm16 = prove_store("Thm16",
e0
(cheat)
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








val exists_forall_dual = prove_store("exists_forall_dual",
e0
(strip_tac >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[]) >>
 ccontra_tac >>
 qby_tac ‘!f:A->B.~P(f)’ 
 >-- (strip_tac >> ccontra_tac >>
     qsuff_tac ‘?f:A->B. P(f)’ >-- arw[] >> 
     qexists_tac ‘f’ >> arw[]) >>
 fs[])
(form_goal “!A B. (?f:A->B.P(f)) <=>
 ~(!f:A->B.~P(f))”));


val forall_exists_dual = prove_store("forall_exists_dual",
e0
(strip_tac >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (ccontra_tac >> rfs[]) >>
 strip_tac >> ccontra_tac >>
 qsuff_tac ‘?f:A->B. ~P(f)’ >-- arw[] >> 
 qexists_tac ‘f’ >> arw[])
(form_goal “!A B. (!f:A->B.P(f)) <=>
 ~(?f:A->B.~P(f))”));


val fac_through_Mono = prove_store("fac_through_Mono",
e0
(rpt strip_tac >>
 qsuff_tac ‘?fb:X->S. f = i o fb’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘fb’ >> arw[] >>
      rpt strip_tac >> fs[Mono_def] >> first_x_assum irule >> arw[]) >>
 qsuff_tac
 ‘?(cf : fun(X, S)).
        !(a : fun(2, X))  (b : fun(2, S)). f o a = i o b <=> cf o a = b’ 
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     irule $ iffLR fun_ext >> arw[o_assoc]) >>
 match_mp_tac
 (CC5 |> qspecl [‘X’,‘S’] 
 |> fVar_sInst_th “R(x:2->X,s:2->S)”
    “f:X->A o x:2->X = i:S->A o s”) >>
 strip_tac (* 2 *) >--
 (strip_tac >> first_x_assum (qsspecl_then [‘f'’] strip_assume_tac) >>
 uex_tac >> qexists_tac ‘s’ >> arw[] >>
 fs[Mono_def] >> rpt strip_tac >> first_x_assum irule >> arw[]) >>
 strip_tac (* 2 *)
 >-- (rpt gen_tac >> disch_tac >> arw[id_def,dom_def,cod_def,GSYM o_assoc]) >>
 rpt strip_tac >>
 qby_tac ‘cpsb(g1,f1)’
 >-- (rw[cpsb_def] >> fs[Mono_def] >> first_x_assum irule >>
     pop_assum (assume_tac o GSYM) >> arw[dom_def,GSYM o_assoc] >>
     qpick_x_assum ‘f o f' = i o f1’ (assume_tac o GSYM) >> arw[] >>
     arw[cod_def,GSYM o_assoc] >> arw[o_assoc,GSYM dom_def,GSYM cod_def] >>
     fs[cpsb_def]) >>
 drule fun_pres_oa >>
 first_x_assum (qsspecl_then [‘i’] assume_tac) >>
 qby_tac ‘f o (g @ f') = i o (g1 @ f1)’
 >-- (rev_drule fun_pres_oa >>
     arw[]) >>
 fs[Mono_def] >> first_x_assum irule >> arw[])
(form_goal
 “!S A i:S->A. Mono(i) ==>
  !X f:X->A.(!x:2->X. ?s:2->S. f o x = i o s) ==>
  ?!fb:X->S. f = i o fb”));


val fac_through_Mono_ex = prove_store("fac_through_Mono_ex",
e0
(rpt strip_tac >>
 qsuff_tac ‘?!fb:X->S. f = i o fb’
 >-- (strip_tac >> pop_assum (strip_assume_tac o uex2ex_rule) >>
     qexists_tac ‘fb’ >> arw[]) >>
 irule fac_through_Mono >> arw[])
(form_goal
 “!S A i:S->A. Mono(i) ==>
  !X f:X->A.(!x:2->X. ?s:2->S. f o x = i o s) ==>
  ?fb:X->S. f = i o fb”));


val fac_through_FSC = prove_store("fac_through_FSC",
e0
(rpt strip_tac >> irule fac_through_Mono >> fs[FSC_def] >>
 strip_tac >> first_x_assum irule  >>
 arw[])
(form_goal
 “!S A i:S->A. FSC(i) ==>
  !X f:X->A.
  (!x:2->X. 
   (?s1:1->S. dom(f o x) = i o s1) & 
   (?s2:1->S. cod(f o x) = i o s2)) ==>
  ?!fb:X->S. f = i o fb”));


val fac_through_FSC_ex = prove_store("fac_through_FSC_ex",
e0
(rpt strip_tac >> 
 qsuff_tac ‘?!fb:X->S. f = i o fb’ 
 >-- (strip_tac >> pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘fb’ >> arw[]) >>
irule fac_through_FSC >> arw[])
(form_goal
 “!S A i:S->A. FSC(i) ==>
  !X f:X->A.
  (!x:2->X. 
   (?s1:1->S. dom(f o x) = i o s1) & 
   (?s2:1->S. cod(f o x) = i o s2)) ==>
  ?fb:X->S. f = i o fb”));





val cf_lemma =  CC5 |> qspecl [‘A’,‘Cl’] 
 |> fVar_sInst_th “R(f:2->A,g:2->Cl)”
    “((?(s1 : fun(1, S)). dom(f:2->A) = i o s1) & 
     (?(s2 : fun(1, S)). cod(f) = i o s2) & 
     (g:2->Cl = id(o1))) | 
     (~(?(s1 : fun(1, S)). dom(f) = i o s1) & 
      ~(?(s2 : fun(1, S)). cod(f) = i o s2) & 
     (g = id(o2))) |
     ((?(s1 : fun(1, S)). dom(f) = i o s1) & 
     ~(?(s2 : fun(1, S)). cod(f) = i o s2) & 
     (g = a1)) |
     (~(?(s1 : fun(1, S)). dom(f) = i o s1) & 
     (?(s2 : fun(1, S)). cod(f) = i o s2) & 
     (g = a2))”
  |> rewr_rule[id_dom,id_cod]

val indisc_2_FSCC = prove_store("indisc_2_FSCC",
e0
(rpt strip_tac >>
 rw[FSCC_def] >> rpt strip_tac >>
 qby_tac
 ‘(!fc:2->Cl. dom(fc) = o1 & cod(fc) = o2 ==> fc = a1)’ 
 >--
 (rpt strip_tac >> 
 first_x_assum (qsspecl_then [‘fc’] strip_assume_tac) (* 3 *)
 >> fs[id_dom,id_cod] >> rfs[]) >> 
 qby_tac
 ‘(!fc:2->Cl. dom(fc) = o2 & cod(fc) = o1 ==> fc = a2)’ >--
 (rpt strip_tac >> 
 last_x_assum (qsspecl_then [‘fc’] strip_assume_tac) >>
 fs[id_dom,id_cod]) >>
 qby_tac ‘~(a1 = id(o1))’ 
 >-- (ccontra_tac >>
     qby_tac ‘cod(a1) = cod(id(o1))’ 
     >-- (pop_assum (assume_tac o GSYM) >> arw[]) >> 
    fs[id_cod]) >> 
 qby_tac
 ‘(!fc:2->Cl. dom(fc) = o1 & cod(fc) = o1 ==> fc = id(o1))’
 >--
 (rpt strip_tac >> 
 last_x_assum (qsspecl_then [‘fc’] strip_assume_tac) >> 
 fs[id_dom,id_cod]) >> 
 qby_tac
 ‘(!fc:2->Cl. dom(fc) = o2 & cod(fc) = o2 ==> fc = id(o2))’
 >-- (rpt strip_tac >> 
 last_x_assum (qsspecl_then [‘fc’] strip_assume_tac) >> 
 fs[id_dom,id_cod] >> rfs[]) >> 
 qby_tac
 ‘!c. isPb(c, o1, i, To1(S)) ==>
  !f:2->A. 
  (!s1 s2. dom(f) = i o s1 & cod(f) = i o s2 ==>
   c o f = id(o1)) & 
  (!s1. dom(f) = i o s1 ==>
        (!s2. ~(cod(f) = i o s2)) ==>
   c o f = a1) & 
  (!s2. cod(f) = i o s2 ==>
        (!s1. ~(dom(f) = i o s1)) ==>
   c o f = a2) &
  (
  (!s1. ~(dom(f) = i o s1)) &
  (!s2. ~(cod(f) = i o s2)) ==> c o f = id(o2))’ 
 >-- (strip_tac >> disch_tac >>
     qby_tac ‘!a s. a = i o s ==>
              c o a = o1’ >--
     (rpt strip_tac >> fs[isPb_def] >>
     arw[GSYM o_assoc] >> rw[o_assoc,one_to_one_Id,IdR]) >> 
     qby_tac
     ‘!a:1->A. (?s. a = i o s) <=> c o a = o1’
     >-- (strip_tac >> dimp_tac >> strip_tac (* 2 *)
         >-- (first_x_assum drule >> arw[]) >>
         fs[isPb_def] >>
         first_x_assum 
         (qsspecl_then [‘a’,‘Id(1)’] assume_tac) >> 
         rfs[IdR] >>
         pop_assum (strip_assume_tac o uex2ex_rule) >>
         qexists_tac ‘a'’ >> arw[]) >> 
 rpt strip_tac (* 4 *)
 >-- (fs[isPb_def,FSC_def] >>
     first_x_assum 
     (qsspecl_then [‘f’,‘s1’,‘s2’] assume_tac) >> rfs[] >>
     fs[GSYM o_assoc] >>
     rw[o_assoc] >> rw[To1_def,id_def])
 >-- (first_x_assum irule >> arw[dom_o,cod_o] >>
     first_x_assum 
     (qsspecl_then [‘i o s1’,‘s1’] assume_tac) >> fs[] >>
     last_x_assum (qsspecl_then [‘c o cod(f)’] assume_tac)>>
     fs[] >>
     fs[isPb_def,cod_def] >> 
     first_x_assum (qsspecl_then [‘f o 1f’,‘Id(1)’] assume_tac) >> rfs[IdR] >>
     pop_assum (strip_assume_tac o uex2ex_rule) >>
     first_x_assum (qspecl_then [‘a’] assume_tac) >> rfs[]) 
 >-- (first_x_assum irule >>
     arw[dom_o,cod_o] >> first_x_assum drule >> rfs[] >>
     last_x_assum (qsspecl_then [‘c o dom(f)’] assume_tac)>>
     fs[] >>
     fs[isPb_def,dom_def] >> 
     first_x_assum (qsspecl_then [‘f o 0f’,‘Id(1)’] assume_tac) >> rfs[IdR] >>
     pop_assum (strip_assume_tac o uex2ex_rule) >>
     first_x_assum (qspecl_then [‘a’] assume_tac) >> rfs[])>>
 first_x_assum irule >> 
 qsuff_tac
 ‘~(dom(c o f) = o1) & ~(cod(c o f) = o1)’ 
 >-- (strip_tac >>
     last_assum
     (qsspecl_then [‘dom(c o f)’] assume_tac) >>
     last_x_assum
     (qsspecl_then [‘cod(c o f)’] assume_tac) >>
     rfs[]) >> strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[dom_def,o_assoc] >>
     first_x_assum (drule o iffRL) >>
     pop_assum strip_assume_tac >>
     rfs[]) >>
 ccontra_tac >> fs[cod_def,o_assoc] >>
 first_x_assum (drule o iffRL) >>
 pop_assum strip_assume_tac >>
 rfs[]) >>
 qsuff_tac ‘?c.isPb(c, o1, i, To1(S))’
 >-- (strip_tac >> uex_tac >>
     qexists_tac ‘c’ >> arw[] >>
     rpt strip_tac >>
     irule $ iffLR fun_ext >>
     strip_tac >> 
     qby_tac
     ‘(!s1:1->S. ~(dom(a) = i o s1)) <=> 
      ~(?s1:1->S. dom(a) = i o s1)’
     >-- accept_tac(forall_exists_dual |> qspecl [‘1’,‘S’] 
     |> fVar_sInst_th “P(s1:1->S)” “~(dom(a:2->A) = i o s1:1->S)” 
     |> rewr_rule[]) >>
     qby_tac
     ‘(!s2:1->S. ~(cod(a) = i o s2)) <=> 
     ~(?s2:1->S. cod(a) = i o s2)’
     >-- accept_tac(forall_exists_dual |> qspecl [‘1’,‘S’] 
     |> fVar_sInst_th “P(s2:1->S)” “~(cod(a:2->A) = i o s2:1->S)” 
     |> rewr_rule[]) >> 
     qcases ‘?s1.dom(a) = i o s1’ >>
     qcases ‘?s2.cod(a) = i o s2’ (* 4 *)
     >-- (first_assum drule >>
         first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
         first_x_assum rev_drule >>
         first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
         qsuff_tac ‘c' o a = id(o1) & c o a = id(o1)’
         >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
         >-- (first_x_assum irule >> arw[]) >>
         first_x_assum irule >> arw[]) 
     >-- (pop_assum mp_tac >> pop_assum strip_assume_tac >>
          rpt strip_tac >>
          first_assum drule >> 
          first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
          first_x_assum drule >>
          first_x_assum rev_drule >> 
          first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >> 
          first_x_assum drule >>
          qsuff_tac ‘c' o a = a1 & c o a = a1’
          >-- (strip_tac >> arw[]) >>
          strip_tac (* 2 *)
          >-- (first_x_assum irule >> arw[]) >>
          first_x_assum irule >> arw[])
     >-- (pop_assum strip_assume_tac >>
          first_assum drule >>  
          first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
          first_x_assum drule >>
          first_x_assum rev_drule >> 
          first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >> 
          first_x_assum drule >>
          qsuff_tac ‘c' o a = a2 & c o a = a2’
          >-- (strip_tac >> arw[]) >> 
          strip_tac (* 2 *)
          >-- (first_x_assum irule >> arw[]) >>
          first_x_assum irule >> arw[]) >>
     first_assum drule >>
     first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
     first_x_assum rev_drule >> 
     first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >> 
     qsuff_tac ‘c' o a = id(o2) & c o a = id(o2)’ 
     >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
     >-- (first_x_assum irule >> arw[]) >>
     first_x_assum irule >> arw[]) >> pop_assum (K all_tac) >>
qsuff_tac 
‘?c:A->Cl. 
 !f:2->A. (!(s1 : fun(1, S))  (s2 : fun(1, S)).
                     dom(f) = i o s1 & cod(f) = i o s2 ==>
                     c o f = id(o1)) &
                 (!(s1 : fun(1, S)).
                     dom(f) = i o s1 ==>
                     (!(s2 : fun(1, S)). ~(cod(f) = i o s2)) ==> c o f = a1) &
                 (!(s2 : fun(1, S)).
                     cod(f) = i o s2 ==>
                     (!(s1 : fun(1, S)). ~(dom(f) = i o s1)) ==> c o f = a2) &
                 ((!(s1 : fun(1, S)). ~(dom(f) = i o s1)) &
                   (!(s2 : fun(1, S)). ~(cod(f) = i o s2)) ==>
                   c o f = id(o2))’ >-- 
 (strip_tac >> qexists_tac ‘c’ >> rw[isPb_def] >>
 qby_tac ‘c o i = o1 o To1(S)’
 >-- (irule $ iffLR fun_ext >> rw[o_assoc] >>
     strip_tac >> rw[To1_def,GSYM id_def] >>
     first_x_assum (qspecl_then [‘i o a’] strip_assume_tac) >>
     first_x_assum irule >> rw[dom_def,cod_def,o_assoc] >>
     strip_tac (* 2 *)
     >-- (qexists_tac ‘a o 0f’ >> arw[]) >>
     qexists_tac ‘a o 1f’ >> arw[]) >> arw[] >>
 rpt strip_tac >>rw[To1_def] >> flip_tac >> 
 irule fac_through_FSC >> arw[] >> strip_tac >> 
 qby_tac ‘c o dom(u o x) = o1’
 >-- (arw[GSYM o_assoc,dom_o] >> rw[o_assoc] >> rw[one_to_one_Id,IdR]) >>
 qby_tac ‘c o cod(u o x) = o1’
 >-- (arw[GSYM o_assoc,cod_o] >> rw[o_assoc] >> rw[one_to_one_Id,IdR]) >>
 qby_tac
 ‘(!s1:1->S. ~(dom(u o x) = i o s1)) <=> 
  ~(?s1:1->S. dom(u o x) = i o s1)’
 >-- accept_tac(forall_exists_dual |> qspecl [‘1’,‘S’] 
     |> fVar_sInst_th “P(s1:1->S)” “~(dom(u:A'->A o x:2->A') = i o s1:1->S)” 
     |> rewr_rule[]) >>
 qby_tac
 ‘(!s2:1->S. ~(cod(u o x) = i o s2)) <=> 
  ~(?s2:1->S. cod(u o x) = i o s2)’
 >-- accept_tac(forall_exists_dual |> qspecl [‘1’,‘S’] 
     |> fVar_sInst_th “P(s2:1->S)” “~(cod(u:A'->A o x:2->A') = i o s2:1->S)” 
     |> rewr_rule[]) >> 
 qby_tac ‘c o u o x = id(o1)’ 
 >-- (first_x_assum irule >> 
      once_rw[dom_o] >> arw[] >> once_rw[cod_o] >> arw[]) >> 
 qcases ‘(?(s1 : fun(1, S)). dom(u o x) = i o s1)’ >>
 qcases ‘?(s2 : fun(1, S)). cod(u o x) = i o s2’ (* 4 *)
 >-- arw[] 
 >-- (qsuff_tac ‘F’ >-- arw[] >>
     qby_tac ‘c o u o x = a1’ 
     >-- (first_x_assum (qsspecl_then [‘u o x’] strip_assume_tac) >>
         first_x_assum irule >> arw[]) >>
     qby_tac ‘cod(a1) = cod(id(o1))’
     >-- (pop_assum (assume_tac o GSYM)>> 
         qpick_x_assum ‘cod(a1) = o2’ (K all_tac) >> arw[]) >>
     pop_assum mp_tac >> arw[id_cod] >> flip_tac >> arw[])
 >-- (qsuff_tac ‘F’ >-- arw[] >>
     qby_tac ‘c o u o x = a2’ 
     >-- (first_x_assum (qsspecl_then [‘u o x’] strip_assume_tac) >>
         first_x_assum irule >> arw[]) >>
     qby_tac ‘dom(a2) = dom(id(o1))’
     >-- (pop_assum (assume_tac o GSYM)>> 
         qpick_x_assum ‘dom(a2) = o2’ (K all_tac) >> arw[]) >>
     pop_assum mp_tac >> arw[id_dom] >> flip_tac >> arw[]) >>
 qsuff_tac ‘F’ >-- arw[] >>
 qby_tac ‘c o u o x = id(o2)’ 
 >-- (first_x_assum (qsspecl_then [‘u o x’] strip_assume_tac) >>
      first_x_assum irule >> arw[]) >>
 qby_tac ‘id(o1) = id(o2)’ 
 >-- (pop_assum (assume_tac o GSYM) >> arw[]) >>
 fs[id_eq_eq]) >>
 qby_tac
 ‘!f.(!s1:1->S. ~(dom(f) = i o s1)) <=> 
  ~(?s1:1->S. dom(f) = i o s1)’
 >-- (strip_tac >> 
     accept_tac(forall_exists_dual |> qspecl [‘1’,‘S’] 
     |> fVar_sInst_th “P(s1:1->S)” “~(dom(f:2->A) = i o s1:1->S)” 
     |> rewr_rule[])) >>
 qby_tac
 ‘!f.(!s2:1->S. ~(cod(f) = i o s2)) <=> 
  ~(?s2:1->S. cod(f) = i o s2)’
 >-- (strip_tac >>
     accept_tac(forall_exists_dual |> qspecl [‘1’,‘S’] 
     |> fVar_sInst_th “P(s2:1->S)” “~(cod(f:2->A) = i o s2:1->S)” 
     |> rewr_rule[])) >> 
 qsuff_tac
 ‘?(cf : fun(A, Cl)).
        !(a : fun(2, A))  (b : fun(2, Cl)).
          (?(s1 : fun(1, S)). dom(a) = i o s1) &
          (?(s2 : fun(1, S)). cod(a) = i o s2) & b = id(o1) |
          ~(?(s1 : fun(1, S)). dom(a) = i o s1) &
          ~(?(s2 : fun(1, S)). cod(a) = i o s2) & b = id(o2) |
          (?(s1 : fun(1, S)). dom(a) = i o s1) &
          ~(?(s2 : fun(1, S)). cod(a) = i o s2) & b = a1 |
          ~(?(s1 : fun(1, S)). dom(a) = i o s1) &
          (?(s2 : fun(1, S)). cod(a) = i o s2) & b = a2 <=> cf o a = b’ >--
 (strip_tac >> qexists_tac ‘cf’ >>
  strip_tac >> strip_tac (* 2 *)
  >-- (rpt strip_tac >> 
      first_x_assum $ irule o iffLR >>
      disj1_tac >> rw[] >> strip_tac (* 2 *)
      >-- (qexists_tac ‘s1’ >> arw[]) >>
      qexists_tac ‘s2’ >> arw[]) >> strip_tac (* 2 *)
  >-- (rpt strip_tac >> first_x_assum (irule o iffLR) >> 
      disj2_tac >> disj2_tac >> disj1_tac >> arw[] >>
      strip_tac (* 2 *)
      >-- (qexists_tac ‘s1’ >> arw[]) >> ccontra_tac >> fs[]) >> 
  strip_tac (* 2 *) 
  >-- (rpt strip_tac >> first_x_assum (irule o iffLR) >>
      rpt disj2_tac >> arw[] >> strip_tac (* 2 *)
      >-- (ccontra_tac >> fs[]) >>
      qexists_tac ‘s2’ >> arw[]) >>
  rpt strip_tac >> first_x_assum (irule o iffLR) >>
  disj2_tac >> disj1_tac >> arw[] >> rpt strip_tac >> fs[] >>
  ccontra_tac >> fs[]) >> 
 match_mp_tac cf_lemma >> strip_tac (* 2 *) >-- 
 (strip_tac >> 
 qcases ‘(?(s1 : fun(1, S)). dom(f) = i o s1)’ >>
 qcases ‘?(s2 : fun(1, S)). cod(f) = i o s2’ >> arw[] (* 4 *)
 >-- (uex_tac >> qexists_tac ‘id(o1)’ >> arw[])
 >-- (uex_tac >> qexists_tac ‘a1’ >> arw[])
 >-- (uex_tac >> qexists_tac ‘a2’ >> arw[]) >>
 uex_tac >> qexists_tac ‘id(o2)’ >> arw[]) >> strip_tac (* 2 *) >--
 (rpt gen_tac >> strip_tac (* 4 *)
 >-- (arw[] >>
     once_rw[id_dom] >> once_rw[id_cod] >> 
     strip_tac (* 2 *)
     >-- (disj1_tac >> strip_tac (* 2 *)
         >-- (qexists_tac ‘s1’ >> rw[]) >> rw[] >>
         qexists_tac ‘s1’ >> rw[]) >>
     disj1_tac >> rw[] >> strip_tac (* 2 *)
     >-- (qexists_tac ‘s2’ >> rw[]) >>
     qexists_tac ‘s2’ >> rw[]) 
 >-- (arw[] >> rw[id_dom,id_cod]) 
 >-- (arw[] >> disj1_tac >> strip_tac (* 2 *)
     >-- (qexists_tac ‘s1’ >> rw[]) >>
     qexists_tac ‘s1’ >> rw[]) >> 
 arw[] >> disj1_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘s2’ >> rw[]) >>
 qexists_tac ‘s2’ >> rw[]) >> rpt gen_tac >> strip_tac >>
 strip_tac (* 4 *)
 >-- (arw[] >> drule oa_dom_cod >>
     fs[] >> rpt strip_tac (* 16 *)
     >-- (arw[] >> flip_tac >> irule cpsb_idR >> 
         rw[cpsb_def,id_dom,id_cod]) 
     >-- (* lame simplifier, .~?(s2' : fun(1, S)). i o s2 = i o s2'# in assum *)
         (qsuff_tac ‘?(s2' : fun(1, S)). i o s2 = i o s2'’ >-- arw[] >>
         qexists_tac ‘s2’ >> rw[]) 
     >-- (qsuff_tac ‘?(s2' : fun(1, S)). i o s2 = i o s2'’ >-- arw[] >>
         qexists_tac ‘s2’ >> rw[]) 
     >-- (qsuff_tac ‘?(s1 : fun(1, S)). dom(g) = i o s1’ 
         >-- arw[] >> 
         qpick_x_assum ‘~(?(s1 : fun(1, S)). dom(g) = i o s1)’ (K all_tac)>>
         fs[cpsb_def] >> qexists_tac ‘s2'’ >> rw[]) 
     >-- (qsuff_tac ‘?(s2 : fun(1, S)). cod(f) = i o s2’ >-- arw[] >>
         qpick_x_assum ‘~(?(s2 : fun(1, S)). cod(f) = i o s2)’ (K all_tac)>>
         fs[cpsb_def] >> qexists_tac ‘s1'’ >> arw[]) 
     >-- (qsuff_tac ‘?(s2' : fun(1, S)). i o s2 = i o s2'’ >-- arw[] >>
         qexists_tac ‘s2’ >> rw[])
     >-- (qsuff_tac ‘?(s1' : fun(1, S)). i o s1 = i o s1'’ >-- arw[] >>
         qexists_tac ‘s1’ >> rw[])      
     >-- (qsuff_tac ‘?(s1' : fun(1, S)). i o s1 = i o s1'’ >-- arw[] >>
         qexists_tac ‘s1’ >> rw[]) 
     >-- (qsuff_tac ‘?(s2 : fun(1, S)). cod(f) = i o s2’ >-- arw[] >>
         qpick_x_assum ‘~(?(s2 : fun(1, S)). cod(f) = i o s2)’ (K all_tac) >>
         rfs[cpsb_def] >> qexists_tac ‘s1''’ >> rw[])
     >-- (qsuff_tac ‘?(s2' : fun(1, S)). i o s2 = i o s2'’ >-- arw[] >>
         qexists_tac ‘s2’ >> rw[]) 
     >-- (qsuff_tac ‘?(s2' : fun(1, S)). i o s2 = i o s2'’ >-- arw[] >>
         qexists_tac ‘s2’ >> rw[]) 
     >-- arw[] 
     >-- (qsuff_tac ‘?(s1' : fun(1, S)). i o s1 = i o s1'’ >-- arw[] >>
         qexists_tac ‘s1’ >> rw[]) 
     >-- (qsuff_tac ‘?(s2' : fun(1, S)). i o s2 = i o s2'’ >-- arw[] >>
         qexists_tac ‘s2’ >> rw[])
     >-- (qsuff_tac ‘?(s2' : fun(1, S)). i o s2 = i o s2'’ >-- arw[] >>
         qexists_tac ‘s2’ >> rw[])
     >-- (qsuff_tac ‘?(s1' : fun(1, S)). i o s1 = i o s1'’ >-- arw[] >>
         qexists_tac ‘s1’ >> rw[]))
>-- (arw[] >> drule oa_dom_cod >>
    fs[] >> rpt strip_tac (* 4 *)
    >-- (arw[] >> flip_tac >> irule cpsb_idL >> rw[cpsb_def,id_dom,id_cod])
    >-- (qsuff_tac ‘?(s2 : fun(1, S)). cod(f) = i o s2’ >-- arw[] >>
        qexists_tac ‘s1’ >> fs[cpsb_def])
    >-- (qsuff_tac ‘?(s1 : fun(1, S)). dom(g) = i o s1’ >-- arw[] >>
        qexists_tac ‘s2’ >> fs[cpsb_def]) >>
    arw[]) 
>-- (arw[] >> drule oa_dom_cod >>
    fs[] >>
    qby_tac ‘!s:1->S. ?s0. i o s = i o s0’
    >-- (strip_tac >> qexists_tac ‘s’ >> rw[]) >> arw[] >>
    rpt strip_tac (* 4 *)
    >-- (qsuff_tac ‘?(s1 : fun(1, S)). dom(g) = i o s1’ >-- arw[] >>
        qexists_tac ‘s2’ >> fs[cpsb_def])
    >-- (arw[] >> flip_tac >> irule cpsb_idR >> arw[cpsb_def,id_cod]) 
    >-- (arw[] >> flip_tac >> irule cpsb_idL >> arw[cpsb_def,id_dom]) >>
    qsuff_tac ‘?(s2 : fun(1, S)). cod(f) = i o s2’ >-- arw[] >>
    qexists_tac ‘s1'’ >> fs[cpsb_def]) >>
arw[] >> drule oa_dom_cod >> fs[] >> 
qby_tac ‘!s:1->S. ?s0. i o s = i o s0’
>-- (strip_tac >> qexists_tac ‘s’ >> rw[]) >> arw[] >>
rpt strip_tac (* 4 *)
>-- (qsuff_tac ‘?(s2 : fun(1, S)). cod(f) = i o s2’ >-- arw[] >>
    qexists_tac ‘s1’ >> fs[cpsb_def])
>-- (arw[] >> flip_tac >> irule cpsb_idR >> arw[cpsb_def,id_cod]) 
>-- (arw[] >> flip_tac >> irule cpsb_idL >> arw[cpsb_def,id_dom]) >>
qsuff_tac ‘?(s1 : fun(1, S)). dom(g) = i o s1’ 
>-- arw[] >>
qexists_tac ‘s2'’ >> fs[cpsb_def])
(form_goal
 “!Cl o1:1->Cl o2:1->Cl a1:2->Cl a2:2->Cl. 
 dom(a1) = o1 ∧ cod(a1) = o2 ∧ 
 dom(a2) = o2 ∧ cod(a2) = o1 ∧ 
 a1 @ a2 = id(o2) ∧ a2 @ a1 = id(o1) ∧
 ~(o1 = o2) &
 (!oc:1->Cl. oc = o1 | oc = o2) & 
 (∀a:2-> Cl. a = id(o1) | a = id(o2) | a = a1 | a = a2) ==>
 FSCC(o1)”));

val jointEpi2_def = qdefine_psym("jointEpi2",[‘f:A->X’,‘g:B->X’])
‘∀Y y1:X->Y y2. y1 o f = y2 o f & y1 o g = y2 o g ⇒ y1 = y2’



val l = fVar_sInst_th
“R(b:2->B,c:2->C)”
“(dom(b:2->B) = B0 ∧ ~(cod(b) = B0) ∧ c:2->C = h) |
 (~(dom(b) = B0) ∧ cod(b) = B0 ∧ c = k) |
 (dom(b) = B0 ∧ cod(b) = B0 ∧ c = h o 𝟘) |
 (~(dom(b) = B0) ∧ ~(cod(b) = B0) ∧ c = h o 𝟙)”
(CC5 |> qspecl [‘B’,‘C’])

val jointEpi2_onto = prove_store("jointEpi2_onto",
e0
(rpt strip_tac >>
 x_choosel_then ["C","T1","T2","h"] strip_assume_tac Thm14' >>
 drule $ iffLR iso_def >>
 pop_assum (x_choose_then "k" strip_assume_tac) >>
 ccontra_tac >> fs[jointEpi2_def] >> 
 qby_tac
 ‘∀a1:1->A1. ~(B0 = f o a1)’
 >-- cheat >> 
 qby_tac
 ‘∀a2:1->A2. ~(B0 = g o a2)’ >-- cheat >>
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
         arw[]) >>
     qby_tac ‘H o g = (h o 1f o To1(B)) o g’ 
     >-- (irule $ iffLR fun_ext >> strip_tac >> rw[o_assoc] >>
         qsuff_tac ‘H o g o a = h o 𝟙’
         >-- (strip_tac >> arw[To1_def,one_def]) >>
         first_x_assum (qsspecl_then [‘g o a’] strip_assume_tac) >>
         first_x_assum irule >>
         rw[dom_def,cod_def,o_assoc] >> dflip_tac >> 
         arw[]) >> 
     fs[] >> 
     qby_tac ‘H o id(B0) = h o 1f o To1(B) o id(B0)’
     >-- arw[o_assoc] >>
     qby_tac ‘H o id(B0) = h o 𝟘’
     >-- (first_x_assum (qsspecl_then [‘id(B0)’] strip_assume_tac) >> rfs[o_assoc] >>
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
 qby_tac ‘cod(g' @ f') = cod(g') ∧ dom(g' @ f') = dom(f')’
 >-- (fs[GSYM cpsb_def] >>
     drule oa_dom_cod >> arw[]) >>
 qby_tac ‘(h o 𝟙) @ h = h ∧ h @ (h o 𝟘) = h ∧ 
          k @ h = h o 𝟘 ∧ h @ k = h o 𝟙 ∧
          (h o 𝟘) @ k = k ∧ k @ (h o 𝟙) = k ∧ 
          (h o 𝟘) @ h o 𝟘 = (h o 𝟘) ∧
          (h o 𝟙) @ h o 𝟙 = (h o 𝟙)’
 >-- (rw[one_def,zero_def] >>
     rw[GSYM o_assoc] >> rw[GSYM dom_def,GSYM cod_def] >>
     rw[GSYM id_def] >> arw[] >>
     rw[GSYM id_def] >> rpt strip_tac (* 6 *)
     >-- (irule cpsb_idL >> arw[id_dom,cpsb_def]) 
     >-- (irule cpsb_idR >> arw[id_cod,cpsb_def]) 
     >-- (irule cpsb_idL >> arw[id_dom,cpsb_def]) 
     >-- (irule cpsb_idR >> arw[id_cod,cpsb_def]) 
     >-- (irule cpsb_idR >> rw[id_dom,id_cod,cpsb_def]) >>
     irule cpsb_idR >> rw[id_dom,id_cod,cpsb_def]) >>
     once_arw[] >>  strip_tac (* 4 *)
     >-- (once_arw[]  >> rw[] >> rpt strip_tac >> arw[]) 
     >-- (once_arw[]  >> rw[] >> rpt strip_tac >> arw[]) 
     >-- (once_arw[]  >> rw[] >> rpt strip_tac >> arw[]) >>
     once_arw[]  >> rw[] >> rpt strip_tac >> arw[])
(form_goal 
 “!A1 A2 B f:A1->B g:A2->B. jointEpi2(f,g) ==> 
  !B0:1->B. (?a1:1->A1. B0 = f o a1) | 
            (?a2:1->A2. B0 = g o a2)”));


val uex_unique = prove_store("uex_unique",
e0
(rpt strip_tac >>
 last_x_assum (strip_assume_tac o uex_expand) >>
 qsuff_tac ‘f1 = f & f2 = f’ >-- (strip_tac >> arw[]) >>
 strip_tac >>
 first_x_assum irule >> arw[])
(form_goal
 “∀A B. (?!f:A->B. P(f)) ⇒
  ∀f1:A->B f2:A->B. P(f1) & P(f2) ⇒ f1 = f2”));

val isPo_jointEpi2 = prove_store("isPo_jointEpi2",
e0
(rpt strip_tac >> rw[jointEpi2_def] >> rpt strip_tac >>
 fs[isPo_def] >>
 first_x_assum (qsspecl_then [‘y2 o p’,‘y2 o q’] assume_tac) >> rfs[o_assoc] >>
 drule
 (uex_unique |> qspecl [‘P’,‘Y'’]
 |> fVar_sInst_th “P(a:P->Y')” 
    “a:P->Y' o p:X->P = y2 o p & a o q:Y->P = y2 o q”) >>
 first_x_assum irule >> arw[])
(form_goal
 “∀H X f:H->X Y g:H ->Y P p:X->P q:Y->P.
  isPo(f,g,p,q) ⇒ jointEpi2(p,q)”));

val jointEpi2_o_Epi = prove_store("jointEpi2_o_Epi",
e0
(rpt strip_tac >> fs[jointEpi2_def] >>
 rpt strip_tac >>
 fs[Epi_def] >> first_x_assum irule >>
 first_x_assum irule >> arw[o_assoc])
(form_goal “∀A B X f:A->X g:B->X. jointEpi2(f,g) ⇒
 ∀K k:X->K. Epi(k) ⇒ jointEpi2(k o f, k o g)”));
 
val iscoEq_Epi = prove_store("iscoEq_Epi",
e0
(cheat)
(form_goal
 “!A B f:A->B g:A->B Q q:B-> Q. 
  iscoEq(f,g,q) ==> Epi(q)”));

val one_to_two = prove_store("one_to_two",
e0
cheat
(form_goal “∀f:1->2. f = 0f | f = 1f”));

(*maybe have lemma with assumption P(dom(c)), P(cod(c))*)
local
val l = 
 CC5 |> qspecl [‘C’,‘C’]
 |> fVar_sInst_th “R(fc1:2->C,fc2:2->C)”
    “(dom(fc1) = c1 & cod(fc1) = c2 & fc2 = f1:2->C) |
     (dom(fc1) = c2 & cod(fc1) = c1 & fc2 = f2:2->C) |
     (dom(fc1) = c1 & cod(fc1) = c1 & fc2 = id(c1)) |
     (dom(fc1) = c2 & cod(fc1) = c2 & fc2 = id(c2))”
 |> rewr_rule[id_dom,id_cod]
in
val Cl_has_func_to_itself = prove_store("Cl_has_func_to_itself",
e0
(rpt strip_tac >> 
 qby_tac ‘~(c2 = c1)’ >-- (ccontra_tac >> fs[]) >>
 qsuff_tac
 ‘?(cf : fun(C, C)).
        !(a : fun(2, C))  (b : fun(2, C)).
          (dom(a) = c1 & cod(a) = c2 & b = f1) |
          (dom(a) = c2 & cod(a) = c1 & b = f2) |
          (dom(a) = c1 & cod(a) = c1 & b = id(c1)) |
          (dom(a) = c2 & cod(a) = c2 & b = id(c2)) <=> cf o a = b’ >--
 (strip_tac >> qexists_tac ‘cf’ >>
  pop_assum (assume_tac o GSYM) >> once_arw[] >>
  once_rw[id_eq_eq]  >> once_arw[] >> rw[] >>
  rpt strip_tac (* 4 *) >> arw[]) >>
 match_mp_tac l >> strip_tac (* 2 *)
 >-- (strip_tac >> 
     qby_tac ‘∀c:1->C. ~(c = c1) ⇔ (c = c2)’ 
     >-- (strip_tac >> qcases ‘c = c1’ >> arw[] >>
         first_x_assum (qsspecl_then [‘c’] strip_assume_tac)) >>
     qcases ‘dom(f) = c1’ >>
     qcases ‘cod(f) = c1’ (* 4 *)
     >-- (arw[] >> uex_tac >> qexists_tac ‘id(c1)’ >> rw[]) 
     >-- (rfs[] >> uex_tac >> qexists_tac ‘f1’ >> rw[]) 
     >-- (rfs[] >> uex_tac>> qexists_tac ‘f2’ >> rw[]) >>
     rfs[] >> uex_tac >> qexists_tac ‘id(c2)’ >> rw[]) >>
 strip_tac (* 2 *)
 >-- (qby_tac ‘∀c:1->C. ~(c = c1) ⇔ (c = c2)’ 
     >-- (strip_tac >> qcases ‘c = c1’ >> arw[] >>
         first_x_assum (qsspecl_then [‘c’] strip_assume_tac)) >>
     once_rw[id_eq_eq] >> rpt gen_tac >> strip_tac (* 4 *)
     >-- arw[] >-- arw[] >-- arw[id_dom,id_cod] >> arw[id_dom,id_cod]) >>
 rpt gen_tac >> strip_tac >>
 drule oa_dom_cod >> arw[] >> strip_tac (* 4 *)
 >-- (arw[] >> rpt strip_tac >> rpt gen_tac >> rpt strip_tac (* 4 *)
     >-- (arw[] >> fs[cpsb_def]) 
     >-- (arw[] >> flip_tac >> irule cpsb_idL >> arw[cpsb_def,id_dom]) 
     >-- (arw[] >> flip_tac >> irule cpsb_idR >> arw[cpsb_def,id_cod]) >>
     fs[cpsb_def]) 
 >-- (arw[] >> rpt strip_tac (* 4 *)
     >-- (arw[] >> fs[cpsb_def]) 
     >-- (arw[] >> flip_tac >> irule cpsb_idL >> arw[cpsb_def,id_dom])
     >-- (arw[] >> flip_tac >> irule cpsb_idR >> arw[cpsb_def,id_cod]) >>
     fs[cpsb_def]) 
 >-- (arw[] >> rpt strip_tac (* 4 *)
     >-- arw[]
     >-- (arw[] >> fs[cpsb_def]) 
     >-- (arw[] >> fs[cpsb_def]) >>
     arw[] >> flip_tac >> irule cpsb_idR >> rw[id_dom,id_cod,cpsb_def]) >>
 arw[] >> rpt strip_tac (* 4 *)
 >-- arw[] 
 >-- fs[cpsb_def] 
 >-- fs[cpsb_def] >>
 arw[] >> flip_tac >> irule cpsb_idR >> rw[id_dom,id_cod,cpsb_def])
(form_goal
 “∀C c1 c2 f1:2->C f2:2->C. 
  (∀oc:1->C. oc = c1 | oc = c2) &
  dom(f1) = c1 & cod(f1) = c2 & 
  dom(f2) = c2 & cod(f2) = c1 &
  ~(c1 = c2) &
  (f2 @ f1 = id(c1) & f1 @ f2 = id(c2)) ⇒
 ∃f:C -> C.
  ∀c:2->C. 
  (dom(c) = c1 & cod(c) = c2 ⇒ f o c = f1) &
  (dom(c) = c2 & cod(c) = c1 ⇒ f o c = f2) &
  (dom(c) = c1 & cod(c) = c1 ⇒ f o c = id(c1)) &
  (dom(c) = c2 & cod(c) = c2 ⇒ f o c = id(c2))”));
end

val Cl_ex = prove_store("Cl_ex",
e0
(x_choosel_then ["C","T1","T2","h"] strip_assume_tac Thm14' >>
 drule $ iffLR iso_def >>
 pop_assum (x_choose_then "k" strip_assume_tac) >>
 qsspecl_then [‘coPa(1f,0f)’,‘coPa(0f,1f)’] assume_tac isPo_ex >>
 pop_assum (x_choosel_then ["P","m","n"] assume_tac) >>
 qby_tac ‘cpsb(m,n)’
 >-- (rw[cpsb_def] >> fs[isPo_def] >>
     qby_tac ‘m o coPa(1f, 0f) o i2(1,1) = n o coPa(0f, 1f) o i2(1,1)’
     >-- arw[GSYM o_assoc] >>
     fs[i12_of_coPa,dom_def,cod_def]) >> 
 qby_tac ‘cpsb(n,m)’
 >-- (rw[cpsb_def] >> fs[isPo_def] >>
     qby_tac ‘m o coPa(1f, 0f) o i1(1,1) = n o coPa(0f, 1f) o i1(1,1)’
     >-- arw[GSYM o_assoc] >>
     fs[i12_of_coPa,dom_def,cod_def]) >>
 qby_tac ‘h o coPa(1f, 0f) = k o coPa(0f, 1f)’
 >-- (irule from_coP_eq >> 
      arw[o_assoc,i12_of_coPa,GSYM dom_def,GSYM cod_def]) >>
 qby_tac ‘∃hk:P->C. hk o m = h & hk o n = k’ 
 >-- (fs[isPo_def] >> first_x_assum drule >>
     pop_assum (assume_tac o uex2ex_rule) >>
     pop_assum (x_choose_then "hk" assume_tac) >> 
     qexists_tac ‘hk’ >> arw[]) >>
 pop_assum strip_assume_tac >> 
 qby_tac ‘hk o m o 0f = h o 0f & hk o m o 1f = h o 1f’
 >-- (arw[GSYM o_assoc]) >>
 qby_tac ‘~(m o 0f  = m o 1f)’ 
 >-- (ccontra_tac >> fs[GSYM dom_def,GSYM cod_def] >>
      qby_tac ‘dom(h) = cod(h)’ 
      >-- (qpick_x_assum ‘hk o cod(m) = cod(h)’ (assume_tac o GSYM) >>
          arw[]) >> pop_assum mp_tac >> arw[]) >>
 qby_tac ‘hk o (n @ m) = hk o m o 𝟘’ 
 >-- (drule fun_pres_oa >> arw[] >> arw[GSYM o_assoc] >>
     arw[zero_def,GSYM dom_def] >> rw[GSYM o_assoc,GSYM id_def,id_eq_eq] >>
     rw[GSYM dom_def] >> arw[]) >> 
 qsspecl_then [‘n @ m’,‘m o 𝟘’] assume_tac iscoEq_ex >>
 pop_assum (x_choosel_then ["Cl0","q0"] assume_tac) >> 
 qby_tac ‘∃hk0:Cl0 -> C. hk0 o q0 = hk’
 >-- (fs[iscoEq_def] >> 
     first_x_assum rev_drule >> 
     pop_assum (strip_assume_tac o uex2ex_rule) >> 
     qexists_tac ‘x0’ >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘cpsb(q0 o m,q0 o n)’ 
 >-- (irule o_cpsb >> arw[]) >>
 qby_tac ‘hk0 o ((q0 o m) @ (q0 o n)) = hk0 o q0 o (n o 𝟘)’ 
 >-- (drule fun_pres_oa >> arw[] >> arw[GSYM o_assoc] >>
     rw[zero_def,GSYM o_assoc]>> rw[GSYM id_def,id_eq_eq] >>
     rw[GSYM dom_def] >> arw[]) >> 
 qsspecl_then [‘q0 o (m @ n)’,‘q0 o (n o 𝟘)’] assume_tac iscoEq_ex >>
 pop_assum (x_choosel_then ["Cl","q"] assume_tac) >>
 (*qsspecl_then [‘m’,‘n’] assume_tac fun_pres_oa >>
 first_x_assum drule >> fs[] *)
 qby_tac ‘∃hk1:Cl -> C. hk1 o q = hk0’ 
 >-- (fs[iscoEq_def] >>
     qsspecl_then [‘n’,‘m’] assume_tac fun_pres_oa >>
     first_x_assum drule >> fs[] >>
     first_x_assum rev_drule >>
     pop_assum (strip_assume_tac o uex2ex_rule) >>
     qexists_tac ‘x0’ >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘hk1 o q o q0 o m o 0f = h o 0f & 
          hk1 o q o q0 o m o 1f = h o 1f’
 >-- arw[GSYM o_assoc] >>
 pop_assum strip_assume_tac >>
 qby_tac ‘~(q o q0 o m o 0f = q o q0 o m o 1f)’ 
 >-- (ccontra_tac >> fs[GSYM dom_def,GSYM cod_def]) >>
 qby_tac ‘jointEpi2(m,n)’
 >-- (irule isPo_jointEpi2>> 
     qexistsl_tac [‘1+1’,‘coPa(1f, 0f)’,‘coPa(0f, 1f)’] >> arw[]) >>
 qby_tac ‘jointEpi2(q o q0 o m,q o q0 o n)’ 
 >-- (irule jointEpi2_o_Epi >> strip_tac (* 2 *)
     >-- (irule jointEpi2_o_Epi >> arw[] >>
         rev_drule iscoEq_Epi >> arw[]) >>
     drule iscoEq_Epi >> arw[]) >>
 drule jointEpi2_onto >>
 fs[o_assoc] >> 
 qby_tac ‘∀oc:1->Cl. oc = q o q0 o m o 0f | oc = q o q0 o m o 1f’ 
 >-- (strip_tac >>
     first_x_assum $ qsspecl_then [‘oc’] strip_assume_tac (* 2 *)
     >-- (arw[] >> 
         qsspecl_then [‘a’] strip_assume_tac one_to_two 
         >-- arw[] >>
         arw[]) >> 
     arw[] >>
     qsspecl_then [‘b’] strip_assume_tac one_to_two
     >-- (arw[] >> rw[GSYM dom_def,GSYM cod_def] >> fs[cpsb_def]) >>
     arw[] >> rw[GSYM dom_def,GSYM cod_def] >> fs[cpsb_def]) >>
 qby_tac
 ‘(q o q0 o m) @ (q o q0 o n) = id(q o q0 o n o 0f)’ 
 >-- (fs[iscoEq_def] >> rev_drule fun_pres_oa >>
     fs[] >> drule fun_pres_oa >> fs[] >>
     rw[id_def,zero_def,o_assoc]) >>
 qby_tac ‘n o 0f = m o 1f’ 
 >-- (drule $ iffLR isPo_def >>
     fs[] >>
     qby_tac ‘m o coPa(1f, 0f) o i1(1,1) = n o coPa(0f, 1f) o i1(1,1)’ 
     >-- arw[GSYM o_assoc] >>
     fs[i12_of_coPa]) >> fs[] >>
 qby_tac ‘n o 1f = m o 0f’ 
 >-- (drule $ iffLR isPo_def >>
     fs[] >>
     qby_tac ‘m o coPa(1f, 0f) o i2(1,1) = n o coPa(0f, 1f) o i2(1,1)’ 
     >-- arw[GSYM o_assoc] >>
     fs[i12_of_coPa]) >> fs[] >>
 qby_tac ‘cpsb(q0 o n,q0 o m)’ 
 >-- (irule o_cpsb >> arw[]) >>
 qby_tac
 ‘(q o q0 o n) @ (q o q0 o m) = id(q o q0 o m o 0f)’ 
 >-- (fs[iscoEq_def] >>
      qpick_x_assum ‘cpsb(m,n)’ (K all_tac) >> rev_drule fun_pres_oa >>
      fs[] >> drule $ GSYM fun_pres_oa >> fs[] >>
      rw[id_def,zero_def,o_assoc]) >>
 qabbrev_tac ‘q o q0 o m o 0f = c1’ >>
 qabbrev_tac ‘q o q0 o m o 1f = c2’ >>
 qby_tac
‘∃f:Cl -> Cl.
  ∀c:2->Cl. 
  (dom(c) = c1 & cod(c) = c2 ⇒ f o c = q o q0 o m) &
  (dom(c) = c2 & cod(c) = c1 ⇒ f o c = q o q0 o n) &
  (dom(c) = c1 & cod(c) = c1 ⇒ f o c = id(c1)) &
  (dom(c) = c2 & cod(c) = c2 ⇒ f o c = id(c2))’ 
 >-- (irule Cl_has_func_to_itself >>
     fs[] >>  arw[dom_def,cod_def,o_assoc]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘f = Id(Cl)’ 
 >-- (qby_tac ‘f o q o q0 o m = q o q0 o m’ 
     >-- (first_x_assum (qsspecl_then [‘q o q0 o m’] strip_assume_tac) >>
         first_x_assum irule >> arw[o_assoc,dom_def,cod_def]) >>
     qby_tac ‘f o q o q0 o n = q o q0 o n’ 
     >-- (first_x_assum (qsspecl_then [‘q o q0 o n’] strip_assume_tac) >>
         first_x_assum irule >> arw[o_assoc,dom_def,cod_def]) >>
     drule isPo_jointEpi2 >>
     drule $ iffLR jointEpi2_def >> 
     qby_tac ‘f o q o q0 = q o q0’ 
     >-- (first_x_assum irule >> arw[o_assoc]) >>
     rev_drule $ iscoEq_Epi >> drule $ iscoEq_Epi >>
     fs[Epi_def] >>
     first_x_assum irule >> first_x_assum irule >> arw[o_assoc,IdL]) >>
 fs[IdL] >> 
 qexistsl_tac [‘Cl’,‘q o q0 o m o 0f’,‘q o q0 o m o 1f’,
               ‘q o q0 o m’,‘q o q0 o n’] >>
 arw[dom_def,o_assoc,cod_def] >>
 rpt strip_tac >>
 qby_tac ‘∀c. ~(c = c1) ⇔ c = c2’ 
 >-- (strip_tac >> qcases ‘c = c1’ >> arw[] >>
     first_x_assum (qsspecl_then [‘c’] strip_assume_tac)) >>
 qcases ‘dom(a) = c1’ >> qcases ‘cod(a) = c1’ (* 4 *)
 >-- (disj1_tac >>
     first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
     first_x_assum irule >> arw[]) 
 >-- (rfs[] >>
     disj2_tac >> disj2_tac >> disj1_tac >>
     first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
     first_x_assum irule >> arw[]) 
 >-- (rfs[] >> rpt disj2_tac >>
     first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
     first_x_assum irule >> arw[]) >>
 rfs[] >> disj2_tac >> disj1_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 first_x_assum irule >> arw[]) 
(form_goal
 “?Cl o1:1->Cl o2:1->Cl a1:2->Cl a2:2->Cl. 
 dom(a1) = o1 ∧ cod(a1) = o2 ∧ 
 dom(a2) = o2 ∧ cod(a2) = o1 ∧ 
 a1 @ a2 = id(o2) ∧ a2 @ a1 = id(o1) ∧
 ~(o1 = o2) &
 (!oc:1->Cl. oc = o1 | oc = o2) & 
 !(a : fun(2, Cl)). a = id(o1) | a = id(o2) | a = a1 | a = a2”));

val Thm17 = prove_store("Thm17",
e0
(strip_assume_tac Cl_ex >> 
 qexistsl_tac [‘Cl’,‘o1’] >>
 irule indisc_2_FSCC >> qexistsl_tac [‘a1’,‘a2’,‘o2’] >>
 arw[])
(form_goal “?Cl t:1->Cl. FSCC(t)”));

(*
val Thm17 = prove_store("Thm17",
e0
(qby_tac ‘∃Cl o1:1->Cl o2:1->Cl a1:2->Cl a2:2->Cl. 
 dom(a1) = o1 ∧ cod(a1) = o2 ∧ dom(a2) = o2 ∧ cod(a2) = o1 ∧ 
 a1 @ a2 = id(o2) ∧ a2 @ a1 = id(o1) ∧
 (∀a:2-> Cl. a = id(o1) | a = id(o2) | a = a1 | a = a2)’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘Cl’,‘o1’] >> rw[FSCC_def] >>
 rpt strip_tac >> 
 fs[FSC_def] >> 
 qby_tac
 ‘∀c:A -> Cl. isPb(c,o1,i,To1(S)) ⇒ 
  (∀f:2->A. (FT(i,dom(f)) ∧ FT(i,cod(f)) ⇒ c o f = id(o1)) ∧ 
            (FT(i,dom(f)) ∧ ~FT(i,cod(f)) ⇒ c o f = a1) ∧ 
            (~FT(i,dom(f)) ∧ FT(i,cod(f)) ⇒ c o f = a2))’
 >-- 
 )
(form_goal “?Cl t:1->Cl. FSCC(t)”));
*)
