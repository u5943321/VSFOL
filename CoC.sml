

val _ = new_sort "cat" [];

val _ = new_sort "fun" [("A",mk_sort "cat" []),("B",mk_sort "cat" [])]

val _ = new_sort_infix "fun" "->"

val cat_sort = mk_sort "cat" []
fun fun_sort A B = mk_sort "fun" [A,B]
fun mk_cat A = mk_var(A,cat_sort)
fun mk_fun F A B = mk_var(F,fun_sort A B)

val _ = EqSorts := "fun" :: (!EqSorts)

 

val _ = new_sort "nt" [("f",fun_sort (mk_cat "A") (mk_cat "B")),
                       ("g",fun_sort (mk_cat "A") (mk_cat "B"))]


val _ = new_fun "o" (mk_sort "fun" [mk_var("A",mk_sort "cat" []),mk_var("C",mk_sort "cat" [])],[("f",mk_sort "fun" [mk_var("B",mk_sort "cat" []),mk_var("C",mk_sort "cat" [])]),("g",mk_sort "fun" [mk_var("A",mk_sort "cat" []),mk_var("B",mk_sort "cat" [])])])


fun ex2fsym0 name args th = th |> eqT_intro |> iffRL |> ex2fsym name args
                               |> C mp (trueI []) 

fun uex_expand th = rewr_rule [uex_def $ concl th] th

val isPr_def = define_pred
“!A B AB p1:AB->A p2:AB->B. isPr(p1,p2) <=>
   !X f:X->A g:X->B.?!fg:X->AB. p1 o fg = f & p2 o fg = g”

val isPr_ex = store_ax("isPr_ex",“!A B.?AB p1:AB->A p2:AB->B.isPr(p1,p2)”);

val Po_def = isPr_ex |> spec_all |> ex2fsym0 "*" ["A","B"] |> gen_all |> store_as "Po_def"

val p1_def = Po_def |> spec_all |> ex2fsym0 "p1" ["A","B"] |> gen_all |> store_as "p1_def"

val p2_def = p1_def |> spec_all |> ex2fsym0 "p2" ["A","B"] |> gen_all |> store_as "p2_def"


val Pa_def = p2_def |> rewr_rule[isPr_def] |> spec_all
                    |> uex_expand 
                    |> ex2fsym0 "Pa" ["f","g"] |> gen_all
                    |> store_as "Pa_def"

val _ = add_parse 0x1D7D8

val _ = add_parse 120793




val isEq_def = define_pred
“!A B f:A->B g E e:E->A. 
      isEq(f,g,e) <=> 
      f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0”

val isEq_ex = store_ax("isEq_ex",“!A B f:A->B g:A->B.?E e:E->A.isEq(f,g,e)”)

val Eqa_def = 
    isEq_def |> iffLR 
             |> spec_all |> undisch |> conjE2 
             |> spec_all |> undisch |> uex_expand
             |> conj_all_assum |> disch_all
             |> ex2fsym "Eqa" ["f","g","e","a"]
             |> gen_all
             |> store_as "Eqa_def"
 

val is0_def = 
define_pred “!ZERO.is0(ZERO) <=> !X.?!f:ZERO ->X. T”


val ZERO_ex = store_ax("ZERO_ex",“?ZERO.is0(ZERO)”)

val ZERO_def = ex2fsym0 "0" [] ZERO_ex |> store_as "ZERO_def"

val ZERO_prop = ZERO_def |> conv_rule (once_depth_fconv no_conv (rewr_fconv (spec_all is0_def))) |> store_as "ZERO_prop"

val From0_def = ZERO_prop |> spec_all |> uex_expand |> ex2fsym0 "From0" ["X"] |> gen_all |> store_as "From0_def"



val is1_def = define_pred
“!ONE. is1(ONE) <=> !X.?!f:X->ONE.T”



val ONE_ex = store_ax("ONE_ex",“?ONE.is1(ONE)”)
                    
val ONE_def = ex2fsym0 "1" [] ONE_ex |> store_as "ONE_def"

val ONE_prop = ONE_def |> rewr_rule [is1_def]
                       |> store_as "ONE_prop"

val To1_def = ONE_prop |> spec_all |> uex_expand |> ex2fsym0 "To1" ["X"] |> gen_all |> store_as "To1_def"



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


val isExp_def = define_pred
“!A B A2B ev:A * A2B -> B.
         isExp(ev) <=> !X f:A * X->B. ?!h:X->A2B. ev o Pa(p1(A,X), h o p2(A,X)) = f”




val isExp_ex = store_ax("isExp_ex",“!A B. ?A2B ev:A * A2B->B. isExp(ev)”);

val Exp_def = isExp_ex |> spec_all 
                       |> ex2fsym0 "Exp" ["A","B"] |> gen_all
                       |> store_as "Exp_def"

val Ev_def = Exp_def |> spec_all |> rewr_rule[isExp_def]
                     |> ex2fsym0 "Ev" ["A","B"]
                     |> gen_all
                     |> store_as "Ev_def"

val Tp_def = Ev_def |> spec_all |> uex_expand 
                    |> ex2fsym0 "Tp" ["f"] |> gen_all
                    |> store_as "Tp_def"


val _ = new_pred "isPb"
  [("f",fun_sort (mk_cat "X") (mk_cat "Z")),
   ("g",fun_sort (mk_cat "Y") (mk_cat "Z")),
   ("p",fun_sort (mk_cat "P") (mk_cat "X")),
   ("q",fun_sort (mk_cat "P") (mk_cat "Y"))];


val isPb_def = store_ax("isPb_def",
“!X H f:X -> H Y g : Y -> H P p : P -> X q : P -> Y.
 isPb(f, g, p, q) <=> f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v”);

val isPb_expand = isPb_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : A -> P. p:P->X o a = u & q:P->Y o a = v”) |> store_as "isPb_expand";

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

val uex_tac:tactic = fn (ct,asl,w) =>
    let val th = uex_def w
        val w' = snd $ dest_dimp $ concl th
    in ([(ct,asl,w')],(sing (dimp_mp_r2l th)))
    end
 
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

val iscoPr_def = define_pred
“!A B AB i1:A->AB i2:B->AB. iscoPr(i1,i2) <=>
   !X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g”




val iscoPr_ex = store_ax("iscoPr_ex",“!A B.?AB i1:A->AB i2:B->AB.iscoPr(i1,i2)”);

val coPo_def = iscoPr_ex |> spec_all |> ex2fsym0 "+" ["A","B"] |> gen_all |> store_as "coPo_def";

val i1_def = coPo_def |> spec_all |> ex2fsym0 "i1" ["A","B"] |> gen_all |> store_as "i1_def";

val i2_def = i1_def |> spec_all |> ex2fsym0 "i2" ["A","B"] |> gen_all |> store_as "i2_def";

val coPa_def = i2_def |> rewr_rule[iscoPr_def] |> spec_all
                      |> uex_expand 
                      |> ex2fsym0 "coPa" ["f","g"]
                      |> gen_all
                      |> store_as "coPa_def";


val _ = new_pred "Mono" [("f",fun_sort (mk_cat "A") (mk_cat "B"))]

val Mono_def = store_ax("Mono_def",“!A B f:A->B. Mono(f) <=> !X g:X->A h. f o g = f o h ==> g = h”);

val rfs = rev_full_simp_tac

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

val Epi_def = store_ax("Epi_def",“!A B f:A->B. Epi(f) <=> !X g:B->X h. g o f = h o f ==> g = h”);

val CC3 = store_ax("CC3", “~Epi(coPa(0f,1f))”);

val isgen_def = define_pred
“!G. isgen(G) <=> !A B f1:A->B f2. ~(f1 = f2) ==> ?g: G -> A. ~(f1 o g = f2 o g)”


val isPb_def = store_ax("isPb_def",
“!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y.
 isPb(f, g, p, q) <=> f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v”);


val _ = new_pred "isPo"
  [("f",fun_sort (mk_cat "Z") (mk_cat "X")),
   ("g",fun_sort (mk_cat "Z") (mk_cat "Y")),
   ("p",fun_sort (mk_cat "X") (mk_cat "P")),
   ("q",fun_sort (mk_cat "Y") (mk_cat "P"))];


val isPo_def = store_ax("isPo_def",
“!H X f:H -> X Y g : H -> Y P p : X -> P q : Y -> P.
 isPo(f, g, p, q) <=> p o f = q o g &
 !A u : X -> A v : Y -> A. 
    u o f = v o g ==> 
    ?!a : P -> A. a o p = u & a o q = v”);

val isPo_expand = isPo_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : P -> A. a o p:X->P = u & a o q:Y->P = v”) |> store_as "isPo_expand";

val isPo_ex = store_ax("isPo_ex",“!H X f:H->X Y g:H->Y. ?P p:X->P q:Y->P. isPo(f,g,p,q)”);

val E_ex = prove_store("E_ex",
e0
(rw[isPo_ex] >> cheat)
(form_goal
 “∃E e1:2->E e2:2-> E. isPo(coPa(0f,1f),coPa(0f,1f),e1,e2)”));

val E_def = E_ex |> ex2fsym0 "E" [] |> ex2fsym0 "ε1" []
                 |> ex2fsym0 "ε2" [] |> store_as "E_def";

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

val two_ex = prove_store("two_ex",
e0
cheat
(form_goal
 “∃t:2->2. t = Id(2)”));

val two_def = two_ex |> ex2fsym0 "𝟚" [];

val _ = add_parse (int_of "𝟚");

val e1_ne_e2 = prove_store("e1_ne_e2",
e0
(ccontra_tac >>
 qsuff_tac ‘isPo(coPa(0f,1f),coPa(0f,1f),𝟚,𝟚)’
 >-- rw[GSYM Epi_iff_Po_Id,two_def,CC3] >>
 assume_tac E_def >> rfs[two_def] >>
 drule Po_equal_Id >> first_x_assum accept_tac
 )
(form_goal “~(ε1 = ε2)”));



val dom_ex = prove_store("dom_ex",
e0
(rpt strip_tac >> qexists_tac ‘f o 0f’ >> rw[])
(form_goal
“!A f:2->A. ?df. df = f o 0f”));

val dom_def = dom_ex |> spec_all |> ex2fsym0 "dom" ["f"]
                     |> gen_all

val cod_ex = prove_store("cod_ex",
e0
(cheat)
(form_goal
“!A f:2->A. ?df. df = f o 1f”));

val cod_def = cod_ex |> spec_all |> ex2fsym0 "cod" ["f"]
                     |> gen_all


val e1_e2_same_dom = prove_store("e1_e2_same_dom",
e0
(cheat)
(form_goal “dom(ε1) = dom(ε2)”));


val e1_e2_same_cod = prove_store("e1_e2_same_cod",
e0
(cheat)
(form_goal “cod(ε1) = cod(ε2)”));


val zero_ex = prove_store("zero_ex",
e0
cheat
(form_goal
 “∃z:2->2. z = 0f o To1(2)”));  

val zero_def = zero_ex |> ex2fsym0 "𝟘" [] 


val one_ex = prove_store("one_ex",
e0
cheat
(form_goal
 “∃l:2->2. l = 1f o To1(2)”));  

val one_def = one_ex |> ex2fsym0 "𝟙" [] 


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

(*all distinct*)


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


val flip_tac = 
fconv_tac (rewr_fconv (eq_sym "fun"));


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

(*
And y: 2 -*3 with y 0 0 = a 0 O and y a 1 = ,B a 1. This completes the axiom.
 The functor F: 3 2 with F a = 0 and F o /3 = 2 proves L i /3. The domain and
 codomain relations show neither a nor ,B equals y.
*)

val CC4_1 = store_ax("CC4_1",
“γ o 0f = α o 0f & γ o 1f = β o 1f”)

val CC4_2 = store_ax("CC4_2",“isPo(1f,0f,α,β)”)

val Poa_def = 
    isPo_expand |> iffLR 
                |> strip_all_and_imp
                |> conjE2
                |> strip_all_and_imp
                |> ex2fsym0 
                "Poa" ["f","g","p","q","u","v"]
                |> disch 
                “u:X->A o f:H->X = v:Y->A o g”
                |> qgenl [‘A’,‘u’,‘v’]
                |> disch_all
                |> qgenl
                [‘H’,‘X’,‘f’,‘Y’,‘g’,‘P’,‘p’,‘q’]

val oa_ex = prove_store("oa_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Poa(1f,0f,α,β,f,g) o γ’ >>
 rw[])
(form_goal
 “!A f:2->A g. dom(g) = cod(f)==> 
  ?gf:2->A. gf = Poa(1f,0f,α,β,f,g) o γ”));
  
 
val oa_def = oa_ex |> spec_all |> undisch 
                   |> ex2fsym0 "@" ["g","f"]
                   |> disch_all |> gen_all


(* THEOREM 4. The composite in 2 of the nonIdentity arrow 12 with either of the
 Identity arrows 0 ? !2 and 0 a !2 is 1*)

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

val Thm4 = prove_store("Thm4",
e0
(qby_tac
 ‘dom(𝟙) = cod(𝟚)’ >-- rw[dom_cod_zot] >>
 qby_tac
 ‘dom(𝟚) = cod(𝟘)’ >-- rw[dom_cod_zot] >>
 drule oa_def >>
 rev_drule oa_def >> arw[] >> strip_tac >-- 
 (irule dom_cod_is_two >>
 assume_tac CC4_2 >> drule Poa_def >>
 fs[GSYM dom_def,GSYM cod_def] >>
 first_x_assum (qsspecl_then [‘𝟚’,‘𝟙’] assume_tac) >>
 rfs[] >>
 rw[cod_def,dom_def,CC4_1,o_assoc] >>
 arw[GSYM o_assoc] >> 
 rw[GSYM dom_def,GSYM cod_def,dom_cod_zot]) >>
 irule dom_cod_is_two >>
 assume_tac CC4_2 >> drule Poa_def >>
 fs[GSYM dom_def,GSYM cod_def] >>
 first_x_assum (qsspecl_then [‘𝟘’,‘𝟚’] assume_tac) >>
 rfs[] >>
 rw[cod_def,dom_def,CC4_1,o_assoc] >>
 arw[GSYM o_assoc] >> 
 rw[GSYM dom_def,GSYM cod_def,dom_cod_zot]
 )
(form_goal “𝟙 @ 𝟚 = 𝟚 & 𝟚 @ 𝟘 = 𝟚”)
)



(*composable*)
val cpsb_def = define_pred “!A f:2->A g:2->A. cpsb(g,f) <=> dom(g) = cod(f)”;

val isid_def = define_pred “!A f:2->A. isid(f) <=> ?f0:1->A. f = f0 o To1(2)”

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

val Thm5_1 = prove_store("Thm5_1",
e0
(rpt strip_tac >> 
 fs[cpsb_def] >> 
 assume_tac CC4_2 >> drule Poa_def >>
 first_assum (qsspecl_then [‘𝟚’,‘𝟙’] assume_tac) >>
 fs[GSYM dom_def,GSYM cod_def,dom_cod_zot] >>
 first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
 rfs[] >> 
 qby_tac ‘f o Poa(1f, 0f, α, β, 𝟚, 𝟙) = 
          Poa(1f, 0f, α, β, f, g)’
 >-- (first_x_assum irule >> 
     arw[o_assoc,two_def,IdR] >>
     fs[isid_def] >> rw[one_def,GSYM cod_def,GSYM o_assoc] >>
     qpick_x_assum ‘dom(g) = cod(f)’ (assume_tac o GSYM) >>
     arw[dom_def,o_assoc] >>
     qsuff_tac ‘f0 o (To1(2) o 0f) o To1(2) = f0 o To1(2)’ 
     >-- rw[o_assoc] >> rw[one_to_one_Id,IdL]) >>
 drule oa_def >> arw[] >>
 pop_assum (K all_tac) >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[o_assoc] >>
 assume_tac Thm4 >> assume_tac dom_one_cod_two >>
 drule oa_def >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[two_def,IdR])
(form_goal
 “!A g:2->A. isid(g) ==> 
  (!f. cpsb(g,f) ==> g @ f = f)”));


val Thm5_2 = prove_store("Thm5_2",
e0
(rpt strip_tac >> 
 fs[cpsb_def] >> 
 assume_tac CC4_2 >> drule Poa_def >>
 first_assum (qsspecl_then [‘𝟘’,‘𝟚’] assume_tac) >>
 fs[GSYM dom_def,GSYM cod_def,dom_cod_zot] >>
 first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
 rfs[] >> 
 qby_tac ‘g o Poa(1f, 0f, α, β, 𝟘, 𝟚) = 
          Poa(1f, 0f, α, β, f, g)’
 >-- (first_x_assum irule >> 
     arw[o_assoc,two_def,IdR] >>
     fs[isid_def] >> rw[zero_def,GSYM cod_def,GSYM o_assoc] >>
     arw[GSYM dom_def] >> rw[cod_def,o_assoc] >> 
     qsuff_tac ‘f0 o (To1(2) o 1f) o To1(2) = f0 o To1(2)’ 
     >-- rw[o_assoc] >> rw[one_to_one_Id,IdL]) >>
 drule oa_def >> arw[] >>
 pop_assum (K all_tac) >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[o_assoc] >>
 assume_tac Thm4 >> assume_tac dom_two_cod_zero>>
 drule oa_def >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[two_def,IdR])
(form_goal
 “!A f:2->A. isid(f) ==> 
  (!g. cpsb(g,f) ==> g @ f = g)”));

val _ = add_parse (int_of "¹")
val _ = add_parse (int_of "²")
val _ = add_parse (int_of "³")
val _ = add_parse (int_of "ᵅ") 
val _ = add_parse (int_of "ᵝ")  
val _ = add_parse (int_of "ˠ")  


val Tp0_ex = prove_store("Tp0_ex",
e0
(rpt strip_tac >> qexists_tac ‘Ev(X,Y) o Pa(Id(X),f o To1(X))’ >>
 rw[])
(form_goal
 “!X Y f:1->Exp(X,Y).?tp0:X->Y. Ev(X,Y) o Pa(Id(X),f o To1(X)) = tp0”));

val Tp0_def = 
    Tp0_ex |> spec_all |> ex2fsym0 "Tp0" ["f"] |> gen_all
           |> store_as "Tp0_def"



val Swap_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac ‘Pa(p2(A,B),p1(A,B))’ >> rw[])
(form_goal
 “!A B. ?swap:A * B ->B * A. Pa(p2(A,B),p1(A,B)) = swap”)

val Swap_def = 
    Swap_ex |> spec_all |> eqT_intro
               |> iffRL |> ex2fsym "Swap" ["A","B"] 
               |> C mp (trueI []) |> gen_all
               |> store_as "Swap_def";

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
 strip_tac (* 2 *) >--
 (irule is_Pa >> arw[]) >> once_rw[to_P_component])
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




(*

val Thm6_square= prove_store("Thm6_sqaure",
e0
()
(form_goal
 “!fgij:2 * 2 -> A ghkl:2 * 2 -> A f g i j h k l.
   fgij o Pa(0f o To1(2),Id(2)) = f &
   fgij o Pa(1f o To1(2),Id(2)) = g &
   fgij o Pa(Id(2),0f o To1(2)) = i &
   fgij o Pa(Id(2),1f o To1(2)) = j &
   ghkl o Pa(0f o To1(2),Id(2)) = g &
   ghkl o Pa(1f o To1(2),Id(2)) = h &
   ghkl o Pa(Id(2),0f o To1(2)) = k &
   ghkl o Pa(Id(2),1f o To1(2)) = l ==>
   
   
  fgij o Pa(1f o To1(2),Id(2)) = f 
  ghkl o Pa(0f o To1(2),Id(2)) & 
  !cmp:2 * 2 ->A. 
  cmp o Pa(0f o To1(2),Id(2)) = 

  cpsb(ghkl,fgij) ==> 
  Tp0(ghkl @ fgij) o Pa(Id(2),0f o To1(2)) = 
  (Tp0(ghkl) o Pa(Id(2),0f o To1(2))) @ ”));


val Thm6 = prove_store("Thm6",
e0
()
(form_goal
 “!fgij:2-> Exp(2,A) ghkl:2-> Exp(2,A). 
  cpsb(ghkl,fgij) ==> 
  Tp0(ghkl @ fgij) o Pa(Id(2),0f o To1(2)) = 
  (Tp0(ghkl) o Pa(Id(2),0f o To1(2))) @ ”));

*)



(*commutative square*)

val csL_ex = prove_store("csL_ex",
e0
(cheat)
(form_goal
 “!A cs:2 * 2 ->A. 
  ∃l. l = cs o Pa(𝟘,𝟚)”));

val csL_def = csL_ex |> spec_all |> ex2fsym0 "csL" ["cs"]
                     |> gen_all

val csR_ex = prove_store("csR_ex",
e0
(cheat)
(form_goal
 “!A cs:2 * 2 ->A. 
  ∃r. r = cs o Pa(𝟙,𝟚)”));


val csR_def = csR_ex |> spec_all |> ex2fsym0 "csR" ["cs"]
                     |> gen_all


val csT_ex = prove_store("csT_ex",
e0
(cheat)
(form_goal
 “!A cs:2 * 2 ->A. 
  ∃t.t  = cs o Pa(𝟚,𝟘)”));

val csT_def = csT_ex |> spec_all |> ex2fsym0 "csT" ["cs"]
                     |> gen_all

val csB_ex = prove_store("csB_ex",
e0
(cheat)
(form_goal
 “!A cs:2 * 2 ->A. 
  ∃b. b = cs o Pa(𝟚,𝟙)”));

val csB_def = csB_ex |> spec_all |> ex2fsym0 "csB" ["cs"]
                     |> gen_all

val Pt_ex = prove_store("Pt_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Ev(A,B) o Pa(p1(A,X), h o p2(A,X))’ >>
 rw[])
(form_goal “∀A B X h:X-> Exp(A,B). ∃pt. pt = Ev(A,B) o Pa(p1(A,X), h o p2(A,X))”));

val Pt_def = Pt_ex |> spec_all |> ex2fsym0 "Pt" ["h"]
                   |> gen_all |> store_as "Pt_def";

(*exponential, on dom *)
val Ed_ex = prove_store("Ed_ex",
e0
(rpt strip_tac >>
 qexists_tac‘Tp(Ev(B,X) o Pa(f o p1(A,Exp(B,X)),p2(A,Exp(B,X))))’ >> rw[])
(form_goal
 “∀A B f:A->B X. ∃ed. ed = Tp(Ev(B,X) o Pa(f o p1(A,Exp(B,X)),p2(A,Exp(B,X))))”));

val Ed_def = Ed_ex |> spec_all |> ex2fsym0 "Ed" ["f","X"]
                   |> gen_all

(*erase the label A^1 , an iso A^1 -> A*)
val Er1_ex = prove_store("Er1_ex",
e0
(strip_tac >> qexists_tac ‘Ev(1,A) o Pa(To1(Exp(1,A)),Id(Exp(1,A)))’ >> rw[])
(form_goal
 “∀A. ∃er1. er1 = Ev(1,A) o Pa(To1(Exp(1,A)),Id(Exp(1,A)))”));

val Er1_def = Er1_ex |> spec_all |> ex2fsym0 "Er1" ["A"]
                     |> gen_all

val A1f_ex = prove_store("A1f_ex",
e0
(strip_tac >> qexists_tac ‘Er1(A)  o Ed(1f,A)’ >> rw[])
(form_goal
 “∀A. ∃a1f. a1f = Er1(A) o Ed(1f,A)”));

fun define_const f fsymname inputs = 
let val (l,r) = dest_eq f
    val (n,s) = dest_var l
    val g = form_goal (mk_exists n s f)
    val eth =
        prove_store(fsymname ^ "_ex",e0
                    (exists_tac r >> accept_tac (refl r))
                    g)
    val th = ex2fsym0 fsymname inputs eth |> gen_all
                      |> store_as (fsymname ^ "_def")
in (eth,th)
end

(*define_const “a1f = Er1(A) o Ed(1f,A)” "A1f" ["A"]*)

(*
val (Ed1_ex,Ed1_def) = define_const “a1f = Er1(A) o Ed(f:X->Y,A)” "Ed1" ["f","A"];

*)


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



(*
A0f: A^2 -> A

2 -> A^2 -> A


*)


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
 fs[cpsb_def] >> drule oa_def >> 
 arw[] >> rw[dom_def,cod_def,o_assoc,CC4_1] >>
 assume_tac CC4_2 >> drule Poa_def >>
 fs[dom_def,cod_def] >>
 last_x_assum (assume_tac o GSYM) >>
 first_x_assum drule >> arw[GSYM o_assoc])
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

val pT_ex = prove_store("pT_ex",
e0
(rpt strip_tac >> qexists_tac ‘(Pt(h) o Swap(X,A))’ >>
 rw[])
(form_goal “∀A B X h:X->Exp(A,B). 
 ∃pt. pt = Pt(h) o Swap(X,A)”));

val pT_def = pT_ex |> spec_all |> ex2fsym0 "pT" ["h"]
                   |> gen_all


(* multiply by 1 is iso

A -- Pa(Id(A),To1(A)) --> A * 1 -- p1(A,1) --> A
*)

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
 
(*
generate lemma which says composing with them eq iff eq
*)

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



val id_ex = prove_store("id_ex",
e0
(rpt strip_tac >> qexists_tac ‘a o To1(2)’ >> rw[])
(form_goal
 “∀A a:1->A. ∃id:2->A. id = a o To1(2)”));

val id_def = id_ex |> spec_all |> ex2fsym0 "id" ["a"]
                   |> gen_all |> store_as "id_def";
    
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

(*left_upper*)
val cs_lu_ex = prove_store("cs_lu_ex",
e0
(cheat)
(form_goal
 “∀A f:2->A. ∃s: 2 * 2 -> A. 
  csL(s) = f ∧ csR(s) = id(cod(f)) ∧ 
  csT(s) = f ∧ csB(s) = id(cod(f))”));

(*right lower*)
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

val Poa_ab = prove_store("Poa_ab",
e0
(rpt gen_tac >> disch_tac >>
 irule Poa_def >> fs[dom_def,cod_def,CC4_2])
(form_goal
 “∀A u v. dom(v) = cod(u) ⇒ 
  (Poa(1f, 0f, α, β, u, v) o α = u &
  Poa(1f, 0f, α, β, u, v) o β = v) & 
  !a' : 3 -> A.
   a' o α = u & a' o β = v ==>
   a' = Poa(1f, 0f, α, β, u, v)”));

val Poa_ab_eqn = Poa_ab |> strip_all_and_imp |> conjE1 
                     |> disch_all |> gen_all

val is_Poa_ab = Poa_ab |> strip_all_and_imp |> conjE2 
                     |> disch_all |> gen_all

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


val oa_def' = rewr_rule [GSYM cpsb_def] oa_def

val Poa_ab_eqn' = rewr_rule [GSYM cpsb_def] Poa_ab_eqn


val o4_middle = prove_store("o4_middle",
e0
(rw[o_assoc])
(form_goal “∀A B C D K f:A->B g:B->C h:C->D j:D->K.
 j o h o g o f = j o (h o g) o f”));

val RT_cs2 = prove_store("RT_cs2",
e0
(assume_tac cs2_RT_cpsb >> drule oa_def'>>
 arw[] >>
 irule to_P_eq >> rw[p12_of_Pa] >> strip_tac >> 
 irule dom_cod_is_two >> rw[dom_def,cod_def,o_assoc,CC4_1] >>
 drule Poa_ab_eqn' >> 
 arw[o4_middle] >>
 rw[GSYM o_assoc,p12_of_Pa,one_def,two_def,zero_def,IdL] >>
 rw[o_assoc,one_to_one_Id,IdR])
(form_goal “Pa(𝟙, 𝟚) @ Pa(𝟚, 𝟘) = Pa(𝟚,𝟚)”));


val BL_cs2 = prove_store("BL_cs2",
e0
(assume_tac cs2_BL_cpsb >> drule oa_def'>>
 arw[] >>
 irule to_P_eq >> rw[p12_of_Pa] >> strip_tac >> 
 irule dom_cod_is_two >> rw[dom_def,cod_def,o_assoc,CC4_1] >>
 drule Poa_ab_eqn' >> 
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


val iso_def = define_pred
“!A f:2->A. iso(f) <=> 
 ?g:2->A. dom(g) = cod(f) & dom(f) = cod(g) &
 g @ f = dom(f) o To1(2) & f @ g = cod(f) o To1(2) ”


(*
CC5. If R(f, g) defines a functorial relation from arrows of A to those of B, then
 there is a functor F: A -+ B s


*)
(*
usual functor:


F(id(A)) = id(F(A))

F(g o f) = F(g) o F(f)

∀a:2->A. ∃!b:2->B. R(a,b) ∧
∀a:2->A. isid(a) ⇒ ∀b. R(a,b) ⇒ isid(b)∧
∀f:2->A g:2->A h:2->B. R(g o f,h) ⇔ 
∀f1 g1. R(g,g1) ∧ R(f,f1) ⇒ h = g1 @ f1 ⇒
∃!func:A->B.
∀f:2->A g:2->B. g o f = 

∀b. R(id(a),b) ⇔ b = id 

∀h. R(g o f,h) ⇔ ∃g1 f1. R(g,g1) ∧ R(f,f1) ∧ h = g1 @ f1


*)


val CC5 = store_ax("CC5",
“∀A B. 
 (∀f:2->A. ∃!g:2->B. R(f,g)) ∧
 (∀f:2->A g:2->B. R(f,g) ⇒ 
  R(id(dom(f)),id(dom(g))) ∧ R(id(cod(f)),id(cod(g)))) ∧
 (∀f:2->A g:2->A h: 2->B. cpsb(g,f) ⇒
  R(g @ f, h) ⇒ ∀f1 g1. R(f,f1) ∧ R(g,g1) ⇒ h = g1 @ f1) ⇒
 ∃cf:A->B. ∀a:2->A b:2->B. R(a,b) ⇔ cf o a = b”)


val one2one_def = define_pred “∀A B f:A->B. one2one(f) ⇔ 
 (∀a1:2->A a2:2->A. f o a1 = f o a2 ⇒ a1 = a2)”;

val onto_def = define_pred “∀A B f:A->B. onto(f) ⇔ 
 (∀b:2->B. ∃a:2->A. b = f o a)”;


fun MAP f l = 
   let
     (* map2 is the version where something has changed *)
     fun map2 A [] = List.rev A
       | map2 A (h::t) = map2 ((f h handle e => h) :: A) t
     (* map1 is the version to call where nothing has changed yet *)
     fun map1 n [] = raise UNCHANGED
       | map1 n (h::t) = 
           case total f h of
             SOME fh => map2 (fh::(rev $ List.take(l,n))) t
           | NONE => map1 (n + 1) t
   in
     map1 0 l
   end


fun fVar_Inst_th (pair as (P,(argl:(string * sort) list,Q0))) th = 
    let val (ct,asl,w) = dest_thm th
        val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q0) argl
        val ct' = HOLset.union(ct,lcs)
        val aslw' = MAP (fVar_Inst_f pair) (w :: asl)
    in mk_thm (ct',tl aslw',hd aslw')
    end

fun fVar_sInst_th f f' th = 
    let val (P,args) = dest_fvar f
        val vl = List.map dest_var args
    in fVar_Inst_th (P,(vl,f')) th
    end

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
 >-- (fs[] >> 
 qby_tac ‘cpsb(g1,f1)’ 
 >-- (fs[cpsb_def,dom_def,cod_def,o_assoc,one2one_def] >>  
     qsuff_tac ‘g1 o 0f o To1(2) = f1 o 1f o To1(2)’
     >-- (strip_tac >> ccontra_tac >> drule CC2_2 >>
         fs[To1_def,o_assoc]) >>
     first_x_assum irule >> fs[GSYM o_assoc]) >>
 drule $ GSYM fun_pres_oa >> 
 fs[] >> fs[one2one_def] >> first_x_assum irule >> arw[])
 >-- (uex_tac >> fs[onto_def] >>
     first_x_assum (qspecl_then [‘f'’] strip_assume_tac) >>
     qexists_tac ‘a’ >> arw[] >> rpt strip_tac >>
     fs[one2one_def] >> first_x_assum irule >> arw[])
 >-- (arw[fun_of_id]) >>
 arw[fun_of_id]
 )
(form_goal
 “∀A B f:A->B. one2one(f) ∧ onto(f) ⇒ Iso(f)”));
end

(*
 THEOREM 10. A monic i: I >-4 A factors through j: J >-4 A if every arrow factor-
 ing through i factors throug

*)

val Mono_one2one = prove_store("Mono_one2one",
e0
(rw[Mono_def,one2one_def] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal “∀A B f:A->B. Mono(f) ⇒ one2one(f)”));



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

(*
THEOREM 11. 3 has only the arrows a, β and γ and th
*)

val ba_cpsb = prove_store("ba_cpsb",
e0
(rw[cpsb_def] >> assume_tac CC4_2 >> fs[isPo_def,dom_def,cod_def])
(form_goal
 “cpsb(β,α)”));

val oa_ba = prove_store("oa_ba",
e0
(assume_tac ba_cpsb >> drule oa_def' >> arw[] >>
 fs[cpsb_def] >> drule Poa_ab >> fs[] >>
 first_x_assum (qspecl_then [‘Id(3)’] assume_tac) >>
 fs[IdL] >> pop_assum (assume_tac o GSYM) >> arw[IdL])
(form_goal “β @ α = γ”));

val Poa_ab_Id = prove_store("Poa_ab_Id",
e0
(assume_tac ba_cpsb >> fs[cpsb_def] >> drule Poa_ab >>
 rfs[] >> flip_tac >> first_x_assum irule >>
 rw[IdL])
(form_goal “Poa(1f,0f,α,β,α,β) = Id(3)”));


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
     >-- (rw[GSYM Poa_ab_Id] >>
         assume_tac Poa_ab >> fs[GSYM cpsb_def] >>
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
 drule Poa_ab >>
 qexists_tac ‘Poa(1f, 0f, α, β, Pa(𝟚, 𝟘), Pa(𝟙, 𝟚))’ >>
 arw[] >>
 rw[GSYM oa_ba] >> assume_tac ba_cpsb >> drule fun_pres_oa >>
 arw[RT_cs2] >>
 irule Thm7 >> cheat(*trivial*)
     )
(form_goal “∀f:2->3. f = α | f = β | f = γ | f = id(dom(α)) | f = id(cod(β)) | f = id(dom(β))”));


val _ = add_parse (int_of "η")

(*
val Laj_def = 

val AJC_def = 
“∀ajc:1->Exp(X,A) * Exp(A,X) * Exp(X,Exp(X,2)) * Exp(A,Exp(A,2)). 
 AJC(cj) ⇔ 
 ”

prove_store("AJC_def",
*)

val cpnt_ex = prove_store("cpnt_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Pt(η o a) o Pa(Id(2),To1(2))’ >> rw[])
(form_goal “∀A B η:A -> Exp(2,B) a. ∃cpnt.cpnt = Pt(η o a) o Pa(Id(2),To1(2))”));

val cpnt_def = cpnt_ex |> spec_all |> ex2fsym0 "cpnt" ["η","a"]
                       |> gen_all |> store_as "cpnt_def";



val Nt_def = define_pred “∀A B F G η. Nt(η:A -> Exp(2,B),F:A->B,G:A->B) ⇔ 
 (∀f:2->A. csL(Pt(η o f)) = F o f ∧ csR(Pt(η o f)) = G o f)”


val all_Nt = prove_store("all_Nt",
e0
(cheat)
(form_goal “∀A B η:A -> Exp(2,B). 
 Nt(η,Er1(B) o  Ed(0f,B) o η, Er1(B) o Ed(1f,B) o η)”));




(*

prove as thms that:

(∀a:1->A. dom(cpnt(η,a)) = F o a ∧ cod(cpnt(η,a)) = G o a) ∧ 
 (∀f:2->A. (G o f) @ cpnt(η,dom(f)) = cpnt(η,cod(f)) @ (F o f))

*)


val ID_ex = prove_store("ID_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(F o p2(2,A))’ >> rw[])
(form_goal “∀A B F:A->B. ∃IDF.IDF = Tp(F o p2(2,A))”));

val ID_def = ID_ex |> spec_all |> ex2fsym0 "ID" ["F"] |> gen_all
                   |> store_as "ID_def";

(*exponential, cod*)
val Ec_ex = prove_store("Ec_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(f o Ev(C,A))’ >> rw[])
(form_goal “∀A B f:A->B C. ∃ec:Exp(C,A)->Exp(C,B). ec = Tp(f o Ev(C,A))”));

val Ec_def = Ec_ex |> spec_all |> ex2fsym0 "Ec" ["f","C"]
                   |> store_as "Ec_def";

val Rw_ex = prove_store("Rw_ex",
e0
(rpt strip_tac >> qexists_tac ‘Ec(H,2) o η’ >> rw[])
(form_goal “∀A B η:A -> Exp(2,B) C H:B->C. ∃lw. lw = Ec(H,2) o η”));


val Lw_ex = prove_store("Lw_ex",
e0
(rpt strip_tac >> qexists_tac ‘η o H’ >> rw[])
(form_goal “∀A B η:A -> Exp(2,B) X H:X->A. ∃rw. rw = η o H”));

val Lw_def = Lw_ex |> spec_all |> ex2fsym0 "Lw" ["η","H"]
                   |> gen_all
                   |> store_as "Lw_def";


val Rw_def = Rw_ex |> spec_all |> ex2fsym0 "Rw" ["H","η"]
                   |> gen_all
                   |> store_as "Rw_def";

val Ed_Po_Pb = prove_store("Ed_Po_Pb",
e0
(cheat)
(form_goal “∀X Y f:X->Y Z g:X->Z P p:Y->P q:Z->P. isPo(f,g,p,q) ⇒
 ∀A. isPb(Ed(f,A),Ed(g,A),Ed(p,A),Ed(q,A))”));

val Ed_ab_Pb0 = prove_store("Ed_ab_Pb0",
e0
(strip_tac >> irule Ed_Po_Pb >> rw[CC4_2])
(form_goal “∀A.isPb(Ed(1f,A),Ed(0f,A),Ed(α,A),Ed(β,A))”));





val Pba_def = 
    isPb_expand |> iffLR 
                |> strip_all_and_imp
                |> conjE2
                |> strip_all_and_imp
                |> ex2fsym0 
                "Pba" ["f","g","p","q","u","v"]
                |> disch 
                “f:X->H o u:A->X = g:Y->H o v”
                |> qgenl [‘A’,‘u’,‘v’]
                |> disch_all
                |> qgenl
                [‘H’,‘X’,‘f’,‘Y’,‘g’,‘P’,‘p’,‘q’]


val Ed_ab_Pb = prove_store("Ed_ab_Pb",
e0
(cheat)
(form_goal “∀A.isPb(Er1(A) o Ed(1f,A),Er1(A) o Ed(0f,A),Ed(α,A),Ed(β,A))”));

(*cod η = dom ε *)
val vo_ex = prove_store("vo_ex",
e0
(cheat)
(form_goal
 “∀A B η:A -> Exp(2,B) ε:A->Exp(2,B). 
  ∃μ:A -> Exp(2,B). 
  μ = Ed(γ, B) o Pba(Er1(B) o Ed(1f,B),Er1(B) o Ed(0f,B),Ed(α,B),Ed(β,B),η,ε)
”));


val vo_def = vo_ex |> spec_all |> ex2fsym0 "vo" ["ε","η"]
                   |> qgen ‘ε’ |> gen_all |> store_as "vo_def" 

val Adj_def = define_pred “
∀A X L:X->A R:A->X η ε. Adj(L:X->A, R:A->X, η:X-> Exp(2,X), ε:A -> Exp(2,A)) ⇔ 
 vo(Lw(ε,L),Rw(L,η))  = ID(L) ∧ 
 vo(Rw(R,ε),Lw(η,R))  = ID(R)”

val UFrom_def = define_pred
“∀D C F:D->C x y f.UFrom(F,x:1->C,y:1->D,f:2->C) ⇔ 
 dom(f) = F o y ∧ cod(f) = x ∧
 (∀x':1->D f':2-> C. dom(f') = F o x' ∧ cod(f') = x ⇒
 ∃!fh:2->D. f' = f @ (F o fh))”



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


val Tp1_ex = prove_store("Tp1_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(f o p1(A,1))’ >> rw[])
(form_goal
“!A B f:A->B.?tpf:1->Exp(A,B).Tp(f o p1(A,1)) = tpf”));


val Tp1_def = Tp1_ex |> spec_all |> ex2fsym0 "Tp1" ["f"] 
                     |> gen_all |> store_as "Tp1_def"; 


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
((*dimp_tac >> strip_tac >> arw[] >>
cases_on “A” >> fs[]last_x_assum mp_tac >> pop_assum mp_tac >> 
(*if use fs, then loop*)
arw[] >> rw[] *) cheat)
(form_goal “A | B ⇔ (~A ⇒ B)”));

(*
dimp_tac >> strip_tac (* 3 *)
once_rw[OR_NOT_IMP]
“~(~A ∧ ~ B) ⇔ A | B”

TODO: debug here, loop

“A | B” |> rewr_fconv OR_NOT_IMP basic_once_fconv no_conv OR_NOT_IMP

“~(~A ∧ ~ B) ⇔ A | B”
*)

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
 >-- (rpt gen_tac >> strip_tac >> pop_assum mp_tac >> once_rw[cpsb_def] >>
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
     once_arw[]  >> rw[] >> rpt strip_tac >> arw[]) >>
 strip_tac >-- (strip_tac >> uex_tac >>
 cases_on “dom(f':2->B) = B0” >> cases_on “cod(f':2->B) = B0” >>
 arw[] (* 4 *)
 >-- (qexists_tac ‘h o 𝟘’ >> rpt strip_tac >> arw[])
 >-- (qexists_tac ‘h’ >> rpt strip_tac >> arw[])
 >-- (qexists_tac ‘k’ >> rpt strip_tac >> arw[]) >>
 qexists_tac ‘h o 𝟙’ >> rpt strip_tac >> arw[]) >>
 rpt gen_tac >> 
 cases_on “dom(f':2->B) = B0” >> cases_on “cod(f':2->B) = B0” >>
 arw[] (* 4 *) >>
 strip_tac >> arw[id1,o_zero_dom,o_one_cod] )
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
 strip_tac (* 2 *) >--
 (irule is_coPa >> arw[]) >> once_rw[from_coP_component])
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
     strip_tac >--  (irule $ iffLR fun_ext >>
     rw[o_assoc] >> strip_tac >>
     fs[dom_def] >>
     first_x_assum (qsspecl_then [‘i2(A, B) o a’,‘a o 0f’] assume_tac) >>
     fs[o_assoc] >> 
     qsuff_tac ‘i2(A, B) o (k o i2(A, B)) o a = i2(A, B) o a’ 
     >-- rw[o_assoc] >>
     arw[IdL]) >> 
     irule $ iffLR fun_ext >>
     rw[o_assoc] >> strip_tac >>
     fs[dom_def] >>
     first_x_assum (qsspecl_then [‘i1(A, B) o a’,‘a o 0f’] assume_tac) >>
     fs[o_assoc] >> 
     qsuff_tac ‘i1(A, B) o (j o i1(A, B)) o a = i1(A, B) o a’ 
     >-- rw[o_assoc] >>
     arw[IdL]) >>
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


(*
A full subcategory of A is a monic i: S >-4 A such that if f a 0 and f a I are both
 in S then so is f. A full subcategory classifier is a category Cl with a selected object
 t: 1 -+ Cl such that any full subcategory i: S >-4 A is the pullback of t along a unique
 functor c: A - Cl.
*)


val FSC_def = define_pred
“!S A i:S->A. FSC(i) <=> Mono(i) & 
 !f:2->A d:1->S c:1->S. dom(f) = i o d & cod(f) = i o c ==> 
 ?f0:2->S. f = i o f0”;

val FSCC_def = define_pred
“!Cl t:1->Cl. FSCC(t) <=> 
 (!S A i:S->A. FSC(i) ==> ?!c:A->Cl. isPb(c,t,i,To1(S)))”

(*factor through*)
val FT_def = define_pred
 “∀A B f: A->B X b:X->B.FT(f,b) ⇔ ∃a:X->A. b = f o a”
 
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

val _ = new_fun "op" (cat_sort,[("A",cat_sort)])

val _ = new_fun "opf" (fun_sort (rastt "op(A)") (rastt "op(B)"),
                      [("f",fun_sort (rastt "A") (rastt "B"))])

val _ = EqSorts := "cat" :: (!EqSorts)

val isgen_op2 = prove_store("isgen_op2",
e0
cheat
(form_goal “isgen(op(2))”));

val op2_2_iso = prove_store("op2_2_iso",
e0
(cheat)
(form_goal “∃i:2->op(2) j:op(2) ->2. i o j = Id(op(2)) ∧
 j o i = Id(2)”));

val As2_Sa2_def = op2_2_iso |> ex2fsym0 "Sa2" []
                            |> ex2fsym0 "As2" []

(**)

val op1_1_iso = prove_store("op1_1_iso",
e0
(cheat)
(form_goal “∃i:1->op(1) j:op(1) -> 1. i o j = Id(op(1)) ∧
 j o i = Id(1)”));


val As1_Sa1_def = op1_1_iso |> ex2fsym0 "Sa1" []
                            |> ex2fsym0 "As1" []


(*If have equality on categories,Dom(f:A->B) = A,
 clause 3 and 4 says:


Dom(opf(f)) = op(Dom(f)) ∧
Cod(opf(f)) = op(Cod(f))

but now there is no equality on categories, so it is already given in sort

opf(f:A->B):op(A) -> op(B)
*)

val CC7 = store_ax("CC7",
“(∀A. opf(Id(A)) = Id(op(A))) ∧ 
 (∀A B f:A ->B C g:B->C. opf(g o f) = opf(g) o opf(f)) ∧
”

val _ = add_parse (int_of "%");

val _ = new_fun "%" 
(fun_sort (rastt "A") (rastt "B"),
[("A0",cat_sort),("B0",cat_sort),("A",cat_sort),("B",cat_sort),
 ("f",fun_sort (rastt "A0") (rastt "B0"))])

(*“%(op(1),op(2),1,2,opf(0f)) = 1f”*)



val _ = new_fun "ce" (fun_sort (mk_cat "A") (mk_cat "B"),
                       [("f",fun_sort (rastt "op(op(A))")
                                      (rastt "op(op(B))"))])


val Lc_ex = prove_store("Lc_ex",
e0
(rpt strip_tac >> qexists_tac ‘%(A,B,A',B,f)’ >> rw[])
(form_goal
 “∀A B A' f:A->B. ∃Lc. Lc = %(A,B,A',B,f)”));


val Lc_def = Lc_ex |> spec_all |> ex2fsym0 "Lc" ["A'","f"]
                   |> gen_all |> store_as "Lc_def";

val ce_def = store_ax ("ce_def",
“∀A B f. ce(f:op(op(A)) -> op(op(B))) =
 %(op(op(A)),op(op(B)),A,B,f)”)


val Lce_def = store_ax ("Lce_def",
“∀A B A' f. Lce(f:A -> B) =
 %(A,A',B,B,f)”)

val op_invol = store_ax("op_invol",
“∀A B f:A->B. coe(opf(opf(f))) = f”);



val CC8 = store_ax("CC8",“As2 o opf(0f) o Sa1 = 1f”);


val Thm18 = store_ax("Thm18",
e0
(rpt strip_tac >>
 )
(form_goal “∀A B. 
 (∀f:2->A. ∃!g:2->B. R(f,g)) ∧
 (∀f:2->A g:2->B. R(f,g) ⇒ 
  R(id(dom(f)),id(cod(g))) ∧ R(id(cod(f)),id(dom(g)))) ∧
 (∀f:2->A g:2->A h: 2->B. cpsb(g,f) ⇒
  R(g @ f, h) ⇒ ∀f1 g1. R(f,f1) ∧ R(g,g1) ⇒ h = f1 @ g1) ⇒
 ∃cf:op(A)->B. ∀a:2->op(A) b:2->B. R(a,b) ⇔ cf o a = b”));





(*erase op on corner*)

val _ = new_fun "Eop" (fun_sort (rastt "A") (rastt "B"),
                       [("f",fun_sort (rastt "op(A)") (rastt "op(B)"))])


val asA_ex “2 = op(2)”


val DC_def = define_pred “!A. DC(A) <=> !f:2->A. isid(f)”



val iscoEq_def = define_pred
“!A B f:A->B g cE ce:B -> cE. 
      iscoEq(f,g,ce) <=> 
      ce o f = ce o g & 
      !X x:B->X. x o f = x o g ==>
      ?!x0:cE->X. x = x0 o ce”



val iscoEq_ex = store_ax("iscoEq_ex",“!A B f:A->B g:A->B.?cE ce:B->cE.iscoEq(f,g,ce)”);

val coEqa_def = 
    iscoEq_def |> iffLR 
               |> spec_all |> undisch |> conjE2 
               |> spec_all |> undisch |> uex_expand
               |> conj_all_assum |> disch_all
               |> ex2fsym "coEqa" ["f","g","ce","x"]
               |> store_as "coEqa_def"

 
val Thm20 = prove_store("Thm20",
e0
cheat
(form_goal
 “!D. DC(D) ==> !A f:A->D g Q q:D->Q. iscoEq(f,g,q) ==>
 DC(Q)”));
 
val Thm21 = prove_store("Thm21",
e0
cheat
(form_goal
 “!A. DC(A) ==> !S i:S->A. FSC(i) ==>
  ?!c:A-> 1+1. isPb(c,i2(1,1),i,To1(S))
  ”));

val SO_def = define_pred
“!A S s:S->A. SO(s) <=> 
 (DC(S) & Mono(s) & 
  !X f:X->A. DC(X) ==> ?f0:X->S. f = s o f0)”

val SA_def = define_pred
“!A S s:S -> Exp(2,A). SA(s) <=> SO(s)”

(*
 THEOREM 22. If A has a set of objects, so does the coequalizer of any parallel pair with codomain A.

*)

val Thm22 = prove_store("Thm22",
e0
cheat
(form_goal
 “!A S s:S->A. SO(s) ==> 
  !X f:X->A g Q q:A->Q. iscoEq(f,g,q) ==>
  ?Sq sq:Sq -> Q. SO(q)”));


(*
val Thm23 = prove_store("Thm23",
e0
()
(form_goal
 “”));
*)

val ICat_def = define_pred
“∀C0 C1 s: C1-> C0 t:C1 -> C0 e: C0 -> C1 CC c: CC -> C1. 
 ICat(s,t,e,c) ⇔ 
 s o e = Id(C0) ∧ t o e = Id(C0)”

(*
THEOREM 24. If G: A2 -+ B2 and F: A -+ B are an internal functor between the
 internal categories on A and B, then G = F
*)
val IFun_def = define_pred
“∀F0:C0 -> D0 F1:C1->D1. IFun(F0,F1) ⇔
 ”

!A B. A = B <=> 
 (!X f:X->A. P(f)) <=> (!X f:X->B. P(f)) & 
 (!X f:A->X. P(f)) <=> (!X f:B->X. P(f))


val _ = 
“?C. ”
val Z2_O2_ex




IsTopos(C) ==> hasProd(C)


?C.
(asob(A:Ob(C))):ob 

asOb() 

?ETCS. 
!A B f:A->B. ?



!C \equiv to the WS of ETCS
  P()




IsTopos(ETCS) ==> hasProd(ETCS)

!A:OB(ETCS) B.? AB: OB(ETCS)....



!A:ob B:ob. 





cat sort
fun sort

C:cat

f: C:cat ->D

1 

2

a --> b

C


f(a) --> f(b)


!f:2->C g:2->C. f o 1 = g o 0 ==>
 ?! fog: 2->C. fog o 0 = f o 0 &
               fog o 1 = g o 1


!f:2->C g:2->C h:2->C.

f o 1 = g o 0 & ... ==> 
(h o_C g) o_C f = h o_C g o_C f =



Ob(C) Ar: Ob(C) -> Ob(C)


perfectoId space

fragile

IsTopos(C) ==> hasProd(C)












