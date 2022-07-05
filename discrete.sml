val Disc_def = qdefine_psym("Disc",[‘A’]) ‘!f:2->A. isid(f)’ |> gen_all;

val Epi_onto_obj = prove_store("Epi_onto_obj",
e0
(cheat)
(form_goal
 “!A B f:A->B. Epi(f) ==>
  !b:1->B. ?a:1->A. b = f o a”));
 
val iscoEq_Epi = prove_store("iscoEq_Epi",
e0
(cheat)
(form_goal
 “!A B f:A->B g:A->B Q q:B-> Q. 
  iscoEq(f,g,q) ==> Epi(q)”));

val CC5_uex = prove_store("CC5_uex",
e0
(cheat)
(form_goal
 “∀A B. 
 (∀f:2->A. ∃!g:2->B. R(f,g)) ∧
 (∀f:2->A g:2->B. R(f,g) ⇒ 
  R(id(dom(f)),id(dom(g))) ∧ R(id(cod(f)),id(cod(g)))) ∧
 (∀f:2->A g:2->A h: 2->B. cpsb(g,f) ⇒
  R(g @ f, h) ⇒ ∀f1 g1. R(f,f1) ∧ R(g,g1) ⇒ h = g1 @ f1) ⇒
 ?!cf:A->B. ∀a:2->A b:2->B. R(a,b) ⇔ cf o a = b”));

val CC5_Disc_uex = prove_store("CC5_Disc_uex",
e0
(cheat)
(form_goal
 “∀A. Disc(A) ==> !B. 
 (∀a:1->A. ∃!b:1->B. R(a,b)) ⇒
 ?!cf:A->B. ∀a:1->A b:1->B. R(a,b) ⇔ cf o a = b”));


(*zf_ne_of,CC2_1*)
val zf_xor_of = prove_store("zf_xor_of",
e0
(strip_tac >> qcases ‘f = 0f’ >> arw[zf_ne_of] >>
 ccontra_tac >>
 qsspecl_then [‘id(f)’] strip_assume_tac CC2_1 (* 3 *) >> fs[id_def]
 >-- (qby_tac
     ‘f o To1(2) o 0f = 𝟘 o 0f’ 
     >-- arw[GSYM o_assoc] >>
     fs[zero_def,o_assoc,one_to_one_Id,IdR]) 
 >-- (qby_tac
     ‘f o To1(2) o 0f = 𝟙 o 0f’ 
     >-- arw[GSYM o_assoc] >>
     fs[one_def,o_assoc,one_to_one_Id,IdR]) >>
 qby_tac
 ‘f o To1(2) o 0f = 𝟚 o 0f’ 
 >-- arw[GSYM o_assoc] >>
 fs[two_def,o_assoc,one_to_one_Id,IdR,IdL]
 )
(form_goal
 “!f:1->2. ~(f = 0f) <=> f = 1f”));




val CC5_Disc_uex_one = prove_store("CC5_Disc_uex_one",
e0
(cheat)
(form_goal
 “∀A. Disc(A) ==> 
    !a0:1->A.
      ?!cf:A->2. ∀a:1->A. cf o a = 0f <=> a = a0”));

val no_arrow_1f_to_0f = prove_store("no_arrow_1f_to_0f",
e0
(strip_tac >>
 qsspecl_then [‘f’] strip_assume_tac CC2_1 >> 
 arw[dom_cod_zot,zf_ne_of,GSYM zf_ne_of])
(form_goal
 “!f:2->2. ~(dom(f) = 1f & cod(f) = 0f)”));

(*So no arrow of Q goes from any other object*)
val no_arrow_from_other = prove_store("no_arrow_from_other",
e0
(rpt strip_tac >> ccontra_tac >>
 qsuff_tac
 ‘dom(f o g) = 1f & cod(f o g) = 0f’
 >-- rw[no_arrow_1f_to_0f] >>
 fs[dom_def,cod_def,o_assoc] >>
 first_x_assum irule >> arw[])
(form_goal
 “!A a0:1->A f:A-> 2.
  (f o a0 = 0f &
  (!a:1->A.  ~(a = a0) ==> f o a = 1f)) ==>
  !g:2->A. cod(g) = a0 ==> dom(g) = a0”));

val CC5_ap2_Thm20 = prove_store("CC5_ap2_Thm20",
e0
(cheat)
(form_goal
 “!A. 
    (!a:1->A f:2->A. cod(f) = a ==> dom(f) = a) ==>
    !f:2->A. Id(A) o f = id(dom(f))”));

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

val Disc_fac_eq = prove_store("Disc_fac_eq",
e0
(cheat)
(form_goal
 “!A B f:A->B D g:B -> D
     C h:A->C   k:C -> D.
   Disc(B) & Disc(C) ==>
   (!a:1->A. g o f o a = k o h o a) ==> g o f = k o h”));

val CC5_Disc_uex' = CC5_Disc_uex |> strip_all_and_imp  
                                 |> disch_all 
                                 |> gen_all

val Thm20 = prove_store("Thm20",
e0
(rpt strip_tac >> fs[Disc_def] >>
 strip_tac >>
 qsuff_tac
 ‘Id(Q) o f = id(dom(f))’
 >-- (rw[IdL,isid_def,id_def] >>
     strip_tac >> qexists_tac ‘dom(f)’ >>
     first_x_assum accept_tac) >>
 irule CC5_ap2_Thm20 >>
 strip_tac >> match_mp_tac no_arrow_from_other >>
 qby_tac ‘?t:1->T. q o t = a’ 
 >-- (flip_tac >> irule Epi_onto_obj >>
     irule iscoEq_Epi >>
     qexistsl_tac [‘A’,‘F’,‘G’] >> arw[]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘?g:T->2. 
  (!t'. q o t' = q o t ==> g o t' = 0f) &
  (!t'. ~(q o t' = q o t) ==> g o t' = 1f)’
 >-- (strip_tac >>
     drule $ iffLR iscoEq_def >> 
     pop_assum strip_assume_tac >> 
     qsuff_tac
     ‘g o F = g o G’
     >-- (strip_tac >>
         first_x_assum drule >> 
         pop_assum (assume_tac o uex2ex_rule) >>
         pop_assum (x_choose_then "g0" assume_tac) >>
         qexists_tac ‘g0’ >> rpt strip_tac (* 2 *)
         >-- (qpick_x_assum ‘q o t = a’ (assume_tac o GSYM) >> arw[] >>
             qpick_x_assum ‘g = g0 o q’ (assume_tac o GSYM) >> 
             arw[GSYM o_assoc] >> first_x_assum irule >> rw[]) >>
         qby_tac ‘?t1:1->T. q o t1 = a'’ 
         >-- (flip_tac >> irule Epi_onto_obj >>
              irule iscoEq_Epi >>
              qexistsl_tac [‘A’,‘F’,‘G’] >> arw[]) >>
         pop_assum strip_assume_tac >>
         pop_assum (assume_tac o GSYM) >> arw[] >>
         qpick_x_assum ‘g = g0 o q’ (assume_tac o GSYM) >> 
         arw[GSYM o_assoc] >>
         first_x_assum irule >> ccontra_tac >>
         fs[]) >>
     irule Disc_fac_eq >> arw[Disc_def] >>
     qby_tac
     ‘!a':1->A. q o F o a' = q o G o a'’
     >-- arw[GSYM o_assoc] >>
     strip_tac >> 
     qcases ‘q o F o a' = a’ (* 2 *)
     >-- (qby_tac ‘q o G o a' = a’ >-- rfs[] >>
         last_assum (qspecl_then [‘F o a'’] assume_tac) >>
         last_assum (qspecl_then [‘G o a'’] assume_tac) >>
         rfs[]) >>
     qby_tac ‘~(q o G o a' = a)’ >-- rfs[] >>
     first_assum (qspecl_then [‘F o a'’] assume_tac) >>
     first_assum (qspecl_then [‘G o a'’] assume_tac) >> 
     rfs[]) >>
 assume_tac
 (CC5_Disc_uex' |> qspecl [‘T’,‘2’]  
 |> fVar_sInst_th “R(t':1->T,b:1->2)”
    “(q:T->Q o t':1->T = q o t & b = 0f) |
     (~(q o t' = q o t) & b = 1f)”) >>
 rfs[Disc_def] >>
 qby_tac
 ‘!t':1-> T. 
  ?!b. (q:T->Q o t':1->T = q o t & b = 0f) |
     (~(q o t' = q o t) & b = 1f)’
 >-- (strip_tac >>
     qcases ‘q o t' = q o t’ >> arw[] (* 2 *)
     >-- (uex_tac >> qexists_tac ‘0f’ >> rw[]) >> 
     uex_tac >> qexists_tac ‘1f’ >> rw[]) >>rfs[] >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘cf’ >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rpt strip_tac (* 2 *)
 >> arw[])
(form_goal
 “!T. 
    Disc(T) ==>
    !A F:A->T G:A->T Q q:T->Q. 
      iscoEq(F,G,q) ==> Disc(Q)”));


val to_2_eq = prove_store("to_2_eq",
e0
((*rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 irule FUN_EXT >> strip_tac >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 qcases ‘f1 o a = i1(1,1)’ 
 >-- (arw[] >> flip_tac >> rw[i1_xor_i2_1] >> 
     fs[i1_xor_i2_1]) >>
 fs[i1_xor_i2'] *) cheat)
(form_goal
 “∀X f1:X->1+1 f2. f1 = f2 ⇔ 
     (∀x. f1 o x = i2(1,1) ⇔ f2 o x = i2(1,1))”));

val Thm21_isPb_char = prove_store("Thm21_isPb_char",
e0
(rpt strip_tac >>
 fs[isPb_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >> arw[GSYM o_assoc] >>
     rw[o_assoc,one_to_one_Id,IdR]) >>
 first_x_assum (qsspecl_then [‘d’,‘Id(1)’] assume_tac) >>
 rfs[IdR] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!D c:D->1+1 S i:S->D. isPb(c, i2(1, 1), i, To1(S)) ==>
  !d:1->D. (?s:1->S. i o s = d) <=> c o d = i2(1,1)”));

(*not really used?*)
val FSC_Disc_Disc = prove_store("FSC_Disc_Disc",
e0
cheat
(form_goal “!D. Disc(D) ==>
            !S i:S->D. FSC(i) ==> Disc(S)”));


val Disc_1 = prove_store("Disc_1",
e0
(cheat)
(form_goal “Disc(1)”));

(*
val i2_Mono = prove_store("i2_Mono",
e0
cheat
(form_goal “Mono(i2(1,1))”));
not really used
*)


val Thm21_char_isPb = prove_store("Thm21_char_isPb",
e0
(rpt strip_tac >>
 rw[isPb_def] >>
 qby_tac
 ‘c o i = i2(1, 1) o To1(S)’ 
 >-- (irule  Disc_fac_eq >> arw[Disc_1] >>
     strip_tac >> rw[one_to_one_Id,IdR] >>
     first_x_assum (irule o iffLR) >> qexists_tac ‘a’ >> rw[]) >>
 arw[] >>
 rpt strip_tac >> fs[one_to_one_Id,To1_def] >> 
 qsuff_tac
 ‘?a.i o a = u’
 >-- (fs[FSC_def,Mono_def] >> 
     rpt strip_tac >> uex_tac >> qexists_tac ‘a’ >> arw[] >>
     rpt strip_tac >> first_x_assum irule >> arw[]) >>
 assume_tac
 (CC5 |> qspecl [‘A’,‘S’] 
 |> fVar_sInst_th “R(f:2->A,g:2->S)”
    “i o g:2->S = u:A->D o f:2->A”) >> 
 qsuff_tac
 ‘?cf:A->S. !a:2->A b:2->S. i o b = u o a <=> cf o a = b’
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     irule $ iffLR fun_ext >> arw[o_assoc]) >>
 first_x_assum irule >> rpt strip_tac (* 4 *)
 >-- fs[id_def,dom_def,GSYM o_assoc]
 >-- fs[id_def,cod_def,GSYM o_assoc]
 >-- (*sufficient to prove existence by i is mono*)
    (qsuff_tac ‘?g:2->S. i o g = u o f’ 
    >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> arw[] >>
        rpt strip_tac >> fs[FSC_def,Mono_def] >> 
        first_x_assum irule >> arw[]) >>
    first_x_assum (qspecl_then [‘dom(u o f)’] assume_tac) >>
    fs[dom_def] >> 
    qby_tac
    ‘c o (u o f) o 0f = i2(1, 1)’
    >-- (fs[GSYM o_assoc] >> rw[o_assoc,one_to_one_Id,IdR]) >>
    fs[] >>
    qexists_tac ‘id(s)’ >> fs[Disc_def] >>
    arw[id_def,GSYM o_assoc] >>
    rw[o_assoc] >>
    first_x_assum (qspecl_then [‘u o f’] assume_tac) >>
    fs[isid_def] >> fs[GSYM o_assoc] >> 
    qby_tac
    ‘((f0 o To1(2)) o 0f) o To1(2) = 
     f0 o (To1(2) o 0f) o To1(2)’
    >-- rw[o_assoc] >> 
    arw[one_to_one_Id,IdL]) >>
 qby_tac ‘cpsb(g1,f1)’ >-- cheat >>
 drule fun_pres_oa >>
 first_x_assum (qsspecl_then [‘i’] assume_tac) >> rfs[] >>
 rev_drule fun_pres_oa >> 
 first_x_assum (qsspecl_then [‘u’] (assume_tac o GSYM)) >> fs[] >>
 fs[FSC_def,Mono_def] >> first_x_assum irule >> arw[])
(form_goal
 “!D. Disc(D) ==>
      !S i:S->D. FSC(i) ==>
  !c:D->1+1.
    (!d:1->D. (?s:1->S. i o s = d) <=> c o d = i2(1,1)) ==>
    isPb(c, i2(1, 1), i, To1(S))”));

(*val DISTI_EL = store_ax("DISTI_EL",“?X x1:1->X x2. ~(x1 = x2)”);*)
val i1_ne_i2 = prove_store("i1_ne_i2",
e0
(ccontra_tac >>
 assume_tac zf_ne_of >>
 qsuff_tac ‘0f = 1f’ >-- arw[] >>
 qby_tac ‘coPa(0f,1f) o i1(1,1) = 0f &
          coPa(0f,1f) o i2(1,1) = 1f’ >--
 rw[i12_of_coPa] >>
 pop_assum (assume_tac o GSYM) >> 
 qpick_x_assum ‘~(0f = 1f)’ (K all_tac) >> 
 once_arw[] >> pop_assum (K all_tac) >> arw[])
(form_goal
 “~(i1(1,1) = i2(1,1))”));

val Thm21 = prove_store("Thm21",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?c:D -> 1+1. isPb(c,i2(1,1),i,To1(S))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘c’ >> arw[] >>
     rpt strip_tac >> 
     irule $ iffRL to_2_eq >>
     drule (GSYM Thm21_isPb_char) >>
     rev_drule (GSYM Thm21_isPb_char) >> arw[]) >>
 drule Thm21_char_isPb >>
 first_x_assum drule >>
 qsuff_tac
 ‘?c:D->1+1.
  !d:1->D.
  (?s:1->S. i o s = d) <=> c o d = i2(1,1)’
 >-- (strip_tac >>
     first_x_assum drule >> qexists_tac ‘c’ >> arw[]) >>
 assume_tac
 (CC5_Disc_uex' |> qspecl [‘D’,‘1+1’] 
 |> fVar_sInst_th “R(d:1->D,b:1->1+1)”
    “((?s:1->S. i o s = d:1->D) & b = i2(1,1))| 
     (~(?s:1->S. i o s = d) & b = i1(1,1))”) >>
 rfs[] >>
 qby_tac
 ‘!d:1->D.
  ?!b:1-> 1+1.
  ((?s:1->S. i o s = d:1->D) & b = i2(1,1))| 
     (~(?s:1->S. i o s = d) & b = i1(1,1))’
 >-- (strip_tac >> qcases ‘?s:1->S. i o s = d:1->D’ >> arw[] (* 2 *)
     >-- (uex_tac >> qexists_tac ‘i2(1,1)’ >> rw[]) >> 
     uex_tac >> qexists_tac ‘i1(1,1)’ >> rw[]) >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘cf’ >>  
 pop_assum (assume_tac o GSYM) >> arw[] >> strip_tac >>
 qcases ‘?s:1->S. i o s = d:1->D’ >> arw[] >>
 rw[GSYM i1_ne_i2])
(form_goal
 “!S D i:S->D. Disc(D) & FSC(i) ==>
  ?!c:D -> 1+1. isPb(c,i2(1,1),i,To1(S))”));


