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
cheat
(form_goal
 “!f:1->2. ~(f = 0f) <=> f = 1f”));




val CC5_Disc_uex_one = prove_store("CC5_Disc_uex_one",
e0
(cheat)
(form_goal
 “∀A. Disc(A) ==> 
    !a0:1->A.
      ?!cf:A->2. ∀a:1->A. cf o a = 0f <=> a = a0”));

(*So no arrow of Q goes from any other object*)
val no_arrow_from_other = prove_store("no_arrow_from_other",
e0
(cheat)
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



