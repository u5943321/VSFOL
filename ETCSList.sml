(*
collect the set of all sets of of sets of (n,a) pairs such that 
{} in the set 
if l is in in the set, then for every a\in A, l ∪ (CARD l,a) is in the set

*)



val Lists_cond_ex = prove_store("Lists_cond_ex",
e0
(rpt strip_tac >> 
 qby_tac
 ‘?P0. !ls. P0 o ls = TRUE <=> IN(Empty(N * A),ls)’ >--
 (qexists_tac ‘Mem(Exp(N * A, 1 + 1)) o 
             Pa(Empty(N * A) o To1(Exp(Exp(N * A, 1 + 1), 1 + 1)),id(Exp(Exp(N * A, 1 + 1), 1 + 1)))’
 >> rw[o_assoc,Pa_distr,IN_def] >>
 once_rw[one_to_one_id] >> rw[idL,idR,True1TRUE]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘?P1. !ls. P1 o ls = TRUE <=> 
 (!l:1-> Exp(N * A,1+1). IN(l,ls) ==>
 !a. IN(Ins(Pa(CARD(l),a),l), ls))’ >-- 
 (strip_tac >>
 qexists_tac ‘And(P0,P1)’ >>
 once_rw[GSYM And_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> 
 once_rw[CONJ_def] >> arw[]) >>
 pop_assum (K all_tac) >>
 qsuff_tac
 ‘?P2. !l ls. P2 o Pa(l,ls) = TRUE <=> 
  (IN(l,ls) ==>
   !a:1->A. IN(Ins(Pa(CARD(l),a),l), ls))’ >--
 (strip_tac >> qexists_tac ‘ALL(P2)’ >>
  once_rw[GSYM ALL_def] >> once_rw[o_assoc] >>
  once_rw[All_def] >> arw[]) >>
 qby_tac
 ‘?P3. !l:1-> Exp(N * A,1+1) ls. P3 o Pa(l,ls) = TRUE <=> 
  IN(l,ls)’
 >-- (qexists_tac ‘Mem(Exp(N * A,1+1))’ >>
      rw[IN_def,True1TRUE]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘?P4. !a l:1-> Exp(N * A,1+1) ls.
 P4 o Pa(a,Pa(l,ls)) = TRUE <=> 
 IN(Ins(Pa(CARD(l),a),l), ls)’ 
 >-- (strip_tac >> 
      qexists_tac ‘Imp(P3,ALL(P4))’ >>
      once_rw[GSYM Imp_def] >> once_rw[o_assoc] >>
      once_rw[Pa_distr] >> once_rw[IMP_def] >>
      rw[ALL_property] >> arw[]) >>
 pop_assum (K all_tac) >>
 rw[IN_def,True1TRUE] >>
 qexists_tac ‘ Mem(Exp(N * A, 1 + 1)) o Pa(Ins(
 Pa
 (CARD(p32(A,Exp(N * A,1+1),Exp(Exp(N * A, 1 + 1), 1 + 1)))
 ,
 p31(A,Exp(N * A,1+1),Exp(Exp(N * A, 1 + 1), 1 + 1))
  )
  ,
 p32(A,Exp(N * A,1+1),Exp(Exp(N * A, 1 + 1), 1 + 1)))
 ,
 p33(A,Exp(N * A,1+1),Exp(Exp(N * A, 1 + 1), 1 + 1))
)
’ >>
 rw[Pa3_def,GSYM Ins_def] >> rw[Pa_distr,o_assoc] >>
 rw[p31_of_Pa3,p32_of_Pa3,p33_of_Pa3] >>
 once_rw[GSYM CARD_def] >> rw[o_assoc,Pa_distr] >>
 once_rw[p32_of_Pa3] >> rw[])
(form_goal “!A.?P. !ls.P o ls = TRUE <=>
IN(Empty(N * A),ls) &
 !l. IN(l,ls) ==>
 !a. IN(Ins(Pa(CARD(l),a),l), ls)”));

(*sets contain the set of lists as a subset*)
val cLists_def = Lists_cond_ex |>  spec_all
                               |> ex2fsym0 "cLists" ["A"]
                               |> gen_all
                               |> store_as "cLists_def";

val Lists_ex = prove_store("Lists_ex",
e0
(strip_tac >> qexists_tac ‘BIGINTER(Exp(N * A,1+1)) o 
           Tp1(cLists(A))’ >> rw[])
(form_goal
 “!A. ?la. BIGINTER(Exp(N * A,1+1)) o 
           Tp1(cLists(A)) = la”));

val Lists_def = Lists_ex |> spec_all |> ex2fsym0 "Lists" ["A"]
                           |> gen_all
                           |> store_as "Lists_def";

val isList_ex = prove_store("isList_ex",
e0
(strip_tac >> qexists_tac ‘Tp0(Lists(A))’ >> rw[])
(form_goal “!A. ?isl. Tp0(Lists(A)) = isl”));


val isList_def = isList_ex |> spec_all |> ex2fsym0 "isList" ["A"]
                           |> gen_all
                           |> store_as "isList_def";

val isList_property = prove_store("isList_property",
e0
(rpt strip_tac >> once_rw[GSYM isList_def] >>
 once_rw[GSYM Lists_def] >> 
 once_rw[GSYM Tp0_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> rw[o_assoc,idL] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 rw[BIGINTER_property] >> 
 rw[GSYM Tp1_def] >> rw[Ev_of_Tp_el',p12_of_Pa,o_assoc] >>
 rw[Ev_of_el] >> 
 once_rw[cLists_def] >> rw[IN_o] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum (qspecl_then [‘Tp1(P)’] assume_tac) >>
     fs[Tp0_Tp1_inv] >> rfs[]) >>
 last_x_assum (qsspecl_then [‘Tp0(s0)’] assume_tac) >> rfs[]
)
(form_goal
 “!A l. isList(A) o l = TRUE <=> 
  (!P.( P o Empty(N * A) = TRUE &
      (!l0. P o l0 = TRUE ==>
        !a. P o Ins(Pa(CARD(l0),a),l0) = TRUE)) ==> 
      P o l = TRUE)”));

val List_def = pred_subset_ex' 
                 |> sspecl [rastt "isList(A)"]
                 |> ex2fsym0 "List" ["A"]
                 |> ex2fsym0 "LI" ["A"]
                 |> gen_all
                 |> store_as "List_def";

val List_def1= List_def |> spec_all |> conjE2
                        |> allE ONE
                        |> rewr_rule[True1TRUE]
                        |> gen_all
                        |> store_as "List_def1";

val isList_Empty = prove_store("isList_Empty",
e0
(rw[isList_property] >> rpt strip_tac >> arw[])
(form_goal
 “!A. isList(A) o Empty(N * A) = TRUE”));

val isList_cons = prove_store("isList_cons",
e0
(rw[isList_property] >> rpt strip_tac >>
 first_x_assum (qspecl_then [‘P’] assume_tac) >> rfs[] >>
 first_x_assum irule >> arw[])
(form_goal
 “!A l. isList(A) o l = TRUE ==> 
  !a. isList(A) o Ins(Pa(CARD(l),a),l) = TRUE”));

val Nil_ex = prove_store("Nil_ex",
e0
(rw[GSYM List_def,isList_Empty,True1TRUE])
(form_goal
 “!A.?nil:1->List(A). Empty(N * A) = LI(A) o nil”));

val Nil_def = Nil_ex |> spec_all |> ex2fsym0 "Nil" ["A"]
                     |> gen_all
                     |> GSYM
                     |> store_as "Nil_def";

val Cons_rel_ex = prove_store("Cons_ex",
e0
(strip_tac >> qexists_tac 
 ‘Eq(Exp(N * A,1+1)) o Pa(
  Ins(
      Pa(
         CARD(LI(A) o p2(A,List(A)) o p1(A * List(A),List(A)))
         , 
         p1(A,List(A)) o p1(A * List(A),List(A)))
      , 
      LI(A) o p2(A,List(A)) o p1(A * List(A),List(A)))
  ,
  LI(A) o p2(A * List(A),List(A)))’ >>
 rw[o_assoc] >> rw[Pa_distr] >> rw[Eq_property_TRUE] >>
 rw[o_assoc] >> rw[p12_of_Pa] >>
 rw[GSYM Ins_def,o_assoc,p12_of_Pa,Pa_distr] >>
 rw[GSYM CARD_def,o_assoc,p12_of_Pa,Pa_distr])
(form_goal
 “!A. ?R: (A * List(A)) * List(A) -> 1+1.
 !a0 l0 l. R o Pa(Pa(a0,l0),l) = TRUE <=> 
 Ins(Pa(CARD(LI(A) o l0),a0),LI(A) o l0) = LI(A) o l ”));

val Crel_def = Cons_rel_ex |> spec_all |> ex2fsym0 "Crel" ["A"]
                           |> gen_all 
                           |> store_as "Crel_def";

val Cons_ex = prove_store("Cons_ex",
e0
(strip_tac >>
 assume_tac Rel2Ar' >>
 first_x_assum (qsspecl_then [‘Crel(A)’] assume_tac) >>
 qby_tac
 ‘!al:1-> A * List(A). ?!l. Crel(A) o Pa(al,l) = TRUE’
 >-- (strip_tac >> uex_tac >> 
      qsspecl_then [‘al’] (x_choosel_then ["a0","l0"] assume_tac)
      has_components >>
      fs[] >> rw[Crel_def] >>
      qby_tac ‘isList(A) o (LI(A) o l0) = TRUE’
      >-- (rw[List_def1] >> qexists_tac ‘l0’ >> rw[]) >>
      drule isList_cons  >>
      first_x_assum (qspecl_then [‘a0’] assume_tac) >>
      drule $ iffLR List_def1 >>
      pop_assum (x_choosel_then ["l"] assume_tac) >>
      qexists_tac ‘l’ >> arw[] >>
      rpt strip_tac >> irule $ iffLR Mono_def >>
      qexistsl_tac [‘Exp(N * A,1+1)’,‘LI(A)’] >> arw[List_def]) >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["cons"] assume_tac) >>
 qexists_tac ‘cons’ >> arw[] >> 
 rw[Crel_def])
(form_goal
 “!A. ?cons:A * List(A) ->List(A). 
  !a0:1->A l0 l:1->List(A). cons o Pa(a0,l0) = l <=> 
  Ins(Pa(CARD(LI(A) o l0),a0),LI(A) o l0) = LI(A) o l”));

val Cons_def = Cons_ex |> spec_all |> ex2fsym0 "Cons" ["A"]
                       |> gen_all
                       |> store_as "Cons_def";


val cRf_ex = prove_store("Rf_ex",
e0
(rpt strip_tac >>
 qby_tac
 ‘?P0. !ss. P0 o ss = TRUE <=> IN(Pa(Nil(A), x), ss)’
 >-- (qexists_tac 
     ‘Mem(List(A) * X) o Pa(Pa(Nil(A), x) o To1(Exp(List(A) * X,1+1)),
      id(Exp(List(A) * X,1+1)))’
      >> rw[IN_def1] >> rw[o_assoc,Pa_distr,idL] >>
      once_rw[one_to_one_id] >> rw[idR]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘?P1. !ss. P1 o ss = TRUE <=> 
  !l x. IN(Pa(l, x), ss) ==>
  !a. IN(Pa(Cons(A) o Pa(a, l), t o Pa(a, x)), ss)’ 
 (*here if forgot strip the P0, so P0 is not in context, still be able to qexists on CONJ o Pa(P0,P1), check this*)
 >-- (strip_tac >> qexists_tac ‘CONJ o Pa(P0,P1)’ >> 
      arw[o_assoc,Pa_distr,CONJ_def]) >>
 qsuff_tac
 ‘?P2. !x:1->List(A) l ss. 
  P2 o Pa(x,Pa(l,ss)) = TRUE <=>
   IN(Pa(l, x), ss) ==>
  !a:1->A. IN(Pa(Cons(A) o Pa(a, l), t o Pa(a, x)), ss)’
 >-- (strip_tac >>
      qexists_tac ‘ALL(ALL(P2))’ >>
      rw[ALL_property] >> arw[]) >>
 qby_tac
 ‘?P3. !x:1->X l:1->List(A) ss.
  P3 o Pa(x,Pa(l,ss)) = TRUE <=> IN(Pa(l,x),ss)’
 >-- (qexists_tac 
     ‘Mem(List(A) * X) o 
      Pa(Pa(p32(X,List(A),Exp(List(A) * X,1+1)),
            p31(X,List(A),Exp(List(A) * X,1+1))), p33(X,List(A),Exp(List(A) * X,1+1)))’ >>
     rw[Pa3_def,o_assoc,Pa_distr,
       p31_of_Pa3,p32_of_Pa3,p33_of_Pa3] >> rw[GSYM IN_def1]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘?P4. !a:1->A x:1->X l:1->List(A) ss. 
  P4 o Pa4(a,x,l,ss) = TRUE <=>
  IN(Pa(Cons(A) o Pa(a, l), t o Pa(a, x)), ss)’
 >-- (strip_tac >> qexists_tac ‘Imp(P3,ALL(P4))’ >>
      rw[GSYM Imp_def,o_assoc,Pa_distr,IMP_def] >>
      arw[] >>
      arw[ALL_property,Pa4_def]) >>
 qexists_tac ‘
 Mem(List(A) * X) o Pa(
Pa (CONS(p41(A,X,List(A),Exp(List(A) * X,1+1)),
    p43(A,X,List(A),Exp(List(A) * X,1+1)))
    ,
    t o Pa(p41(A,X,List(A),Exp(List(A) * X,1+1)),
           p42(A,X,List(A),Exp(List(A) * X,1+1))))
,
 p44(A,X,List(A),Exp(List(A) * X,1+1))
)’ >>
 rw[GSYM CONS_def,o_assoc,Pa_distr,
    p41_of_Pa4,p42_of_Pa4,p43_of_Pa4,p44_of_Pa4] >>
 rw[GSYM IN_def1])
(form_goal
 “!X x:1->X A t:A * X ->X.
  ?P:Exp(List(A) * X,1+1) -> 1 + 1.
  !ss. P o ss = TRUE <=> 
       IN(Pa(Nil(A), x),ss) & 
       (!l:1-> List(A) x:1->X. IN(Pa(l,x),ss) ==> 
             !a. IN(Pa(Cons(A) o Pa(a,l), t o Pa(a,x)),ss) )”));

val cRf_def = cRf_ex |> spec_all |> ex2fsym0 "cRf" ["x","t"]
                     |> qgen ‘t’ |> qgen ‘A’
                     |> gen_all 
                     |> store_as "cRf_def";

val Rf_ex = prove_store("Rf_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Tp0(BIGINTER(List(A) * X) o Tp1(cRf(x,t)))’ >> rw[])
(form_goal
 “!X x:1->X A t:A * X ->X.
  ?R.Tp0(BIGINTER(List(A) * X) o Tp1(cRf(x,t))) = R”));

val Rf_def = Rf_ex |> spec_all |> ex2fsym0 "Rf" ["x","t"]
                   |> qgen ‘t’ |> qgen ‘A’
                   |> gen_all 
                   |> store_as "Rf_def";

val CONS_ex = prove_store("CONS_ex",
e0
(rpt strip_tac >> qexists_tac ‘Cons(A) o Pa(a0,l0)’ >> rw[])
(form_goal
 “!X a0:X->A l0. ?l. Cons(A) o Pa(a0,l0) = l”));

val CONS_def = CONS_ex |> spec_all |> ex2fsym0 "CONS" ["a0","l0"]
                       |> gen_all |> store_as "CONS_def";


val isList_ind =
    isList_property |> iffLR
                    |> strip_all_and_imp
                    |> disch “isList(A) o l = TRUE”
                    |> gen_all
                    |> disch_all |> gen_all
                    |> store_as "isList_ind";

val LI_Mono = List_def |> spec_all |> conjE1
                       |> gen_all
                       |> store_as "LI_Mono";


val List_ind = prove_store("List_ind",
e0
(assume_tac isList_ind >> rpt strip_tac >>
 qby_tac
 ‘?P0:Exp(N * A,1+1) -> 1+1.
  !ss. P0 o ss = TRUE <=>
  ?l:1->List(A). ss = LI(A) o l & P o l = TRUE’
 >-- (qexists_tac 
      ‘EX(And(Eq(Exp(N * A,1+1)) o 
              Pa(p2(List(A), Exp(N * A,1+1)),
                 LI(A) o p1(List(A), Exp(N * A,1+1))) ,
              P o p1(List(A), Exp(N * A,1+1))))’ >>
      rw[EX_property] >>
      rw[GSYM And_def,o_assoc,Pa_distr,p12_of_Pa] >>
      rw[CONJ_def,Eq_property_TRUE]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac 
 ‘P0 o LI(A) o l = TRUE’ 
 >-- (arw[] >> rpt strip_tac >>
      qsuff_tac ‘l = l'’ >-- (strip_tac >> arw[]) >>
      qspecl_then [‘A’] assume_tac LI_Mono >>
      drule $ iffLR Mono_def >> first_x_assum drule >>
      arw[]) >>
 first_assum irule >> rw[List_def1] >> strip_tac (* 2 *)
 >-- (qexists_tac ‘l’ >> rw[]) >>
 arw[] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘Nil(A)’ >> arw[Nil_def]) >>
 qexists_tac ‘CONS(a,l')’ >> first_assum drule >> arw[] >>
 rw[GSYM Cons_def] >> rw[GSYM CONS_def]
 )
(form_goal
 “!A P. P o Nil(A) = TRUE & 
        (!l. P o l = TRUE ==> !a. P o CONS(a,l) = TRUE) ==>
        !l. P o l = TRUE”));


val Rf_property = prove_store("Rf_property",
e0
(once_rw[GSYM Rf_def] >> 
 once_rw[GSYM Tp0_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[o_assoc] >>
 once_rw[idL] >> once_rw[one_to_one_id] >>
 once_rw[idR] >> once_rw[BIGINTER_property] >>
 once_rw[GSYM Tp1_def] >>
 once_rw[Ev_of_Tp_el'] >> once_rw[o_assoc] >>
 once_rw[p1_of_Pa] >> once_rw[Mem_def] >> once_rw[GSYM IN_def1] >>
 once_rw[cRf_def] >> once_rw[CONS_def] >> rpt strip_tac >>
 first_assum irule >> first_assum irule >> arw[])
(form_goal
 “!X x:1->X A t:A * X ->X. Rf(x,t) o Pa(Nil(A),x) = TRUE & 
   !l x0. Rf(x,t) o Pa(l,x0) = TRUE ==> 
   !a. Rf(x,t) o Pa(CONS(a,l), t o Pa(a,x0)) = TRUE
  ”));





val Rf_min = prove_store("Rf_min",
e0
(once_rw[GSYM Rf_def] >> 
 once_rw[GSYM Tp0_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[o_assoc] >>
 once_rw[idL] >> once_rw[one_to_one_id] >>
 once_rw[idR] >> once_rw[BIGINTER_property] >>
 once_rw[GSYM Tp1_def] >>
 once_rw[Ev_of_Tp_el'] >> once_rw[o_assoc] >>
 once_rw[p1_of_Pa] >> once_rw[Mem_def] >> once_rw[GSYM IN_def1] >>
 once_rw[cRf_def]  >> rpt strip_tac >>
 first_x_assum (qsspecl_then [‘Tp1(P)’] assume_tac) >>
 fs[IN_o,Tp0_Tp1_inv] >>
 first_assum irule >> arw[CONS_def])
(form_goal
 “!X x:1->X A t:A * X ->X P. P o Pa(Nil(A),x) = TRUE & 
   (!l x0. P o Pa(l,x0) = TRUE ==> 
          !a. P o Pa(CONS(a,l), t o Pa(a,x0)) = TRUE) ==> 
   !l x0. Rf(x,t) o Pa(l,x0) = TRUE ==> P o Pa(l,x0) = TRUE
  ”));

val CONS_NOTNIL = prove_store("CONS_NOTNIL",
e0
(rpt strip_tac >> ccontra_tac >>
 fs[GSYM CONS_def,Cons_def,Nil_def] >> 
 fs[Ins_NONEMPTY])
(form_goal
 “!A a l. ~(CONS(a,l) = Nil(A))”));

val Rf_Nil_unique = prove_store("Rf_base_unique",
e0
(rpt strip_tac >> ccontra_tac >> 
 qsuff_tac ‘?P. P o Pa(Nil(A),x) = TRUE & 
   (!l x0. P o Pa(l,x0) = TRUE ==> 
    !a. P o Pa(CONS(a,l), t o Pa(a,x0)) = TRUE) & 
    ~(P o Pa(Nil(A),x0) = TRUE)’ >--
 (strip_tac >>
  qsspecl_then [‘x’,‘t’,‘P’] assume_tac Rf_min>>
  qby_tac ‘P o Pa(Nil(A), x0) = TRUE’
  >-- (first_x_assum irule>> arw[]) >>
  fs[]) >>
 qsuff_tac
 ‘?P. !l1 x1. P o Pa(l1,x1) = TRUE <=> 
  Rf(x,t) o Pa(l1,x1) = TRUE & ~(l1 = Nil(A) & x1 = x0)’
 >-- (strip_tac >> qexists_tac ‘P’ >>
      arw[] >> strip_tac (* 2 *)
      >-- (rw[Rf_property] >> dflip_tac >> arw[]) >>
      (*should not need the thing between the rpt strip ans fs. should be done by arw*)
      rpt strip_tac >> fs[] >>
      first_assum (qsspecl_then [‘l’,‘x0'’] assume_tac) >> 
      fs[] >>
      qsspecl_then [‘x’,‘t’] strip_assume_tac Rf_property >>
      last_x_assum (K all_tac) >>
      first_x_assum rev_drule >> arw[] >>
      rw[CONS_NOTNIL]) >>
 qexists_tac
 ‘And(Rf(x,t),
      Not
      (And(Eq(List(A)) o 
           Pa(p1(List(A),X),Nil(A) o To1(List(A) * X)),
           Eq(X) o 
           Pa(p2(List(A),X), x0 o To1(List(A) * X)) )))’ >>
 rw[GSYM And_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[GSYM Not_def] >> once_rw[o_assoc] >>
 once_rw[NEG_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> rw[TRUE_xor_FALSE] >> once_rw[CONJ_def] >>
 rw[o_assoc,Pa_distr] >> once_rw[one_to_one_id] >>
 rw[idR,p12_of_Pa] >> rw[Eq_property_TRUE])
(form_goal
 “!X x:1->X A t:A * X ->X x0. Rf(x,t) o Pa(Nil(A),x0) = TRUE ==> x0 = x”));


val Rf_CONS = Rf_property |> spec_all |> conjE2
                          |> gen_all
                          |> store_as "Rf_CONS";

val CONS_eq_eq = prove_store("CONS_eq_eq",
e0
(strip_tac >>
 qby_tac
 ‘?P. !a’)
(form_goal
 “!A a1:1->A l1:1->List(A) a2 l2.
  CONS(a1,l1) = CONS(a2,l2) <=> (a1 = a2 & l2 = l2) ”));


val Rf_Cons_back = prove_store("Rf_Cons_back",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 qby_tac
 ‘?P. !l0:1->List(A) x0:1->X. P o Pa(l0,x0) = TRUE <=>
  (Rf(x,t) o Pa(l0,x0) = TRUE & 
  !a:1->A l1. l0 = CONS(a,l1) ==> 
  ?x1:1->X. Rf(x,t) o Pa(l1,x1) = TRUE & x0 = t o Pa(a,x1))’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘!l0 x0.Rf(x, t) o Pa(l0, x0) = TRUE ==> P o Pa(l0,x0) = TRUE’
 >-- (rpt strip_tac >> first_x_assum drule >> rfs[] >>
      first_x_assum drule >> arw[]) >>
 match_mp_tac Rf_min >> arw[] >> 
 rw[GSYM CONS_NOTNIL] >> rpt strip_tac (* 3 *)
 >-- rw[Rf_property] 
 >-- (drule Rf_CONS >> arw[]) >>
 cases_on
 “?a2:1->A l2. l = CONS(a2,l2)”
 >-- (pop_assum strip_assume_tac >> first_x_assum drule >>
      pop_assum strip_assume_tac >>  
      qby_tac ‘l1 = l’ >-- cheat
      (*need lemma saying a:: l = a' :: l'*) >>
      qexists_tac ‘x0'’ >> arw[] >> fs[] >> 
      qby_tac ‘a = a'’ >-- cheat >> arw[]) >>
 (*need lemma saying cons xor nil,so if it is not cons, then it is nil*)
 qby_tac ‘l = Nil(A)’ >-- cheat >> fs[] >>
 qby_tac ‘l1 = l’ >-- cheat >> fs[] >>
 qexists_tac ‘x0'’ >> fs[] >>
 qby_tac ‘a = a'’ >-- cheat >> arw[] 
)
(form_goal
 “!X x:1->X A t:A * X ->X l0 x0. Rf(x,t) o Pa(l0,x0) = TRUE ==>
  Rf(x,t) o Pa(l0,x0) = TRUE & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Rf(x,t) o Pa(l1,x1) = TRUE & x0 = t o Pa(a,x1)”));

val Rf_unique = prove_store("Rf_unique",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 qby_tac
 ‘?P. !l0 x0. P o Pa(l0,x0) = TRUE <=>
 (!x'. Rf(x,t) o Pa(l0,x') = TRUE ==> x' = x0)’
 >-- cheat >> pop_assum strip_assume_tac >>
 qsuff_tac 
 ‘!l0 x0. Rf(x,t) o Pa(l0,x0) = TRUE ==> P o Pa(l0,x0) = TRUE’ 
 >-- cheat >>
 match_mp_tac Rf_min >> arw[] >> 
 strip_tac (* 2 *)
 >-- rw[Rf_Nil_unique] >> rpt strip_tac >>
 drule Rf_Cons_back >> 
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘a’,‘l’] assume_tac) >> fs[] >>
 first_x_assum drule >> arw[]                                                            
 )
(form_goal
 “!X x:1->X A t:A * X ->X l0 x0. 
  Rf(x,t) o Pa(l0,x0) = TRUE ==>
  !x'. Rf(x,t) o Pa(l0,x') = TRUE ==> x' = x0”));

val List_rec = prove_store("List_rec",
e0
()
(form_goal
 “!X x:1->X A t:A * X ->X. 
  ?!f:List(A) -> X. f o Nil(A) = x &
      f o Cons(A) = t o Pa(p1(A,List(A)), f o p2(A,List(A)))”));
