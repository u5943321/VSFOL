val p31_ex = prove_store("p31_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p31: A * B * C ->A. p1(A,B * C) = p31”));

val p31_def = p31_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p31" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all

val p32_ex = prove_store("p32_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(B,C) o p2(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p32: A * B * C ->B.p1(B,C) o p2(A,B * C) = p32”));

val p32_def = p32_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p32" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all

val p33_ex = prove_store("p33_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(B,C) o p2(A,B * C)’ >> rw[])
(form_goal
 “!A B C. ?p33: A * B * C ->C.p2(B,C) o p2(A,B * C) = p33”));

val p33_def = p33_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p33" ["A","B","C"]
                     |> C mp (trueI []) |> gen_all

                    

val Insert_ex = prove_store("Insert_ex",
e0
(strip_tac >> qexists_tac
 ‘Tp(DISJ o 
    Pa(Eq(X) o Pa(p31(X,X,Exp(X,1+1)),p32(X,X,Exp(X,1+1))),
       Ev(X,1+1) o Pa(p31(X,X,Exp(X,1+1)),p33(X,X,Exp(X,1+1)))))’
 >> rw[])
(form_goal
 “!X.?Ins: X * Exp(X,1+1) -> Exp(X,1+1). 
 Tp(DISJ o 
    Pa(Eq(X) o Pa(p31(X,X,Exp(X,1+1)),p32(X,X,Exp(X,1+1))),
       Ev(X,1+1) o Pa(p31(X,X,Exp(X,1+1)),p33(X,X,Exp(X,1+1))))) = Ins ”));


val Delete_ex = prove_store("Delete_ex",
e0
(strip_tac >> qexists_tac
 ‘Tp(CONJ o 
    Pa(NEG o Eq(X) o Pa(p31(X,X,Exp(X,1+1)),p32(X,X,Exp(X,1+1))),
       Ev(X,1+1) o Pa(p31(X,X,Exp(X,1+1)),p33(X,X,Exp(X,1+1)))))’
 >> rw[])
(form_goal
 “!X.?Del: X * Exp(X,1+1) -> Exp(X,1+1). 
 Tp(CONJ o 
    Pa(NEG o Eq(X) o Pa(p31(X,X,Exp(X,1+1)),p32(X,X,Exp(X,1+1))),
       Ev(X,1+1) o Pa(p31(X,X,Exp(X,1+1)),p33(X,X,Exp(X,1+1))))) = Del ”));


val Insert_def = 
    Insert_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Insert" ["X"]
              |> C mp (trueI []) |> gen_all



val Delete_def = 
    Delete_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Delete" ["X"]
              |> C mp (trueI []) |> gen_all


val Ins_ex = prove_store("Ins_ex",
e0
(rpt strip_tac >> qexists_tac ‘Insert(X) o Pa(x,s0)’ >> rw[])
(form_goal
“!A X x:A->X s0:A->Exp(X,1+1).?f. Insert(X) o Pa(x,s0) = f”));


val Del_ex = prove_store("Del_ex",
e0
(rpt strip_tac >> qexists_tac ‘Delete(X) o Pa(x,s0)’ >> rw[])
(form_goal
“!A X x:A->X s0:A->Exp(X,1+1).?f. Delete(X) o Pa(x,s0) = f”));



val Ins_def = 
    Ins_ex |> spec_all |> eqT_intro
           |> iffRL |> ex2fsym "Ins" ["x","s0"]
           |> C mp (trueI []) |> gen_all


val Del_def = 
    Del_ex |> spec_all |> eqT_intro
           |> iffRL |> ex2fsym "Del" ["x","s0"]
           |> C mp (trueI []) |> gen_all




val p31_of_Pa = prove_store("p31_of_Pa",
                            e0
                                (rpt strip_tac >> rw[GSYM p31_def,p1_of_Pa] )
                                (form_goal
                                     “!A B C X a:X-> A bc: X-> B * C. p31(A,B,C) o Pa(a, bc) = a”));


val p32_of_Pa = prove_store("p32_of_Pa",
e0
(rpt strip_tac >> rw[GSYM p32_def,o_assoc,p12_of_Pa] )
(form_goal
“!A B C X a:X-> A b: X-> B c: X-> C. p32(A,B,C) o Pa(a, Pa(b,c)) = b”));


val p33_of_Pa = prove_store("p33_of_Pa",
e0
(rpt strip_tac >> rw[GSYM p33_def,o_assoc,p2_of_Pa] )
(form_goal
“!A B C X a:X-> A b: X-> B c: X-> C. p33(A,B,C) o Pa(a, Pa(b,c)) = c”));

val Ins_property = prove_store("Ins_property",
e0
(rpt strip_tac >> rw[GSYM Ins_def,GSYM Insert_def,Ev_of_Tp] >> 
 rw[Ev_of_Tp_el,Pa_distr,o_assoc,DISJ_def,p31_def] >> rw[p31_of_Pa,p32_of_Pa] >> 
(qspecl_then [‘X’,‘1’,‘x’,‘x0’] mp_tac) $ GSYM Eq_property >> once_rw[True1TRUE] >> 
 strip_tac >> arw[] >> rw[p33_of_Pa]
)
(form_goal
 “!X x0:1->X s0:1->Exp(X,1+1).
  !x:1->X. Ev(X,1+1) o Pa(x,Ins(x0,s0)) = TRUE <=> 
  (x = x0 | Ev(X,1+1) o Pa(x,s0) = TRUE)”));



val Del_property = prove_store("Del_property",
e0
(rpt strip_tac >> rw[GSYM Del_def,GSYM Delete_def,Ev_of_Tp] >> 
 rw[Ev_of_Tp_el,Pa_distr,o_assoc,CONJ_def,p31_def,NEG_def] >> rw[p31_of_Pa,p32_of_Pa,p33_of_Pa,TRUE_xor_FALSE,Eq_property_TRUE] >> 
 dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X x0:1->X s0:1->Exp(X,1+1).
  !x:1->X. Ev(X,1+1) o Pa(x,Del(x0,s0)) = TRUE <=> 
  (Ev(X,1+1) o Pa(x,s0) = TRUE & ~(x = x0))”));




val Pa3_ex = prove_store("Pa3_ex",
e0
(rpt strip_tac >> qexists_tac ‘Pa(f,Pa(g,h))’ >> rw[])
(form_goal
 “!A B C X f:X->A g:X ->B h:X->C. ?Pa3.
 Pa(f,Pa(g,h)) = Pa3 
”));


val Pa3_def = Pa3_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa3" ["f","g","h"]
              |> C mp (trueI []) |> gen_all

val Pa4_ex = prove_store("Pa4_ex",
e0
(rpt strip_tac >> qexists_tac ‘Pa(f,Pa(g,Pa(h,j)))’ >> rw[])
(form_goal
 “!A B C D X f:X->A g:X ->B h:X->C j:X->D. ?Pa4.
 Pa(f,Pa(g,Pa(h,j))) = Pa4
”));

val Pa4_def = Pa4_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa4" ["f","g","h","j"]
              |> C mp (trueI []) |> gen_all

val p41_ex = prove_store("p41_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A, B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p41. p1(A,B * C * D) = p41”));

val p41_def = p41_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p41" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val p42_ex = prove_store("p42_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p42. p1(B, C * D) o p2(A,B * C * D) = p42”));


val p42_def = p42_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p42" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p43_ex = prove_store("p43_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p43. p1(C,D) o p2(B, C * D) o p2(A,B * C * D) = p43”));


val p43_def = p43_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p43" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p44_ex = prove_store("p44_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p44. p2(C,D) o p2(B, C * D) o p2(A,B * C * D) = p44”));


val p44_def = p44_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "p44" ["A","B","C","D"]
                     |> C mp (trueI []) |> gen_all

fun mk_o a1 a2 = mk_fun "o" [a1,a2]

val CONJ = mk_fun "CONJ" []

fun Pa f g = mk_fun "Pa" [f,g]

fun Ex X = mk_fun "Ex" [X]

fun Tp f = mk_fun "Tp" [f]



val Empty_ex = prove_store("Empty_ex",
e0
(strip_tac >> qexists_tac ‘Tp(False(X) o p1(X,1))’ >> rw[])
(form_goal
“!X.?ept:1->Exp(X,1+1). Tp(False(X) o p1(X,1))= ept”));


val Empty_def = 
    Empty_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Empty" ["X"]
             |> C mp (trueI []) |> gen_all

val Mem_ex = prove_store("Mem_ex",
e0
(strip_tac >> qexists_tac ‘Ev(X,1+1)’ >> rw[])
(form_goal
 “!X. ?mem. Ev(X,1+1) = mem”));

val Mem_def = Mem_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Mem" ["X"]
             |> C mp (trueI []) |> gen_all



val contain_empty = 
mk_o (rastt "Mem(Exp(X,1+1))") $
Pa
(rastt "Empty(X) o To1(Exp(Exp(X,1+1),1+1))")
(rastt "id(Exp(Exp(X,1+1),1+1))")


val longpred_ant = rastt "Ev(Exp(X,1+1),1+1)"

val longpred_conc = 
rastt $ q2str
‘All(X) o Tp(Ev(Exp(X,1+1),1+1) o 
             Pa(Ins(p31(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1)),
                    p32(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1))),
                p33(X,Exp(X,1+1),Exp(Exp(X,1+1),1+1))))’

val IMP = mk_fun "IMP" []

val longpred0 = 
mk_o (rastt "All(Exp(X,1+1))") $ Tp (mk_o IMP (Pa longpred_ant longpred_conc))

val longpred = 
mk_o CONJ (Pa contain_empty longpred0)

val bigset = Tp1 longpred





val BIGINTER_ex = prove_store("BIGINTER_ex",
e0
(*?(biX : Exp(Exp(X#, 2), 2) -> Exp(X#, 2))*)
(strip_tac >> qexists_tac ‘Tp (All(Exp(X,1+1)) o Tp(IMP o Pa
 (Ev(Exp(X,1+1),1+1) o 
  Pa(p31(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1)),
     p33(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1))),
  Ev(X,1+1) o 
  Pa(p32(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1)),
     p31(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1))))  ))’ >> rw[])
(form_goal
“!X.?biX.
 Tp (All(Exp(X,1+1)) o Tp(IMP o Pa
 (Ev(Exp(X,1+1),1+1) o 
  Pa(p31(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1)),
     p33(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1))),
  Ev(X,1+1) o 
  Pa(p32(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1)),
     p31(Exp(X,1+1),X,Exp(Exp(X,1+1),1+1))))  )) = biX ”));


val BIGINTER_def = 
BIGINTER_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "BIGINTER" ["X"] 
            |> C mp (trueI []) |> gen_all

val BIGINTER_property = prove_store("BIGINTER_property",
e0
(rpt strip_tac >> rw[GSYM BIGINTER_def] >>
 rw[Ev_of_Tp_el] >> rw[o_assoc,All_def] >> 
 rw[Pa_distr,IMP_def] >>
 rw[o_assoc,Pa_distr,p33_of_Pa,p31_of_Pa,p32_of_Pa])
(form_goal
 “!X ss:1->Exp(Exp(X,1+1),1+1) x:1->X.
  Ev(X,1+1) o Pa(x,BIGINTER(X) o ss) = TRUE <=> 
  !s0:1-> Exp(X,1+1). Ev(Exp(X,1+1),1+1) o Pa(s0,ss) = TRUE ==>
   Ev(X,1+1) o Pa(x,s0) = TRUE”));



val finites = 
mk_o (rastt "BIGINTER(Exp(X,1+1))") bigset

val isFinite_subset = 
mk_o (mk_o (rastt "Ev(Exp(X,1+1),1+1)") 
(Pa (rastt "p1(Exp(X,1+1),1)") (mk_o finites (rastt "p2(Exp(X,1+1),1)")))) (rastt "Pa(id(Exp(X,1+1)),To1(Exp(X,1+1)))")


val two = rastt "1+1";

val isFinite_ex = prove_store("isFinite_ex",
e0
(strip_tac >> 
 exists_tac isFinite_subset >> rw[])
(form_goal $
mk_forall "X" ob_sort
 (mk_exists "f" (ar_sort (Exp (mk_ob "X") two) two)
  (mk_eq isFinite_subset (rastt "f:Exp(X,1+1) -> 1+1")))
));

val isFinite_def = 
isFinite_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "isFinite" ["X"] 
            |> C mp (trueI []) |> gen_all;



val p31_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p31_def,p1_of_Pa])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p31(A,B,C) o Pa3(f,g,h) = f”)



val p32_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p32_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p32(A,B,C) o Pa3(f,g,h) = g”)


val p33_of_Pa3 = prove_store("p33_of_Pa3",
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM p33_def,p2_of_Pa,o_assoc])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. p33(A,B,C) o Pa3(f,g,h) = h”));

val isFinite_property = prove_store("isFinite_property",
e0
(rpt strip_tac >> rw[GSYM isFinite_def] >>
rw[o_assoc,Pa_distr,idL,p1_of_Pa] >>
rw[BIGINTER_property] >> 
rw[p2_of_Pa] >> rw[GSYM Tp1_def] >>
rw[Ev_of_Tp_el] >> rw[o_assoc,CONJ_def,Pa_distr] >>
rw[p1_of_Pa,idL] >> rw[All_def] >>
rw[o_assoc,Pa_distr] >> rw[IMP_def] >>
rw[All_def] >> rw[o_assoc,Pa_distr] >>
rw[Pa3_def] >> rw[p32_of_Pa3,p33_of_Pa3] >>
rw[GSYM Ins_def] >> rw[Pa_distr,o_assoc] >>
rw[p31_of_Pa3,p32_of_Pa3] >>
rw[GSYM Mem_def] >> once_rw[one_to_one_id] >> rw[idR]
)
(form_goal
“!X a:1->Exp(X,1+1). isFinite(X) o a = TRUE <=>
!P: 1-> Exp(Exp(X,1+1),1+1). 
 Ev(Exp(X,1+1),1+1) o Pa(Empty(X),P) = TRUE &
 (!s0:1-> Exp(X,1+1). Ev(Exp(X,1+1),1+1) o Pa(s0,P) = TRUE ==>
   !e:1->X.Ev(Exp(X,1+1),1+1) o Pa(Ins(e,s0),P) = TRUE) ==>
 Ev(Exp(X,1+1),1+1) o Pa(a,P) = TRUE
 ”));



val Ev_of_Tp_el' = prove_store("Ev_of_Tp_el'",
e0
(rpt strip_tac >> 
 qby_tac ‘Tp(f) = Tp(f) o id(P)’ >-- rw[idR] >>
 once_arw[] >> rw[Ev_of_Tp_el])
(form_goal
“!A B P f:A * P -> B  a:P -> A.
Ev(A, B) o Pa(a, Tp(f)) = f o Pa(a, id(P))”));


val Ev_of_el = prove_store("Ev_of_el",
e0
(rpt strip_tac >>
 qby_tac 
 ‘f = Tp1(Tp0(f))’ >-- rw[Tp1_Tp0_inv] >> once_arw[] >>
 rw[GSYM Tp1_def,Ev_of_Tp_el'] >> rw[Tp1_def,Tp1_Tp0_inv] >>
 rw[o_assoc,p1_of_Pa,idR])
(form_goal
 “!A B f:1->Exp(A,B) a:1->A.
  Ev(A,B) o Pa(a,f) = Tp0(f) o a”));


val isFinite_property1 =prove_store("isFinite_property1",
e0
(rw[isFinite_property] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (first_x_assum (qspecl_then [‘Tp1(P)’] assume_tac) >>
  fs[GSYM Tp1_def,Ev_of_Tp_el',o_assoc,p1_of_Pa] >>
  first_x_assum irule >> arw[]) >>
 rw[Ev_of_el] >> first_x_assum irule >>
 fs[Ev_of_el]
 )
(form_goal 
 “!X a:1->Exp(X,1+1). isFinite(X) o a = TRUE <=> !P:Exp(X,1+1) ->1+1.
 P o Empty(X) = TRUE &
 (!s0:1-> Exp(X,1+1). 
  P o s0 = TRUE ==> !e:1->X.P o Ins(e,s0) = TRUE) ==>
 P o a = TRUE
 ”));

fun Po A B = mk_fun "*" [A,B]

val FINITE_def = new_ax 
“!X. FINITE(X) <=> isFinite(X) o Tp1(True(X)) =TRUE”


val isFinite_Empty = prove_store("isFinite_Empty",
e0
(strip_tac >> rw[isFinite_property1] >> rpt strip_tac)
(form_goal
 “!X. isFinite(X) o Empty(X) = TRUE”));


val isFinite_Insert = prove_store("isFinite_Insert",
e0
(rw[isFinite_property1] >> rpt strip_tac >>
 qsuff_tac 
 ‘All(X) o Tp(P o Insert(X)) o a = TRUE’ >--
 (rw[All_def,o_assoc,Ins_def] >> strip_tac >> arw[]) >>
 rw[GSYM o_assoc] >> first_x_assum irule >>
 strip_tac >-- 
 (rw[All_def,o_assoc,Ins_def] >> strip_tac >> strip_tac >>
  strip_tac >> first_x_assum irule >> arw[]) >>
 rw[All_def,o_assoc,Ins_def] >> first_x_assum irule >> arw[]
 )
(form_goal
 “!X a:1-> Exp(X,1+1). isFinite(X) o a = TRUE ==>
  !x:1->X. isFinite(X) o Ins(x,a) = TRUE”));




val p41_ex = prove_store("p41_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A, B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p41. p1(A,B * C * D) = p41”));

val p41_def = p41_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p41" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val p42_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac ‘p1(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p42. p1(B, C * D) o p2(A,B * C * D) = p42”)


val p42_def = p42_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p42" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p43_ex = prove_store("p43_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p43. p1(C,D) o p2(B, C * D) o p2(A,B * C * D) = p43”));


val p43_def = p43_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p43" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val p44_ex = prove_store("p44_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(C,D) o p2(B, C * D) o p2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?p44. p2(C,D) o p2(B, C * D) o p2(A,B * C * D) = p44”));


val p44_def = p44_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "p44" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all





val p41_of_Pa4 = prove_store("p41_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p41_def,p12_of_Pa])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p41(A,B,C,D) o Pa4(f,g,h,k) = f”));

val p42_of_Pa4 = prove_store("p42_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p42_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p42(A,B,C,D) o Pa4(f,g,h,k) = g”));


val p43_of_Pa4 = prove_store("p43_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p43_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p43(A,B,C,D) o Pa4(f,g,h,k) = h”));


val p44_of_Pa4 = prove_store("p44_of_Pa4",
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM p44_def,p12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 p44(A,B,C,D) o Pa4(f,g,h,k) = k”));


val Tp0_INJ = prove_store("Tp0_INJ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >-- 
 (once_rw[GSYM Tp1_Tp0_inv] >> arw[]) >> arw[])
(form_goal
 “!A B f:1->Exp(A,B) g:1->Exp(A,B).
  Tp0(f) = Tp0(g) <=> f = g”));

val pred_ext = prove_store("pred_ext",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (cases_on “p1:1->1+1 = TRUE” >-- fs[] >>
 fs[TRUE2FALSE] >> fs[TRUE_ne_FALSE] >>
 fs[TRUE2FALSE]) >>
 arw[])
(form_goal
“!p1 p2. (p1 = TRUE <=> p2 = TRUE) <=> p1 = p2”));


val ABSORPTION_RWT = prove_store("ABSORPTION_RWT",
e0
(rpt strip_tac >> rw[GSYM Mem_def] >>
 once_rw[GSYM Tp0_INJ] >> dimp_tac >> strip_tac (* 2 *) >-- 
 (irule FUN_EXT >> strip_tac >> 
 rw[GSYM Tp0_def,o_assoc,Pa_distr,idL] >> 
 once_rw[one_to_one_id] >> rw[idR] >>
 once_rw[GSYM pred_ext] >> rw[Ins_property] >>
 dimp_tac >> strip_tac (* 2 *) 
 >-- fs[] >> arw[]) >>
 pop_assum mp_tac >>  
 rw[GSYM Tp0_def,o_assoc,Pa_distr,idL] >> 
 once_rw[GSYM FUN_EXT_iff] >> once_rw[one_to_one_id] >>
 rw[idR] >> once_rw[GSYM pred_ext] >> rw[] >>
 rw[Pa_distr,o_assoc] >> once_rw[one_to_one_id] >>
 rw[idL,idR] >> rw[Ins_property] >> rpt strip_tac >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 fs[])
(form_goal
“!X x:1->X s0:1->Exp(X,1+1). (Mem(X) o Pa(x,s0) = TRUE) <=>
 Ins(x,s0) = s0”));


val NOT_IN_Empty = prove_store("NOT_IN_Empty",
e0
(rpt strip_tac >> rw[GSYM Mem_def,GSYM Empty_def,Ev_of_Tp_el',o_assoc] >> once_rw[one_to_one_id] >> rw[idR,False2FALSE]>>
 rw[TRUE2FALSE])
(form_goal
“!X x:1->X. ~(Mem(X) o Pa(x,Empty(X)) = TRUE)”));


val _ = new_pred "IN" [("a",ar_sort (mk_ob "X") (mk_ob "A")),
                       ("as",ar_sort (mk_ob "X") (Exp (mk_ob "A") two))]

val IN_def = store_ax("IN_def",
“!X A a:X->A ss:X->Exp(A,1+1). 
 IN(a,ss) <=> Mem(A) o Pa(a,ss) = True(X)”);

val IN_def1 = prove_store("IN_def1",
e0
(rw[True1TRUE,IN_def])
(form_goal “!A a:1->A ss:1->Exp(A,1+1). 
 IN(a,ss) <=> Mem(A) o Pa(a,ss) = TRUE”));

val NOTIN_Empty = prove_store("NOTIN_Empty",
e0
(assume_tac NOT_IN_Empty >> fs[GSYM IN_def1])
(form_goal “!X x. ~IN(x,Empty(X))”));

val IN_Ins = prove_store("IN_Ins",
e0
(assume_tac Ins_property >> fs[GSYM IN_def1,Mem_def] )
(form_goal “!X x:1->X x0 xs0. IN(x,Ins(x0,xs0)) <=> x = x0 | IN(x,xs0)”));


val IN_Del = prove_store("IN_Ins",
e0
(assume_tac Del_property >> fs[GSYM IN_def1,Mem_def] )
(form_goal “!X x:1->X x0 xs0. IN(x,Del(x0,xs0)) <=> IN(x,xs0) & ~(x = x0)”));

val Ins_absorb = prove_store("Ins_absorb",
e0
(assume_tac ABSORPTION_RWT  >> fs[IN_def,True1TRUE])
(form_goal “!X x:1->X s0.IN(x,s0) <=> Ins(x,s0) = s0”));


val IN_EXT = prove_store("IN_EXT",
e0
(rw[IN_def,GSYM Mem_def] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac >> arw[] >> irule Ev_eq_eq >> 
 fs[True1TRUE,pred_ext] >> irule FUN_EXT >>
 rpt strip_tac >> rw[Pa_distr,o_assoc] >>
 once_rw[one_to_one_id] >> rw[idR] >> arw[])
(form_goal “!X s1:1-> Exp(X,1+1) s2.
 s1 = s2 <=> (!x.IN(x,s1) <=> IN(x,s2))”));
 
val Del_Ins = prove_store("Del_Ins",
e0
(rpt strip_tac >> rw[IN_EXT,IN_Del,IN_Ins] >>
 strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 ccontra_tac >> fs[])
(form_goal “!X x0:1->X xs0. (~IN(x0,xs0)) ==> Del(x0,Ins(x0,xs0)) =xs0”));


val Ins_NONEMPTY = prove_store("Ins_NONEMPTY",
e0
(rw[IN_EXT,IN_Ins,NOTIN_Empty] >> rpt strip_tac >> 
ccontra_tac >>
 first_x_assum (qspecl_then [‘x0’] assume_tac) >> fs[])
(form_goal
 “!X x0:1->X xs.~(Ins(x0,xs) = Empty(X))”));

val IN_Ins_SND = prove_store("IN_Ins_SND",
e0
(rw[IN_Ins] >> rpt strip_tac)
(form_goal “!X x0:1->X xs0 x. IN(x, Ins(x0, xs0)) & (~(x = x0)) ==> IN(x,xs0)”)); 

val Del_Ins_SWAP = prove_store("Del_Ins_SWAP",
e0
(rpt strip_tac >> rw[IN_EXT,IN_Ins,IN_Del] >> 
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X x0 x:1->X.(~(x0 = x)) ==> !xs.Del(x,Ins(x0, xs)) = Ins(x0,Del(x,xs))”));

fun Pow A = Exp A two


val contain_empty_O = 
mk_o (rastt "Mem(Exp(X,1+1) * N)") $
Pa
(rastt "Pa(Empty(X),O) o To1(Exp(Exp(X,1+1) * N,1+1))")
(rastt "id(Exp(Exp(X,1+1) * N,1+1))")

val longp_ant = rastt "Ev(Exp(X,1+1) * N,1+1)";


val notin_pred = 
rastt $ q2str 
‘NEG o Mem(X) o 
       Pa(p31(X,
              Exp(X,1+1) * N,
              Exp(Exp(X,1+1) * N,1+1)),
          p1(Exp(X,1+1), N) o 
          p32(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1)))’

val notin_conc_pred = 
rastt $ q2str
‘Mem(Exp(X,1+1) * N) o 
      Pa(Pa(Ins(p31(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1)),
             p1(Exp(X,1+1), N) o
             p32(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1))),
            SUC o 
            p2(Exp(X,1+1), N) o
            p32(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1))),
         p33(X,Exp(X,1+1) * N,Exp(Exp(X,1+1) * N,1+1)))’

val imp_pred = mk_o IMP (Pa notin_pred notin_conc_pred)

val longp_conc = mk_o (rastt "All(X)") (Tp imp_pred)

val longp0 = 
mk_o (rastt "All(Exp(X,1+1) * N)") $ Tp (mk_o IMP (Pa longp_ant longp_conc))

val longp = 
mk_o CONJ (Pa contain_empty_O longp0)

val sets_contain_pair = Tp1 longp

val hasCard = mk_o (rastt "BIGINTER(Exp(X,1+1) * N)") sets_contain_pair

fun Tp0 f = mk_fun "Tp0" [f]

val hasCard_ar = Tp0 hasCard

val hasCard_ex = prove_store("hasCard_ex",
e0
(strip_tac >> 
 exists_tac hasCard_ar >> rw[])
(form_goal $
mk_forall "X" ob_sort
 (mk_exists "f" (ar_sort (Po (Exp (mk_ob "X") two) N) two)
  (mk_eq hasCard_ar (rastt "f:Exp(X,1+1) * N -> 1+1")))
));

val hasCard_def = 
hasCard_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "hasCard" ["X"] 
            |> C mp (trueI []) |> gen_all;

val hasCard_property = prove_store("hasCard_property",
e0
(rpt strip_tac >> rw[GSYM hasCard_def] >>
 rw[GSYM Tp0_def] >>
 rw[o_assoc,Pa_distr,idL,p1_of_Pa] >>
 once_rw[one_to_one_id] >> rw[idR,idL] >>
 once_rw[GSYM p31_def] >> 
once_rw [GSYM p32_def] >> 
 once_rw[GSYM p33_def] >>
 rw[o_assoc,Pa_distr,p12_of_Pa] >>
 rw[GSYM p31_def,GSYM p32_def,GSYM p33_def] >>
 once_rw[BIGINTER_property] >> once_rw[GSYM Tp1_def] >>
 once_rw[Ev_of_Tp_el'] >> 
 rw[o_assoc] >> rw[p12_of_Pa] >>
 once_rw[Pa_distr] >> once_rw[CONJ_def]>>
 rw[Pa_distr,o_assoc] >> rw[idL,idR] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 once_rw[All_def] >> rw[o_assoc,Pa_distr] >>
 once_rw[IMP_def] >> once_rw[All_def] >>
 rw[o_assoc,Pa_distr] >>
 once_rw[IMP_def] >>
 rw[o_assoc] >> rw[p12_of_Pa] >>
 once_rw[NEG_def] >>
 once_rw[TRUE_xor_FALSE] >>
 once_rw[Pa_distr] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >>
 once_rw[GSYM Ins_def] >> 
 rw[o_assoc] >> rw[Pa_distr] >> rw[p12_of_Pa] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum irule >> once_rw[GSYM Mem_def] >>
     once_arw[] >> rw[] >> strip_tac >>
     qby_tac ‘?s n. x = Pa(s,n)’ >-- 
     (qexistsl_tac [‘p1(Exp(X,1+1),N) o x’,
                    ‘p2(Exp(X,1+1),N) o x’] >>
     rw[GSYM to_P_component]) >>
     pop_assum strip_assume_tac >>
     once_arw[] >> rw[p12_of_Pa,o_assoc,Pa_distr] >>
     rpt strip_tac >> first_x_assum drule >>
     first_x_assum irule >> 
     rw[IN_def,GSYM Mem_def,True1TRUE] >>
     first_x_assum accept_tac) >>
 last_x_assum (qspecl_then [‘s0’] assume_tac) >> 
 first_x_assum irule >> fs[GSYM Mem_def] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘Pa(s0',n0)’] assume_tac) >>
 pop_assum mp_tac >> rw[p12_of_Pa,o_assoc,Pa_distr] >> 
 rpt strip_tac >> first_x_assum irule >> arw[] >>
 fs[IN_def,GSYM Mem_def,True1TRUE]
)
(form_goal
 “!X xs:1->Exp(X,1+1) n. hasCard(X) o Pa(xs,n) = TRUE <=>
 !P:1 -> Exp(Exp(X,1+1) * N,1+1).
  Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(Empty(X),O),P) = TRUE & 
  (!s0:1-> Exp(X,1+1) n0:1-> N. Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(s0,n0),P) = TRUE ==>
  !e:1->X.~(IN(e,s0)) ==>
    Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(Ins(e,s0),SUC o n0),P) = TRUE) ==> 
  Ev(Exp(X,1+1) * N,1+1) o Pa(Pa(xs,n),P) = TRUE”));



