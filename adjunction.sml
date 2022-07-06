
val _ = add_parse (int_of "η");

val cpnt_def = qdefine_fsym("cpnt",
[‘η:A -> Exp(2,B)’,‘a:1->A’])
‘Pt(η o a) o Pa(Id(2),To1(2))’
|> gen_all

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



(*RT_cs2, BL_cs2 cs2_RT_cpsb*)

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



val Nt_ext = prove_store("Nt_ext",
e0
(rpt strip_tac >>
 irule $ iffLR fun_ext >>
 strip_tac >>
 irule $ iffLR Pt_eq_eq >> 
 irule cs_ext >> 
 fs[Nt_def] >> strip_tac (* 2 *)
 >-- (first_x_assum (qspecl_then [‘dom(a)’] assume_tac) >>
     rw[csT_dom] >> fs[dom_def,o_assoc]) >>
 first_x_assum (qspecl_then [‘cod(a)’] assume_tac) >>
 rw[csB_cod] >> fs[cod_def,o_assoc])
(form_goal
 “∀F1:A->B F2:A->B η1:A -> Exp(2,B) η2.
  Nt(η1,F1,F2) & Nt(η2,F1,F2) &
  (∀a:1->A. η1 o a  = η2 o a) ⇒ η1 = η2”));

val tP_def = qdefine_fsym("tP",[‘f:A * X->B’])
‘Tp(f o Swap(X,A))’

val ID_def = 
qdefine_fsym("ID",[‘F:A->B’])
‘Tp(Pt(id(Tp1(F))) o Swap(2,A))’


val ID_ap = prove_store("ID_ap",
e0
(rw[ID_def]>> rw[GSYM Tp1_def] >>
 rpt strip_tac >>
 irule Ev_eq_eq >>
 rw[Ev_of_Tp_el,o_assoc,p12_of_Pa,one_to_one_Id,IdR,
    To1_def,id_def,Pt_def,Swap_property,p12_of_Pa])
(form_goal
 “∀X A L:X->A x:1->X. 
 Tp1(id(L o x)) = ID(L) o x”));



val ID_ap_ar = prove_store("ID_ap_ar",
e0
(rw[ID_def]>> rw[GSYM Tp1_def] >>
 rpt strip_tac >>
 irule Ev_eq_eq >>
 rw[Ev_of_Tp_el,o_assoc,p12_of_Pa,one_to_one_Id,IdR,
    To1_def,id_def,Pt_def,Swap_property,p12_of_Pa] >>
 qby_tac
 ‘L o f o p1(2, 2) o Swap(2, 2) o Pa(p1(2, 2), p2(2, 2)) = L o f o (p1(2, 2) o Swap(2, 2)) o Pa(p1(2, 2), p2(2, 2))’
 >-- rw[o_assoc] >>
 arw[Swap_property,p12_of_Pa])
(form_goal
 “∀X A L:X->A f:2->X. 
 Tp(Pt(id(Tp1(L o f))) o Swap(2,2)) = ID(L) o f”));


val Ev_of_el = prove_store("Ev_of_el",
e0
(rpt strip_tac >>
 qby_tac 
 ‘f = Tp1(Tp0(f))’ >-- rw[Tp1_Tp0_inv] >> once_arw[] >>
 rw[GSYM Tp1_def,Ev_of_Tp_el'] >> rw[Tp1_def,Tp1_Tp0_inv] >>
 rw[o_assoc,p12_of_Pa,idR])
(form_goal
 “!A B f:1->Exp(A,B) a:1->A.
  Ev(A,B) o Pa(a,f) = Tp0(f) o a”));


val Ev_of_el_gen = prove_store("Ev_of_el_gen",
e0
(rpt strip_tac >>
 rw[Pt_def] >> rw[o_assoc,Pa_distr,p12_of_Pa,IdR])
(form_goal
 “!A B f:X->Exp(A,B) a:X->A.
  Ev(A,B) o Pa(a,f) = Pt(f) o Pa(a,Id(X))”));

(*,csR_csB'*)
val ID_Nt = prove_store("ID_Nt",
e0
(rw[Nt_def] >> rw[GSYM ID_ap_ar] >>
 rw[Pt_Tp] >> 
 rw[id_def,o_assoc,csL_def,csB_def,csR_def,To1_def] >>
 rpt strip_tac (* 2 *)
 >-- (rw[Pt_def,Tp1_def,Ev_of_Tp_el,o_assoc,
        GSYM Swap_def,p12_of_Pa,Pa_distr,To1_def] >>
     once_rw[Ev_of_el_gen] >> 
     rw[Pt_def] >> rw[two_def] >> rw[GSYM Tp1_def] >>
     qby_tac
     ‘(Tp(((L o f) o p1(2, 1))) o To1(2)) o p2(2, 2) = 
      Tp(((L o f) o p1(2, 1))) o (To1(2) o p2(2, 2))’
     >-- rw[o_assoc] >> arw[] >>
     rw[Ev_of_Tp_el] >>
     rw[o_assoc,p12_of_Pa,Pa_distr,IdR]) >>
 rw[Pt_def,Tp1_def,Ev_of_Tp_el,o_assoc,
        GSYM Swap_def,p12_of_Pa,Pa_distr,To1_def] >>
 once_rw[Ev_of_el_gen] >> 
 rw[Pt_def] >> rw[two_def] >> rw[GSYM Tp1_def] >>
     qby_tac
     ‘(Tp(((L o f) o p1(2, 1))) o To1(2)) o p2(2, 2) = 
      Tp(((L o f) o p1(2, 1))) o (To1(2) o p2(2, 2))’
     >-- rw[o_assoc] >> arw[] >>
     rw[Ev_of_Tp_el] >>
     rw[o_assoc,p12_of_Pa,Pa_distr,IdR])
(form_goal
 “∀X A L:X->A. Nt(ID(L), L, L)”));

val Adj_alt = prove_store("Adj_alt",
e0
(rpt strip_tac >> rw[Adj_def] >>
 strip_tac (* 2 *)
 >-- irule Nt_ext >> arw[ID_ap] >>
     qexistsl_tac [‘L’,‘L’] >> rw[ID_Nt] >>
     
     
 )
(form_goal 
 “∀L:X->A R:A->X η: X-> Exp(2,X) ε:A->Exp(2,A).
  Nt(ε, L o R,Id(A)) &
  Nt(η,Id(X),R o L) &
  (∀x:1->X. 
  vo(Lw(ε,L),Rw(L,η)) o x = Tp1(id(L o x))) & 
  (∀a:1->A.
  vo(Rw(R,ε),Lw(η,R)) o a = Tp1(id(R o a))) ⇒
  Adj(L,R,η,ε)”

vo(Lw(ε,L),Rw(L,η))  = ID(L) ∧ 
  vo(Rw(R,ε),Lw(η,R))  = ID(R)”));

val Thm13_ex = prove_store("Thm13_ex",
e0
(rpt strip_tac >>
 qby_tac
 ‘!G:A->X η:X->Exp(2,X) ε:A->Exp(2,A). 
  
   ⇒ Adj(F,G,η,ε) ∧
   ∀a:1->A. cod(cpnt(ε,a)) = a ∧ U(G o a,cpnt(ε,a))’)
(form_goal
 “∀X A F:X->A. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃!x:1->X f:2->A. cod(f) = a ∧ U(x,f)) ⇒
  ∃G:A->X η ε:A->Exp(2,A). Adj(F,G,η,ε) ∧
   ∀a:1->A. cod(cpnt(ε,a)) = a ∧ U(G o a,cpnt(ε,a))”));

