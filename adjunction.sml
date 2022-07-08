
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

val cs_of_vo_0f = prove_store("cs_of_vo_0f",
e0
(rpt strip_tac >> drule irt_def >>
pop_assum strip_assume_tac >>  
rw[vo_def] >> 
qby_tac
‘Ed(0f, B) o Ed(γ, B) = Ed(0f, B) o Ed(α, B)’
>-- cheat >>
arw[GSYM o_assoc] >> rw[o_assoc] >>
qby_tac
‘Ed(0f, B) o Ed(α, B) o irt(η, ε) o f = 
Ed(0f, B) o (Ed(α, B) o irt(η, ε)) o f’ 
>-- rw[o_assoc] >>
arw[])
(form_goal
“∀η:A -> Exp(2,B) ε:A -> Exp(2,B).
 Ed(1f,B) o η = Ed(0f,B) o ε ⇒
 ∀f:2->A. Ed(0f, B) o vo(ε,η) o f = 
          Ed(0f, B) o η o f”));

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

val Ed_1f_gamma = prove_store("Ed_1f_gamma",
e0
(rw[GSYM Ed_o] >> irule Ed_eq >> rw[CC4_1])
(form_goal
 “Ed(1f, B) o Ed(γ, B) = Ed(1f, B) o Ed(β, B)”));

val cs_of_vo_1f = prove_store("cs_of_vo_1f",
e0
(rpt strip_tac >> drule irt_def >>
pop_assum strip_assume_tac >>  
rw[vo_def] >> 
qby_tac
‘Ed(1f, B) o Ed(γ, B) = Ed(1f, B) o Ed(β, B)’
>-- cheat >>
arw[GSYM o_assoc] >> rw[o_assoc] >>
qby_tac
‘Ed(1f, B) o Ed(β, B) o irt(η, ε) o f = 
Ed(1f, B) o (Ed(β, B) o irt(η, ε)) o f’ 
>-- rw[o_assoc] >>
arw[])
(form_goal
“∀η:A -> Exp(2,B) ε:A -> Exp(2,B).
 Ed(1f,B) o η = Ed(0f,B) o ε ⇒
 ∀f:2->A. Ed(1f, B) o vo(ε,η) o f = 
          Ed(1f, B) o ε o f”));


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


val Er1_eq_eq = prove_store("Er1_eq_eq",
e0
cheat
(form_goal “∀A B f1 f2:A-> Exp(1,B). 
Er1(B) o f1 = Er1(B) o f2 ⇔ f1 = f2”));

val vo_Nt_Nt = prove_store("vo_Nt_Nt",
e0
(rpt strip_tac >> 
 fs[Nt_def] >> strip_tac >>
 qsspecl_then [‘η1’,‘η2’] assume_tac cs_of_vo_0f >>
 qsspecl_then [‘η1’,‘η2’] assume_tac cs_of_vo_1f >>
 qby_tac
 ‘Ed(1f, B) o η1 = Ed(0f, B) o η2’
 >-- (irule $ iffLR fun_ext >>
     strip_tac >> irule $ iffLR Er1_eq_eq >>
     arw[o_assoc,GSYM csR_Pt_Ed,GSYM csL_Pt_Ed])>>
 qby_tac
 ‘Ed(1f, B) o η1 = Ed(0f, B) o η2’
 >-- (irule $ iffLR fun_ext >>
     strip_tac >> irule $ iffLR Er1_eq_eq >>
     arw[o_assoc,GSYM csR_Pt_Ed,GSYM csL_Pt_Ed]) >>
 first_x_assum drule >>
 first_x_assum drule >>
 (*fs[GSYM o_assoc,fun_ext] >> *)
 arw[csL_Pt_Ed,csR_Pt_Ed] >> 
 rw[GSYM csL_Pt_Ed,GSYM csR_Pt_Ed] >> arw[])
(form_goal
 “∀A B F1:A->B F2:A->B F3:A->B 
  η1:A -> Exp(2,B) η2:A -> Exp(2,B).
  Nt(η1,F1,F2) & Nt(η2,F2,F3) ⇒
  Nt(vo(η2,η1),F1,F3)”));

val Nt_Lw_Nt = prove_store("Nt_Lw_Nt",
e0
(rw[Nt_def] >> rpt gen_tac >> strip_tac >>
 rpt gen_tac >>
 arw[Lw_def,o_assoc])
(form_goal 
 “∀A B F1 F2:A->B η.
  Nt(η,F1,F2) ⇒
  ∀C F3:C->A. Nt(Lw(η,F3),F1 o F3,F2 o F3)”));

(*
val csL_Pt_o = prove_store("csL_Pt_o",
e0
()
(form_goal
 “csL(Pt(Ec(F, X) o f)) = ”));
*)

val Er1_Ed_Tp = prove_store("Er1_Ed_Tp",
e0
(rw[Ed_def,Er1_def,Pa_distr,IdR,o_assoc,To1_def,IdL] >>
rw[Ev_of_Tp_el] >> 
rw[o_assoc,Pa_distr,To1_def,p12_of_Pa]  >>
rw[Ev_of_Tp_el'] >>
rw[o_assoc,Pa_distr,To1_def,IdR,IdL,p12_of_Pa])
(form_goal 
 “Er1(C) o Ed(f, C) o Tp((F o Ev(X, B))) = 
  F o Er1(B) o Ed(f, B)”));

(*
rw[Ed_def,Er1_def,Pa_distr,IdR,o_assoc,To1_def,IdL] >>
rw[Ev_of_Tp_el] >> 
rw[o_assoc,Pa_distr,To1_def,p12_of_Pa]  >>
rw[Ev_of_Tp_el'] >>
rw[o_assoc,Pa_distr,To1_def,IdR,IdL,p12_of_Pa]
“ Er1(C) o Ed(0f, C) o Tp((F3 o Ev(2, B))) = 
  F3 o Er1(B) o Ed(0f, B)”
*)

val Nt_Rw_Nt = prove_store("Nt_Rw_Nt",
e0
(rw[Nt_def] >> rpt gen_tac >> strip_tac >>
 rpt gen_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[csL_Pt,csR_Pt] >> arw[o_assoc] >>
 rw[csL_Pt,csR_Pt] >> rw[Rw_def,Ec_def] >>
 rw[o_assoc] >>
 qsuff_tac
 ‘(Er1(C) o Ed(0f, C) o Tp((F3 o Ev(2, B)))) o η o f = 
  (F3 o Er1(B) o Ed(0f, B)) o η o f &
  (Er1(C) o Ed(1f, C) o Tp((F3 o Ev(2, B)))) o η o f = 
  (F3 o Er1(B) o Ed(1f, B)) o η o f’
 >-- rw[o_assoc] >>
 rw[Er1_Ed_Tp])
(form_goal 
 “∀A B F1 F2:A->B η.
  Nt(η,F1,F2) ⇒
  ∀C F3:B->C. Nt(Rw(F3,η),F3 o F1,F3 o F2)”));

val Adj_alt = prove_store("Adj_alt",
e0
(rpt strip_tac >> rw[Adj_def] >>
 strip_tac (* 2 *)
 >-- (irule Nt_ext >> arw[ID_ap] >>
     qexistsl_tac [‘L’,‘L’] >> rw[ID_Nt] >>
     irule vo_Nt_Nt >>
     qexistsl_tac [‘L o R o L’] >>
     strip_tac (* 2 *)
     >-- (rev_drule Nt_Lw_Nt >> fs[IdL,o_assoc]) >>
     drule Nt_Rw_Nt >> fs[IdR]) >>
 irule Nt_ext >> arw[ID_ap] >>
 qexistsl_tac [‘R’,‘R’] >> rw[ID_Nt] >>
 irule vo_Nt_Nt >>
 qexistsl_tac [‘R o L o R’] >>
 strip_tac (* 2 *)
 >-- (rev_drule Nt_Rw_Nt >> fs[IdR]) >>
 drule Nt_Lw_Nt >> fs[IdL,o_assoc])
(form_goal 
 “∀L:X->A R:A->X η: X-> Exp(2,X) ε:A->Exp(2,A).
  Nt(ε, L o R,Id(A)) &
  Nt(η,Id(X),R o L) &
  (∀x:1->X. 
  vo(Lw(ε,L),Rw(L,η)) o x = Tp1(id(L o x))) & 
  (∀a:1->A.
  vo(Rw(R,ε),Lw(η,R)) o a = Tp1(id(R o a))) ⇒
  Adj(L,R,η,ε)”));

(*
vo(Lw(ε,L),Rw(L,η))  = ID(L) ∧ 
  vo(Rw(R,ε),Lw(η,R))  = ID(R)”));
*)

(*
val CC5_alt = prove_store("CC5_alt",
e0
()
(form_goal
 “∀A B. ∀a:1->A. ∃!b:1->B.Ro(a,b) &
  ∀f:2->A.
  ∃!g:2->B. 
  Ra(a,b) & Ro(dom(a),dom(b)) & Ro(cod(a),cod(b)) &
  ”));
*)

(*Parallel product arrow*)
val Prla_def = 
    qdefine_fsym ("Prla",[‘f:A->B’,‘g:C->D’])
    ‘Pa(f o p1(A,C),g o p2(A,C))’
    |> gen_all |> store_as "Prla_def";(**)

(*
val Nt_to_ID_cod = prove_store("Nt_to_ID_cod",
e0
()
(form_goal
 “”));
*)


(*should follow from csL_Pt_Ed *)
val Er1_Ed_cod_cpnt = prove_store("Er1_Ed_cod_cpnt",
e0
(rpt strip_tac >> rw[cod_def,cpnt_def,Pt_def,Pa_distr,
  p12_of_Pa,o_assoc,IdL] >>
rw[Ed_def,Er1_def,Pa_distr,o_assoc,p12_of_Pa,IdL] >>
rw[To1_def] >> 
 rw[Ev_of_Tp_el] >>
 rw[o_assoc,Pa_distr,p12_of_Pa,To1_def] >>
 rw[one_to_one_Id] >> rw[IdR])
(form_goal
“∀A B η a.Er1(B) o Ed(1f,B) o η o a:1->A = cod(cpnt(η,a))”));


(*should follow from csR_Pt_Ed *)
val Er1_Ed_dom_cpnt = prove_store("Er1_Ed_dom_cpnt",
e0
(rpt strip_tac >> rw[dom_def,cpnt_def,Pt_def,Pa_distr,
  p12_of_Pa,o_assoc,IdL] >>
rw[Ed_def,Er1_def,Pa_distr,o_assoc,p12_of_Pa,IdL] >>
rw[To1_def] >> 
 rw[Ev_of_Tp_el] >>
 rw[o_assoc,Pa_distr,p12_of_Pa,To1_def] >>
 rw[one_to_one_Id] >> rw[IdR])
(form_goal
“∀A B η a.Er1(B) o Ed(0f,B) o η o a:1->A = dom(cpnt(η,a))”));



val vo_cpsb = prove_store("vo_cpsb",
e0
(rpt strip_tac >> rw[cpsb_def] >>
 rw[GSYM Er1_Ed_dom_cpnt,GSYM Er1_Ed_cod_cpnt] >>
 qsuff_tac
 ‘Er1(B) o (Ed(0f, B) o ε) o a = 
  Er1(B) o (Ed(1f, B) o η) o a’
 >-- rw[o_assoc] >> arw[])
(form_goal
 “∀A B η ε.
  Ed(1f, B) o η = Ed(0f, B) o ε ⇒
  ∀a:1->A. cpsb(cpnt(ε,a) , cpnt(η,a))”));

(*
val vo_ab = prove_store("vo_ab",
e0
()
(form_goal
 “Ed(1f, B) o η = Ed(0f, B) o ε ⇒
  ”));
*)

“Ev(3, B) o Pa(γ, irt(η, ε) o f:2->A) = 
 tri(Ev(2, B) o Pa(Id(2), η o f), 
     Ev(2, B) o Pa(Id(2), ε o f)) o γ”

(*
val is_Tp1 = 

val Tp1_eq_eq = 


“irt() :A-> Exp(3,B) = 3-> Exp(A,B)”
rw[Tp0_def,irt_def] >>

rw[GSYM Tp0_def,Ed_def]   >> rw[Ev_of_Tp_el,o_assoc] >>
rw[Pa_distr,p12_of_Pa,o_assoc,IdR]   
“Tp0(Ed(γ,B) o irt(ε,η)) = 
 Ev(3, B) o Pa(γ, irt(ε, η) o To1(2))”


“Tp0(Ed(γ,B) o irt(ε,η)) = 
 tri((Ev(2, B) o Pa(Id(2), η o f)), (Ev(2, B) o
                  Pa(Id(2), ε o f))) o γ”

“Ev(3, B) o Pa(γ, irt(ε, η) o To1(2)) = 
 tri((Ev(2, B) o Pa(Id(2), η o f)), (Ev(2, B) o
                  Pa(Id(2), ε o f))) o γ”

*)

val Tp0_Ed_gamma = prove_store("Tp0_Ed_gamma",
e0
(rpt strip_tac >> rw[GSYM Tp0_def] >>
 rw[Ed_def,o_assoc,Ev_of_Tp_el] >>
 rw[o_assoc,p12_of_Pa,Pa_distr,IdL,IdR,To1_def])
(form_goal
“∀A t:1->Exp(3,B). Tp0(Ed(γ,B) o t) = Tp0(t) o γ”));

val Tp0_Ed_o = prove_store("Tp0_Ed_o",
e0
(rpt strip_tac >> 
rw[GSYM Tp0_def,Ed_def,o_assoc,Ev_of_Tp_el]   >> 
rw[Pa_distr,p12_of_Pa,o_assoc,IdL,IdR,To1_def])
(form_goal “∀Y P p:Y->P A t1:1->Exp(P,A). 
 Tp0(t1) o p = Tp0(Ed(p,A) o t1)”));

val Tp0_eq_eq = prove_store("Tp0_eq_eq",
e0
(cheat)
(form_goal “∀A B f:1->Exp(A,B) g. Tp0(f) = Tp0(g) ⇔ f = g”));

val Tp0_Tp = prove_store("Tp0_Tp",
e0
(cheat)
(form_goal
 “Tp0(Tp(f:A * 1 -> B)) = f o Pa(Id(A),To1(A))”));

val Er1_eq_eq = prove_store("Er1_eq_eq",
e0
(cheat)
(form_goal “∀X A f:X->Exp(1,A) g. Er1(A) o f = Er1(A) o g ⇔ f = g”));


val Pa_p1_p2 = prove_store("Pa_p1_p2",
e0
(rpt strip_tac >> flip_tac >>
 irule is_Pa >> rw[IdR])
(form_goal
 “!A B. Pa(p1(A,B),p2(A,B)) = Id(A * B)”));



val vo_cpnt = prove_store("vo_cpnt",
e0
(rpt strip_tac >> rw[oa_def] >>
 qsspecl_then [‘tri(cpnt(η, a), cpnt(ε, a))’] assume_tac
 (GSYM Tp0_Tp1_inv) >> once_arw[] >>
 rw[GSYM Tp0_Ed_gamma] >> rw[cpnt_def] >> 
 rw[vo_def,Pt_def] >> 
 rw[o_assoc,Pa_distr,p12_of_Pa] >>
 rw[GSYM Tp0_def] >>
 rw[GSYM Tp1_def] >> rw[o_assoc] >>
 qsuff_tac
 ‘Tp((tri((Ev(2, B) o Pa(Id(2), η o a o To1(2))), (Ev(2, B) o
                  Pa(Id(2), ε o a o To1(2)))) o p1(3, 1))) = 
   irt(η, ε) o a ’
 >-- (strip_tac >> arw[o_assoc]) >>
 irule $ iffLR Tp0_eq_eq >> rw[Tp0_Tp] >>
 rw[o_assoc,p12_of_Pa,IdR] >>
 pop_assum (K all_tac) >> 
 qsuff_tac
 ‘Tp0(irt(η, ε) o a) o α =
  Ev(2, B) o Pa(Id(2), η o a o To1(2)) & 
  Tp0(irt(η, ε) o a) o β =
  Ev(2, B) o Pa(Id(2), ε o a o To1(2))’
 >-- (strip_tac >>
     qabbrev_tac ‘Ev(2, B) o Pa(Id(2), η o a o To1(2)) = l1’>>
     qabbrev_tac ‘Ev(2, B) o Pa(Id(2), ε o a o To1(2)) = l2’>>
     qsspecl_then [‘l1’,‘l2’] assume_tac tri_def >>
     qby_tac ‘dom(l2) = cod(l1)’ 
     >-- (qpick_x_assum ‘Ev(2, B) o Pa(Id(2), η o a o To1(2)) = l1’ (assume_tac o GSYM) >> arw[] >>
         rw[cod_def,o_assoc,Pa_distr,IdL,To1_def] >>
         qpick_x_assum ‘Ev(2, B) o Pa(Id(2), ε o a o To1(2)) = l2’ (assume_tac o GSYM) >> arw[] >>
         rw[dom_def,o_assoc,Pa_distr,IdL,To1_def] >>
         qby_tac
         ‘Ed(1f, B) o η o a = Ed(0f, B) o ε o a’
         >-- arw[GSYM o_assoc] >>
         qby_tac
         ‘Pt(Ed(1f, B) o η o a) = Pt(Ed(0f, B) o ε o a)’
         >-- arw[] >>
         pop_assum mp_tac >> 
         rw[Pt_def,o_assoc,Ed_def,Ev_of_Tp_el] >>
         rw[o_assoc,Pa_distr,p12_of_Pa] >>
         rw[one_to_one_Id,IdR] >> strip_tac >>
         qby_tac
         ‘Ev(2, B) o Pa(1f o p1(1, 1), η o a o p2(1, 1)) o 
         Pa(Id(1),Id(1)) = Ev(2, B) o
               Pa(0f o p1(1, 1), ε o a o p2(1, 1)) o 
         Pa(Id(1),Id(1)) ’ 
         >-- arw[GSYM o_assoc] >> 
         pop_assum mp_tac >>
         rw[Pa_distr,p12_of_Pa,o_assoc,IdR] >>
         strip_tac >> arw[]) >>
     first_x_assum drule >>
     arw[] >> pop_assum strip_assume_tac >>
     flip_tac >> first_x_assum irule >>
     fs[]) >>
 (*rw[GSYM Tp0_def] >> *)rw[Tp0_Ed_o] >>
 qsspecl_then [‘η’,‘ε’] assume_tac irt_def >>
 first_x_assum drule >> arw[GSYM o_assoc] >>
 rw[GSYM Tp0_def])
(form_goal
 “∀A B η ε.
  Ed(1f, B) o η = Ed(0f, B) o ε ⇒
  ∀a:1->A. cpnt(vo(ε,η),a) = cpnt(ε,a) @ cpnt(η,a)”));

val Thm13_ex = prove_store("Thm13_ex",
e0
(rpt strip_tac >> 
 qby_tac
 ‘∃G:A->X. 
  ∀a:2->A a1 a2. dom(a) = a1 & cod(a) = a2 ⇒
           ∃f1:2->A f2:2->A.
           dom(f1) = F o G o a1 & cod(f1) = a1 &
           dom(f2) = F o G o a2 & cod(f2) = a2 &
           U(G o a1,f1) & U(G o a2,f2) & 
           f2 @ (F o G o a) = a @ f2’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘∃η:X -> Exp(2,X). 
   Nt(η, Id(X), G o F) &
   ∀x:1->X. 
    ∃fFx:2-> A.
      U(G o F o x,fFx) & 
      fFx @ cpnt(Rw(F,η), x) = id(F o x)’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘∃ε:A -> Exp(2,A). 
   Nt(ε,F o G,Id(A)) &
   ∀a:1->A. 
      U(G o a,cpnt(ε,a)) & 
     ∃f. cpnt(ε,a) @ f = id(a)’
 >-- cheat >>
 pop_assum strip_assume_tac >> 
 qexistsl_tac [‘G’,‘η’,‘ε’] >>
 qby_tac
 ‘∀a.cod(cpnt(ε, a)) = a & U(G o a, cpnt(ε, a)) ’
 >-- strip_tac >>
     arw[] >> 
     (*follows from Nt(ε, F o G, Id(A))*)
     fs[Nt_def] >> 
     first_x_assum cheat >>
 arw[] >> irule Adj_alt >> arw[] >>
 




     qby_tac ‘U(G o a,cpnt(ε,a))’ >-- arw[] >>
     last_assum drule >>
     drule $ iffLR UFrom_def >> 


“fFx @ cpnt(Rw(F,η), x) = id(F o x:1->X)”

rastt "cpnt(Lw(F:X->A,η:X->Exp(2,X)), x:1->X)"
“id(F o x:1->X) = a”

Adj_def
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

