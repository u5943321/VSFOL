
val _ = add_parse (int_of "η");

val cpnt_def = qdefine_fsym("cpnt",
[‘η:A -> Exp(2,B)’,‘a:1->A’])
‘Pt(η o a) o Pa(Id(2),To1(2))’
|> gen_all

val _ = add_parse (int_of "η");

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


val Adj_alt1 = prove_store("Adj_alt1",
e0
(rpt strip_tac >>
 irule Adj_alt >> arw[] >>
 once_rw[GSYM Tp0_eq_eq]>> rw[Tp0_Tp1_inv] >>
 pop_assum_list (map_every (assume_tac o GSYM)) >>
 arw[] >>
 rw[GSYM Tp0_def,cpnt_def,Pt_def,o_assoc,Pa_distr,p12_of_Pa] )
(form_goal
 “∀L:X->A R:A->X η: X-> Exp(2,X) ε:A->Exp(2,A).
  Nt(ε, L o R,Id(A)) &
  Nt(η,Id(X),R o L) &
  (∀x:1->X. 
  cpnt(vo(Lw(ε,L),Rw(L,η)),x) = id(L o x)) & 
  (∀a:1->A.
  cpnt(vo(Rw(R,ε),Lw(η,R)),a) = id(R o a)) ⇒
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

(*
“Ev(3, B) o Pa(γ, irt(η, ε) o f:2->A) = 
 tri(Ev(2, B) o Pa(Id(2), η o f), 
     Ev(2, B) o Pa(Id(2), ε o f)) o γ”
*)

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



val Lw_cpnt = prove_store("Lw_cpnt",
e0
(rw[cpnt_def,Lw_def,o_assoc])
(form_goal
 “cpnt(Lw(ε:B->Exp(2,A), F:X->B), x:1->X) = 
  cpnt(ε,F o x)”));


val Rw_cpnt = prove_store("Rw_cpnt",
e0
(rw[cpnt_def,Rw_def,o_assoc,Ec_def,Pt_def] >>
 rw[o_assoc,Ev_of_Tp_el,Pa_distr,p12_of_Pa]  )
(form_goal
 “cpnt(Rw(H:B->C,η:A->Exp(2,B)), a:1->A) = 
  H o cpnt(η, a)”));

val Thm13_eqn2_lemma = prove_store("Thm13_eqn2_lemma",
e0
(rpt strip_tac >>
first_assum rev_drule >>
drule $ iffLR UFrom_def >>
pop_assum strip_assume_tac >>
first_x_assum (qsspecl_then [‘G o a’,‘e’] assume_tac) >>
rfs[] >>
qby_tac
‘e @ id(F o G o a) = e’
>-- cheat >>
qby_tac
‘e @ (F o id(G o a)) = e’
>-- cheat >>
qby_tac
 ‘∀k. e @ F o k = e ⇒ k = id(G o a)’
>-- cheat (*by uniqueness
      ?!(fh : fun(2, X)). e = e @ F o fh#*) >>
first_x_assum irule >>
arw[])
(form_goal
“∀X A F:X->A G:A->X η h1 h2 a. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃!x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∃e. U(G o a:1->A,e) & dom(e) = cod(F o h2)) &
   U(dom(h2), F o h2) & 
    F o (h2 @ h1) = F o id(G o a) ⇒
  h2 @ h1 = id(G o a)”));


val csL_Pt' = rewr_rule[o_assoc] csL_Pt 

(*
Er1_Ed_dom_cpnt |> rewr_rule[GSYM csL_Pt']

 cs_of_vo_0f
*)
 
val cs_of_Nt = prove_store("cs_of_Nt",
e0
(cheat)
(form_goal
 “∀F1 F2 η:A->Exp(2,B).
   Nt(η,F1,F2) ⇒
   ∀f:2->A. 
   csT(Pt(η o f)) = cpnt(η,dom(f)) &
   csB(Pt(η o f)) = cpnt(η,cod(f)) &
   csL(Pt(η o f)) = F1 o f &
   csR(Pt(η o f)) = F2 o f”));



val id_cod = prove_store("id_cod",
e0
(rw[cod_def,id_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. cod(id(a)) = a”));


val id_dom = prove_store("id_dom",
e0
(rw[dom_def,id_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. dom(id(a)) = a”));

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

val cpnt_csB_Pt = prove_store("cpnt_csB_Pt",
e0
(rw[csB_Pt,cpnt_def] >> rpt strip_tac >>
rw[Er1_def,Ed_def,o_assoc,Pt_def] >>
 rw[o_assoc,Pa_distr,p12_of_Pa,To1_def,IdL,IdR] >>
 rw[Ev_of_Tp_el] >> 
 rw[o_assoc,p12_of_Pa,Pa_distr,To1_def] >>
 rw[Ev_of_Tp_el'] >>
 rw[o_assoc,p12_of_Pa,Pa_distr,To1_def,Swap_Pa] >>
 rw[id_def,one_to_one_Id,IdR,IdL,o_assoc] >>
 qby_tac
 ‘ η o c o To1(2) o 1f o To1(2) = 
   η o c o (To1(2) o 1f) o To1(2)’ >-- rw[o_assoc] >>
 arw[] >> rw[one_to_one_Id,IdL])
(form_goal
“∀A B η:A->Exp(2,B) c. csB(Pt(η o id(c))) = cpnt(η, c)”));


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




val Nt_compr = prove_store("Nt_compr",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?cf :C -> Exp(2, D).
    !a : 2->C  b: 2 -> Exp(2, D).
          P(dom(a), csT(Pt(b))) &
          P(cod(a), csB(Pt(b))) &
          csL(Pt(b)) = F1 o a & csR(Pt(b)) = F2 o a <=> cf o a = b’ 
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     qby_tac ‘Nt(cf, F1, F2)’ 
     >-- (rw[Nt_def] >> strip_tac >>
     first_x_assum (qsspecl_then [‘f’,‘cf o f’] assume_tac) >>
     fs[]) >> arw[] >>
     strip_tac >>
     first_x_assum 
     (qsspecl_then [‘id(c)’,‘cf o id(c)’]
                   assume_tac) >>
     fs[] >> fs[id_dom,id_cod] >> rw[GSYM cpnt_csB_Pt] >> 
     arw[]) >>
 match_mp_tac
 (CC5 |> qspecl [‘C’,‘Exp(2,D)’] 
 |> fVar_sInst_th “R(f:2->C,g:2->Exp(2,D))”
    “P(dom(f),csT(Pt(g))) & 
     P(cod(f),csB(Pt(g))) &
     csL(Pt(g)) = F1:C->D o f & 
     csR(Pt(g)) = F2 o f”
 |> rewr_rule[id_dom,id_cod]
 |> rewr_rule[csB_Pt_id,csT_Pt_id]) >>
 strip_tac (* 2 *)
 >-- (strip_tac >> 
     qsuff_tac
     ‘∃g: 2-> Exp(2,D).
      P(dom(f), csT(Pt(g))) &
      P(cod(f), csB(Pt(g))) &
      csL(Pt(g)) = F1 o f & csR(Pt(g)) = F2 o f’
     >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR Pt_eq_eq >>
     irule cs_ext >> arw[] >> strip_tac (* 2 *)
     >-- 
     (first_assum (qspecl_then [‘dom(f)’] assume_tac) >>
     pop_assum (strip_assume_tac o uex_expand) >> 
     qsuff_tac ‘csT(Pt(g')) = cpc & csT(Pt(g)) = cpc’ 
     >-- (strip_tac >> arw[]) >>
     strip_tac >> first_assum irule >> arw[]) >>
     first_assum (qspecl_then [‘cod(f)’] assume_tac) >>
     pop_assum (strip_assume_tac o uex_expand) >> 
     qsuff_tac ‘csB(Pt(g')) = cpc & csB(Pt(g)) = cpc’ 
     >-- (strip_tac >> arw[]) >>
     strip_tac >> first_assum irule >> arw[]) >>
     qsuff_tac
     ‘∃g0:2 * 2 ->D.
      P(dom(f), csT(g0)) &
      P(cod(f), csB(g0)) &
      csL(g0) = F1 o f & csR(g0) = F2 o f’
     >-- (strip_tac >> qexists_tac ‘Tp(g0)’ >>
         arw[Pt_Tp]) >>
     first_assum (qsspecl_then [‘dom(f)’] 
                               (assume_tac o uex2ex_rule)) >>
     pop_assum (x_choose_then "cpc1" assume_tac) >>
     first_assum (qsspecl_then [‘cod(f)’]
                               (assume_tac o uex2ex_rule)) >>
     pop_assum (x_choose_then "cpc2" assume_tac) >>
     qsspecl_then [‘cpc1’,‘F2 o f’,‘F1 o f’,‘cpc2’] 
     assume_tac Thm7 >>
     qsuff_tac
     ‘?q: 2 * 2 -> D.
        csT(q) = cpc1 &
        csR(q) = F2 o f & csL(q) = F1 o f & csB(q) = cpc2’
     >-- (strip_tac >> qexists_tac ‘q’ >> arw[]) >>
     first_x_assum irule >> 
     qby_tac
     ‘cpsb(cpc2, F1 o f)’
     >-- (rw[cpsb_def] >>
         first_x_assum drule>> arw[] >> 
         rw[cod_def,o_assoc]) >>
     qby_tac
     ‘cpsb(F2 o f, cpc1)’
     >-- (rw[cpsb_def] >>
         first_x_assum rev_drule>> arw[] >> 
         rw[dom_def,o_assoc]) >>
     arw[] >>
     first_x_assum irule >> strip_tac (* 2 *)
     >-- (qexists_tac ‘dom(f)’ >> arw[]) >>
     qexists_tac ‘cod(f)’ >> arw[]) >>
 strip_tac (* 2 *) >--
 (rpt gen_tac >> strip_tac >>
  rw[GSYM csT_Pt_Tp0,GSYM csB_Pt_Tp0] >> arw[] >>
  qpick_x_assum
  ‘csL(Pt(g)) = F1 o f’ (assume_tac o GSYM) >>
  rw[id_def,dom_def,cod_def] >> rw[o_assoc] >> 
  arw[GSYM o_assoc] >>
  qpick_x_assum 
  ‘csR(Pt(g)) = F2 o f’ (assume_tac o GSYM) >>
  arw[o_assoc] >>
  rw[GSYM dom_def,GSYM cod_def,GSYM o_assoc] >>
  rw[GSYM id_def] >>
  arw[] >>
  rw[csL_Pt_id,csR_Pt_id] >>
  qby_tac
  ‘dom(csL(Pt(g))) = dom(csT(Pt(g))) & 
   dom(csR(Pt(g))) = cod(csT(Pt(g)))’
  >-- rw[dom_csL_dom_csT,dom_csR_cod_csT] >>
  arw[csT_Pt_Tp0] >>
  qby_tac
  ‘cod(csL(Pt(g))) = dom(csB(Pt(g))) & 
   cod(csR(Pt(g))) = cod(csB(Pt(g)))’ 
  >-- rw[cod_csL_dom_csB,cod_csR_cod_csB] >>
  arw[csB_Pt_Tp0]) >>
 rpt strip_tac >>
 irule $ iffLR Pt_eq_eq >> irule cs_ext >>
 arw[] >>
 qby_tac ‘dom(g @ f) = dom(f) & cod(g @ f) = cod(g)’ 
 >-- (drule oa_dom_cod >> arw[]) >> fs[] >>
 qby_tac
 ‘∀c:1->C cp1 cp2. P(c,cp1:2->D) & P(c,cp2) ⇒ cp1 = cp2’
 >-- (rpt strip_tac >> 
     first_x_assum (qspecl_then [‘c’] assume_tac) >>
     pop_assum (strip_assume_tac o uex_expand) >>
     qsuff_tac ‘cp1 = cpc & cp2 = cpc’
     >-- (strip_tac >> arw[]) >>
     strip_tac >> first_x_assum irule >> arw[]) >>
 qby_tac
 ‘csT(Pt(h)) = csT(Pt(f1))’ 
 >-- (first_x_assum irule >> 
     qexists_tac ‘dom(f)’ >> arw[]) >> arw[] >>
 qby_tac
 ‘csB(Pt(h)) = csB(Pt(g1))’
 >-- (first_x_assum irule >> 
     qexists_tac ‘cod(g)’ >> arw[]) >> arw[] >>
 drule fun_pres_oa >> arw[] >>
 qpick_x_assum
 ‘csL(Pt(g1)) = F1 o g’ (assume_tac o GSYM) >> arw[] >>
 qpick_x_assum
 ‘csR(Pt(g1)) = F2 o g’ (assume_tac o GSYM) >> arw[] >>
 qpick_x_assum
 ‘csL(Pt(f1)) = F1 o f’ (assume_tac o GSYM) >> arw[] >>
 qpick_x_assum
 ‘csR(Pt(f1)) = F2 o f’ (assume_tac o GSYM) >> arw[] >>
 qby_tac ‘cpsb(g1,f1)’ 
 >-- (rw[cpsb_def] >> fs[csB_Pt_Tp0,csT_Pt_Tp0] >>
     irule $ iffLR Tp0_eq_eq >>
     first_x_assum irule >>
     qexists_tac ‘cod(f)’ >> arw[] >>
     fs[cpsb_def] >> rfs[]
     (*by uniqueness using definition of cpsb,assum 1*))>>
 drule csL_Pt_oa >>
 drule csR_Pt_oa >>
 drule csT_Pt_oa >>
 drule csB_Pt_oa >> arw[])
(form_goal
 “∀C D F1:C->D F2:C->D. 
  (∀c cpc. P(c,cpc) ⇒ 
           dom(cpc) = F1 o c & cod(cpc) = F2 o c) &
  (∀c:1->C. ∃!cpc:2->D. P(c,cpc)) &
  (∀f:2->C c1 c2. dom(f) = c1 & cod(f) = c2 ⇒
  ∀cpc1 cpc2. P(c1,cpc1) & P(c2,cpc2) ⇒  
   (F2 o f) @ cpc1 = cpc2 @ (F1 o f)) ⇒
  ∃η:C-> Exp(2,D).
   Nt(η,F1,F2) &
   ∀c:1->C. P(c,cpnt(η,c))”));

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
 >-- (*strip_tac >>
     arw[] >> 
     (*follows from Nt(ε, F o G, Id(A))*)
     fs[Nt_def] >> 
     first_x_assum*) cheat >>
 arw[] >> irule Adj_alt1 >> arw[] >> 
 qsspecl_then [‘Rw(F, η)’,‘Lw(ε, F)’] assume_tac
 vo_cpnt >>
 qby_tac
 ‘Ed(1f, A) o Rw(F, η) = Ed(0f, A) o Lw(ε, F)’
 >-- cheat >>
 first_x_assum drule>> arw[] >>
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 qsspecl_then [‘Lw(η, G)’,‘Rw(G, ε)’] assume_tac
 vo_cpnt >>
 qby_tac
 ‘Ed(1f, X) o Lw(η, G) = Ed(0f, X) o Rw(G, ε)’
 >-- cheat >>
 first_x_assum drule>> arw[] >> rw[Lw_cpnt,Rw_cpnt] >>
 rpt strip_tac (* 2 *)
 qsuff_tac
 ‘’
 
 




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

