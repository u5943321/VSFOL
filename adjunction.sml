
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
 ∃!fh:2->D. dom(fh) = x' & cod(fh) = y & f @ (F o fh) = f')’ 
|> qgenl [‘D’,‘C’,‘F’,‘x’,‘y’,‘f’]


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


val cpsb_idL = prove_store("cpsb_idL",
e0
cheat
(form_goal
 “∀A a:1->A f.cpsb(id(a),f) ⇒ id(a) @ f = f”));


val cpsb_idR = prove_store("cpsb_idR",
e0
cheat
(form_goal
 “∀A a:1->A f.cpsb(f,id(a)) ⇒ f @ id(a) = f”));

val id_cod = prove_store("id_cod",
e0
(rw[cod_def,id_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. cod(id(a)) = a”));


val id_dom = prove_store("id_dom",
e0
(rw[dom_def,id_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. dom(id(a)) = a”));


(*(*idL idR*)
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
>-- (qby_tac ‘cpsb(e,id(F o G o a))’
    >-- (rw[cpsb_def]>> arw[id_cod]) >>
    drule cpsb_idR >> arw[]) >>
qby_tac
‘e @ (F o id(G o a)) = e’
>-- (qsuff_tac ‘(F o id(G o a)) = id(F o G o a)’
    >-- (strip_tac >> arw[]) >>
    rw[id_def,o_assoc]) >>
qby_tac
 ‘∀k. dom(k) = G o a & cod(k) = G o a &
      e @ F o k = e ⇒ k = id(G o a)’
>-- (qpick_x_assum
    ‘?!fh:2->X. dom(fh) = G o a & cod(fh) = G o a & 
     e @ (F o fh) = e’ 
    (strip_assume_tac o uex_expand) >>
    rpt strip_tac >>
    qsuff_tac ‘k = fh & id(G o a) = fh’ 
    >-- (strip_tac >> arw[]) >>
    strip_tac >> first_x_assum irule >> arw[id_dom,id_cod] ) >>
   (*by uniqueness
      ?!(fh : fun(2, X)). e = e @ F o fh#*) 
first_x_assum irule >>
arw[] >>
drule oa_dom_cod >> arw[])
(form_goal
“∀X A F:X->A G:A->X h1 h2 a. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃!x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∃e. U(G o a:1->A,e) & dom(e) = cod(F o h2)) &
   cpsb(h2,h1) &
   cod(h2) = G o a & dom(h1) = G o a &
   U(dom(h2), F o h2) & 
    F o (h2 @ h1) = F o id(G o a) ⇒
  h2 @ h1 = id(G o a)”));

*)


(*idL idR*)
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
>-- (qby_tac ‘cpsb(e,id(F o G o a))’
    >-- (rw[cpsb_def]>> arw[id_cod]) >>
    drule cpsb_idR >> arw[]) >>
qby_tac
‘e @ (F o id(G o a)) = e’
>-- (qsuff_tac ‘(F o id(G o a)) = id(F o G o a)’
    >-- (strip_tac >> arw[]) >>
    rw[id_def,o_assoc]) >>
qby_tac
 ‘∀k. dom(k) = G o a & cod(k) = G o a &
      e @ F o k = e ⇒ k = id(G o a)’
>-- (qpick_x_assum
    ‘?!fh:2->X. dom(fh) = G o a & cod(fh) = G o a & 
     e @ (F o fh) = e’ 
    (strip_assume_tac o uex_expand) >>
    rpt strip_tac >>
    qsuff_tac ‘k = fh & id(G o a) = fh’ 
    >-- (strip_tac >> arw[]) >>
    strip_tac >> first_x_assum irule >> arw[id_dom,id_cod] ) >>
   (*by uniqueness
      ?!(fh : fun(2, X)). e = e @ F o fh#*) 
first_x_assum irule >>
arw[] >>
drule oa_dom_cod >> arw[])
(form_goal
“∀X A F:X->A G:A->X h1 h2 a. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (*(∀a:1->A. ∃x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∀a:1->A x1:1->X f1:2->A x2:1->X f2:2->A. 
   cod(f1) = a ∧ U(x1,f1) &
   cod(f2) = a ∧ U(x2,f2) ⇒ x1 = x2 & f1 = f2) &*)
  (∃e. U(G o a:1->A,e) & dom(e) = cod(F o h2)) &
   cpsb(h2,h1) &
   cod(h2) = G o a & dom(h1) = G o a &
   (*U(dom(h2), F o h2) & *)
    F o (h2 @ h1) = F o id(G o a) ⇒
  h2 @ h1 = id(G o a)”));



(*
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
“∀X A F:X->A G:A->X h1 h2 a. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃!x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∃e. U(G o a:1->A,e) & dom(e) = cod(F o h2)) &
   U(dom(h2), F o h2) & 
    F o (h2 @ h1) = F o id(G o a) ⇒
  h2 @ h1 = id(G o a)”));
*)

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

val dom_cpnt_dom_csT = prove_store("dom_cpnt_dom_csT",
e0
(rw[GSYM Er1_Ed_dom_cpnt] >>
 rw[csT_Pt] >> rpt strip_tac  >>
 rw[dom_def,o_assoc] >>
 rw[Er1_def,Ed_def,o_assoc,p12_of_Pa,Pa_distr,
    Ev_of_Tp_el,To1_def,IdL,IdR] >>
 rw[Pt_def,id_def,o_assoc,To1_def,Pa_distr,
    Swap_Pa,p12_of_Pa] >>
 rw[one_to_one_Id] >> rw[IdR])
(form_goal
 “∀A a:1->A B η:A->Exp(2,B). dom(cpnt(η, a)) = dom(csT(Pt(η o id(a))))”));


val cod_cpnt_cod_csB = prove_store("cod_cpnt_cod_csB",
e0
(rw[GSYM Er1_Ed_cod_cpnt] >>
 rw[csB_Pt] >> rpt strip_tac  >>
 rw[cod_def,o_assoc] >>
 rw[Er1_def,Ed_def,o_assoc,p12_of_Pa,Pa_distr,
    Ev_of_Tp_el,To1_def,IdL,IdR] >>
 rw[Pt_def,id_def,o_assoc,To1_def,Pa_distr,
    Swap_Pa,p12_of_Pa] >>
 rw[one_to_one_Id] >> rw[IdR])
(form_goal
 “∀A a:1->A B η:A->Exp(2,B). cod(cpnt(η, a)) = cod(csB(Pt(η o id(a))))”));

val cod_cpnt_cod_csR = 
cod_cpnt_cod_csB |> rewr_rule[GSYM cod_csR_cod_csB]


val dom_cpnt_dom_csL = 
dom_cpnt_dom_csT |> rewr_rule[GSYM dom_csL_dom_csT]





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


val F_id_dom = prove_store("F_id_dom",
e0
(rw[id_def,dom_def,o_assoc])
(form_goal “∀A B F g. F:A->B o id(dom(g)) = id(F o dom(g))”));

 
val F_id_cod = prove_store("F_id_cod",
e0
(rw[id_def,cod_def,o_assoc])
(form_goal “∀A B F g. F:A->B o id(cod(g)) = id(F o cod(g))”));


(*dom_o*)
val cpsb_o = prove_store("cpsb_o",
e0
(rpt strip_tac >> fs[cpsb_def] >>
 arw[dom_o,cod_o])
(form_goal
 “∀A g1:2->A f1. cpsb(g1, f1) ⇒
  ∀B F:A->B. cpsb(F o g1, F o f1)”));



val Thm13_G_ex = prove_store("Thm13_G_ex",
e0
(rpt strip_tac >>  
  match_mp_tac     
 (CC5 |> qspecl [‘A’,‘X’] 
 |> fVar_sInst_th “R(a:2->A,ga:2->X)”
    “∀a1:1->A a2:1->A.
     dom(a) = a1 & cod(a) = a2 ⇒
     ∃f1:2->A f2:2->A.
      dom(f1) = F o dom(ga) & cod(f1) = a1 &
      dom(f2) = F o cod(ga) & cod(f2) = a2 &
      U(dom(ga:2->X),f1) & U(cod(ga),f2) & 
      f2 @ (F o ga) = a @ f1”) >> strip_tac (* 2 *) >--
(rpt strip_tac >>
qsuff_tac
      ‘∃g.
!(a1 : fun(1, A))  (a2 : fun(1, A)).
                 dom(f) = a1 & cod(f) = a2 ==>
                 ?(f1 : fun(2, A))  (f2 : fun(2, A)).
                   dom(f1) = F o dom(g) &
                   cod(f1) = a1 &
                   dom(f2) = F o cod(g) &
                   cod(f2) = a2 &
                   U(dom(g), f1) & U(cod(g), f2) & f2 @ F o g = f @ f1 ’ >--
 (strip_tac >> uex_tac >> qexists_tac ‘g’ >>
  arw[] >> rpt strip_tac >>
  qabbrev_tac ‘dom(f) = a1’ >>
  qabbrev_tac ‘cod(f) = a2’ >>
  last_assum (qspecl_then [‘a1’] assume_tac) >>
  pop_assum 
  (x_choosel_then ["Ga1","fa1"] strip_assume_tac) >>
  last_x_assum (qspecl_then [‘a2’] assume_tac) >>
  pop_assum 
  (x_choosel_then ["Ga2","fa2"] strip_assume_tac) >>
  last_assum drule >> drule $ iffLR UFrom_def >>
  pop_assum strip_assume_tac >>
  first_x_assum 
  (qspecl_then [‘Ga1’,‘f @ fa1’] assume_tac) >>
  qby_tac
  ‘cpsb(f,fa1)’ 
  >-- (rw[cpsb_def] >> arw[]) >>
  drule oa_dom_cod >> fs[] >> rfs[] >> 
  qby_tac
  ‘dom(fa1) = F o Ga1’
  >-- (last_x_assum rev_drule >>
       drule $ iffLR UFrom_def >>
       arw[]) >> 
  first_x_assum drule >>
  assume_tac
  (uex_unique |> qspecl [‘2’,‘X’]
  |> fVar_sInst_th “P(fh:2->X)”
     “dom(fh:2->X) = Ga1 & cod(fh) = Ga2 &
     fa2 @ F:X->A o fh = f @ fa1”) >>
  first_x_assum drule >>
  first_x_assum irule >> 
  qsuff_tac
  ‘(dom(g) = Ga1 & cod(g) = Ga2 & 
   fa2 @ F o g = f @ fa1) &
   (dom(g') = Ga1 & cod(g') = Ga2 & 
   fa2 @ F o g' = f @ fa1)’
 >-- (strip_tac >> arw[]) >> conj_tac (* 2 *) >--
 (last_x_assum (qspecl_then [‘a1’,‘a2’] assume_tac) >>
 fs[] >> 
 last_assum (qspecl_then [‘a1’] assume_tac) >>
 qby_tac ‘Ga1 = dom(g) & fa1 = f1’ 
 >-- (first_x_assum irule >> arw[]) >> 
 last_x_assum (qspecl_then [‘a2’] assume_tac) >>
 qby_tac ‘Ga2 = cod(g) & fa2 = f2’ 
 >-- (first_x_assum irule >> arw[]) >> 
 arw[]) >> (*repeat this proof*)
 first_x_assum (qspecl_then [‘a1’,‘a2’] assume_tac) >>
 fs[] >> 
 last_assum (qspecl_then [‘a1’] assume_tac) >>
 qby_tac ‘Ga1 = dom(g') & fa1 = f1’ 
 >-- (first_x_assum irule >> arw[]) >> 
 last_x_assum (qspecl_then [‘a2’] assume_tac) >>
 qby_tac ‘Ga2 = cod(g') & fa2 = f2’ 
 >-- (first_x_assum irule >> arw[]) >> 
 arw[]) >> 
 qabbrev_tac ‘dom(f) = a1’ >>
 qabbrev_tac ‘cod(f) = a2’ >>
 last_assum (qspecl_then [‘a1’] assume_tac) >>
 pop_assum (x_choosel_then ["Ga1","fa1"] strip_assume_tac) >>
 last_assum (qspecl_then [‘a2’] assume_tac) >>
 pop_assum (x_choosel_then ["Ga2","fa2"] strip_assume_tac) >>
 last_assum drule >>
 drule $ iffLR UFrom_def >>
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘Ga1’,‘f @ fa1’] assume_tac) >>
 qby_tac ‘cpsb(f,fa1)’ 
 >-- arw[cpsb_def] >>  
 qby_tac
 ‘dom(f @ fa1) = F o Ga1 & cod(f @ fa1) = cod(fa2)’
 >-- (drule oa_dom_cod >> arw[] >>  
 (*dom(fa1) = F o Ga1 since U(Ga1, fa1),
   last line of this block repeat this step*)
 last_assum rev_drule >> drule $ iffLR UFrom_def >> arw[]) >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘fh’ >> rpt strip_tac >>
 qexistsl_tac [‘fa1’,‘fa2’] >>
 arw[] >> 
 qby_tac
 ‘a1' = a1’ 
 >-- (qpick_x_assum ‘dom(f) = a1'’
     (assume_tac o GSYM) >> arw[]) >>
 qby_tac
 ‘a2' = a2’ 
 >-- (qpick_x_assum ‘cod(f) = a2'’
     (assume_tac o GSYM) >> arw[]) >>
 arw[] >>
 fs[] >> pop_assum (K all_tac) >> pop_assum(K all_tac) >>
 last_assum rev_drule >> drule $ iffLR UFrom_def >> arw[]) >>
 strip_tac (* 2 *) >-- (rpt gen_tac >> strip_tac >> 
 strip_tac (* 2 *)
 >-- (rpt strip_tac >> rw[id_dom,id_cod] >>
     qabbrev_tac ‘dom(f) = d’ >>
     qabbrev_tac ‘cod(f) = c’ >>
     last_assum (qspecl_then [‘d’] assume_tac) >>
     pop_assum
     (x_choosel_then ["Gd","fd"] strip_assume_tac) >>
     qexistsl_tac [‘fd’,‘fd’] >>
     first_x_assum (qspecl_then [‘d’,‘c’] assume_tac) >>
     rfs[] >> 
     qby_tac ‘d = a1 & d = a2’ >-- (fs[id_dom,id_cod]) >>
     arw[] >> pop_assum (K all_tac) >>
     qby_tac ‘a1 = a2’ >-- fs[id_dom,id_cod] >>
     arw[] >> pop_assum (K all_tac) >>
     qsuff_tac ‘fd = f1’ 
     >-- (strip_tac >> arw[] >> rw[F_id_dom] >>
         qby_tac ‘cpsb(id(a2),f1)’ 
         >-- (rw[cpsb_def,id_dom]  >> arw[] >>
             fs[id_dom,id_cod]) >>
         drule cpsb_idL >> arw[] >>
         qby_tac ‘cpsb(f1, id(F o dom(g)))’
         >-- (rw[cpsb_def,id_cod] >> arw[]) >> 
         drule cpsb_idR >> arw[]) >> 
     qsuff_tac ‘Gd = dom(g) & fd = f1’ 
     >-- (strip_tac >> arw[]) >>
     first_x_assum irule >> arw[] >> 
     qexists_tac ‘d’ >> rw[]) >> 
 rpt strip_tac >> rw[id_dom,id_cod] >>
 qabbrev_tac ‘dom(f) = d’ >>
 qabbrev_tac ‘cod(f) = c’ >>
 last_assum (qspecl_then [‘c’] assume_tac) >>
 pop_assum
 (x_choosel_then ["Gc","fc"] strip_assume_tac) >>
 qexistsl_tac [‘fc’,‘fc’] >>
 first_x_assum (qspecl_then [‘d’,‘c’] assume_tac) >>
 rfs[] >> 
 qby_tac ‘c = a1 & c = a2’ >-- (fs[id_dom,id_cod]) >>
 arw[] >> pop_assum (K all_tac) >>
 qby_tac ‘a1 = a2’ >-- fs[id_dom,id_cod] >>
 arw[] >> pop_assum (K all_tac) >>
 qsuff_tac ‘fc = f2’ 
 >-- (strip_tac >> arw[] >> rw[F_id_cod] >>
      qby_tac ‘cpsb(id(a2),f2)’ 
      >-- (rw[cpsb_def,id_dom]  >> arw[] >>
             fs[id_dom,id_cod]) >>
      drule cpsb_idL >> arw[] >>
      qby_tac ‘cpsb(f2, id(F o cod(g)))’
      >-- (rw[cpsb_def,id_cod] >> arw[]) >> 
      drule cpsb_idR >> arw[]) >> 
 qsuff_tac ‘Gc = cod(g) & fc = f2’ 
 >-- (strip_tac >> arw[]) >>
 first_x_assum irule >> arw[] >> 
 qexists_tac ‘c’ >> rw[]) >>
 rpt strip_tac >>
 qabbrev_tac ‘dom(f) = a1’ >>
 qabbrev_tac ‘cod(f) = a2’ >>
 qabbrev_tac ‘cod(g) = a3’ >>
 qby_tac ‘dom(g) = a2’ 
 >-- fs[cpsb_def] >>
 first_x_assum (qspecl_then [‘a2’,‘a3’] assume_tac) >>
 qby_tac ‘dom(g) = a2 & cod(g) = a3’ >-- arw[] >>
 first_x_assum drule >> 
 pop_assum (x_choosel_then ["fa2","fa3"] strip_assume_tac) >>
 fs[] >> 
 first_x_assum (qspecl_then [‘a1’,‘a2’] assume_tac) >>
 qby_tac ‘a1 = a1 & a2 = a2’ >-- arw[] >>
 first_x_assum drule >> 
 pop_assum (x_choosel_then ["fa1","fa21"] strip_assume_tac) >>
 fs[] >> 
 qby_tac ‘fa21 = fa2’ 
 >-- (qsuff_tac ‘cod(f1) = dom(g1) & fa21 = fa2’
     >-- (strip_tac >> arw[]) >>
     first_x_assum irule >> arw[] >> qexists_tac ‘a2’ >>
     rw[]) >> 
 fs[] >>
 pop_assum (K all_tac) >>
 drule oa_dom_cod >> fs[] >>
 first_x_assum (qsspecl_then [‘a1’,‘a3’] assume_tac) >>
 qby_tac ‘a1 = a1 & a3 = a3’ >-- arw[] >>
 first_x_assum drule >> 
 pop_assum 
 (x_choosel_then ["fa11","fa31"] strip_assume_tac) >>
 qby_tac ‘dom(h) = dom(f1) & fa11 = fa1’ 
 >-- (first_x_assum irule >> arw[] >> 
     qexists_tac ‘a1’ >> rw[]) >> fs[] >>
 qby_tac ‘cod(h) = cod(g1) & fa31 = fa3’ 
 >-- (first_x_assum irule >> arw[] >>
     qexists_tac ‘a3’ >> rw[]) >> fs[] >>
 last_assum drule >> drule $ iffLR UFrom_def >>
 pop_assum strip_assume_tac >>
 first_x_assum 
 (qspecl_then [‘dom(f1)’,‘g @ f @ fa1’] assume_tac) >>
 qby_tac ‘cpsb(f,fa1)’ >-- arw[cpsb_def] >>
 drule oa_dom_cod >> 
 qby_tac ‘cpsb(g,f @ fa1)’ 
 >-- arw[cpsb_def] >>
 drule oa_dom_cod >> fs[] >> rfs[] >>
 assume_tac
 (uex_unique |> qspecl [‘2’,‘X’] 
 |> fVar_sInst_th “P(fh:2->X)”
    “dom(fh:2->X) = dom(f1) &
     cod(fh) = cod(g1) & fa3 @ F:X->A o fh = g @ f @ fa1”) >>
 first_x_assum drule >>
 first_x_assum irule >> arw[] >>
 qby_tac ‘cpsb(g1,f1)’
 >-- (arw[cpsb_def] >> 
     qsuff_tac ‘dom(g1) = cod(f1) & fa2 = fa2’ 
     >-- (strip_tac >> arw[]) >>
     first_x_assum irule >> arw[] >> 
     qexists_tac ‘a2’ >> rw[]) >>
 drule oa_dom_cod >> arw[] >>
 qby_tac ‘(g @ f) @ fa1 = g @ f @ fa1’ 
 >-- (irule Thm8 >> arw[]) >>
 arw[] >>
 (*fa3 @ F o g1 = g @ fa2 ,fa2 @ F o f1 = f @ fa1 *)
 drule fun_pres_oa >> arw[] >>
 qby_tac
 ‘fa3 @ (F o g1) @ F o f1 = 
  (fa3 @ (F o g1)) @ F o f1’
 >-- (flip_tac >> irule Thm8 >> 
     drule cpsb_o >> arw[] >>
     rw[cpsb_def] >> arw[cod_o]) >>
 arw[] >> 
 qby_tac ‘(g @ fa2) @ F o f1 = g @ fa2 @ F o f1’
 >-- (irule Thm8 >> arw[cpsb_def,cod_o]) >>
 arw[])
(form_goal
 “∀X A F:X->A. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∀a:1->A x1:1->X f1:2->A x2:1->X f2:2->A. 
   cod(f1) = a ∧ U(x1,f1) &
   cod(f2) = a ∧ U(x2,f2) ⇒ x1 = x2 & f1 = f2) ⇒
  ?(cf : fun(A, X)).
        !(a : fun(2, A))  (b : fun(2, X)).
          (!(a1 : fun(1, A))  (a2 : fun(1, A)).
              dom(a) = a1 & cod(a) = a2 ==>
              ?(f1 : fun(2, A))  (f2 : fun(2, A)).
                dom(f1) = F o dom(b) &
                cod(f1) = a1 &
                dom(f2) = F o cod(b) &
                cod(f2) = a2 &
                U(dom(b), f1) & U(cod(b), f2) & f2 @ F o b = a @ f1) ⇔ cf o a = b”));


val Nt_compr_uex = prove_store("Nt_compr_uex",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘∃η:C-> Exp(2,D).
   Nt(η,F1,F2) &
   ∀c:1->C. P(c,cpnt(η,c))’
 >-- (strip_tac >> qexists_tac ‘η’ >>arw[] >>
     rpt strip_tac >>
     last_x_assum (qsspecl_then [‘c’] 
     (strip_assume_tac o uex_expand)) >>
     dimp_tac >> strip_tac (* 2 *) >--
     (first_assum drule >> 
     first_x_assum (qspecl_then [‘c’] assume_tac) >>
     first_x_assum drule >> arw[]) >>
     arw[]) >>
 irule Nt_compr >> arw[])
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
   (∀c:1->C ad:2->D. P(c,ad) ⇔ ad = cpnt(η,c))”));





val Thm13_epsilon_ex = prove_store("Thm13_epsilon_ex",
e0
(rpt strip_tac >>
 match_mp_tac
 (Nt_compr_uex |> qsspecl [‘F:X->A o G:A->X’,‘Id(A)’] 
 |> fVar_sInst_th “P(a:1->A,ca:2->A)”
    “cod(ca:2->A) = a:1->A ∧ U(G:A->X o a,ca)”) >>
 qby_tac
 ‘!(c : fun(1, A))  (cpc : fun(2, A)).
     cod(cpc) = c & U(G o c, cpc) ==>
     dom(cpc) = (F o G) o c & cod(cpc) = Id(A) o c’
 >-- (rpt gen_tac >> strip_tac >>
     last_x_assum drule >>
     drule $ iffLR UFrom_def >>
     arw[o_assoc] >> rw[IdL]) >> arw[] >>
 qby_tac
 ‘!(c : fun(1, A)). 
  ?!(cpc : fun(2, A)). cod(cpc) = c & U(G o c, cpc)’
 >-- (strip_tac >> uex_tac >>
     first_x_assum 
     (qsspecl_then [‘id(c)’,‘G o id(c)’] assume_tac) >> 
    fs[] >> 
    fs[id_dom,id_cod] >>
    first_x_assum (qsspecl_then [‘c’,‘c’] assume_tac) >>
    fs[dom_o,id_dom,cod_o,id_cod] >>
    qexists_tac ‘f1’ >> arw[] >>
    rpt strip_tac >>
    qsuff_tac
    ‘G o c = G o c & cpc' = f1’ >-- (strip_tac >> arw[]) >>
    first_x_assum irule >> arw[] >> 
    qexists_tac ‘c’>> rw[]) >> arw[] >>
 rpt strip_tac >> rw[IdL,o_assoc] >>
 first_x_assum (qsspecl_then [‘f’,‘G o f’] assume_tac) >>
 fs[] >>
 first_x_assum (qsspecl_then [‘c1’,‘c2’] assume_tac) >>
 fs[dom_o,cod_o] >> rfs[] >>
 qby_tac ‘G o c1 = G o c1 & f1 = cpc1’ 
 >-- (first_x_assum irule >> arw[] >>
     qexists_tac ‘c1’ >> rw[]) >>
 qby_tac ‘G o c2 = G o c2 & f2 = cpc2’ 
 >-- (first_x_assum irule >> arw[] >>
     qexists_tac ‘c2’ >> rw[]) >>
 fs[])
(form_goal
 “∀X A F:X->A G:A->X. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∀a:1->A x1:1->X f1:2->A x2:1->X f2:2->A. 
   cod(f1) = a ∧ U(x1,f1) &
   cod(f2) = a ∧ U(x2,f2) ⇒ x1 = x2 & f1 = f2) & 
  (!(a : fun(2, A))  (b : fun(2, X)).
          (!(a1 : fun(1, A))  (a2 : fun(1, A)).
              dom(a) = a1 & cod(a) = a2 ==>
              ?(f1 : fun(2, A))  (f2 : fun(2, A)).
                dom(f1) = F o dom(b) &
                cod(f1) = a1 &
                dom(f2) = F o cod(b) &
                cod(f2) = a2 &
                U(dom(b), f1) & U(cod(b), f2) & f2 @ F o b = a @ f1) ⇔ G o a = b) ⇒
  ∃ε:A->Exp(2,A).
  Nt(ε, F o G,Id(A)) & 
  ∀a:1->A ca. 
  cod(ca) = a ∧ U(G o a,ca) ⇔ ca = cpnt(ε,a)”));


(*
cod_cpnt_cod_csB
cs_of_Nt
Nt_def
*)

val Nt_dom_cod_cpnt = prove_store("Nt_dom_cod_cpnt",
e0
(cheat)
(form_goal
 “∀A B F1:A->B F2:A->B η:A->Exp(2,B).
  Nt(η,F1,F2) ⇒
  ∀a:1->A. dom(cpnt(η,a)) = F1 o a & 
   cod(cpnt(η,a)) = F2 o a”));
 
val Nt_natural_dom_cod = prove_store("Nt_natural_dom_cod",
e0
(rpt strip_tac >>
 drule $ GSYM cs_of_Nt >>
 arw[] >> 
 first_x_assum (qspecl_then [‘f’] assume_tac) >>
 rfs[] >> rw[cs_comm])
(form_goal
 “∀A B F1:A->B F2:A->B η:A->Exp(2,B).
  Nt(η,F1,F2) ⇒
 ∀f:2-> A a1 a2. dom(f) = a1 & cod(f) = a2 ⇒
 cpnt(η,a2) @ F1 o f = (F2 o f) @ cpnt(η,a1)
 ”));

val Thm13_eta_ex = prove_store("Thm13_eta_ex",
e0
(rpt strip_tac >>
 match_mp_tac
 (Nt_compr_uex |> qsspecl [‘Id(X)’,‘G:A->X o F:X->A’] 
 |> fVar_sInst_th “P(x:1->X,cx:2->X)”
    “dom(cx:2->X) = x:1->X & cod(cx) = G:A->X o F:X->A o x & 
     cpnt(ε:A -> Exp(2,A),F o x) @ (F o cx) = id(F o x)”) >>
 qby_tac
 ‘!(c : fun(1, X))  (cpc : fun(2, X)).
                 dom(cpc) = c &
                 cod(cpc) = G o F o c &
                 cpnt(ε, (F o c)) @ F o cpc = id(F o c) ==>
                 dom(cpc) = Id(X) o c & cod(cpc) = (G o F) o c ’
 >-- (rpt gen_tac >> strip_tac >> arw[IdL,o_assoc]) >> 
 arw[] >>
 qby_tac
 ‘!(c : fun(1, X)).
                 ?!(cpc : fun(2, X)).
                   dom(cpc) = c &
                   cod(cpc) = G o F o c &
                   cpnt(ε, (F o c)) @ F o cpc = id(F o c)’
 >-- (strip_tac >> 
     first_x_assum 
     (qsspecl_then [‘F o c’,‘cpnt(ε,F o c)’] assume_tac) >>
     fs[] >> 
     last_x_assum drule >>
     drule $ iffLR UFrom_def >>
     pop_assum strip_assume_tac >>
     first_x_assum 
     (qsspecl_then [‘c’,‘id(F o c)’] assume_tac) >>
    fs[id_dom,id_cod] >> 
    drule Nt_dom_cod_cpnt >>
    fs[IdL] (*directly given by def of UFrom, do not need to expand uex*))  >> arw[] >>
 rpt strip_tac >> 
 rw[o_assoc,IdL] >>
 qsuff_tac
 ‘cpnt(ε,F o c2) @ (F o (cpc2 @ f)) = F o f & 
  cpnt(ε,F o c2) @ (F o ((G o F o f) @ cpc1)) = F o f’
 >-- (strip_tac >>
     first_assum 
     (qspecl_then [‘F o c2’,‘cpnt(ε, F o c2)’] assume_tac) >>
     fs[] >>
     last_x_assum drule >>
     drule $ iffLR UFrom_def >> 
     pop_assum strip_assume_tac >>
     pop_assum 
     (qspecl_then [‘c1’,‘F o f’] assume_tac) >>
     fs[dom_o,cod_o] >> rfs[] >>
     assume_tac
     (uex_unique
     |> qspecl [‘2’,‘X’]
     |> fVar_sInst_th “P(fh:2->X)”
        “dom(fh:2->X) = c1 &
         cod(fh:2->X) = G o F o c2 & 
         cpnt(ε:A -> Exp(2,A), (F:X->A o c2)) @ F o fh = 
         F o f” ) >>
     first_x_assum drule >>
     first_x_assum irule >> arw[] >>
     qby_tac ‘cpsb(cpc2,f)’ 
     >-- arw[cpsb_def] >>
     drule oa_dom_cod >> arw[] >>
     qby_tac ‘cpsb(G o F o f,cpc1)’ 
     >-- arw[cpsb_def,dom_o] >> 
     drule oa_dom_cod >> arw[] >>
     arw[cod_o]) >>
 strip_tac (* 2 *)
 >-- (qby_tac ‘cpsb(cpc2,f)’ 
     >-- arw[cpsb_def] >> 
     drule fun_pres_oa >>
     arw[] >>
     qby_tac ‘cpnt(ε, (F o c2)) @ (F o cpc2) @ F o f = 
     (cpnt(ε, (F o c2)) @ (F o cpc2)) @ F o f’
     >-- (flip_tac >> irule Thm8 >> strip_tac (* 2 *)
         >-- (irule cpsb_o >> arw[]) >>
         arw[dom_o,cod_o,cpsb_def]  >>
         drule Nt_dom_cod_cpnt >>
         arw[o_assoc]) >> 
     arw[] >>
     irule cpsb_idL >>
     arw[cpsb_def,id_dom,dom_o,cod_o]) >>
 qby_tac ‘cpsb(G o F o f, cpc1)’ 
 >-- arw[cpsb_def,dom_o] >>
 drule fun_pres_oa >> arw[] >> 
 qby_tac
 ‘cpnt(ε, (F o c2)) @ (F o G o F o f) =
  (F o f) @ cpnt(ε, F o c1)’ 
 >-- (drule Nt_natural_dom_cod >>
     fs[IdL,o_assoc] >> 
     first_x_assum irule >>
     arw[dom_o,cod_o]) >>
 qby_tac 
 ‘cpnt(ε, (F o c2)) @ (F o G o F o f) @ F o cpc1 = 
  (cpnt(ε, (F o c2)) @ (F o G o F o f)) @ F o cpc1’
 >-- (flip_tac >> irule Thm8 >>
     arw[cpsb_def,dom_o,cod_o] >>
     drule Nt_dom_cod_cpnt >> arw[o_assoc]) >>
 arw[] >> 
 qby_tac
 ‘((F o f) @ cpnt(ε, F o c1)) @ F o cpc1 =
  (F o f) @ cpnt(ε, F o c1) @ F o cpc1’
 >-- (irule Thm8 >>
     arw[dom_o,cod_o,cpsb_def] >>
     drule Nt_dom_cod_cpnt >> arw[o_assoc,IdL]) >>
 arw[] >>
 irule cpsb_idR >> rw[cpsb_def,id_cod,dom_o] >>
 arw[])
(form_goal
 “∀X A F:X->A G:A->X ε:A->Exp(2,A). 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∀a:1->A x1:1->X f1:2->A x2:1->X f2:2->A. 
   cod(f1) = a ∧ U(x1,f1) &
   cod(f2) = a ∧ U(x2,f2) ⇒ x1 = x2 & f1 = f2) & 
  (!(a : fun(2, A))  (b : fun(2, X)).
          (!(a1 : fun(1, A))  (a2 : fun(1, A)).
              dom(a) = a1 & cod(a) = a2 ==>
              ?(f1 : fun(2, A))  (f2 : fun(2, A)).
                dom(f1) = F o dom(b) &
                cod(f1) = a1 &
                dom(f2) = F o cod(b) &
                cod(f2) = a2 &
                U(dom(b), f1) & U(cod(b), f2) & f2 @ F o b = a @ f1) ⇔ G o a = b) &
  (Nt(ε, F o G,Id(A)) & 
  ∀a:1->A ca. 
  cod(ca) = a ∧ U(G o a,ca) ⇔ ca = cpnt(ε,a)) ⇒
  ∃η:X -> Exp(2,X). 
   Nt(η, Id(X), G o F) &
   ∀x:1->X cx. 
   dom(cx) = x & cod(cx) = G o F o x & 
   cpnt(ε,F o x) @ (F o cx) = id(F o x) ⇔
   cx = cpnt(η,x)
   ”));


val Thm13_G_epsilon_eta = prove_store("Thm13_G_epsilon_eta",
e0
(rpt strip_tac >>
 qpick_x_assum
 ‘(!(a : fun(2, A))  (b : fun(2, X)).
          (!(a1 : fun(1, A))  (a2 : fun(1, A)).
              (dom(a) = a1 & cod(a) = a2 ==>
              ?(f1 : fun(2, A))  (f2 : fun(2, A)).
                dom(f1) = F o dom(b) &
                cod(f1) = a1 &
                dom(f2) = F o cod(b) &
                cod(f2) = a2 &
                U(dom(b), f1) & U(cod(b), f2) & f2 @ F o b = a @ f1)) ⇔ G o a = b)’ (assume_tac o GSYM) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     first_x_assum (qspecl_then [‘a1’,‘a2’] assume_tac) >>
     rfs[] >> 
     qexistsl_tac [‘cpnt(ε,a1)’,‘cpnt(ε,a2)’] >>
     arw[]) >>
 rpt gen_tac >> strip_tac >>
 first_x_assum (qspecl_then [‘a1’,‘a2’] assume_tac) >>
 rfs[] >>
 qsuff_tac
 ‘cpnt(ε, a1) = f1 & cpnt(ε, a2) = f2’
 >-- (strip_tac >> arw[]) >>
 strip_tac (* 2 *)
 >-- (first_x_assum 
     (qsspecl_then [‘a1’,‘cpnt(ε,a1)’] assume_tac) >>
     qby_tac
     ‘cod(cpnt(ε, a1)) = a1 & U(G o a1, cpnt(ε, a1))’
     >-- (once_arw[] >> rw[]) >>
     qpick_x_assum ‘cod(cpnt(ε, a1)) = a1 & U(G o a1, cpnt(ε, a1)) <=>
             cpnt(ε, a1) = cpnt(ε, a1)’ (K all_tac) >>
     (*if instead of pick x assum us fs then seems to loop*)
     pop_assum strip_assume_tac >>
     qsuff_tac
     ‘G o a1 = dom(b) & cpnt(ε, a1) = f1’
     >-- (strip_tac >> arw[]) >> 
     first_x_assum irule >> arw[] >>
     qexists_tac ‘a1’ >> rw[]) >> 
 first_x_assum 
 (qsspecl_then [‘a2’,‘cpnt(ε,a2)’] assume_tac) >>
 qby_tac
 ‘cod(cpnt(ε, a2)) = a2 & U(G o a2, cpnt(ε, a2))’
 >-- (once_arw[] >> rw[]) >>
 qpick_x_assum 
 ‘cod(cpnt(ε, a2)) = a2 & U(G o a2, cpnt(ε, a2)) <=>
             cpnt(ε, a2) = cpnt(ε, a2)’ (K all_tac) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘G o a2 = cod(b) & cpnt(ε, a2) = f2’
 >-- (strip_tac >> arw[]) >> 
 first_x_assum irule >> arw[] >>
 qexists_tac ‘a2’ >> rw[]  
 )
(form_goal
 “∀X A F:X->A G:A->X ε:A->Exp(2,A) η:X -> Exp(2,X). 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∀a:1->A x1:1->X f1:2->A x2:1->X f2:2->A. 
   cod(f1) = a ∧ U(x1,f1) &
   cod(f2) = a ∧ U(x2,f2) ⇒ x1 = x2 & f1 = f2) & 
  (!(a : fun(2, A))  (b : fun(2, X)).
          (!(a1 : fun(1, A))  (a2 : fun(1, A)).
              (dom(a) = a1 & cod(a) = a2 ==>
              ?(f1 : fun(2, A))  (f2 : fun(2, A)).
                dom(f1) = F o dom(b) &
                cod(f1) = a1 &
                dom(f2) = F o cod(b) &
                cod(f2) = a2 &
                U(dom(b), f1) & U(cod(b), f2) & f2 @ F o b = a @ f1)) ⇔ G o a = b) &
  (Nt(ε, F o G,Id(A)) & 
  ∀a:1->A ca. 
  cod(ca) = a ∧ U(G o a,ca) ⇔ ca = cpnt(ε,a)) &
   Nt(η, Id(X), G o F) &
   (∀x:1->X cx. 
   dom(cx) = x & cod(cx) = G o F o x & 
   cpnt(ε,F o x) @ (F o cx) = id(F o x) ⇔
   cx = cpnt(η,x)) ⇒ 
  !(a : fun(2, A))  (b : fun(2, X)).
          (!(a1 : fun(1, A))  (a2 : fun(1, A)).
              dom(a) = a1 & cod(a) = a2 ==>
                dom(cpnt(ε,a1)) = F o dom(b) &
                cod(cpnt(ε,a1)) = a1 &
                dom(cpnt(ε,a2)) = F o cod(b) &
                cod(cpnt(ε,a2)) = a2 &
                U(dom(b), cpnt(ε,a1)) &
                U(cod(b), cpnt(ε,a2)) & 
                cpnt(ε,a2) @ F o b = a @ cpnt(ε,a1)) ⇔ G o a = b
 ”));



val Thm13_G_epsilon_eta_ex = 
prove_store("Thm13_G_epsilon_eta_ex",
e0
(cheat
 )
(form_goal
 “∀X A F:X->A. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∀a:1->A x1:1->X f1:2->A x2:1->X f2:2->A. 
   cod(f1) = a ∧ U(x1,f1) &
   cod(f2) = a ∧ U(x2,f2) ⇒ x1 = x2 & f1 = f2) ⇒
  ∃G:A->X ε:A->Exp(2,A) η:X -> Exp(2,X).
  (!(a : fun(2, A))  (b : fun(2, X)).
          (!(a1 : fun(1, A))  (a2 : fun(1, A)).
              dom(a) = a1 & cod(a) = a2 ==>
                dom(cpnt(ε,a1)) = F o dom(b) &
                cod(cpnt(ε,a1)) = a1 &
                dom(cpnt(ε,a2)) = F o cod(b) &
                cod(cpnt(ε,a2)) = a2 &
                U(dom(b), cpnt(ε,a1)) &
                U(cod(b), cpnt(ε,a2)) & 
                cpnt(ε,a2) @ F o b = a @ cpnt(ε,a1)) ⇔ G o a = b) &
  (Nt(ε, F o G,Id(A)) & 
  ∀a:1->A ca. 
  cod(ca) = a ∧ U(G o a,ca) ⇔ ca = cpnt(ε,a)) &
   Nt(η, Id(X), G o F) &
   (∀x:1->X cx. 
   dom(cx) = x & cod(cx) = G o F o x & 
   cpnt(ε,F o x) @ (F o cx) = id(F o x) ⇔
   cx = cpnt(η,x)) ”));


val cpnt_o_Rw = prove_store("cpnt_o_Rw",
e0
(rpt strip_tac >> rw[cpnt_def] >> rw[Pt_def] >>
 rw[o_assoc,p12_of_Pa,Pa_distr] >>
 rw[Rw_def,Ec_def] >>  
rw[Ev_of_Tp_el,Pa_distr,o_assoc])
(form_goal
 “∀A B η a C F.F:B->C o cpnt(η:A->Exp(2,B),a:1->A) = 
  cpnt(Rw(F,η),a)”));


val cpnt_o_Lw = prove_store("cpnt_o_Lw",
e0
(rpt strip_tac >> rw[cpnt_def] >> rw[Pt_def] >>
 rw[o_assoc,p12_of_Pa,Pa_distr] >>
 rw[Lw_def,Ec_def] >> rw[o_assoc])
(form_goal
 “∀A B C η a F.cpnt(η:B->Exp(2,C),F o a:1->A) = 
  cpnt(Lw(η,F),a)”));


val Nt_vo_cpnt = prove_store("Nt_vo_cpnt",
e0
(rpt strip_tac >>
 irule vo_cpnt >> fs[Nt_def] >>
 fs[csL_Pt_Ed,csR_Pt_Ed] >> 
 irule $ iffLR Er1_eq_eq >>
 irule $ iffLR fun_ext >> strip_tac >>
 arw[o_assoc])
(form_goal
 “∀A B F1:A->B F2:A->B F3:A->B η1:A->Exp(2,B) η2:A->Exp(2,B).
  Nt(η1,F1,F2) & Nt(η2,F2,F3) ⇒
  ∀a:1->A. 
  cpnt(vo(η2, η1), a) = cpnt(η2, a) @ cpnt(η1, a)”));

val Thm13_ex = prove_store("Thm13_ex",
e0
(rpt strip_tac >>
 qby_tac
 ‘ ∃G:A->X ε:A->Exp(2,A) η:X -> Exp(2,X).
  (!(a : fun(2, A))  (b : fun(2, X)).
          (!(a1 : fun(1, A))  (a2 : fun(1, A)).
              dom(a) = a1 & cod(a) = a2 ==>
                dom(cpnt(ε,a1)) = F o dom(b) &
                cod(cpnt(ε,a1)) = a1 &
                dom(cpnt(ε,a2)) = F o cod(b) &
                cod(cpnt(ε,a2)) = a2 &
                U(dom(b), cpnt(ε,a1)) &
                U(cod(b), cpnt(ε,a2)) & 
                cpnt(ε,a2) @ F o b = a @ cpnt(ε,a1)) ⇔ G o a = b) &
  (Nt(ε, F o G,Id(A)) & 
  ∀a:1->A ca. 
  cod(ca) = a ∧ U(G o a,ca) ⇔ ca = cpnt(ε,a)) &
   Nt(η, Id(X), G o F) &
   (∀x:1->X cx. 
   dom(cx) = x & cod(cx) = G o F o x & 
   cpnt(ε,F o x) @ (F o cx) = id(F o x) ⇔
   cx = cpnt(η,x))’ 
 >-- (irule Thm13_G_epsilon_eta_ex >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘G’,‘η’,‘ε’] >>
 qby_tac
 ‘!(a : fun(1, A)). cod(cpnt(ε, a)) = a & 
  U(G o a, cpnt(ε, a))’
 >-- arw[] >> arw[] >>
 irule Adj_alt1 >> arw[] >>
 qby_tac
 ‘∀x. cpnt(vo(Lw(ε, F), Rw(F, η)), x) = id(F o x)’
 >-- (strip_tac >>
     drule Nt_Rw_Nt >>
     first_x_assum (qsspecl_then [‘F’] assume_tac) >> 
     pop_assum mp_tac >> rw[IdR,o_assoc] >> strip_tac >>
     rev_drule Nt_Lw_Nt >>
     first_x_assum (qsspecl_then [‘F’] assume_tac) >>
     pop_assum mp_tac >> rw[IdL,o_assoc] >> strip_tac >>
     qsspecl_then [‘F’,‘F o G o F’,‘F’,‘Rw(F,η)’,‘Lw(ε,F)’] 
     assume_tac vo_Nt_Nt >> rfs[] >>
     qsspecl_then [‘F’,‘F o G o F’,‘F’,‘Rw(F,η)’,‘Lw(ε,F)’] 
     assume_tac Nt_vo_cpnt >>
     rfs[] >>
     rw[GSYM cpnt_o_Lw,GSYM cpnt_o_Rw] >>
     first_x_assum
     (qsspecl_then [‘x’,‘cpnt(η,x)’] assume_tac) >>
     pop_assum mp_tac >> rw[] >> strip_tac >> arw[])>> 
 arw[] >> strip_tac >> 
 drule Nt_Lw_Nt >>
 first_x_assum (qsspecl_then [‘G’] assume_tac) >> 
 pop_assum mp_tac >> rw[IdL,o_assoc] >> strip_tac >>
 rev_drule Nt_Rw_Nt >>
 first_x_assum (qsspecl_then [‘G’] assume_tac) >>
 pop_assum mp_tac >> rw[IdR,o_assoc] >> strip_tac >>
 qsspecl_then 
 [‘G o F o G’,‘G’,‘G o F o G’,‘Rw(G,ε)’,‘Lw(η,G)’] 
 assume_tac Nt_vo_cpnt >> 
(*
 qby_tac
 ‘!(a : fun(1, X)).
               cpnt(vo(Lw(ε, F), Rw(F, η)), a) = cpnt(Lw(ε, F), a) @
                 cpnt(Rw(F, η), a)’
 >-- *)
 qby_tac
 ‘cpnt(vo(Rw(G, ε), Lw(η, G)), a) = 
  cpnt(Rw(G, ε),a) @ cpnt(Lw(η, G), a)’ 
 >-- (irule Nt_vo_cpnt >>
     qexistsl_tac [‘G’,‘G o F o G’,‘G’] >>
     arw[]) >> arw[] >>
 first_x_assum (qsspecl_then [‘a’,‘cpnt(ε,a)’] assume_tac) >>
 pop_assum mp_tac >> rw[] >>
 strip_tac >>
 last_assum drule >>
 qby_tac ‘cpsb(cpnt(Rw(G, ε), a),cpnt(Lw(η, G), a))’ 
 >-- (rw[cpsb_def] >> 
     drule Nt_dom_cod_cpnt >> arw[o_assoc] >>
 qsspecl_then [‘G’,‘G o F o G’,‘Lw(η,G)’]
 assume_tac Nt_dom_cod_cpnt >> 
 first_x_assum drule >> arw[o_assoc]) >>
 qsuff_tac
 ‘cpnt(ε,a) @ 
  (F o (cpnt(Rw(G, ε), a) @ cpnt(Lw(η, G), a))) = 
  cpnt(ε,a)’
 >-- (strip_tac >> 
     drule $ iffLR UFrom_def >>
     pop_assum strip_assume_tac >> 
     first_x_assum 
     (qsspecl_then [‘G o a’,‘cpnt(ε,a)’] assume_tac) >>
     rfs[] >> assume_tac
     (uex_unique |> qspecl [‘2’,‘X’] 
     |> fVar_sInst_th “P(fh:2->X)”
        “dom(fh:2->X) = G:A->X o a &
         cod(fh) = G o a & 
         cpnt(ε, a) @ F:X->A o fh = cpnt(ε, a)”) >>
     first_x_assum drule >>
     first_x_assum irule >>
     rw[id_dom,id_cod] >> arw[] >> 
     qby_tac ‘cpnt(ε, a) @ F o id(G o a) = cpnt(ε, a)’ 
     >-- (rw[id_def,o_assoc] >> rw[GSYM o_assoc] >>
         rw[GSYM id_def] >> rw[o_assoc] >>
         irule cpsb_idR >> arw[cpsb_def] >>
         rw[id_cod]) >> arw[] >> 
     drule oa_dom_cod  >> arw[] >>
     rw[GSYM cpnt_o_Lw,GSYM cpnt_o_Rw] >>
     rw[cod_o] >> 
     qsspecl_then [‘Id(X)’,‘G o F’,‘η’] 
     assume_tac Nt_dom_cod_cpnt >>
     first_x_assum drule >> arw[o_assoc,IdL]) >>
rev_drule Nt_natural_dom_cod >>
first_x_assum 
 (qsspecl_then [‘cpnt(ε,a)’,‘F o G o a’,‘a’] assume_tac) >>
rfs[] >>
qby_tac ‘dom(cpnt(ε, a)) = F o G o a’ 
>-- rev_drule Nt_dom_cod_cpnt >> arw[o_assoc] >>
first_x_assum drule >>
pop_assum mp_tac >> rw[o_assoc,IdL] >> strip_tac >>
qby_tac
‘cpnt(ε, F o G o a) @ (F o cpnt(η,G o a)) = id(F o G o a)’
>-- (first_x_assum (qspecl_then [‘G o a’] assume_tac) >>
     qsspecl_then [‘F’,‘F o G o F’,‘F’,‘Rw(F, η)’,‘Lw(ε, F)’] assume_tac Nt_vo_cpnt >>
     qby_tac
     ‘Nt(Rw(F, η), F, F o G o F) &
      Nt(Lw(ε, F), F o G o F, F)’
     >-- (rev_drule Nt_Lw_Nt >> pop_assum mp_tac >> 
         rw[IdL,o_assoc] >>
         strip_tac >> arw[] >>
         qsspecl_then [‘Id(X)’,‘G o F’,‘η’] assume_tac
         Nt_Rw_Nt >>
         first_x_assum drule >> 
         pop_assum mp_tac >> rw[IdR] >>
         strip_tac >> arw[]) >> 
    first_x_assum drule >>
    fs[] >> 
    fs[GSYM cpnt_o_Lw] >> fs[GSYM cpnt_o_Rw]) >>
drule fun_pres_oa >> arw[] >>
drule cpsb_o >>
first_x_assum (qsspecl_then [‘F’] assume_tac) >>
qby_tac
‘cpnt(ε, a) @ (F o cpnt(Rw(G, ε), a)) @ F o cpnt(Lw(η, G), a) = 
 (cpnt(ε, a) @ (F o cpnt(Rw(G, ε), a))) @ F o cpnt(Lw(η, G), a)’
>-- (flip_tac >> irule Thm8 >> arw[] >>
     rw[cpsb_def,cod_o] >> 
     drule Nt_dom_cod_cpnt >> arw[o_assoc]) >>
arw[] >> arw[GSYM cpnt_o_Rw] >>
qby_tac
‘(cpnt(ε, a) @ cpnt(ε, F o G o a)) @ F o cpnt(Lw(η, G), a) =
 cpnt(ε, a) @ cpnt(ε, F o G o a) @ F o cpnt(Lw(η, G), a)’
>-- (irule Thm8 >> arw[cpsb_def,dom_o,cod_o] >>
     qsspecl_then [‘G’,‘G o F o G’,‘Lw(η,G)’] assume_tac 
     Nt_dom_cod_cpnt >>
     first_x_assum drule >> arw[o_assoc] >>
     rev_drule Nt_dom_cod_cpnt  >> arw[o_assoc]) >>
arw[GSYM cpnt_o_Lw] >>
irule cpsb_idR >> 
rw[cpsb_def] >>
rev_drule Nt_dom_cod_cpnt >> arw[o_assoc,id_cod])
(form_goal
 “∀X A F:X->A. 
  (∀x:1->X f:2->A. U(x,f) ⇒ UFrom(F,cod(f),x,f)) ∧
  (∀a:1->A. ∃x:1->X f:2->A. cod(f) = a ∧ U(x,f)) &
  (∀a:1->A x1:1->X f1:2->A x2:1->X f2:2->A. 
   cod(f1) = a ∧ U(x1,f1) &
   cod(f2) = a ∧ U(x2,f2) ⇒ x1 = x2 & f1 = f2) ⇒
  ∃G:A->X η ε:A->Exp(2,A). Adj(F,G,η,ε) ∧
   ∀a:1->A. cod(cpnt(ε,a)) = a ∧ U(G o a,cpnt(ε,a))”));


