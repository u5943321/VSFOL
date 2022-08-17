val Id0_def = qdefine_fsym("Id0",[‘A’])
‘Er1(A) o Ed(0f,A)’

val Id1_def = qdefine_fsym("Id1",[‘A’])
‘Er1(A) o Ed(1f,A)’


val icat_Pb= prove_store("icat_Pb",
e0
(rw[Id1_def,Id0_def] >>
 assume_tac Ed_ab_Pb0 >>
 first_x_assum (qspecl_then [‘A’] assume_tac) >>
 fs[isPb_def] >> arw[o_assoc,Er1_eq_eq])
(form_goal “isPb(Id1(A), Id0(A), Ed(α, A), Ed(β, A))”));


val pb2tri_tri2pb_ex = proved_th $
e0
(qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
 assume_tac icat_Pb >>
 rev_drule isPb_unique' >>
 first_x_assum drule >> arw[])
(form_goal
 “?pb2tri: Pbo(Id1(A),Id0(A)) -> Exp(3,A)
   tri2pb:Exp(3,A)-> Pbo(Id1(A),Id0(A)).
  pb2tri o tri2pb = Id(Exp(3,A)) &
  tri2pb o pb2tri = Id(Pbo(Id1(A),Id0(A))) &
  Ed(α,A) o pb2tri = Pba1(Id1(A),Id0(A)) &
  Ed(β,A) o pb2tri = Pba2(Id1(A),Id0(A)) &
  Pba1(Id1(A),Id0(A)) o tri2pb = Ed(α,A) &
  Pba2(Id1(A),Id0(A)) o tri2pb = Ed(β,A)
  ”)



val pb2tri_uex = proved_th $
e0
(assume_tac icat_Pb >>
 drule Pb12_eq_eq >>
 qsuff_tac
 ‘?pb2tri: Pbo(Id1(A),Id0(A)) -> Exp(3,A).
   ?tri2pb:Exp(3,A)-> Pbo(Id1(A),Id0(A)).
  pb2tri o tri2pb = Id(Exp(3,A)) &
  tri2pb o pb2tri = Id(Pbo(Id1(A),Id0(A))) &
  Ed(α,A) o pb2tri = Pba1(Id1(A),Id0(A)) &
  Ed(β,A) o pb2tri = Pba2(Id1(A),Id0(A)) &
  Pba1(Id1(A),Id0(A)) o tri2pb = Ed(α,A) &
  Pba2(Id1(A),Id0(A)) o tri2pb = Ed(β,A)’
 >-- (strip_tac >> uex_tac >>
     qexistsl_tac [‘pb2tri’] >> rpt strip_tac (* 2 *)
     >-- (qexists_tac ‘tri2pb’ >> arw[]) >>
     first_x_assum irule >> arw[]) >>
 rw[pb2tri_tri2pb_ex])
(form_goal
 “?!pb2tri: Pbo(Id1(A),Id0(A)) -> Exp(3,A).
   ?tri2pb:Exp(3,A)-> Pbo(Id1(A),Id0(A)).
  pb2tri o tri2pb = Id(Exp(3,A)) &
  tri2pb o pb2tri = Id(Pbo(Id1(A),Id0(A))) &
  Ed(α,A) o pb2tri = Pba1(Id1(A),Id0(A)) &
  Ed(β,A) o pb2tri = Pba2(Id1(A),Id0(A)) &
  Pba1(Id1(A),Id0(A)) o tri2pb = Ed(α,A) &
  Pba2(Id1(A),Id0(A)) o tri2pb = Ed(β,A)
  ”)
|> qsimple_uex_spec "pb2tri" [‘A’]


val tri2pb_def = proved_th $
e0
(qsuff_tac
 ‘?tri2pb:Exp(3,A)-> Pbo(Id1(A),Id0(A)).
  pb2tri(A) o tri2pb = Id(Exp(3,A)) &
  tri2pb o pb2tri(A) = Id(Pbo(Id1(A),Id0(A))) &
  Ed(α,A) o pb2tri(A) = Pba1(Id1(A),Id0(A)) &
  Ed(β,A) o pb2tri(A) = Pba2(Id1(A),Id0(A)) &
  Pba1(Id1(A),Id0(A)) o tri2pb = Ed(α,A) &
  Pba2(Id1(A),Id0(A)) o tri2pb = Ed(β,A)’
 >-- (strip_tac >> uex_tac >>
     qexists_tac ‘tri2pb’ >> arw[] >>
     rpt strip_tac >> irule Pba12_eq_eq >> arw[]) >>
 rw[pb2tri_uex])
(form_goal
 “?!tri2pb:Exp(3,A)-> Pbo(Id1(A),Id0(A)).
  pb2tri(A) o tri2pb = Id(Exp(3,A)) &
  tri2pb o pb2tri(A) = Id(Pbo(Id1(A),Id0(A))) &
  Ed(α,A) o pb2tri(A) = Pba1(Id1(A),Id0(A)) &
  Ed(β,A) o pb2tri(A) = Pba2(Id1(A),Id0(A)) &
  Pba1(Id1(A),Id0(A)) o tri2pb = Ed(α,A) &
  Pba2(Id1(A),Id0(A)) o tri2pb = Ed(β,A)
  ”)
|> qsimple_uex_spec "tri2pb" [‘A’]



val Ir_def = qdefine_fsym("Ir",[‘A’])
‘Ed(γ,A) o pb2tri(A)’


val Ii_def = qdefine_fsym("Ii",[‘A’])
‘Tp(p2(2,A))’



val is_irt = proved_th $
e0
(rpt strip_tac >> assume_tac irt_def >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >> first_x_assum irule >>
 arw[])
(form_goal
 “∀A B η:A->Exp(2,B) ε:A -> Exp(2,B).
  Ed(1f,B) o η = Ed(0f,B) o ε ⇒
  (∀a'. Ed(α,B) o a' = η & Ed(β,B) o a' = ε ⇒
   a' = irt(η,ε))”)

val tri2pb_eqns = tri2pb_def;


val Ed1_Ii_Tp_p2 = prove_store("Ed1_Ii_Tp_p2",
e0
(rw[Ed_def,Ii_def] >> irule Ev_eq_eq >>
 rw[Ev_of_Tp_el,o_assoc] >> rw[Pa_distr,p12_of_Pa,o_assoc]>>
rw[Ev_of_Tp_el,p12_of_Pa])
(form_goal “Ed(1f, A) o Ii(A) = Tp(p2(1, A))”));


val Ed1_Ii_Er_Id = prove_store("Ed1_Ii_Er_Id",
e0
(rw[GSYM o_assoc,Ed1_Ii_Tp_p2,Er1_inv])
(form_goal “Ed(1f, A) o Ii(A) o Er1(A) = Id(Exp(1,A))”));


val Ed_Ii = prove_store("Ed_Ii",
e0
(qsspecl_then [‘Id(A)’,‘Id0(A)’] assume_tac Pb_def >>
 fs[isPb_def] >>
 fs[Id0_def,IdL] >> rw[o_assoc] >>
 qsuff_tac
 ‘(Ed(1f, A) o Ii(A) o Er1(A)) o Ed(0f, A) o Pba2(Id(A), Id0(A)) = Ed(0f, A) o
               Pba2(Id(A), Id0(A))’ >-- rw[o_assoc] >>
 rw[Ed1_Ii_Er_Id,IdL])
(form_goal
 “Ed(1f, A) o Ii(A) o Pba1(Id(A), Id0(A)) =
  Ed(0f, A) o Pba2(Id(A), Id0(A))”));


val Ii_Id0_ID = prove_store("Ii_Id0_ID",
e0
(rw[ID_def,Ii_def,Id0_def] >>
irule Ev_eq_eq >> rw[o_assoc,Ev_of_Tp_el] >>
rw[Swap_Pa,p12_of_Pa] >> rw[Er1_def,Ed_def] >>
rw[Pt_def,o_assoc,p12_of_Pa,Pa_distr,Ev_of_Tp_el,To1_def] >>
rw[IdL,Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa,Pa_distr] >>
rw[To1_def] >> rw[id_def,GSYM Tp1_def,Ev_of_Tp_el] >>
rw[o_assoc,Ev_of_Tp_el] >> rw[p12_of_Pa,Pa_distr,o_assoc] >>
rw[To1_def])
(form_goal
“Ii(A) o Id0(A) o a = ID(Er1(A) o Ed(0f, A) o a:2->Exp(2,A))”
));



val Dom_def = qdefine_fsym("Dom",[‘η:A -> Exp(2,B)’])
‘Er1(B) o Ed(0f, B) o η’

val Cod_def = qdefine_fsym("Cod",[‘η:A -> Exp(2,B)’])
‘Er1(B) o Ed(1f, B) o η’

val Id0_Dom = prove_store("Id0_Dom",
e0
(rw[Dom_def,Id0_def,o_assoc])
(form_goal
“∀A B G:A -> Exp(2,B).Id0(B) o G = Dom(G)”));


val Id1_Cod = prove_store("Id1_Cod",
e0
(rw[Cod_def,Id1_def,o_assoc])
(form_goal
“∀A B G:A -> Exp(2,B).Id1(B) o G = Cod(G)”));

val Nt_Dom_Cod = prove_store("Nt_Dom_Cod",
e0
(rw[Dom_def,Cod_def,all_Nt])
(form_goal “∀A B η:A -> Exp(2,B). Nt(η,Dom(η),Cod(η))”));


val Sq_def = qdefine_fsym("Sq",[‘F:A->B’])
‘Tp(F o Ev(2,A))’

val Id0_Sq = prove_store("Id0_Sq",
e0
(rw[Id0_def,Sq_def,Er1_def,Ed_def,o_assoc,Pa_distr,p12_of_Pa] >>
rw[IdL,To1_def] >> rw[Ev_of_Tp_el] >>
rw[Ev_of_Tp_el'] >>
rw[o_assoc,Pa_distr,p12_of_Pa,Ev_of_Tp_el] >>
rw[To1_def] >> rw[Ev_of_Tp_el'] >> rw[o_assoc] )
(form_goal “Id0(B) o Sq(F) = F o Id0(A)”));


val Id1_Sq = prove_store("Id1_Sq",
e0
(rw[Id1_def,Sq_def,Er1_def,Ed_def,o_assoc,Pa_distr,p12_of_Pa] >>
rw[IdL,To1_def] >> rw[Ev_of_Tp_el] >>
rw[Ev_of_Tp_el'] >>
rw[o_assoc,Pa_distr,p12_of_Pa,Ev_of_Tp_el] >>
rw[To1_def] >> rw[Ev_of_Tp_el'] >> rw[o_assoc] )
(form_goal “Id1(B) o Sq(F) = F o Id1(A)”));


val Cr1_Pa_eq_eq = prove_store("Cr1_Pa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘f o Pa(Id(A), To1(A)) o p1(A, 1) =
          g o Pa(Id(A), To1(A)) o p1(A, 1)’
 >-- arw[GSYM o_assoc] >>
 fs[Cr1_iso] >> fs[IdR])
(form_goal “∀A B f:A * 1->B g. f o Pa(Id(A), To1(A)) = g o Pa(Id(A), To1(A)) ⇔ f = g”));


val csR_csT_22 = prove_store("csR_csT_22",
e0
(rw[csR_def,csT_def] >>
assume_tac RT_cs2 >>
assume_tac cs2_RT_cpsb >>
drule fun_pres_oa >> pop_assum (assume_tac o GSYM) >>
arw[])
(form_goal
“∀A cs:2 * 2->A. csR(cs) @ csT(cs) = cs o Pa(𝟚,𝟚)”));


val Id1_csR_Pt = prove_store("Id1_csR_Pt",
e0
(rw[Id1_def] >> rw[o_assoc,GSYM csR_Pt])
(form_goal “Id1(B) o G o a:2->Exp(2,A) = csR(Pt(G o a))”));


val Id0_csL_Pt = prove_store("Id0_csL_Pt",
e0
(rw[Id0_def] >> rw[o_assoc,GSYM csL_Pt])
(form_goal “Id0(B) o G o a:2->Exp(2,A) = csL(Pt(G o a))”));


val On0_Tp0_dom = proved_th $
e0
(rw[csT_Pt_Tp0] >> rw[dom_o])
(form_goal
“∀G:Exp(2,A)->Exp(2,B) a:2->Exp(2,A).
 csT(Pt(G o a)) = Tp0(G o dom(a))”);


val On0_Tp0_cod = proved_th $
e0
(rw[csB_Pt_Tp0] >> rw[cod_o])
(form_goal
“∀G:Exp(2,A)->Exp(2,B) a:2->Exp(2,A).
 csB(Pt(G o a)) = Tp0(G o cod(a))”);


val csL_Pt_o_Dom = proved_th $
e0
(rw[csL_Pt,Dom_def,o_assoc])
(form_goal “csL(Pt(G:Exp(2,A)->Exp(2,B) o cs)) =
 Dom(G:Exp(2,A)->Exp(2,B)) o cs”)


val csR_Pt_o_Cod = proved_th $
e0
(rw[csR_Pt,Cod_def,o_assoc])
(form_goal “csR(Pt(G:Exp(2,A)->Exp(2,B) o cs)) =
 Cod(G:Exp(2,A)->Exp(2,B)) o cs”)

val csL_Pt_o_id = proved_th $
e0
(rw[csL_Pt_o_Dom,id_o])
(form_goal
 “csL(Pt(G:Exp(2,A)->Exp(2,B) o id(Tp1(id(a))))) =
 id(Dom(G) o Tp1(id(a)))”)


val Tp_p2_ob = prove_store("Tp_p2_ob",
e0
(rpt strip_tac >> irule Ev_eq_eq >>
rw[o_assoc,Ev_of_Tp_el] >>
rw[p12_of_Pa,id_def,o_assoc] >> rw[To1_def])
(form_goal
“∀A a:1->A. Tp(p2(2, A)) o a = Tp(id(a) o p1(2, 1))”));

val Ii_ap = prove_store("Ii_ap",
e0
(rpt strip_tac >>
rw[Ii_def,GSYM Tp1_def,Tp_p2_ob])
(form_goal
“∀A a:1->A. Ii(A) o a = Tp1(id(a))”));



val Sq_ob = prove_store("Sq_ob",
e0
(rpt strip_tac >>
 rw[Sq_def,GSYM Tp1_def,GSYM Tp0_def] >>
 irule Ev_eq_eq >> rw[o_assoc,Ev_of_Tp_el] >>
 rw[o_assoc,p12_of_Pa,Pa_distr,IdL,To1_def])
(form_goal “∀A B F:A->B aob:1->Exp(2,A).
 Sq(F) o aob = Tp1(F o Tp0(aob))”));

val Sq_Tp1_id = proved_th $
e0
(rw[Sq_ob,Tp0_Tp1_inv])
(form_goal “∀A B F:A->B a0.Sq(F) o Tp1(id(a0)) =
                                   Tp1(F o id(a0))”)

val Pt_dom_Pa_id_iff = proved_th $
e0
(rw[Pt_def,Tp0_def,o_assoc,p12_of_Pa,Pa_distr] >>
rw[Tp0_iff_Tp1])
(form_goal
“Pt(dom(cs)) o Pa(Id(2), To1(2)) = id(a0:1->A) ⇔
 dom(cs) = Tp1(id(a0))”)


val Dom_Sq_csL_Pt = proved_th $
e0
(rpt strip_tac >> rw[csL_Pt] >> rw[Dom_def] >>
rw[Sq_def,Er1_def,Ed_def] >> rw[o_assoc] >>
rw[Pa_distr,p12_of_Pa,o_assoc] >>
rw[To1_def] >> rw[IdL] >>
rw[Ev_of_Tp_el] >>
rw[o_assoc,Pa_distr,p12_of_Pa] >>
rw[To1_def] >> rw[Ev_of_Tp_el] >> rw[o_assoc])
(form_goal
“∀A B F:A->B cs.Dom(Sq(F)) o cs = F o csL(Pt(cs))”)



val Cod_Sq_csR_Pt = proved_th $
e0
(rpt strip_tac >> rw[csR_Pt] >> rw[Cod_def] >>
rw[Sq_def,Er1_def,Ed_def] >> rw[o_assoc] >>
rw[Pa_distr,p12_of_Pa,o_assoc] >>
rw[To1_def] >> rw[IdL] >>
rw[Ev_of_Tp_el] >>
rw[o_assoc,Pa_distr,p12_of_Pa] >>
rw[To1_def] >> rw[Ev_of_Tp_el] >> rw[o_assoc])
(form_goal
“∀A B F:A->B cs.Cod(Sq(F)) o cs = F o csR(Pt(cs))”)


val Thm24 = prove_store("Thm24",
e0
(rpt strip_tac >>
 irule Nt_ext_cpnt >> fs[IFun_def] >>
 strip_tac (*2  *)
 >-- (qexistsl_tac [‘Dom(G)’,‘Cod(G)’] >>
 rw[Nt_Dom_Cod] >>
 qsspecl_then [‘Sq(F)’] assume_tac Nt_Dom_Cod >>
 qsuff_tac ‘Dom(Sq(F)) = Dom(G) & Cod(Sq(F)) = Cod(G)’
 >-- (strip_tac >> fs[]) >>
 rw[GSYM Id0_Dom,GSYM Id1_Cod] >> arw[]  >>
 rw[Id1_Sq,Id0_Sq]) >>
 strip_tac >>
 qby_tac
 ‘∀a0:1->A. G o Tp1(id(a0)) = Sq(F) o Tp1(id(a0))’
 >-- (rw[GSYM Ii_ap] >>
     qpick_x_assum ‘Ii(B) o F = G o Ii(A)’
     (assume_tac o GSYM) >> arw[GSYM o_assoc] >>
     rw[o_assoc,Ii_ap] >> rw[Sq_Tp1_id,id_o]) >>
 qby_tac
 ‘∀cs:2->Exp(2,A) a0. csT(Pt(cs)) = id(a0) ⇒
  csT(Pt(G o cs)) = F o id(a0)’
 >-- (rw[csT_dom] >> rpt strip_tac >>
     fs[Pt_dom_Pa_id_iff] >> rw[GSYM id_o] >>
     rw[Pt_dom_Pa_id_iff] >>
     rw[dom_o] >> arw[] >>
     rw[Sq_Tp1_id] >> rw[id_o]) >>
 qby_tac
 ‘Dom(Sq(F)) = Dom(G) & Cod(Sq(F)) = Cod(G)’
 >-- (rw[GSYM Id0_Dom,GSYM Id1_Cod] >> arw[]  >>
     rw[Id1_Sq,Id0_Sq]) >>
 pop_assum (strip_assume_tac o GSYM) >>
 qby_tac
 ‘∀cs:2->Exp(2,A) a0. csL(Pt(cs)) = id(a0) ⇒
  csL(Pt(G o cs)) = F o id(a0)’
 >-- (rw[csL_Pt_o_Dom] >> arw[] >>
     rpt strip_tac >> rw[Dom_Sq_csL_Pt] >> arw[]) >>
 qby_tac
 ‘∀cs:2->Exp(2,A) f. csR(Pt(cs)) = f ⇒
  csR(Pt(G o cs)) = F o f’
 >-- (rw[csR_Pt_o_Cod] >> arw[] >>
     rpt strip_tac >> rw[Cod_Sq_csR_Pt] >> arw[]) >>
 qsuff_tac ‘Tp0(G o a) = F o Tp0(a)’
 >-- (rw[cpnt_def] >> rw[Cr1_Pa_eq_eq] >>
     rw[Pt_eq_eq] >> rw[Tp0_iff_Tp1] >>
     rw[Sq_ob]) >>
 qby_tac
 ‘∀cs:2->Exp(2,A) f. csB(Pt(cs)) = f ⇒
  csB(Pt(G o cs)) = Tp0(G o Tp1(f))’
 >-- (rw[csB_Pt_Tp0] >> rpt strip_tac >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[Tp1_Tp0_inv] >> rw[cod_o]) >>
 qby_tac
 ‘∃cs. csT(Pt(cs)) = id(dom(Tp0(a))) &
       csR(Pt(cs)) = Tp0(a) &
       csL(Pt(cs)) = id(dom(Tp0(a))) &
       csB(Pt(cs)) = Tp0(a)’
 >-- (qsuff_tac
     ‘∃cs. csT(cs) = id(dom(Tp0(a))) &
       csR(cs) = Tp0(a) &
       csL(cs) = id(dom(Tp0(a))) &
       csB(cs) = Tp0(a)’
     >-- (strip_tac >>
         qexists_tac ‘Tp(cs)’ >> arw[Pt_Tp]) >>
     irule Thm7 >>
     rw[cpsb_def,id_dom,id_cod]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘csL(Pt(G o cs)) = F o id(dom(Tp0(a)))’
 >-- (first_x_assum irule >> arw[]) >>
 qby_tac
 ‘csT(Pt(G o cs)) = F o id(dom(Tp0(a)))’
 >-- (first_x_assum irule >> arw[]) >>
 qby_tac
 ‘csR(Pt(G o cs)) = F o Tp0(a)’
 >-- (first_x_assum irule >> arw[]) >>
 qby_tac
 ‘csB(Pt(G o cs)) = Tp0(G o a)’
 >-- (qsuff_tac
      ‘csB(Pt(G o cs)) = Tp0(G o Tp1(Tp0(a)))’
      >-- rw[Tp1_Tp0_inv] >>
      first_x_assum irule >> arw[]) >>
 qsspecl_then [‘Pt(G o cs)’] assume_tac cs_comm >>
 rfs[] >>
 fs[GSYM id_o] >>
 qby_tac ‘(F o Tp0(a)) @ id(F o dom(Tp0(a))) = F o Tp0(a)’
 >-- (once_rw[GSYM dom_o] >> once_rw[idR] >> rw[]) >>
 fs[] >>
 qsuff_tac ‘cpsb(Tp0(G o a),id(F o dom(Tp0(a))))’
 >-- (strip_tac >> drule cpsb_idR >> arw[]) >>
 qsspecl_then [‘Pt(G o cs)’] assume_tac
 cs_cpsb >> rfs[])
(form_goal
 “!A B F:A->B G.
  IFun(Id0(A),Id1(A),Ii(A),Ir(A),
       Id0(B),Id1(B),Ii(B),Ir(B),F,G) ==>
   G = Sq(F)”));
