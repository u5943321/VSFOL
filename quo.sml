
val resp1_def = qdefine_psym("resp1",[‘f:A->B’,‘R:A~>A’]) ‘resp(f,R,id(B))’

val resp1_property = prove_store("resp1_property",
e0
(rpt strip_tac >> rw[resp1_def,resp_def,id_def])
(form_goal “!A B f:A->B R. resp1(f,R) <=> 
 (!a1 a2. Holds(R,a1,a2) ==> App(f,a1) = App(f,a2))”));

val Inj_INV = prove_store("Inj_INV",
e0
(rpt strip_tac >>
 assume_tac
 (P2fun_uex |> qspecl [‘B’,‘A’] 
 |> fVar_sInst_th “P(x:mem(B),y:mem(A))”
    “App(f:A->B,y) = x |
     (!a. ~(App(f,a) = x)) & y = a0”) >>
 qby_tac
 ‘!x. ?!y. 
  App(f:A->B,y) = x |
     (!a. ~(App(f,a) = x)) & y = a0’
 >-- (strip_tac >> uex_tac >>
     qcases ‘?a. App(f,a) = x’ (* 2 *)
     >-- (fs[] >> qexists_tac ‘a’ >> arw[] >>
         rpt strip_tac >> fs[Inj_def]  >>
         first_x_assum irule >> arw[]) >>
     qby_tac ‘!a. ~(App(f,a) = x)’ 
     >-- (strip_tac >> ccontra_tac >>
          qby_tac ‘?a. App(f,a) = x’ 
          >-- (qexists_tac ‘a’ >> arw[]) >>
          rfs[]) >>
     qexists_tac ‘a0’ >> arw[]) >>
 first_x_assum drule >>
 qsuff_tac
 ‘?ivf:B->A. ivf o f = Id(A) & 
 (!b.(!a. ~(App(f,a) = b)) ==> App(ivf,b) = a0)’
 >-- (strip_tac >> uex_tac >>
     qexists_tac ‘ivf’ >> arw[] >>
     rpt strip_tac >> rw[GSYM FUN_EXT] >> strip_tac >>
     qcases ‘?a1.App(f,a1) = a’ (*  2 *)
     >-- (pop_assum (strip_assume_tac  o GSYM)>> 
         arw[GSYM App_App_o]) >>
     qby_tac ‘!a1. ~(App(f,a1) = a)’ 
     >-- (strip_tac >> ccontra_tac >>
          qby_tac ‘?a1. App(f,a1) = a’ 
          >-- (qexists_tac ‘a1’ >> arw[]) >>
          rfs[]) >>
     first_x_assum drule >>
     first_x_assum drule >> arw[]) >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘f'’ >> rpt strip_tac (* 2 *)
 >-- (rw[GSYM FUN_EXT] >> strip_tac >>
     first_x_assum (qspecl_then [‘App(f,a)’] assume_tac) >>
     fs[] (* 2 *)
     >-- (fs[Inj_def] >> first_x_assum drule >>
         arw[App_App_o,Id_def]) >>
     first_x_assum (qspecl_then [‘a’] assume_tac) >>
     fs[]) >>
 first_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
 rfs[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !a0:mem(A). ?!ivf:B->A. ivf o f = Id(A) & 
 (!b.(!a. ~(App(f,a) = b)) ==> App(ivf,b) = a0)”));

val fun_mem_ex = proved_th $
e0
(rpt strip_tac >>
 assume_tac
 (P2fun |> qspecl [‘B’,‘A’]
 |> fVar_sInst_th “P(b:mem(B),a:mem(A))” “a = a0:mem(A)”) >>
 qby_tac ‘!x:mem(B). ?!y. y = a0’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘a0’ >> rw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >> arw[]
 )
(form_goal “!A a0:mem(A) B. ?f:B->A.T”)


val LINV_def = Inj_INV |> spec_all |> undisch |> spec_all
                       |> uex2ex_rule 
                       |> SKOLEM (fun_mem_ex |> qspecl [‘A’,‘a0:mem(A)’,‘B’])
                       "LINV" [dest_var (rastt "f:A->B"),
                               dest_var (rastt "a0:mem(A)")]
                       |> gen_all |> disch_all |> gen_all

val Abs_def = qdefine_fsym("Abs",[‘r:A~>A’,‘i:Q->Pow(A)’,‘q0:mem(Q)’]) ‘LINV(i,q0) o Rsi(r)’

val abs_def = qdefine_fsym("abs",[‘r:A~>A’,‘i:Q->Pow(A)’,‘q0:mem(Q)’,‘a:mem(A)’]) ‘App(Abs(r,i,q0),a)’

val Quot_def = qdefine_psym("Quot",[‘r:A~>A’,‘i:Q->Pow(A)’])
‘Inj(i) & (!s. (?q. s = App(i:Q->Pow(A),q)) <=> (?a. s = rsi(r:A~>A,a)))’

val Inj_LINV = prove_store("Inj_LINV",
e0
(rpt strip_tac >>
 rw[GSYM FUN_EXT,Id_def,App_App_o] >> drule LINV_def >>
 strip_tac >> 
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 arw[GSYM App_App_o,Id_def])
(form_goal “!A B f:A->B.Inj(f) ==> !a.LINV(f,a) o f = Id(A)”));

val Abs_Surj = prove_store("Abs_Surj",
e0
(rpt strip_tac >> rw[Surj_def] >> 
 strip_tac >> fs[Quot_def] >>
 rw[Abs_def,App_App_o,GSYM rsi_def] >>
 first_x_assum (qspecl_then [‘App(i,b)’] assume_tac) >>
 qby_tac
 ‘?q. App(i,b) = App(i,q)’ 
 >-- (qexists_tac ‘b’ >> rw[]) >>
 first_x_assum (drule o iffLR) >>
 fs[] >>
 qexists_tac ‘a’ >> pop_assum (assume_tac o GSYM) >>
 arw[GSYM App_App_o] >> drule Inj_LINV >>
 arw[Id_def] >> fs[Inj_def] >> 
 first_x_assum irule >> arw[])
(form_goal
 “!A r:A~>A Q i:Q->Pow(A). Quot(r,i) ==>
  !q0. Surj(Abs(r,i,q0))”));


val Quot_ER_Holds = prove_store("Quot_ER_Holds",
e0
(rpt strip_tac >> fs[Quot_def] >>
 drule (GSYM Inj_eq_eq) >> arw[] >>
 drule rsi_eq_ER >> arw[])
(form_goal “!A r:A~>A.ER(r) ==> !Q i:Q->Pow(A). Quot(r,i) ==>
 !q1 q2 a1 a2. App(i,q1) = rsi(r,a1) & App(i,q2) = rsi(r,a2) ==> (Holds(r,a1,a2) <=> q1 = q2)”));

val Quot_abs = prove_store("Quot_abs",
e0
(rpt strip_tac >>
 rw[abs_def,Abs_def,App_App_o,GSYM rsi_def] >>
 fs[Quot_def] >>
 first_assum (qspecl_then [‘rsi(r,a1)’] assume_tac) >>
 qby_tac ‘?a.rsi(r,a1) = rsi(r,a)’ 
 >-- (qexists_tac ‘a1’ >> arw[]) >>
 first_x_assum (drule o iffRL) >> fs[] >>
 first_assum (qspecl_then [‘rsi(r,a2)’] assume_tac) >>
 qby_tac ‘?a.rsi(r,a2) = rsi(r,a)’ 
 >-- (qexists_tac ‘a2’ >> arw[]) >>
 first_x_assum (drule o iffRL) >> 
 pop_assum strip_assume_tac >> arw[GSYM App_App_o] >>
 drule Inj_LINV  >> arw[Id_def] >> 
 drule Quot_ER_Holds >>
 pop_assum (assume_tac o GSYM) >>
 first_x_assum irule >>
 qexists_tac ‘i’ >> arw[] >>
 arw[Quot_def])
(form_goal 
 “!A r:A~>A.ER(r) ==> !Q i:Q->Pow(A). Quot(r,i) ==>
!q0 a1 a2.abs(r, i, q0, a1) = abs(r, i, q0, a2) <=> Holds(r,a1,a2)”));

val Quot_UMP  = prove_store("Quot_UMP",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?fb: Q -> B. !a. 
  App(fb,abs(R,i,q0,a)) = App(f,a)’ 
 >-- (rpt strip_tac >>
     uex_tac >> qexists_tac ‘fb’ >> arw[] >>
     rpt strip_tac >>
     irule Surj_Epi >>
     qexistsl_tac [‘A’,‘Abs(R,i,q0)’] >>
     drule Abs_Surj >> arw[] >>
     arw[GSYM FUN_EXT,App_App_o,GSYM abs_def]) >>
 assume_tac
 (P2fun |> qspecl [‘Q’,‘B’] 
 |> fVar_sInst_th “P(q:mem(Q),b:mem(B))”
    “?a.q =abs(R,i:Q->Pow(A),q0,a) & App(f:A->B,a) = b ”) >>
 qby_tac ‘!x. ?!y. 
 (?a. x = abs(R,i,q0,a) & App(f,a) = y)’
 >-- (strip_tac >> 
      qsuff_tac
      ‘?y a. x = abs(R, i, q0, a) & App(f, a) = y’
      >-- (strip_tac >> uex_tac >> qexists_tac ‘y’ >>
          rpt strip_tac (* 2 *)
          >-- (qexists_tac ‘a’ >> arw[]) >>
          fs[resp1_property] >>
          qsuff_tac ‘App(f, a) = App(f,a')’
          >-- (strip_tac >> fs[]) >>
          first_x_assum irule >> 
          irule $ iffLR Quot_abs >> arw[] >>
          qexistsl_tac [‘Q’,‘i’,‘q0’] >> arw[]) >>
      drule Abs_Surj >>
      first_x_assum (qspecl_then [‘q0’] assume_tac) >>
      fs[Surj_def] >>
      first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
      fs[GSYM abs_def] >>
      qexistsl_tac [‘App(f,a)’,‘a’] >> arw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f'’ >>
 arw[] >> strip_tac >> qexists_tac ‘a’ >> rw[])
(form_goal 
 “!A R:A~>A. ER(R) ==>
 !B f:A->B. resp1(f,R) ==> 
  !Q i:Q->Pow(A). Quot(R,i) ==>
  !q0. 
  ?!fb: Q -> B. !a. 
  App(fb,abs(R,i,q0,a)) = App(f,a)”));




(*
val Qc_def = Thm_2_4 |> qspecl [‘Pow(G)’]
                    |> fVar_sInst_th “P(s:mem(Pow(G)))”
                    “?a. s = rsi(cstR(g,H:mem(Pow(G))),a)”
                    |> qSKOLEM "Qc" [‘g’,‘H’]
                    |> qSKOLEM "iQc" [‘g’,‘H’]
                    |> store_as "Qc_def";

val mem_Qc_e = prove_store("mem_Qc_e",
e0
(rpt strip_tac >> 
 qsuff_tac ‘?a:mem(Qc(g:mem(Grp(G)),H:mem(Pow(G)))).
 App(iQc(g,H),a) = rsi(cstR(g,H),eof(g))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘a’ >> arw[] >>
     rpt strip_tac >> 
     qsspecl_then [‘H’,‘g’] assume_tac iQc_Inj >>
     fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 flip_tac >> rw[GSYM Qc_def] >>
 qexists_tac ‘eof(g)’ >> rw[]) 
(form_goal “!G g H. ?!a:mem(Qc(g:mem(Grp(G)),H:mem(Pow(G)))).
 App(iQc(g,H),a) = rsi(cstR(g,H),eof(g))”));

val ecst_def = mem_Qc_e |> spec_all |> uex2ex_rule
                        |> qSKOLEM "ecst" [‘g’,‘H’]
                        |> gen_all




(*group quotient map *)
val gqm_def = qdefine_fsym("gqm",[‘g:mem(Grp(G))’,‘H:mem(Pow(G))’]) ‘Abs(cstR(g,H),iQc(g,H),ecst(g,H))’

(*As coset*)
val Ascs_def = qdefine_fsym("Ascs",[‘g:mem(Grp(G))’,‘H:mem(Pow(G))’]) 
‘LINV(iQc(g,H),ecst(g,H))’


(*quotient group transpost *)
val Qctp_def = qdefine_fsym("Qctp",[‘g:mem(Grp(G))’,‘H1:mem(Pow(G))’,‘H2:mem(Pow(G))’]) ‘LINV(iQc(g,H2),ecst(g,H2)) o iQc(g,H1)’

val Rcs_Csof = prove_store("Rcs_Csof",
e0
cheat
(form_goal 
 “!G g H a:mem(G).Rcs(Csof(g, H, a)) = rsi(cstR(g, H), a)”));

val Qctp_property = prove_store("Qctp_property",
e0
(rpt strip_tac >>
 rw[Qctp_def,App_App_o,GSYM Rcs_def,Rcs_Csof] >>
 arw[] >> 
 rw[GSYM Rcs_Csof,Rcs_def,GSYM App_App_o] >>
 qsspecl_then [‘H2’,‘g’] assume_tac iQc_Inj >>
 drule Inj_LINV >> arw[Id_def])
(form_goal
 “!G g H1 H2:mem(Pow(G)).
  H1 = H2 ==> 
  !a.App(Qctp(g,H1,H2),Csof(g,H1,a)) = Csof(g,H2,a)”));

val Qc_of_equal = prove_store("Qc_of_equal",
e0
(rpt strip_tac (* 2 *)
 >-- (drule Qctp_property >>
     rw[GSYM FUN_EXT,Id_def,App_App_o] >>
     strip_tac >> 
     qsspecl_then [‘g’,‘H2’] assume_tac gqm_Surj >>
     fs[Surj_def] >>
     first_assum 
     (qspecl_then [‘a’]
                  (x_choose_then "x" (assume_tac o GSYM))) >>
     arw[gqm_Csof] >>
     last_x_assum (assume_tac o GSYM) >>
     drule Qctp_property >>
     arw[]) >>
 cheat )
(form_goal “!G H1 H2:mem(Pow(G)).
 H1 = H2 ==> 
 !g.Qctp(g,H1,H2) o Qctp(g,H2,H1) = Id(Qc(g,H2)) &
 Qctp(g,H2,H1) o Qctp(g,H1,H2) = Id(Qc(g,H1))”));

val Qctp_ghom = prove_store("Qctp_ghom",
e0
(rpt strip_tac >> 
 (*if arw[] here, then cannot make any change *)
 rw[ghom_def] >> rpt strip_tac >>
 qsspecl_then [‘g’,‘H1’] assume_tac gqm_Surj >>
 fs[Surj_def] >>
 first_assum 
     (qspecl_then [‘a’]
                  (x_choose_then "x" (assume_tac o GSYM))) >>
     arw[gqm_Csof] >>
 first_assum 
     (qspecl_then [‘b’]
                  (x_choose_then "y" (assume_tac o GSYM))) >>
     arw[gqm_Csof] >>
 drule Qctp_property >> arw[] >>
 last_x_assum (assume_tac o GSYM) >>
 drule Qctp_property >> arw[] >>
 rw[gmul_Qg] >> arw[])
(form_goal
 “!G g H1 H2:mem(Pow(G)).
 H1 = H2 ==> ghom(Qctp(g,H1,H2),Qg(g,H1),Qg(g,H2))”));

val Quot_cstR_iQc = prove_store("Quot_cstR_iQc",
e0
cheat
(form_goal “!G g H:mem(Pow(G)). Quot(cstR(g, H), iQc(g, H))”))

val gqm_Surj = prove_store("gqm_Surj",
e0
(rw[gqm_def] >> rpt strip_tac >> irule Abs_Surj >>
 rw[Quot_cstR_iQc])
(form_goal “!G g H:mem(Pow(G)). Surj(gqm(g,H))”));


val gmul_Qg = prove_store("gmul_Qg",
e0
cheat
(form_goal “!G g H:mem(Pow(G)) a b.gmul(Qg(g,H),Csof(g,H,a),Csof(g,H,b)) = 
 Csof(g,H,gmul(g,a,b))”));

val gqm_Csof = prove_store("gqm_Csof",
e0
cheat
(form_goal “!G g H a:mem(G). App(gqm(g,H),a) = Csof(g,H,a)”));

val ghom_e = prove_store("ghom_e",
e0
cheat
(form_goal 
 “!G1 g1:mem(Grp(G1)) G2 g2 f:G1->G2.
  ghom(f,g1,g2) ==> App(f,eof(g1)) = eof(g2)”));

val first_iso_thm = prove_store("first_iso_thm",
e0
(rpt strip_tac >>
 qspecl_then [‘G1’,‘g1’,‘ker(f, g1, g2)’] assume_tac 
 ER_cstR >>
 drule Quot_UMP >>
 qby_tac ‘resp1(f, cstR(g1, ker(f, g1, g2)))’ 
 >-- cheat >>
 first_x_assum drule >>
 qby_tac ‘Quot(cstR(g1, ker(f, g1, g2)), 
               iQc(g1,ker(f, g1, g2)))’ 
 >-- cheat >>
 first_x_assum drule >>
 first_x_assum (qspecl_then [‘ecst(g1,ker(f, g1, g2))’]
                            assume_tac) >>
 qsuff_tac
 ‘?phi.
     Inj(phi) &
     ghom(phi, Qg(g1, ker(f, g1, g2)), g2) &
     phi o gqm(g1, ker(f, g1, g2)) = f’ 
 >-- (strip_tac >> uex_tac >>
     qexists_tac ‘phi’ >> arw[] >> rpt strip_tac >>
     irule Surj_Epi >>
     qexistsl_tac [‘G1’,‘gqm(g1, ker(f, g1, g2))’] >>
     arw[gqm_Surj]) >> 
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘fb’ >>
 qby_tac ‘fb o gqm(g1, ker(f, g1, g2)) = f’ 
 >-- (rw[GSYM FUN_EXT,App_App_o] >> 
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[gqm_def,GSYM abs_def]) >>
 arw[] >>
 qby_tac
 ‘ghom(fb, Qg(g1, ker(f, g1, g2)), g2)’
 >-- (rw[ghom_def] >> rpt strip_tac >> 
     qsspecl_then [‘g1’,‘ker(f, g1, g2)’] assume_tac 
     gqm_Surj >> fs[Surj_def] >>
     first_assum 
     (qspecl_then [‘a’]
                  (x_choose_then "x" (assume_tac o GSYM))) >>
     first_assum 
     (qspecl_then [‘b’] 
                  (x_choose_then "y" (assume_tac o GSYM))) >>
     arw[] >> fs[gqm_Csof,gmul_Qg] >>
     rw[GSYM gqm_Csof,GSYM App_App_o] >>arw[] >>
     fs[ghom_def]) >>
 arw[] >>
 rw[Inj_def] >> rpt strip_tac >>
 qsspecl_then [‘g1’,‘ker(f, g1, g2)’] assume_tac gqm_Surj >>
 fs[Surj_def] >>
 first_assum 
 (qspecl_then [‘x1’]
              (x_choose_then "a" (assume_tac o GSYM))) >>
 first_assum 
 (qspecl_then [‘x2’] 
              (x_choose_then "b" (assume_tac o GSYM))) >>
 arw[] >> fs[] >> 
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 pop_assum (K all_tac) >>
 rfs[GSYM App_App_o] >> 
 rw[gqm_Csof] >>
 qsuff_tac ‘IN(gmul(g1,a,ginv(g1,b)),ker(f,g1,g2))’ 
 >-- cheat >>
 rw[ker_def] >>
 fs[ghom_def] >> last_x_assum (assume_tac o GSYM) >> arw[] >>
 rw[gmul_ginv] >>
 irule ghom_e >> arw[ghom_def])
(form_goal “!G1 G2 f:G1->G2 g1 g2. 
 ghom(f,g1,g2) & Surj(f) ==>
 ?!phi:Qc(g1,ker(f,g1,g2)) -> G2. Inj(phi) & 
 ghom(phi, Qg(g1,ker(f,g1,g2)), g2) &
 phi o gqm(g1,ker(f,g1,g2)) = f”));

(*

“H1 = H2 ==> LINV(iQc(g,H2)) o iQc(g,H1)
 Abs Rep
 Qc(g,H1) -> Qc(g,H2) ”

*)

val first_iso_thm = prove_store("first_iso_thm",
e0
(rpt strip_tac >>
 qabbrev_tac ‘ker(f, g1, g2) = K’ >>
 (* if arw[] then no change*)(*
 qby_tac
 ‘!phi:Qc(g1,ker(f, g1, g2)) -> G2.
    (Inj(phi) &
    ghom(phi, Qg(g1, ker(f, g1, g2)), g2) &
    phi o gqm(g1, ker(f, g1, g2)) = f) <=> 
   (Inj(phi o Qctp(g1,K,ker(f, g1, g2))) &
     ghom(phi o Qctp(g1,K,ker(f, g1, g2)), Qg(g1, K), g2) &
    phi o Qctp(g1,K,ker(f, g1, g2)) o gqm(g1, K) = f)’ 
 >-- cheat >> 
 qby_tac
 ‘!phi:Qc(g1,ker(f, g1, g2)) -> G2.
  ?psi:Qc(g1,K) -> G2. 
   phi = psi o Qctp(g1,ker(f, g1, g2),K)’
 >-- cheat >>
 qby_tac
 ‘!psi:Qc(g1,K) -> G2.
  ?phi:Qc(g1,ker(f, g1, g2)) -> G2. 
   psi = phi o Qctp(g1,K,ker(f, g1, g2))’
 >-- cheat >>
 qby_tac
 ‘?!psi. Inj(psi) &
  ghom(psi,Qg(g1,K),g2) &
  psi o gqm(g1,K) = f’
 >-- cheat >> *)
 qsuff_tac
 ‘?phi0. !phi. 
  (Inj(phi) &
  ghom(phi,Qg(g1,ker(f, g1, g2)),g2) &
  phi o gqm(g1,ker(f, g1, g2)) = f) <=> phi = phi0’  
 >-- cheat >> 
 qby_tac
 ‘!phi:Qc(g1,ker(f, g1, g2)) -> G2.
    (Inj(phi) &
    ghom(phi, Qg(g1, ker(f, g1, g2)), g2) &
    phi o gqm(g1, ker(f, g1, g2)) = f) <=> 
   (Inj(phi o Qctp(g1,K,ker(f, g1, g2))) &
     ghom(phi o Qctp(g1,K,ker(f, g1, g2)), Qg(g1, K), g2) &
    phi o Qctp(g1,K,ker(f, g1, g2)) o gqm(g1, K) = f)’ 
 >-- cheat >> 
 arw[] >>
 qby_tac 
 ‘!phi phi0:Qc(g1, ker(f, g1, g2))-> G2. phi = phi0 <=> 
  phi o Qctp(g1,K, ker(f, g1, g2)) = phi0 o Qctp(g1,K, ker(f, g1, g2))’
 >-- cheat >>
 arw[] >>
 qsuff_tac
 ‘?psi0. !psi. 
  (Inj(psi) &
  ghom(psi,Qg(g1,K),g2) &
  psi o gqm(g1,K) = f) <=> psi = psi0’ 
 >-- (strip_tac >>
     qexists_tac ‘psi0 o Qctp(g1,ker(f, g1, g2),K)’ >>
     strip_tac >>
     fs[GSYM o_assoc] >> rw[o_assoc] >> 
     drule Qc_of_equal >>
     arw[IdR]) >>
 



 (*if have Makkai rule then everything is solved*)
 pop_assum strip_assume_tac >>
 qexists_tac ‘psi0 o Qctp(g1,ker(f, g1, g2),K)’ >>
 strip_tac >> 
 qby_tac 
 ‘phi = psi0 o Qctp(g1, ker(f, g1, g2), K) <=> 
  phi o Qctp(g1,K, ker(f, g1, g2)) = psi0’
 >-- cheat >>
 arw[] >> 
 qby_tac
 ‘!phi:Qc(g1,ker(f, g1, g2)) -> G2.
    (Inj(phi) &
    ghom(phi, Qg(g1, ker(f, g1, g2)), g2) &
    phi o gqm(g1, ker(f, g1, g2)) = f) <=> 
   (Inj(phi o Qctp(g1,K,ker(f, g1, g2))) &
     ghom(phi o Qctp(g1,K,ker(f, g1, g2)), Qg(g1, K), g2) &
    phi o Qctp(g1,K,ker(f, g1, g2)) o gqm(g1, K) = f)’ 
 >-- cheat >>
 arw[App_App_o] >>
 first_x_assum
 (qspecl_then [‘phi o Qctp(g1, K, ker(f, g1, g2))’]
  assume_tac)>> 
 fs[o_assoc]





 qby_tac
 ‘(!phi0 . (!phi.(Inj(phi) &
    ghom(phi, Qg(g1, ker(f, g1, g2)), g2) &
    phi o gqm(g1, ker(f, g1, g2)) = f) <=> phi = phi0)) ’
 

 qsuff_tac
 ‘?!psi. Inj(psi) &
  ghom(psi,Qg(g1,K),g2) &
  psi o gqm(g1,K) = f’
 (*should be an iff*)
 >-- strip_tac >> arw[] >>
     

 ‘!phi:Qc(g1,ker(f, g1, g2)) -> G2.
  (Inj(phi) & 
  ghom(phi, Qg(g1,K), g2) &
  phi o gqm(g1,K) = f)’ <=> 
  (Inj(phi o Qctp(g,K,ker(f, g1, g2))))’

 qsuff_tac
 ‘?!phi:Qc(g1,K) -> G2. 
   Inj(phi) & 
   ghom(phi, Qg(g1,K), g2) &
   phi o gqm(g1,K) = f’
 >-- strip_tac >>
     qsuff_tac 
     


 qspecl_then [‘G1’,‘g1’,‘ker(f, g1, g2)’] assume_tac 
 ER_cstR >>
 drule Quot_UMP >>
 qby_tac ‘resp1(f, cstR(g1, ker(f, g1, g2)))’ 
 >-- cheat >>
 first_x_assum drule >>
 qby_tac ‘Quot(cstR(g1, ker(f, g1, g2)), 
               iQc(g1,ker(f, g1, g2)))’ 
 >-- cheat >>
 first_x_assum drule >>
 first_x_assum (qspecl_then [‘ecst(g1,ker(f, g1, g2))’]
                            assume_tac) >>
 qsuff_tac
 ‘?phi.
     Inj(phi) &
     ghom(phi, Qg(g1, ker(f, g1, g2)), g2) &
     phi o gqm(g1, ker(f, g1, g2)) = f’ 
 >-- (strip_tac >> uex_tac >>
     qexists_tac ‘phi’ >> arw[] >> rpt strip_tac >>
     irule Surj_Epi >>
     qexistsl_tac [‘G1’,‘gqm(g1, ker(f, g1, g2))’] >>
     arw[gqm_Surj]) >> 
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘fb’ >>
 qby_tac ‘fb o gqm(g1, ker(f, g1, g2)) = f’ 
 >-- (rw[GSYM FUN_EXT,App_App_o] >> 
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[gqm_def,GSYM abs_def]) >>
 arw[] >>
 qby_tac
 ‘ghom(fb, Qg(g1, ker(f, g1, g2)), g2)’
 >-- (rw[ghom_def] >> rpt strip_tac >> 
     qsspecl_then [‘g1’,‘ker(f, g1, g2)’] assume_tac 
     gqm_Surj >> fs[Surj_def] >>
     first_assum 
     (qspecl_then [‘a’]
                  (x_choose_then "x" (assume_tac o GSYM))) >>
     first_assum 
     (qspecl_then [‘b’] 
                  (x_choose_then "y" (assume_tac o GSYM))) >>
     arw[] >> fs[gqm_Csof,gmul_Qg] >>
     rw[GSYM gqm_Csof,GSYM App_App_o] >>arw[] >>
     fs[ghom_def]) >>
 arw[] >>
 rw[Inj_def] >> rpt strip_tac >>
 qsspecl_then [‘g1’,‘ker(f, g1, g2)’] assume_tac gqm_Surj >>
 fs[Surj_def] >>
 first_assum 
 (qspecl_then [‘x1’]
              (x_choose_then "a" (assume_tac o GSYM))) >>
 first_assum 
 (qspecl_then [‘x2’] 
              (x_choose_then "b" (assume_tac o GSYM))) >>
 arw[] >> fs[] >> 
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 pop_assum (K all_tac) >>
 rfs[GSYM App_App_o] >> 
 rw[gqm_Csof] >>
 qsuff_tac ‘IN(gmul(g1,a,ginv(g1,b)),ker(f,g1,g2))’ 
 >-- cheat >>
 rw[ker_def] >>
 fs[ghom_def] >> last_x_assum (assume_tac o GSYM) >> arw[] >>
 rw[gmul_ginv] >>
 irule ghom_e >> arw[ghom_def])
(form_goal “!G1 G2 f:G1->G2 g1 g2. 
 ghom(f,g1,g2) & Surj(f) ==>
 ?!phi:Qc(g1,ker(f,g1,g2)) -> G2. Inj(phi) & 
 ghom(phi, Qg(g1,ker(f,g1,g2)), g2) &
 phi o gqm(g1,ker(f,g1,g2)) = f”));


val sgmul_def = proved_th $
e0
cheat
(form_goal “!G g H K:mem(Pow(G)). ?!HK. !hk. IN(hk,HK) <=> 
 ?h k. IN(h,H) & IN(k,K) & hk = gmul(g,h,k)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "sgmul" [‘g’,‘H’,‘K’]
 
val IM_def = qdefine_fsym("IM",[‘f:A->B’]) ‘IMAGE(f,Whole(A))’

(*try this approach: for every subset, it can be regarded as a injection to the original set, this injection is unique up to iso in the cat of triangles, and therefore gives a function symbol Inc*)

Thm_2_4 |> qspecl [‘A’] 
|> fVar_sInst_th “P(a:mem(A))”
   “IN(a,s:mem(Pow(A)))”
|> qSKOLEM "Set" [‘s’] |> qSKOLEM "Inc" [‘s’]

(*regard subgroup H as inc, then there is a group structure on Set(H) that makes it a group
maybe abbr with equality is an issue suggests that should not use equality as abbrv, should be parsing/pp level stuff.
 *)


(*if H is given as a member of subgroup set, then can prove exists element of set H .*)

val Set_sgrp_grp = proved_th $
e0
cheat
(form_goal 
 “!G g:mem(Grp(G)) H. issgrp(H,g) ==>
  ?!h:mem(Grp(Set(H))).
   Inc(H) o mof(h) = mof(g) o Prla(Inc(H),Inc(H)) &
   Inc(H) o iof(h) = iof(g) &
   App(Inc(H),eof(h)) = eof(g)”)
 
(* H/H ∩ K ~ HK/K*)
val second_iso_thm = prove_store("second_iso_thm",
e0
()
(form_goal 
 “!G g H h:mem(Grp(H)) ih: H->G K k:mem(Grp(K)) ik:K->G. 
  issgrp(IM(ih),g) & isnml(IM(ik),g) ==>
  
  
  
 ”));

(*
rastt "Qg(g1,H1:mem(Pow(G)))";
val it = Qg(g1, H1): term
> sort_of it;
val it = mem(Grp(Qc(g1, H1))): sort

if have K:mem(Pow(G)), not be able to subst in

EQ_fsym "Qg" [refl(rastt "g1:mem(Grp(G))"),assume “H1 = H2:mem(Pow(G))”]




*)

“Qg(g1, H1) = Qg(g2,H2)”

top_depth_conv (rewr_conv (assume “H1 = H2:mem(Pow(G))”)) (rastt "Qg(g1, H1:mem(Pow(G)))")
*)



val Quot_Quo = prove_store("Quot_Quo",
e0
(rpt strip_tac >> rw[Quot_def,Quo_def] >>
 qcases ‘Inj(i)’ >> arw[] >>
drule Inj_ex_uex >> flip_tac >> arw[])
(form_goal 
“∀A r:A~>A Q i:Q-> Pow(A).
 Quot(r,i) <=> Inj(i) & Quo(r,i) ”));


(*does not need injection to prove ER_Quot_nonempty*)
val ER_Quot_nonempty = prove_store("ER_Quot_nonempty",
e0
(rpt strip_tac >> 
 fs[Quot_def] >>
 first_x_assum (qsspecl_then [‘App(i,q)’] assume_tac) >>
 qby_tac ‘?a.App(i,q) = rsi(r,a)’ 
 >-- (first_x_assum (irule o iffLR) >> qexists_tac ‘q’ >>
     rw[]) >> 
 pop_assum strip_assume_tac >> arw[] >>
 drule ER_rsi_nonempty >> qexists_tac ‘a’ >> arw[])
(form_goal
 “∀A r:A~>A Q i:Q-> Pow(A).ER(r) & Quot(r,i) ==>
 !q. ?a. IN(a,App(i,q))”));

val Quot_cong = prove_store("Quot_cong",
e0
(rpt strip_tac >> rw[Quot_Quo] >>
 rpt strip_tac 
 >-- (irule ipow2_Inj_Inj >> rpt strip_tac (* 4 *)
     >-- fs[Quot_def] 
     >-- (irule ER_Quot_nonempty >> qexists_tac ‘r2’ >>
         arw[]) 
     >-- (irule ER_Quot_nonempty >> qexists_tac ‘r1’ >>
         arw[]) >>
     fs[Quot_def]) >>
 fs[Quot_Quo] >> irule Quo_cong >> arw[])
(form_goal 
“∀A r1:A~>A Q1 i1:Q1-> Pow(A) B r2:B~>B Q2 i2:Q2 -> Pow(B). 
 ER(r1) & ER(r2) &
 Quot(r1,i1) & Quot(r2,i2) ⇒
 Quot(prrel(r1,r2),ipow2(i1,i2))”));


val abs_cong = prove_store("abs_cong",
e0
(rpt strip_tac >>
 rw[abs_def,Abs_def,App_App_o,GSYM rsi_def] >> 
 qby_tac ‘Quot(prrel(r1,r2),ipow2(i1, i2))’ 
 >-- (irule Quot_cong >> arw[]) >>
 fs[Quot_def] >>
 first_x_assum (qspecl_then [‘rsi(prrel(r1, r2), Pair(a, b))’]
 assume_tac) >>
 qby_tac ‘?q.rsi(prrel(r1, r2), Pair(a, b)) =
 App(ipow2(i1, i2),q)’ 
 >-- (first_x_assum $ irule o iffRL >>
     qexists_tac ‘Pair(a,b)’ >> rw[]) >>
 pop_assum (x_choosel_then ["q12"] assume_tac) >>
 qsspecl_then [‘q12’] (x_choosel_then ["q01","q02"] assume_tac) Pair_has_comp >>
 fs[] >>
 drule Inj_LINV >> arw[GSYM App_App_o,Id_def] >>
 rw[Pair_eq_eq] >> 
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 pop_assum mp_tac >> pop_assum (K all_tac) >>
 strip_tac >>
 qby_tac
 ‘?q2. rsi(r2,b) = App(i2,q2)’
 >-- (first_x_assum (irule o iffRL) >> qexists_tac ‘b’ >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?q1. rsi(r1,a) = App(i1,q1)’
 >-- (first_x_assum (irule o iffRL) >> qexists_tac ‘a’ >> arw[]) >>
 pop_assum strip_assume_tac >>
 arw[] >>
 qpick_x_assum ‘Inj(ipow2(i1, i2))’ (K all_tac) >>
 drule Inj_LINV >> arw[GSYM App_App_o,Id_def] >>
 rev_drule Inj_LINV >> arw[GSYM App_App_o,Id_def] >>
 qsuff_tac ‘App(i1,q01) = App(i1,q1') & App(i2,q02) = App(i2,q2')’ 
 >-- (rpt strip_tac (* 2 *)
     >-- (irule $ iffLR Inj_eq_eq >> qexistsl_tac [‘Pow(A)’,‘i1’] >> arw[]) >>
     irule $ iffLR Inj_eq_eq >> qexistsl_tac [‘Pow(B)’,‘i2’] >> arw[]) >>
 irule Pow_conj_eq >> rpt strip_tac (* 3 *)
 >-- (irule ER_Quot_nonempty >> qexists_tac ‘r2’ >> arw[Quot_def])
 >-- (irule ER_Quot_nonempty >> qexists_tac ‘r1’ >> arw[Quot_def]) >>
 qpick_x_assum
 ‘rsi(prrel(r1, r2), Pair(a, b)) = App(ipow2(i1, i2), Pair(q01, q02))’
 mp_tac >>
 rw[GSYM IN_EXT_iff,IN_rsi] >> 
 forall_cross_tac >> arw[prrel_def,ipow2_def,GSYM IN_rsi] >>
 rpt strip_tac >> arw[])
(form_goal
 “∀A r1:A~>A Q1 i1:Q1-> Pow(A) B r2:B~>B Q2 i2:Q2 -> Pow(B). 
 ER(r1) & ER(r2) &
 Quot(r1,i1) & Quot(r2,i2) ⇒
 !q1 q2 a b.abs(prrel(r1,r2),ipow2(i1,i2),Pair(q1,q2),Pair(a,b)) = 
 Pair(abs(r1,i1,q1,a),abs(r2,i2,q2,b))”));


val Rep_of_abs = prove_store("Rep_of_abs",
e0
(rpt strip_tac >> 
 rw[abs_def,Abs_def,App_App_o,GSYM rsi_def] >>
 fs[Quot_def] >>
 qby_tac ‘?a0. rsi(r,a) = rsi(r,a0)’ 
 >-- (qexists_tac ‘a’ >> rw[]) >>
 first_x_assum (drule o iffRL) >>
 fs[] >> rw[GSYM App_App_o,o_assoc] >>
 drule Inj_LINV >> arw[IdR])
(form_goal “!A r:A~>A Q i:Q->Pow(A). 
 Quot(r,i) ==> !q0 a.App(i,abs(r,i,q0,a)) = rsi(r,a) ”));

val Quot_rsi_uex = prove_store("Quot_rsi_uex",
e0
(rw[Quot_def] >> rpt strip_tac >>
 drule Inj_ex_uex  >>
 arw[] >> pop_assum (K all_tac) >>
 flip_tac >> arw[] >>
 qexists_tac ‘a’>> rw[])
(form_goal “!A r:A~>A Q i:Q->Pow(A). 
 Quot(r,i) ==>
 !a.?!q. App(i,q) = rsi(r,a)”));



val ER_Quot_rsi_char = prove_store("Quot_rsi_char",
e0
(rpt strip_tac >> drule $ iffLR Quot_def >> fs[] >>
dimp_tac >> 
rpt strip_tac >> arw[] (* 2 *)
>-- (qby_tac ‘?a0. App(i, q) = rsi(r,a0)’ 
    >-- (first_x_assum (irule o iffLR) >>
        qexists_tac ‘q’ >> arw[]) >>
    pop_assum strip_assume_tac >> arw[] >>
    fs[] >> drule rsi_eq_ER  >>
    arw[] >>
    fs[IN_rsi]) >>
rw[IN_rsi] >> fs[ER_def,Refl_def])
(form_goal
“!A r:A~>A. ER(r) ==>
 !Q i:Q-> Pow(A).  Quot(r,i) ==>
 !q a. IN(a,App(i,q)) <=> App(i,q) = rsi(r,a)”));


val Quot_IN_BIGUNION_rep = 
prove_store("Quot_IN_BIGUNION_rep",
e0
(rpt strip_tac >> rw[IN_BIGUNION] >>
 drule $ iffLR Quot_def >>
 dimp_tac >> rpt strip_tac >> arw[] (* 2 *)
 >-- (fs[IMAGE_def] >> 
     qexists_tac ‘a’ >> arw[] >>
     irule $ iffLR Inj_eq_eq >>
     qexistsl_tac [‘Pow(A)’,‘i’] >> arw[] >>
     drule Rep_of_abs  >> arw[] >>
     drule ER_Quot_rsi_char >>
     first_x_assum drule >>
     flip_tac >> 
     first_x_assum (irule o iffLR) >>
     rfs[]) >>
 qexists_tac ‘App(i,a)’ >>
 drule ER_Quot_rsi_char >> first_x_assum drule >>
 arw[] >> rw[IMAGE_def] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘a’ >> arw[]) >>
 drule Rep_of_abs >>
 qpick_x_assum ‘abs(r, i, q0, ra) = a’
 (assume_tac o GSYM) >> arw[])
(form_goal 
“!A r:A~>A. ER(r) ==> 
 !Q i:Q->Pow(A). Quot(r,i) ==>
 !q0 ra s. IN(ra,BIGUNION(IMAGE(i,s))) <=> 
    ?a. IN(a,s) & abs(r,i,q0,ra) = a”));



val Quot_IN_BIGUNION_abs = 
prove_store("Quot_IN_BIGUNION_abs",
e0
(rpt strip_tac >> drule Quot_IN_BIGUNION_rep >>
 first_x_assum drule >>
 arw[] >> dimp_tac >> rpt strip_tac >> arw[] >>
 qexists_tac ‘abs(r, i, q0, ra)’ >> arw[])
(form_goal 
“!A r:A~>A. ER(r) ==> 
 !Q i:Q->Pow(A). Quot(r,i) ==>
 !q0 ra s. IN(ra,BIGUNION(IMAGE(i,s))) <=> 
IN(abs(r,i,q0,ra),s)”));



val Quot_el_same = prove_store("Quot_el_same",
e0
(cheat)
(form_goal
 “!A r:A~>A.
    ER(r) ==> 
    !Q i:Q->Pow(A). 
      Quot(r,i) ==>
      !q1 q2. q1 = q2 <=>
              ?a1 a2.
                IN(a1,App(i,q1)) & 
                IN(a2,App(i,q2)) & 
                Holds(r,a1,a2)
  ”));
