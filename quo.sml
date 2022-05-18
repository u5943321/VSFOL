
val resp1_def = qdefine_psym("resp1",[‘f:A->B’,‘R:A~>A’]) ‘resp(f,R,id(B))’

val resp1_property = prove_store("resp1_property",
e0
cheat
(form_goal “!A B f:A->B R. resp(f,R,id(B)) <=> 
 (!a1 a2. Holds(R,a1,a2) ==> App(f,a1) = App(f,a2))”));

val Inj_INV = prove_store("Inj_INV",
e0
cheat
(form_goal “!A B f:A->B. Inj(f) ==>
 !a0:mem(A). ?!ivf:B->A.!b.(!a.App(f,a) = b ==> App(ivf,b) = a) &
 ((!a. ~(App(f,a) = b)) ==> App(ivf,b) = a0)”));

val fun_mem_ex = proved_th $
e0
cheat
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
 first_x_assum (qspecl_then [‘a’,‘App(f,a')’] 
 strip_assume_tac) >>
 first_x_assum irule >> rw[])
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

val Surj_Epi = prove_store("Surj_Epi",
e0
(rpt strip_tac >> fs[Surj_def,GSYM FUN_EXT,App_App_o] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal “!A B f:A->B. Surj(f) ==>
 !C g1:B->C g2. g1 o f = g2 o f ==> g1 = g2”));

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

val gmul_ginv = prove_store("gmul_ginv",
e0
cheat
(form_goal 
     “!G g:mem(Grp(G)) a.
              gmul(g,ginv(g,a),a)= eof(g) &
              gmul(g,a,ginv(g,a))= eof(g)”));

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


val sgmul_def = proved_th $
e0
cheat
(form_goal “!G g H K:mem(Pow(G)). ?!HK. !hk. IN(hk,HK) <=> 
 ?h k. IN(h,H) & IN(k,K) & hk = gmul(g,h,k)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "sgmul" [‘g’,‘H’,‘K’]
 
val second_iso_thm = prove_store("second_iso_thm",
e0
()
(form_goal “”));

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
