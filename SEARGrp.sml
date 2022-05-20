
val mul_def = qdefine_fsym("mul",[‘m:G * G ->G’,‘g1:mem(G)’,‘g2:mem(G)’])
‘App(m,Pair(g1,g2))’


val asc_def = qdefine_psym("asc",[‘m:A * A -> A’])
‘!a1 a2 a3. mul(m,mul(m,a1,a2),a3) = mul(m,a1,mul(m,a2,a3))’

(*
App(m,Pair(App(m,Pair(a1,a2)),a3)) = 
App(m,Pair(a1,App(m,Pair(a2,a3))))’ |> gen_all
*)

val isunit_def = qdefine_psym("isunit",[‘m:A * A -> A’,‘e:mem(A)’])
‘!a. mul(m,e,a) = a & mul(m,a,e) = a’


val isinv_def = qdefine_psym("isinv",[‘m:A * A -> A’,‘i:A->A’,‘e:mem(A)’])
‘!a. mul(m,App(i,a),a) = e & mul(m,a,App(i,a)) = e’



(*c for component*)
val c31_def = qdefine_fsym("c31",[‘abc:mem(A * B * C)’]) ‘Fst(abc)’
val c32_def = qdefine_fsym("c32",[‘abc:mem(A * B * C)’]) ‘Fst(Snd(abc))’
val c33_def = qdefine_fsym("c33",[‘abc:mem(A * B * C)’]) ‘Snd(Snd(abc))’

val isgrp_def = qdefine_psym("isgrp",[‘g:mem(Exp(G * G,G) * Exp(G,G) * G)’])
‘asc(tof(c31(g))) & 
 isunit(tof(c31(g)),c33(g)) & 
 isinv(tof(c31(g)),tof(c32(g)),c33(g))’

val Grp_def = Thm_2_4 |> qspecl [‘Exp(G * G,G) * Exp(G,G) * G’]
                      |> fVar_sInst_th “P(g:mem(Exp(G * G,G) * Exp(G,G) * G))”
                         “isgrp(g:mem(Exp(G * G,G) * Exp(G,G) * G))”
                      |> qSKOLEM "Grp" [‘G’]
                      |> qSKOLEM "iG" [‘G’]
                      |> gen_all

val RepG_def = qdefine_fsym("RepG",[‘g:mem(Grp(G))’]) ‘App(iG(G),g)’

val mof_def = qdefine_fsym("mof",[‘g:mem(Grp(G))’]) ‘tof(c31(RepG(g)))’
val iof_def = qdefine_fsym("iof",[‘g:mem(Grp(G))’]) ‘tof(c32(RepG(g)))’
val eof_def = qdefine_fsym("eof",[‘g:mem(Grp(G))’]) ‘c33(RepG(g))’

val gmul_def = qdefine_fsym("gmul",[‘g:mem(Grp(G))’,‘x:mem(G)’,‘y:mem(G)’])
‘mul(mof(g),x,y)’

val ginv_def = qdefine_fsym("ginv",[‘g:mem(Grp(G))’,‘x:mem(G)’])
‘App(iof(g),x)’


val ghom_def = qdefine_psym("ghom",[‘f:G1->G2’,‘g1:mem(Grp(G1))’,
                                               ‘g2:mem(Grp(G2))’])
‘!a b. App(f,gmul(g1,a,b)) = gmul(g2,App(f,a),App(f,b))’ |> gen_all


val issgrp_def = qdefine_psym("issgrp",[‘h:mem(Pow(G))’,‘g:mem(Grp(G))’])
‘IN(eof(g),h) & 
 (!a b. IN(a,h) & IN(b,h) ==> IN(gmul(g,a,b),h)) &
 (!a. IN(a,h) ==> IN(ginv(g,a),h))’

val sgrp_def = Thm_2_4 |> qspecl [‘Pow(G)’]
                       |> fVar_sInst_th “P(H:mem(Pow(G)))”
                       “issgrp(H:mem(Pow(G)),g)”
                       |> qSKOLEM "sgrp" [‘g’]
                       |> qSKOLEM "Rsg" [‘g’]

val rsg_def = qdefine_fsym("rsg",[‘H:mem(sgrp(g:mem(Grp(G))))’])
              ‘App(Rsg(g),H)’ |> gen_all

val lcs_def = proved_th $
e0
(rpt strip_tac >>
 accept_tac
 (IN_def_P |> qspecl [‘G’]
 |> fVar_sInst_th “P(x:mem(G))” 
    “?h. IN(h,rsg(H:mem(sgrp(g)))) & x = gmul(g:mem(Grp(G)),a,h)”))
(form_goal “!G g H:mem(sgrp(g)) a:mem(G). 
 ?!lc. !x. IN(x,lc) <=> ?h. IN(h,rsg(H)) & x = gmul(g,a,h)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "lcs" [‘a’,‘H’]

val rcs_def = proved_th $
e0
(rpt strip_tac >>
 accept_tac
 (IN_def_P |> qspecl [‘G’]
 |> fVar_sInst_th “P(x:mem(G))” 
    “?h. IN(h,rsg(H:mem(sgrp(g)))) & x = gmul(g:mem(Grp(G)),h,a)”))
(form_goal “!G g H:mem(sgrp(g)) a:mem(G). 
 ?!lc. !x. IN(x,lc) <=> ?h. IN(h,rsg(H)) & x = gmul(g,h,a)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "rcs" [‘H’,‘a’]


val isnml_def = qdefine_psym("isnml",[‘h:mem(sgrp(g:mem(Grp(G))))’])
‘!a. rcs(h,a) = lcs(a,h)’

val nsgrp_def = Thm_2_4 |> qspecl [‘sgrp(g:mem(Grp(G)))’]
                       |> fVar_sInst_th “P(H:mem(sgrp(g:mem(Grp(G)))))”
                       “isnml(H:mem(sgrp(g:mem(Grp(G)))))”
                       |> qSKOLEM "nsgrp" [‘g’]
                       |> qSKOLEM "Rnsg" [‘g’]
                       |> gen_all

val rnsg_def = qdefine_fsym("rnsg",[‘H:mem(nsgrp(g:mem(Grp(G))))’])
              ‘App(Rnsg(g),H)’ |> gen_all

val qgR_def = 
AX1 |> qspecl [‘G’,‘G’] |> uex2ex_rule
    |> fVar_sInst_th “P(g1:mem(G),g2:mem(G))”
    “lcs(g1,rnsg(H)) =
     lcs(g2:mem(G),rnsg(H:mem(nsgrp(g:mem(Grp(G))))))”
    |> qSKOLEM "qgR" [‘H’] 
    |> gen_all
    |> store_as "qgR_def";


val qgR_Refl = prove_store("qgR_Refl",
e0
(rw[Refl_def,qgR_def])
(form_goal
 “!G g:mem(Grp(G)) H:mem(nsgrp(g)). 
  Refl(qgR(H))”));


val qgR_Sym = prove_store("qgR_Sym",
e0
(rw[Sym_def,qgR_def] >> rpt strip_tac >> arw[])
(form_goal
 “!G g:mem(Grp(G)) H:mem(nsgrp(g)). 
  Sym(qgR(H))”));


val qgR_Trans = prove_store("qgR_Trans",
e0
(rw[Trans_def,qgR_def] >> rpt strip_tac >> arw[])
(form_goal
 “!G g:mem(Grp(G)) H:mem(nsgrp(g)). 
  Trans(qgR(H))”));


val qgR_ER = prove_store("qgR_ER",
e0
(rw[ER_def,qgR_Refl,qgR_Sym,qgR_Trans])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).ER(qgR(H))”));

(*cosets*)
val css_def = Thm_2_4 |> qspecl [‘Pow(G)’]
                    |> fVar_sInst_th “P(s:mem(Pow(G)))”
                    “?a:mem(G). s = rsi(qgR(H:mem(nsgrp(g))),a)”
                    |> qSKOLEM "css" [‘H’]
                    |> qSKOLEM "Rcss" [‘H’]
                    |> gen_all
                    |> store_as "css_def";

val Rcss_Inj = css_def |> spec_all |> conjE1 |> gen_all

val rcss_def = qdefine_fsym("rcss",[‘cs:mem(css(H:mem(nsgrp(g:mem(Grp(G))))))’])
‘App(Rcss(H),cs)’

val rcss_eq_eq = prove_store("rcss_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 fs[rcss_def] >> irule $ iffLR Inj_eq_eq>>
 qexistsl_tac [‘Pow(G)’,‘Rcss(H)’] >> arw[Rcss_Inj])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a b:mem(css(H)).
rcss(a) = rcss(b) <=> a = b ”));

val mem_css_e = prove_store("mem_css_e",
e0
(rpt strip_tac >> 
 qsuff_tac ‘?a:mem(css(H)).
 rcss(a) = rsi(qgR(H),eof(g))’ 
 >-- (rpt strip_tac >>
     uex_tac >> qexists_tac ‘a’ >> arw[] >>
     rpt strip_tac >>
     irule $ iffLR rcss_eq_eq >> arw[]) >>
 flip_tac >> rw[rcss_def,GSYM css_def] >> 
 qexists_tac ‘eof(g)’ >> rw[]) 
(form_goal 
 “!G g:mem(Grp(G)) H:mem(nsgrp(g)). 
  ?!a:mem(css(H)).
   rcss(a) = rsi(qgR(H),eof(g))”));

val ecs_def = mem_css_e |> spec_all |> uex2ex_rule
                        |> qSKOLEM "ecs" [‘H’]
                        |> gen_all

val cs_def = qdefine_fsym("cs",[‘a:mem(G)’,‘H:mem(nsgrp(g:mem(Grp(G))))’])
‘abs(qgR(H),Rcss(H),ecs(H),a)’ |> gen_all

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

val Quot_qgR_Rcss = prove_store("Quot_qgR_Rcss",
e0
(rw[Quot_def,css_def])
(form_goal 
 “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
  Quot(qgR(H), Rcss(H))”));

val rcss_cs = prove_store("rcss_cs",
e0
(rpt strip_tac >> rw[rcss_def,cs_def] >> 
 irule Rep_of_abs >> rw[Quot_qgR_Rcss])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a.
 rcss(cs(a,H)) = rsi(qgR(H),a)”));



val nsgrp_rcs_lcs = prove_store("nsgrp_rcs_lcs",
e0
(rpt strip_tac >>
 qsspecl_then [‘g’] strip_assume_tac nsgrp_def >>
 fs[isnml_def] >> 
 first_x_assum (qspecl_then [‘rnsg(H)’] assume_tac) >> 
 first_x_assum (irule o iffRL) >>
 qexists_tac ‘H’ >> rw[rnsg_def])
(form_goal
 “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a.
  rcs(rnsg(H),a) = lcs(a,rnsg(H))”));

(*set multiplication*)
val smul_def = proved_th $
e0
(rpt strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘G’] 
 |> fVar_sInst_th “P(a:mem(G))”
    “?x:mem(G) y. IN(x,s1) & IN(y,s2) & a = gmul(g,x,y)”))
(form_goal “!G g:mem(Grp(G)) s1 s2.?!s. !a. IN(a,s) <=> 
 ?x y. IN(x,s1) & IN(y,s2) & a = gmul(g,x,y)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "smul" [‘g’,‘s1’,‘s2’]
|> gen_all 

val nsgrp_swap_l2r = prove_store("nsgrp_swap_l2r",
e0
(rpt strip_tac >>
 qsspecl_then [‘g’,‘H’,‘a’] assume_tac nsgrp_rcs_lcs >> 
 fs[GSYM IN_EXT_iff,rcs_def,lcs_def] >>
 qexists_tac ‘h’ >> arw[])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) h.
 IN(h,rsg(rnsg(H))) ==>
 !a.?h1. IN(h1,rsg(rnsg(H))) & gmul(g,a,h) = gmul(g,h1,a)”));


val nsgrp_swap_r2l = prove_store("nsgrp_swap_r2l",
e0
(rpt strip_tac >>
 qsspecl_then [‘g’,‘H’,‘a’] assume_tac 
 (GSYM nsgrp_rcs_lcs) >> 
 fs[GSYM IN_EXT_iff,rcs_def,lcs_def] >>
 qexists_tac ‘h’ >> arw[])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) h.
 IN(h,rsg(rnsg(H))) ==>
 !a.?h1. IN(h1,rsg(rnsg(H))) & gmul(g,h,a) = gmul(g,a,h1)”));

val RepG_isgrp = prove_store("RepG_isgrp",
e0
(rw[RepG_def] >> rpt strip_tac >>
 qspecl_then [‘G’] strip_assume_tac Grp_def >>
 arw[] >> qexists_tac ‘g’ >> rw[])
(form_goal “!G g:mem(Grp(G)).isgrp(RepG(g))”));

val asc_mof = prove_store("asc_mof",
e0
(rw[mof_def] >> rpt strip_tac >>
 qsspecl_then [‘g’] assume_tac RepG_isgrp >>
 drule $ iffLR isgrp_def >> arw[])
(form_goal “!G g:mem(Grp(G)). asc(mof(g))”));

val gmul_assoc = prove_store("gmul_assoc",
e0
(rw[gmul_def,GSYM asc_def,asc_mof])
(form_goal “!G g:mem(Grp(G)) a b c.
 gmul(g,gmul(g,a,b),c) = gmul(g,a,gmul(g,b,c))”));

val gmul_e = prove_store("gmul_e",
e0
(rpt gen_tac >> rw[gmul_def] >>
 qsspecl_then [‘g’] assume_tac RepG_isgrp >>
 fs[isgrp_def,isunit_def,GSYM mof_def,GSYM eof_def])
(form_goal “!G g:mem(Grp(G)) a.
 gmul(g,a,eof(g)) = a & 
 gmul(g,eof(g),a) = a”));

val rsg_issgrp = prove_store("rsg_issgrp",
e0
(rw[sgrp_def] >> rpt strip_tac >>
 qexists_tac ‘H’ >> rw[rsg_def])
(form_goal
 “!G g:mem(Grp(G)) H:mem(sgrp(g)).issgrp(rsg(H),g)”));

val e_IN_rsg = prove_store("e_IN_rsg",
e0
(rpt strip_tac >> 
 qsspecl_then [‘g’,‘H’] assume_tac rsg_issgrp >>
 fs[issgrp_def])
(form_goal “!G g:mem(Grp(G)) H:mem(sgrp(g)).
 IN(eof(g),rsg(H))”));

val gmul_IN_rsg = prove_store("gmul_IN_rsg",
e0
(rpt strip_tac >>
 qsspecl_then [‘g’,‘H’] assume_tac rsg_issgrp >> 
 fs[issgrp_def] >>
 first_x_assum irule >> arw[])
(form_goal “!G g:mem(Grp(G)) H:mem(sgrp(g)) h1.
 IN(h1,rsg(H)) ==> !h2. IN(h2,rsg(H)) ==> 
 IN(gmul(g,h1,h2),rsg(H))”));


val ginv_IN_rsg = prove_store("ginv_IN_rsg",
e0
(rpt strip_tac >>
 qsspecl_then [‘g’,‘H’] assume_tac rsg_issgrp >> 
 fs[issgrp_def] >>
 first_x_assum irule >> arw[])
(form_goal “!G g:mem(Grp(G)) H:mem(sgrp(g)) h.
 IN(h,rsg(H)) ==> 
 IN(ginv(g,h),rsg(H))”));

val gmul_lcs_smul = prove_store("gmul_lcs_smul",
e0
(rpt strip_tac >>
 qsspecl_then [‘g’,‘H’,‘b’] assume_tac nsgrp_rcs_lcs >>
 rw[GSYM IN_EXT_iff,lcs_def,smul_def] >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (drule nsgrp_swap_l2r >>
     first_x_assum
     (qspecl_then [‘b’] (x_choose_then "h1" assume_tac)) >>
     qexistsl_tac [‘a’,‘gmul(g,b,h)’] >>
     fs[gmul_assoc] >> rpt strip_tac (* 2 *)
     >-- (qexists_tac ‘eof(g)’ >> rw[e_IN_rsg,gmul_e])
     >-- (qexists_tac ‘h’ >> arw[])) >>
 arw[] >> 
 drule nsgrp_swap_l2r >>
 first_x_assum
 (qspecl_then [‘b’] (x_choose_then "h1" assume_tac)) >>
 fs[] >>
 qby_tac
 ‘gmul(g, gmul(g, a, h), gmul(g, h1, b)) = 
  gmul (g,a,gmul(g,gmul(g,h,h1),b))’    
 >-- rw[gmul_assoc] >>
 arw[] >>
 qby_tac ‘IN(gmul(g, h, h1), rsg(rnsg(H)))’  
 >-- (irule gmul_IN_rsg >> arw[]) >>
 drule nsgrp_swap_r2l >>
 first_x_assum
 (qspecl_then [‘b’] (x_choose_then "h2" assume_tac)) >>
 fs[] >>
 qexists_tac ‘h2’ >> arw[gmul_assoc])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a b.
 lcs(gmul(g,a,b),rnsg(H)) = 
 smul(g,lcs(a,rnsg(H)),lcs(b,rnsg(H)))”));

val mof_resp = prove_store("mof_resp",
e0
(rw[resp1_property] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rpt strip_tac >>
 rw[App_App_o,GSYM abs_def,GSYM cs_def] >> 
 fs[prrel_def,qgR_def] >> 
 rw[GSYM rcss_eq_eq,rcss_cs] >> 
 irule $ iffRL rsi_eq_ER >> rw[qgR_ER,qgR_def] >>
 arw[GSYM gmul_def,GSYM mul_def,gmul_lcs_smul])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 resp1(Abs(qgR(H),Rcss(H),ecs(H)) o mof(g:mem(Grp(G))),prrel(qgR(H),qgR(H)))”));

val prrel_qgR_ER = prove_store("prrel_qgR_ER",
e0
(rpt strip_tac >> irule prrel_ER_ER >>
 rw[qgR_ER])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 ER(prrel(qgR(H), qgR(H)))”));



val Inj_ex_uex = prove_store("Inj_ex_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- first_x_assum (accept_tac o uex2ex_rule) >>
 uex_tac >> qexists_tac ‘a’ >> arw[] >> rpt strip_tac >>
 fs[Inj_def] >> first_x_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !b. (?!a.App(f,a) = b) <=> (?a.App(f,a) = b)”));



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

val qgR_Rcss_cong = prove_store("qgR_Rcss_cong",
e0
(rpt strip_tac >> irule Quot_cong >>
 rw[Quot_qgR_Rcss,qgR_ER])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 Quot(prrel(qgR(H), qgR(H)), ipow2(Rcss(H), Rcss(H)))”));

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

val qgR_Rcss_abs_cong = prove_store("qgR_Rcss_abs_cong",
e0
(rpt strip_tac >> irule abs_cong >>
 rw[qgR_Rcss_cong,qgR_ER,Quot_qgR_Rcss])
(form_goal 
 “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a b.
  abs(prrel(qgR(H), qgR(H)),ipow2(Rcss(H), Rcss(H)),
     Pair(ecs(H), ecs(H)),Pair(a,b)) = 
 Pair(abs(qgR(H),Rcss(H),ecs(H),a),
      abs(qgR(H),Rcss(H),ecs(H),b))”));


val mulcs_def =
Quot_UMP
|> qspecl [‘G * G’,
           ‘prrel(qgR(H:mem(nsgrp(g:mem(Grp(G))))),qgR(H))’]
|> C mp (prrel_qgR_ER |> spec_all)
|> qspecl [‘css(H:mem(nsgrp(g:mem(Grp(G)))))’,
           ‘Abs(qgR(H),Rcss(H),ecs(H)) o mof(g:mem(Grp(G)))’]
|> C mp (spec_all mof_resp)
|> qspecl [‘css(H:mem(nsgrp(g:mem(Grp(G))))) * 
            css(H:mem(nsgrp(g:mem(Grp(G)))))’,
           ‘ipow2(Rcss(H:mem(nsgrp(g:mem(Grp(G))))),
                  Rcss(H))’]
|> C mp (spec_all qgR_Rcss_cong)
|> qspecl [‘Pair(ecs(H:mem(nsgrp(g:mem(Grp(G))))),
                 ecs(H))’]
|> uex2ex_rule |> qSKOLEM "mulcs" [‘H’]
|> rewr_rule[App_App_o]
|> qspecl [‘Pair(a:mem(G),b:mem(G))’]
|> rewr_rule[GSYM mul_def,GSYM gmul_def,GSYM cs_def,GSYM abs_def,qgR_Rcss_abs_cong]
|> qgenl [‘G’,‘g’,‘H’,‘a’,‘b’] |> store_as "mulcs_def"

val sinv_def = proved_th $
e0
(rpt strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘G’] 
 |> fVar_sInst_th “P(a:mem(G))”
    “?x:mem(G). IN(x,s) & a = ginv(g,x)”))
(form_goal “!G g:mem(Grp(G)) s.
 ?!invs. !a. IN(a,invs) <=> 
 ?x. IN(x,s) & a = ginv(g,x)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "sinv" [‘g’,‘s’]
|> gen_all 

val gmul_lcancel = prove_store("gmul_lcancel",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qsuff_tac ‘gmul(g,ginv(g,x),gmul(g, x, y)) = 
          gmul(g,ginv(g,x),gmul(g, x, z))’ 
 >-- rw[GSYM gmul_assoc,gmul_ginv,gmul_e] >> 
 arw[])
(form_goal “!G g x y z:mem(G). 
 gmul(g,x,y) = gmul(g,x,z) <=> y = z”));


val gmul_rcancel = prove_store("gmul_rcancel",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qsuff_tac ‘gmul(g,gmul(g, y, x),ginv(g,x)) = 
          gmul(g,gmul(g, z, x),ginv(g,x))’ 
 >-- rw[gmul_assoc,gmul_ginv,gmul_e] >> 
 arw[])
(form_goal “!G g x y z:mem(G). 
 gmul(g,y,x) = gmul(g,z,x) <=> y = z”));

val ginv_oneside = prove_store("ginv_oneside",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >--
 (qsuff_tac ‘a1 = ginv(g,a)’ 
 >-- (strip_tac >> arw[gmul_ginv]) >>
 irule $ iffLR gmul_lcancel >>
 qexistsl_tac [‘g’,‘a’] >> arw[gmul_ginv]) >>
 qsuff_tac ‘a = ginv(g,a1)’ 
 >-- (strip_tac >> arw[gmul_ginv]) >>
 irule $ iffLR gmul_lcancel >>
 qexistsl_tac [‘g’,‘a1’] >> arw[gmul_ginv])
(form_goal “!G g a:mem(G) a1. gmul(g,a,a1) = eof(g) <=>
 gmul(g,a1,a) = eof(g)”));


val is_ginv = prove_store("is_ginv",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 3 *)
 >-- arw[gmul_ginv] 
 >-- (irule $ iffLR gmul_lcancel >>
     qexistsl_tac [‘g’,‘a’] >> arw[gmul_ginv]) >>
 irule $ iffLR gmul_rcancel >>
 qexistsl_tac [‘g’,‘a’] >> arw[gmul_ginv])
(form_goal “!G g a:mem(G) a1. a1 = ginv(g,a) <=> 
 (gmul(g,a,a1) = eof(g) | gmul(g,a1,a) = eof(g))”));

val ginv_gmul = prove_store("ginv_gmul",
e0
(rpt strip_tac >> flip_tac >>
 rw[is_ginv] >>
 once_rw[GSYM gmul_assoc] >> disj1_tac >>
 qby_tac
 ‘gmul(g, gmul(g, a, b), ginv(g, b)) = 
  gmul(g, a, gmul(g, b, ginv(g, b)))’
 >-- rw[gmul_assoc] >>
 arw[] >> rw[gmul_ginv,gmul_e])
(form_goal “!G g:mem(Grp(G)) a b.
 ginv(g,gmul(g,a,b)) = gmul(g,ginv(g,b),ginv(g,a))”));

val ginv_ginv = prove_store("ginv_ginv",
e0
(rpt strip_tac >> flip_tac >> rw[is_ginv] >>
 rw[gmul_ginv])
(form_goal “!G g a:mem(G). ginv(g,ginv(g,a)) = a”));

val ginv_lcs = prove_store("ginv_lcs",
e0
(rpt strip_tac >>
 qsspecl_then [‘g’,‘H’,‘a’] assume_tac nsgrp_rcs_lcs >>
 rw[GSYM IN_EXT_iff,lcs_def,sinv_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (arw[] >> 
     pop_assum (K all_tac) >> 
     qexists_tac ‘gmul(g,ginv(g,h),a)’ >>
     rw[ginv_gmul,ginv_gmul,ginv_ginv] >>
     drule ginv_IN_rsg >>
     drule nsgrp_swap_r2l >> arw[]) >>
 arw[] >> rw[ginv_gmul] >>
 drule ginv_IN_rsg >> 
 drule nsgrp_swap_r2l >> arw[])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a.
  lcs(ginv(g, a), rnsg(H)) = sinv(g,lcs(a, rnsg(H)))”));

val iof_resp = prove_store("iof_resp",
e0
(rw[resp1_property] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rpt strip_tac >>
 rw[App_App_o,GSYM abs_def,GSYM cs_def] >> 
 fs[qgR_def] >> 
 rw[GSYM rcss_eq_eq,rcss_cs] >> 
 irule $ iffRL rsi_eq_ER >> rw[qgR_ER,qgR_def] >>
 arw[GSYM ginv_def,ginv_lcs])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 resp1(Abs(qgR(H),Rcss(H),ecs(H)) o iof(g:mem(Grp(G))),
       qgR(H))”));

val invcs_def =
Quot_UMP
|> qspecl [‘G’,
           ‘qgR(H:mem(nsgrp(g:mem(Grp(G)))))’]
|> C mp (qgR_ER |> spec_all)
|> qspecl [‘css(H:mem(nsgrp(g:mem(Grp(G)))))’,
           ‘Abs(qgR(H),Rcss(H),ecs(H)) o iof(g:mem(Grp(G)))’]
|> C mp (spec_all iof_resp)
|> qspecl [‘css(H:mem(nsgrp(g:mem(Grp(G)))))’,
           ‘Rcss(H:mem(nsgrp(g:mem(Grp(G)))))’]
|> C mp (spec_all Quot_qgR_Rcss)
|> qspecl [‘ecs(H:mem(nsgrp(g:mem(Grp(G)))))’]
|> uex2ex_rule |> qSKOLEM "invcs" [‘H’]
|> rewr_rule[App_App_o]
|> qspecl [‘a:mem(G)’]
|> rewr_rule[GSYM cs_def,GSYM abs_def,GSYM ginv_def]
|> qgenl [‘G’,‘g’,‘H’,‘a’] |> store_as "invcs_def"

val qmap_def = qdefine_fsym("qmap",[‘H:mem(nsgrp(g:mem(Grp(G))))’]) ‘Abs(qgR(H),Rcss(H),ecs(H))’|> gen_all

val qmap_Surj = prove_store("qmap_Surj",
e0
(rpt strip_tac >> rw[qmap_def] >> irule Abs_Surj >>
 rw[Quot_qgR_Rcss])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 Surj(qmap(H))”));

val css_rep_ex = qmap_Surj |> rewr_rule[Surj_def,qmap_def,
 GSYM cs_def,GSYM abs_def] |> GSYM


val ecs_cs = prove_store("ecs_cs",
e0
(rpt strip_tac >> rw[GSYM rcss_eq_eq,rcss_cs,ecs_def])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 ecs(H)= cs(eof(g),H)”));

val mulcs_invcs_ecs_isgrp = prove_store("mulcs_invcs_ecs_isgrp",
e0
(rpt strip_tac >>
 rw[isgrp_def,c31_def,c32_def,c33_def,Pair_def',
    tof_Tpm_inv,asc_def,isunit_def,isinv_def] >>
 rpt strip_tac (* 5 *)
 >-- (qsspecl_then [‘g’,‘H’,‘a1’]
     (x_choose_then "x" assume_tac) css_rep_ex >>
     qsspecl_then [‘g’,‘H’,‘a2’]
     (x_choose_then "y" assume_tac) css_rep_ex >>
     qsspecl_then [‘g’,‘H’,‘a3’]
     (x_choose_then "z" assume_tac) css_rep_ex >>
     arw[mulcs_def,gmul_assoc]) 
 >-- (qsspecl_then [‘g’,‘H’,‘a’]
     (x_choose_then "x" assume_tac) css_rep_ex >> 
     arw[ecs_cs,mulcs_def,gmul_e]) 
 >-- (qsspecl_then [‘g’,‘H’,‘a’]
     (x_choose_then "x" assume_tac) css_rep_ex >> 
     arw[ecs_cs,mulcs_def,gmul_e])
 >-- (qsspecl_then [‘g’,‘H’,‘a’]
     (x_choose_then "x" assume_tac) css_rep_ex >> 
     arw[ecs_cs,invcs_def,mulcs_def,gmul_ginv])
 >-- (qsspecl_then [‘g’,‘H’,‘a’]
     (x_choose_then "x" assume_tac) css_rep_ex >> 
     arw[ecs_cs,invcs_def,mulcs_def,gmul_ginv])
)
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 isgrp(Pair(Tpm(mulcs(H)),Pair(Tpm(invcs(H)),ecs(H))))”));
 
(*
val Grp_ex = prove_store("Grp_ex",
e0
cheat
(form_goal “!G x:mem(G).?g:mem(Grp(G)).T”));

val css_Grp_ex =
Grp_ex |> qspecl [‘css(H:mem(nsgrp(g:mem(Grp(G)))))’,
                  ‘ecs(H:mem(nsgrp(g:mem(Grp(G)))))’]

*)


(*if do like this, then do not need AC*)
val qgrp_def = proved_th $
e0
(rpt strip_tac >>
 qspecl_then [‘css(H)’] strip_assume_tac Grp_def >>
 rw[RepG_def] >>
 flip_tac >>
 qsuff_tac
 ‘?qg. App(iG(css(H)),qg) = Pair(Tpm(mulcs(H)),Pair(Tpm(invcs(H)),ecs(H)))’
 >-- (strip_tac >>
     uex_tac >> qexists_tac ‘qg’ >> arw[] >>
     rpt strip_tac >>
     fs[Inj_def] >>
     first_x_assum irule >> arw[]) >>
 flip_tac >>
 first_x_assum (irule o iffLR) >> rw[mulcs_invcs_ecs_isgrp])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 ?!qg:mem(Grp(css(H))). RepG(qg) = Pair(Tpm(mulcs(H)),Pair(Tpm(invcs(H)),ecs(H)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "qgrp" [‘H’] 
|> gen_all 

val mof_qgrp = prove_store("mof_qgrp",
e0
(rw[qgrp_def,mof_def,c31_def,Pair_def',tof_Tpm_inv])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 mof(qgrp(H)) = mulcs(H)”));


val iof_qgrp = prove_store("iof_qgrp",
e0
(rw[qgrp_def,iof_def,c32_def,Pair_def',tof_Tpm_inv])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 iof(qgrp(H)) = invcs(H)”));


val eof_qgrp = prove_store("eof_qgrp",
e0
(rw[qgrp_def,eof_def,c33_def,Pair_def'])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 eof(qgrp(H)) = ecs(H)”));

val gmul_qgrp = prove_store("gmul_qgrp",
e0
(rw[gmul_def,mof_qgrp,mulcs_def])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a b.
 gmul(qgrp(H),cs(a,H),cs(b,H)) = cs(gmul(g,a,b),H)”));


val ginv_qgrp = prove_store("ginv_qgrp",
e0
(rw[ginv_def,iof_qgrp,invcs_def])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a b.
 ginv(qgrp(H),cs(a,H)) = cs(ginv(g,a),H)”));


val qmap_cs = prove_store("qmap_cs",
e0
(rw[qmap_def,cs_def,abs_def])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a.
 App(qmap(H),a) = cs(a,H)”));


val qmap_ghom = prove_store("qmap_ghom",
e0
(rpt strip_tac >>
 rw[ghom_def] >> rpt strip_tac >>
 rw[qmap_cs,gmul_qgrp])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 ghom(qmap(H),g,qgrp(H))”));


val ker_def = proved_th $
e0
(rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘G1’] 
           |> fVar_sInst_th “P(x:mem(G1))”
              “App(f:G1->G2,x) = eof(g2:mem(Grp(G2)))”) >>
 arw[])
(form_goal “!G1 G2 f:G1->G2 g1:mem(Grp(G1)) g2:mem(Grp(G2)). 
 ?!k:mem(Pow(G1)). !x. IN(x,k) <=> App(f,x) = eof(g2)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "ker" [‘f’,‘g1’,‘g2’]

val hom_def = 
    Thm_2_4 |> qspecl [‘Exp(G1,G2)’]
            |> fVar_sInst_th “P(f:mem(Exp(G1,G2)))”
            “ghom(tof(f:mem(Exp(G1,G2))),g1,g2)”
            |> qSKOLEM "hom" [‘g1’,‘g2’]
            |> qSKOLEM "ih" [‘g1’,‘g2’]
            |> gen_all

val constf_def = fun_tm_compr_uex 
                       (dest_var (rastt "a:mem(A)"))
                       (rastt "b:mem(B)")
                       |> uex2ex_rule
                       |> qSKOLEM "constf" [‘A’,‘b’]
                       |> gen_all
                       |> store_as "constf_def";

val constf_ghom = prove_store("constf_ghom",
e0
(rw[ghom_def,constf_def,gmul_e])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)).
 ghom(constf(G1,eof(g2)),g1,g2)”));

val homfun_def = 
qdefine_fsym("homfun",[‘h:mem(hom(g1:mem(Grp(G1)),g2:mem(Grp(G2))))’]) ‘tof(App(ih(g1,g2),h))’ |> gen_all

val PREIM_def = proved_th $
e0
(rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a:mem(A))”
    “?b. IN(b,s) & App(f:A->B,a) = b”) >>
 arw[])
(form_goal “!A B f:A->B s.?!s0.
 !a. IN(a,s0) <=> ?b. IN(b,s) & App(f,a) = b ”)
|> spec_all |> uex2ex_rule |> qSKOLEM "PREIM" [‘f’,‘s’]
|> gen_all


(*kernel set, kernel should always be regarded as a normal subgroup*)
val kers_def = qdefine_fsym("kers",[‘f:mem(hom(g1:mem(Grp(G1)),g2:mem(Grp(G2))))’]) ‘PREIM(homfun(f),Sing(eof(g2)))’

val IN_Sing = prove_store("IN_Sing",
e0
(rw[Sing_def,Sg_def])
(form_goal “!A a0 a:mem(A). IN(a,Sing(a0)) <=> a = a0”));

val ginv_e = prove_store("ginv_e",
e0
(rpt strip_tac >> flip_tac >> rw[is_ginv,gmul_e] )
(form_goal “!G g:mem(Grp(G)). ginv(g,eof(g)) = eof(g)”));

val sgrp_mem_ex = proved_th $
e0
(rw[issgrp_def,IN_Sing,gmul_e] >>
 rpt strip_tac >> arw[ginv_e,gmul_e])
(form_goal “!G g:mem(Grp(G)).issgrp(Sing(eof(g)),g)”)

val esg_def = sgrp_def |> conjE2 |> qspecl [‘Sing(eof(g:mem(Grp(G))))’]
             |> rewr_rule[sgrp_mem_ex]
             |> qSKOLEM "esg" [‘g’] |> gen_all



val nsgrp_mem_ex = proved_th $
e0
(rw[isnml_def] >> cheat)
(form_goal “!G g:mem(Grp(G)).isnml(esg(g))”)

val ensg_def = nsgrp_def |> spec_all
                         |> conjE2
                         |> qspecl [‘esg(g:mem(Grp(G)))’]
                         |> rewr_rule[nsgrp_mem_ex]
                         |> qSKOLEM "ensg" [‘g’] |> gen_all

val ker_def = qdefine_fsym("ker",[‘f:mem(hom(g1:mem(Grp(G1)),
                                         g2:mem(Grp(G2))))’])
‘App(LINV(Rnsg(g1),ensg(g1)) o LINV(Rsg(g1),esg(g1)),kers(f))’ |> gen_all

val kers_issgrp = prove_store("kers_issgrp",
e0
(cheat)
(form_goal “!G1 G2 g1:mem(Grp(G1)) g2:mem(Grp(G2)) f:mem(hom(g1,g2)). issgrp(kers(f))”));

val qhom_def = qdefine_fsym("qhom",[‘f:mem(hom(g1:mem(Grp(G1)),
                                         g2:mem(Grp(G2))))’])
‘LINV()’

val first_iso_thm = prove_store("first_iso_thm",
e0
(rpt strip_tac >>
 )
(form_goal 
 “!G1 G2 g1:mem(Grp(G1)) g2:mem(Grp(G2)) f:mem(hom(g1,g2)).
  ?!fb:mem(hom(qgrp(ker(f)),g2)).
  Inj(homfun(fb)) &
  homfun(fb) o qmap(ker(f)) = homfun(f)
  ”));


val second_iso_thm = prove_store("second_iso_thm",
e0
()
(form_goal “!G g:mem(Grp(G)) H:sgrp(g) K:nsgrp(g).
 ?phi:hom(qgrp(),qgrp(grp(smul(g,rsg(),rsg())))). giso(phi) ”));
