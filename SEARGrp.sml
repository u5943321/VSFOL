
val mul_def = qdefine_fsym("mul",[‘m:G * G ->G’,‘g1:mem(G)’,‘g2:mem(G)’])
‘App(m,Pair(g1,g2))’


val asc_def = qdefine_psym("asc",[‘m:A * A -> A’])
‘!a1 a2 a3. mul(m,mul(m,a1,a2),a3) = mul(m,a1,mul(m,a2,a3))’

val isunit_def = qdefine_psym("isunit",[‘m:A * A -> A’,‘e:mem(A)’])
‘!a. mul(m,e,a) = a & mul(m,a,e) = a’


val isinv_def = qdefine_psym("isinv",[‘m:A * A -> A’,‘i:A->A’,‘e:mem(A)’])
‘!a. mul(m,App(i,a),a) = e & mul(m,a,App(i,a)) = e’




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


val RepG_isgrp = prove_store("RepG_isgrp",
e0
(rw[RepG_def] >> rpt strip_tac >>
 qspecl_then [‘G’] strip_assume_tac Grp_def >>
 arw[] >> qexists_tac ‘g’ >> rw[])
(form_goal “!G g:mem(Grp(G)).isgrp(RepG(g))”));


val mof_def = qdefine_fsym("mof",[‘g:mem(Grp(G))’]) ‘tof(c31(RepG(g)))’
val iof_def = qdefine_fsym("iof",[‘g:mem(Grp(G))’]) ‘tof(c32(RepG(g)))’
val eof_def = qdefine_fsym("eof",[‘g:mem(Grp(G))’]) ‘c33(RepG(g))’

val gmul_def = qdefine_fsym("gmul",[‘g:mem(Grp(G))’,‘x:mem(G)’,‘y:mem(G)’])
‘mul(mof(g),x,y)’

val ginv_def = qdefine_fsym("ginv",[‘g:mem(Grp(G))’,‘x:mem(G)’])
‘App(iof(g),x)’


val isghom_def = qdefine_psym("isghom",[‘f:G1->G2’,‘g1:mem(Grp(G1))’,
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


val Rnsg_Inj = nsgrp_def |> spec_all 
                         |> conjE1 |> gen_all

val nsg_ex_uex = mp 
                  (Inj_ex_uex |> qsspecl [‘Rnsg(g:mem(Grp(G)))’])
                  (spec_all Rnsg_Inj) |> GSYM

                 

val nsg_uex = nsgrp_def |> spec_all 
                        |> conjE2 
                        |> spec_all 
                        |> iffLR |> undisch 
                        |> GSYM 
                        |> mp (iffLR nsg_ex_uex
                                       |> qspecl [‘a:mem(sgrp(g:mem(Grp(G))))’])
                        |> disch_all |> gen_all
                       

val lsmul_def = proved_th $
e0
(rpt strip_tac >> assume_tac 
 (IN_def_P |> qspecl [‘G’] 
 |> fVar_sInst_th “P(a:mem(G))”
    “?y. IN(y,s) & a = gmul(g:mem(Grp(G)),x,y)”) >> arw[])
(form_goal “!G g:mem(Grp(G)) x s.?!xs. !a. IN(a,xs) <=> 
 ?y. IN(y,s) & a = gmul(g,x,y)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "lsmul" [‘g’,‘x’,‘s’]
|> gen_all 


val rsmul_def = proved_th $
e0
(rpt strip_tac >> assume_tac 
 (IN_def_P |> qspecl [‘G’] 
 |> fVar_sInst_th “P(a:mem(G))”
    “?x. IN(x,s) & a = gmul(g:mem(Grp(G)),x,y)”) >> arw[])
(form_goal “!G g:mem(Grp(G)) s y.?!sy. !a. IN(a,sy) <=> 
 ?x. IN(x,s) & a = gmul(g,x,y)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "rsmul" [‘g’,‘s’,‘y’]
|> gen_all 


val rcs_rsmul = prove_store("rcs_rsmul",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,rcs_def,rsmul_def])
(form_goal “!G g:mem(Grp(G)) H:mem(sgrp(g)) a.
 rcs(H,a) = rsmul(g,rsg(H),a)”));


val lcs_lsmul = prove_store("lcs_lsmul",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,lcs_def,lsmul_def])
(form_goal “!G g:mem(Grp(G)) H:mem(sgrp(g)) a.
 lcs(a,H) = lsmul(g,a,rsg(H))”));



val Rsg_Inj = sgrp_def |> spec_all |> conjE1 
                       |> gen_all

val sg_ex_uex = mp 
                  (Inj_ex_uex |> qsspecl [‘Rsg(g:mem(Grp(G)))’])
                  (spec_all Rsg_Inj) |> GSYM

val sg_uex = sgrp_def |> spec_all 
                      |> conjE2 
                      |> spec_all 
                      |> iffLR |> undisch 
                      |> GSYM 
                      |> mp (iffLR sg_ex_uex
                                   |> qspecl [‘a:mem(Pow(G))’])
                      |> disch_all |> gen_all 
                       

val gmul_e = prove_store("gmul_e",
e0
(rpt gen_tac >> rw[gmul_def] >>
 qsspecl_then [‘g’] assume_tac RepG_isgrp >>
 fs[isgrp_def,isunit_def,GSYM mof_def,GSYM eof_def])
(form_goal “!G g:mem(Grp(G)) a.
 gmul(g,a,eof(g)) = a & 
 gmul(g,eof(g),a) = a”));





val gmul_e = prove_store("gmul_e",
e0
(rpt gen_tac >> rw[gmul_def] >>
 qsspecl_then [‘g’] assume_tac RepG_isgrp >>
 fs[isgrp_def,isunit_def,GSYM mof_def,GSYM eof_def])
(form_goal “!G g:mem(Grp(G)) a.
 gmul(g,a,eof(g)) = a & 
 gmul(g,eof(g),a) = a”));


val gmul_ginv = prove_store("gmul_ginv",
e0
(rw[gmul_def] >>
 rpt strip_tac >> 
 qsspecl_then [‘g’] assume_tac RepG_isgrp >>
 fs[isgrp_def] >>
 fs[isinv_def,mof_def,ginv_def,iof_def,eof_def])
(form_goal 
     “!G g:mem(Grp(G)) a.
              gmul(g,ginv(g,a),a)= eof(g) &
              gmul(g,a,ginv(g,a))= eof(g)”));


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


val ginv_e = prove_store("ginv_e",
e0
(rpt strip_tac >> flip_tac >> rw[is_ginv,gmul_e] )
(form_goal “!G g:mem(Grp(G)). ginv(g,eof(g)) = eof(g)”));


val e_sgrp = proved_th $
e0
(rw[issgrp_def,IN_Sing,gmul_e] >>
 rpt strip_tac >> arw[ginv_e,gmul_e])
(form_goal “!G g:mem(Grp(G)).issgrp(Sing(eof(g)),g)”)


val esg_def = 
sg_uex |> qsspecl [‘Sing(eof(g:mem(Grp(G))))’,‘g:mem(Grp(G))’]
            |> rewr_rule[e_sgrp]
            |> uex2ex_rule
            |> qSKOLEM "esg" [‘g’] |> gen_all




val rsg_esg = prove_store("rsg_esg",
e0
(rw[esg_def,rsg_def])
(form_goal “!G g:mem(Grp(G)). rsg(esg(g)) = Sing(eof(g))”));


val e_nsgrp = prove_store("e_nsgrp",
e0
(rw[isnml_def] >> rpt strip_tac >>
 rw[rcs_rsmul,lcs_lsmul,GSYM IN_EXT_iff,lsmul_def,rsmul_def,
    rsg_esg,IN_Sing] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘eof(g)’ >> arw[gmul_e]) >>
 qexists_tac ‘eof(g)’ >> arw[gmul_e])
(form_goal “!G g:mem(Grp(G)).isnml(esg(g))”));

val ensg_def = 
    nsg_uex |> qsspecl [‘g:mem(Grp(G))’,‘esg(g:mem(Grp(G)))’]
            |> rewr_rule[e_nsgrp]
            |> uex2ex_rule
            |> qSKOLEM "ensg" [‘g’] |> gen_all

val nsg_def = qdefine_fsym("nsg",[‘h:mem(sgrp(g:mem(Grp(G))))’]) ‘App(LINV(Rnsg(g),ensg(g)),h)’ |> gen_all



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




val qgR_Rcss_cong = prove_store("qgR_Rcss_cong",
e0
(rpt strip_tac >> irule Quot_cong >>
 rw[Quot_qgR_Rcss,qgR_ER])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 Quot(prrel(qgR(H), qgR(H)), ipow2(Rcss(H), Rcss(H)))”));

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


val is_e = prove_store("is_e",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 3 *)
 >-- (disj1_tac >> qexists_tac ‘eof(g)’ >> arw[gmul_e]) 
 >-- (irule $ iffLR gmul_rcancel >>
      qexistsl_tac [‘g’,‘x’] >> arw[gmul_e]) >>
 irule $ iffLR gmul_lcancel >>
 qexistsl_tac [‘g’,‘x’] >> arw[gmul_e])
(form_goal “!G g a:mem(G). a = eof(g) <=> 
 ((?x. gmul(g,a,x) = x) | (?x. gmul(g,x,a) = x))”));


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


val qmap_isghom = prove_store("qmap_isghom",
e0
(rpt strip_tac >>
 rw[isghom_def] >> rpt strip_tac >>
 rw[qmap_cs,gmul_qgrp])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 isghom(qmap(H),g,qgrp(H))”));

(*

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
*)


val ghom_def = 
    Thm_2_4 |> qspecl [‘Exp(G1,G2)’]
            |> fVar_sInst_th “P(f:mem(Exp(G1,G2)))”
            “isghom(tof(f:mem(Exp(G1,G2))),g1,g2)”
            |> qSKOLEM "ghom" [‘g1’,‘g2’]
            |> qSKOLEM "ih" [‘g1’,‘g2’]
            |> gen_all

val ih_Inj = ghom_def |> spec_all 
                         |> conjE1 |> gen_all

val ghom_ex_uex = 
    mp 
       (Inj_ex_uex
       |> qsspecl [‘ih(g1:mem(Grp(G1)),g2:mem(Grp(G2)))’])
                  (spec_all ih_Inj) |> GSYM

val ghom_uex = ghom_def |> spec_all 
                        |> conjE2 
                        |> spec_all 
                        |> iffLR |> undisch 
                        |> GSYM 
                        |> mp (iffLR ghom_ex_uex
                                     |> qspecl [‘a:mem(Exp(G1,G2))’])
                        |> disch_all 
                        |> qgenl [‘G1’,‘g1’,‘G2’,‘g2’,‘a’]


val constf_isghom = prove_store("constf_isghom",
e0
(rw[isghom_def,constf_def,gmul_e])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)).
 isghom(constf(G1,eof(g2)),g1,g2)”));


val eghm_def = 
ghom_uex |> qspecl [‘G1’,‘g1:mem(Grp(G1))’,‘G2’,‘g2:mem(Grp(G2))’,‘Tpm(constf(G1,eof(g2:mem(Grp(G2)))))’]
            |> rewr_rule[tof_Tpm_inv,constf_isghom]
            |> uex2ex_rule
            |> qSKOLEM "eghm" [‘g1’,‘g2’] |> gen_all


val ghm_def = qdefine_fsym("ghm",[‘h:G1->G2’,‘g1:mem(Grp(G1))’,‘g2:mem(Grp(G2))’]) ‘App(LINV(ih(g1,g2),eghm(g1,g2)),Tpm(h))’ |> gen_all


val homfun_def = 
qdefine_fsym("homfun",[‘h:mem(ghom(g1:mem(Grp(G1)),g2:mem(Grp(G2))))’]) ‘tof(App(ih(g1,g2),h))’ |> gen_all



val isghom_homfun_ghm = prove_store("isghom_homfun_ghm",
e0
(rpt strip_tac >>
 once_rw[GSYM tof_Tpm_inv] >> rw[ghom_def] >> 
 rw[tof_Tpm_inv] >> 
 dimp_tac >> rpt strip_tac
 (* 2 *)
 >-- (arw[homfun_def,ghm_def,GSYM App_App_o] >>
      qsspecl_then [‘g1’,‘g2’] assume_tac ih_Inj >>
      drule Inj_LINV >> arw[IdR]>>
      rw[GSYM Tpm_eq_eq] >> arw[Tpm_tof_inv]) >>
 fs[homfun_def] >>
 qexists_tac ‘ghm(f, g1, g2)’ >>
 arw[GSYM tof_eq_eq,tof_Tpm_inv])
(form_goal
 “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:G1->G2. 
 isghom(f,g1,g2) <=> homfun(ghm(f,g1,g2)) = f”));


(*kernel set, kernel should always be regarded as a normal subgroup*)
val kers_def = qdefine_fsym("kers",[‘f:mem(ghom(g1:mem(Grp(G1)),g2:mem(Grp(G2))))’]) ‘PREIM(homfun(f),Sing(eof(g2)))’

val sg_def = qdefine_fsym("sg",[‘h:mem(Pow(G))’,‘g:mem(Grp(G))’]) ‘App(LINV(Rsg(g),esg(g)),h)’ |> gen_all



val ker_def = qdefine_fsym("ker",[‘f:mem(ghom(g1:mem(Grp(G1)),
                                         g2:mem(Grp(G2))))’])
‘nsg(sg(kers(f),g1))’ |> gen_all


val IN_kers = prove_store("IN_kers",
e0
(rpt strip_tac >> rw[kers_def,PREIM_def,IN_Sing] >>
 dimp_tac >> rpt strip_tac >> arw[] >>
 qexists_tac ‘eof(g2)’ >> arw[])
(form_goal 
 “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)) x. IN(x,kers(f)) <=> App(homfun(f),x) = eof(g2)”));



val homfun_isghom = prove_store("homfun_isghom",
e0
(rw[ghom_def,homfun_def] >> rpt strip_tac >>
 qexists_tac ‘f’ >> rw[])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)). isghom(homfun(f),g1,g2)”));




val homfun_gmul = prove_store("homfun_gmul",
e0
(rpt strip_tac >>
 irule $ iffLR isghom_def >> rw[homfun_isghom])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)) x y.
 App(homfun(f),gmul(g1, x, y)) = 
 gmul(g2, App(homfun(f), x), App(homfun(f), y))”));


val homfun_e = prove_store("homfun_e",
e0
(rpt strip_tac >> rw[is_e] >>
 disj1_tac >>
 qexists_tac ‘App(homfun(f), eof(g1))’ >>
 rw[GSYM homfun_gmul,gmul_e])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)).
 App(homfun(f),eof(g1)) = eof(g2)”));


val homfun_ginv = prove_store("homfun_ginv",
e0
(rpt strip_tac >> rw[is_ginv,GSYM homfun_gmul,gmul_ginv,
  homfun_e])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)) a.
 App(homfun(f),ginv(g1,a)) = ginv(g2,App(homfun(f),a))”));



val e_IN_kers = prove_store("e_IN_kers",
e0
(rpt strip_tac >> rw[IN_kers,homfun_e])
(form_goal 
 “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)).
  IN(eof(g1),kers(f))”));

val kers_issgrp = prove_store("kers_issgrp",
e0
(rpt strip_tac >> rw[issgrp_def] >>
 rw[e_IN_kers] >> rw[IN_kers,homfun_gmul,homfun_ginv] >>
 rpt strip_tac (* 2 *)
 >-- arw[gmul_e] >>
 arw[ginv_e])
(form_goal “!G1 G2 g1:mem(Grp(G1)) g2:mem(Grp(G2)) f:mem(ghom(g1,g2)). issgrp(kers(f),g1)”));





val qhom_def = qdefine_fsym("qhom",[‘H:mem(nsgrp(g:mem(Grp(G))))’])
‘ghm(qmap(H),g, qgrp(H))’ |> gen_all




(*
val first_iso_thm0 = prove_store("first_iso_thm0",
e0
(rpt strip_tac >>
 )
(form_goal 
 “!G1 G2 g1:mem(Grp(G1)) g2:mem(Grp(G2)) f:mem(hom(g1,g2)).
  ?!fb:mem(hom(qgrp(ker(f)),g2)).
  Inj(homfun(fb)) &
  homfun(fb) o qmap(ker(f)) = homfun(f)”));
*)

(*conjugate*)
val cjg_def = 
qdefine_fsym("cjg",[‘g:mem(Grp(G))’,‘a:mem(G)’,‘h:mem(G)’])
‘gmul(g,a,gmul(g,h,ginv(g,a)))’


val lsmul_gmul = prove_store("lsmul_gmul",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,lsmul_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (arw[] >> qexists_tac ‘y'’ >> arw[gmul_assoc]) >>
 arw[] >> qexists_tac ‘gmul(g,b,y)’ >> arw[gmul_assoc] >>
 qexists_tac ‘y’ >> arw[])
(form_goal “!G g:mem(Grp(G)) a b s:mem(Pow(G)).
 lsmul(g,a,lsmul(g,b,s)) = lsmul(g,gmul(g,a,b),s)”));


val rsmul_gmul = prove_store("rsmul_gmul",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,rsmul_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (arw[] >> qexists_tac ‘x''’ >> arw[gmul_assoc]) >>
 arw[] >> qexists_tac ‘gmul(g,x',a)’ >> arw[gmul_assoc] >>
 qexists_tac ‘x'’ >> arw[])
(form_goal “!G g:mem(Grp(G)) s:mem(Pow(G)) a b.
 rsmul(g,rsmul(g,s,a),b) = rsmul(g,s,gmul(g,a,b))”));

val lsmul_e = prove_store("lsmul_e",
e0
(rw[GSYM IN_EXT_iff,lsmul_def,gmul_e] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 qexists_tac ‘x’ >> arw[])
(form_goal “!G g:mem(Grp(G)) s:mem(Pow(G)).
 lsmul(g,eof(g),s) = s”));


val rsmul_e = prove_store("rsmul_e",
e0
(rw[GSYM IN_EXT_iff,rsmul_def,gmul_e] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 qexists_tac ‘x’ >> arw[])
(form_goal “!G g:mem(Grp(G)) s:mem(Pow(G)).
 rsmul(g,s,eof(g)) = s”));

val lsmul_rsmul_comm = prove_store("rsmul_lsmul_comm",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,rsmul_def,lsmul_def] >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (arw[] >> qexists_tac ‘gmul(g,y,b)’ >>
     rw[gmul_assoc] >> qexists_tac ‘y’ >> arw[]) >>
 arw[] >> qexists_tac ‘gmul(g,a,x')’ >>
 arw[gmul_assoc] >> qexists_tac ‘x'’ >> arw[])
(form_goal “!G g:mem(Grp(G)) a s:mem(Pow(G)) b.
 rsmul(g,lsmul(g,a,s),b) = lsmul(g,a,rsmul(g,s,b))”));

val scjg_def = qdefine_fsym("scjg",[‘g:mem(Grp(G))’,‘a:mem(G)’,‘s:mem(Pow(G))’]) ‘lsmul(g,a,rsmul(g,s,ginv(g,a)))’

val isnml_alt = prove_store("isnml_alt",
e0
(rw[isnml_def,scjg_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[GSYM rcs_rsmul] >> arw[] >>
      rw[lcs_lsmul,lsmul_gmul,gmul_ginv,lsmul_e]) >>
 rw[rcs_rsmul,lcs_lsmul] >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 qby_tac
 ‘rsmul(g,lsmul(g, a, rsmul(g, rsg(H), ginv(g, a))),a) = 
  rsmul(g,rsg(H),a)’
 >-- arw[] >>
 fs[lsmul_rsmul_comm,rsmul_gmul,gmul_ginv,rsmul_e])
(form_goal
 “!G g:mem(Grp(G)) H:mem(sgrp(g)). isnml(H) <=>
  !a. scjg(g,a,rsg(H)) = rsg(H)”));

val scjg_cjg = prove_store("scjg_cjg",
e0
(rpt strip_tac >> 
 rw[scjg_def,cjg_def,lsmul_def,rsmul_def] >>
 dimp_tac >> rpt strip_tac >> arw[] (* 2 *)
 >-- (qexists_tac ‘x'’ >> arw[]) >>
 qexists_tac ‘gmul(g,h,ginv(g,a))’ >> rw[] >>
 qexists_tac ‘h’ >> arw[])
(form_goal “!G g:mem(Grp(G)) a H.
  !x.IN(x,scjg(g,a,H)) <=> ?h. IN(h,H) & x = cjg(g,a,h)”));

val SS_scjg = prove_store("SS_scjg",
e0
(rpt strip_tac >> rw[SS_def,scjg_cjg] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum irule >> qexists_tac ‘x’>> arw[]) >>
 arw[] >> first_x_assum irule >> arw[])
(form_goal “!G g:mem(Grp(G)) a s.
SS(scjg(g,a,s),s) <=> !x. IN(x,s) ==> IN(cjg(g,a,x),s)”));

val SS_rsmul = prove_store("SS_rsmul",
e0
(rpt strip_tac >> rw[SS_def,rsmul_def] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘x’ >> arw[] >>
     first_x_assum irule >> arw[]) >>
 first_x_assum (qspecl_then [‘eof(g)’,‘gmul(g,a,eof(g))’]
   assume_tac) >>
 qby_tac
 ‘?x. IN(x, s1) & gmul(g, a, eof(g)) = gmul(g, x, eof(g))’ 
 >-- (qexists_tac ‘a’ >> arw[]) >>
 first_x_assum drule >>
 fs[gmul_e])
(form_goal
 “!G g:mem(Grp(G)) s1 s2. SS(s1,s2) <=> 
  !a.SS(rsmul(g,s1,a),rsmul(g,s2,a))”));



val SS_lsmul = prove_store("SS_lsmul",
e0
(rpt strip_tac >> rw[SS_def,lsmul_def] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘y’ >> arw[] >>
     first_x_assum irule >> arw[]) >>
 first_x_assum (qspecl_then [‘eof(g)’,‘gmul(g,eof(g),a)’]
   assume_tac) >>
 qby_tac
 ‘?x. IN(x, s1) & gmul(g, eof(g),a) = gmul(g, eof(g),x)’ 
 >-- (qexists_tac ‘a’ >> arw[]) >>
 first_x_assum drule >>
 fs[gmul_e])
(form_goal
 “!G g:mem(Grp(G)) s1 s2. SS(s1,s2) <=> 
  !a.SS(lsmul(g,a,s1),lsmul(g,a,s2))”));


val isnml_cjg = prove_store("isnml_cjg",
e0
(rw[isnml_alt] >> 
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[SS_scjg] >> rpt strip_tac >> last_x_assum mp_tac >> 
     rw[GSYM IN_EXT_iff,lsmul_def,rsmul_def] >>
     rpt strip_tac >>
     first_x_assum (irule o iffLR) >>
     qexists_tac ‘a’ >> rw[scjg_cjg] >>
     qexists_tac ‘x’ >> arw[]) >>
 irule SS_SS_eq >> arw[] >>
 first_x_assum (qspecl_then [‘ginv(g,a)’] assume_tac) >>
 drule $ iffLR SS_rsmul >>
 first_x_assum (qspecl_then [‘ginv(g,a)’] assume_tac) >>
 fs[scjg_def] >> 
 fs[lsmul_rsmul_comm,ginv_ginv,rsmul_gmul,gmul_ginv,
    rsmul_e] >>
 drule $ iffLR SS_lsmul >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 fs[lsmul_gmul,gmul_ginv,lsmul_e])
(form_goal
 “!G g:mem(Grp(G)) H:mem(sgrp(g)). isnml(H) <=>
 !a.SS(scjg(g,a,rsg(H)),rsg(H))”));


val IN_gmul_rsmul = prove_store("IN_gmul_rsmul",
e0
(rpt strip_tac >> rw[rsmul_def] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘a’ >> arw[]) >>
 first_x_assum (qspecl_then [‘eof(g)’] assume_tac) >>
 fs[gmul_e])
(form_goal “!G g:mem(Grp(G)) H:mem(Pow(G)) a. 
 IN(a,H) <=> !b.IN(gmul(g,a,b),rsmul(g,H,b))”));


val IN_gmul_lsmul = prove_store("IN_gmul_lsmul",
e0
(rpt strip_tac >> rw[lsmul_def] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘b’ >> arw[]) >>
 first_x_assum (qspecl_then [‘eof(g)’] assume_tac) >>
 fs[gmul_e])
(form_goal “!G g:mem(Grp(G)) H:mem(Pow(G)) b. 
 IN(b,H) <=> !a.IN(gmul(g,a,b),lsmul(g,a,H))”));

val gmul_IN_rsmul = prove_store("gmul_IN_rsmul",
e0
(rpt strip_tac >> rw[rsmul_def] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘gmul(g,a,b)’ >>
     arw[gmul_assoc,gmul_ginv,gmul_e]) >>
 arw[gmul_ginv,gmul_e,gmul_assoc])
(form_goal “!G g:mem(Grp(G)) H:mem(Pow(G)) a b. 
 IN(gmul(g,a,b),H) <=> IN(a,rsmul(g,H,ginv(g,b)))”));


val gmul_IN_lsmul = prove_store("gmul_IN_lsmul",
e0
(rpt strip_tac >> rw[rsmul_def] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘gmul(g,a,b)’ >>
     arw[gmul_assoc,gmul_ginv,gmul_e]) >>
 arw[gmul_ginv,gmul_e,gmul_assoc])
(form_goal “!G g:mem(Grp(G)) H:mem(Pow(G)) a b. 
 IN(gmul(g,a,b),H) <=> IN(a,rsmul(g,H,ginv(g,b)))”));

val rnsg_isnml = prove_store("rnsg_isnml",
e0
(rw[nsgrp_def,rnsg_def] >>
 rpt strip_tac >> qexists_tac ‘H’ >> rw[])
(form_goal 
 “!G g:mem(Grp(G)) H:mem(nsgrp(g)). 
  isnml(rnsg(H))”));

val rnsg_rcs_lcs = prove_store("rnsg_rcs_lcs",
e0
(rpt strip_tac >> irule $ iffLR isnml_def >>
 rw[rnsg_isnml])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a.
 rcs(rnsg(H),a) = lcs(a,rnsg(H))”));

 
val SS_ex_lsmul = prove_store("SS_ex_lsmul",
e0
(rpt strip_tac >> rw[SS_def,lsmul_def] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘eof(g)’ >> arw[gmul_e] >>
     rpt strip_tac >> qexists_tac ‘y’ >> arw[] >>    
     first_x_assum irule >> arw[]) >>
 first_x_assum (qspecl_then [‘gmul(g,a,a')’]
   assume_tac) >>
 qby_tac
 ‘?y. IN(y, s1) & gmul(g, a, a') = gmul(g, a, y)’ 
 >-- (qexists_tac ‘a'’ >> arw[]) >>
 first_x_assum drule >>
 fs[gmul_lcancel] >> rfs[])
(form_goal
 “!G g:mem(Grp(G)) s1 s2. SS(s1,s2) <=> 
  ?a.SS(lsmul(g,a,s1),lsmul(g,a,s2))”));


val same_cs_cond = prove_store("same_cs_cond",
e0
(rpt strip_tac >> rw[GSYM rcss_eq_eq,rcss_cs] >>
 qsspecl_then [‘g’,‘H’] assume_tac qgR_ER >>
 drule rsi_eq_ER >> arw[qgR_def] >>
 pop_assum_list (map_every (K all_tac)) >>
 dimp_tac >> rpt strip_tac 
 (* 2 *)
 >-- (rw[gmul_IN_rsmul,ginv_ginv,GSYM rcs_rsmul,
        rnsg_rcs_lcs] >> 
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[lcs_lsmul,lsmul_def] >> 
     qexists_tac ‘eof(g)’ >> rw[e_IN_rsg,gmul_e]) >>
 irule SS_SS_eq >> strip_tac
 >-- (drule $ iffLR IN_gmul_rsmul >> 
     first_x_assum (qspecl_then [‘b’] assume_tac) >>
     fs[gmul_assoc,gmul_ginv,gmul_e] >>
     fs[GSYM rcs_rsmul,rnsg_rcs_lcs] >>
     fs[lcs_lsmul,lsmul_def,SS_def] >>
     rpt strip_tac >>
     qexists_tac ‘gmul(g,y,y')’ >>
     fs[gmul_assoc] >> 
     irule gmul_IN_rsg  >> arw[]) >>
 qby_tac
 ‘IN(gmul(g, ginv(g,ginv(g,a)), ginv(g, b)), rsg(rnsg(H)))’
 >-- arw[ginv_ginv] >>
 fs[GSYM ginv_gmul] >>
 drule ginv_IN_rsg >> fs[ginv_ginv] >> 
 drule $ iffLR IN_gmul_rsmul >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 fs[gmul_assoc,gmul_ginv,gmul_e] >>
 fs[GSYM rcs_rsmul,rnsg_rcs_lcs] >>
 fs[lcs_lsmul,lsmul_def,SS_def] >>
 rpt strip_tac >>
 qexists_tac ‘gmul(g,y,y')’ >>
 fs[gmul_assoc] >> 
 irule gmul_IN_rsg  >> arw[])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)) a b.
 cs(a,H) = cs(b,H) <=> 
 IN(gmul(g,a,ginv(g,b)),rsg(rnsg(H))) ”));

val sg_rsg = prove_store("sg_rsg",
e0
(rw[sg_def,rsg_def,GSYM App_App_o] >> 
 rpt strip_tac >>
 qsspecl_then [‘g’] assume_tac Rsg_Inj >>
 drule Inj_LINV >> arw[Id_def])
(form_goal “!G g:mem(Grp(G)) H:mem(sgrp(g)).
 sg(rsg(H),g) = H”));



val nsg_rnsg = prove_store("nsg_rnsg",
e0
(rw[nsg_def,rnsg_def,GSYM App_App_o] >> 
 rpt strip_tac >>
 qsspecl_then [‘g’] assume_tac Rnsg_Inj >>
 drule Inj_LINV >> arw[Id_def])
(form_goal “!G g:mem(Grp(G)) H:mem(nsgrp(g)).
 nsg(rnsg(H)) = H”));

val issgrp_rsg_sg = prove_store("issgrp_rsg_sg",
e0
(rw[sgrp_def] >> rpt strip_tac>> dimp_tac >> rpt strip_tac
 (* 2 *)
 >-- (arw[rsg_def,sg_def,App_App_o] >>
     qsspecl_then [‘g’] assume_tac Rsg_Inj >>
     drule Inj_LINV >>
     arw[Id_def,GSYM App_App_o,o_assoc,IdR]) >>
 rw[GSYM rsg_def] >> qexists_tac ‘sg(H, g)’ >> arw[])
(form_goal
 “!G g:mem(Grp(G)) H:mem(Pow(G)).
 issgrp(H,g) <=> rsg(sg(H,g)) = H”));

 
val isnml_rnsg_nsg = prove_store("isnml_rnsg_nsg",
e0
(rw[nsgrp_def] >> rpt strip_tac>> dimp_tac >> rpt strip_tac
 (* 2 *)
 >-- (arw[rnsg_def,nsg_def,App_App_o] >>
     qsspecl_then [‘g’] assume_tac Rnsg_Inj >>
     drule Inj_LINV >>
     arw[Id_def,GSYM App_App_o,o_assoc,IdR]) >>
 rw[GSYM rnsg_def] >> qexists_tac ‘nsg(H)’ >> arw[])
(form_goal
 “!G g:mem(Grp(G)) H:mem(sgrp(g)).
 isnml(H) <=> rnsg(nsg(H)) = H”));



(*
!G g:mem(Grp(G)) H:mem(nsgrp(G)).
 


*)

val sg_kers_isnml = prove_store("sg_kers_isnml",
e0
(rw[isnml_cjg] >> rpt strip_tac >>
 qby_tac 
 ‘rsg(sg(kers(f), g1)) = kers(f)’ 
 >-- (irule $ iffLR issgrp_rsg_sg >> rw[kers_issgrp]) >>
 arw[] >> rw[SS_def,IN_kers] >>
 rw[scjg_def,lsmul_def,rsmul_def,IN_kers] >> 
 rpt strip_tac >> arw[] >>
 arw[homfun_gmul,gmul_e] >>
 rw[GSYM homfun_gmul,gmul_ginv,homfun_e])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)). isnml(sg(kers(f),g1))”));


val rsg_rnsg_ker = prove_store("rsg_rnsg_ker",
e0
(rpt strip_tac >> rw[ker_def] >>
 qsspecl_then [‘g1’,‘g2’,‘f’] assume_tac sg_kers_isnml >>
 fs[isnml_rnsg_nsg] >> 
 rw[GSYM issgrp_rsg_sg,kers_issgrp])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)). rsg(rnsg(ker(f))) = kers(f)”));

val rgh_def =
qdefine_fsym("rgh",[‘f:mem(ghom(g1:mem(Grp(G1)),
                                g2:mem(Grp(G2))))’])
‘App(ih(g1,g2),f)’ |> gen_all

val rgh_eq_eq = prove_store("rgh_eq_eq",
e0
(rw[rgh_def] >> rpt strip_tac >>
 irule Inj_eq_eq >> rw[ghom_def])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f1 f2:mem(ghom(g1,g2)). rgh(f1) = rgh(f2) <=> f1 = f2”));


val homfun_eq_eq = prove_store("homfun_eq_eq",
e0
(rw[homfun_def,tof_eq_eq,GSYM rgh_def,rgh_eq_eq])
(form_goal “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f1 f2:mem(ghom(g1,g2)). homfun(f1) = homfun(f2) <=> f1 = f2”));

val homfun_eq_ker = prove_store("homfun_eq_ker",
e0
(rpt strip_tac >> rw[homfun_gmul,homfun_ginv] >>
 dimp_tac >> rpt strip_tac (* 2 *) >> arw[]
 >-- rw[gmul_ginv] >>
 irule $ iffLR gmul_lcancel >>
 qexistsl_tac [‘g2’,‘ginv(g2, App(homfun(f), a1))’] >>
 arw[gmul_ginv])
(form_goal
 “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)) a1 a2. App(homfun(f), a1) = App(homfun(f), a2) <=>
 App(homfun(f),gmul(g1,ginv(g1,a1),a2)) = eof(g2)”));


val homfun_resp1_qgR_ker = prove_store("homfun_resp1_qgR_ker",
e0
(rw[resp1_property] >> rpt strip_tac >> 
 fs[qgR_def] >>
 qby_tac 
 ‘lsmul(g1,ginv(g1,a1),lcs(a1, rnsg(ker(f)))) = 
  lsmul(g1,ginv(g1,a1),lcs(a2, rnsg(ker(f))))’ 
 >-- arw[] >>
 pop_assum mp_tac >>
 rw[lcs_lsmul,lsmul_gmul,gmul_ginv,lsmul_e] >>
 rw[rsg_rnsg_ker] >> rpt strip_tac >>
 rw[homfun_eq_ker] >> rw[GSYM IN_kers] >>
 once_arw[] >> rw[lsmul_def] >>
 qexists_tac ‘eof(g1)’ >>
 rw[e_IN_kers,gmul_e])
(form_goal
 “!G1 g1:mem(Grp(G1)) G2 g2:mem(Grp(G2)) f:mem(ghom(g1,g2)).  resp1(homfun(f), qgR(ker(f)))”));


val first_iso_thm = prove_store("first_iso_thm",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?fb:css(ker(f)) -> G2.
  fb o qmap(ker(f)) = homfun(f)’ >--
 (rpt strip_tac >>
 qby_tac ‘isghom(fb,qgrp(ker(f)),g2)’
 >-- (rw[isghom_def] >> rpt strip_tac >>
     qsspecl_then [‘g1’,‘ker(f)’,‘a’]
     (x_choose_then "x" assume_tac)
     css_rep_ex >>
     qsspecl_then [‘g1’,‘ker(f)’,‘b’]
     (x_choose_then "y" assume_tac)
     css_rep_ex >>
     arw[gmul_qgrp] >> arw[GSYM qmap_cs,GSYM App_App_o] >>
     rw[homfun_gmul]) >>
 qby_tac ‘Inj(fb)’ 
 >-- (rw[Inj_def] >> rpt strip_tac >>
     qsspecl_then [‘g1’,‘ker(f)’,‘x1’]
     (x_choose_then "a" assume_tac)
     css_rep_ex >>
     qsspecl_then [‘g1’,‘ker(f)’,‘x2’]
     (x_choose_then "b" assume_tac)
     css_rep_ex >> fs[] >>
     rfs[GSYM qmap_cs,GSYM App_App_o] >>
     fs[qmap_cs] >>
     rw[same_cs_cond] >> rw[rsg_rnsg_ker,IN_kers] >>
     arw[homfun_gmul,homfun_ginv,gmul_ginv]) >>
 uex_tac >> qexists_tac ‘ghm(fb,qgrp(ker(f)),g2)’ >>
 drule $ iffLR isghom_homfun_ghm >> arw[] >>
 rpt strip_tac >>
 arw[GSYM homfun_eq_eq]  >>
 qsspecl_then [‘g1’,‘ker(f)’] assume_tac qmap_Surj >>
 drule Surj_Epi >>
 first_x_assum irule >> arw[]) >>
 assume_tac
 (Quot_UMP |> qsspecl [‘qgR(ker(f:mem(ghom(g1:mem(Grp(G1)),
                                     g2:mem(Grp(G2))))))’]
         |> rewr_rule[qgR_ER]
         |> qsspecl [‘homfun(f:mem(ghom(g1:mem(Grp(G1)),
                                     g2:mem(Grp(G2)))))’]
         |> rewr_rule[homfun_resp1_qgR_ker] 
         |> qsspecl [‘Rcss(ker(f:mem(ghom(g1:mem(Grp(G1)),
                                     g2:mem(Grp(G2))))))’]
         |> rewr_rule[Quot_qgR_Rcss]
         |> qsspecl [‘ecs(ker(f:mem(ghom(g1:mem(Grp(G1)),
                                     g2:mem(Grp(G2))))))’]
         |> rewr_rule[FUN_EXT,abs_def,GSYM App_App_o,
                     GSYM qmap_def]
         |> uex2ex_rule) >>
 arw[])
(form_goal 
 “!G1 G2 g1:mem(Grp(G1)) g2:mem(Grp(G2)) f:mem(ghom(g1,g2)).
  ?!fb:mem(ghom(qgrp(ker(f)),g2)).
  Inj(homfun(fb)) &
  homfun(fb) o qmap(ker(f)) = homfun(f)”));


(*
val Card_bij = prove_store("Card_bij",
e0
(cheat)
(form_goal “!A B s1 s2.Card(s1) = Card(s2) <=>
 ?f:A->B. !b. IN(b,s2) ==> ?!a. IN(a,s1) & App(f,a) = b”));

val Lagrange_lemma = prove_store("Lagrange_lemma",
e0
(rpt strip_tac >>
 rw[Card_bij] >>
 qby_tac
 ‘!x.?!y.
 (?h.IN(h, rsg(H)) & x = gmul(g, a, h) & y = gmul(g, b, h)) |
 (!h. IN(h, rsg(H)) ==> ~(x = gmul(g, a, h))) & y = eof(g)’
 >-- (strip_tac >>
      qcases ‘?h. IN(h,rsg(H)) & x = gmul(g,a,h)’
      >-- (pop_assum strip_assume_tac >>
          uex_tac >>
          qexists_tac ‘gmul(g,b,h)’ >>
          arw[] >> rw[gmul_lcancel] >>
          rpt strip_tac (* 3 *)
          >-- (disj1_tac >> qexists_tac ‘h’ >> arw[]) 
          >-- arw[] >>
          first_x_assum (qspecl_then [‘h’] assume_tac) >>
          rfs[]) >>
      qby_tac
      ‘!h. IN(h,rsg(H)) ==> ~(x = gmul(g,a,h))’ 
      >-- (rpt strip_tac >>
          ccontra_tac >>
          qsuff_tac ‘?h. IN(h,rsg(H)) &(x = gmul(g,a,h))’ 
          >-- arw[] >>
          qexists_tac ‘h’ >> arw[]) >>
      arw[] >>
      uex_tac >> qexists_tac ‘eof(g)’ >>
      arw[] >> rpt strip_tac >> arw[] >>
      qsuff_tac ‘?h. IN(h,rsg(H)) &(x = gmul(g,a,h))’ 
      >-- arw[] >> qexists_tac ‘h’ >> arw[]) >> 
 drule 
 (P2fun' |> qspecl [‘G’,‘G’]
 |> fVar_sInst_th “P(x:mem(G),y:mem(G))”
    “(?h.IN(h:mem(G),rsg(H:mem(sgrp(g)))) & x = gmul(g,a,h) & y = gmul(g,b,h)) | (!h. IN(h:mem(G),rsg(H)) ==> ~(x = gmul(g,a,h))) &
       y = eof(g)”) >>
 qsuff_tac
 ‘?f:G->G.
  !h.IN(h,rsg(H)) ==> App(f,gmul(g,a,h)) = gmul(g,b,h)’
 >-- (rpt strip_tac >>
     qexists_tac ‘f’ >> rpt strip_tac >>
     uex_tac >>
     fs[lcs_lsmul,lsmul_def] >>
     qexists_tac ‘gmul(g,a,y)’ >> rpt strip_tac (* 3 *)
     >-- (qexists_tac ‘y’ >> arw[]) 
     >-- (first_x_assum irule >> arw[]) >> 
     fs[] >> rfs[] >>
     first_x_assum drule >>
     arw[gmul_lcancel] >> 
     irule $ iffLR gmul_lcancel >>
     qexistsl_tac [‘g’,‘b’] >> 
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘gmul(g,a,h)’] assume_tac) >>
 fs[gmul_lcancel] >>
 first_x_assum (qspecl_then [‘h’] assume_tac)  >>
 rfs[])
(form_goal
 “!G g:mem(Grp(G)) H:mem(sgrp(g)) a b.
  Card(lcs(a,H)) = Card(lcs(b,H))”));


(*
val Lagrange_theorem = prove_store("Lagrange_theorem",
e0
()
(form_goal
 “”));

val sgrp_Grp = prove_store("sgrp_Grp",
e0
()
(form_goal
 “!G g:mem(Grp(G)) sh:mem(sgrp(g)).
  ?H h:mem(Grp(H)). 
  ”));

val isgiso_def = qdefine_psym("isgiso",[‘f:mem(ghom(g1:mem(Grp(G1)),g2:mem(Grp(G2))))’]) ‘Bij(homfun(f))’
|> gen_all 


val second_iso_thm = prove_store("second_iso_thm",
e0
()
(form_goal “!G g:mem(Grp(G)) H:sgrp(g) K:nsgrp(g).
 
 ?phi:hom(qg(sg2G(H),),qgrp(grp(smul(g,rsg(),rsg())))). isgiso(phi) ”));


val second_iso_thm = prove_store("second_iso_thm",
e0
()
(form_goal “!G g:mem(Grp(G)) sh:sgrp(g) sk:nsgrp(g)
  H h:mem(Grp(H)) ih:mem(ghom(h,g))
  HK hk:mem(Grp(HK)) ihk:mem(ghom(hk,g)) 
  HiK:mem(nsgrp())  


 ?


 hh: hk
 ?phi:hom(qgrp(),qgrp(grp(smul(g,rsg(),rsg())))). giso(phi) ”));
*)

*)
