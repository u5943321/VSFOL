
val iscoPr_def = qdefine_psym("iscoPr",[‘i1:A->AB’,‘i2:B->AB’])
‘!X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g’
|> qgenl [‘A’,‘B’,‘AB’,‘i1’,‘i2’]
|> store_as "iscoPr_def";



val iscoPr_ex = prove_store("iscoPr_ex",
e0
cheat
(form_goal “!A B.?AB i1:A->AB i2:B->AB.iscoPr(i1,i2)”));



val coPo_def = iscoPr_ex |> spec_all 
                         |> qSKOLEM "+" [‘A’,‘B’] |> gen_all
                         |> store_as "coPo_def";

val i1_def = coPo_def |> spec_all 
                      |> qSKOLEM "i1" [‘A’,‘B’] |> gen_all
                      |> store_as "i1_def";

val i2_def = i1_def |> spec_all |> qSKOLEM "i2" [‘A’,‘B’] |> gen_all
                    |> store_as "i2_def";

val coPa_def = i2_def |> rewr_rule[iscoPr_def] |> spec_all
                      |> uex_expand 
                      |> qSKOLEM "coPa" [‘f’,‘g’]
                      |> gen_all
                      |> store_as "coPa_def";


val BU_ex = prove_store("BU_ex",
e0
(cheat)
(form_goal
 “!A. ?!BU:Pow(Pow(A)) -> Pow(A). 
  !sss a:mem(A). IN(a,App(BU,sss)) <=>
  ?ss.IN(ss,sss) & IN(a,ss)”));
 

val BU_def = BU_ex |> spec_all |> uex2ex_rule
                         |> qSKOLEM "BU" [‘A’]
                         |> gen_all
                         |> store_as "BU_def"; 


val BIGUNION_def = qdefine_fsym("BIGUNION",[‘sss:mem(Pow(Pow(A)))’])
‘App(BU(A),sss)’ |> gen_all |> store_as "BIGUNION_def";


val IN_BIGUNION = BU_def |> rewr_rule[GSYM BIGUNION_def] 
                         |> store_as "IN_BIGUNION";


val prims_def = proved_th $
e0
cheat
(form_goal “!A f:Pow(A) ->Pow(A).
 ?!prims:mem(Pow(Pow(A))).
 !sa.IN(sa,prims) <=> SS(sa,App(f,sa))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "prims" [‘f’]

val gfp_def = qdefine_fsym("gfp",[‘f:Pow(A) -> Pow(A)’])
‘BIGUNION(prims(f))’ |> gen_all 


val IN_gfp = prove_store("IN_gfp",
e0
(cheat)
(form_goal “!f a:mem(A). 
 IN(a,gfp(f)) <=> ?sa. SS(sa,App(f,sa)) & IN(a,sa)”));

val weak_coind = prove_store("weak_coind",
e0
(rpt strip_tac >> rw[IN_gfp] >>
 qexists_tac ‘sa’ >> arw[])
(form_goal “!A sa a:mem(A) f.IN(a,sa) & SS(sa,App(f,sa)) ==> IN(a,gfp(f))  ”));

val monotone_def = qdefine_psym("monotone",[‘f:Pow(A)->Pow(B)’])
‘!s1 s2. SS(s1,s2) ==> SS(App(f,s1), App(f, s2))’ |> gen_all


val SS_gfp_fgfp = prove_store("SS_gfp_fgfp",
e0
(rw[SS_def,IN_gfp] >> 
 rpt strip_tac >>
 first_assum drule >> fs[monotone_def] >>
 qsuff_tac ‘SS(App(f,sa),App(f,gfp(f)))’ 
 >-- (rw[SS_def] >> rpt strip_tac >> first_x_assum irule >> arw[]) >>
 first_x_assum irule >> 
 rw[SS_def,IN_gfp] >> rpt strip_tac >>
 qexists_tac ‘sa’ >> arw[])
(form_goal
 “monotone(f:Pow(A)->Pow(A)) ==> SS(gfp(f), App(f,gfp(f)))”));


val rules0 = prove_store("rule0",
e0
(rw[SS_def,IN_gfp] >> rpt strip_tac >>
 assume_tac SS_gfp_fgfp >> first_x_assum drule >> 
 qexists_tac ‘gfp(f)’ >> arw[GSYM SS_def] >>
 rw[IN_gfp] >> qexists_tac ‘App(f,gfp(f))’ >> arw[] >>
 fs[monotone_def] >> first_x_assum irule >> arw[])
(form_goal
 “monotone(f:Pow(A) -> Pow(A)) ==> SS(App(f,gfp(f)),
 gfp(f))”));


val cases0 = prove_store("cases0",
e0
(rpt strip_tac >> irule SS_SS_eq >>
 drule rules0 >> drule SS_gfp_fgfp >> arw[])
(form_goal “monotone(f) ==> gfp(f:Pow(A) -> Pow(A)) =  App(f,gfp(f))”))

val coind0 = prove_store("coind0",
e0
(rpt strip_tac >> rw[SS_def] >> rpt strip_tac >> irule weak_coind >>
 qexists_tac ‘sa’ >> arw[])
(form_goal “!f:Pow(A) ->Pow(A) sa. SS(sa,App(f,sa)) ==> SS(sa,gfp(f))”));

(*inc to option*)

val Inc_def = qdefine_fsym("Inc",[‘a:mem(A)’])
‘App(i1(A,1),a)’ |> gen_all

val shift1_def = proved_th $
e0
(cheat)
(form_goal “!X f0:N->X + 1 x.?!f. 
 App(f,O) = Inc(x) & 
 (!n. App(f,Suc(n)) = App(f0,n))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "shift1" [‘x’,‘f0’]
|> gen_all 

val Null_def = proved_th $
e0
cheat
(form_goal “!X. ?!f:N->X+1.!n. App(f,n) = App(i2(X,1),dot)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Null" [‘X’]
|> gen_all

val tof_def = proved_th $
e0
cheat
(form_goal “!A B f0:mem(Exp(A,B)).
 ?!f:A->B. 
 !a. App(Ev(A,B),Pair(a,f0)) = App(f,a)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "tof" [‘f0’]

val llf_uex = prove_store("llf_uex",
e0
(cheat)
(form_goal
 “?!f: Pow(Exp(N,X+1)) -> Pow(Exp(N,X+1)).
  !gs:mem(Pow(Exp(N,X+1))) g.
  IN(g,App(f,gs)) <=>
  g = Tpm(Null(X)) |
  ?h t. g  = Tpm(shift1(h,t)) & IN(Tpm(t),gs)”));

val llf_def = llf_uex |> uex2ex_rule |> qSKOLEM "llf" [‘X’]
                      |> gen_all

val llf_monotone = prove_store("llf_monotone",
e0
cheat
(form_goal “!X.monotone(llf(X))”));

val islls_def = qdefine_fsym("islls",[‘X’]) ‘gfp(llf(X))’


val llist_def1 = Thm_2_4 |> qspecl [‘Exp(N,X+1)’]
                         |> fVar_sInst_th
                         “P(g:mem(Exp(N,X+1)))”
                         “IN(g,islls(X))”
                         |> qSKOLEM "llist" [‘X’] 
                         |> qSKOLEM "repll" [‘X’]
                         |> gen_all 

val repll_Inj = llist_def1 |> spec_all 
                          |> conjE1 |> gen_all
                          |> store_as "repll_Inj"; 

val ll_rules = rules0 |> gen_all |> qsspecl [‘llf(X)’] 
                       |> C mp (llf_monotone |> spec_all)
                       |> rewr_rule[SS_def,llf_def] 
                       |> mk_rules2 |> mk_rules3
                       |> rewr_rule[GSYM islls_def]
                       |> gen_all

val ll_coind = coind0 |> gen_all |> qspecl [‘Exp(N,X + 1)’,‘llf(X)’]
                      |> rewr_rule[SS_def,llf_def]
                      |> rewr_rule[GSYM islls_def]
                      |> gen_all

val ll_cases = cases0 |> gen_all |> qsspecl [‘llf(X)’] 
                      |> C mp (llf_monotone |> spec_all)
                      |> rewr_rule[GSYM IN_EXT,llf_def]
                      |> rewr_rule[GSYM islls_def]
                      |> gen_all


val isll_def = qdefine_psym("isll",[‘l:mem(Exp(N,X + 1))’]) 
                          ‘IN(l,islls(X))’
                          |> gen_all |> store_as "isll_def"; 



val isll_lnil = prove_store("isll_lnil",
e0
(rw[isll_def,ll_rules])
(form_goal
 “!X. isll(Tpm(Null(X)))”)); 


val isll_shift = ll_rules |> spec_all |> conjE2 
                        |> rewr_rule[GSYM isll_def]
                        |> spec_all |> undisch 
                        |> gen_all |> disch_all
                        |> gen_all |> store_as "isll_shift";



val Repll_def = qdefine_fsym ("Repll",[‘l:mem(llist(X))’])
                            ‘App(repll(X),l)’
                            |> gen_all |> store_as "Repll_def";

val llist_def = llist_def1 |> rewr_rule[GSYM isll_def]


val LNil_def = proved_th $
e0
(strip_tac >> uex_tac >>
 qspecl_then [‘X’] strip_assume_tac llist_def >>
 first_assum (qspecl_then [‘Tpm(Null(X))’] assume_tac) >>
 fs[isll_lnil,GSYM isll_def] >>
 qexists_tac ‘b’ >> arw[Repll_def] >>
 fs[Inj_def])
(form_goal “!X. ?!l.Repll(l) = Tpm(Null(X))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "LNil" [‘X’] |> gen_all
|> store_as "LNil_def";

val repll_isll = prove_store("repll_isll",
e0
(rpt strip_tac >> 
 qspecl_then [‘X’] assume_tac llist_def >>
 fs[] >> qexists_tac ‘ll’ >> rw[])
(form_goal “!X ll. isll(App(repll(X) ,ll))”)); 


val isll_Repll = llist_def |> spec_all |> conjE2
                        |> rewr_rule[GSYM isll_def,
                                     GSYM Repll_def] 
                        |> gen_all 
                        |> store_as "isll_Repll";


val LCons_def = proved_th $
e0
(cheat)
(form_goal
 “!X xl1:mem(X * llist(X)).?!l2.
  Repll(l2) = Tpm(shift1(Fst(xl1),tof(Repll(Snd(xl1)))))”)
|> qspecl [‘X’,‘Pair(x:mem(X),ll:mem(llist(X)))’]
|> uex2ex_rule |> rewr_rule[Pair_def'] 
|> qSKOLEM "LCons" [‘x’,‘ll’] |> gen_all


val Repll_eq_eq = prove_store("Repll_eq_eq",
e0
(rpt strip_tac >> rw[Repll_def] >> irule Inj_eq_eq >>
 rw[repll_Inj])
(form_goal “!X l1:mem(llist(X)) l2.
 Repll(l1) = Repll(l2) <=> l1 = l2”));


val LCons_NONLNIL = prove_store("LCons_NONLNIL",
e0
(cheat)
(form_goal
 “!X x l. ~(LCons(x,l) = LNil(X))”));


val Repll_lnil_uex = prove_store("Repl_lnil_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[LNil_def] >>
 rw[GSYM Repll_eq_eq] >> arw[LNil_def])
(form_goal
 “!X l. Repll(l) = Tpm(Null(X)) <=> l = LNil(X)”));

val lnil_def = qdefine_fsym("lnil",[‘X’]) ‘Tpm(Null(X))’

val NONE_def = qdefine_fsym("NONE",[‘X’])
‘App(i2(X,1),dot)’

val llcrf_def = proved_th $
e0
cheat
(form_goal
 “!X h:A -> (X * A) + 1. 
  ?!f:Pow(A * llist(X)) -> Pow(A * llist(X)).
  !ps0 p. IN(p,App(f,ps0)) <=>
  (App(h,Fst(p)) = NONE(X * A) & Snd(p) = LNil(X)) |
  (?a0 ll0 x. IN(Pair(a0,ll0),ps0) &
              App(h,Fst(p)) = Inc(Pair(x,a0)) & 
              Snd(p) = LCons(x,ll0))”)

(*FUNPOW*)
val FP_def = proved_th $
e0
cheat
(form_goal “!f:X->X.?!fp:N * X -> X.
 !x. App(fp,Pair(O,x)) = x & 
     !n. App(fp,Pair(Suc(n),x)) = App(fp,Pair(n,App(f,x)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "FP" [‘f’]

(*OPTION_MAP*)

val OM_def = proved_th $
e0
cheat
(form_goal
 “!A B f:A->B. ?!om:A+1 -> B + 1.
   App(om,NONE(A)) = NONE(B) &
  (!a. App(om,Inc(a)) = Inc(App(f,a)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "OM" [‘f’]

(*OPTION_BIND*)

val OB_def = proved_th $
e0
cheat
(form_goal
 “!A B f:A->B + 1.?!ob.
 App(ob,Pair(NONE(A),Tpm(f))) = NONE(B) &
 !a.App(ob,Pair(Inc(a),Tpm(f))) = App(f,a)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "OB" [‘f’]

“!f:A->B + 1 a.
 ”

“!X h:A->(X * A)+1 a.  ?!g:N -> X + 1.
 (!a x a0. App(h,a) = Inc(Pair(x,a0)) ==>
  App(g,O) = Inc(x) &
  (!n x1 a1. App(g,Suc(n)) =  ))
 ”
