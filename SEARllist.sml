val BU_ex = prove_store("BU_ex",
e0
(strip_tac >>
 qsuff_tac
 ‘?BU:Pow(Pow(A)) -> Pow(A). 
  !sss a:mem(A). IN(a,App(BU,sss)) <=>
  ?ss.IN(ss,sss) & IN(a,ss)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘BU’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >> strip_tac >>
     irule IN_EXT >> arw[]) >>
 irule 
 (P2fun' |> qspecl [‘Pow(Pow(A))’,‘Pow(A)’]
 |> fVar_sInst_th “P(sss:mem(Pow(Pow(A))),u:mem(Pow(A)))”
    “!a:mem(A). IN(a,u) <=>
           (?ss.IN(ss,sss) & IN(a,ss))”) >>
 strip_tac >>
 accept_tac (IN_def_P |> qspecl [‘A’] |> fVar_sInst_th “P(a:mem(A))”
 “ (?ss.IN(ss,x) & IN(a:mem(A),ss))”)
 )
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
(rpt strip_tac >>
accept_tac (IN_def_P |> qspecl [‘Pow(A)’] 
 |> fVar_sInst_th “P(sa:mem(Pow(A)))” “SS(sa,App(f:Pow(A) -> Pow(A),sa))”))
(form_goal “!A f:Pow(A) ->Pow(A).
 ?!prims:mem(Pow(Pow(A))).
 !sa.IN(sa,prims) <=> SS(sa,App(f,sa))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "prims" [‘f’]

val gfp_def = qdefine_fsym("gfp",[‘f:Pow(A) -> Pow(A)’])
‘BIGUNION(prims(f))’ |> gen_all 


val IN_gfp = prove_store("IN_gfp",
e0
(rw[gfp_def,IN_BIGUNION,prims_def])
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

val SOME_def = qdefine_fsym("SOME",[‘a:mem(A)’])
‘App(i1(A,1),a)’ |> gen_all

val lcons0_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?f. 
 App(f,O) = SOME(x) & 
 (!n. App(f,Suc(n)) = App(f0,n))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >>
     irule $ iffLR FUN_EXT >> ind_with N_induct >>
     arw[]) >>
 assume_tac(P2fun' |> qspecl [‘N’,‘X + 1’] 
 |> fVar_sInst_th “P(n:mem(N),x1:mem(X+1))”
    “(n = O & x1 = SOME(x)) | (?n0. n = Suc(n0) & x1 = App(f0:N->X+1,n0))”) >>
 qsuff_tac
 ‘?f :N -> X+1.
   !a:mem(N). (a = O & App(f, a) = SOME(x)) |
 ?n0:mem(N). a = Suc(n0) & App(f, a) = App(f0, n0)’ 
 >-- (strip_tac >> qexists_tac ‘f’ >>  
     first_assum (qspecl_then [‘O’] assume_tac) >> fs[] >--
     (rpt strip_tac >>
     first_x_assum (qspecl_then [‘Suc(n)’] assume_tac) >>
     fs[Suc_NONZERO] >> fs[Suc_eq_eq]) >> fs[GSYM Suc_NONZERO]) >>
 first_x_assum irule >>
 ind_with N_induct >> strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘SOME(x)’ >> rw[] >> rw[GSYM Suc_NONZERO] >>
     rpt strip_tac >> arw[]) >>
 rpt strip_tac >> rw[Suc_NONZERO] >> rw[Suc_eq_eq] >> uex_tac >>
 qexists_tac ‘App(f0,n)’ >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘n’ >> rw[]) >>
 arw[])
(form_goal “!X f0:N->X + 1 x.?!f. 
 App(f,O) = SOME(x) & 
 (!n. App(f,Suc(n)) = App(f0,n))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "lcons0" [‘x’,‘f0’]
|> gen_all 



val NONE_def = qdefine_fsym("NONE",[‘X’])
‘App(i2(X,1),dot)’

val Null_def = proved_th $
e0
(strip_tac >> rw[GSYM NONE_def] >>
 qsuff_tac
 ‘?f:N->X+1.!n. App(f,n) = NONE(X)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rw[GSYM FUN_EXT] >> rpt strip_tac >> arw[]) >>
 assume_tac (P2fun' |> qspecl [‘N’,‘X + 1’] 
 |> fVar_sInst_th “P(n:mem(N),x1:mem(X+1))” “x1 = NONE(X)”) >>
 first_x_assum irule >> strip_tac >> uex_tac >> qexists_tac ‘NONE(X)’ >>
 rw[] >> rpt strip_tac >> arw[])
(form_goal “!X. ?!f:N->X+1.!n. App(f,n) = App(i2(X,1),dot)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Null" [‘X’]
|> gen_all

val llf_uex = prove_store("llf_uex",
e0
(qsuff_tac
 ‘?f: Pow(Exp(N,X+1)) -> Pow(Exp(N,X+1)).
  !gs:mem(Pow(Exp(N,X+1))) g.
  IN(g,App(f,gs)) <=>
  g = Tpm(Null(X)) |
  ?h t. g  = Tpm(lcons0(h,t)) & IN(Tpm(t),gs)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >> rpt strip_tac >>
     rw[GSYM FUN_EXT] >> strip_tac >> rw[GSYM IN_EXT_iff] >> arw[]) >>
 assume_tac
 (P2fun' |> qspecl [‘Pow(Exp(N,X+1))’,‘Pow(Exp(N,X+1))’] 
         |> fVar_sInst_th “P(s0:mem(Pow(Exp(N,X+1))),s1 :mem(Pow(Exp(N,X+1))))”
         “!g. IN(g,s1) <=> 
         g = Tpm(Null(X)) |
  ?h t. g  = Tpm(lcons0(h,t)) & IN(Tpm(t),s0:mem(Pow(Exp(N,X+1))))”) >>
 qby_tac
 ‘!s0. ?!y. !g. IN(g,y) <=> 
  g = Tpm(Null(X)) |
  ?h t. g  = Tpm(lcons0(h,t)) & IN(Tpm(t),s0:mem(Pow(Exp(N,X+1))))’
 >-- (strip_tac >> 
 assume_tac (IN_def_P |> qspecl [‘Exp(N,X+1)’]
                      |> fVar_sInst_th “P(g:mem(Exp(N,X+1)))”
                         “g = Tpm(Null(X)) |
  ?h t. g  = Tpm(lcons0(h,t)) & IN(Tpm(t),s0:mem(Pow(Exp(N,X+1))))”) >>
 arw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >> arw[])
(form_goal
 “?!f: Pow(Exp(N,X+1)) -> Pow(Exp(N,X+1)).
  !gs:mem(Pow(Exp(N,X+1))) g.
  IN(g,App(f,gs)) <=>
  g = Tpm(Null(X)) |
  ?h t. g  = Tpm(lcons0(h,t)) & IN(Tpm(t),gs)”));

val llf_def = llf_uex |> uex2ex_rule |> qSKOLEM "llf" [‘X’]
                      |> gen_all



val Tpm_eq_eq = prove_store("Tpm_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >> 
 irule $ iffLR FUN_EXT >>
 once_rw[GSYM Tpm_def] >> arw[])
(form_goal “!A B f1:A->B f2. Tpm(f1) = Tpm(f2) <=> f1 = f2”));

val llf_monotone = prove_store("llf_monotone",
e0
(rw[monotone_def,llf_def,SS_def] >> rpt strip_tac >> arw[Tpm_eq_eq] >>
 disj2_tac >> qexistsl_tac [‘h’,‘t’] >> arw[] >> first_x_assum irule >> arw[])
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
 
val Repll_isll = repll_isll |> rewr_rule[GSYM Repll_def]

val isll_rules = ll_rules |> rewr_rule[GSYM isll_def]

val isll_lcons0 = isll_rules |> spec_all |> conjE2 
                             |> spec_all |> undisch |> gen_all
                             |> disch_all |> gen_all

val Tpm_tof_inv = prove_store("Tpm_tof_inv",
e0
(flip_tac >> rpt strip_tac >> irule is_Tpm >>
 rw[tof_def])
(form_goal
 “!A B f:mem(Exp(A,B)). Tpm(tof(f))  = f”));


val Repll_eq_eq = prove_store("Repll_eq_eq",
e0
(rpt strip_tac >> rw[Repll_def] >> irule Inj_eq_eq >>
 rw[repll_Inj])
(form_goal “!X l1:mem(llist(X)) l2.
 Repll(l1) = Repll(l2) <=> l1 = l2”));



val LCons_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?l2.
  Repll(l2) = Tpm(lcons0(Fst(xl1),tof(Repll(Snd(xl1)))))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘l2’ >> arw[] >>
     rpt strip_tac >> arw[GSYM Repll_eq_eq]) >>
 qsspecl_then [‘xl1’] (x_choosel_then ["x1","l1"] assume_tac) Pair_has_comp >>
 arw[Pair_def'] >> 
 qsspecl_then [‘l1’] assume_tac Repll_isll >>
 qby_tac ‘isll(Tpm(tof(Repll(l1))))’ 
 >-- arw[Tpm_tof_inv] >>
 drule isll_lcons0 >>
 first_x_assum (qspecl_then [‘x1’] assume_tac) >>
 fs[isll_Repll] >> qexists_tac ‘b''’ >> rw[])
(form_goal
 “!X xl1:mem(X * llist(X)).?!l2.
  Repll(l2) = Tpm(lcons0(Fst(xl1),tof(Repll(Snd(xl1)))))”)
|> qspecl [‘X’,‘Pair(x:mem(X),ll:mem(llist(X)))’]
|> uex2ex_rule |> rewr_rule[Pair_def'] 
|> qSKOLEM "LCons" [‘x’,‘ll’] |> gen_all


val SOME_NOTNONE = prove_store("SOME_NOTNONE",
e0
(rpt strip_tac >> rw[SOME_def,NONE_def] >> rw[i1_ne_i2])
(form_goal “!X x.~(SOME (x) = NONE(X)) ”));


val LCons_NONLNIL = prove_store("LCons_NONLNIL",
e0
(rpt strip_tac >> rw[GSYM Repll_eq_eq,LCons_def,LNil_def,Tpm_eq_eq] >>
 rw[GSYM FUN_EXT] >> ccontra_tac >>
 first_x_assum (qspecl_then [‘O’] assume_tac) >>
 fs[lcons0_def,Null_def,GSYM NONE_def,SOME_NOTNONE] )
(form_goal
 “!X x l. ~(LCons(x,l) = LNil(X))”));


val Repll_lnil_uex = prove_store("Repl_lnil_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[LNil_def] >>
 rw[GSYM Repll_eq_eq] >> arw[LNil_def])
(form_goal
 “!X l. Repll(l) = Tpm(Null(X)) <=> l = LNil(X)”));

val lnil_def = qdefine_fsym("lnil",[‘X’]) ‘Tpm(Null(X))’


(*
val llcrf_def = proved_th $
e0
cheat
(form_goal
 “!X h:A -> (X * A) + 1. 
  ?!f:Pow(A * llist(X)) -> Pow(A * llist(X)).
  !ps0 p. IN(p,App(f,ps0)) <=>
  (App(h,Fst(p)) = NONE(X * A) & Snd(p) = LNil(X)) |
  (?a0 ll0 x. IN(Pair(a0,ll0),ps0) &
              App(h,Fst(p)) = SOME(Pair(x,a0)) & 
              Snd(p) = LCons(x,ll0))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "llcrf"  [‘h’]
|> gen_all

val llcrf_monotone = proved_th $
e0
cheat
(form_goal 
“!h:A -> (X * A) + 1. monotone(llcrf(h))”)

val llcrf_cases0 = 
 cases0 |> gen_all |> qsspecl [‘llcrf(h:A -> (X * A) + 1)’] 
        |> C mp (llcrf_monotone |> spec_all)
        |> rewr_rule[GSYM IN_EXT]
        |> conv_rule (depth_fconv no_conv forall_cross_fconv)
        |> rewr_rule[GSYM IN_EXT_iff]
        |> rewr_rule[llcrf_def]
        |> gen_all
        |> qspecl [‘A’,‘X’,‘h:A -> (X * A) + 1’,
                   ‘Pair(a:mem(A),ll:mem(llist(X)))’]
        |> rewr_rule[Pair_def']


val llcrf_rules0 =
    rules0 |> gen_all |> qsspecl [‘llcrf(h:A -> (X * A) + 1)’] 
           |> C mp (llcrf_monotone |> spec_all)
           |> rewr_rule[SS_def] 
           |> conv_rule (depth_fconv no_conv forall_cross_fconv)
           |> rewr_rule[llcrf_def,Pair_def']
           |> mk_rules2 |> mk_rules3
           |> gen_all


(*
(pull_conj_fconv is_eq)

“P(q) & a = b:A->B & P(c) & c  = d:C->D”


!a c. a = b ==> P(a)

1.look at a var quantifier, find if there is some a(quantified var) = b or b = a, if there is, and if lower variables does not depend on this, then move the quantifier in, move the eqn, eliminate it. This completes the conv. Otherwise just fail, therefore can do depth_conv on this
t      
 check if some vars among these quantifiers 

!a. a = b ==> P(a)
*)

(*either subst in immediately after pull eqlity to LHS 
  HOL does this.

, or call recursively on the rest of conjuncts*)

val llcrf_coind0 = 
    coind0 |> gen_all |> qspecl [‘A * llist(X)’,‘llcrf(h:A -> (X * A) + 1)’]
                      |> rewr_rule[SS_def]
                      |> conv_rule (depth_fconv no_conv forall_cross_fconv)
                      |> rewr_rule[llcrf_def,Pair_def']
                      |> gen_all
*)
                       
(*
val Expo_def = proved_th $
e0
cheat
(form_goal
 “!A B C.?!expo:Exp(A,B) * Exp(B,C) -> Exp(A,C).
  !f:A->B g:B->C.
   App(expo,Pair(Tpm(f),Tpm(g))) = ”)
*)




(*FUNPOW*)
val FP_def = proved_th $
e0
(strip_tac >> 
 qby_tac
 ‘?h:Exp(X,X) -> Exp(X,X). 
  !f0. App(h,f0) = Tpm(tof(f0) o f)’
 >-- (irule (P2fun' |> qspecl [‘Exp(X,X)’,‘Exp(X,X)’] 
 |> fVar_sInst_th “P(g1:mem(Exp(X,X)),g2:mem(Exp(X,X)))”
     “g2 = Tpm(tof(g1:mem(Exp(X,X))) o f:X->X)”) >>
     strip_tac >> uex_tac  >> qexists_tac ‘Tpm(tof(x) o f)’ >> rw[]) >>
 pop_assum strip_assume_tac >>
 assume_tac
 (Thm1_case_1 |> qspecl [‘Exp(X,X)’,‘El(Tpm(Id(X)))’,‘h:Exp(X,X) ->Exp(X,X) o p2(N,Exp(X,X))’]
 |> rewr_rule[p12_of_Pa,o_assoc]) >>
 qsuff_tac
 ‘?fp:N * X -> X.
 !x. App(fp,Pair(O,x)) = x & 
     !n. App(fp,Pair(Suc(n),x)) = App(fp,Pair(n,App(f,x)))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘fp’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >>
     qsuff_tac
     ‘!n x. App(fp',Pair(n,x)) = App(fp,Pair(n,x))’ 
     >-- (rpt strip_tac >>
         qsspecl_then [‘a’] strip_assume_tac Pair_has_comp >>
         arw[]) >>
     ind_with N_induct >> arw[] >> rpt strip_tac >> arw[]) >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choosel_then ["f1"] assume_tac) >>
 qby_tac
 ‘?fp:N * X ->X.
   !n x. App(fp,Pair(n,x)) = App(tof(App(f1,n)),x)’
 >-- (irule (P2fun' |> qspecl [‘N * X’,‘X’] 
                   |> fVar_sInst_th “P(nx:mem(N * X),x1:mem(X))”
                   “x1 = App(tof(App(f1:N->Exp(X,X),Fst(nx))),Snd(nx))”
                   |> conv_rule (depth_fconv no_conv forall_cross_fconv) 
                   |> rewr_rule[Pair_def']) >>
     rpt strip_tac >> uex_tac >> qexists_tac ‘App(tof(App(f1, a)), b)’ >>
     rw[]) >> pop_assum strip_assume_tac >>
 qexists_tac ‘fp’ >> arw[] >> rpt strip_tac (*2 *)
 >-- (fs[GSYM FUN_EXT] >>
     first_x_assum (qspecl_then [‘dot’] assume_tac) >>
     fs[App_App_o,El_def,tof_Tpm_inv,Id_def]) >>
 fs[GSYM FUN_EXT] >> 
 last_x_assum (qspecl_then [‘n’] assume_tac) >>
 fs[App_App_o,GSYM Suc_def,tof_Tpm_inv])
(form_goal “!f:X->X.?!fp:N * X -> X. 
 !x. App(fp,Pair(O,x)) = x & 
     !n. App(fp,Pair(Suc(n),x)) = App(fp,Pair(n,App(f,x)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "FP" [‘f’]

(*OPTION_MAP
 (∀f x. OPTION_MAP f:α->β (SOME x) = SOME (f x)) ∧
     ∀f. OPTION_MAP f NONE = NONE
*)


val SOME_eq_eq = prove_store("SOME_eq_eq",
e0
(rw[SOME_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 assume_tac i1_Inj >> fs[Inj_def] >> 
 first_x_assum drule >> arw[])
(form_goal “!X x1:mem(X) x2. SOME(x1) = SOME(x2) <=> x1 = x2”));


val option_xor = prove_store("option_xor",
e0
(rpt strip_tac >> rw[NONE_def,SOME_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qsuff_tac ‘?a0. a1 = App(i1(A,1),a0)’ 
     >-- (strip_tac >> uex_tac >> qexists_tac ‘a0’ >> arw[] >>
         qspecl_then [‘A’,‘1’] assume_tac i1_Inj >> fs[Inj_def] >>
         rpt strip_tac >> first_x_assum irule >> arw[]) >>
     rw[GSYM i2_xor_i1] >> ccontra_tac >> fs[dot_def]) >>
 pop_assum (assume_tac o uex2ex_rule) >> 
 drule $ iffRL i2_xor_i1 >> ccontra_tac >>
 qsuff_tac ‘?b. a1 = App(i2(A, 1), b)’ >-- arw[] >>
 qexists_tac ‘dot’ >> arw[])
(form_goal “!A a1:mem(A+1). ~(a1 = NONE(A)) <=> ?!a0. a1 = SOME(a0)”));


val OM_def = proved_th $
e0
(rpt strip_tac >> 
 qsuff_tac
 ‘?om:A+1 -> B + 1.
   App(om,NONE(A)) = NONE(B) &
  (!a. App(om,SOME(a)) = SOME(App(f,a)))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘om’ >> arw[] >>
     rpt strip_tac >> rw[GSYM FUN_EXT] >> strip_tac >>
     qcases ‘a = NONE(A)’ (* 2 *)
     >-- arw[] >>
     fs[option_xor] >> pop_assum (strip_assume_tac o uex2ex_rule) >>
     arw[]) >>
 assume_tac 
 (P2fun' |> qspecl [‘A + 1’,‘B + 1’] 
         |> fVar_sInst_th “P(a1:mem(A+1),b1:mem(B + 1))”
         “(a1 = NONE(A) & b1 = NONE(B)) |
          (?a.a1 = SOME(a) & b1 = SOME(App(f:A->B,a)))”) >>
 qsuff_tac
 ‘?f':A+1->B+1. 
 !a1. (a1 = NONE(A) & App(f',a1) = NONE(B)) | 
(?a.a1 = SOME(a) & App(f',a1) = SOME(App(f,a)))’
 >-- (strip_tac >> qexists_tac ‘f'’ >> 
     first_assum (qspecl_then [‘NONE(A)’] assume_tac) >>
     fs[GSYM SOME_NOTNONE] >> strip_tac >>
     first_x_assum (qspecl_then [‘SOME(a)’] assume_tac) >> 
     fs[SOME_NOTNONE,SOME_eq_eq]) >>
 first_x_assum irule >>
 strip_tac >> uex_tac >>
 qcases ‘x = NONE(A)’ >> arw[GSYM SOME_NOTNONE] (* 2 *)
 >-- (qexists_tac ‘NONE(B)’ >> rw[] >> rpt strip_tac >> arw[]) >>
 fs[option_xor] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 arw[SOME_eq_eq] >> qexists_tac ‘SOME(App(f,a0))’ >> 
 rpt strip_tac >> arw[] >>
 qexists_tac ‘a0’ >> arw[])
(form_goal
 “!A B f:A->B. ?!om:A+1 -> B + 1.
   App(om,NONE(A)) = NONE(B) &
  (!a. App(om,SOME(a)) = SOME(App(f,a)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "OM" [‘f’]

(*OPTION_BIND
(∀f. OPTION_BIND NONE f:β->α opt = NONE) ∧ ∀x f. OPTION_BIND (SOME x) f = f x

*)

val OB_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?ob.!f.
 App(ob,Pair(NONE(A),Tpm(f))) = NONE(B) &
 !a.App(ob,Pair(SOME(a),Tpm(f))) = App(f,a)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘ob’ >> arw[]>> rpt strip_tac >>
     rw[GSYM FUN_EXT] >> strip_tac >>
     qsspecl_then [‘a’] (x_choosel_then ["a1","f0"] assume_tac) Pair_has_comp >>
     arw[] >>
     qcases ‘a1 = NONE(A)’ 
     >-- (fs[] >>
         first_x_assum (qspecl_then [‘tof(f0)’] assume_tac) >>
         last_x_assum (qspecl_then [‘tof(f0)’] assume_tac) >> 
         fs[Tpm_tof_inv]) >>
     fs[option_xor] >>
     pop_assum (strip_assume_tac o uex2ex_rule) >> arw[] >>
     first_x_assum (qspecl_then [‘tof(f0)’] assume_tac) >>
     last_x_assum (qspecl_then [‘tof(f0)’] assume_tac) >> 
     fs[Tpm_tof_inv]) >>
 assume_tac
 (P2fun' |> qspecl [‘(A + 1) * Exp(A,B+1)’,‘B + 1’] 
 |> fVar_sInst_th “P(a1f:mem((A + 1) * Exp(A,B+1)),b1:mem(B + 1))”
    “(Fst(a1f:mem((A + 1) * Exp(A,B+1))) = NONE(A) & b1 = NONE(B)) |
     (?a. Fst(a1f) = SOME(a) & b1 = App(tof(Snd(a1f)),a))”) >>
 qsuff_tac
 ‘?f:(A + 1) * Exp(A,B+1) -> B + 1.
   !a1f : mem((A + 1) * Exp(A, (B + 1))).
           (Fst(a1f) = NONE(A) & App(f, a1f) = NONE(B)) |
   ?a:mem(A).
         Fst(a1f) = SOME(a) & App(f, a1f) = App(tof(Snd(a1f)), a)’
 >-- (strip_tac >> qexists_tac ‘f’ >> rpt strip_tac (* 2 *)
     >-- (first_x_assum (qspecl_then [‘Pair(NONE(A),Tpm(f'))’] assume_tac) >>
         fs[Pair_def',GSYM SOME_NOTNONE]) >>
     first_x_assum (qspecl_then [‘Pair(SOME(a),Tpm(f'))’] assume_tac) >>
     fs[Pair_def',SOME_NOTNONE] >>
     fs[tof_Tpm_inv,SOME_eq_eq]) >>  
 first_x_assum irule >>
 strip_tac >>
 qsspecl_then [‘x’] (x_choosel_then ["a1","f"] assume_tac) Pair_has_comp >>
 arw[Pair_def'] >> 
 qcases ‘a1 = NONE(A)’ 
 >-- (arw[GSYM SOME_NOTNONE] >> uex_tac >> qexists_tac ‘NONE(B)’ >> rw[] >>
     rpt strip_tac) >>
 fs[option_xor] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 arw[SOME_NOTNONE,SOME_eq_eq] >> uex_tac >>
 qexists_tac ‘App(tof(f),a0)’ >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘a0’ >> rw[]) >> arw[])
(form_goal
 “!A B.?!ob. !f:A->B + 1.
 App(ob,Pair(NONE(A),Tpm(f))) = NONE(B) &
 !a.App(ob,Pair(SOME(a),Tpm(f))) = App(f,a)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "OB" [‘A’,‘B’]
(* [‘f’]*)

(*FUNPOW Body in LUNFOLD_def*)
val FPB_def = proved_th $
e0
(strip_tac >> 
 qsuff_tac
 ‘?fpb:(B * A) + 1 -> (B * A) + 1.
 App(fpb,NONE(B * A)) = NONE(B * A) &
 !b a. App(fpb,SOME(Pair(b,a))) = App(f,b)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘fpb’ >> arw[] >>
     rpt strip_tac >> rw[GSYM FUN_EXT] >>
     strip_tac >>
     qcases ‘a = NONE(B * A)’ >> arw[] >>
     fs[option_xor] >> pop_assum (assume_tac o uex2ex_rule) >>
     pop_assum (x_choosel_then ["ab"] assume_tac) >>
     qsspecl_then [‘ab’] (x_choosel_then ["a1","b1"] assume_tac) 
     Pair_has_comp >> arw[]) >> 
 assume_tac (P2fun' |> qspecl [‘(B * A) +1’,‘(B * A) + 1’] 
                    |> fVar_sInst_th “P(ba1:mem((B * A) + 1),
                                        ba2:mem((B * A) + 1))”
                    “(ba1 = NONE(B * A) & ba2 = NONE(B * A)) |
                     (?b:mem(B) a:mem(A). ba1 = SOME(Pair(b,a)) &
                                      ba2 = App(f:B->(B * A + 1),b))”) >>
 qsuff_tac
 ‘!x. ?!y. x = NONE(B * A) & y = NONE(B * A) |
 (?b a. x = SOME(Pair(b,a)) & y = App(f,b))’ 
 >-- (strip_tac >> first_x_assum drule >>
     pop_assum strip_assume_tac >>
     qexists_tac ‘f'’ >> 
     first_assum (qspecl_then [‘NONE(B * A)’] assume_tac) >> 
     fs[GSYM SOME_NOTNONE] >>
     rpt strip_tac >>
     first_x_assum (qspecl_then [‘SOME(Pair(b,a))’] assume_tac) >>
     fs[SOME_NOTNONE,SOME_eq_eq,Pair_eq_eq]) >>
 strip_tac >>
 uex_tac >> qcases ‘x = NONE(B * A)’ (* 2 *)
 >-- (arw[] >> qexists_tac ‘NONE(B * A)’ >> rw[GSYM SOME_NOTNONE] >>
     rpt strip_tac >> arw[]) >>
 fs[option_xor] >> pop_assum (strip_assume_tac o uex2ex_rule) >>
 qsspecl_then [‘a0’] (x_choosel_then ["b1","a1"] assume_tac) Pair_has_comp >>
 arw[] >>
 rw[SOME_NOTNONE,SOME_eq_eq,Pair_eq_eq] >> 
 qexists_tac ‘App(f,b1)’ >> rw[] >> rpt strip_tac (* 2 *)
 >-- (qexistsl_tac [‘b1’,‘a1’] >> arw[]) >> rfs[]
  )
(form_goal
“!f: B -> (B * A)+1. ?!fpb:(B * A) + 1 -> (B * A) + 1.
 App(fpb,NONE(B * A)) = NONE(B * A) &
 !b a. App(fpb,SOME(Pair(b,a))) = App(f,b)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "FPB" [‘f’] 


val toabs_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac ‘?toabs.
 !n.App(toabs,n) = App(OM(p2(B,A)),App(FP(FPB(f)),Pair(n,App(f,z))))’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘toabs’ >> arw[] >>
     rpt strip_tac >> rw[GSYM FUN_EXT] >> arw[]) >>
 irule
 (P2fun' |> qspecl [‘N’,‘A + 1’]
 |> fVar_sInst_th “P(n:mem(N),a1:mem(A+1))”
 “a1 =  App(OM(p2(B,A)),App(FP(FPB(f)),Pair(n,App(f:B -> (B * A)+1,z))))”) >>
 strip_tac >> uex_tac >>
 qexists_tac ‘App(OM(p2(B, A)), App(FP(FPB(f)), Pair(x, App(f, z))))’ >>
 rw[])
(form_goal “!f:B-> (B * A)+1 z. ?!toabs.
 !n.App(toabs,n) = App(OM(p2(B,A)),App(FP(FPB(f)),Pair(n,App(f,z))))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "toabs" [‘f’,‘z’]


val toabs_char0 = proved_th $
e0
(rpt strip_tac (* 2 *)
 >-- (rw[GSYM FUN_EXT] >> 
     qsuff_tac ‘!n. App(toabs(f, z), n) = App(Null(A), n)’
     >-- rw[] >> 
     ind_with N_induct >> strip_tac (* 2 *)
     >-- (arw[toabs_def,Null_def,FP_def,OM_def] >> 
         rw[NONE_def]) >>
     rpt strip_tac >> arw[Null_def,toabs_def,FP_def] >>
     fs[toabs_def] >> rw[FPB_def] >> rfs[] >> rw[Null_def]) >>
 rw[GSYM FUN_EXT] >> 
 qsuff_tac ‘!n. App(toabs(f, z), n) = App(lcons0(a, toabs(f, b)), n)’
 >-- rw[] >> strip_tac >>
 rw[toabs_def] >> arw[] >>
 qcases ‘n = O’
 >-- arw[FP_def,OM_def,Pair_def,lcons0_def] >>
 fs[O_xor_Suc] >> rw[FP_def,FPB_def] >>
 rw[lcons0_def] >> rw[toabs_def]
)
(form_goal
 “!f:B -> (B * A) + 1 z.
  (App(f,z) = NONE(B * A) ==> toabs(f,z) = Null(A)) &
  (!b a. App(f,z) = SOME(Pair(b,a)) ==>
   toabs(f,z) = lcons0(a,toabs(f,b)))”)


val toabs_isll = prove_store("toabs_isll",
e0
(strip_tac >>
qby_tac
 ‘?sa. !g.IN(g,sa)<=>
   ?z.g = Tpm(toabs(f,z))’ >-- 
accept_tac (IN_def_P_ex |> qspecl [‘Exp(N,A+1)’] 
|> fVar_sInst_th “P(g:mem(Exp(N, A + 1)))”
   “?z.g = Tpm(toabs(f:B ->(B * A) + 1,z))”
|> GSYM) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac ‘!g. IN(g,sa) ==> isll(g)’ 
 >-- (strip_tac >> rfs[] >>
     strip_tac >> first_assum irule >> qexists_tac ‘z’ >> rw[]) >>
 match_mp_tac (ll_coind |> rewr_rule[GSYM isll_def]) >>
 arw[] >>
 rpt strip_tac >>
 qcases ‘App(f,z) = NONE(B * A)’ 
 >-- (disj1_tac >> arw[] >> rw[Tpm_eq_eq] >>
     drule (toabs_char0 |> spec_all |> conjE1) >> arw[]) >>
 fs[option_xor] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 disj2_tac >>
 qsspecl_then [‘a0’] (x_choosel_then ["b1","a1"] assume_tac) Pair_has_comp >>
 fs[] >> drule (toabs_char0 |> spec_all |> conjE2) >>
 arw[] >>
 qexistsl_tac [‘a1’,‘toabs(f,b1)’] >> rw[] >>
 qexists_tac ‘b1’ >> rw[])
(form_goal
 “!f:B->(B * A) + 1 z. isll(Tpm(toabs(f,z)))”));

val tof_eq_eq = prove_store("tof_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘Tpm(tof(f)) = Tpm(tof(g))’ >-- arw[]>> fs[Tpm_tof_inv] )
(form_goal
 “!A B f:mem(Exp(A,B)) g. tof(f)  = tof(g) <=> f = g”));




(*"LNTH_THM",
  ``(!n. LNTH n LNIL = NONE) /\
    (!h t. LNTH 0 (LCONS h t) = SOME h) /\
    (!n h t. LNTH (SUC n) (LCONS h t) = LNTH n t)``*)

(*
∀f g.
          (∀x. g x = case f x of NONE => [||] | SOME (v1,v2) => v2:::g v1) ⇒
          ∀y. g y = LUNFOLD f y

REWRITE_TAC [LNTH_EQ] >>

 ∀f g.
     (∀x n.
        LNTH n (g x) =
        LNTH n (case f x of NONE => [||] | SOME (v1,v2) => v2:::g v1)) ⇒
     ∀y n. LNTH n (g y) = LNTH n (LUNFOLD f y)

REPEAT GEN_TAC >>

(∀x n.
      LNTH n (g x) =
      LNTH n (case f x of NONE => [||] | SOME (v1,v2) => v2:::g v1)) ⇒
   ∀y n. LNTH n (g y) = LNTH n (LUNFOLD f y)

DISCH_TAC

 0.  ∀x n.
          LNTH n (g x) =
          LNTH n (case f x of NONE => [||] | SOME (v1,v2) => v2:::g v1)
   ------------------------------------
        ∀y n. LNTH n (g y) = LNTH n (LUNFOLD f y)

Induct_on `n`

0.  ∀x n.
          LNTH n (g x) =
          LNTH n (case f x of NONE => [||] | SOME (v1,v2) => v2:::g v1)
    1.  ∀y. LNTH n (g y) = LNTH n (LUNFOLD f y)
   ------------------------------------
        ∀y. LNTH (SUC n) (g y) = LNTH (SUC n) (LUNFOLD f y)
   
    0.  ∀x n.
          LNTH n (g x) =
          LNTH n (case f x of NONE => [||] | SOME (v1,v2) => v2:::g v1)
   ------------------------------------
        ∀y. LNTH 0 (g y) = LNTH 0 (LUNFOLD f y)

(1)
GEN_TAC

 0.  ∀x n.
          LNTH n (g x) =
          LNTH n (case f x of NONE => [||] | SOME (v1,v2) => v2:::g v1)
   ------------------------------------
        LNTH 0 (g y) = LNTH 0 (LUNFOLD f y)
  ONCE_ASM_REWRITE_TAC [LUNFOLD]

0.  ∀x n.
          LNTH n (g x) =
          LNTH n (case f x of NONE => [||] | SOME (v1,v2) => v2:::g v1)
   ------------------------------------
        LNTH 0 (case f y of NONE => [||] | SOME (v1,v2) => v2:::g v1) =
        LNTH 0 (case f y of NONE => [||] | SOME (v1,v2) => v2:::LUNFOLD f v1)

Cases_on `f y`



*)
val toabs_unique = prove_store("toabs_unique",
e0
(rw[GSYM tof_eq_eq] >> rw[tof_Tpm_inv] >> 
 rpt gen_tac >> strip_tac >>
 rw[GSYM FUN_EXT] >>
 qsuff_tac
 ‘!n z.App(tof(App(g, z)), n) = App(toabs(f, z), n)’
 >-- (strip_tac >> arw[]) >> 
 ind_with N_induct >> strip_tac (* 2 *)
 >-- (strip_tac >>
     qcases ‘App(f,z) = NONE(B * A)’ (* 2 *)
     >-- (drule (toabs_char0 |> spec_all |> conjE1) >> 
         first_x_assum (qspecl_then [‘z’] strip_assume_tac) >>
         first_x_assum drule >> arw[] >>
         rw[tof_Tpm_inv]) >>
      fs[option_xor] >>
     pop_assum (strip_assume_tac o uex2ex_rule) >>
     qsspecl_then [‘a0’] (x_choosel_then ["b1","a1"] assume_tac) 
     Pair_has_comp >> fs[] >> 
     first_x_assum (qspecl_then [‘z’] strip_assume_tac) >>
     first_x_assum drule >> arw[tof_Tpm_inv] >>
     drule (toabs_char0 |> spec_all |> conjE2) >> arw[] >>
     rw[lcons0_def]) >> 
 rpt strip_tac >>
 qcases ‘App(f,z) = NONE(B * A)’ 
 >-- (drule (toabs_char0 |> spec_all |> conjE1) >> 
 last_x_assum (qspecl_then [‘z’] strip_assume_tac) >>
 first_x_assum drule >> arw[] >> rw[tof_Tpm_inv]) >>
 fs[option_xor] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qsspecl_then [‘a0’] (x_choosel_then ["b1","a1"] assume_tac) 
 Pair_has_comp >> fs[] >> 
 last_assum (qspecl_then [‘z’] strip_assume_tac) >>
 first_x_assum drule >> arw[lcons0_def] >> 
 drule (toabs_char0 |> spec_all |> conjE2) >> arw[lcons0_def])
(form_goal 
 “!f:B -> (B * A) + 1.
  !g.
  (!z.(App(f,z) = NONE(B * A) ==> App(g,z) = Tpm(Null(A))) &
      (! b a. App(f,z) = SOME(Pair(b,a)) ==>
         App(g,z) = Tpm(lcons0(a,(tof(App(g,b)))))))==>
  !z. App(g,z) = Tpm(toabs(f,z))”));


val llcr0_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?g:B->Exp(N,A +1).
  !z.App(g,z) = Tpm(toabs(f,z))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> arw[] >>
     rpt strip_tac >> rw[GSYM FUN_EXT] >> arw[]) >>
 irule
 (P2fun' |> qspecl [‘B’,‘Exp(N,A + 1)’] 
         |> fVar_sInst_th “P(b:mem(B),f0:mem(Exp(N,A+1)))”
         “f0 = Tpm(toabs(f:B -> (B * A) + 1,b))”) >>
 strip_tac >> uex_tac >>
 qexists_tac ‘Tpm(toabs(f, x))’ >> rw[])
(form_goal
 “!A B f:B -> (B * A)+1.
  ?!g:B->Exp(N,A +1).
  !z.App(g,z) = Tpm(toabs(f,z))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "llcr0" [‘f’]

val llrec0_uex = prove_store("llrec0_uex",
e0
(rpt strip_tac >> uex_tac >> qexists_tac ‘llcr0(f)’ >> 
 qby_tac
 ‘!z.
  (App(f,z) = NONE(B * A) ==> App(llcr0(f),z) = Tpm(Null(A))) &
  (!b a. App(f,z) = SOME(Pair(b,a)) ==>
   App(llcr0(f),z) = Tpm(lcons0(a,tof(App(llcr0(f),b))))) &
  isll(App(llcr0(f),z))’
 >-- (strip_tac >> rw[llcr0_def,toabs_isll,Tpm_eq_eq,toabs_char0,tof_Tpm_inv])>>
 arw[] >>
 rpt strip_tac >> irule $ iffLR FUN_EXT >>
 strip_tac >>
 rw[GSYM tof_eq_eq] >>
 rw[llcr0_def,tof_Tpm_inv] >>
 rw[GSYM Tpm_eq_eq] >>
 (*!(z : mem(B)). App(g#, z#) = Tpm(toabs(f#, z#))*)
 rw[Tpm_tof_inv] >>
 irule toabs_unique >> arw[]
 )
(form_goal
 “!A B f:B ->(B * A) + 1.
  ?!cr:B -> Exp(N,A+1). 
  !z.
  (App(f,z) = NONE(B * A) ==> App(cr,z) = Tpm(Null(A))) &
  (!b a. App(f,z) = SOME(Pair(b,a)) ==>
   App(cr,z) = Tpm(lcons0(a,tof(App(cr,b))))) &
  isll(App(cr,z))”));

val llcr_uex = prove_store("llcr_uex",
e0
(rpt strip_tac >>
 qspecl_then [‘A’] assume_tac repll_Inj >>
 drule Inj_lift_fun >>
 qsspecl_then [‘f’] assume_tac llrec0_uex >>
 pop_assum (strip_assume_tac o uex_expand) >>
 last_x_assum (qsspecl_then [‘cr’] assume_tac) >>
 qby_tac
 ‘!x. ?a.App(cr,x) = App(repll(A),a)’ 
 >-- (strip_tac >> rw[GSYM Repll_def] >> rw[GSYM isll_Repll] >>
     first_x_assum (qspecl_then [‘x’] strip_assume_tac)) >>
     (*qcases ‘App(f,x) = NONE(B * A)’ (* 2 *)
     >-- last_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
     (*fs[option_xor] ERR
     ("disjE.first disjunct not in the formula list: ", [], [],
      [Pred ("=", true, [App(f, x), NONE(B * A)])]) raised*)
     pop_assum mp_tac >> rw[option_xor] >> strip_tac >>
     pop_assum (strip_assume_tac o uex2ex_rule) >> 
     qsspecl_then [‘a0’] strip_assume_tac Pair_has_comp >> 
     (*last_x_assum (qspecl_then [‘x’] strip_assume_tac)*)*)
 first_x_assum drule >>
 pop_assum (x_choosel_then ["crf"] assume_tac) >>
 uex_tac >> qexists_tac ‘crf’ >>
 fs[App_App_o] >>
 qby_tac
 ‘!z.
  (App(f,z) = NONE(B * A) ==> App(crf,z) = LNil(A)) &
  (!b a. App(f,z) = SOME(Pair(b,a)) ==>
   App(crf,z) = LCons(a,App(crf,b)))’
 >-- (rpt strip_tac (* 2 *)
     >-- (irule $ iffLR Repll_eq_eq >> arw[Repll_def] >>
         last_x_assum (qspecl_then [‘z’] strip_assume_tac) >>
         first_x_assum drule >> arw[LNil_def,GSYM Repll_def]) >>
     irule $ iffLR Repll_eq_eq >> arw[Repll_def] >>
     last_x_assum (qspecl_then [‘z’] strip_assume_tac) >>
     first_x_assum drule >> arw[] >> rw[LCons_def,GSYM Repll_def] >>
     arw[Repll_def]) >>
 arw[] >> rpt strip_tac >>
 irule $ iffLR FUN_EXT >> strip_tac >>
 irule  $ iffLR Repll_eq_eq >> rw[Repll_def] >>
 rw[GSYM App_App_o] >>
 qby_tac ‘repll(A) o crf = cr’ 
 >-- arw[GSYM FUN_EXT,App_App_o] >>
  arw[] >>
 qsuff_tac ‘repll(A) o cr' = cr’ 
 >-- (strip_tac >> arw[]) >>
 first_x_assum irule >> rw[App_App_o,GSYM Repll_def,isll_Repll] >>
 rw[GSYM LNil_def] >> rw[Repll_eq_eq] >>
 arw[] >> rw[GSYM LCons_def] >> rw[Repll_eq_eq] >> arw[] >>
 strip_tac >> qexists_tac ‘App(cr', z)’ >> rw[])
(form_goal
 “!A B f:B ->(B * A) + 1.
  ?!cr:B -> llist(A). 
  !z.
  (App(f,z) = NONE(B * A) ==> App(cr,z) = LNil(A)) &
  (!b a. App(f,z) = SOME(Pair(b,a)) ==>
   App(cr,z) = LCons(a,App(cr,b)))”));






val CB_def = proved_th $
e0
(strip_tac >>
 qsuff_tac
 ‘?cB:Pow(llist(X) * llist(X)) ->
                    Pow(llist(X) * llist(X)).
 !R:mem(Pow(llist(X) * llist(X))).
  !ll1 ll2.IN(Pair(ll1,ll2),App(cB,R)) <=> 
  (ll1 = LNil(X) & ll2 = LNil(X)) | 
  (?l01 l02 x. IN(Pair(l01,l02),R) &
   ll1 = LCons(x,l01) & ll2 = LCons(x,l02))’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘cB’ >> arw[] >> rpt strip_tac >>
     rw[GSYM FUN_EXT] >> strip_tac >> irule IN_EXT >>
     strip_tac >>
     qsspecl_then [‘x’] (x_choosel_then ["ll1","ll2"] assume_tac)
     Pair_has_comp >> arw[]) >>
 assume_tac (P2fun' |> qspecl [‘Pow(llist(X) * llist(X))’,
                               ‘Pow(llist(X) * llist(X))’] 
                    |> fVar_sInst_th “P(R0:mem(Pow(llist(X) * llist(X))),
                                        R1:mem(Pow(llist(X) * llist(X))))”
                    “!ll1 ll2.IN(Pair(ll1,ll2),R1) <=> 
                    (ll1 = LNil(X) & ll2 = LNil(X)) | 
             (?l01 l02 x. IN(Pair(l01,l02),R0) &
               ll1 = LCons(x,l01) & ll2 = LCons(x,l02))”) >>
 qby_tac
 ‘!R0. ?!R1.
  !ll1 ll2. IN(Pair(ll1,ll2),R1) <=>
  (ll1 = LNil(X) & ll2 = LNil(X)) | 
             (?l01 l02 x. IN(Pair(l01,l02),R0) &
               ll1 = LCons(x,l01) & ll2 = LCons(x,l02))’
 >-- (strip_tac >>
     assume_tac 
     (IN_def_P |> qspecl [‘llist(X) * llist(X)’] 
               |> fVar_sInst_th “P(ll12:mem(llist(X) * llist(X)))”
                  “(Fst(ll12) = LNil(X) & Snd(ll12) = LNil(X)) | 
             (?l01 l02 x. IN(Pair(l01,l02),R0) &
               Fst(ll12) = LCons(x,l01) & Snd(ll12) = LCons(x,l02))”
               |>  conv_rule (depth_fconv no_conv forall_cross_fconv)
               |> rewr_rule[Pair_def']) >> arw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >> qexists_tac ‘f’ >> arw[])
(form_goal “!X. ?!cB:Pow(llist(X) * llist(X)) ->
                    Pow(llist(X) * llist(X)).
 !R:mem(Pow(llist(X) * llist(X))).
  !ll1 ll2.IN(Pair(ll1,ll2),App(cB,R)) <=> 
  (ll1 = LNil(X) & ll2 = LNil(X)) | 
  (?l01 l02 x. IN(Pair(l01,l02),R) &
   ll1 = LCons(x,l01) & ll2 = LCons(x,l02))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "CB" [‘X’]


val CB_monotone = prove_store("CB_monotone",
e0
(rw[monotone_def,SS_def] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[CB_def] >> rpt strip_tac >> arw[] >>
 disj2_tac >> 
 qexistsl_tac [‘l01’,‘l02’,‘x’] >> arw[] >>
 first_x_assum irule >> arw[])
(form_goal “monotone(CB(X))”));



val CB_cases = cases0 |> gen_all |> qsspecl [‘CB(X)’] 
                      |> C mp CB_monotone
                      |> rewr_rule[GSYM IN_EXT]
                      |> conv_rule (depth_fconv no_conv forall_cross_fconv)
                      |> rewr_rule[CB_def]
                      |> gen_all


val CB_rules00  = rules0 |> gen_all |> qsspecl [‘CB(X)’] 
                       |> C mp CB_monotone 
                       |> rewr_rule[SS_def] 
                       |> conv_rule (depth_fconv no_conv forall_cross_fconv)
                       |> rewr_rule[CB_def]
                       |> mk_rules2 |> mk_rules3
                       |> gen_all

val CB_rules0 = prove_store("CB_rules0",
e0
(strip_tac >>
 qspecl_then [‘X’] strip_assume_tac CB_rules00 >>
 rpt strip_tac (* 2 *)
 >-- (first_x_assum irule >> rw[]) >>
 first_x_assum irule >> qexists_tac ‘l02’ >> arw[])
(form_goal
 “!X. IN(Pair(LNil(X),LNil(X)),gfp(CB(X))) &
  !l01 l02. 
  IN(Pair(l01,l02),gfp(CB(X))) ==>
  !x. IN(Pair(LCons(x,l01),LCons(x,l02)),gfp(CB(X)))”));




val CB_coind0 = coind0 |> gen_all |> qspecl [‘llist(X) * llist(X)’,‘CB(X)’]
                      |> rewr_rule[SS_def]
                      |> conv_rule (depth_fconv no_conv forall_cross_fconv)
                      |> rewr_rule[CB_def]
                      |> gen_all



val Repll_n_EQ = prove_store("Repll_n_EQ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 arw[GSYM Repll_eq_eq,GSYM tof_eq_eq,GSYM FUN_EXT])
(form_goal
 “!A ll1:mem(llist(A)) ll2.
  (!n. App(tof(Repll(ll1)),n) = App(tof(Repll(ll2)),n)) <=> ll1 = ll2”))


val LNTH_def = qdefine_fsym("LNTH",[‘n:mem(N)’,‘ll:mem(llist(A))’])
‘App(tof(Repll(ll)),n) ’ |> gen_all

val LNTH_EQ = Repll_n_EQ |> rewr_rule[GSYM LNTH_def]

val LHD_def = qdefine_fsym("LHD",[‘ll:mem(llist(X))’])
‘App(tof(Repll(ll)),O)’ |> gen_all

val isll_cases0 = ll_cases |> rewr_rule[GSYM IN_EXT_iff] 
                          |> rewr_rule[GSYM isll_def,llf_def,GSYM LNil_def,
                                       GSYM LCons_def]


val LHD_THM = prove_store("LHD_THM",
e0
(rw[LHD_def,LNil_def,tof_Tpm_inv,Null_def,NONE_def,
    LCons_def,lcons0_def])
(form_goal “LHD(LNil(X)) = NONE(X) &(!h:mem(X) t. LHD (LCons(h,t)) = SOME(h))”));


val LTL_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?ltl.
  (LHD(ll) = NONE(X) ==> ltl = NONE(llist(X))) &
  (!hd. LHD(ll) = SOME(hd) ==> ?ltl0.
    ltl = SOME(ltl0) &
    !n.App(tof(Repll(ltl0)),n) = App(tof(Repll(ll)),Suc(n)))’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘ltl’ >> arw[] >> rpt strip_tac >>
     qcases ‘LHD(ll) = NONE(X)’ (* 2 *)
     >-- (first_x_assum drule >> arw[] >>
         last_x_assum drule >> arw[]) >>
     fs[option_xor] >>
     pop_assum (strip_assume_tac o uex2ex_rule) >>
     first_x_assum drule >> 
     last_x_assum drule >> fs[] >>
     rw[SOME_eq_eq,GSYM Repll_eq_eq,GSYM tof_eq_eq] >> 
     irule $ iffLR FUN_EXT >> arw[]) >>
 qcases ‘LHD(ll) = NONE(X)’ (* 2 *)
 >-- (qexists_tac ‘NONE(llist(X))’ >> arw[GSYM SOME_NOTNONE]) >>
 qby_tac ‘isll(Repll(ll))’ 
 >-- (rw[isll_Repll] >> qexists_tac ‘ll’ >> rw[]) >>
 drule $ iffLR isll_cases0 >>
 qby_tac ‘~(Repll(ll) = Repll(LNil(X)))’ 
 >-- (rw[Repll_eq_eq] >> ccontra_tac >> fs[LHD_THM]) >>
 fs[] >> drule $ iffLR isll_Repll >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘SOME(b)’ >> rpt strip_tac >> qexists_tac ‘b’ >> rw[] >>
 qpick_assum ‘Tpm(t) = Repll(b)’ (assume_tac o GSYM) >> once_arw[] >>
 rw[tof_Tpm_inv] >> 
 rw[lcons0_def])
(form_goal
 “!X ll:mem(llist(X)).?!ltl.
  (LHD(ll) = NONE(X) ==> ltl = NONE(llist(X))) &
  (!hd. LHD(ll) = SOME(hd) ==> ?ltl0.
    ltl = SOME(ltl0) &
    !n.App(tof(Repll(ltl0)),n) = App(tof(Repll(ll)),Suc(n)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "LTL" [‘ll’] |> gen_all



val LCons_NONLNIL = prove_store("LCons_NONLNIL",
e0
(rpt strip_tac >> rw[GSYM Repll_eq_eq] >>
 rw[LNil_def,LCons_def,Tpm_eq_eq,GSYM FUN_EXT] >> ccontra_tac >>
 first_x_assum (qspecl_then [‘O’] assume_tac) >>
 fs[lcons0_def,Null_def] >> fs[SOME_NOTNONE,GSYM NONE_def])
(form_goal
 “!X x l. ~(LCons(x,l) = LNil(X))”));

val LCons_xor_LNil = prove_store("LCons_xor_LNil",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[LCons_NONLNIL] >>
 rw[GSYM Repll_eq_eq] >> rw[LCons_def] >>
 qsspecl_then [‘Repll(ll)’] assume_tac isll_cases0 >>
 fs[isll_Repll] >>
 rfs[Repll_eq_eq] >>
 qby_tac ‘?b.ll = b’ >-- (qexists_tac ‘ll’ >> rw[]) >> 
 pop_assum mp_tac >> arw[] >>
 strip_tac >> 
 qexistsl_tac [‘h’,‘b’] >> arw[] >> 
 pop_assum (assume_tac o GSYM) >> arw[tof_Tpm_inv])
(form_goal
 “!X ll:mem(llist(X)). ~(ll = LNil(X)) <=> ?h t. ll = LCons(h,t)”));




val LTL_THM = prove_store("LTL_THM",
e0
(qspecl_then [‘X’] strip_assume_tac LTL_def >>
 first_assum (qspecl_then [‘LNil(X)’] assume_tac) >>
 fs[LHD_THM] >> pop_assum (K all_tac) >> rpt strip_tac >> 
 first_x_assum (qspecl_then [‘LCons(h,t)’] strip_assume_tac) >> 
 fs[LHD_THM,SOME_eq_eq] >>
 first_x_assum (qspecl_then [‘h’] assume_tac) >> fs[] >>
 rw[SOME_eq_eq] >> 
 fs[LCons_def,tof_Tpm_inv,lcons0_def] >> 
 rw[GSYM Repll_eq_eq] >> arw[GSYM tof_eq_eq,GSYM FUN_EXT])
(form_goal “LTL(LNil(X)) = NONE(llist(X)) & (!h:mem(X) t. LTL (LCons(h,t)) = SOME(t))”));

(*
val accept_tac = 
 fn th => fn (ct,asl,w) =>
    if eq_form(concl th,w)  then ([], empty th) 
    else raise ERR ("accept_tac.concl of th not equal to the goal",[],[],[concl th,w])
*)

(*bug MWE

strip_tac 
qcases ‘B’ >-- accept_tac (trueI [“B”])
>> accept_tac (trueI [“~B”])
“A==>T”

“ LNTH(Suc(O), LCons(h:mem(X), t)) = LNTH(O, t)”
cases_on ‘t = LNil(X)’ >> arw[] (* 2 *)
     >-- rw[LNTH_def,LCons_def,tof_Tpm_inv,lcons0_def,LNil_def,Null_def,
            NONE_def] >>

qsspecl_then [‘tof(Repll(t))’,‘h’,‘O’] accept_tac(lcons0_def |> spec_all |> conjE2 |> gen_all) 
*)


val LNTH_THM = prove_store("LNTH_THM",
e0
(strip_tac >>
 qby_tac ‘(!n. LNTH(n,LNil(X)) = NONE(X)) &
  (!h:mem(X) t. LNTH(O,LCons(h,t)) = SOME(h))’
>-- (rpt strip_tac >> rw[LNTH_def] (* 2 *)
         >-- rw[LNil_def,tof_Tpm_inv,Null_def,NONE_def] 
         >-- rw[LCons_def,tof_Tpm_inv,lcons0_def]) >>
 arw[] >> ind_with N_induct >> rpt strip_tac (* 2 *)
 >-- (qcases ‘t = LNil(X)’ >> arw[] (* 2 *)
     >-- rw[LNTH_def,LCons_def,tof_Tpm_inv,lcons0_def,LNil_def,Null_def,
            NONE_def] >>
     rw[LNTH_def,LCons_def,tof_Tpm_inv,LNil_def,lcons0_def]) >> 
 qcases ‘t = LNil(X)’
 >-- (arw[] >> rw[LNTH_def,LCons_def,tof_Tpm_inv,lcons0_def,LNil_def,
                 Null_def,NONE_def]) >> 
 fs[LCons_xor_LNil] >>
 rw[LNTH_def,LCons_def,tof_Tpm_inv,lcons0_def] 
 (*may not need induction...*)
 )
(form_goal
 “!X.(!n. LNTH(n,LNil(X)) = NONE(X)) &
  (!h:mem(X) t. LNTH(O,LCons(h,t)) = SOME(h)) &
 (!n h:mem(X) t. LNTH(Suc(n),LCons(h,t)) = LNTH(n,t))”));

val gfp_CB = prove_store("gfp_CB",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >-- 
 (rw[GSYM LNTH_EQ] >> fs[IN_gfp,SS_def,CB_def] >>
 qsuff_tac
 ‘!n g1 g2.IN(Pair(g1, g2), sa) ==> LNTH(n, g1) = LNTH(n, g2)’
 >-- (rpt strip_tac >> first_x_assum drule >> arw[]) >>
 ind_with strong_ind >> 
 last_x_assum mp_tac >> fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[CB_def] >> strip_tac >>
 rpt strip_tac >>
 first_assum drule >>
 qcases ‘g1' = LNil(X) & g2' = LNil(X)’ >-- arw[] >>
 fs[] >> qcases ‘a = O’ (* 2 *)
 >-- (arw[] >> rw[LNTH_THM]) >>
 fs[O_xor_Suc] >> rw[LNTH_THM] >>first_assum irule >> arw[Lt_Suc]) >>
 qby_tac
 ‘?ss. !a b. IN(Pair(a:mem(llist(X)),b:mem(llist(X))),ss) <=> a = b’
 >-- assume_tac (IN_def_P |> qspecl [‘llist(X) * llist(X)’] 
 |> fVar_sInst_th “P(a:mem(llist(X) * llist(X)))”
    “Fst(a) = Snd(a:mem(llist(X) * llist(X)))” |> uex2ex_rule
                 |> conv_rule(depth_fconv no_conv forall_cross_fconv)
                 |> rewr_rule[Pair_def']) >>
 pop_assum (x_choose_then "ss" assume_tac) >>
 rw[IN_gfp] >>
 qexists_tac ‘ss’ >> arw[] >> rw[SS_def] >>
 strip_tac >>
 qsspecl_then [‘a’] (x_choosel_then ["ll1","ll2"] assume_tac) Pair_has_comp >>
 arw[CB_def] >> strip_tac >>
 qcases ‘ll1 = LNil(X) & ll2 = LNil(X)’ >> arw[] >>
 qby_tac ‘?ll0. SOME(ll0) = LTL(ll2)’
 >-- (qby_tac ‘~(ll1 = LNil(X))’ 
     >-- (ccontra_tac >> fs[] >> rfs[]) >>
     fs[LCons_xor_LNil] >> rfs[LTL_THM] >> qexists_tac ‘t’ >> rw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘?x0. SOME(x0) = LHD(ll2)’
 >-- (qby_tac ‘~(ll1 = LNil(X))’ 
     >-- (ccontra_tac >> fs[] >> rfs[]) >> 
     fs[LCons_xor_LNil] >> rfs[] >> rw[LHD_THM] >> qexists_tac ‘h’ >> rw[]) >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘ll0’,‘ll0’,‘x0’] >> rw[] >>
 qby_tac ‘~(ll2 = LNil(X))’ >-- 
 (ccontra_tac >> fs[LHD_THM]) >>
 fs[LCons_xor_LNil] >> fs[LTL_THM,LHD_THM,SOME_eq_eq])
(form_goal
“!X g1 g2. IN(Pair(g1,g2),gfp(CB(X))) <=> g1 = g2”));



(*TODO: rw LHS*)

val LLIST_BISIMULATION0 = prove_store("LLIST_BISIMULATION0",
e0
(rpt strip_tac >> 
 qsspecl_then [‘ll1’,‘ll2’] assume_tac (GSYM gfp_CB) >> arw[] >>
 rw[IN_gfp] >>
 rw[SS_def] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[CB_def] >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘sa’ >> arw[] >> rpt strip_tac >> first_x_assum drule >>
     qcases ‘ll3 = LNil(X) & ll4 = LNil(X)’ >-- fs[] >> 
     (fs[] >> qexistsl_tac [‘x’,‘l01’,‘l02’] >> arw[])) >>
 qexistsl_tac [‘R’] >>
 arw[] >> rpt strip_tac >>
 first_x_assum drule >>
 qcases ‘a' = LNil(X) & b = LNil(X)’
 >-- fs[] >>
 fs[] >> qexistsl_tac [‘t1’,‘t2’,‘h’] >> arw[]
 )
(form_goal
 “!ll1 ll2.
       (ll1 = ll2) <=>
       ?R. IN(Pair(ll1,ll2),R) &
           !ll3 ll4.
           IN(Pair(ll3,ll4),R) ==>
              (ll3 = LNil(X)) & (ll4 = LNil(X)) |
?h t1 t2. IN(Pair(t1,t2),R) & 
 ll3 = LCons(h,t1) & ll4 = LCons(h,t2)”));

(*Map over llist, functorial law for Map. using list_bisimulation*)



(*

  (“P(A,B)”,“Iso(A,B)”) take 
  (“P(a,b)”,“a = b”)

  ?A. Q(A) & !B. Q(B) ==> A Divides B


A * B

A --> F(A)
f: A->F(A) g:A->F(A) define bisimulation on f and g



*)
