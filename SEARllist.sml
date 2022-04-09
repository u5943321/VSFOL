
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

val SOME_def = qdefine_fsym("SOME",[‘a:mem(A)’])
‘App(i1(A,1),a)’ |> gen_all

val lcons0_def = proved_th $
e0
(cheat)
(form_goal “!X f0:N->X + 1 x.?!f. 
 App(f,O) = SOME(x) & 
 (!n. App(f,Suc(n)) = App(f0,n))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "lcons0" [‘x’,‘f0’]
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
  ?h t. g  = Tpm(lcons0(h,t)) & IN(Tpm(t),gs)”));

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
  Repll(l2) = Tpm(lcons0(Fst(xl1),tof(Repll(Snd(xl1)))))”)
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


val CB_def = proved_th $
e0
cheat
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
cheat
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
cheat
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



val gfp_CB = prove_store("gfp_CB",
e0
cheat
(form_goal
“!X g1 g2. IN(Pair(g1,g2),gfp(CB(X))) <=> g1 = g2”));


val LLIST_BISIMULATION = prove_store("LLIST_BISIMULATION",
e0
cheat
(form_goal
 “!ll1 ll2.
       (ll1 = ll2) <=>
       ?R. IN(Pair(ll1,ll2),R) &
           !ll3 ll4.
           IN(Pair(ll3,ll4),R) ==>
              (ll3 = LNil(X)) /\ (ll4 = LNil(X)) |
?h t1 t2. IN(Pair(t1,t2),R) & 
 ll3 = LCons(h,t1) & ll4 = LCons(h,t2)”));



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
  (!a. App(om,SOME(a)) = SOME(App(f,a)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "OM" [‘f’]

(*OPTION_BIND
(∀f. OPTION_BIND NONE f:β->α opt = NONE) ∧ ∀x f. OPTION_BIND (SOME x) f = f x

*)

val OB_def = proved_th $
e0
cheat
(form_goal
 “!A B f:A->B + 1.?!ob.
 App(ob,Pair(NONE(A),Tpm(f))) = NONE(B) &
 !a.App(ob,Pair(SOME(a),Tpm(f))) = App(f,a)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "OB" [‘f’]

(*FUNPOW Body in LUNFOLD_def*)
val FPB_def = proved_th $
e0
cheat
(form_goal
“!f: B -> (B * A)+1. ?!fpb:(B * A) + 1 -> (B * A) + 1.
 App(fpb,NONE(B * A)) = NONE(B * A) &
 !b a. App(fpb,SOME(Pair(b,a))) = App(f,b)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "FPB" [‘f’] 


val toabs_def = proved_th $
e0
cheat
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


val Tpm_eq_eq = prove_store("Tpm_eq_eq",
e0
(cheat)
(form_goal “!A B f1:A->B f2. Tpm(f1) = Tpm(f2) <=> f1 = f2”));

val option_xor = prove_store("option_xor",
e0
(cheat)
(form_goal “!A a1:mem(A+1). ~(a1 = NONE(A)) <=> ?!a0. a1 = SOME(a0)”));

val toabs_isll = prove_store("toabs_isll",
e0
(strip_tac >>
qby_tac
 ‘?sa. !g.IN(g,sa)<=>
   ?z.g = Tpm(toabs(f,z))’ >-- cheat >>
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
cheat
(form_goal
 “!A B f:mem(Exp(A,B)) g. tof(f)  = tof(g) <=> f = g”));


val tof_Tpm_inv = prove_store("tof_Tpm_inv",
e0
cheat
(form_goal
 “!A B f:A->B. tof(Tpm(f))  = f”));


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


(*

  (“P(A,B)”,“Iso(A,B)”) take 
  (“P(a,b)”,“a = b”)

  ?A. Q(A) & !B. Q(B) ==> A Divides B


A * B

A --> F(A)
f: A->F(A) g:A->F(A) define bisimulation on f and g



*)
