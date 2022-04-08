
val BU_ex = prove_store("BU_ex",
e0
(cheat)
(form_goal
 “!A. ?!BU:Exp(Exp(A,1+1),1+1) -> Exp(A,1+1). 
  !sss a:1->A. IN(a,BU o sss) <=>
  ?ss.IN(ss,sss) & IN(a,ss)”));
 

val BU_def = BU_ex |> spec_all |> uex2ex_rule 
                         |> qSKOLEM "BU" [‘A’]
                         |> gen_all
                         |> store_as "BU_def"; 


val BIGUNION_def = qdefine_fsym("BIGUNION",[‘sss:1->Exp(Exp(A,1+1),1+1)’])
‘BU(A) o sss’ |> gen_all |> store_as "BIGUNION_def";


val IN_BIGUNION = BU_def |> rewr_rule[GSYM BIGUNION_def] 
                         |> store_as "IN_BIGUNION";


(*for every f:Exp(A,1+1) -> Exp(A,1+1), there is a unique predicate coresponds the predicate X ⊆ f X

qform2IL [‘P1:1->Exp(A,2)’] ‘SS(P1,P2)’*)


val SSf_IL_u   vex = prove_store("SSf_IL_uex",
e0
(cheat)
(form_goal “!A f:Exp(A,1+1) ->Exp(A,1+1). ?!p:Exp(A,1+1) -> 1+1.
 !s:1->Exp(A,1+1). SS(s,f o s) <=> p o s = TRUE”));

val SSf_IL_def = SSf_IL_uex |> spec_all |> uex2ex_rule |> qSKOLEM "SSfIL" [‘f’]
                            |> gen_all

val gfp_def = qdefine_fsym("gfp",[‘f:Exp(A,1+1) -> Exp(A,1+1)’])
‘BIGUNION(Tp1(SSfIL(f)))’ |> gen_all 


val IN_gfp = prove_store("IN_gfp",
e0
(cheat)
(form_goal “!f:Exp(A,1+1) ->Exp(A,1+1) a. 
 IN(a,gfp(f)) <=> ?X. SS(X,f o X) & IN(a,X)”));

val weak_coind = prove_store("weak_coind",
e0
(rpt strip_tac >> rw[IN_gfp] >>
 qexists_tac ‘X’ >> arw[])
(form_goal “!A X:1->Exp(A,1+1) a f.IN(a,X) & SS(X,f o X) ==> IN(a,gfp(f))  ”));

val monotone_def = qdefine_psym("monotone",[‘f:Exp(A,1+1)->Exp(B,1+1)’])
‘!s1 s2. SS(s1,s2) ==> SS(f o s1, f o s2)’ |> gen_all


val SS_gfp_fgfp = prove_store("SS_gfp_fgfp",
e0
(rw[SS_def,IN_gfp] >> 
 rpt strip_tac >>
 first_assum drule >> fs[monotone_def] >>
 qsuff_tac ‘SS(f o X,f o gfp(f))’ 
 >-- (rw[SS_def] >> rpt strip_tac >> first_x_assum irule >> arw[]) >>
 first_x_assum irule >> 
 rw[SS_def,IN_gfp] >> rpt strip_tac >>
 qexists_tac ‘X’ >> arw[])
(form_goal
 “monotone(f) ==> SS(gfp(f:Exp(A,1+1) ->Exp(A,1+1)), f o gfp(f))”));


val rules0 = prove_store("rule0",
e0
(rw[SS_def,IN_gfp] >> rpt strip_tac >>
 assume_tac SS_gfp_fgfp >> first_x_assum drule >> 
 qexists_tac ‘gfp(f)’ >> arw[GSYM SS_def] >>
 rw[IN_gfp] >> qexists_tac ‘f o gfp(f)’ >> arw[] >>
 fs[monotone_def] >> first_x_assum irule >> arw[])
(form_goal
 “monotone(f) ==> SS(f o gfp(f),gfp(f:Exp(A,1+1) ->Exp(A,1+1)))”));


val cases0 = prove_store("cases0",
e0
(rpt strip_tac >> irule SS_SS_eq >>
 drule rules0 >> drule SS_gfp_fgfp >> arw[])
(form_goal “monotone(f) ==> gfp(f:Exp(A,1+1) ->Exp(A,1+1)) =  f o gfp(f)”))

val coind0 = prove_store("coind0",
e0
(rpt strip_tac >> rw[SS_def] >> rpt strip_tac >> irule weak_coind >>
 qexists_tac ‘X’ >> arw[])
(form_goal “!f:Exp(A,1+1) ->Exp(A,1+1) X. SS(X,f o X) ==> SS(X,gfp(f))”));



(*
val lrep_ok_cases =
   ⊢ ∀a0.
       lrep_ok a0 ⇔
       a0 = (λn. NONE) ∨
       ∃h t. a0 = (λn. if n = 0 then SOME h else t (n − 1)) ∧ lrep_ok t: thm
val lrep_ok_coind =
   ⊢ ∀lrep_ok'.
       (∀a0.
          lrep_ok' a0 ⇒
          a0 = (λn. NONE) ∨
          ∃h t. a0 = (λn. if n = 0 then SOME h else t (n − 1)) ∧ lrep_ok' t) ⇒
       ∀a0. lrep_ok' a0 ⇒ lrep_ok a0: thm
val lrep_ok_rules =
   ⊢ lrep_ok (λn. NONE) ∧
     ∀h t. lrep_ok t ⇒ lrep_ok (λn. if n = 0 then SOME h else t (n − 1)): thm

*)

(*Exp app 
 input f:Exp(A,B) ->Exp(C,D), g:A->B
 output C->D.*)

val Exap_def = qdefine_fsym("Exap",[‘f:Exp(A,B) -> Exp(C,D)’,‘g:A->B’])
‘Tp0(f o Tp1(g))’ |> gen_all

(*shift1(x):Exp(N,X) ->Exp(N,X) *)
val shift1_uex = prove_store("shift1_uex",
e0
(cheat)
(form_goal “!x:1->X.?!f:Exp(N,X) ->Exp(N,X).
 !g:N ->X. Exap(f,g) o O = x & !n:1->N.Exap(f,g) o Suc(n) = g o n”));

val shift1_def = shift1_uex |> spec_all |> uex2ex_rule 
                            |> qSKOLEM "shift1" [‘x’] 

val llf_uex = prove_store("llf_uex",
e0
(cheat)
(form_goal
 “?!f: Exp(Exp(N,A+1),1+1) -> Exp(Exp(N,A+1),1+1).
  !gs:1-> Exp(Exp(N,A+1),1+1) g.
  IN(g,f o gs) <=>
  g = Tp1(i2(A,1) o To1(N)) |
  ?h t. g  = shift1(i1(A,1) o h) o t & IN(t,gs)”));

val llf_def = llf_uex |> uex2ex_rule |> qSKOLEM "llf" [‘A’]
                      |> gen_all

val llf_monotone = prove_store("llf_monotone",
e0
cheat
(form_goal “monotone(llf(A))”));

val islls_def = qdefine_fsym("islls",[‘A’]) ‘gfp(llf(A))’

val llist_def1 = Thm_2_4 |> qsspecl [‘Tp0(islls(X))’]
                              |> qSKOLEM "llist" [‘X’] 
                              |> qSKOLEM "repll" [‘X’]
                              |> gen_all 

val repll_Inj = llist_def1 |> spec_all 
                          |> conjE1 |> gen_all
                          |> store_as "repll_Inj"; 

val ll_rules = rules0 |> gen_all |> qsspecl [‘llf(A)’] 
                       |> C mp llf_monotone 
                       |> rewr_rule[SS_def,llf_def] 
                       |> mk_rules2 |> mk_rules3
                       |> rewr_rule[GSYM islls_def]
                       |> gen_all

val ll_coind = coind0 |> gen_all |> qspecl [‘Exp(N,A + 1)’,‘llf(A)’]
                      |> rewr_rule[SS_def,llf_def]
                      |> rewr_rule[GSYM islls_def]
                      |> gen_all

val ll_cases = cases0 |> gen_all |> qsspecl [‘llf(A)’] 
                      |> C mp llf_monotone
                      |> rewr_rule[GSYM IN_EXT,llf_def]
                      |> rewr_rule[GSYM islls_def]
                      |> gen_all

val isll_def = qdefine_psym("isll",[‘l:1->Exp(N,X + 1)’]) 
                          ‘IN(l,islls(X))’
                          |> gen_all |> store_as "isll_def"; 

val isll_coinduct = ll_coind |> rewr_rule[IN_Tp0] 
                             |> qsspecl [‘Tp1(P:Exp(N, X + 1)-> 2)’]
                             |> rewr_rule[Tp0_Tp1_inv]
                             |> rewr_rule[GSYM IN_Tp0,GSYM isll_def]
                             |> gen_all

val isll_lnil = prove_store("isll_lnil",
e0
(rw[isll_def,ll_rules])
(form_goal
 “!X. isll(Tp1(i2(X, 1) o To1(N)))”)); 


val isll_shift = ll_rules |> spec_all |> conjE2 
                        |> rewr_rule[GSYM isll_def]
                        |> spec_all |> undisch 
                        |> gen_all |> disch_all
                        |> gen_all |> store_as "isll_shift";


val Repll_def = qdefine_fsym ("Repll",[‘l:1-> llist(X)’])
                            ‘repll(X) o l’
                            |> gen_all |> store_as "Repll_def";
 
val llist_def = llist_def1 |> rewr_rule[GSYM IN_Tp1,Tp1_Tp0_inv]
                         |> gen_all
                         |> store_as "llist_def";


val LNil_def = proved_th $
e0
(strip_tac >> uex_tac >>
 qspecl_then [‘X’] strip_assume_tac llist_def >>
 first_assum (qspecl_then [‘Tp1(i2(X, 1) o To1(N))’] assume_tac) >>
 fs[isll_lnil,GSYM isll_def] >>
 qexists_tac ‘b’ >> arw[Repll_def] >>
 fs[Inj_def])
(form_goal “!X. ?!l.Repll(l) = Tp1(i2(X, 1) o To1(N))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "LNil" [‘X’] |> gen_all
|> store_as "LNil_def";


val lcons0_def = 
    qdefine_fsym ("lcons0",[‘x:1->X’,‘l:1->Exp(N,X + 1)’])
    ‘shift1((i1(X, 1) o x)) o l’ |> qgenl [‘X’,‘x’,‘l’]


val lcons1_def = proved_th $
e0
cheat
(form_goal “?!lcons1:X * Exp(N,X + 1) -> Exp(N,X+1).!x l.
 lcons1 o Pa(x,l) = lcons0(x,l)”)
|> uex2ex_rule |> qSKOLEM "lcons1" [‘X’] |> gen_all


val repll_isll = prove_store("repll_isll",
e0
(rpt strip_tac >> 
 rw[isll_def] >> 
 qspecl_then [‘X’] assume_tac llist_def >>
 fs[] >> qexists_tac ‘ll’ >> rw[])
(form_goal “!X ll. isll(repll(X) o ll)”)); 


val isll_Repll = llist_def |> spec_all |> conjE2
                        |> rewr_rule[GSYM isll_def,
                                     GSYM Repll_def] 
                        |> gen_all 
                        |> store_as "isll_Repll";


val llift_cond2 = proved_th $
e0
(fconv_tac forall_cross_fconv >>
 rw[Prla_def,Pa_distr,o_assoc,
    p12_of_Pa,idL,lcons1_def] >>
 rpt strip_tac >>
 qsspecl_then [‘b’] assume_tac repll_isll >>
 drule isll_shift >> rw[GSYM Repll_def,GSYM isll_Repll] >>
 fs[Repll_def,lcons0_def])
(form_goal
 “!xl1:1-> X * llist(X).?l2.
 (lcons1(X) o Prla(id(X),repll(X))) o xl1 = repll(X) o l2”)


val llift_cond2' = proved_th $
e0
(assume_tac llift_cond2 >> strip_tac >> uex_tac >>
 first_x_assum (qspecl_then [‘xl1’] strip_assume_tac) >>
 qexists_tac ‘l2’ >> arw[] >> assume_tac repll_Inj >>
 fs[Inj_def] >> rpt strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “!xl1:1-> X * llist(X).?!l2.
 (lcons1(X) o Prla(id(X),repll(X))) o xl1 = repll(X) o l2”)


val LCONS_def = P2fun' |> qspecl [‘X * llist(X)’,‘llist(X)’]
                     |> specl [qform2IL [‘xl1:1->X * llist(X)’,‘l2:1-> llist(X)’]
 ‘(lcons1(X) o Prla(id(X),repll(X))) o xl1 = repll(X) o l2’]
                     |> rewr_rule[Holds_def]
                     |> rewr_rule[Eq_property_TRUE,o_assoc,
                                 Pa_distr ,p12_of_Pa]
                     |> C mp (llift_cond2' |> rewr_rule[o_assoc])
                     |> uex2ex_rule
                     |> qSKOLEM "LCONS" [‘X’]
                     |> qspecl 
                     [‘Pa(x:1->X,l:1-> llist(X))’]
                     |> rewr_rule[Prla_def,
                                  p12_of_Pa,idL,Pa_distr,
                                  o_assoc,lcons1_def,lcons0_def,GSYM Repll_def]
                     |> gen_all
                     |> store_as "LCONS_def"; 

val LCons_def = 
    qdefine_fsym ("LCons",[‘x:1->X’,‘l:1->llist(X)’])
    ‘LCONS(X) o Pa(x,l)’ 
    |> gen_all |> store_as "LCons_def";

val Repll_LCons = LCONS_def |> rewr_rule[GSYM LCons_def]
                         |> GSYM
                         |> store_as "Repll_LCons";



val Repll_eq_eq = prove_store("Repll_eq_eq",
e0
(rpt strip_tac >> rw[Repll_def] >> irule Inj_eq_eq >>
 rw[repll_Inj])
(form_goal “!X l1:1->llist(X) l2.
 Repll(l1) = Repll(l2) <=> l1 = l2”));

val Ev_eq_eq' = prove_store("Ev_eq_eq'",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[]>> 
 drule Ev_eq_eq >> arw[])
(form_goal “!A B X f:X->Exp(A,B) g. 
 Ev(A,B) o Pa(p1(A,X),f o p2(A,X)) = 
 Ev(A,B) o Pa(p1(A,X),g o p2(A,X)) <=> f = g”));


val Ev_eq_eq' = prove_store("Ev_eq_eq'",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[]>> 
 drule Ev_eq_eq >> arw[])
(form_goal “!A B X f:X->Exp(A,B) g. 
 Ev(A,B) o Pa(p1(A,X),f o p2(A,X)) = 
 Ev(A,B) o Pa(p1(A,X),g o p2(A,X)) <=> f = g”));

val Tp0_eq_eq = prove_store("Tp0_eq_eq",
e0
(cheat)
(form_goal “!A B f:1->Exp(A,B) g. Tp0(f) = Tp0(g) <=> f = g”));


val Tp1_eq_eq = prove_store("Tp1_eq_eq",
e0
(cheat)
(form_goal “!A B f:A->B g. Tp1(f) = Tp1(g) <=> f = g”));

val i12_disjoint = prove_store("i12_disjoint",
e0
cheat
(form_goal “!A B a:1->A b:1->B. ~(i1(A,B) o a = i2(A,B) o b)”));

val LCons_NONLNIL = prove_store("LCons_NONLNIL",
e0
(rw[GSYM Repll_eq_eq,LNil_def,Repll_LCons] >>
 rpt strip_tac >> rw[GSYM Tp0_eq_eq] >>
 rw[Tp0_Tp1_inv] >> once_rw[GSYM FUN_EXT_iff] >>
 ccontra_tac >>
 first_x_assum (qspecl_then [‘O’] assume_tac) >>
 fs[o_assoc,one_to_one_id,idR] >>
 qby_tac ‘Tp0((shift1((i1(X, 1) o x)) o Repll(l))) o O = 
  Exap(shift1(i1(X, 1) o x),Tp0(Repll(l))) o O’
 >-- rw[Exap_def,Tp1_Tp0_inv] >>
 fs[shift1_def] >>
 qsspecl_then [‘x’,‘id(1)’] assume_tac i12_disjoint >>
 fs[idR])
(form_goal
 “!X x l. ~(LCons(x,l) = LNil(X))”));



val Repll_lnil_uex = prove_store("Repl_lnil_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[LNil_def] >>
 rw[GSYM Repll_eq_eq] >> arw[LNil_def])
(form_goal
 “!X l. Repll(l) = Tp1(i2(X, 1) o To1(N)) <=> l = LNil(X)”));



val _ = new_psym2IL("isll",(rastt "Tp0(islls(X))",List.map (dest_var o rastt) ["nxs:A->Exp(N,X+1)"]))

val _ = new_fsym2IL("Repll",(rastt "repll(X)",List.map (dest_var o rastt) ["l:A-> llist(X)"]))

val lnil_def = qdefine_fsym("lnil",[‘X’]) ‘Tp1(i2(X, 1) o To1(N))’

(*\cal B*)
val CB_def = proved_th $
e0
cheat
(form_goal “!X. ?!f:Exp(Exp(N,X+1) * Exp(N,X+1) ,1+1) ->
                    Exp(Exp(N,X+1) * Exp(N,X+1),1+1).
 !g1 g2 R. IN(Pa(g1,g2),f o R) <=>
 (g1 = lnil(X) & g2 = lnil(X)) | 
 ?f1 f2 x. IN(Pa(f1,f2),R) & g1 = lcons0(x,f1) & g2 = lcons0(x,f2) & 
 isll(f1) & isll(f2)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "CB" [‘X’]


(*
> > > > > # 1 subgoal:
val it =
   X(g2 : ar(1, Exp(N, X + 1)))(g1 : ar(1, Exp(N, X + 1)))(X' :
      ar(1, Exp(Exp(N, (X + 1)) * Exp(N, (X + 1)), 2)))
   1.!(a' : ar(1, Exp(N, X + 1)))  (b : ar(1, Exp(N, X + 1))).
               IN(Pa(a'#, b#), X') ==>
               a'# = lnil(X) & b# = lnil(X) |
               ?(f1 : ar(1, Exp(N, X + 1)))  (f2 : ar(1, Exp(N, X + 1)))
               (x1 : ar(1, X))  (x2 : ar(1, X)).
                 IN(Pa(f1#, f2#), X') &
                 a'# = lcons0(x1#, f1#) &
                 b# = lcons0(x2#, f2#) & isll(f1#) & isll(f2#)
   2.IN(Pa(g1, g2), X')
   3.isll(g1) & isll(g2)
   4.~g1 = g2
   ----------------------------------------------------------------------
   F

*)

val NTC0_def = proved_th $
e0
cheat
(form_goal “?NTC:N * Exp(N,X+1) -> Exp(N,X+1).!n0 g0.
  (!n. Le(n,n0) ==> Tp0(NTC o Pa(n0,g0)) o n = Tp0(g0) o n) & 
  (!n. ~(Le(n,n0)) ==> Tp0(NTC o Pa(n0,g0)) o n = i2(X,1))”)
|> qSKOLEM "NTC0" [‘X’]

val ntc0_def = qdefine_fsym("ntc0",[‘n:1->N’,‘g:1->Exp(N,X+1)’])
‘NTC0(X) o Pa(n,g)’

val ntc0_eq_eq = prove_store("ntc_eq_eq",
e0
cheat
(form_goal “!g1 g2:1->Exp(N,X+1). isll(g1) & isll(g2) & 
 (!n. ntc0(n,g1) = ntc0(n,g2)) ==> g1 = g2”));

val ntc0_lcons0 = prove_store("ntc0_lcons0",
e0
(cheat)
(form_goal “!n x f. ntc0(Suc(n), lcons0(x, f)) = 
shift1(i1(X,1) o x) o ntc0(n,f)”));

(*proved_th $
e0
cheat
(form_goal
 “!n0:1->N g0:1->Exp(N,X+1).?!g:1->Exp(N,X + 1).
  (!n. Le(n,n0) ==> Tp0(g) o n = Tp0(g0) o n) & 
  (!n. ~(Le(n,n0)) ==> Tp0(g) o n = i2(X,1))”)*)




val CB_monotone = prove_store("CB_monotone",
e0
cheat
(form_goal “monotone(CB(X))”));



(*P ⊆ A, ϕ: A -> X * A g: A -> LL(X)*)

val llindf_def = proved_th $
e0
cheat
(form_goal “!A P:1->Exp(A,1+1) phi:A -> X * A.
 ?!f:Exp(A * llist(X),1+1) -> Exp(A * llist(X),1+1).
 !s:1-> Exp(A * llist(X),1+1).
  !p:1->A * llist(X). 
  IN(p, f o s) <=>
  (IN(Fst(p),P) & Snd(p)= LNil(X)) |
  (?p0:1->A * llist(X). IN(p0,s) &
   ~IN(Fst(p),P) & Snd(phi o Fst(p)) = Fst(p0) &
   Snd(p) = LCons(Fst(phi o Fst(p)), Snd(p0)))”)
 |> spec_all |> uex2ex_rule |> qSKOLEM "llindf"[‘P’,‘phi’]


val llindf_monotone = prove_store("llindf_monotone",
e0
cheat
(form_goal “monotone(llindf(P:1->Exp(A,1+1),phi:A->X * A))”));


val llinds_def = qdefine_fsym("llinds",[‘P:1->Exp(A,1+1)’,‘phi:A->X * A’])
‘gfp(llindf(P, phi))’


val llind_rules  = rules0 |> gen_all |> qsspecl [‘llindf(P:1->Exp(A,1+1),phi:A->X * A)’] 
                       |> C mp llindf_monotone 
                       |> rewr_rule[SS_def,llindf_def] 
                       |> rewr_rule[GSYM llinds_def]
                       |> mk_rules2 |> mk_rules3
                       |> gen_all

val llind_coind = coind0 |> gen_all |> qspecl [‘A * llist(X)’,‘llindf(P:1->Exp(A,1+1),phi:A->X * A)’]
                      |> rewr_rule[SS_def,llindf_def]
                      |> rewr_rule[GSYM llinds_def]
                      |> gen_all


val CB_cases = cases0 |> gen_all |> qsspecl [‘CB(X)’] 
                      |> C mp CB_monotone
                      |> rewr_rule[GSYM IN_EXT]
                      |> conv_rule (depth_fconv no_conv forall_cross_fconv)
                      |> rewr_rule[CB_def]
                      |> gen_all


val CB_rules  = rules0 |> gen_all |> qsspecl [‘CB(X)’] 
                       |> C mp CB_monotone 
                       |> rewr_rule[SS_def] 
                       |> conv_rule (depth_fconv no_conv forall_cross_fconv)
                       |> rewr_rule[CB_def]
                       |> mk_rules2 |> mk_rules3
                       |> gen_all

val CB_coind = coind0 |> gen_all |> qspecl [‘Exp(N,X+1) * Exp(N,X+1)’,‘CB(X)’]
                      |> rewr_rule[SS_def]
                      |> conv_rule (depth_fconv no_conv forall_cross_fconv)
                      |> rewr_rule[CB_def]
                      |> gen_all



val llind_cases = cases0 |> gen_all |> qsspecl [‘llindf(P:1->Exp(A,1+1),phi:A->X * A)’] 
                      |> C mp llindf_monotone
                      |> rewr_rule[GSYM IN_EXT,llindf_def]
                      |> rewr_rule[GSYM llinds_def]
                      |> gen_all

val gfp_CB = prove_store("gfp_CB",
e0
cheat
(form_goal
“!X g1 g2. IN(Pa(g1,g2),gfp(CB(X))) <=> (g1 = g2 &  isll(g1) & isll(g2))”));

val CB_coind1 = CB_coind |> rewr_rule[gfp_CB]

“?f:Exp(A,1+1) * Exp(B,1+1) -> !sa:1->Exp(A,1+1) sb:1->Exp(B,1+1).
 ”

rpt strip_tac >>
irule $ iffLR Repll_eq_eq >>
qsuff_tac ‘Repll(ll1) = Repll(ll2) & isll(Repll(ll1)) & isll(Repll(ll2))’
>-- (strip_tac >> arw[]) >>
irule CB_coind1 >>
qby_tac
‘?s:1->Exp(Exp(N, (X + 1)) * Exp(N, (X + 1)), 1+1). 
 ’


qexists_tac ‘Pa(llinds(P, phi),llinds(P, phi))’
llind_cases 
“!a:1->A.!ll1:1->llist(X) ll2.IN(Pa(a,ll1),llinds(P,phi)) &
 IN(Pa(a,ll2),llinds(P,phi)) ==> ll1 = ll2”


(*if a in P then the unique ll is [], 
 else a is hit by some snd of phi:A->X * A.



If P ⊆ X and ϕ : X → N × X, then g : X → L *)



“!a:1->A.?!ll:1->llist(X).IN(Pa(a,ll),llinds(P,phi)) ”



(*

⊢ ∀f z.
       LUNFOLD f z =
       llist_abs
         (λn.
              OPTION_MAP SND
                (FUNPOW (λm:(β#α)opt. OPTION_BIND m (UNCURRY (K ∘ f))) n (f z))):


 "LUNFOLD",
  `!f x.
     LUNFOLD f:β->(β #a) opt x:β =
       case f x of NONE => [||] | SOME (v1,v2) => v2 ::: LUNFOLD f v1`

val it =
   ⊢ (∀f x. OPTION_MAP f:α->β (SOME x) = SOME (f x)) ∧
     ∀f. OPTION_MAP f NONE = NONE


(∀f. OPTION_BIND NONE f:β->α opt = NONE) ∧ ∀x f. OPTION_BIND (SOME x) f = f x


("arithmetic", "FUNPOW"),
     (⊢ (∀f x. FUNPOW f 0 x = x) ∧
        ∀f n x. FUNPOW f (SUC n) x = FUNPOW f n (f x), Def))

“!g1 g2 n. IN(Pa(g1,g2),gfp(CB(X))) ==> ntc0(n,g1) =  ntc0(n,g2)”
rw[IN_gfp] >> rpt strip_tac >> rw[SS_def] >>
fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
rw[CB_def] >> dimp_tac >> strip_tac (* 2 *) >-- 
qby_tac ‘!n f1 f2.IN(Pa(f1,f2),X') ==> ntc0(n,f1) = ntc0(n,f2)’
>-- qsuff_tac ‘!n. (!n0. Lt(n0,n) ==> !f1 f2.IN(Pa(f1,f2),X') ==> ntc0(n0,f1) = ntc0(n0,f2)) ==> !f1 f2.IN(Pa(f1,f2),X') ==> ntc0(n,f1) = ntc0(n,f2)’
    >-- cheat >> 
rpt strip_tac >>
first_assum drule >> pop_assum strip_assume_tac >-- cheat >>
arw[] >> 
cheat


rpt strip_tac >> dimp_tac >-- cheat >>
rpt strip_tac >> arw[] >> rw[IN_gfp] >> 

qsuff_tac ‘!n0. Le(n0,n) ==>  ntc0(n0, f1) = ntc0(n0, f2)’
>-- cheat >>

qsuff_tac ‘!n0. Le(n0,n) ==> Tp0(f1) o n0 = Tp0(f2) o n0’     
>-- cheat >>
rpt strip_tac >>
qcases ‘n0 = n’ >> arw[] >>
first_assum drule >> pop_assum strip_assume_tac >-- cheat (*Nil trivial*) >>




>-- rpt strip_tac >>
    qsuff_tac ‘!n.(!n0.Lt(n0,n) ==> ntc0(n0, f1) = ntc0(n0, f2)) ==>
                ntc0(n, f1) = ntc0(n, f2)’
    >-- cheat >>
    rpt strip_tac >> first_assum drule >>
    pop_assum strip_assume_tac >-- cheat >>
    


qsuff_tac ‘isll(g1) & isll(g2)’ >-- 
strip_tac >> arw[] >> irule ntc0_eq_eq >> arw[] >>
qsuff_tac ‘ntc0(O,g1) = ntc0(O,g2) & IN(Pa(ntc0(O,g1),ntc0(O,g2)),X') &
 (!n0. ntc0(n0,g1) = ntc0(n0,g2) & IN(Pa(ntc0(n0,g1),ntc0(n0,g2)),X') ==>
 ntc0(Suc(n0),g1) = ntc0(Suc(n0),g2) &
  IN(Pa(ntc0(Suc(n0),g1),ntc0(Suc(n0),g2)),X'))’
>-- cheat >>
strip_tac >-- cheat >> strip_tac >-- cheat >>
strip_tac >> disch_tac >>




cheat  >>
strip_tac >> irule ll_coind >> cheat



>-- disch_tac >> arw[] >> 
    qsuff_tac ‘!n. ntrunc g1 = ntrunc g2 & isll(ntrunc g1) & isll(ntrunc g2)’
    induct on n
   Nil = Nil
   assume ntrunc n g1 = ntrunc n g2 & isll(ntrunc n g1) & isll(ntrunc n g2)
want 

“!g1 g2. IN(Pa(g1,g2),gfp(CB(X))) <=> (g1 = g2 &  isll(g1) & isll(g2))”

coind0 |> gen_all |> qspecl [‘Exp(N,X + 1) * Exp(N,X + 1)’,‘CB(X)’]
|> rewr_rule[SS_def]
|> conv_rule  (depth_fconv no_conv forall_cross_fconv) 
|> rewr_rule[CB_def]

cases0 |> gen_all |> qsspecl [‘CB(X)’] 
|> C mp CB_monotone
|> rewr_rule[GSYM IN_EXT,CB_def]
|> conv_rule (depth_fconv no_conv forall_cross_fconv) 
|> rewr_rule[CB_def]

(*
(form_goal “!X. ?!f:Pow(llist(X) * llist(X)) -> Pow(llist(X) * llist(X)).
 !a1 a2 a3 a4. IN(Pa(a3,a4),f o Pa(a1,a2)) <=> 
 a3 = LNil(X) & a4 = LNil(X) & ...
 ”) cannot define like this since must be Exp 
*)




“?form conj: form * form -> form disj:form -> form > form neg:form ->form
 imp:form * form ->form diam:form -> form.
 
”
prove_store("isL_coinduct",
e0
(rw[isll_def] >> strip_tac >> strip_tac >>
 qsspecl_then [‘Tp1(P)’] assume_tac ll_coind >>
 fs[IN_Tp1])
(form_goal 
 “!X P.P o Tp1(i2(X, 1) o To1(N))  = TRUE & 
  (!lls0 x. P o lls0 = TRUE ==>
    P o Ins(Pa(Card(ls0),x),ls0) = TRUE) ==> 
  !l:1-> Exp(N * X,1+1). isL(l) ==> P o l = TRUE”));



 "LTAKE_SNOC_LNTH",
  ``!n ll. LTAKE (SUC n) ll =
             case LTAKE n ll of
               NONE => NONE
             | SOME l => (case LNTH n ll of
                             NONE => NONE
                           | SOME e => SOME (l ++ [e]))``

 "LTAKE_EQ_NONE_LNTH",
  ``!n ll. (LTAKE n ll = NONE) ==> (LNTH n ll = NONE)``

  "LNTH_EQ",
  ``!ll1 ll2. (ll1 = ll2) = (!n. LNTH n ll1 = LNTH n ll2)``

 "LTAKE_EQ",
  ``!ll1 ll2. (ll1 = ll2) = (!n. LTAKE n ll1 = LTAKE n ll2)``


*)
