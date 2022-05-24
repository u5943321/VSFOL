(*facts about ultrafilters*)


val INTER_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qspecl [‘Pow(A) * Pow(A)’,‘Pow(A)’] 
           |> fVar_sInst_th 
           “P(s12:mem(Pow(A) * Pow(A)),s:mem(Pow(A)))”
           “!a. IN(a,s) <=> IN(a:mem(A),Fst(s12)) & IN(a,Snd(s12))”
           |> conv_rule (depth_fconv no_conv forall_cross_fconv)
           |> rewr_rule[Pair_def']) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a':mem(A))”
    “IN(a':mem(A),a) & IN(a',b)”) >> arw[])
(form_goal “!A. ?!f:Pow(A) * Pow(A) -> Pow(A).
 !s1 s2 a. IN(a,App(f,Pair(s1,s2))) <=> IN(a,s1) & IN(a,s2)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "INTER" [‘A’]

val Inter_def = qdefine_fsym("Inter",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘App(INTER(A),Pair(s1,s2))’ 



val UNION_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qspecl [‘Pow(A) * Pow(A)’,‘Pow(A)’] 
           |> fVar_sInst_th 
           “P(s12:mem(Pow(A) * Pow(A)),s:mem(Pow(A)))”
           “!a. IN(a,s) <=> IN(a:mem(A),Fst(s12)) | IN(a,Snd(s12))”
           |> conv_rule (depth_fconv no_conv forall_cross_fconv)
           |> rewr_rule[Pair_def']) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a':mem(A))”
    “IN(a':mem(A),a) | IN(a',b)”) >> arw[])
(form_goal “!A. ?!f:Pow(A) * Pow(A) -> Pow(A).
 !s1 s2 a. IN(a,App(f,Pair(s1,s2))) <=> IN(a,s1) | IN(a,s2)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "UNION" [‘A’]

val IN_Inter = prove_store("IN_Inter",
e0
(rw[Inter_def,INTER_def])
(form_goal “!A s1 s2 a. IN(a:mem(A),Inter(s1,s2)) <=> IN(a,s1) & IN(a,s2)”));


val COMPL_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qspecl [‘Pow(A)’,‘Pow(A)’] 
           |> fVar_sInst_th 
           “P(s0:mem(Pow(A)),s:mem(Pow(A)))”
           “!a. IN(a,s) <=> ~IN(a:mem(A),s0)”) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a':mem(A))”
    “~IN(a':mem(A),x)”) >> arw[])
(form_goal “!A. ?!f:Pow(A) -> Pow(A).
 !s a. IN(a,App(f,s)) <=> ~IN(a,s)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "COMPL" [‘A’]

val Compl_def = qdefine_fsym("Compl",[‘s:mem(Pow(A))’])
‘App(COMPL(A),s)’

val IN_Compl = prove_store("IN_Compl",
e0
(rw[Compl_def,COMPL_def])
(form_goal “!A s a. IN(a:mem(A),Compl(s)) <=> ~IN(a,s)”));


val filter_def = qdefine_psym("filter",[‘L:mem(Pow(Pow(J)))’])
‘~EMPTY(J) & IN(Whole(J),L) & 
  (!X Y. IN(X,L) & IN(Y,L) ==> IN(Inter(X,Y),L)) & 
  (!X. IN(X,L) ==> !Y. SS(X,Y) ==> IN(Y,L))’


val ufilter_def = qdefine_psym("ufilter",[‘L:mem(Pow(Pow(J)))’])
‘filter(L) & 
 (!X. ~(IN(Compl(X),L)) <=> IN(X,L))’

val Inter_IN_filter = filter_def |> iffLR |> undisch |> conjE2
                                 |> conjE2 |> conjE1
                                 |> disch_all
                                 |> gen_all

val ufilter_filter = ufilter_def |> iffLR |> undisch |> conjE1
                                 |> disch_all |> gen_all

val Inter_IN_ufilter = prove_store("Inter_IN_ufilter",
e0
(rpt strip_tac >> drule ufilter_filter >>
 drule Inter_IN_filter >> first_x_assum irule >> arw[])
(form_goal “!J L:mem(Pow(Pow(J))). ufilter(L) ==>
 !X Y. IN(X,L) & IN(Y,L) ==> IN(Inter(X,Y),L)”));

val SS_IN_filter = filter_def |> iffLR |> undisch |> conjE2
                              |> conjE2 |> conjE2
                              |> disch_all
                              |> gen_all

val SS_IN_ufilter = prove_store("SS_IN_ufilter",
e0
(rpt strip_tac >> drule ufilter_filter >>
 drule SS_IN_filter >> first_x_assum drule >>
 first_x_assum drule >> arw[])
(form_goal “!J L:mem(Pow(Pow(J))). ufilter(L) ==>
 !X. IN(X,L) ==> !Y. SS(X,Y) ==> IN(Y,L)”))

val Whole_IN_filter = filter_def |> iffLR |> undisch |> conjE2
                                 |> conjE1
                                 |> disch_all |> gen_all
                                 |> store_as "Whole_IN_filter"

val Whole_IN_ufilter = prove_store("Whole_IN_ufilter",
e0
(rpt strip_tac >> drule ufilter_filter >> drule Whole_IN_filter >> arw[])
(form_goal “!J L:mem(Pow(Pow(J))). ufilter(L) ==> IN(Whole(J),L)”));

val Compl_Whole = prove_store("Compl_Whole",
e0
(rw[GSYM IN_EXT_iff,IN_Compl,Whole_def,Empty_def])
(form_goal “!A. Compl(Whole(A)) = Empty(A)”));

val Compl_Empty = prove_store("Compl_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Compl,Whole_def,Empty_def])
(form_goal “!A. Compl(Empty(A)) = Whole(A)”));

val Empty_NOTIN_UF = prove_store("Empty_NOTIN_UF",
e0
(rw[ufilter_def] >> rpt strip_tac >>
 first_x_assum (qsspecl_then [‘Whole(J)’] assume_tac) >>
 fs[Compl_Whole] >> drule Whole_IN_filter >> arw[])
(form_goal “!J L.ufilter(L) ==> ~IN(Empty(J),L)”));


val IN_UF_NONEMPTY = prove_store("IN_UF_NONEMPTY",
e0
(rpt strip_tac >> drule Empty_NOTIN_UF >> ccontra_tac >> fs[])
(form_goal “!J L.ufilter(L) ==> !X.IN(X,L) ==> ~(X = Empty(J))”));

val UFs_def = Thm_2_4 |> qspecl [‘Pow(Pow(J))’]
                      |> fVar_sInst_th “P(a:mem(Pow(Pow(J))))”
                      “ufilter(a:mem(Pow(Pow(J))))”
                      |> qSKOLEM "UFs" [‘J’]
                      |> qSKOLEM "iUF" [‘J’] 


val Repu_def = qdefine_fsym("Repu",[‘u:mem(UFs(J))’])
‘App(iUF(J),u)’

val from_UFs = UFs_def |> conjE2 |> rewr_rule[GSYM Repu_def]

val Repu_ufilter = prove_store("Repu_ufilter",
e0
(rw[UFs_def,Repu_def] >> rpt strip_tac >> qexists_tac ‘u’ >> rw[])
(form_goal “!A u:mem(UFs(A)). ufilter(Repu(u))”));
 


val Empty_NOTIN_UFs = prove_store("Empty_NOTIN_UFs",
e0
(rpt strip_tac >> qsspecl_then [‘u’] assume_tac Repu_ufilter >>
 drule Empty_NOTIN_UF >> arw[])
(form_goal “!J u.~IN(Empty(J),Repu(u))”));



val ufilter_alt = prove_store("ufilter_alt",
e0
(rw[ufilter_def] >> dimp_tac >> strip_tac  
 >-- (strip_tac >-- first_x_assum accept_tac >>
     strip_tac >> first_x_assum (qspecl_then [‘X’] (assume_tac o GSYM)) >>
     arw[]) >>
 strip_tac >-- first_x_assum accept_tac >>
 strip_tac >> first_x_assum (qspecl_then [‘X’] assume_tac) >> arw[])
(form_goal “ufilter(L) <=> filter(L) &
  !X. IN(Compl(X:mem(Pow(J))),L) <=> ~IN(X,L)”));

val Compl_Repu = prove_store("Compl_Repu",
e0
(qsspecl_then [‘u’] assume_tac Repu_ufilter >>
 drule $ iffLR ufilter_alt >>
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘X’] assume_tac) >> arw[])
(form_goal “IN(Compl(X:mem(Pow(J))), Repu(u)) <=> ~IN(X,Repu(u))”));


val Union_def = qdefine_fsym("Union",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘App(UNION(A),Pair(s1,s2))’

val neg_or_distr = proved_th $
e0
(dimp_tac >> strip_tac (* 2 *)
 >-- (qcases ‘A’ >> fs[]) >>
 arw[])
(form_goal “(~(A | B)) <=> (~A & ~B)”)

val Inter_Compl_Compl = prove_store("Inter_Compl_Compl",
e0
(rw[GSYM IN_EXT_iff,Inter_def,INTER_def,Compl_def,COMPL_def,
    UNION_def,Union_def,neg_or_distr])
(form_goal “Inter(Compl(s1:mem(Pow(J))), Compl(s2)) = 
 Compl(Union(s1,s2))”));

val SS_Union = prove_store("SS_Union",
e0
(rw[SS_def,Union_def,UNION_def] >> rpt strip_tac >> arw[])
(form_goal “(!A a:mem(Pow(A)) b.SS(a,Union(a,b))) &
            (!A a:mem(Pow(A)) b.SS(a,Union(b,a)))”));

val SS_Union1 = SS_Union |> conjE1
val SS_Union2 = SS_Union |> conjE2;
 
val Union_Repu = prove_store("Union_Repu",
e0
(dimp_tac >> strip_tac (* 3 *)
 >-- (ccontra_tac >> fs[neg_or_distr] >>
     fs[GSYM Compl_Repu] >> 
     qby_tac ‘IN(Inter(Compl(s1),Compl(s2)),Repu(u))’
     >-- (irule Inter_IN_ufilter >> arw[Repu_ufilter]) >>
     fs[Inter_Compl_Compl] >>
     fs[Compl_Repu]) 
 >-- (qsspecl_then [‘s1’,‘s2’] assume_tac SS_Union1 >>
     irule SS_IN_ufilter >> rw[Repu_ufilter] >>
     qexists_tac ‘s1’ >> arw[SS_Union]) >>
 qsspecl_then [‘s1’,‘s2’] assume_tac SS_Union2 >>
 irule SS_IN_ufilter >> rw[Repu_ufilter] >>
 qexists_tac ‘s2’ >> arw[SS_Union])
(form_goal “IN(Union(s1:mem(Pow(J)),s2), Repu(u)) <=> (IN(s1,Repu(u)) | IN(s2,Repu(u)))”));




val FIP_def = qdefine_psym("FIP",[‘ss:mem(Pow(Pow(A)))’])
‘!ss0. SS(ss0,ss) & Fin(ss0) & ~(ss0 = Empty(Pow(A))) ==> ~(BIGINTER(ss0) = Empty(A))’

(*closed under finite intersection*)
val CUI_def = qdefine_psym("CUI",[‘ss:mem(Pow(Pow(A)))’])
                      ‘!ss0.
        SS(ss0, ss) & Fin(ss0) & ~(ss0 = Empty(Pow(A))) ==>
        IN(BIGINTER(ss0),ss)’

val IN_Union = prove_store("IN_Union",
e0
(rw[Union_def,UNION_def])
(form_goal “!A s1 s2 a:mem(A). IN(a,Union(s1,s2)) <=> IN(a,s1) | IN(a,s2)”));


val Union_Sing = prove_store("Union_Sing",
e0
(rw[GSYM IN_EXT_iff,IN_Union,IN_Sing,Ins_def])
(form_goal “!A a s.Union(Sing(a:mem(A)),s) = Ins(a,s)”));

val SS_Refl = prove_store("SS_Refl",
e0
(rw[SS_def])
(form_goal “!A s:mem(Pow(A)). SS(s,s)”));

val SS_Ins = prove_store("SS_Ins",
e0
(rw[SS_def,Ins_def] >> rpt strip_tac >> arw[])
(form_goal “!A a:mem(A) s. SS(s,Ins(a,s))”));

val BIGINTER_Sing = prove_store("BIGINTER_Sing",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,IN_Sing] >> 
 rw[IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal “!A s:mem(Pow(A)). BIGINTER(Sing(s)) = s”));

val Whole_Inter = prove_store("Whole_Inter",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Whole_def])
(form_goal “!A s.Inter(Whole(A),s) = s”));


val Inter_Whole = prove_store("Inter_Whole",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Whole_def])
(form_goal “!A s.Inter(s,Whole(A)) = s”));


val IN_Inter = prove_store("IN_Inter",
e0
(rw[Inter_def,INTER_def])
(form_goal “!A s1:mem(Pow(A)) s2 a. IN(a,Inter(s1,s2)) <=> IN(a,s1) & IN(a,s2)”));

val Empty_SS = prove_store("Empty_SS",
e0
(rw[SS_def,Empty_def])
(form_goal “!A s. SS(Empty(A),s)”));

val BIGINTER_Empty = prove_store("BIGINTER_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,Whole_def,Empty_def])
(form_goal “BIGINTER(Empty(Pow(A))) = Whole(A)”));

val BIGINTER_Ins_Empty = prove_store("BIGINTER_Ins_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,Ins_def,Empty_def] >>
 rw[IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum irule >> arw[]) >>
 rpt strip_tac >> arw[])
(form_goal “!A x.BIGINTER(Ins(x, Empty(Pow(A)))) = x”));

val Inter_same = prove_store("Inter_same",
e0
(rw[GSYM IN_EXT_iff,IN_Inter] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal “!A x:mem(Pow(A)).Inter(x,x) = x”));


val BIGINTER_Ins = prove_store("BIGINTER_Ins",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,IN_Inter,Ins_def] >>
 rw[IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (first_assum (qspecl_then [‘x’] assume_tac) >>
     fs[] >>
     rpt strip_tac >> first_x_assum irule >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[] >>
 first_x_assum irule >> arw[])
(form_goal “!A x:mem(Pow(A)) xs0. BIGINTER(Ins(x, xs0)) = 
 Inter(x,BIGINTER(xs0))”));


val imp_or_distr = prove_store("imp_or_distr",
e0
(dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum irule >> arw[]) 
 >-- (first_x_assum irule >> arw[]) 
 >-- (first_x_assum drule >> arw[]) >>
 first_x_assum drule >> arw[])
(form_goal “(A | B ==> C) <=> (A ==> C) & (B ==> C)”));
 

val BIGINTER_Union = prove_store("BIGINTER_Union",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,IN_Union,IN_Inter] >>
 rpt strip_tac >> rw[imp_or_distr] >>
 (*better strategy here*)
 dimp_tac >> strip_tac >> arw[])
(form_goal 
     “!A s1 s2:mem(Pow(Pow(A))).
BIGINTER(Union(s1,s2)) = Inter(BIGINTER(s1),BIGINTER(s2))”));


val Empty_Inter = prove_store("Empty_Inter",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Empty_def])
(form_goal “!A s. Inter(Empty(A),s) = Empty(A)”));

val Union_EMPTY = prove_store("Union_EMPTY",
e0
(rw[GSYM IN_EXT_iff,IN_Union,Empty_def] >>
 rw[neg_or_distr] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal “!A s1 s2. Union(s1,s2) = Empty(A) <=> 
    s1 = Empty(A) & s2 = Empty(A)”));

val neg_and_distr = prove_store("neg_and_distr",
e0
(dimp_tac >> strip_tac (* 3 *)
 >> qcases ‘A’ >> fs[])
(form_goal “~(A & B) <=> (~A | ~B)”));

val Fin_Ins_Ins = prove_store("Fin_Ins_Ins",
e0
(rpt strip_tac >> irule Fin_Ins >> irule Fin_Ins >>
 rw[Fin_Empty])
(form_goal “!A a1 a2.Fin(Ins(a1,Ins(a2,Empty(A))))”));

val CUI_iff_binary = prove_store("CUI_iff_binary",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qsuff_tac ‘!s. Fin(s) ==> SS(s,A) & ~(s = Empty(Pow(W))) ==> 
     IN(BIGINTER(s),A)’
     >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
     ind_with (Fin_induct |> qspecl [‘Pow(W)’]) >>
     rw[Ins_NONEMPTY] >> rpt strip_tac >>
     qcases ‘IN(BIGINTER(xs0), A)’ 
     >-- (rw[BIGINTER_Ins] >> 
         first_x_assum irule >> arw[] >>
         fs[SS_def,Ins_def] >> first_x_assum irule >> arw[]) >>
     qby_tac ‘~(SS(xs0, A) & ~(xs0 = Empty(Pow(W))))’
     >-- (ccontra_tac >>  first_x_assum drule >> fs[]) >>
     fs[neg_and_distr] (* 2 *)
     >-- (qby_tac ‘SS(xs0,Ins(x,xs0))’ 
         >-- rw[SS_Ins] >>
         drule SS_Trans >> first_x_assum drule >> fs[]) >>
     rw[BIGINTER_Ins,BIGINTER_Empty,Inter_Whole] >>
     fs[SS_def,Ins_def] >> first_x_assum irule >> arw[]) >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘Ins(a1,Ins(a2,Empty(Pow(W))))’] assume_tac) >>
 fs[GSYM Union_Sing,BIGINTER_Union,BIGINTER_Empty,Inter_Whole,BIGINTER_Sing] >>
 first_x_assum irule >> rw[Union_Sing,Ins_NONEMPTY] >> 
 rw[Fin_Ins_Ins] >> rw[SS_def,Ins_def,Empty_def] >> rpt strip_tac >> arw[])
(form_goal
 “!W A:mem(Pow(Pow(W))).
  (!a1. IN(a1,A) ==> !a2.IN(a2,A) ==> IN(Inter(a1,a2),A)) <=> 
  (!s. SS(s,A) & Fin(s) & ~(s = Empty(Pow(W))) ==> IN(BIGINTER(s),A))”));

(*
val SS_Union = prove_store("SS_Union",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (x_choose_then "s1" assume_tac
 (IN_def_P_ex |> qspecl [‘Pow(W)’] 
 |> fVar_sInst_th “P(a:mem(Pow(W)))”
    “IN(a,s) & IN(a,A:mem(Pow(Pow(W))))”) >> 
 x_choose_then "s2" assume_tac
 (IN_def_P_ex |> qspecl [‘Pow(W)’] 
 |> fVar_sInst_th “P(a:mem(Pow(W)))”
    “IN(a,s) & IN(a,B:mem(Pow(Pow(W))))”) >>
 qexistsl_tac [‘s1’,‘s2’] >>
 (*AQ:automatic improvement here*)
 qby_tac ‘SS(s1,A)’
 >-- (rw[SS_def] >> rpt strip_tac >>
     first_x_assum (drule o iffRL) >> arw[]) >>
 qby_tac ‘SS(s2,B)’
 >-- (rw[SS_def] >> rpt strip_tac >>
     first_x_assum (drule o iffRL) >> arw[]) >> arw[] >>
 rw[GSYM IN_EXT_iff,IN_Union] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[SS_def,IN_Union] >> 
     first_x_assum drule >> pop_assum strip_assume_tac (* 2 *)
     >-- (disj1_tac >> first_x_assum (irule o iffLR) >> arw[]) >>
     disj2_tac >> first_x_assum (irule o iffLR) >> arw[]) >>
 first_x_assum (drule o iffRL) >> arw[]) >>
 rw[SS_def,IN_Union] >> rpt strip_tac >>
 fs[GSYM IN_EXT_iff,IN_Union] >>
 first_x_assum (drule o iffLR) >> pop_assum strip_assume_tac (* 2 *)
 >-- (fs[SS_def] >> disj1_tac >> first_x_assum irule >> arw[]) >>
 fs[SS_def] >> disj2_tac >> first_x_assum irule >> arw[] )
(form_goal “!W A B:mem(Pow(W)) s. SS(s,Union(A,B)) <=>
  ?s1 s2. SS(s1,A) & SS(s2,B) & s = Union(s1,s2) ”));
*)

 
val SS_Union_split = prove_store("SS_Union_split",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (x_choose_then "s1" assume_tac
 (IN_def_P_ex |> qspecl [‘W’] 
 |> fVar_sInst_th “P(a:mem(W))”
    “IN(a,s) & IN(a,A:mem(Pow(W)))”) >> 
 x_choose_then "s2" assume_tac
 (IN_def_P_ex |> qspecl [‘W’] 
 |> fVar_sInst_th “P(a:mem(W))”
    “IN(a,s) & IN(a,B:mem(Pow(W)))”) >>
 qexistsl_tac [‘s1’,‘s2’] >>
 (*AQ:automatic improvement here*)
 qby_tac ‘SS(s1,A)’
 >-- (rw[SS_def] >> rpt strip_tac >>
     first_x_assum (drule o iffRL) >> arw[]) >>
 qby_tac ‘SS(s2,B)’
 >-- (rw[SS_def] >> rpt strip_tac >>
     first_x_assum (drule o iffRL) >> arw[]) >> arw[] >>
 rw[GSYM IN_EXT_iff,IN_Union] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[SS_def,IN_Union] >> 
     first_x_assum drule >> pop_assum strip_assume_tac (* 2 *)
     >-- (disj1_tac >> first_x_assum (irule o iffLR) >> arw[]) >>
     disj2_tac >> first_x_assum (irule o iffLR) >> arw[]) >>
 first_x_assum (drule o iffRL) >> arw[]) >>
 rw[SS_def,IN_Union] >> rpt strip_tac >>
 fs[GSYM IN_EXT_iff,IN_Union] >>
 first_x_assum (drule o iffLR) >> pop_assum strip_assume_tac (* 2 *)
 >-- (fs[SS_def] >> disj1_tac >> first_x_assum irule >> arw[]) >>
 fs[SS_def] >> disj2_tac >> first_x_assum irule >> arw[] )
(form_goal “!W A B:mem(Pow(W)) s. SS(s,Union(A,B)) <=>
  ?s1 s2. SS(s1,A) & SS(s2,B) & s = Union(s1,s2) ”));


val Inter_Empty = prove_store("Inter_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Empty_def])
(form_goal “!A s. Inter(s,Empty(A)) = Empty(A)”));


val IN_NONEMPTY = prove_store("IN_NONEMPTY",
e0
(rw[GSYM IN_EXT_iff,Empty_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[]) >>
 ccontra_tac >>
 qsuff_tac ‘!a. ~IN(a,s)’ >-- arw[] >>
 strip_tac >> ccontra_tac >>
 qsuff_tac ‘?a. IN(a,s)’ >--arw[] >>
 qexists_tac ‘a’ >> arw[])
(form_goal “!A s. (?a. IN(a,s)) <=> ~(s = Empty(A))”));

val SS_Sing = prove_store("SS_Sing",
e0
(rw[SS_def,IN_Sing] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac >> arw[] (* 3 *)
 >-- (qcases ‘?a. IN(a,s)’ (* 2 *)
     >-- (disj1_tac >> rw[GSYM IN_EXT_iff,IN_Sing] >>
         strip_tac >> dimp_tac >> arw[] >> strip_tac >>
         fs[] >> first_x_assum drule >> fs[]) >>
     disj2_tac >> fs[IN_NONEMPTY])
 >-- rfs[IN_Sing] >>
 rfs[Empty_def])
(form_goal “!A a s. SS(s,Sing(a)) <=> s = Sing(a) | s = Empty(A)”));

val Empty_Union = prove_store("Empty_Union",
e0
(rw[GSYM IN_EXT_iff,IN_Union,Empty_def])
(form_goal “!A s. Union(Empty(A),s) = s”));


val SS_Empty = prove_store("SS_Empty",
e0
(rw[GSYM IN_EXT_iff,Empty_def,SS_def])
(form_goal “!A s. SS(s,Empty(A)) <=> s = Empty(A)”));


val Fin_SS = prove_store("Fin_SS",
e0
(strip_tac >>
 ind_with (Fin_induct |> qspecl [‘A’]) >>
 rw[SS_Empty] >> rpt strip_tac >> arw[Fin_Empty] >>
 fs[GSYM Union_Sing,SS_Union_split,SS_Sing] (* 2 *)
 >-- (rw[Union_Sing] >> irule Fin_Ins >> 
     first_x_assum irule >> arw[]) >>
 rw[Empty_Union] >> first_x_assum irule >> arw[])
(form_goal “!A s:mem(Pow(A)). Fin(s) ==> !t. SS(t,s) ==> Fin(t) ”));


val disj_assoc = prove_store("disj_assoc",
e0
(dimp_tac >> qcases ‘A’ >> fs[])
(form_goal “(A | B) | C <=> A | B | C”));

val Union_assoc = prove_store("Union_assoc",
e0
(rw[GSYM IN_EXT_iff,IN_Union,disj_assoc])
(form_goal “!A s1:mem(Pow(A)) s2 s3. Union(Union(s1,s2),s3) = Union(s1,Union(s2,s3))”));

val Fin_Union = prove_store("Fin_Union",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (strip_tac >> irule Fin_SS >> 
     qexists_tac ‘Union(s1,s2)’ >> arw[SS_Union1]) >>
 arw[SS_Union2] >>
 qsuff_tac ‘!s1:mem(Pow(A)).
 Fin(s1) ==> !s2. Fin(s2) ==> Fin(Union(s1,s2))’
 >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
 pop_assum_list  (map_every (K all_tac)) >> 
 ind_with (Fin_induct |> qspecl [‘A’]) >>
 rw[Empty_Union] >> rpt strip_tac >>
 rw[GSYM Union_Sing,Union_assoc] >> 
 rw[Union_Sing] >> first_x_assum drule >>
 irule Fin_Ins >> arw[])
(form_goal “!A s1:mem(Pow(A)) s2.Fin(Union(s1,s2)) <=> Fin(s1) & Fin(s2)”));

val FIP_CUI_lemma = prove_store("FIP_CUI_lemma",
e0
(rpt strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[] >> fs[GSYM IN_NONEMPTY] >>
     first_x_assum (qspecl_then [‘Empty(W)’] assume_tac) >>
     first_x_assum drule >> first_x_assum drule >>
     fs[Empty_Inter,Empty_def]) >>
 ccontra_tac >> fs[] >> fs[GSYM IN_NONEMPTY] >>
 first_x_assum drule >>
 first_x_assum (qspecl_then [‘Empty(W)’] assume_tac) >>
 first_x_assum drule >>
 fs[Inter_Empty,Empty_def])
(form_goal “!W A B. 
 ~(A = Empty(Pow(W))) & ~(B = Empty(Pow(W))) &
 (!a. IN(a,A) ==> !b. IN(b,B) ==> ~(Inter(a,b) = Empty(W))) ==>
 ~IN(Empty(W),A) & ~IN(Empty(W),B)
 ”));

val FIP_closed_under_Inter = prove_store("FIP_closed_under_Inter",
e0
(rpt strip_tac >> fs[CUI_iff_binary] >>
 rw[FIP_def] >> strip_tac >> rw[SS_Union_split] >>
 rpt strip_tac >> arw[BIGINTER_Union] >> rfs[Union_EMPTY,Fin_Union] >>
 qby_tac ‘~IN(Empty(W),A) & ~IN(Empty(W),B)’ 
 >-- (irule FIP_CUI_lemma >> arw[]) >> fs[] >> 
 qcases ‘s1 = Empty(Pow(W))’
 >-- (fs[BIGINTER_Empty,Whole_Inter] >>
     qby_tac ‘IN(BIGINTER(s2),B)’ 
     >-- (first_x_assum irule >> arw[]) >>
     fs[GSYM IN_NONEMPTY] >> rw[IN_NONEMPTY] >>
     first_x_assum drule >>
     first_x_assum drule >> fs[IN_NONEMPTY] >>
     ccontra_tac >> fs[Inter_Empty]) >>
 qcases ‘s2 = Empty(Pow(W))’
 >-- (fs[BIGINTER_Empty,Inter_Whole] >>
     qby_tac ‘IN(BIGINTER(s1),A)’ 
     >-- (first_x_assum irule >> arw[]) >>
     fs[GSYM IN_NONEMPTY] >> rw[IN_NONEMPTY] >>
     first_x_assum drule >>
     first_x_assum drule >> fs[IN_NONEMPTY] >>
     ccontra_tac >> fs[Empty_Inter]) >>
 first_x_assum irule >> strip_tac (* 2 *) >>
 first_x_assum irule >> arw[])
(form_goal
 “!W A B. ~(A = Empty(Pow(W))) & ~(B = Empty(Pow(W))) &
  (!a1. IN(a1,A) ==> !a2.IN(a2,A) ==> IN(Inter(a1,a2),A)) &
  (!b1. IN(b1,B) ==> !b2.IN(b2,B) ==> IN(Inter(b1,b2),B)) & 
  (!a. IN(a,A) ==> !b. IN(b,B) ==> ~(Inter(a,b) = Empty(W))) ==>
  FIP(Union(A,B))
 ”));
 


val Ins_Ins_Fin = prove_store("Ins_Ins_Fin",
e0
(qspecl_then [‘A’] assume_tac Fin_Empty >>
 drule Fin_Ins >>
 first_x_assum (qspecl_then [‘s2’] assume_tac) >>
 drule Fin_Ins >> arw[])
(form_goal “Fin(Ins(s1, Ins(s2, Empty(A))))”));



(*
val closed_under_inter_two = prove_store("FIP_iff_two",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     first_x_assum 
     (qspecl_then [‘Ins(s1,Ins(s2,Empty(Pow(A))))’] assume_tac) >>
     fs[Ins_Ins_Fin] >>
     fs[SS_def,Ins_def,Empty_def] >>
     qby_tac ‘BIGINTER(Ins(s1, Ins(s2, Empty(Pow(A))))) = Inter(s1, s2)’
     >-- (rw[IN_BIGINTER,GSYM IN_EXT_iff,IN_Inter,Ins_def,Empty_def] >>
         rw[IN_EXT_iff] >> strip_tac >> dimp_tac (* 2 *)
         >-- (rpt strip_tac >> first_x_assum irule >> rw[]) >>
         rpt strip_tac >> arw[]) >>
     fs[] >> first_x_assum irule >> arw[] >> rpt strip_tac >> arw[] >>
     fs[Ins_NONEMPTY]) >>
 qsuff_tac
 ‘!ss0. Fin(ss0) ==> SS(ss0,ss) ==> ~(ss0 = Empty(Pow(A))) ==>
  IN(BIGINTER(ss0),ss)’
 >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
 ind_with (Fin_induct |> qspecl [‘Pow(A)’]) >>
 rw[Empty_SS,BIGINTER_Empty] >>
 rpt strip_tac >>
 qby_tac ‘SS(xs0, ss)’ >-- cheat >>
 first_x_assum drule >> 
 qby_tac ‘IN(x,ss)’ 
 >-- (fs[SS_def,Ins_def] >> last_x_assum irule >> rw[]) >>
 qcases ‘xs0 = Empty(Pow(A))’ 
 >-- arw[BIGINTER_Ins_Empty] >> 
 first_assum (qspecl_then [‘x’] assume_tac) >>
 first_x_assum drule >>
 first_assum (qspecl_then [‘x’] assume_tac) >>
 first_x_assum drule >> fs[Inter_same] >>
 qby_tac
 ‘’
 
     
 
 )
(form_goal “!ss:mem(Pow(Pow(A))). (!ss0.SS(ss0,ss) & Fin(ss0) & ~(ss0 = Empty(Pow(A))) ==> IN(BIGINTER(ss0),ss)) <=> 
 (!s1. IN(s1,ss) ==> !s2.IN(s2,ss) ==> IN(Inter(s1,s2),ss))”));
*)

val gfss_def = proved_th $
e0
(rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘Pow(Pow(A))’] 
 |> fVar_sInst_th “P(a:mem(Pow(Pow(A))))”
    “SS(s0,a:mem(Pow(Pow(A)))) & filter(a)”) >>
 arw[])
(form_goal “!A s0:mem(Pow(Pow(A))).
 ?!ss. !s. IN(s,ss) <=> SS(s0,s) & filter(s)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "gfss" [‘s0’]

val gfilter_def = qdefine_fsym("gfilter",[‘s:mem(Pow(Pow(A)))’])
‘BIGINTER(gfss(s:mem(Pow(Pow(A)))))’

val IN_gfilter = 
    gfilter_def |> rewr_rule[GSYM IN_EXT_iff,IN_BIGINTER,gfss_def] 

val gfilter_ind = IN_gfilter |> iffLR  
                             |> strip_all_and_imp
                             |> disch “IN(x:mem(Pow(A)), gfilter(s))”
                             |> qgen ‘x’
                             |> disch_all
                             |> gen_all

val gfilter_filter = prove_store("gfilter_filter",
e0
(rw[filter_def] >> rpt strip_tac >> arw[] (* 3 *)
 >-- (rw[IN_gfilter] >> rpt strip_tac >> irule Whole_IN_filter >> arw[]) 
 >-- (fs[IN_gfilter] >> rpt strip_tac >> irule Inter_IN_filter >>
     arw[] >> strip_tac >> first_x_assum irule >> arw[]) >>
 fs[IN_gfilter] >> rpt strip_tac >>
 irule SS_IN_filter >> arw[] >>
 qexists_tac ‘X’ >> arw[] >> first_x_assum irule >> arw[])
(form_goal “!A.~(EMPTY(A)) ==>  !s:mem(Pow(Pow(A))). filter(gfilter(s))”));

val pfilter_def = qdefine_psym("pfilter",[‘L:mem(Pow(Pow(J)))’])
‘filter(L) & ~(L = Whole(Pow(J)))’

val SS_gfilter = prove_store("SS_gfilter",
e0
(rw[SS_def,IN_gfilter] >>
 rpt strip_tac >>  first_x_assum irule >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))).SS(s,gfilter(s))”));

val gfilter1_def = proved_th $
e0
(strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘Pow(A)’]
           |> fVar_sInst_th “P(a:mem(Pow(A)))”
              “a = Whole(A) |
               ?ss. SS(ss,s) & Fin(ss) & ~(ss = Empty(Pow(A))) & SS(BIGINTER(ss),a)”) >> arw[])
(form_goal
 “!s. ?!gf. !x. IN(x,gf) <=>
 ( x = Whole(A) | ?ss. SS(ss,s) & Fin(ss) & ~(ss = Empty(Pow(A))) & SS(BIGINTER(ss),x))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "gfilter1" [‘s’]


val Inter_Whole_Whole = prove_store("Inter_Whole_Whole",
e0
(rpt strip_tac >> dimp_tac >> arw[] >> rpt strip_tac (* 3 *)
 >> fs[GSYM IN_EXT_iff,Whole_def,IN_Inter])
(form_goal “!A s1:mem(Pow(A)) s2. Inter(s1,s2) = Whole(A) <=> s1 = Whole(A) & s2 = Whole(A)”));

val Union_SS1 = prove_store("Union_SS1",
e0
(rpt strip_tac >> rw[SS_def,IN_Union,imp_or_distr] >>
 dimp_tac >> strip_tac >> arw[])
(form_goal “!A s1 s2 s:mem(Pow(A)). SS(Union(s1,s2),s) <=>
 SS(s1,s) & SS(s2,s)”));


val Union_Empty = Union_EMPTY

val SS_Inter = prove_store("SS_Inter",
e0
(rw[SS_def,IN_Inter] >> rpt strip_tac >> 
 dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum drule >> arw[])
 >-- (first_x_assum drule >> arw[]) 
 >-- (first_x_assum irule >> arw[]) >>
 first_x_assum irule >> arw[])
(form_goal “!A s1 s2:mem(Pow(A)) s. SS(s,Inter(s1,s2)) <=>
 SS(s,s1) & SS(s,s2)”));
 
val Inter_SS = prove_store("Inter_SS",
e0
(rw[SS_def,IN_Inter] >> rpt strip_tac)
(form_goal “!A s1 s2:mem(Pow(A)). SS(Inter(s1,s2),s1) & SS(Inter(s1,s2),s2)”));

val Whole_SS = prove_store("Whole_SS",
e0
(rw[SS_def,Whole_def,GSYM IN_EXT_iff])
(form_goal “!A X.SS(Whole(A),X) ==> X = Whole(A)”));

val gfilter1_filter = prove_store("gfilter1_filter",
e0
(rw[filter_def] >> rpt strip_tac >> arw[] (* 3 *)
 >-- rw[gfilter1_def]
 >-- (rw[gfilter1_def] >>
     qcases ‘X = Whole(A)’ (* 2 *)
     >-- (qcases ‘Y = Whole(A)’ 
         >-- (disj1_tac >> arw[Inter_Whole]) >>
         fs[Whole_Inter] >> drule $ iffLR gfilter1_def >> rfs[] >>
         qexists_tac ‘ss’ >> arw[]) >>
     qcases ‘Y = Whole(A)’ (* 2 *)
     >-- (arw[Inter_Whole] >> rev_drule $ iffLR gfilter1_def >> rfs[] >>
         qexists_tac ‘ss’ >> arw[]) >> arw[Inter_Whole_Whole] >>
     fs[gfilter1_def] >>
     qexists_tac ‘Union(ss,ss')’ >>
     arw[Union_SS1,Fin_Union,Union_Empty,BIGINTER_Union,SS_Inter] >>
     strip_tac >> irule SS_Trans (* 2 *)
     >-- (qexists_tac ‘BIGINTER(ss)’ >> arw[Inter_SS]) >>
     qexists_tac ‘BIGINTER(ss')’ >> arw[Inter_SS]) >>
 fs[gfilter1_def] (* 2 *)
 >-- (disj1_tac >> irule Whole_SS >> rfs[]) >>
 disj2_tac >> qexists_tac ‘ss’ >> arw[] >>
 irule SS_Trans >> qexists_tac ‘X’ >> arw[])
(form_goal “!A.~(EMPTY(A)) ==>  !s:mem(Pow(Pow(A))). filter(gfilter1(s))”));

val Sing_Ins_Empty = prove_store("Sing_Ins_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Sing,Ins_def,Empty_def])
(form_goal “!A a:mem(A). Sing(a) = Ins(a,Empty(A))”));

val Fin_Sing = prove_store("Fin_Sing",
e0
(rw[Sing_Ins_Empty] >> rpt strip_tac >> irule Fin_Ins >>
rw[Fin_Empty])
(form_goal “!A a:mem(A).Fin(Sing(a))”));

val SS_gfilter1 = prove_store("SS_gfilter1",
e0
(rw[SS_def,gfilter1_def] >> rpt strip_tac >>
 disj2_tac >>
 qexists_tac ‘Sing(a)’ >> rw[IN_Sing,Sing_NONEMPTY,BIGINTER_Sing,Fin_Sing] >>
 rpt strip_tac >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))). SS(s,gfilter1(s))”));

val CUI_filter = prove_store("CUI_filter",
e0
(rpt strip_tac >> fs[filter_def,CUI_def] >> rpt gen_tac >> strip_tac >>
 irule $ iffLR CUI_iff_binary >> arw[] >>
 rpt strip_tac >> last_x_assum irule >> arw[])
(form_goal “!A L:mem(Pow(Pow(A))).filter(L) ==> CUI(L)”));

val gfilter_gfilter1 = prove_store("gfilter_gfilter1",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff] >> rpt strip_tac >>
 drule gfilter_filter >> drule gfilter1_filter >>
 dimp_tac >--
 (match_mp_tac gfilter_ind >> arw[SS_gfilter1]) >>
 rw[IN_gfilter,gfilter1_def] >> rpt strip_tac >> arw[]
 >-- (irule Whole_IN_filter >> arw[]) >>
 drule CUI_filter >> fs[CUI_def] >>
 first_x_assum (qspecl_then [‘ss’] assume_tac) >>
 rfs[] >>
 qby_tac ‘SS(ss, ss')’ >-- (irule SS_Trans >> qexists_tac ‘s’ >> arw[]) >>
 fs[] >>
 irule SS_IN_filter >> arw[] >> qexists_tac ‘BIGINTER(ss)’ >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))).~(EMPTY(A)) ==> gfilter(s) = gfilter1(s)”));

val Empty_NOTIN_pfilter = prove_store("Empty_NOTIN_pfilter",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[pfilter_def] >> ccontra_tac >>
     qsuff_tac ‘s = Whole(Pow(A))’ 
     >-- arw[] >>
     rw[GSYM IN_EXT_iff,Whole_def] >> strip_tac >>
     irule SS_IN_filter >> arw[] >>
     qexists_tac ‘Empty(A)’ >> arw[Empty_SS]) >>
 fs[pfilter_def] >> ccontra_tac >> fs[Whole_def])
(form_goal “!A s.pfilter(s) <=> filter(s) & ~IN(Empty(A),s)”));

val EMPTY_Empty_Whole = prove_store("EMPTY_Empty_Whole",
e0
(rw[GSYM IN_EXT_iff,Empty_def,Whole_def,EMPTY_def])
(form_goal “!A. EMPTY(A) <=> Empty(A) = Whole(A)”));

val FIP_Empty_NOTIN_gfilter = prove_store("FIP_Empty_NOTIN_gfilter",
e0
(rpt strip_tac >> ccontra_tac >>
 fs[FIP_def] >> drule gfilter_gfilter1 >> fs[] >>
 fs[gfilter1_def] 
 >-- fs[EMPTY_Empty_Whole] >>
 fs[SS_Empty] >>
 first_x_assum (qspecl_then [‘ss’] assume_tac) >> rfs[])
(form_goal “!A.~EMPTY(A) ==> !s:mem(Pow(Pow(A))).FIP(s) ==> 
 ~IN(Empty(A),gfilter(s)) ”));

val FIP_PSUBSET_proper_filter = prove_store("FIP_PSUBSET_proper_filter",
e0
(rpt strip_tac >> qexists_tac ‘gfilter(s)’ >> 
 rw[SS_gfilter] >> rw[Empty_NOTIN_pfilter] >>
 drule gfilter_filter >> arw[] >>
 irule FIP_Empty_NOTIN_gfilter >> arw[])
(form_goal “!A. ~EMPTY(A) ==>
 !s:mem(Pow(Pow(A))).FIP(s) ==> ?v.pfilter(v) & SS(s,v)”));


val PSS_def = qdefine_psym("PSS",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘SS(s1:mem(Pow(A)),s2) & ~(s1 = s2)’

(*NEQ_IN terrible*)

val NEQ_IN = prove_store("NEQ_IN",
e0
(rw[GSYM IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> strip_tac (* 3 *)
 >-- (qcases ‘?a:mem(A).IN(a,s1) & ~IN(a,s2)’ >> arw[] >>
     ccontra_tac >> 
     qsuff_tac ‘!x.IN(x,s1) <=> IN(x,s2)’ >-- arw[] >>
     strip_tac >> last_x_assum (K all_tac) >>
     qcases ‘IN(x,s1)’ >> arw[] (* 2 *)
     >-- (ccontra_tac >>
         (*how can HOL realise it from here?*)
         qsuff_tac ‘?a. IN(a,s1) & ~IN(a,s2)’ >-- arw[] >>
         qexists_tac ‘x’ >> arw[]) >>
     ccontra_tac >>
     qsuff_tac ‘?a. IN(a,s2) & ~IN(a,s1)’ >-- arw[] >>
     qexists_tac ‘x’ >> arw[]) 
 >> ccontra_tac >> fs[])
(form_goal “!A s1 s2. ~(s1 = s2) <=> 
 (?a:mem(A).IN(a,s1) & ~IN(a,s2)) | (?a. IN(a,s2) & ~IN(a,s1))”));
 
val PSS_alt = prove_store("PSS_alt",
e0
(rw[PSS_def] >> rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] (* 2 *)
 >-- (fs[NEQ_IN,SS_def] (*2 *)
     >-- (first_x_assum drule >> fs[]) >>
     qexists_tac ‘a’ >> arw[]) >>
 ccontra_tac >> fs[])
(form_goal “!A s1 s2:mem(Pow(A)).PSS(s1,s2) <=> 
 SS(s1,s2) & ?a. IN(a,s2) & ~IN(a,s1)”));


val filter_Whole = prove_store("filter_Whole",
e0
(rw[Whole_def,filter_def])
(form_goal “!J.~EMPTY(J) ==> filter(Whole(Pow(J)))”));

val filter_Empty_Whole = prove_store("filter_Empty_Whole",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (rw[GSYM IN_EXT_iff,Whole_def] >> 
     drule SS_IN_filter >> first_x_assum drule >>
     strip_tac >> first_x_assum (qspecl_then [‘x’] assume_tac) >>
     fs[Empty_SS]) >>
 drule filter_Whole >> arw[Whole_def])
(form_goal “!J. ~EMPTY(J) ==> !L. filter(L) & IN(Empty(J),L) <=> L = Whole(Pow(J))”));

val Inter_Compl = prove_store("Inter_Compl",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,IN_Compl,Empty_def] >> rpt strip_tac >> rw[] >>
 ccontra_tac >> fs[])
(form_goal “!A a:mem(Pow(A)). Inter(a,Compl(a)) = Empty(A)”));

val ufilter_maximal = prove_store("ufilter_maximal",
e0
(rpt strip_tac >> fs[] >> fs[PSS_alt] >>
 irule $ iffLR filter_Empty_Whole >> arw[] >>
 qby_tac ‘~EMPTY(J)’ >-- fs[filter_def] >> arw[] >>
 drule Inter_IN_filter >>
 fs[ufilter_def] >>
 last_x_assum (qspecl_then [‘a’] assume_tac) >>
 pop_assum (assume_tac o GSYM) >> rfs[] >>
 fs[SS_def] >> first_x_assum drule >>
 first_x_assum (qspecl_then [‘a’,‘Compl(a)’] assume_tac) >>
 rfs[Inter_Compl])
(form_goal
 “!J u:mem(Pow(Pow(J))). ufilter(u) ==>
  !s. filter(s) & PSS(u,s) ==> s = Whole(Pow(J))”));

val neg_iff = prove_store("neg_iff",
e0
(dimp_tac >> strip_tac >> qcases ‘A’ >> fs[])
(form_goal “~(A <=> B) <=> (A & ~B) | (B & ~A)”));



val CUI_Empty_NOTIN_FIP = prove_store("CUI_Empty_NOTIN_FIP",
e0
(rw[FIP_def,CUI_def] >> rpt strip_tac >>
 ccontra_tac >> 
 qsuff_tac ‘IN(BIGINTER(ss0),s)’ 
 >-- arw[] >>
 first_x_assum irule >> arw[])
(form_goal “!W s:mem(Pow(Pow(W))). 
 CUI(s) & ~IN(Empty(W),s) ==> FIP(s)”));

val pfilter_FIP = prove_store("pfilter_FIP",
e0
(rpt strip_tac >> irule CUI_Empty_NOTIN_FIP >>
 fs[Empty_NOTIN_pfilter] >> drule CUI_filter >> arw[] )
(form_goal “!W s:mem(Pow(Pow(W))). pfilter(s) ==>
 FIP(s)”));

val pfilter_filter = prove_store("pfilter_filter",
e0
(rw[pfilter_def] >> rpt strip_tac)
(form_goal “!A s:mem(Pow(Pow(A))). pfilter(s) ==> filter(s)”));

val Union_Empty2 = prove_store("Union_Empty2",
e0
(rw[IN_Union,GSYM IN_EXT_iff,Empty_def])
(form_goal “!A s. Union(s,Empty(A)) = s”));

val Inter_eq_Empty = prove_store("Inter_eq_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,SS_def,IN_Compl,Empty_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> ccontra_tac >>
 fs[] (* 2 *)
 >-- (first_x_assum (qspecl_then [‘a’] assume_tac) >>
     rfs[]) >>
 first_x_assum drule >> fs[])
(form_goal 
 “!W s1 s2.
 Inter(s1,s2) = Empty(W) <=> SS(s2,Compl(s1))”));

val pfilter_INSERT_FIP =
    prove_store("proper_filter_INSERT_FIP",
e0
(rw[FIP_def] >> rpt strip_tac >>
 qby_tac ‘~(b = Empty(W))’ >-- 
 (ccontra_tac >> fs[Compl_Empty,pfilter_def,filter_def]) >>  
 drule pfilter_FIP >>
 fs[GSYM Union_Sing] >> fs[SS_Union_split] >>
 fs[SS_Sing] (* 2 *)
 >-- (qcases ‘s2 = Empty(Pow(W))’ (* 2 *)
     >-- arw[Union_Empty2,BIGINTER_Sing] >>
     rw[BIGINTER_Union,BIGINTER_Sing] >>
     drule pfilter_filter >>
     drule CUI_filter >> ccontra_tac >>
     qsuff_tac ‘SS(BIGINTER(s2), Compl(b))’ 
     >-- (strip_tac >> drule SS_IN_filter >>
         first_x_assum
         (qspecl_then [‘BIGINTER(s2)’] assume_tac) >>
         rfs[Fin_Union] >>
         qby_tac ‘IN(BIGINTER(s2), s)’ 
         >-- (fs[CUI_def] >> last_x_assum irule >>
             arw[]) >>
         first_x_assum drule >>
         first_x_assum drule >> fs[]) >>
     fs[Inter_eq_Empty]) >>
 fs[Empty_Union] >> 
 qcases ‘s2 = Empty(Pow(W))’ (* 2 *)
 >-- (arw[BIGINTER_Empty] >> flip_tac >> 
     rw[GSYM EMPTY_Empty_Whole] >>
     fs[pfilter_def,filter_def]) >>
 ccontra_tac >> 
 drule pfilter_filter >>
 drule CUI_filter >>
 qby_tac ‘IN(BIGINTER(s2), s)’ 
 >-- (drule $ iffLR CUI_def >> last_x_assum irule >>
      arw[] >> rfs[Fin_Union]) >>
 qby_tac ‘IN(b,s)’ 
 >-- (irule SS_IN_filter >> fs[pfilter_def] >>
     qexists_tac ‘Empty(W)’ >> rfs[Empty_SS]) >>
 fs[])
(form_goal “!W s:mem(Pow(Pow(W))). pfilter(s) ==>
 !b. ~IN(b,s) & ~IN(Compl(b),s) ==> FIP(Ins(b,s))”));


val maximal_ufilter = prove_store("maximal_ufilter",
e0
(rpt strip_tac >> arw[ufilter_def] >>
 qby_tac ‘filter(u)’ >-- fs[pfilter_def] >> arw[] >>
 strip_tac >> ccontra_tac >>
 fs[neg_iff] (* 2 *)
 >-- (qby_tac ‘FIP(Ins(X,u))’ >-- 
      (irule pfilter_INSERT_FIP >> arw[]) >>
     qby_tac ‘~EMPTY(J)’ >-- fs[filter_def,pfilter_def] >>
     drule FIP_PSUBSET_proper_filter >> first_x_assum drule >>
     pop_assum strip_assume_tac >> 
     first_x_assum (qspecl_then [‘v’] assume_tac) >>
     qby_tac ‘filter(v)’ >-- fs[pfilter_def] >> 
     qby_tac ‘PSS(u,v)’ 
     >-- (rw[PSS_alt] >> strip_tac (* 2 *)
         >-- (irule SS_Trans >> qexists_tac ‘Ins(X, u)’ >>
             arw[SS_Ins]) >>
         qexists_tac ‘X’ >> arw[] >>
         fs[SS_def] >> first_x_assum irule >> rw[Ins_def]) >>
     fs[pfilter_def]) >>
 drule Inter_IN_filter >>
 first_x_assum (qspecl_then [‘X’,‘Compl(X)’] assume_tac) >> rfs[] >>
 fs[Inter_Compl] >> 
 qby_tac ‘u = Whole(Pow(J))’ 
 >-- (irule $ iffLR filter_Empty_Whole >>
     fs[filter_def]) >>
 fs[pfilter_def])
(form_goal “!J u. pfilter(u) ==> 
 (!s. filter(s) & PSS(u,s) ==> s = Whole(Pow(J))) ==>
 ufilter(u) ”));



val chain_def = qdefine_psym("chain",[‘t:mem(Pow(A))’,‘R:A~>A’])
‘!a1 a2. IN(a1,t) & IN(a2,t) ==> Holds(R,a1,a2) | Holds(R,a2,a1)’

val ptorder_def = qdefine_psym("ptorder",[‘R:A~>A’])
‘Trans(R) & Refl(R) & Asym(R)’

val ubound_def = qdefine_psym("ubound",[‘s:mem(Pow(A))’,‘R:A~>A’,‘x:mem(A)’])
‘!y. IN(y,s) ==> Holds(R,y,x)’

val ismax_def = qdefine_psym("ismax",[‘R:A~>A’,‘m:mem(A)’]) 
‘!x. Holds(R,m,x) ==> x = m’

val zorns_lemma = store_ax("zorns_lemma",
“!A R:A~>A. ptorder(R) ==> 
  (!c. chain(c,R) & ~(c = Empty(A)) ==> ?ub. ubound(c,R,ub)) ==>
  ?m. ismax(R,m)”);




(*
val Ubs_def = proved_th $
e0
()
(form_goal “!A s R:A~>A. ?!ubs. 
 !x. IN(x,ubs) <=> !y. IN(y,s) ==> Holds(R,y,x)”)

val zorns_lemma = store_ax("zorns_lemma",
“!r s. ptorder”);

*)

(* partial_order_def 
∀r s.
       partial_order r s ⇔
       domain r ⊆ s ∧ range r ⊆ s ∧ transitive r ∧ reflexive r s ∧ antisym r:
   thm

 chain_def 
 ∀s r. chain s r ⇔ ∀x y. x ∈ s ∧ y ∈ s ⇒ (x,y) ∈ r ∨ (y,x) ∈ r: thm

upper_bounds_def = 
 ∀s r. upper_bounds s r = {x | x ∈ range r ∧ ∀y. y ∈ s ⇒ (y,x) ∈ r}

zorns_lemma

∀r s.
       s ≠ ∅ ∧ partial_order r s ∧ (∀t. chain t r ⇒ upper_bounds t r ≠ ∅) ⇒
       ∃x. x ∈ maximal_elements s r: thm




("set_relation", "maximal_elements_def"),
     (⊢ ∀xs r.
          maximal_elements xs r =
          {x | x ∈ xs ∧ ∀x'. x' ∈ xs ∧ (x,x') ∈ r ⇒ x = x'}

*)

val ufilter_iff_maximal = prove_store("ufilter_iff_maximal",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (drule maximal_ufilter >> first_x_assum drule >> arw[]) >>
 drule ufilter_maximal >> arw[])
(form_goal “!J u. pfilter(u) ==>
 ((!s. filter(s) & PSS(u,s) ==> s= Whole(Pow(J))) <=> ufilter(u))”));


val PSS_SS = prove_store("PSS_SS",
e0
(rpt strip_tac >> fs[PSS_def])
(form_goal “!A s1:mem(Pow(A)) s2. PSS(s1,s2) ==> SS(s1,s2)”));

val SS_BIGUNION = prove_store("SS_BIGUNION",
e0
(rw[SS_def,IN_BIGUNION] >> rpt strip_tac >>
 qexists_tac ‘s0’ >> arw[] >> first_x_assum irule >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))) ss s0. IN(s0,ss) & SS(s,s0) ==>
  SS(s,BIGUNION(ss))”));



val UNION_chain_filter_filter = prove_store("UNION_chain_filter_filter",
e0
(rpt strip_tac >> arw[filter_def] >> rpt strip_tac (* 3 *)
 >-- (rw[IN_BIGUNION] >> fs[GSYM IN_NONEMPTY] >>
     qexists_tac ‘a’ >> arw[] >> first_x_assum drule >>
     fs[filter_def])
 >-- (fs[IN_BIGUNION] >>
     qby_tac ‘SS(ss',ss'') | SS(ss'',ss')’ 
     >-- (first_x_assum irule >> arw[]) >>
     pop_assum strip_assume_tac (* 2 *) >--
     (qexists_tac ‘ss''’ >> fs[SS_def] >>
     first_x_assum drule >>
     irule Inter_IN_filter >> arw[] >>
     first_x_assum irule >> arw[]) >>
     qexists_tac ‘ss'’ >> fs[SS_def] >>
     first_x_assum drule >>
     irule Inter_IN_filter >> arw[] >>
     first_x_assum irule >> arw[]) >>
 fs[IN_BIGUNION] >>
 qexists_tac ‘ss'’ >> arw[] >> irule SS_IN_filter >> 
 qby_tac ‘filter(ss')’ 
 >-- (first_x_assum irule >> arw[]) >> arw[] >>
 qexists_tac ‘X’ >> arw[])
(form_goal “!W. ~EMPTY(W) ==>
 !ss. ~(ss = Empty(Pow(Pow(W)))) & 
 (!s:mem(Pow(Pow(W))). IN(s,ss) ==> filter(s)) &
 (!a b. IN(a,ss) & IN(b,ss) ==> SS(a,b) | SS(b,a)) ==>
 filter(BIGUNION(ss))”));


val UNION_chain_pfilter_pfilter = prove_store("UNION_chain_pfilter_pfilter",
e0
(rpt strip_tac >> rw[Empty_NOTIN_pfilter] >> strip_tac (* 2 *)
 >-- (irule UNION_chain_filter_filter >> arw[] >>
     rpt strip_tac >> first_x_assum drule >> fs[pfilter_def]) >>
 qby_tac ‘!s.IN(s,ss) ==> ~(IN(Empty(W),s))’ 
 >-- (rpt strip_tac >> first_x_assum drule >>
     fs[Empty_NOTIN_pfilter]) >>
 rw[IN_BIGUNION] >> ccontra_tac >> pop_assum strip_assume_tac >>
 first_x_assum drule >> fs[])
(form_goal “!W. ~EMPTY(W) ==>
 !ss. ~(ss = Empty(Pow(Pow(W)))) & 
 (!s:mem(Pow(Pow(W))). IN(s,ss) ==> pfilter(s)) &
 (!a b. IN(a,ss) & IN(b,ss) ==> SS(a,b) | SS(b,a)) ==>
 pfilter(BIGUNION(ss))”));

val IMAGE_eq_Empty = prove_store("IMAGE_eq_Empty",
e0
(rw[GSYM IN_EXT_iff,IMAGE_def,Empty_def] >> rpt strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (ccontra_tac >> 
     first_x_assum (qspecl_then [‘App(f,x)’] assume_tac) >>
     qsuff_tac ‘?a. IN(a,s) & App(f,x) = App(f,a)’
     >-- arw[] >> qexists_tac ‘x’>> arw[]) >>
 ccontra_tac >> fs[] >> rfs[])
(form_goal “!A B f:A->B s. IMAGE(f,s) = Empty(B) <=> 
 s = Empty(A)”));

val ufilter_thm = prove_store("ufilter_thm",
e0
(rpt strip_tac >>
 x_choosel_then ["pf","i"] strip_assume_tac
 (Thm_2_4 |> qspecl [‘Pow(Pow(A))’] 
 |> fVar_sInst_th “P(v:mem(Pow(Pow(A))))”
    “pfilter(v:mem(Pow(Pow(A)))) & SS(s,v)”) >>
 qby_tac ‘?r.!s1 s2:mem(pf). Holds(r,s1,s2)<=> SS(App(i,s1),App(i,s2))’
 >-- accept_tac(AX1 |> qspecl [‘pf’,‘pf’]
 |> fVar_sInst_th “P(s1:mem(pf),s2:mem(pf))”
    “SS(App(i:pf->Pow(Pow(A)),s1),App(i,s2))”
|> uex2ex_rule) >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘?m. ismax(r,m)’ >--
 (strip_tac >> fs[ismax_def] >>
 qexists_tac ‘App(i,m)’ >>
 qby_tac ‘pfilter(App(i,m)) & SS(s,App(i,m))’
 >-- (arw[] >> qexists_tac ‘m’ >> rw[]) >>
 arw[] >>
 pop_assum strip_assume_tac >> drule $ GSYM ufilter_iff_maximal >>
 arw[] >> 
 pop_assum (K all_tac) >>
 rpt strip_tac >>
 ccontra_tac >>
 qsuff_tac ‘?x. Holds(r,m,x) & ~(x = m)’
 >-- (strip_tac >> first_x_assum drule >> fs[]) >>
 qby_tac ‘pfilter(s') & SS(s,s')’ 
 >-- (rw[pfilter_def] >> arw[] >> irule SS_Trans >>
     qexists_tac ‘App(i,m)’ >> arw[] >> irule PSS_SS >> arw[]) >>
 qby_tac ‘?s0. s' = App(i,s0)’ >-- (rfs[] >> qexists_tac ‘b’>> rw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘s0’ >> arw[] >> fs[] >>
 drule PSS_SS >> arw[] >>
 ccontra_tac >> fs[PSS_def]) >>
 irule zorns_lemma >>
 qby_tac ‘ptorder(r)’ 
 >-- (rw[ptorder_def,Trans_def,Refl_def,Asym_def] >> rpt strip_tac (* 3 *)
     >-- (rfs[] >> irule SS_Trans >> qexists_tac ‘App(i,a2)’>> arw[]) 
     >-- arw[SS_Refl] >>
     rfs[] >> fs[Inj_def] >> first_x_assum irule >>
     irule SS_SS_eq >> arw[]) >>
 arw[] >>
 rpt strip_tac >>
 qby_tac ‘~EMPTY(A)’ >-- fs[pfilter_def,filter_def] >>
 qby_tac ‘pfilter(BIGUNION(IMAGE(i,c)))’
 >-- (irule UNION_chain_pfilter_pfilter >>
     arw[IMAGE_eq_Empty] >> rpt strip_tac (* 2 *)
     >-- (qsuff_tac ‘pfilter(s') & SS(s,s')’ 
         >-- (strip_tac >> arw[]) >>
         arw[] >> fs[IMAGE_def] >> 
         qexists_tac ‘a’ >> rw[]) >>
     fs[chain_def] >>
     rfs[] >> fs[IMAGE_def] >>
     first_x_assum irule >> arw[]) >>
 qby_tac ‘SS(s,BIGUNION(IMAGE(i,c)))’ 
 >-- (irule SS_BIGUNION >> fs[GSYM IN_NONEMPTY] >>
     qexists_tac ‘App(i,a)’ >> 
     qby_tac ‘?b. App(i,a) = App(i,b)’ >-- (qexists_tac ‘a’ >> rw[]) >>
     first_x_assum (drule o iffRL) >> arw[] >>
     rw[IMAGE_def] >> qexists_tac ‘a’ >> arw[])  >>
 qby_tac ‘?u0. BIGUNION(IMAGE(i, c)) = App(i,u0)’ 
 >-- (first_x_assum (irule o iffLR) >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘u0’ >> arw[ubound_def] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rpt strip_tac >>
 irule SS_BIGUNION >> qexists_tac ‘App(i,y)’ >> rw[SS_Refl] >>
 rw[IMAGE_def] >> qexists_tac ‘y’ >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))). pfilter(s) ==>
 ?u. ufilter(u) & SS(s,u)”));

val ufilter_thm_coro = prove_store("ufilter_thm_coro",
e0
(rpt strip_tac >> drule FIP_PSUBSET_proper_filter >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >> drule ufilter_thm >>
 pop_assum strip_assume_tac >> qexists_tac ‘u’ >> arw[] >>
 irule SS_Trans >> qexists_tac ‘v’ >> arw[])
(form_goal “!A ss:mem(Pow(Pow(A))). FIP(ss) & ~(EMPTY(A)) ==>
 ?u. ufilter(u) & SS(ss,u)”));




val Prop_5_3 = prove_store("Prop_5_3",
e0
(rpt gen_tac >> disch_tac >> drule ufilter_thm_coro >>
 pop_assum strip_assume_tac >> 
 drule $ iffLR from_UFs >> 
 pop_assum strip_assume_tac >>
 qexists_tac ‘b’ >> fs[])
(form_goal “!A ss:mem(Pow(Pow(A))). FIP(ss) & ~(EMPTY(A)) ==>
 ?u:mem(UFs(A)). SS(ss,Repu(u))”));


val FIP_Sing = prove_store("FIP_Sing",
e0
(rw[FIP_def] >> rpt strip_tac >>
 fs[SS_Sing,BIGINTER_Sing])
(form_goal “!W a. ~(a = Empty(W)) ==> FIP(Sing(a)) ”));



val Pr_uex = prove_store("Pr_uex",
e0
cheat
(form_goal “!A B. ?AB p1:AB->A p2:AB ->B. 
 isPr(p1,p2) &
 (!AB' p1':AB'->A p2'. isPr(p1',p2') ==>
  ?!i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
  p1' o i = p1 & p2' o i = p2 &
  p1 o j = p1' & p2 o j = p2')”));

val Pr_ts_ex = proved_th $
e0
cheat
(form_goal “!A B. ?AB p1:AB->A p2:AB ->B. T”)

val Reqv = proved_th $
e0
cheat
(form_goal 
“(!AB p1:AB->A p2:AB->B.
 ?!i:AB->AB j. i o j = Id(AB) & j o i = Id(AB) &
  p1 o i = p1 & p2 o i = p2 &
  p1 o j = p1 & p2 o j = p2) &
 (!AB p1:AB->A p2:AB->B AB' p1':AB'->A p2':AB'->B. 
  (?!i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   p1' o i = p1 & p2' o i = p2 &
   p1 o j = p1' & p2 o j = p2')==>
  (?!i:AB'->AB j. i o j = Id(AB) & j o i = Id(AB') &
   p1 o i = p1' & p2 o i = p2' &
   p1' o j = p1 & p2' o j = p2)) & 
 (!AB p1:AB->A p2:AB->B AB' p1':AB'->A p2':AB'->B
      AB'' p1'':AB''->A p2'':AB''->B. 
  (?!i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   p1' o i = p1 & p2' o i = p2 &
   p1 o j = p1' & p2 o j = p2') &
  (?!i:AB'->AB'' j. i o j = Id(AB'') & j o i = Id(AB') &
   p1'' o i = p1' & p2'' o i = p2' &
   p1' o j = p1'' & p2' o j = p2'') ==>
  (?!i:AB->AB'' j. i o j = Id(AB'') & j o i = Id(AB) &
   p1'' o i = p1 & p2'' o i = p2 &
   p1 o j = p1'' & p2 o j = p2''))
 ”)

val uexth = Pr_uex |> spec_all

val eth = Pr_ts_ex |> spec_all

val eqvth = Reqv

val fnames = ["*","p1","p2"]

val iseqr = “P()”


val arg1 = List.map (dest_var o rastt) 
                    ["AB","p1:AB->A","p2:AB->B"]

val arg2 = List.map (dest_var o rastt) 
                     ["AB'","p1':AB'->A","p2':AB'->B"]

val eqr = 
“?!i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   (p1':AB'->A) o i = p1 & (p2':AB'->B) o i = p2 &
   p1 o j = p1' & p2 o j = p2'”

(*must have arg1 and arg2 as var list, not terms, since they cannot always be represented as a single term. even if they can after certain function symbols exists, but newspec is often the fsyms which are required for capturing these arguments as a single term*)

fun mk_tinst l = mk_inst l [] 

fun addprims l = 
            case l of [] => l
                    | (n,s) :: t =>
                      let val new = (n^"'",s)
                      in
                          new :: 
                          (List.map 
                               (dest_var o 
                                (substt ((n,s),mk_var new)) o mk_var) (addprims t))
                      end
 (*if do arg3 like this, need all non-local constant 
         terms to be given in the input list,
         add all input vars by a "'",
         [AB,p1:AB->A,p2:AB->B] |-> 
         [AB',p1':AB'->A,p2':AB'->B]
         but if
         [A,B,AB,p1,p2], then give:
         [A',B',AB',p1':AB'->A',p2':AB'->B']
*)    
(*should check arg1 and arg2 vars are all distinct*)

val arg = arg1
val Q = “isPr(p1:AB->A,p2:AB->B)”


fun mk_existss nsl f = 
    case nsl of 
        [] => f
      | (h as (n,s)) :: t =>
        mk_exists n s (mk_existss t f)

val vl = List.map dest_var [rastt "A",rastt "B"]

(*
newspec (arg1,arg2,eqr) (arg,Q) fnames vl eth eqvth
uexth
*)


(*
(AB,p1,p2),(AB',p1',p2') -> 
 ?!(i : fun(AB, AB'))  (j : fun(AB', AB)).
     i# o j# = Id(AB') &
     j# o i# = Id(AB) &
     p1' o i# = p1 & p2' o i# = p2 & p1 o j# = p1' & p2 o j# = p2'


ER_def

split the check into several functions

*)

fun mk_tinst l = mk_inst l [] 

fun addprims l = 
            case l of [] => l
                    | (n,s) :: t =>
                      let val new = (n^"'",s)
                      in
                          new :: 
                          (List.map 
                               (dest_var o 
                                (substt ((n,s),mk_var new)) o mk_var) (addprims t))
                      end


fun mk_existss nsl f = 
    case nsl of 
        [] => f
      | (h as (n,s)) :: t =>
        mk_exists n s (mk_existss t f)



fun dest_n_exists n f = 
    if n = 0 then ([],f) else 
    let val (l,b) = dest_n_exists (n-1) f
        val (ns,b1) = dest_exists b
    in (l @ [ns],b1)
    end


fun newspec (arg1:(string * sort) list,
             arg2:(string * sort) list,eqr) 
            (arg:(string * sort) list,Q)
            fnames vl eth eqvth uexth = 
    let 
        (*1.check eqvth states eqr is ER*)
        val argtrefl = List.map mk_var arg1
        val reflbody = 
            inst_form (mk_tinst (zip arg2 argtrefl)) eqr
        val reflcl = mk_foralls arg1 reflbody
        val (symt1,symt2) = (List.map mk_var arg1,
                             List.map mk_var arg2)
        val symconc = 
            inst_form
            (mk_tinst((zip arg1 symt2) @ (zip arg2 symt1)))
            eqr
        val symbody = 
            mk_imp eqr symconc
        val symcl = mk_foralls (arg1 @ arg2) symbody          
        val arg3 = addprims arg2
        val (transt1,transt2,transt3) =
            (List.map mk_var arg1,
             List.map mk_var arg2,
             List.map mk_var arg3)
        val transant2 = 
            inst_form
            (mk_tinst((zip arg1 transt2) @ (zip arg2 transt3)))
            eqr
        val transconc = 
            inst_form
            (mk_tinst((zip arg1 transt1) @ (zip arg2 transt3)))
            eqr
        val transbody = mk_imp (mk_conj eqr transant2)
                               transconc
        val transcl = mk_foralls (arg1 @ arg2 @ arg3)
                                 transbody
        val eqvcls = mk_conj reflcl (mk_conj symcl transcl)
        val _ = eq_form (eqvcls,concl eqvth) orelse
                raise simple_fail "newspec.eqvth concl"
        val _ = HOLset.isSubset(cont eqvth,cont uexth) orelse
                raise simple_fail "newspec.eqvth cont"
        val _ = List.all (fn asm => List.exists
                                        (fn a => eq_form(a,asm)) (ant uexth)) (ant eqvth) orelse
                raise simple_fail "newspec.eqvth ant"
        (*check the uexth*)
        val maint = List.map mk_var arg
        val mainprimv = addprims arg
        val mainprimt = List.map mk_var mainprimv
        val mainprim = inst_form
            (mk_tinst (zip arg mainprimt)) Q
        val relf = 
            inst_form
            (mk_tinst((zip arg1 maint) @ (zip arg2 mainprimt)))
            eqr
        val cj2ofit = mk_foralls mainprimv 
                      (mk_imp mainprim relf)
        val whole = mk_existss arg (mk_conj Q cj2ofit)
        val _ = eq_form(whole,concl uexth) orelse
                raise simple_fail "newspec.uexth concl"
        (*check eth*)
        val _ = HOLset.isSubset(cont eth,cont uexth) orelse
                raise simple_fail "newspec.eth has extra variables"
        val _ = eq_forml (ant eth) [] orelse
                raise simple_fail "newspec.eth has assumptions"
        val _ = eq_form(concl eth, mk_existss arg TRUE)
                orelse 
                raise simple_fail "newspec.ill-formed eth"
        (*check the input contains all necessary ones*)
        val inputvars0 = filter_cont (cont th)
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) 
                           essps vl
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val (newspvs,b) = dest_n_exists (length arg1) (concl uexth)
        val (main,impf) = dest_conj b 
        val recoverex = mk_existss newspvs main
        val sts = List.map snd newspvs
        val (ct,asm) = (cont uexth,ant uexth)
(*List.FOLD!!!!!!!!*)

(*
        fun itmk fnl vl f =
            List.foldl 
            (fn (nfsy,f0) => 
                let val _ = new_fun nfsy (hd sts,vl)
                    val ft = mk_fun nfsy (List.map mk_var vl)
                    val (ns,b) = dest_exists f0
                in substf (ns,ft) b
                end) f fnl  *)
        fun itmk fnl vl f = List.foldl 
            case fnl of 
                [] => (fnl,f)
              | h :: t =>
                let val _ = new_fun (hd fnl) (hd sts,vl)
                    val ft = mk_fun (hd fnl) (List.map mk_var vl)
                    val (ns,b) = dest_exists f
                    val f0 = substf (ns,ft) b
                in itmk (tl fnl) vl f0
                end 
        val (_,conc) = itmk fnames vl recoverex
    in
        mk_thm(ct,asm,conc)
    end

ord(a) ->ord(a)

!o
d:ord(a). ?!od':ord(a). od < od' & !od''. od < od'' ==> od' = od''




AX5 |> qspecl [‘N’] 
|> fVar_sInst_th “P(n:mem(N),X)”
   “nPow(B,n,X)”
*)


(*

Γ, A |- phi

a0:S0 /\ a1:S1 /\ a2:S2 ..../\ Assuptimes ==> phi


!X Y f:X->Y. id(Y) o f = f 

into

∀X Y f. isob(X) & isob(Y) & isar(f,X,Y) ==> (id Y) o f = f


γ1, A1 |- f1   γ2,A2 |- f2
--------------------
γ1 ∪ γ2, A1 @ A2 |- f1 & f2


(a0:S0 /\ a1:S1 /\ a2:S2 ..../\ Assuptimes ==> phi) &
a0:S0 /\ a1:S1 /\ a2:S2 ..../\ Assuptimes ==> phi

--------
a0:S0 /\ a1:S1 /\ a2:S2 ..../\ Assuptimes ==> phi & phi2






*)





(*workflow:
Define function A -> B.

take clause 1, generate subset s1 of A such that !a. IN(a,s1) <=> P1(a).
take clause 2, generate subset s2 of A such that !a. IN(a,s2) <=> P2(a), 
intersect it with complement of s1, get s2'.

!a. IN(a,Union(s1 U s2', Compl(s1 U s2'))) ==>
    





!a. (P1(a) | (~P1(a) & P2(a)) | (~P1(a) & ~P2(a)))

!a. ?!b. (P1(a) & b = t1(a)) | 
         (~P1(a) & P2(a) & b = t2(a)) |
         (~P1(a) & ~P2(a) & b = t3(a))

obtained from turn ant into true from:

!a. IN(a,Union(Union(s1,s2'), Compl(s1 U s2'))) ==> 
    ?!b. (P1(a) & b = t1(a)) | 
         (~P1(a) & P2(a) & b = t2(a)) |
         (~P1(a) & ~P2(a) & b = t3(a))

obtained from pack up def of Union 

!a. IN(a,s1) | IN(a,s2) | IN(a,Compl(s1 U s2')) ==> 
    ?!b. (P1(a) & b = t1(a)) | 
         (~P1(a) & P2(a) & b = t2(a)) |
         (~P1(a) & ~P2(a) & b = t3(a))

obtained from distr of:


!a. (IN(a,s1) ==> ?!b. (P1(a) & b = t1(a)) | 
         (~P1(a) & P2(a) & b = t2(a)) |
         (~P1(a) & ~P2(a) & b = t3(a))) &
    (IN(a,s2') ==>  ?!b. (P1(a) & b = t1(a)) | 
         (~P1(a) & P2(a) & b = t2(a)) |
         (~P1(a) & ~P2(a) & b = t3(a)))) |
    (IN(a,Compl(s1 U s2')) ==> ?!b. (P1(a) & b = t1(a)) | 
         (~P1(a) & P2(a) & b = t2(a)) |
         (~P1(a) & ~P2(a) & b = t3(a))) 

obtained from disjI from

!a. IN(a,s1) ==> ?!b. (P1(a) & b = t1(a))  & 
    IN(a,s2') ==> ?!b. (~P1(a) & P2(b) = t1(a)) & 
    IN(a,Compl(s1 U s2') ==> ?!b. ~P1(a) & ~P2(a) & b = t3(a) )
    



*)


val cond_unique_lemma = proved_th $
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘b’ >> arw[] >> rpt strip_tac >> arw[])
(form_goal “!A B.
  (!a:mem(A). P1(a) ==> ?!b.Q1(a,b)) & 
  (!a. ~P1(a) & P2(a) ==> ?!b. Q2(a,b) )”)




val f = “!a. (P1(a) ==> App(f,a) = (Suc(a))) &
             (~P1(a) & P2(a) ==> App(f,a) = Suc(Suc(a))) &
             (~P1(a) & ~P2(a) ==> App(f,a) = a)”

val f = “!a. (P1(a) ==> App(f,a) = (Suc(a))) &
             (~P1(a) & P2(a) ==> App(f,a) = Suc(Suc(a))) &
             (~P1(a) & ~P2(a) ==> App(f,a) = a)”


(P1(a) | (~P1(a) & P2(a))) | 
~(P1(a) |  (~P1(a) & P2(a)) )

Prove (~P1(a) & ~P2(a) & ... & ~Pn(a) <=>
      ~P1(a) & ~(~P1(a) & P2(a)) & ... P  )

(*
Prove ~P1(a) & ~(~P1(a) & P2(a)) <=> ~P1(a) & ~P2(a)

by rw assuming conjuncts

*)





(*
fun rw_fm_with f = 
    let val th = assume f 
        val tthl = rw_tcanon th
        val fthl = rw_fcanon th
    basic_fconv (rewr_conv (assume f)) (rewr_fconv (assume f))
*)




(*fun djEs fthl = List.foldl (uncurry djE) (List.hd fthl) (rev (List.tl fthl))*)





(*
((P1 | ~P1 & P2) | ~P1 & ~P2 & P3) | ~P1 & ~P2 & ~P3

turned into

(P1 | P2) | (~P1 & )

repeatly assume all disjuncts and turn bigdisjunction into T



*)



val TAUT' = proved_th $
e0
(qcases ‘A(x)’ >> arw[])
(form_goal “A(x:mem(X)) | ~A(x)”)


val disj_neg_absorb' = proved_th $
e0
(dimp_tac >> strip_tac >> qcases ‘A(x)’ >> qcases ‘B(x)’ >> arw[] (* 4 *)
 >> first_x_assum opposite_tac)
(form_goal “(A(x:mem(X)) | (~A(x) & B(x))) <=> A(x) | B(x)”)



val disj_of_negconj' = proved_th $
e0
(dimp_tac >> strip_tac >> arw[] >> strip_tac >>
 qcases ‘A(x)’ >> qcases ‘B(x)’ >> arw[] 
 >-- (qsuff_tac ‘A(x) | B(x)’ >-- arw[] >> disj1_tac >> arw[]) 
 >-- (qsuff_tac ‘A(x) | B(x)’ >-- arw[] >> disj1_tac >> arw[]) 
 >-- (qsuff_tac ‘A(x) | B(x)’ >-- arw[] >> disj1_tac >> arw[]) >>
 (qsuff_tac ‘A(x) | B(x)’ >-- arw[] >> disj2_tac >> arw[]))
(form_goal “(~A(x:mem(X)) & ~B(x)) <=> ~(A(x) | B(x))”)


val CONJ_ASSOC' = proved_th $
e0
(dimp_tac >> strip_tac >> arw[])
(form_goal “(A(x:mem(X)) & B(x)) & C(x) <=> 
           A(x:mem(X)) & B(x) & C(x) ”)



fun define_fun f = 
    let val (inputvar as (n,s),clauses) = dest_forall f
        val inputt = mk_var(n,s)
        val setvar = s |> dest_sort |> #2 |> hd
        val cll = strip_conj clauses
        val conds = List.map iant cll
        val outputs = List.map (#2 o dest_eq o iconc) cll
        val culemma = cond_unique_lemma |> specl [setvar,inputt]
        val fvar0 = mk_fvar "P" [inputt]
        val cases = List.map 
                        (fn (cond,output) =>
                            culemma 
                                |> fVar_sInst_th fvar0 cond
                                |> undisch |> sspecl [output])
                             (zip conds outputs)
        val vconseqs = List.map (dest_uex o concl) cases
        val conseqs = List.map #2 vconseqs
        val djconseq = mk_disjl conseqs 
        val iffs = List.map (fn f => mk_dimp f djconseq) conseqs
        val eqvTs = List.map 
                        (fn (cond,iff) => 
                                         (REWR_FCONV [assume cond])
                                        iff |> rewr_rule[]) 
                        (zip conds iffs)
        val casesunified = List.map 
                               (fn (cl,eqth) =>
                               conv_rule (once_depth_fconv no_fconv (rewr_fconv eqth)) cl) (zip cases eqvTs)
        val todjEs = zip conds casesunified
        val (djf,djEedth0) = djEs todjEs 
        val djEedth = djEedth0 |> disch djf |> rewr_rule[disj_assoc] 
        fun thsfc thl = basic_fconv no_fconv 
                                   (first_fconv (List.map rewr_fconv thl))
        val fc0 = thsfc [GSYM CONJ_ASSOC,disj_of_negconj,
                                      disj_neg_absorb,TAUT]
        val provecond = 
        fun fc0 f0 = 
            let val fth = REWR_FCONV [GSYM CONJ_ASSOC,disj_of_negconj,
                                      disj_neg_absorb',TAUT] f0 

(gen_rewrite_fconv basic_fconv Net.empty fempty [TAUT]) “P(a) | ~P(a)” 
 
basic_fconv no_conv
           (rewrites_fconv (add_frewrites fempty [TAUT']))
“P(a) | ~P(a)” 

basic_fconv no_conv
(fn f => first_fconv (fmatch f (add_frewrites fempty [TAUT'])) f)
“P(a) | ~P(a)” 

List.hd (fmatch “P(a) | ~P(a)” (add_frewrites fempty [TAUT'])) “P(a) | ~P(a)” 

first_fconv (fmatch f (add_frewrites fempty [TAUT])) f
val f = “P(a) | ~P(a)” 

REWR_FCONV [TAUT] “P(a) | ~P(a)” 

(fmatch f (add_frewrites fempty [TAUT]))

basic_fconv no_conv
(first_fconv (List.map rewr_fconv (rw_fcanon TAUT)))
“P(a) | ~P(a)” 


basic_fconv no_conv
(rewr_fconv TAUT)
“P(a) | ~P(a)” 





rewr_fconv (eqT_intro TAUT) “P(a) | ~P(a)” 

basic_fconv no_conv  
REWR_FCONV[ disj_neg_absorb] “(P1 | (~P1 & P2))”

basic_fconv no_fconv (rewr_fconv disj_neg_absorb)
fc0 “(P1(a:mem(N)) | (~P1(a) & P2(a)))”

val f0 = “(P1(a) | (~P1(a) & P2(a))) | (~P1(a) & ~P2(a))”



val f0 = “(P1 | (~P1 & P2)) | (~P1 & ~P2)”

val djs = strip_disj f
                        val (dj1,dj2) = (el 1 djs,el 2 djs) 
                        val dj2' = 

rewr_rule [] (assume “A | ~A”)
(basic_fconv no_conv (rewr_fconv disj_neg_absorb))
                  thenfc ()
        val djf |> basic_fconv no_conv (rewr_fconv disj_neg_absorb)


val f0 = “(((P1 | (~P1 & P2)) | (~P1 & ~P2 & P3)) | (~P1 & ~P2 & ~P3 & P4)) |
         (~P1 & ~P2 & ~P3 & ~P4)”


 [disj_neg_absorb]

basic_fconv no_conv (rewr_fconv disj_neg_absorb) “(P1(a) | ~P1(a) & P2(a))”




val cond = el 2 conds 
val iff = el 2 iffs
basic_fconv no_conv (rewr_fconv (eqT_intro (assume cond))) iff


rewr_fconv (assume cond) “P1(a:mem(N))”

(assume)

        val djequivths = List.map
                             (fn (cond,concl) => djconseq )

 cases |> concl |> dest_exists

 val conseq = 
        val _ = 
        val cjccases = conjIs cases


conjIs cases



        val define_subsets = 
            List.map (fn cond => IN_def_P |> specl [setvar] 
                                          |> fVar_sInst_th fvar0 cond) conds


IN_def_P |> specl [setvar] 
                                 |> fVar_sInst_th fvar0
                                    


“(!a. A1(a) ==> App(f,a) = ... &
 (!a. A2(a) ==> App(f,a) = ... &
 !a.~(A1 | A2 | ... | An (a)) ==> App(f,a) = ...”





(*carve out a subset of A * B ?


*)




fun itmk fnl sts vl f = 
    List.fold
        (fn (fsynfsort as (fsyn,fsort),f) =>
            let val _ = new_fun fsyn fsort)


“(!a. P(a) ==> t = t) ==> ?!f:A->B. !a.”
