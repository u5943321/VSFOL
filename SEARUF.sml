(*facts about ultrafilters*)


val INTER_def = proved_th $ 
e0
cheat
(form_goal “!A. ?f:Pow(A) * Pow(A) -> Pow(A).
 !s1 s2 a. IN(a,App(f,Pair(s1,s2))) <=> IN(a,s1) & IN(a,s2)”)
|> spec_all |> qSKOLEM "INTER" [‘A’]

val Inter_def = qdefine_fsym("Inter",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘App(INTER(A),Pair(s1,s2))’



val UNION_def = proved_th $ 
e0
cheat
(form_goal “!A. ?f:Pow(A) * Pow(A) -> Pow(A).
 !s1 s2 a. IN(a,App(f,Pair(s1,s2))) <=> IN(a,s1) | IN(a,s2)”)
|> spec_all |> qSKOLEM "UNION" [‘A’]

val IN_Inter = prove_store("IN_Inter",
e0
cheat
(form_goal “!A s1 s2 a. IN(a:mem(A),Inter(s1,s2)) <=> IN(a,s1) & IN(a,s2)”));

val EMPTY_def = qdefine_psym("EMPTY",[‘A’])
‘!x:mem(A).F’

val COMPL_def = proved_th $ 
e0
cheat
(form_goal “!A. ?f:Pow(A) -> Pow(A).
 !s a. IN(a,App(f,s)) <=> ~IN(a,s)”)
|> spec_all |> qSKOLEM "COMPL" [‘A’]

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
                              |> conjE2
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
                                 |> conj


val Empty_NOTIN_UF = prove_store("Empty_NOTIN_UF",
e0
(rpt strip_tac >> )
(form_goal “!J L.ufilter(L) ==> ~IN(Empty(J),L)”));


val Empty_NOTIN_UFs = prove_store("Empty_NOTIN_UFs",
e0
cheat
(form_goal “!J u.~IN(Empty(J),Repu(u))”));


val UFs_def = Thm_2_4 |> qspecl [‘Pow(Pow(J))’]
                      |> fVar_sInst_th “P(a:mem(Pow(Pow(J))))”
                      “ufilter(a:mem(Pow(Pow(J))))”
                      |> qSKOLEM "UFs" [‘J’]
                      |> qSKOLEM "iUF" [‘J’] 

val Repu_def = qdefine_fsym("Repu",[‘u:mem(UFs(J))’])
‘App(iUF(J),u)’

val Repu_ufilter = prove_store("Repu_ufilter",
e0
(rw[UFs_def,Repu_def] >> rpt strip_tac >> qexists_tac ‘u’ >> rw[])
(form_goal “!A u:mem(UFs(A)). ufilter(Repu(u))”));
 
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
val SS_Union2 = SS_Union |> conjE2
;
 
val Union_Repu = prove_store("Union_Repu",
e0
(dimp_tac >> strip_tac (* 3 *)
 >-- (ccontra_tac >> fs[neg_or_distr] >>
     fs[GSYM Compl_Repu] >> 
     qby_tac ‘IN(Inter(Compl(s1),Compl(s2)),Repu(u))’
     >-- (irule Inter_IN_ufilter >> arw[Repu_ufilter]) >>
     fs[Inter_Compl_Compl] >>
     fs[Compl_Repu]) 
 >-- 
     )
(form_goal “IN(Union(s1:mem(Pow(J)),s2), Repu(u)) <=> (IN(s1,Repu(u)) | IN(s2,Repu(u)))”));


val FIP_def = qdefine_psym("FIP",[‘ss:mem(Pow(Pow(A)))’])
‘!ss0. SS(ss0,ss) & Fin(ss0) & ~(ss0 = Empty(Pow(A))) ==> ~(BIGINTER(ss0) = Empty(A))’


val FIP_closed_under_Inter = prove_store("FIP_closed_under_Inter",
e0
cheat
(form_goal
 “!W A B. 
  (!a1. IN(a1,A) ==> !a2.IN(a2,A) ==> IN(Inter(a1,a2),A)) &
  (!b1. IN(b1,B) ==> !b2.IN(b2,B) ==> IN(Inter(b1,b2),B)) & 
  (!a. IN(a,A) ==> !b. IN(b,B) ==> ~(Inter(a,b) = Empty(W))) ==>
  FIP(Union(A,B))
 ”));



val FIP_iff_two = prove_store("FIP_iff_two",
e0
(rpt strip_tac >> 
 dimp_tac >> strip_tac >> fs[FIP_def] 
 >-- (rpt strip_tac >> 
     first_x_assum (qsspecl_then [‘Union(Sing(s1),Sing(s2))’] assume_tac) >>
     cheat) >>
 qsuff_tac
 ‘!ss0. Fin(ss0) ==> SS(ss0,ss) & ~(ss0 = Empty(Pow(A))) ==>
        ~(BIGINTER(ss0) = Empty(A))’
 >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
 ind_with (Fin_induct |> qspecl [‘Pow(A)’]) >>
 cheat)
(form_goal “!ss. FIP(ss) <=> 
 !s1. IN(s1,ss) ==> !s2.IN(s2,ss) ==> ~(Inter(s1,s2) = Empty(A))”));


val closed_under_inter_two = prove_store("FIP_iff_two",
e0
(cheat)
(form_goal “!ss:mem(Pow(Pow(A))). (!ss0.SS(ss0,ss) & Fin(ss0) ==> IN(BIGINTER(ss0),ss)) <=> 
 !s1. IN(s1,ss) ==> !s2.IN(s2,ss) ==> IN(Inter(s1,s2),ss)”));





val Prop_5_3 = prove_store("Prop_5_3",
e0
cheat
(form_goal “!A ss:mem(Pow(Pow(A))). FIP(ss) & ~(EMPTY(A)) ==>
 ?u:mem(UFs(A)). SS(ss,Repu(u))”));

