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

val IN_Sing = prove_store("IN_Sing",
e0
(rw[Sing_def,Sg_def])
(form_goal “!A a0 a:mem(A). IN(a,Sing(a0)) <=> a = a0”));

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
(cheat)
(form_goal “!A a:mem(A) s. SS(s,Ins(a,s))”));

val BIGINTER_Sing = prove_store("BIGINTER_Sing",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,IN_Sing] >> 
 rw[IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal “!A s:mem(Pow(A)). BIGINTER(Sing(s)) = s”));

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
 cheat (*need Fin_Ins_Ins*) )
(form_goal
 “!W A:mem(Pow(Pow(W))).
  (!a1. IN(a1,A) ==> !a2.IN(a2,A) ==> IN(Inter(a1,a2),A)) <=> 
  (!s. SS(s,A) & Fin(s) & ~(s = Empty(Pow(W))) ==> IN(BIGINTER(s),A))”));

val IN_Union = prove_store("IN_Union",
e0
(rw[Union_def,UNION_def])
(form_goal “!A s1 s2 a:mem(A). IN(a,Union(s1,s2)) <=> IN(a,s1) | IN(a,s2)”));

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
(form_goal “!W A B:mem(Pow(Pow(W))) s. SS(s,Union(A,B)) <=>
  ?s1 s2. SS(s1,A) & SS(s2,B) & s = Union(s1,s2) ”));

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

val Inter_Empty = prove_store("Inter_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Empty_def])
(form_goal “!A s. Inter(s,Empty(A)) = Empty(A)”));



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

val Whole_Inter = prove_store("Whole_Inter",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Whole_def])
(form_goal “!A s.Inter(Whole(A),s) = s”));


val Inter_Whole = prove_store("Inter_Whole",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Whole_def])
(form_goal “!A s.Inter(s,Whole(A)) = s”));

val Fin_SS = prove_store("Fin_SS",
e0
(cheat)
(form_goal “!A s:mem(Pow(A)). Fin(s) ==> !t. SS(t,s) ==> Fin(t) ”));

val Fin_Union = prove_store("Fin_Union",
e0
cheat
(form_goal “!A s1:mem(Pow(A)) s2.Fin(Union(s1,s2)) <=> Fin(s1) & Fin(s2)”));

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
 rw[FIP_def] >> strip_tac >> rw[SS_Union] >>
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
(cheat)
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
(cheat)
(form_goal
 “!s. ?!gf. !x. IN(x,gf) <=>
 ( x = Whole(A) | ?ss. SS(ss,s) & Fin(ss) & ~(ss = Empty(Pow(A))) & SS(BIGINTER(ss),x))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "gfilter1" [‘s’]


val Inter_Whole_Whole = prove_store("Inter_Whole_Whole",
e0
cheat
(form_goal “!A s1:mem(Pow(A)) s2. Inter(s1,s2) = Whole(A) <=> s1 = Whole(A) & s2 = Whole(A)”));

val SS_Union1 = prove_store("SS_Union1",
e0
(cheat)
(form_goal “!A s1 s2 s:mem(Pow(A)). SS(Union(s1,s2),s) <=>
 SS(s1,s) & SS(s2,s)”));


val Union_Empty = Union_EMPTY

val SS_Inter = prove_store("SS_Inter",
e0
cheat
(form_goal “!A s1 s2:mem(Pow(A)) s. SS(s,Inter(s1,s2)) <=>
 SS(s,s1) & SS(s,s2)”));
 
val Inter_SS = prove_store("Inter_SS",
e0
(cheat)
(form_goal “!A s1 s2:mem(Pow(A)). SS(Inter(s1,s2),s1) & SS(Inter(s1,s2),s2)”));

val Whole_SS = prove_store("Whole_SS",
e0
cheat
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
     arw[SS_Union1,Fin_Union,Union_Empty,BIGINTER_Union,SS_Inter] >>
     strip_tac >> irule SS_Trans (* 2 *)
     >-- (qexists_tac ‘BIGINTER(ss)’ >> arw[Inter_SS]) >>
     qexists_tac ‘BIGINTER(ss')’ >> arw[Inter_SS]) >>
 fs[gfilter1_def] (* 2 *)
 >-- (disj1_tac >> irule Whole_SS >> rfs[]) >>
 disj2_tac >> qexists_tac ‘ss’ >> arw[] >>
 irule SS_Trans >> qexists_tac ‘X’ >> arw[])
(form_goal “!A.~(EMPTY(A)) ==>  !s:mem(Pow(Pow(A))). filter(gfilter1(s))”));


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
(cheat)
(form_goal “!A s.pfilter(s) <=> filter(s) & ~IN(Empty(A),s)”));

val EMPTY_Empty_Whole = prove_store("EMPTY_Empty_Whole",
e0
cheat
(form_goal “!A. EMPTY(A) <=> Empty(A) = Whole(A)”));

val SS_Empty = prove_store("SS_Empty",
e0
cheat
(form_goal “!A s. SS(s,Empty(A)) <=> s = Empty(A)”));

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

val ufilter_thm = prove_store("ufilter_thm",
e0
cheat
(form_goal “!A s:mem(Pow(Pow(A))). pfilter(s) ==>
 ?u. ufilter(u) & SS(s,u)”));

(*
val zorns_lemma = prove_store("zorns_lemma",
cheat
(form_goal “!r s. ”)
`!r s. (s <> {}) /\ partial_order r s /\
  (!t. chain t r ==> upper_bounds t r <> {})
  ==>
  (?x. x IN maximal_elements s r)`,
*)

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
cheat
(form_goal “!A ss:mem(Pow(Pow(A))). FIP(ss) & ~(EMPTY(A)) ==>
 ?u:mem(UFs(A)). SS(ss,Repu(u))”));

