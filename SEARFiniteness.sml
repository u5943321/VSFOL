local
val FI_cl = 
 “(xs = Empty(X) ==> IN(xs,FIs)) &
  (!xs0 x. IN(xs0,FIs) & xs = Ins(x,xs0) ==> IN(xs,FIs))”
in
val (FI_incond,x1) = mk_incond FI_cl;
val FIf_ex = mk_fex FI_incond x1;
val FIf_def = mk_fdef "FIf" FIf_ex;
val FIf_monotone = mk_monotone FIf_def;
val FI's_def = mk_prim FIf_def;
val FIs_def = mk_LFP (rastt "FI's(X)");
val FIs_cond = mk_cond FIs_def FI's_def;
val FIs_SS = mk_SS FIs_def FI's_def;
val FI_rules0 = mk_rules FIf_monotone FIs_SS FIs_cond;
val FI_cases0 = mk_cases FIf_monotone FI_rules0 FIs_cond;
val FI_ind0 = mk_ind FIs_cond;
val FI_ind1 = mk_ind1 FIf_def FI_ind0;
val FI_ind2 = mk_ind2 FI_ind1;
val FI_cases1 = mk_case1 FIf_def FI_cases0;
val FI_rules1 = mk_rules1 FIf_def FI_rules0;
val FI_rules2 = mk_rules2 FI_rules1;
val FI_rules3 = mk_rules3 FI_rules2;
end

val FI_ind = FI_ind2 |> store_as "FI_ind";
val FI_cases = FI_cases1 |> store_as "FI_cases";
val FI_rules = FI_rules3 |> store_as "FI_rules";




val Fin_def = qdefine_psym("Fin",[‘A:mem(Pow(X))’]) ‘IN(A,FIs(X))’
                          |> gen_all |> store_as "Fin_def"; 




local
val Cd_cl = 
 “(xsn = Pair(Empty(X),O) ==> IN(xsn,Cds)) &
  (!xsn0 x. IN(xsn0,Cds) & ~(IN(x,Fst(xsn0))) & 
            xsn = Pair(Ins(x,Fst(xsn0)),Suc(Snd(xsn0))) ==> IN(xsn,Cds))”
in
val (Cd_incond,x1) = mk_incond Cd_cl;
val Cdf_ex = mk_fex Cd_incond x1;
val Cdf_def = mk_fdef "Cdf" Cdf_ex;
val Cdf_monotone = mk_monotone Cdf_def;
val Cd's_def = mk_prim Cdf_def;
val Cds_def = mk_LFP (rastt "Cd's(X)");
val Cds_cond = mk_cond Cds_def Cd's_def;
val Cds_SS = mk_SS Cds_def Cd's_def;
val Cd_rules0 = mk_rules Cdf_monotone Cds_SS Cds_cond;
val Cd_cases0 = mk_cases Cdf_monotone Cd_rules0 Cds_cond;
val Cd_ind0 = mk_ind Cds_cond;
val Cd_ind1 = mk_ind1 Cdf_def Cd_ind0;
val Cd_ind2 = mk_ind2 Cd_ind1;
val Cd_cases1 = mk_case1 Cdf_def Cd_cases0;
val Cd_rules1 = mk_rules1 Cdf_def Cd_rules0;
val Cd_rules2 = mk_rules2 Cd_rules1;
val Cd_rules3 = mk_rules3 Cd_rules2;
end

val Cd_ind = Cd_ind2 |> store_as "Cd_ind";
val Cd_cases = Cd_cases1 |> store_as "Cd_cases";
val Cd_rules = Cd_rules3 |> store_as "Cd_rules";



val Cds_ind = prove_store("Cds_ind",
e0
(rpt gen_tac >> disch_tac >>
 qsuff_tac
 ‘!xsn. IN(xsn,Cds(X)) ==> IN(xsn,ss)’
 >-- (fconv_tac (depth_fconv no_conv forall_cross_fconv) >> rw[]) >>
 match_mp_tac Cd_ind (* irule does not work *) >>
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >> 
 rw[Pair_def'] >> arw[]
 )
(form_goal 
 “!X ss.IN(Pair(Empty(X),O),ss) & 
 (!xs0 n0 x. IN(Pair(xs0,n0),ss)  & ~(IN(x,xs0)) ==> 
  IN(Pair(Ins(x,xs0),Suc(n0)),ss)) ==> 
 !xs n. IN(Pair(xs,n),Cds(X)) ==> IN(Pair(xs,n),ss)”));


val Cd_induct0 = prove_store("Cd_induct0",
e0
(strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘Pow(X) * N’]) >>
 arw[Cds_ind])
(form_goal 
 “!X.P(Pair(Empty(X),O)) & 
 (!xs0 n0 x:mem(X). P(Pair(xs0,n0)) & ~(IN(x,xs0)) ==> 
  P(Pair(Ins(x,xs0),Suc(n0)))) ==> 
 !xs n. IN(Pair(xs,n),Cds(X)) ==> P(Pair(xs,n))”));


val Cd_induct = prove_store("Cd_induct",
e0
(strip_tac >> assume_tac (Cd_induct0 |> qspecl [‘X’] 
            |> fVar_sInst_th “P(xsn:mem(Pow(X) * N))”
               “P(Fst(xsn:mem(Pow(X) * N)),Snd(xsn))”
            |> rewr_rule[Pair_def']) >> arw[])
(form_goal 
 “!X.P(Empty(X),O) & 
 (!xs0 n0 x:mem(X). P(xs0,n0) & ~(IN(x,xs0)) ==> 
  P(Ins(x,xs0),Suc(n0))) ==> 
 !xs n. IN(Pair(xs,n),Cds(X)) ==> P(xs,n)”));
 
val Fin_induct = prove_store("Fin_induct",
e0
(rw[Fin_def] >> strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘Pow(X)’]) >>
 arw[FI_ind])
(form_goal 
 “!X.P(Empty(X)) & 
 (!xs0:mem(Pow(X)) x. P(xs0) ==> P(Ins(x,xs0))) ==> 
 !xs:mem(Pow(X)). Fin(xs) ==> P(xs)”));
 

(*Card rel*)
val Cdr_def = qdefine_psym("Cdr",[‘xs:mem(Pow(X))’,‘n:mem(N)’])
‘IN(Pair(xs,n),Cds(X))’ |> qgenl[‘X’,‘xs’,‘n’] 
|> store_as "Cdr_def";

val Cdr_induct = Cd_induct |> rewr_rule[GSYM Cdr_def]
                           |> store_as "Cdr_induct";


val Cdr_Empty = prove_store("Cdr_Empty",
e0
(rw[Cdr_def,Cd_rules])
(form_goal
 “!X.Cdr(Empty(X),O)”));

val Cdr_Ins = Cd_rules |> conjE2 |> spec_all |> undisch |> gen_all |> disch_all
                       |> gen_all
                       |> qspecl [‘X’,‘Pair(xs0:mem(Pow(X)),n:mem(N))’]
                       |> rewr_rule[GSYM Cdr_def,Pair_def']
                       |> gen_all
                       |> store_as "Cdr_Ins";



val Ins_NONEMPTY = prove_store("Ins_NONEMPTY",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,Ins_def,Empty_def] >>
 ccontra_tac >> first_x_assum (qspecl_then [‘x0’] assume_tac) >> fs[])
(form_goal
 “!X x0 xs:mem(Pow(X)).~(Ins(x0,xs) = Empty(X))”));

val IN_Ins_SND = prove_store("IN_Ins_SND",
e0
(rw[Ins_def] >> rpt strip_tac)
(form_goal “!X x0 xs0:mem(Pow(X)) x. IN(x, Ins(x0, xs0)) & (~(x = x0)) ==> IN(x,xs0)”));

val Cdr_Empty_unique = prove_store("Cdr_Empty_unique",
e0
(rw[Cdr_def] >> once_rw[Cd_cases] >> rpt strip_tac >>
 fs[Pair_eq_eq,GSYM Ins_NONEMPTY])
(form_goal
 “!X n.Cdr(Empty(X),n) ==> n = O”));




val Del_Ins_SWAP = prove_store("Del_Ins_SWAP",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,Ins_def,Del_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X x0 x:mem(X).(~(x0 = x)) ==> !xs.Del(Ins(x0, xs), x) = Ins(x0,Del(xs,x))”));


val Cdr_Ins = 
Cd_cases |> qspecl [‘Pair(Ins(x0:mem(X),xs0),n:mem(N))’]
|> rewr_rule[Pair_eq_eq,Ins_NONEMPTY] 
|> conv_rule (basic_fconv no_conv exists_cross_fconv)
|> rewr_rule[Pair_def',GSYM Cdr_def]
|> gen_all |> store_as "Cdr_Ins";

val Cdr_Empty = Cd_rules |> conjE1 |> gen_all |> rewr_rule[GSYM Cdr_def] 
                         |> store_as "Cdr_Empty";


val Cdr_Del = prove_store("Cdr_Del",
e0
(strip_tac >> ind_with (Cdr_induct |> qspecl [‘X’]) >>
 rw[Cdr_Empty,Empty_def] >> rpt strip_tac (* 2 *)
 >-- (irule $ iffRL Cdr_Ins >>
     qexistsl_tac [‘xs0’,‘n0’,‘x’] >> arw[]) >>
 rw[Pre_Suc] >>
 qcases ‘x' = x’ >> fs[] (* 2 *)
 >-- (drule Del_Ins >> arw[]) >>
 qby_tac ‘IN(x',xs0)’ >-- (irule IN_Ins_SND >> qexists_tac ‘x’ >> arw[]) >>
 first_x_assum drule >> 
 qcases ‘n0 = O’ 
 >-- (fs[] >> qsuff_tac ‘xs0 = Empty(X)’ >-- (strip_tac >> fs[Empty_def]) >>
      qpick_x_assum ‘Cdr(xs0, O)’ mp_tac >>
      rw[Cdr_def] >> once_rw[Cd_cases] >> rw[Pair_eq_eq,GSYM Suc_NONZERO] >>
      rpt strip_tac) >>
 fs[O_xor_Suc] >> fs[Pre_Suc] >> 
 qby_tac ‘Del(Ins(x, xs0), x') = Ins(x, Del(xs0,x'))’
 >-- (irule Del_Ins_SWAP >> ccontra_tac >> fs[]) >>
 arw[] >> irule $ iffRL Cdr_Ins >> 
 qexistsl_tac [‘Del(xs0, x')’,‘pn’,‘x’] >> arw[Del_def])
(form_goal
 “!X xs:mem(Pow(X)) n.Cdr(xs,n) ==> 
  Cdr(xs,n) & !x. IN(x,xs) ==> Cdr(Del(xs,x),Pre(n))”));


val Fin_Card = prove_store("Card_Fun",
e0
(strip_tac >> ind_with (Fin_induct |> qspecl [‘X’]) >> rpt strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘O’ >> rw[Cdr_Empty,Cdr_Empty_unique]) >>
 pop_assum (strip_assume_tac o uex_expand) >> uex_tac >>
 qcases ‘IN(x,xs0)’ 
 >-- (drule Ins_absorb >> arw[] >> qexists_tac ‘n’ >> arw[]) >>
 qexists_tac ‘Suc(n)’ >> rpt strip_tac (* 2 *)
 >-- (irule $ iffRL Cdr_Ins >> qexistsl_tac [‘xs0’,‘n’,‘x’] >> arw[]) >>
 drule Cdr_Del >> fs[] >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 fs[Ins_def] >> drule Del_Ins >> fs[] >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >> arw[] >>
 qsuff_tac ‘~(n' = O)’ >-- (rw[O_xor_Suc] >> strip_tac >> arw[Pre_Suc]) >>
 rw[O_xor_Suc] >> qpick_x_assum ‘Cdr(Ins(x, xs0), n')’ mp_tac >>
 strip_tac >> drule $ iffLR Cdr_Ins >> pop_assum strip_assume_tac >>
 qexists_tac ‘b’ >> arw[])
(form_goal
 “!X xs:mem(Pow(X)).Fin(xs) ==> ?!n.Cdr(xs,n)”));

val CARD_def = 
    AX1 |> qspecl [‘Pow(X)’,‘N’] 
        |> fVar_sInst_th “P(xs:mem(Pow(X)), n:mem(N))”
           “(Fin(xs:mem(Pow(X))) & Cdr(xs,n)) | (~Fin(xs) & n = O)”
        |> uex2ex_rule
        |> qSKOLEM "CARD" [‘X’]
        |> gen_all |> store_as "CARD_def";

val CARD_unique = proved_th $
e0
(rpt strip_tac >> rw[CARD_def] >> 
 qcases ‘Fin(xs)’ 
 >-- (drule Fin_Card >> pop_assum (strip_assume_tac o uex_expand) >>
      uex_tac >> qexists_tac ‘n’ >> arw[]) >>
 uex_tac >> qexists_tac ‘O’ >> arw[])
(form_goal “!X xs:mem(Pow(X)). ?!n. Holds(CARD(X),xs,n)”)
 
 
val Cd0_def = P2fun |> qspecl [‘Pow(X)’,‘N’] 
                 |> fVar_sInst_th “P(x:mem(Pow(X)),y:mem(N))”
                    “Holds(CARD(X),x,y)” 
                 |> C mp (CARD_unique |> qspecl [‘X’]) 
                 |> qSKOLEM "Cd0" [‘X’] |> gen_all |> store_as "Cd0_def";


val Card_def = qdefine_fsym ("Card",[‘xs:mem(Pow(X))’])
                            ‘App(Cd0(X),xs)’
                            |> gen_all |> store_as "Card_def";

val Del_Empty = prove_store("Del_Empty",
e0
(rw[GSYM IN_EXT_iff,Del_def,Empty_def])
(form_goal
 “!X x. Del(Empty(X),x) = Empty(X)”));

val Ins_eq_eq = prove_store("Ins_eq_eq",
e0
(rpt strip_tac >-- (ccontra_tac >>
 qsuff_tac ‘~(IN(a2,Ins(a2,s2)))’
 >-- rw[Ins_def] >>
 qsuff_tac ‘~(IN(a2,Ins(a1,s1)))’
 >-- arw[] >>
 arw[Ins_def] >> flip_tac >> first_x_assum accept_tac) >>
 irule IN_EXT >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘IN(x,Ins(a1,s1))’ >-- arw[Ins_def] >> rfs[] >>
      fs[Ins_def] >> pop_assum (assume_tac o GSYM) >> fs[]) >>
 qpick_x_assum ‘Ins(a1, s1) = Ins(a2, s2)’ (assume_tac o GSYM) >>
 qby_tac ‘IN(x,Ins(a2,s2))’ >-- arw[Ins_def] >>
 rfs[] >> fs[Ins_def] >> pop_assum (assume_tac o GSYM) >> fs[])
(form_goal
 “!A a1:mem(A) s1 a2 s2. ~(IN(a1,s1)) & ~(IN(a2,s2)) & ~(IN(a1,s2)) & ~(IN(a2,s1)) & 
 Ins(a1,s1) = Ins(a2,s2) ==> a1 = a2 & s1 = s2”));

val Fin_Empty = FI_rules |> conjE1 |> rewr_rule[GSYM Fin_def] 
                         |> gen_all |> store_as "Fin_Empty";

val Fin_Ins = FI_rules |> conjE2 |> rewr_rule[GSYM Fin_def]
                       |> spec_all |> undisch |> gen_all |> disch_all 
                       |> gen_all |> store_as "Fin_Ins";


val Fin_Ins_Ins = prove_store("Fin_Ins_Ins",
e0
(rpt strip_tac >> irule Fin_Ins >> irule Fin_Ins >>
 rw[Fin_Empty])
(form_goal “!A a1 a2.Fin(Ins(a1,Ins(a2,Empty(A))))”));



val Fin_Del0 = prove_store("Fin_Del",
e0
(strip_tac >> ind_with (Fin_induct |> qspecl [‘X’]) >> 
 rw[Fin_Empty,Del_Empty] >> rpt strip_tac (* 2 *)
 >-- (drule Fin_Ins >> arw[]) >>
 qcases ‘x = x'’ (* 2 *)
 >-- (arw[] >> qcases ‘IN(x',xs0)’ (* 2 *)
     >-- (drule Ins_absorb >> arw[]) >>
     drule Del_Ins >> arw[]) >>
 drule Del_Ins_SWAP >> arw[] >>
 irule Fin_Ins >> arw[])
(form_goal
 “!X xs:mem(Pow(X)).Fin(xs) ==> Fin(xs) &  !x. Fin(Del(xs,x)) ”));

val Fin_Del = prove_store("Fin_Del",
e0
(rpt strip_tac >> drule Fin_Del0 >> arw[])
(form_goal “!X xs:mem(Pow(X)).Fin(xs) ==> !x. Fin(Del(xs,x))”));

val Card_Fin = prove_store("Card_Fin",
e0
(rpt strip_tac >> arw[Card_def,Cd0_def,CARD_def])
(form_goal
 “!X xs:mem(Pow(X)). Fin(xs) ==>
  (!n. Card(xs) = n <=> Cdr(xs,n))”));


val Card_Empty = prove_store("Card_Empty",
e0
(strip_tac >> qspecl_then [‘X’] assume_tac Fin_Empty >>
 drule Card_Fin >> arw[Cdr_Empty])
(form_goal
 “!X. Card(Empty(X)) = O”));


val Cdr_Card = prove_store("Cdr_Card",
e0
(rpt strip_tac >> drule Card_Fin >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal “!X xs:mem(Pow(X)). Fin(xs) ==> 
 Cdr(xs, Card(xs))”));


val Card_Ins = prove_store("Card_Ins",
e0
(rpt strip_tac >> drule Fin_Ins >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Card_Fin >> arw[] >> irule $ iffRL Cdr_Ins >>
 qexistsl_tac [‘xs’,‘Card(xs)’,‘x’] >> arw[] >>
 (* Cdr(xs, Card(xs))*)
 rw[Card_def] >> 
 qsspecl_then [‘xs’,‘App(Cd0(X), xs)’] assume_tac Cd0_def >>
 fs[] >> fs[CARD_def])
(form_goal
 “!X xs:mem(Pow(X)). 
  Fin(xs) ==> !x.~(IN(x,xs)) ==> Card(Ins(x,xs)) = Suc(Card(xs))”));



val Card_Del = prove_store("Card_Del",
e0
(rpt strip_tac >> drule Fin_Del >> 
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Card_Fin >> arw[] >>
 irule (Cdr_Del |> spec_all |> undisch |> conjE2 |> disch_all |> gen_all) >>
 arw[] >> irule Cdr_Card >> arw[])
(form_goal
 “!X xs:mem(Pow(X)). Fin(xs) ==> 
  !x. IN(x,xs) ==> Card(Del(xs,x)) = Pre(Card(xs))”));
 

val IMAGE_FINITE = prove_store("IMAGE_FINITE",
e0
(cheat)
(form_goal “!A s:mem(Pow(A)).Fin(s) ==> !B f:A->B.Fin(IMAGE(f,s))”));
 
val IN_App_IMAGE = prove_store("IN_App_IMAGE",
e0
(rw[IMAGE_def] >> rpt strip_tac >> qexists_tac ‘a’ >> arw[])
(form_goal “!A a s. IN(a,s) ==> !B f:A->B. IN(App(f,a),IMAGE(f,s))”));



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

 


val Ins_Ins_Fin = prove_store("Ins_Ins_Fin",
e0
(qspecl_then [‘A’] assume_tac Fin_Empty >>
 drule Fin_Ins >>
 first_x_assum (qspecl_then [‘s2’] assume_tac) >>
 drule Fin_Ins >> arw[])
(form_goal “Fin(Ins(s1, Ins(s2, Empty(A))))”));



val Fin_Sing = prove_store("Fin_Sing",
e0
(rw[Sing_Ins_Empty] >> rpt strip_tac >> irule Fin_Ins >>
rw[Fin_Empty])
(form_goal “!A a:mem(A).Fin(Sing(a))”));

