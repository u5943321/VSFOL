
val Ins_def = IN_def_P |> qspecl [‘X’]
                       |> fVar_sInst_th “P(x:mem(X))”
                       “x:mem(X) = x0 | IN(x,s0)”
                       |> uex2ex_rule
                       |> qSKOLEM "Ins" [‘x0’,‘s0’]
                       |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
                       |> store_as "Ins_def";


val Empty_def = IN_def_P |> qspecl [‘X’]
                         |> fVar_sInst_th “P(x:mem(X))” “F”
                         |> uex2ex_rule
                         |> qSKOLEM "Empty" [‘X’]
                         |> rewr_rule[]
                         |> gen_all |> store_as "Empty_def";


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





val Del_def = IN_def_P |> qspecl [‘X’]
                       |> fVar_sInst_th “P(x:mem(X))”
                          “IN(x,s0) & (~(x:mem(X) = x0))” 
                       |> uex2ex_rule
                       |> qSKOLEM "Del" [‘s0’,‘x0’]
                       |> qgen ‘x0’ |> qgen ‘s0’ |> qgen ‘X’
                       |> store_as "Del_def";

val Del_Ins = prove_store("Del_Ins",
e0
(rpt strip_tac >> irule IN_EXT >> 
 arw[Ins_def,Del_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >> ccontra_tac >> fs[])
(form_goal “!X x0:mem(X) xs0. (~IN(x0,xs0)) ==> Del(Ins(x0,xs0),x0) =xs0”));




val Ins_absorb = prove_store("Ins_absorb",
e0
(rpt strip_tac >> irule IN_EXT >> rw[Ins_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal “!X x0:mem(X) xs0. IN(x0,xs0) ==> Ins(x0,xs0) =xs0”));


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

(*Card rel*)
val Cdr_def = qdefine_psym("Cdr",[‘xs:mem(Pow(X))’,‘n:mem(N)’])
‘IN(Pair(xs,n),Cds(X))’ |> qgenl[‘X’,‘xs’,‘n’] 
|> store_as "Cdr_def";


val Cdr_Empty = prove_store("Cdr_Empty",
e0
(rw[Cdr_def,Cd_rules])
(form_goal
 “!X.Cdr(Empty(X),O)”));

val hasCard_Ins = prove_store("hasCard_Ins",
e0
(rw[Card_def'] >> rpt strip_tac >>
 first_assum irule >> arw[] >> first_assum irule >> arw[])
(form_goal
 “!X xs:mem(Pow(X)) n.hasCard(xs,n) ==>
  !x0. (~(IN(x0,xs))) ==> hasCard(Ins(x0,xs),Suc(n))”));




val Ins_NONEMPTY = prove_store("Ins_NONEMPTY",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac
 ‘!x. IN(x,Ins(x0,xs)) <=> IN(x,Empty(X))’ >-- arw[] >>
 fs[Empty_property,GSYM Ins_property] >>
 first_x_assum (qspecl_then [‘x0’] assume_tac) >> fs[])
(form_goal
 “!X x0 xs:mem(Pow(X)).~(Ins(x0,xs) = Empty(X))”));

val IN_Ins_SND = prove_store("IN_Ins_SND",
e0
(rw[GSYM Ins_property] >> rpt strip_tac)
(form_goal “!X x0 xs0:mem(Pow(X)) x. IN(x, Ins(x0, xs0)) & (~(x = x0)) ==> IN(x,xs0)”));

local
val l = 
fVar_Inst 
[("P",([("xsns",mem_sort $ Cross (Pow $ mk_set "X") N)],
“hasCard(Fst(xsns),Snd(xsns)) & 
 ~(Fst(xsns) = Empty(X) & Snd(xsns) = n)”))] 
(IN_def_P_expand |> qspecl [‘(Pow(X) * N)’])
in 
val Card_Empty_unique = prove_store("Card_Empty_unique",
e0
(rpt strip_tac >> ccontra_tac >>
 qsuff_tac
 ‘?ss. IN(Pair(Empty(X),O),ss) &
  (!xs n. IN(Pair(xs,n),ss) ==>
   !x0. (~IN(x0,xs)) ==> IN(Pair(Ins(x0,xs),Suc(n)),ss)) &
  ~(IN(Pair(Empty(X),n),ss))’
 >-- (fs[Card_def'] >>
     ccontra_tac >> pop_assum strip_assume_tac >>
     qsuff_tac ‘IN(Pair(Empty(X), n), ss)’ >-- arw[] >>
     first_assum irule >> arw[]) >>
 strip_assume_tac l >> pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> qexists_tac ‘s’ >>
 once_arw[] >>
 rw[Pair_def'] >> rw[hasCard_Empty] >> strip_tac 
 >-- (flip_tac >> first_assum accept_tac) >>
 strip_tac >> strip_tac >>  (*do not know why does not work if not strip,
 maybe know, how to fix?
*)
 arw[] >>
 rw[Pair_def'] >> rpt strip_tac >--
 (irule hasCard_Ins >> arw[]) >> 
 qsuff_tac
 ‘~(Ins(x0,xs) = Empty(X))’ >-- (strip_tac >> arw[]) >>
 rw[Ins_NONEMPTY]
 )
(form_goal
 “!X n.hasCard(Empty(X),n) ==> n = O”));
end


val hasCard_ind = prove_store("hasCard_ind",
e0
(once_rw[Card_def'] >> rpt strip_tac >>
 first_assum irule >> arw[])
(form_goal
“!X ss. IN(Pair(Empty(X),O),ss) & 
      (!xs n. IN(Pair(xs,n),ss) ==>
       !x0. (~IN(x0,xs)) ==> IN(Pair(Ins(x0,xs),Suc(n)),ss)) ==>
      !xs n.hasCard(xs,n) ==> IN(Pair(xs,n),ss) ”));

val Del_Ins_SWAP = prove_store("Del_Ins_SWAP",
e0
(rpt strip_tac >> irule IN_EXT >> rw[GSYM Ins_property,GSYM Del_property] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X x0 x:mem(X).(~(x0 = x)) ==> !xs.Del(Ins(x0, xs), x) = Ins(x0,Del(xs,x))”));




local
val l = 
fVar_Inst 
[("P",([("xsns",mem_sort $ Cross (Pow $ mk_set "X") N)],
“hasCard(Fst(xsns),Snd(xsns)) & !x0:mem(X) xs0. Fst(xsns) = Ins(x0,xs0) ==> ?n0. Snd(xsns) = Suc(n0)”))] 
(IN_def_P_expand |> qspecl [‘(Pow(X) * N)’])
in
val hasCard_Ins_Suc = prove_store("hasCard_Ins_Suc",
e0
(strip_tac >> strip_assume_tac l >> pop_assum (K all_tac) >>
 qsuff_tac ‘!xs n.hasCard(xs,n) ==> IN(Pair(xs,n),s)’ 
 >-- (pop_assum (assume_tac o GSYM) >> arw[Pair_def']) >>
 strip_tac >> strip_tac >> match_mp_tac hasCard_ind >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rw[Pair_def'] >> 
 rw[hasCard_Empty] >> rpt strip_tac (* 3 *)
 >-- (qby_tac ‘IN(x0,Ins(x0,xs0))’ >-- fs[GSYM Ins_property] >>
     qpick_x_assum ‘Empty(X) = Ins(x0, xs0)’ (assume_tac o GSYM) >>
     fs[Empty_property]) 
 >-- (drule hasCard_Ins >> first_assum drule >> arw[]) >>
 qexists_tac ‘n'’ >> rw[])
(form_goal
 “!X xs:mem(Pow(X)) n. hasCard(xs,n) ==> hasCard(xs,n) & !x0 xs0. xs = Ins(x0,xs0) ==> ?n0. n = Suc(n0)”));
end

local
val l = 
fVar_Inst 
[("P",([("xsns",mem_sort $ Cross (Pow $ mk_set "X") N)],
“hasCard(Fst(xsns),Snd(xsns)) & !x. IN(x:mem(X),Fst(xsns)) ==> hasCard(Del(Fst(xsns),x),Pre(Snd(xsns)))”))] 
(IN_def_P_expand |> qspecl [‘(Pow(X) * N)’])
in
val hasCard_Del = prove_store("hasCard_Del",
e0
(strip_tac >> strip_assume_tac l >> pop_assum (K all_tac) >>
 qsuff_tac ‘!xs n.hasCard(xs,n) ==> IN(Pair(xs,n),s)’  >--
 (rpt strip_tac >> first_x_assum drule >> 
  first_x_assum (qspecl_then [‘Pair(xs,n)’] assume_tac) >> 
  pop_assum (assume_tac o GSYM) >> fs[] >> fs[Pair_def'] >> first_x_assum drule >>
  arw[]) >>
 strip_tac >> strip_tac >>
 match_mp_tac hasCard_ind >> (*
 qby_tac 
 ‘!xs n. (!x.IN(x,xs) ==> hasCard(Del(xs,x),Pre(n))) <=> IN(Pair(xs,n),s)’
 >-- (rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[Pair_def']) >>*)
 pop_assum (assume_tac o GSYM) >> arw[] >> rpt strip_tac (* 2 *)
 >-- fs[Pair_def',hasCard_Empty] >-- fs[Empty_property,Pair_def'] >--
 (fs[Pair_def'] >> drule hasCard_Ins >> first_x_assum drule >> arw[]) >>
 fs[Pair_def'] >>
 cases_on “x:mem(X) = x0” >--
 (fs[] >> drule Del_Ins >> arw[Pre_Suc]) >> 
 qby_tac ‘IN(x,xs')’ >-- (irule IN_Ins_SND >> qexists_tac ‘x0’ >> arw[]) >>
 first_x_assum drule >>  
 qpick_x_assum ‘~(x = x0)’ (assume_tac o GSYM) >>
 drule Del_Ins_SWAP >> arw[] >> drule hasCard_Ins >> 
 qby_tac ‘~(IN(x0,Del(xs',x)))’ >--
 (rw[GSYM Del_property] >> arw[]) >>
 first_x_assum drule >> rw[Pre_Suc] >>
 cases_on “n' = O”
 >-- (fs[] >>
     drule Ins_absorb >>
     qby_tac ‘hasCard(Ins(x, xs'), O)’ >-- arw[] >>
     drule hasCard_Ins_Suc >> pop_assum strip_assume_tac >>
     first_x_assum (qspecl_then [‘x’,‘xs'’] assume_tac) >> fs[GSYM Suc_NONZERO])>>
 fs[O_xor_Suc] >> fs[] >>
 fs[Pre_Suc])
(form_goal
 “!X xs:mem(Pow(X)) n.hasCard(xs,n) ==> hasCard(xs,n) & 
  !x. IN(x,xs) ==> hasCard(Del(xs,x),Pre(n))”));
end







val Fin_Card = prove_store("Card_Fun",
e0
(rw[Fun_expand,Card_lemma] >> strip_tac >> match_mp_tac Fin_ind_card >>
 strip_tac >--
 (uex_tac >> qexists_tac ‘O’ >> rw[hasCard_Empty] >> rpt strip_tac >> drule Card_Empty_unique >> arw[]) >>
 rpt strip_tac >> pop_assum (strip_assume_tac o uex_expand) >> uex_tac >>
 cases_on “IN(x0,xs0:mem(Pow(X)))” 
 >-- (qexists_tac ‘n’ >> 
     qby_tac ‘Ins(x0,xs0) = xs0’ 
     >-- (irule Ins_absorb >> arw[]) >> arw[]) >>    
 qexists_tac ‘Suc(n)’ >> drule hasCard_Ins >> first_x_assum drule >> arw[] >>
 rpt strip_tac >> 
 drule hasCard_Del >>
 fs[] >>
 qby_tac ‘IN(x0, Ins(x0, xs0))’ >-- fs[GSYM Ins_property] >>
 first_x_assum drule >> drule Del_Ins >> fs[] >> first_x_assum drule >>
 qpick_x_assum ‘hasCard(Ins(x0, xs0), n')’ (assume_tac o GSYM) >>
 drule hasCard_Ins_Suc >> fs[] >>
 first_x_assum (qspecl_then [‘x0’,‘xs0’] assume_tac) >> fs[] >>
 fs[] >> fs[Pre_Suc])
(form_goal
 “!X xs:mem(Pow(X)).Fin(xs) ==> ?!n.hasCard(xs,n)”));




val Card_def = 
 fVar_Inst 
[("P",([("xs",mem_sort $ Pow (mk_set "X")),
        ("n",mem_sort N)],
“(Fin(xs:mem(Pow(X))) & hasCard(xs,n)) | (~Fin(xs) & n = O)”))]
(AX1 |> qspecl [‘Pow(X)’,‘N’]) 
|> uex_expand |> ex2fsym0 "Card" ["X"] |> conjE1
|> gen_all 
|> store_as "Card_def";

val Card_Fun = prove_store("Card_Fun",
e0
(rw[Fun_expand,Card_def] >> rpt strip_tac (* 3 *)
 >-- (cases_on “Fin(a:mem(Pow(X)))” (* 2 *)
     >-- (drule Fin_Card >> 
         pop_assum (strip_assume_tac o uex_expand) >>
         qexists_tac ‘n’ >> arw[]) >>
     qexists_tac ‘O’ >> arw[])
 >-- (drule Fin_Card >> pop_assum (strip_assume_tac o uex_expand)>>
     first_assum rev_drule >> arw[] >> flip_tac >>
     first_assum irule >> arw[]) >>
 arw[])
(form_goal 
 “!X. isFun(Card(X))”));
 
val CARD_ex = prove_store("CARD_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(Card(X),xs)’ >> rw[])
(form_goal
 “!X xs:mem(Pow(X)). ?cxs. Eval(Card(X),xs) = cxs”));

val CARD_def = CARD_ex |> spec_all |> ex2fsym0 "CARD" ["xs"]
                       |> gen_all |> store_as "CARD_def"; 

 
val Fin_Empty= Fin_property |> spec_all |> conjE1
                            |> gen_all |> store_as "Fin_Empty";

val Fin_Ins = Fin_property |> spec_all |> conjE2
                            |> gen_all |> store_as "Fin_Ins";

val Del_Empty = prove_store("Del_Empty",
e0
(rpt strip_tac >> match_mp_tac IN_EXT >>
  rw[GSYM Del_property,Empty_property])
(form_goal
 “!X x. Del(Empty(X),x) = Empty(X)”));

val IN_Ins =  GSYM Ins_property |> store_as "IN_Ins";

val Ins_eq_eq = prove_store("Ins_eq_eq",
e0
(rpt strip_tac >-- (ccontra_tac >>
 qsuff_tac ‘~(IN(a2,Ins(a2,s2)))’
 >-- rw[GSYM Ins_property] >>
 qsuff_tac ‘~(IN(a2,Ins(a1,s1)))’
 >-- arw[] >>
 rw[IN_Ins] >> arw[] >> flip_tac >> first_x_assum accept_tac) >>
 irule IN_EXT >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘IN(x,Ins(a1,s1))’ >-- arw[IN_Ins] >> rfs[] >>
      fs[IN_Ins] >> pop_assum (assume_tac o GSYM) >> fs[]) >>
 qpick_x_assum ‘Ins(a1, s1) = Ins(a2, s2)’ (assume_tac o GSYM) >>
 qby_tac ‘IN(x,Ins(a2,s2))’ >-- arw[IN_Ins] >>
 rfs[] >> fs[IN_Ins] >> pop_assum (assume_tac o GSYM) >> fs[]
 )
(form_goal
 “!A a1:mem(A) s1 a2 s2. ~(IN(a1,s1)) & ~(IN(a2,s2)) & ~(IN(a1,s2)) & ~(IN(a2,s1)) & 
 Ins(a1,s1) = Ins(a2,s2) ==> a1 = a2 & s1 = s2”));


local
val l = fVar_Inst 
[("P",([("xs",mem_sort $ Pow (mk_set "X"))],
“Fin(xs) & !x. Fin(Del(xs,x:mem(X)))”))]
(Fin_ind_P |> qspecl [‘X’])
in
val Fin_Del0 = prove_store("Fin_Del",
e0
(strip_tac >> strip_tac >> match_mp_tac l >>
 rw[Del_Empty,Fin_Empty] >> rpt strip_tac >--
 (drule Fin_Ins >> arw[]) >>
 cases_on “x = x0:mem(X)” 
 >-- (arw[] >> cases_on “IN(x0:mem(X),xs0)”
      >-- (drule Ins_absorb >> arw[]) >>
      drule Del_Ins >> arw[]) >>
 pop_assum (assume_tac o GSYM) >>
 drule Del_Ins_SWAP >> arw[]>> 
 last_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Fin_Ins >> arw[])
(form_goal
 “!X xs:mem(Pow(X)).Fin(xs) ==> Fin(xs) &  !x. Fin(Del(xs,x)) ”));
end

val Fin_Del = prove_store("Fin_Del",
e0
(rpt strip_tac >> drule Fin_Del0 >> arw[])
(form_goal “!X xs:mem(Pow(X)).Fin(xs) ==> !x. Fin(Del(xs,x))”));

val Card_Fin = prove_store("Card_Fin",
e0
(rpt strip_tac >> rw[GSYM CARD_def] >> assume_tac Card_def >>
 first_x_assum (qspecl_then [‘X’,‘xs’,‘n’] assume_tac) >>
 rfs[] >> pop_assum (assume_tac o GSYM)>> arw[] >>
 qspecl_then [‘X’] assume_tac Card_Fun >>
 drule Eval_def >> arw[] >> lflip_tac >> rw[])
(form_goal
 “!X xs:mem(Pow(X)). Fin(xs) ==>
  (!n. CARD(xs) = n <=> hasCard(xs,n))”));


val CARD_Empty = prove_store("CARD_Empty",
e0
(assume_tac Fin_Empty >> strip_tac >>
 first_x_assum $ qspecl_then [‘X’] assume_tac >>
 drule Card_Fin >> arw[] >> rw[hasCard_Empty])
(form_goal
 “!X. CARD(Empty(X)) = O”));

val CARD_Ins = prove_store("CARD_Ins",
e0
(rpt strip_tac >> drule Fin_Ins >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Card_Fin >> arw[] >> irule hasCard_Ins >>
 arw[] >> rev_drule $ GSYM Card_Fin >> arw[])
(form_goal
 “!X xs:mem(Pow(X)). 
  Fin(xs) ==> !x.~(IN(x,xs)) ==> CARD(Ins(x,xs)) = Suc(CARD(xs))”));

val hasCard_Del' = hasCard_Del |> strip_all_and_imp 
                               |> conjE2 |> disch_all 
                               |> gen_all
                               |> store_as "hasCard_Del'";

val CARD_Del = prove_store("CARD_Del",
e0
(rpt strip_tac >> drule Fin_Del >> 
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Card_Fin >> arw[] >>
 irule hasCard_Del' >> arw[] >>
 rev_drule Card_Fin >> pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!X xs:mem(Pow(X)). Fin(xs) ==> 
  !x. IN(x,xs) ==> CARD(Del(xs,x)) = Pre(CARD(xs))”));
 


(*

 Card_def' |> spec_all |> iffRL

val hasCard_Ins_pre = prove_store("hasCard_Ins_pre",
e0
(rw[Card_def'] >>
 rpt strip_tac (* 2 *)
 >-- (first_assum irule >> arw[]) >>
 


 >-- first_assum accept_tac >> 
 first_assum irule
 )
(form_goal
 “!X xs:mem(Pow(X)) n. hasCard(xs,n) ==> hasCard(xs,n) & 
  (!x0 xs0 n0. (~IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) ==> hasCard(xs0,n0))”));

val Fin_Card = prove_store("Card_Fun",
e0
(rw[Fun_expand,Card_lemma] >> strip_tac >> match_mp_tac Fin_ind_card >>
 strip_tac >-- cheat >>
 rpt strip_tac >> )
(form_goal
 “!X xs:mem(Pow(X)).Fin(xs) ==> ?!n.hasCard(xs,n)”));


val rel_ex_lemma = 
fVar_Inst 
[("P",([("n",mem_sort N),("xs",mem_sort $Pow (mk_set "X"))],
“?r.Eval(u0:U~> N * Pow(X),r) = Pair(n,xs)”))]
(AX1 |> qspecl [‘N’,‘Pow(X)’]) |> uex_expand
val hasCard_ex = prove_store("hasCard_ex",
e0
()
(form_goal
 “!X. ?hc. IN(Pair(O,Empty(X)),hc) & 
 !x0. ”));



(*union is finite <=> A and B are finite*)

end
*)
