
local
val isL_cl = 
 “(ls = Empty(N * X) ==> IN(ls,isLs)) &
  (!ls0 x. IN(ls0,isLs) & 
           ls = Ins(Pa(Card(ls0),x),ls0) ==> IN(ls,isLs))”
in
val (isL_incond,x1) = mk_incond isL_cl;

val _ = new_fsym2IL("Card",(rastt "Cd0(X)",[dest_var (rastt "xs:A->Exp(X,1+1)")]));

val isLr_def = define_fsym("isLr",[("X",ob_sort)]) (qform2IL [‘isLs0 : 1->Exp(Exp(N * X,1+1),1+1)’,‘isLs1 : 1->Exp(Exp(N * X,1+1),1+1)’]
 ‘!ls : 1-> Exp(N * X,1+1).
     IN(ls, isLs1) <=>
     ls = Empty(N * X) |
     ?ls0 :1-> Exp(N * X, 1+1)  x.
       IN(ls0, isLs0) & ls = Ins(Pa(Card(ls0), x), ls0)’)
val IL_lemma = 
proved_th $
e0
(rpt strip_tac  >>
 rw[o_assoc,Pa_distr,DISJ_def,p12_of_Pa,Eq_property_TRUE,
             one_to_one_id,idR,isLr_def] >>
 once_rw[All_def,o_assoc,Pa_distr] >>
 rw[IFF_def,o_assoc,Pa_distr] >>
 rw[DISJ_def,o_assoc,Pa_distr] >>
 once_rw[Ex_def] >> rw[o_assoc] >> once_rw[Ex_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[p52_def] >> once_rw[p51_def] >> once_rw[p53_def] >>
 once_rw[p54_def] >> once_rw[p55_def] >> 
 once_rw[p31_def] >> once_rw[p32_def] >> once_rw[p33_def] >>
 once_rw[o_assoc] >> 
 once_rw[Pa_distr] >> once_rw[Eq_property_TRUE] >>
 once_rw[p12_of_Pa] >> once_rw[p12_of_Pa] >> 
 rw[Pa_distr] >> rw[p12_of_Pa,o_assoc] >> rw[Pa_distr] >>
 rw[one_to_one_id] >> rw[idR] >>
 rw[Card_def] >> rw[Ins_def,IN_def])
(form_goal “!a a'.
 isLr(X) o Pa(a,a') =TRUE <=>
  !ls : 1-> Exp(N * X,1+1).
     IN(ls, a') <=>
     ls = Empty(N * X) |
     ?ls0 :1-> Exp(N * X, 1+1)  x.
       IN(ls0, a) & ls = Ins(Pa(Card(ls0), x), ls0)”);
val isLsi_def = 
define_fsym("isLsi",[dest_var (rastt "a : 1->Exp(Exp(N * X,1+1),1+1)")]) (qform2IL [‘ls : 1-> Exp(N * X,1+1)’]
 ‘ls = Empty(N * X) |
     ?ls0 :1-> Exp(N * X, 1+1)  x.
       IN(ls0, a) & ls = Ins(Pa(Card(ls0), x), ls0)’);
val isLsi_property = proved_th $
e0
(rw[isLsi_def] >> rpt strip_tac >>
 rw[o_assoc,DISJ_def,Pa_distr] >> 
 once_rw[Ex_def] >> rw[o_assoc,Ex_def] >>
 rw[CONJ_def,Pa_distr,o_assoc] >>
 rw[one_to_one_id,idR] >>
 once_rw[p31_def,p32_def,p33_def] >>
 rw[p12_of_Pa,o_assoc,Pa_distr] >>
 rw[Eq_property_TRUE,IN_def,Ins_def] >> 
 rw[Card_def,idL])
(form_goal 
“!a ls. isLsi(a) o ls = TRUE <=>
 ls = Empty(N * X) |
     ?ls0 :1-> Exp(N * X, 1+1)  x.
       IN(ls0, a) & ls = Ins(Pa(Card(ls0), x), ls0)”);
val isLf_precond = proved_th $
e0
(strip_tac >>
 qsuff_tac
 ‘?a'.!ls : 1-> Exp(N * X,1+1).
     IN(ls, a') <=>
     ls = Empty(N * X) |
     ?ls0 :1-> Exp(N * X, 1+1)  x.
       IN(ls0, a) & ls = Ins(Pa(Card(ls0), x), ls0)’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘a'’ >>
      arw[] >> rpt strip_tac >> irule $ iffLR IN_EXT >> arw[]) >>
 qexists_tac ‘Tp1(isLsi(a))’ >>
 rw[IN_Tp1] >> rw[isLsi_property])
(form_goal “!a. ?!a'.
 !ls : 1-> Exp(N * X,1+1).
     IN(ls, a') <=>
     ls = Empty(N * X) |
     ?ls0 :1-> Exp(N * X, 1+1)  x.
       IN(ls0, a) & ls = Ins(Pa(Card(ls0), x), ls0)”);
val isLf_def = 
Rel2Ar_uex
|> sspecl [rastt "isLr(X)"]
|> rewr_rule[IL_lemma]
|> C mp isLf_precond
|> qsimple_uex_spec "isLf" [‘X’]
|> spec_all |> qgen ‘b’
|> qspecl [‘isLf(X) o a’]
|> rewr_rule[] |> qgen ‘a’;
val isLf_monotone = mk_monotone isLf_def;
val isL's_def = mk_prim isLf_def;
val isLs_def = mk_LFP (rastt "isL's(X)");
val isLs_cond = mk_cond isLs_def isL's_def;
val isLs_SS = mk_SS isLs_def isL's_def;
val isL_rules0 = mk_rules isLf_monotone isLs_SS isLs_cond;
val isL_cases0 = mk_cases isLf_monotone isL_rules0 isLs_cond;
val isL_ind0 = mk_ind isLs_cond;
val isL_ind1 = mk_ind1 isLf_def isL_ind0;
val isL_ind2 = mk_ind2 isL_ind1;
val isL_cases1 = mk_case1 isLf_def isL_cases0;
val isL_rules1 = mk_rules1 isLf_def isL_rules0;
val isL_rules2 = mk_rules2 isL_rules1;
val isL_rules3 = mk_rules3 isL_rules2;
end

val isL_ind = isL_ind2 |> store_as "isL_ind";
val isL_cases = isL_cases1 |> store_as "isL_cases";
val isL_rules = isL_rules3 |> store_as "isL_rules";

val List_def0 = pred_subset_ex' |> qsspecl [‘Tp0(isLs(X))’]
                              |> qSKOLEM "List" [‘X’] 
                              |> qSKOLEM "iL" [‘X’]
                              |> gen_all 

val iL_Mono = List_def0 |> spec_all 
                      |> conjE1 |> gen_all
                      |> store_as "iL_Mono"; 

val List_def1 = List_def0 |> spec_all |> conjE2
                          |> qspecl [‘1’]
                          |> rewr_rule[True1TRUE]
                          |> C conjI (spec_all iL_Mono)
                          |> store_as "List_def1";




val isL_def = qdefine_psym("isL",[‘l:1->Exp(N * X,1+1)’]) 
                          ‘IN(l,isLs(X))’
                          |> gen_all |> store_as "isL_def"; 

val isL_induct = prove_store("isL_induct",
e0
(rw[isL_def] >> strip_tac >> strip_tac >>
 qsspecl_then [‘Tp1(P)’] assume_tac isL_ind >>
 fs[IN_Tp1])
(form_goal 
 “!X P.P o Empty(N * X) = TRUE & 
  (!ls0 x. P o ls0 = TRUE ==>
    P o Ins(Pa(Card(ls0),x),ls0) = TRUE) ==> 
  !l:1-> Exp(N * X,1+1). isL(l) ==> P o l = TRUE”));
 
val isL_Empty = prove_store("isL_Empty",
e0
(rw[isL_def,isL_rules])
(form_goal
 “!X. isL(Empty(N * X))”)); 

val isL_Ins = isL_rules |> spec_all |> conjE2 
                        |> rewr_rule[GSYM isL_def]
                        |> spec_all |> undisch 
                        |> gen_all |> disch_all
                        |> gen_all |> store_as "isL_Ins";

val Repl_def = qdefine_fsym ("Repl",[‘l:1-> List(X)’])
                            ‘iL(X) o l’
                            |> gen_all |> store_as "Repl_def";
 
val List_def = List_def1 |> rewr_rule[GSYM IN_Tp1,Tp1_Tp0_inv]
                         |> gen_all
                         |> store_as "List_def";



val Nil_def = proved_th $
e0
(strip_tac >> uex_tac >>
 qspecl_then [‘X’] strip_assume_tac List_def >>
 first_assum (qspecl_then [‘Empty(N * X)’] assume_tac) >>
 fs[isL_Empty,GSYM isL_def] >>
 qexists_tac ‘x0’ >> arw[Repl_def] >>
 fs[Mono_def])
(form_goal “!X. ?!l.Repl(l) = Empty(N * X)”)
|> spec_all |> qsimple_uex_spec "Nil" [‘X’] |> gen_all
|> store_as "Nil_def";

val cons0_def = 
    qdefine_fsym ("cons0",[‘x:1->X’,‘l:1->Exp(N * X,1+1)’])
    ‘Ins(Pa(Card(l),x:1->X),l)’

local
val l = proved_th $
e0
(rpt strip_tac >> uex_tac >> 
 qexists_tac ‘Ins(Pa(Card(b), a'), b)’ >>
 rw[] >> rpt strip_tac >> arw[])
(form_goal “!a':1->X b. ?!b'. b' = Ins(Pa(Card(b), a'), b)”) 
in
val cons1_def = 
P2fun_uex |> qspecl [‘X * Exp(N * X,1+1)’,‘Exp(N * X,1+1)’]
|> specl [qform2IL [‘xl:1->X * Exp(N * X,1+1)’,‘l':1->Exp(N * X,1+1)’] ‘l' = Ins(Pa(Card(Snd(xl)), Fst(xl)), Snd(xl))’]
|> rewr_rule[Holds_def]
|> rewr_rule[o_assoc,Pa_distr,p12_of_Pa,Eq_property_TRUE,Fst_def,Snd_def]
|> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[o_assoc,Pa_distr,p12_of_Pa]
|> rewr_rule[GSYM Card_def,GSYM Ins_def]
|> C mp l
|> qsimple_uex_spec "cons1" [‘X’]
|> qspecl [‘x:1->X’,‘l:1-> Exp(N * X,1+1)’]
|> rewr_rule[GSYM cons0_def]
|> qspecl [‘cons0(x, l)’]  |> rewr_rule[]
|> qgenl[‘X’,‘x’,‘l’]
|> store_as "cons1_def"
end

(*Parallel product arrow*)
val Prla_def = 
    qdefine_fsym ("Prla",[‘f:A->B’,‘g:C->D’])
    ‘Pa(f o p1(A,C),g o p2(A,C))’
    |> gen_all |> store_as "Prla_def";


val Inj_def = 
    qdefine_psym ("Inj",[‘f:A->B’]) 
                 ‘!x1:1->A x2. f o x1 = f o x2 ==> x1 = x2’
    |> gen_all |> store_as "Inj_def";

val Inj_Mono = prove_store("Inj_Mono",
e0
(rpt strip_tac >>
 rw[Inj_def,Mono_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule FUN_EXT >> strip_tac >>
     first_x_assum irule >> arw[GSYM o_assoc]) >>
 first_x_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) <=> Mono(f)”));

val Prla_Inj = prove_store("Prla_Inj",
e0
(rpt strip_tac >> fs[Inj_def,Prla_def] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[Pa_eq_eq,Pa_distr,o_assoc,p12_of_Pa] >>
 rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !C D g:C->D. Inj(g) ==>
 Inj(Prla(f,g))”));


val id_Inj = prove_store("id_Inj",
e0
(rw[Inj_def,idL])
(form_goal
 “!X. Inj(id(X))”));

(*iL_isL should be automated*)
val iL_isL = prove_store("iL_isL",
e0
(rpt strip_tac >> 
 rw[isL_def] >> 
 qspecl_then [‘X’] assume_tac List_def >>
 fs[] >> qexists_tac ‘l’ >> rw[])
(form_goal “!X l. isL(iL(X) o l)”)); 

val isL_Repl = List_def |> spec_all |> conjE1
                        |> rewr_rule[GSYM isL_def,
                                     GSYM Repl_def] 
                        |> gen_all 
                        |> store_as "isL_Repl";

val lift_cond2 = proved_th $
e0
(fconv_tac forall_cross_fconv >>
 rw[Prla_def,Pa_distr,o_assoc,
    p12_of_Pa,idL,cons1_def] >>
 rpt strip_tac >>
 qsspecl_then [‘b’] assume_tac iL_isL >>
 drule isL_Ins >> rw[GSYM Repl_def,GSYM isL_Repl] >>
 fs[Repl_def,cons0_def])
(form_goal
 “!xl1:1-> X * List(X).?l2.
 (cons1(X) o Prla(id(X),iL(X))) o xl1 = iL(X) o l2”)


val lift_cond2' = proved_th $
e0
(assume_tac lift_cond2 >> strip_tac >> uex_tac >>
 first_x_assum (qspecl_then [‘xl1’] strip_assume_tac) >>
 qexists_tac ‘l2’ >> arw[] >> assume_tac iL_Mono >>
 fs[Mono_def] >> rpt strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “!xl1:1->X * List(X).?!l2.
 (cons1(X) o Prla(id(X),iL(X))) o xl1 = iL(X) o l2”)


val CONS_def = P2fun_uex |> qspecl [‘X * List(X)’,‘List(X)’]
                     |> specl [qform2IL [‘xl1:1->X * List(X)’,‘l2:1-> List(X)’]
 ‘(cons1(X) o Prla(id(X),iL(X))) o xl1 = iL(X) o l2’]
                     |> rewr_rule[Holds_def]
                     |> rewr_rule[Eq_property_TRUE,o_assoc,
                                 Pa_distr ,p12_of_Pa]
                     |> C mp (lift_cond2' |> rewr_rule[o_assoc])
                     |> qsimple_uex_spec "CONS" [‘X’]
                     |> qspecl 
                     [‘Pa(x:1->X,l:1-> List(X))’,
                      ‘CONS(X) o Pa(x:1->X,l:1-> List(X))’]
                     |> rewr_rule[Prla_def,
                                  p12_of_Pa,idL,Pa_distr,
                                  o_assoc,cons1_def,cons0_def,GSYM Repl_def]
                     |> gen_all
                     |> store_as "CONS_def"; 


val Cons_def = 
    qdefine_fsym ("Cons",[‘x:1->X’,‘l:1->List(X)’])
    ‘CONS(X) o Pa(x,l)’ 
    |> gen_all |> store_as "Cons_def";

val Repl_Cons = CONS_def |> rewr_rule[GSYM Cons_def]
                         |> GSYM
                         |> store_as "Repl_Cons";

val Inj_eq_eq = prove_store("Inj_eq_eq",
e0
(rpt strip_tac >> fs[Inj_def] >> dimp_tac >>
 rpt strip_tac >> arw[] >>
 first_x_assum irule >> arw[])
(form_goal “!X Y i:X->Y. Inj(i) ==>
 (!x1 x2:1->X.i o x1 = i o x2 <=> x1 =  x2)”));
 
val iL_Inj = iL_Mono |> rewr_rule[GSYM Inj_Mono]

(*should automate*)
val Repl_eq_eq = prove_store("Repl_eq_eq",
e0
(rpt strip_tac >> rw[Repl_def] >> irule Inj_eq_eq >>
 rw[iL_Inj])
(form_goal “!X l1:1->List(X) l2.
 Repl(l1) = Repl(l2) <=> l1 = l2”));




val Cons_NONNIL = prove_store("Cons_NONNIL",
e0
(rw[GSYM Repl_eq_eq,Nil_def,Repl_Cons,Ins_NONEMPTY])
(form_goal
 “!X x l. ~(Cons(x,l) = Nil(X))”));


val Repl_Empty_uex = prove_store("Repl_Empty_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[Nil_def] >>
 rw[GSYM Repl_eq_eq] >> arw[Nil_def])
(form_goal
 “!X l. Repl(l) = Empty(N * X) <=> l = Nil(X)”));


val _ = new_psym2IL("isL",(rastt "Tp0(isLs(X))",List.map (dest_var o rastt) ["nxs:A->Exp(N * X,1+1)"]))

val _ = new_fsym2IL("Repl",(rastt "iL(X)",List.map (dest_var o rastt) ["l:A-> List(X)"]))

val IN_Tp0 = prove_store("IN_Tp0",
e0
(rw[IN_def,Tp0_def,In_def,Pa_distr,
    one_to_one_id,idL,idR,o_assoc])
(form_goal “!X x:1->X xs.IN(x,xs) <=> Tp0(xs) o x = TRUE”));

val List_induct = prove_store("List_induct",
e0
(strip_tac >> strip_tac >> disch_tac >>
 qsuff_tac ‘!nxs:1 -> Exp(N * X,1+1). isL(nxs) ==> isL(nxs) &
 (!l. Repl(l) = nxs ==> P o l = TRUE)’
 >-- (strip_tac >>
     qby_tac ‘!nxs:1-> Exp(N * X,1+1). isL(nxs) ==>
                      (!l. Repl(l) = nxs ==> P o l = TRUE)’ 
     >-- (rpt strip_tac >> first_x_assum drule >>
          rfs[] >> first_x_assum irule >> arw[]) >>
     strip_tac >> first_x_assum irule >>
     qexists_tac ‘Repl(l)’ >> rw[isL_Repl] >>
     qexists_tac ‘l’ >> rw[]) >>
 qby_tac
 ‘?P1. !nxs.(isL(nxs) &
           !l:1-> List(X). Repl(l) = nxs ==> P o l = TRUE)
  <=> P1 o nxs = TRUE’
 >-- (exists_tac (qform2IL [‘nxs:1->Exp(N * X,1+1)’] 
      ‘isL(nxs) &
       !l:1-> List(X). Repl(l) = nxs ==> P o l = TRUE’) >>
      rw[o_assoc,CONJ_def,Pa_distr,p12_of_Pa,All_def,
         IMP_def,Eq_property_TRUE,one_to_one_id,idL,idR] >>
      rw[Repl_def,isL_def] >> rw[IN_Tp0]) >>
 ind_with1 (isL_induct |> qspecl [‘X’]) >>
 rw[isL_Empty] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     qsuff_tac ‘l = Nil(X)’ >-- (strip_tac >> arw[]) >>
     irule $ iffLR Repl_Empty_uex >> arw[]) >>
 rpt gen_tac >> disch_tac >>
 pop_assum strip_assume_tac >>
 qby_tac ‘isL(Ins(Pa(Card(ls0), x), ls0))’ 
 >-- (irule isL_Ins >> arw[]) >> arw[] >>
 rpt strip_tac >>
 qby_tac ‘?l0. Repl(l0) = ls0’ 
 >-- (fs[isL_Repl] >> qexists_tac ‘x0’ >> rw[]) >>
 pop_assum strip_assume_tac >>
 first_x_assum drule >>
 qsuff_tac ‘l = Cons(x,l0)’ 
 >-- (strip_tac  >> last_x_assum strip_assume_tac >>
      arw[] >> first_x_assum irule >> arw[]) >>
 rw[GSYM Repl_eq_eq] >> arw[Repl_Cons])
(form_goal
 “!X P. P o Nil(X) = TRUE & 
  (!l:1->List(X). P o l = TRUE ==> !x. P o Cons(x,l) = TRUE) ==>
     !l:1->List(X).P o l = TRUE”));

val Fin_Repl = prove_store("Fin_Repl",
e0
(strip_tac >>
 qby_tac ‘?P.!l:1->List(X). Fin(Repl(l)) <=> P o l = TRUE’
 >-- (exists_tac (qform2IL [‘l:1->List(X)’] ‘Fin(Repl(l))’) >>
     rw[idR,Fin_def,IN_Tp0,Repl_def,o_assoc,idL]) >>
 ind_with1 (List_induct |> qspecl [‘X’]) >>
 rw[Nil_def,Fin_Empty,Repl_Cons] >>
 rpt strip_tac >> drule Fin_Ins >> arw[])
(form_goal
 “!X l:1->List(X). Fin(Repl(l))”)); 

val isL_Card_NOTIN0 = prove_store("isL_Card_NOTIN0",
e0
(strip_tac >> 
 qby_tac
 ‘?P.!l. (!n x:1->X. 
  (IN(Pa(n, x), Repl(l)) ==> Lt(n, Card(Repl(l))))) <=> 
  P o l = TRUE’
 >-- (exists_tac (qform2IL [‘l:1->List(X)’]
      ‘!n x:1->X. 
  (IN(Pa(n, x), Repl(l)) ==> Lt(n, Card(Repl(l))))’) >>
      rw[All_def,o_assoc,Pa_distr,p12_of_Pa,IMP_def] >>
      once_rw[p31_def,p32_def,p33_def] >>
      rw[Pa_distr,o_assoc,p12_of_Pa] >>
      rw[LT_Lt,Repl_def,IN_def,Card_def]) >>
ind_with1 (List_induct |> qspecl [‘X’]) >>
 rw[Nil_def,Empty_def,Repl_Cons,Ins_def1,Pa_eq_eq] >>
 rpt strip_tac (* 2 *)
 >-- (arw[] >> qsspecl_then [‘l’] assume_tac Fin_Repl >>
     drule Card_Ins >> 
     qby_tac ‘~(IN(Pa(Card(Repl(l)),x), Repl(l)))’ 
     >-- (ccontra_tac >> first_x_assum drule >>
          fs[Lt_def]) >>
     first_x_assum drule >> arw[Lt_Suc]) >>
 first_assum drule >>
 irule Lt_trans >>
 qexists_tac ‘Card(Repl(l))’ >> arw[] >>
 qsspecl_then [‘l’] assume_tac Fin_Repl >>
 drule Card_Ins >> 
 qby_tac ‘~(IN(Pa(Card(Repl(l)),x), Repl(l)))’(* repeated *)
 >-- (ccontra_tac >> first_x_assum drule >>
                  fs[Lt_def]) >>
 first_x_assum drule >>
 arw[Lt_Suc])
(form_goal
 “!X l n x:1->X. IN(Pa(n,x),Repl(l)) ==> 
              Lt(n,Card(Repl(l)))”));



val CONS_Inj = prove_store("CONS_Inj",
e0
(strip_tac >> rw[Inj_def,CONS_def] >> rpt strip_tac >>
 qsspecl_then [‘x1’]
 (x_choosel_then ["a1","l1"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘x2’] 
 (x_choosel_then ["a2","l2"] assume_tac) Pair_has_comp >>
 fs[] >> fs[GSYM Repl_eq_eq,GSYM CONS_def] >> 
 qsuff_tac
 ‘Pa(Card(Repl(l1)), a1) = Pa(Card(Repl(l2)), a2) & 
  Repl(l1) = Repl(l2)’
 >-- (rw[Pa_eq_eq,Repl_eq_eq] >> rpt strip_tac >> arw[]) >>
 irule Ins_eq_eq >> arw[] >>
 qby_tac
 ‘~IN(Pa(Card(Repl(l1)), a1), Repl(l1)) & 
  ~IN(Pa(Card(Repl(l2)), a2), Repl(l2))’
 >-- (strip_tac >> ccontra_tac >> drule isL_Card_NOTIN0 >>
      fs[Lt_def]) >> arw[] >> 
 pop_assum strip_assume_tac >>
 qby_tac ‘Card(Repl(l2)) = Card(Repl(l1))’ 
 >-- (ccontra_tac >>
      qsuff_tac
      ‘~(Card(Ins(Pa(Card(Repl(l1)), a1), Repl(l1))) =
         Card(Ins(Pa(Card(Repl(l2)), a2), Repl(l2))))’
      >-- rfs[] >>
      qby_tac
      ‘Card(Ins(Pa(Card(Repl(l1)), a1), Repl(l1))) = 
       Suc(Card(Repl(l1))) & 
       Card(Ins(Pa(Card(Repl(l2)), a2), Repl(l2))) = 
       Suc(Card(Repl(l2)))’
      >-- (strip_tac >> irule Card_Ins >> arw[Fin_Repl]) >>
      arw[Suc_eq_eq] >> flip_tac >> arw[]) >>
 strip_tac (* 2 *)
 >-- (arw[] >>
     ccontra_tac >> drule isL_Card_NOTIN0 >> fs[Lt_def]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 ccontra_tac >> drule isL_Card_NOTIN0 >> fs[Lt_def])
(form_goal
 “!X. Inj(CONS(X))”));



val Cons_eq_eq = prove_store("Cons_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> disch_tac >> arw[] >>
 fs[Cons_def] >> assume_tac CONS_Inj >>
 fs[Inj_def] >>
 first_x_assum drule >> fs[Pa_eq_eq])
(form_goal
 “!X x1:1->X l1 x2 l2.Cons(x1,l1) = Cons(x2,l2) <=> (x1 = x2 & l1 = l2)”));


val _ = new_fsym2IL("Cons",(rastt "CONS(X)",[dest_var (rastt "x:A-> X"),dest_var (rastt "l:A->List(X)")]));

val Cons_or_Nil = prove_store("Cons_or_Nil",
e0
(strip_tac >> 
 qby_tac ‘?P.!l:1->List(X).(l = Nil(X) | ?x0 l0. l = Cons(x0,l0)) <=> P o l = TRUE ’
 >-- (exists_tac (qform2IL [‘l:1->List(X)’]
      ‘l = Nil(X) | ?x0 l0. l = Cons(x0,l0)’) >>
     rw[o_assoc,DISJ_def,Pa_distr,Eq_property_TRUE,idL,
        Ex_def] >>
     rw[p31_def,p32_def,p33_def,Pa_distr,p12_of_Pa,o_assoc] >>
     rw[Cons_def,one_to_one_id,idR]) >>
ind_with1 (List_induct |> qspecl [‘X’]) >>
 rw[Cons_NONNIL] >> rpt strip_tac >>
 (qexistsl_tac [‘x’,‘l’] >> rw[]))
(form_goal
 “!X l:1->List(X). l = Nil(X) | ?x0 l0. l = Cons(x0,l0)”));




val Cons_xor_Nil = prove_store("Cons_xor_Nil",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qsspecl_then [‘l’] strip_assume_tac Cons_or_Nil >>
 qexistsl_tac [‘x0’,‘l0’] >> arw[]) >>
 arw[Cons_NONNIL])
(form_goal
 “!X l:1-> List(X). ~(l = Nil(X))<=> ?x0 l0. l = Cons(x0,l0)”));






local
val Lind_cl = 
 “(p = Pa(Nil(X),a0:1->A) ==> IN(p,Lind)) &
  (!p0:1->List(X) * A x:1->X.
   IN(p0,Lind) & 
        p = Pa(Cons(x,Fst(p0)),
            f0:X * A ->A o Pa(x,Snd(p0)))
    ==> IN(p,Lind))”
in
val (Lind_incond,x1) = mk_incond Lind_cl;
val Lindr_def = define_fsym("Lindr",List.map (dest_var o rastt) ["a0:1->A","f0:X * A->A"]) (qform2IL [‘Lind0 : 1->Exp(List(X) * A,1+1)’,
  ‘Lind1 : 1->Exp(List(X) * A,1+1)’]
 ‘!p : 1-> List(X) * A.
     IN(p, Lind1) <=>
     p = Pa(Nil(X), a0) |
  ?p0 :1 -> List(X) * A  x:1->X.
   IN(p0, Lind0) & p = Pa(Cons(x, Fst(p0)), f0 o Pa(x, Snd(p0)))’);
val IL_lemma = 
proved_th $
e0
(rpt strip_tac  >>
 rw[o_assoc,Pa_distr,DISJ_def,p12_of_Pa,Eq_property_TRUE,
             one_to_one_id,idR,Lindr_def] >>
 once_rw[All_def,o_assoc,Pa_distr] >>
 rw[IFF_def,o_assoc,Pa_distr] >>
 rw[DISJ_def,o_assoc,Pa_distr] >>
 once_rw[Ex_def] >> rw[o_assoc] >> once_rw[Ex_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[p52_def] >> once_rw[p51_def] >> once_rw[p53_def] >>
 once_rw[p54_def] >> once_rw[p55_def] >> 
 once_rw[p31_def] >> once_rw[p32_def] >> once_rw[p33_def] >>
 once_rw[o_assoc] >> 
 once_rw[Pa_distr] >> once_rw[Eq_property_TRUE] >>
 once_rw[p12_of_Pa] >> once_rw[p12_of_Pa] >> 
 rw[Pa_distr] >> rw[p12_of_Pa,o_assoc] >> rw[Pa_distr] >>
 rw[one_to_one_id] >> rw[idR] >>
 once_rw[Fst_def,Snd_def] >>
 rw[Pa_distr,o_assoc,p12_of_Pa] >>
 rw[Cons_def] >> rw[Ins_def,IN_def])
(form_goal “!a a'.
 Lindr(a0:1->A,f0:X * A -> A) o Pa(a,a') =TRUE <=>
 !p : 1-> List(X) * A.
     IN(p, a') <=>
     p = Pa(Nil(X), a0) |
  ?p0 :1 -> List(X) * A  x:1->X.
   IN(p0, a) & p = Pa(Cons(x, Fst(p0)), f0 o Pa(x, Snd(p0)))
”);
val Lindsi_def = 
define_fsym("Lindsi",
List.map (dest_var o rastt)
["a0:1->A","f0:X * A -> A","a:1->Exp(List(X) * A,1+1)"]) (qform2IL [‘p : 1->List(X) * A’]
 ‘ p = Pa(Nil(X), a0) |
  ?p0 :1 -> List(X) * A  x:1->X.
   IN(p0, a) & p = Pa(Cons(x, Fst(p0)), f0 o Pa(x, Snd(p0)))’);
val Lindsi_property = proved_th $
e0
(rw[Lindsi_def] >> rpt strip_tac >>
 rw[o_assoc,DISJ_def,Pa_distr] >> 
 once_rw[Ex_def] >> rw[o_assoc,Ex_def] >>
 rw[CONJ_def,Pa_distr,o_assoc] >>
 rw[one_to_one_id,idR] >>
 once_rw[p31_def,p32_def,p33_def] >>
 rw[p12_of_Pa,o_assoc,Pa_distr] >>
 rw[Eq_property_TRUE,IN_def,Ins_def] >> 
 once_rw[Fst_def,Snd_def] >>
 rw[o_assoc,Pa_distr,p12_of_Pa] >> 
 rw[Cons_def,idL])
(form_goal 
“!a p. Lindsi(a0:1->A,f0,a) o p = TRUE <=>
 p = Pa(Nil(X), a0) |
  ?p0 :1 -> List(X) * A  x:1->X.
   IN(p0, a) & p = Pa(Cons(x, Fst(p0)), f0 o Pa(x, Snd(p0)))”);
val Lindf_precond = proved_th $
e0
(strip_tac >>
 qsuff_tac
 ‘?a'.
 !p : 1-> List(X) * A.
     IN(p, a') <=>
     p = Pa(Nil(X), a0) |
  ?p0 :1 -> List(X) * A  x:1->X.
   IN(p0,a) & p = Pa(Cons(x, Fst(p0)), f0 o Pa(x, Snd(p0)))’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘a'’ >>
      arw[] >> rpt strip_tac >> irule $ iffLR IN_EXT >> arw[]) >>
 qexists_tac ‘Tp1(Lindsi(a0,f0,a))’ >>
 rw[IN_Tp1] >> rw[Lindsi_property])
(form_goal “!a. ?!a'.
 !p : 1-> List(X) * A.
     IN(p, a') <=>
     p = Pa(Nil(X), a0) |
  ?p0 :1 -> List(X) * A  x:1->X.
   IN(p0,a) & p = Pa(Cons(x, Fst(p0)), f0 o Pa(x, Snd(p0)))”);
val Lindf_def = 
Rel2Ar_uex
|> sspecl [rastt "Lindr(a0:1->A,f0:X * A->A)"]
|> rewr_rule[IL_lemma]
|> C mp Lindf_precond
|> qsimple_uex_spec "Lindf" [‘a0’,‘f0’]
|> spec_all |> qgen ‘b’
|> qspecl [‘Lindf(a0,f0) o a’]
|> rewr_rule[] |> qgen ‘a’;
val Lindf_monotone = mk_monotone Lindf_def;
val Lind's_def = mk_prim Lindf_def;
val Linds_def = mk_LFP (rastt "Lind's(a0:1->A,f0:X * A->A)");
val Linds_cond = mk_cond Linds_def Lind's_def;
val Linds_SS = mk_SS Linds_def Lind's_def;
val Lind_rules0 = mk_rules Lindf_monotone Linds_SS Linds_cond;
val Lind_cases0 = mk_cases Lindf_monotone Lind_rules0 Linds_cond;
val Lind_ind0 = mk_ind Linds_cond;
val Lind_ind1 = mk_ind1 Lindf_def Lind_ind0;
val Lind_ind2 = mk_ind2 Lind_ind1; 
val Lind_cases1 = mk_case1 Lindf_def Lind_cases0; 
val Lind_rules1 = mk_rules1 Lindf_def Lind_rules0; 
val Lind_rules2 = mk_rules2 Lind_rules1; 
val Lind_rules3 = mk_rules3 Lind_rules2;
end

val Lind_ind = Lind_ind2 |> store_as "Lind_ind";
val Lind_cases = Lind_cases1 |> store_as "Lind_cases";
val Lind_rules = Lind_rules3 |> store_as "Lind_rules";


val Cdr_def = qdefine_psym("Cdr",[‘xs:1->Exp(X,1+1)’,‘n:1->N’])
‘IN(Pa(xs,n),Cds(X))’ |> qgenl[‘X’,‘xs’,‘n’] 
|> store_as "Cdr_def";

(*exactly same proof as Nind_uex*)

(* qform2IL [‘l:1-> List(X)’]
 ‘(?!a:1->A. IN(Pa(l, a), Linds(a0, f0)))’ 
 term2IL [dest_var o rastt $ "a:1->A"] 
val t = (rastt "f0:X * A ->A")

val (n,s) = dest_var t

val bvs = [dest_var o rastt $ "a:1->A"] 
val t = (rastt "Linds(a0:1->A, f0:X * A->A)")
val (f,s,tl) = dest_fun t

Linds(a0, f0)

cannot build*)
val Lind_uex = prove_store("Lind_uex",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 rw[IN_Tp0] >>
 qby_tac
 ‘?P.!l. (?!a:1->A. Tp0(Linds(a0, f0)) o Pa(l, a) = TRUE) <=>
  P o l = TRUE’
 >-- (exists_tac (qform2IL [‘l:1-> List(X)’]
 ‘?!a:1->A. Tp0(Linds(a0, f0)) o Pa(l, a) = TRUE’) >>
     rw[E1_def1,o_assoc,Pa_distr,p12_of_Pa,Eq_property_TRUE,
     one_to_one_id,idL,idR]) >>
 pop_assum mp_tac >> rw[GSYM IN_Tp0] >> disch_tac >>
 ind_with1 (List_induct |> qspecl [‘X’]) >> strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘a0’ >>
      rw[Lind_rules] >> once_rw[Lind_cases] >>
      rw[Pa_eq_eq,GSYM Cons_NONNIL] >> rpt strip_tac) >>
 rpt strip_tac >> uex_tac >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f0 o Pa(x,a)’ >>
 drule (Lind_rules |> conjE2) >> fs[Pair_def'] >>
 rpt strip_tac >> drule $ iffLR Lind_cases >>
 fs[Pa_eq_eq,Cons_NONNIL] >>
 qsspecl_then [‘p0’] (x_choosel_then ["l1","a1"] strip_assume_tac) Pair_has_comp >> fs[Pair_def',Cons_eq_eq] >>
 qby_tac ‘a1 = a’ 
 >-- (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal
 “!A a0:1->A X f0: X * A ->A l:1-> List(X). ?!a. IN(Pa(l,a),Linds(a0,f0))”));


val Lrec_def = P2fun_uex |> qspecl [‘List(X)’,‘A’]
                     |> specl [qform2IL [‘l:1-> List(X)’,‘a:1->A’]
 ‘Tp0(Linds(a0, f0)) o Pa(l, a) = TRUE’]
|>  rewr_rule[E1_def1,o_assoc,Pa_distr,p12_of_Pa,Eq_property_TRUE,
     one_to_one_id,idL,idR,Holds_def,p31_def,p32_def,p33_def]
|> rewr_rule[GSYM IN_Tp0]
|> C mp 
   (Lind_uex |> spec_all |> qgen ‘l’)
|> qsimple_uex_spec "Lrec" [‘a0’,‘f0’]
|> spec_all
|> qgen ‘b’
|> qspecl [‘Lrec(a0, f0) o a’] |> rewr_rule[]
|> qgenl [‘A’,‘a0’,‘X’,‘f0’,‘a’]
|> store_as "Lrec_def";


val Lrec_Nil = prove_store("Lrec_Nil",
e0
(rpt strip_tac >>
 qsspecl_then [‘a0’,‘f0’,‘Nil(X)’] assume_tac Lrec_def >>
 drule $ iffLR Lind_cases >>
 fs[Pa_eq_eq,GSYM Cons_NONNIL])
(form_goal “!A a0 X f0:X * A -> A. 
 Lrec(a0,f0) o Nil(X) = a0”));



val App_Lrec_Linds = prove_store("App_Lrec_Linds",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >--
(pop_assum (assume_tac o GSYM) >> arw[Lrec_def]) >>
qsspecl_then [‘a0’,‘f0’,‘l’] assume_tac Lrec_def >>
qsspecl_then [‘a0’,‘f0’,‘l’] assume_tac Lind_uex >>
pop_assum (strip_assume_tac o uex_expand) >>
qby_tac ‘Lrec(a0, f0) o  l = a' & a = a'’ 
>-- (strip_tac >> first_x_assum irule >> arw[]) >>
arw[])
(form_goal “!A a0 X f0:X * A ->A.
!l a. Lrec(a0,f0) o l = a <=> 
IN(Pa(l,a),Linds(a0,f0))”));


val Lrec_Cons = prove_store("Lrec_Cons",
e0
(rpt strip_tac >>
 qsspecl_then [‘a0’,‘f0’,‘Cons(x,l)’] assume_tac Lrec_def >>
 drule $ iffLR Lind_cases >> 
 fs[Pa_eq_eq,Cons_NONNIL,Cons_eq_eq] >>
 qsspecl_then [‘p0’] (x_choosel_then ["l1","a1"] assume_tac) 
 Pair_has_comp >> fs[Pair_def'] >>
 qsuff_tac ‘a1 = Lrec(a0, f0) o l1’ 
 >-- (strip_tac >> arw[]) >>
 flip_tac >> arw[App_Lrec_Linds])
(form_goal “!A a0 X f0:X * A ->A l x. 
 Lrec(a0,f0) o Cons(x,l) = 
 f0 o Pa(x,Lrec(a0,f0) o l)”));


(*qform2IL [‘l:1->List(X)’] ‘r = Lrec(a0,f)’ cannot build*)
val Lrec_unique = prove_store("Lrec_unique",
e0
(rpt strip_tac >> irule FUN_EXT >>
 qby_tac
 ‘∃P. ∀a:1->List(X). r o a = Lrec(a0,f) o a ⇔ 
  P o a = TRUE’
 >-- (exists_tac (qform2IL [‘l:1->List(X)’] ‘r o l = Lrec(a0:1->A,f) o l’) >>
 rw[Eq_property_TRUE,o_assoc,p12_of_Pa,idL,idR,Pa_distr]) >>
 ind_with1 (List_induct |> qspecl [‘X’]) >>
 arw[Lrec_Nil,Lrec_Cons] >> rpt strip_tac >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Cons_def,GSYM o_assoc] >> arw[] >>
 rw[Prla_def,o_assoc,idL,p12_of_Pa,Pa_distr])
(form_goal
 “!A a0 X f:X * A->A r:List(X)->A. r o Nil(X) = a0 & 
  r o CONS(X) = f o Prla(id(X),r) ==> r = Lrec(a0,f)”));


val Lrec_Cons_eqn =
    Lrec_Cons |> rewr_rule[Cons_def] 
              |> spec_all
              |> qgenl [‘x’,‘l’]
              |> mp (FUN_EXT |> qspecl
                             [‘X * List(X)’,‘A’,‘Lrec(a0, f0:X * A->A) o CONS(X)’,
                                                              ‘f0 o Prla(id(X),Lrec(a0, f0:X * A->A))’] 
                             |> conv_rule
 (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[Pa_distr,Prla_def,p12_of_Pa,idL,o_assoc])
              |> rewr_rule[GSYM Prla_def
                           |> qspecl [‘X’,‘X’,‘id(X)’]
                           |> rewr_rule[idL]]
              |> qgenl [‘A’,‘a0’,‘X’,‘f0’]
              |> store_as "Lrec_Cons_eqn";

val LENGTH_def = qdefine_fsym ("LENGTH",[‘X’])
                              ‘Lrec(O,SUC o p2(X,N))’
                           |> gen_all 
                           |> store_as "LENGTH_def";
 
val Length_def = qdefine_fsym ("Length",[‘l:1->List(X)’])
                              ‘LENGTH(X) o l’
                           |> gen_all 
                           |> store_as "Length_def";

val Length_Nil = prove_store("Length_Nil",
e0
(rw[Length_def,LENGTH_def,Lrec_Nil])
(form_goal
 “!X. Length(Nil(X)) = O”));


val Length_Cons = prove_store("Length_Cons",
e0
(rw[Length_def,LENGTH_def,Lrec_Cons,o_assoc,Pa_distr,p12_of_Pa,
    Suc_def])
(form_goal
“!A a:1->A l. Length(Cons(a,l)) = Suc(Length(l))”));


 
(*do Map it in induction with num. use N_ind and hd and tl.*)
