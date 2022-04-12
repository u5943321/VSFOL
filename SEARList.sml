
local
val isL_cl = 
 “(ls = Empty(N * X) ==> IN(ls,isLs)) &
  (!ls0 x. IN(ls0,isLs) & 
           ls = Ins(Pair(Card(ls0),x),ls0) ==> IN(ls,isLs))”
in
val (isL_incond,x1) = mk_incond isL_cl;
val isLf_ex = mk_fex isL_incond x1;
val isLf_def = mk_fdef "isLf" isLf_ex;
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





val List_def = Thm_2_4 |> qspecl [‘Pow(N * X)’] 
                    |> fVar_sInst_th 
                       “P(a:mem(Pow(N * X)))” 
                       “IN(a:mem(Pow(N * X)),isLs(X))”
                    |> qSKOLEM "List" [‘X’] 
                    |> qSKOLEM "iL" [‘X’]
                    |> gen_all

val iL_Inj = List_def |> spec_all 
                      |> conjE1 |> gen_all
                      |> store_as "iL_Inj"; 


val isL_def = qdefine_psym("isL",[‘l:mem(Pow(N * X))’]) 
                          ‘IN(l,isLs(X))’
                          |> gen_all |> store_as "isL_def"; 

val isL_induct = prove_store("isL_induct",
e0
(rw[isL_def] >> strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘Pow(N * X)’]) >>
 arw[isL_ind])
(form_goal 
 “!X.P(Empty(N * X)) & 
  (!ls0 x:mem(X). P(ls0) ==>
    P(Ins(Pair(Card(ls0),x),ls0))) ==> 
  !l:mem(Pow(N * X)). isL(l) ==> P(l)”));
 


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

val Repl_def = qdefine_fsym ("Repl",[‘l:mem(List(X))’])
                            ‘App(iL(X),l)’
                            |> gen_all |> store_as "Repl_def";
 
val Nil_def = proved_th $
e0
(strip_tac >> uex_tac >>
 qspecl_then [‘X’] strip_assume_tac List_def >>
 first_assum (qspecl_then [‘Empty(N * X)’] assume_tac) >>
 fs[isL_Empty,GSYM isL_def] >>
 qexists_tac ‘b’ >> arw[Repl_def] >>
 fs[Inj_def])
(form_goal “!X. ?!l.Repl(l) = Empty(N * X)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Nil" [‘X’] |> gen_all
|> store_as "Nil_def";

val cons0_def = 
    qdefine_fsym ("cons0",[‘x:mem(X)’,‘l:mem(Pow(N * X))’])
    ‘Ins(Pair(Card(l),x:mem(X)),l)’

    
val cons1_def =
    fun_tm_compr (dest_var (rastt "xl:mem(X * Pow(N * X))"))
    (rastt "cons0(Fst(xl:mem(X * Pow(N * X))),Snd(xl))")
    |> qSKOLEM "cons1" [‘X’]
    |> qspecl [‘Pair(x:mem(X),l:mem(Pow(N * X)))’] 
    |> rewr_rule[Pair_def',cons0_def] 


(*Parallel product arrow*)
val Prla_def = 
    qdefine_fsym ("Prla",[‘f:A->B’,‘g:C->D’])
    ‘Pa(f o p1(A,C),g o p2(A,C))’
    |> gen_all |> store_as "Prla_def";

val Prla_Inj = prove_store("Prla_Inj",
e0
(rpt strip_tac >> fs[Inj_def,Prla_def] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[App_Pa,Pair_eq_eq,App_App_o,p12_of_Pair] >>
 rpt strip_tac >> first_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !C D g:C->D. Inj(g) ==>
 Inj(Prla(f,g))”));


val Id_Inj = prove_store("Id_Inj",
e0
(rw[Inj_def,Id_def])
(form_goal
 “!X. Inj(Id(X))”));

(*iL_isL should be automated*)
val iL_isL = prove_store("iL_isL",
e0
(rpt strip_tac >> 
 rw[isL_def] >> 
 qspecl_then [‘X’] assume_tac List_def >>
 fs[] >> qexists_tac ‘l’ >> rw[])
(form_goal “!X l. isL(App(iL(X),l))”)); 

val isL_Repl = List_def |> spec_all |> conjE2
                        |> rewr_rule[GSYM isL_def,
                                     GSYM Repl_def] 
                        |> gen_all 
                        |> store_as "isL_Repl";

val lift_cond2 = proved_th $
e0
(fconv_tac forall_cross_fconv >>
 rw[Prla_def,App_App_o,App_Pa,
    p12_of_Pair,Id_def,cons1_def] >>
 rpt strip_tac >>
 qsspecl_then [‘b’] assume_tac iL_isL >>
 drule isL_Ins >> rw[GSYM Repl_def,GSYM isL_Repl] >>
 fs[Repl_def])
(form_goal
 “!xl1:mem(X * List(X)).?l2.
 App(cons1(X) o Prla(Id(X),iL(X)),xl1) = App(iL(X),l2)”)


val lift_cond2' = proved_th $
e0
(assume_tac lift_cond2 >> strip_tac >> uex_tac >>
 first_x_assum (qspecl_then [‘xl1’] strip_assume_tac) >>
 qexists_tac ‘l2’ >> arw[] >> assume_tac iL_Inj >>
 fs[Inj_def] >> rpt strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “!xl1:mem(X * List(X)).?!l2.
 App(cons1(X) o Prla(Id(X),iL(X)),xl1) = App(iL(X),l2)”)

val CONS_def = P2fun |> qspecl [‘X * List(X)’,‘List(X)’]
                     |> fVar_sInst_th 
                        “P(xl1:mem(X * List(X)),
                           l2:mem(List(X)))”
                        “App(cons1(X) o Prla(Id(X),iL(X)),xl1) = App(iL(X),l2)”
                                                                                   |> C mp lift_cond2'
                     |> qSKOLEM "CONS" [‘X’] 
                     |> qspecl 
                     [‘Pair(x:mem(X),l:mem(List(X)))’,
                      ‘App(CONS(X),Pair(x:mem(X),l:mem(List(X))))’]
                     |> rewr_rule[App_App_o,Prla_def,App_Pa,
                                  p12_of_Pair,Id_def,
                                  cons1_def,GSYM Repl_def]
                     |> gen_all
                     |> store_as "CONS_def"; 


val Cons_def = 
    qdefine_fsym ("Cons",[‘x:mem(X)’,‘l:mem(List(X))’])
    ‘App(CONS(X),Pair(x,l))’ 
    |> gen_all |> store_as "Cons_def";

val Repl_Cons = CONS_def |> rewr_rule[GSYM Cons_def]
                         |> GSYM
                         |> store_as "Repl_Cons";

(*should automate*)
val Repl_eq_eq = prove_store("Repl_eq_eq",
e0
(rpt strip_tac >> rw[Repl_def] >> irule Inj_eq_eq >>
 rw[iL_Inj])
(form_goal “!X l1:mem(List(X)) l2.
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



val List_induct = prove_store("List_induct",
e0
(strip_tac >> disch_tac >>
 qsuff_tac ‘!nxs:mem(Pow(N * X)). isL(nxs) ==> isL(nxs) &
 (!l. Repl(l) = nxs ==> P(l))’
 >-- (strip_tac >>
     qby_tac ‘!nxs:mem(Pow(N * X)). isL(nxs) ==>
                      (!l. Repl(l) = nxs ==> P(l))’ 
     >-- (rpt strip_tac >> first_x_assum drule >>
          rfs[] >> first_x_assum irule >> arw[]) >>
     strip_tac >> first_x_assum irule >>
     qexists_tac ‘Repl(l)’ >> rw[isL_Repl] >>
     qexists_tac ‘l’ >> rw[]) >>
 ind_with (isL_induct |> qspecl [‘X’]) >>
 rw[isL_Empty] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     qsuff_tac ‘l = Nil(X)’ >-- (strip_tac >> arw[]) >>
     irule $ iffLR Repl_Empty_uex >> arw[]) >>
 rpt gen_tac >> disch_tac >>
 pop_assum strip_assume_tac >>
 qby_tac ‘isL(Ins(Pair(Card(ls0), x), ls0))’ 
 >-- (irule isL_Ins >> arw[]) >> arw[] >>
 rpt strip_tac >>
 qby_tac ‘?l0. Repl(l0) = ls0’ 
 >-- (fs[isL_Repl] >> qexists_tac ‘b’ >> rw[]) >>
 pop_assum strip_assume_tac >>
 first_x_assum drule >>
 qsuff_tac ‘l = Cons(x,l0)’ 
 >-- (strip_tac  >> last_x_assum strip_assume_tac >>
      arw[] >> first_x_assum irule >> arw[]) >>
 rw[GSYM Repl_eq_eq] >> arw[Repl_Cons])
(form_goal
 “!X. P(Nil(X)) & 
      (!l:mem(List(X)). P(l) ==> !x. P(Cons(x,l))) ==>
     !l:mem(List(X)).P(l) ”));

val Fin_Repl = prove_store("Fin_Repl",
e0
(strip_tac >> ind_with (List_induct |> qspecl [‘X’]) >>
 rw[Nil_def,Fin_Empty,Repl_Cons] >>
 rpt strip_tac >> drule Fin_Ins >> arw[])
(form_goal
 “!X l:mem(List(X)). Fin(Repl(l))”));

val isL_Card_NOTIN0 = prove_store("isL_Card_NOTIN0",
e0
(strip_tac >> ind_with (List_induct |> qspecl [‘X’]) >>
 rw[Nil_def,Empty_def,Repl_Cons,Ins_def,Pair_eq_eq] >>
 rpt strip_tac (* 2 *)
 >-- (arw[] >> qsspecl_then [‘l’] assume_tac Fin_Repl >>
     drule Card_Ins >> 
     qby_tac ‘~(IN(Pair(Card(Repl(l)),x), Repl(l)))’ 
     >-- (ccontra_tac >> first_x_assum drule >>
          fs[Lt_def]) >>
     first_x_assum drule >> arw[Lt_Suc]) >>
 first_assum drule >>
 irule Lt_trans >>
 qexists_tac ‘Card(Repl(l))’ >> arw[] >>
 qsspecl_then [‘l’] assume_tac Fin_Repl >>
 drule Card_Ins >> 
 qby_tac ‘~(IN(Pair(Card(Repl(l)),x), Repl(l)))’(* repeated *)
 >-- (ccontra_tac >> first_x_assum drule >>
                  fs[Lt_def]) >>
 first_x_assum drule >>
 arw[Lt_Suc])
(form_goal
 “!X l n x:mem(X). IN(Pair(n,x),Repl(l)) ==> 
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
 ‘Pair(Card(Repl(l1)), a1) = Pair(Card(Repl(l2)), a2) & 
  Repl(l1) = Repl(l2)’
 >-- (rw[Pair_eq_eq,Repl_eq_eq] >> rpt strip_tac >> arw[]) >>
 irule Ins_eq_eq >> arw[] >>
 qby_tac
 ‘~IN(Pair(Card(Repl(l1)), a1), Repl(l1)) & 
  ~IN(Pair(Card(Repl(l2)), a2), Repl(l2))’
 >-- (strip_tac >> ccontra_tac >> drule isL_Card_NOTIN0 >>
      fs[Lt_def]) >> arw[] >> 
 pop_assum strip_assume_tac >>
 qby_tac ‘Card(Repl(l2)) = Card(Repl(l1))’ 
 >-- (ccontra_tac >>
      qsuff_tac
      ‘~(Card(Ins(Pair(Card(Repl(l1)), a1), Repl(l1))) =
         Card(Ins(Pair(Card(Repl(l2)), a2), Repl(l2))))’
      >-- rfs[] >>
      qby_tac
      ‘Card(Ins(Pair(Card(Repl(l1)), a1), Repl(l1))) = 
       Suc(Card(Repl(l1))) & 
       Card(Ins(Pair(Card(Repl(l2)), a2), Repl(l2))) = 
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
 first_x_assum drule >> fs[Pair_eq_eq])
(form_goal
 “!X x1:mem(X) l1 x2 l2.Cons(x1,l1) = Cons(x2,l2) <=> (x1 = x2 & l1 = l2)”));



val Cons_or_Nil = prove_store("Cons_or_Nil",
e0
(strip_tac >> ind_with (List_induct |> qspecl [‘X’]) >>
 rw[Cons_NONNIL] >> rpt strip_tac >>
 (qexistsl_tac [‘x’,‘l’] >> rw[]))
(form_goal
 “!X l:mem(List(X)). l = Nil(X) | ?x0 l0. l = Cons(x0,l0)”));




val Cons_xor_Nil = prove_store("Cons_xor_Nil",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qsspecl_then [‘l’] strip_assume_tac Cons_or_Nil >>
 qexistsl_tac [‘x0’,‘l0’] >> arw[]) >>
 arw[Cons_NONNIL])
(form_goal
 “!X l:mem(List(X)). ~(l = Nil(X))<=> ?x0 l0. l = Cons(x0,l0)”));






local
val Lind_cl = 
 “(p = Pair(Nil(X),a0:mem(A)) ==> IN(p,Lind)) &
  (!p0:mem(List(X) * A) x:mem(X).
   IN(p0,Lind) & 
        p = Pair(Cons(x,Fst(p0)),
            App(f0:X * A ->A,Pair(x,Snd(p0))))
    ==> IN(p,Lind))”
in
val (Lind_incond,x1) = mk_incond Lind_cl;
val Lindf_ex = mk_fex Lind_incond x1;
val Lindf_def = mk_fdef "Lindf" Lindf_ex;
val Lindf_monotone = mk_monotone Lindf_def;
val Lind's_def = mk_prim Lindf_def;
val Linds_def = mk_LFP (rastt "Lind's(a0:mem(A),f0:X * A->A)");
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


(*exactly same proof as Nind_uex*)
val Lind_uex = prove_store("Lind_uex",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 ind_with (List_induct |> qspecl [‘X’]) >> strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘a0’ >>
      rw[Lind_rules] >> once_rw[Lind_cases] >>
      rw[Pair_eq_eq,GSYM Cons_NONNIL] >> rpt strip_tac) >>
 rpt strip_tac >> uex_tac >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘App(f0,Pair(x,a))’ >>
 drule (Lind_rules |> conjE2) >> fs[Pair_def'] >>
 rpt strip_tac >> drule $ iffLR Lind_cases >>
 fs[Pair_eq_eq,Cons_NONNIL] >>
 qsspecl_then [‘p0’] (x_choosel_then ["l1","a1"] strip_assume_tac) Pair_has_comp >> fs[Pair_def',Cons_eq_eq] >>
 qby_tac ‘a1 = a’ 
 >-- (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal
 “!A a0:mem(A) X f0: X * A ->A l:mem(List(X)). ?!a. IN(Pair(l,a),Linds(a0,f0))”));



val Lrec_def = P2fun' |> qspecl [‘List(X)’,‘A’] 
                      |> fVar_sInst_th “P(l:mem(List(X)),
                                          a:mem(A))”
                          “IN(Pair(l,a),
                              Linds(a0:mem(A),f0:X * A ->A))”
                      |> C mp (Lind_uex |> spec_all
                                        |> qgen ‘l’)
                      |> qSKOLEM "Lrec" [‘a0’,‘f0’]
                      |> qgenl [‘A’,‘a0’,‘X’,‘f0’]
                      |> store_as "Lrec_def";


val Lrec_Nil = prove_store("Lrec_Nil",
e0
(rpt strip_tac >>
 qsspecl_then [‘a0’,‘f0’,‘Nil(X)’] assume_tac Lrec_def >>
 drule $ iffLR Lind_cases >>
 fs[Pair_eq_eq,GSYM Cons_NONNIL])
(form_goal “!A a0 X f0:X * A -> A. 
 App(Lrec(a0,f0),Nil(X)) = a0”));



val App_Lrec_Linds = prove_store("App_Lrec_Linds",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >--
(pop_assum (assume_tac o GSYM) >> arw[Lrec_def]) >>
qsspecl_then [‘a0’,‘f0’,‘l’] assume_tac Lrec_def >>
qsspecl_then [‘a0’,‘f0’,‘l’] assume_tac Lind_uex >>
pop_assum (strip_assume_tac o uex_expand) >>
qby_tac ‘App(Lrec(a0, f0), l) = a' & a = a'’ 
>-- (strip_tac >> first_x_assum irule >> arw[]) >>
arw[])
(form_goal “!A a0 X f0:X * A ->A.
!l a. App(Lrec(a0,f0),l) = a <=> 
IN(Pair(l,a),Linds(a0,f0))”));


val Lrec_Cons = prove_store("Lrec_Cons",
e0
(rpt strip_tac >>
 qsspecl_then [‘a0’,‘f0’,‘Cons(x,l)’] assume_tac Lrec_def >>
 drule $ iffLR Lind_cases >> 
 fs[Pair_eq_eq,Cons_NONNIL,Cons_eq_eq] >>
 qsspecl_then [‘p0’] (x_choosel_then ["l1","a1"] assume_tac) 
 Pair_has_comp >> fs[Pair_def'] >>
 qsuff_tac ‘a1 = App(Lrec(a0, f0), l1)’ 
 >-- (strip_tac >> arw[]) >>
 flip_tac >> arw[App_Lrec_Linds])
(form_goal “!A a0 X f0:X * A ->A l x. 
 App(Lrec(a0,f0),Cons(x,l)) = 
 App(f0,Pair(x,App(Lrec(a0,f0),l)))”));



val Lrec_unique = prove_store("Lrec_unique",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT] >> 
 ind_with (List_induct |> qspecl [‘X’]) >>
 arw[Lrec_Nil,Lrec_Cons] >> rpt strip_tac >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[GSYM App_App_o,Cons_def] >> arw[] >>
 rw[App_App_o,Prla_def,App_Pa,Id_def,p12_of_Pair])
(form_goal
 “!A a0 X f:X * A->A r:List(X)->A. App(r,Nil(X)) = a0 & 
  r o CONS(X) = f o Prla(Id(X),r) ==> r = Lrec(a0,f)”));


val Lrec_Cons_eqn =
    Lrec_Cons |> rewr_rule[GSYM App_App_o,Cons_def] 
              |> spec_all
              |> qgenl [‘x’,‘l’]
              |> rewr_rule[App_App_o]
              |> mp (FUN_EXT |> qspecl
                             [‘X * List(X)’,‘A’,‘Lrec(a0, f0:X * A->A) o CONS(X)’,
                                                              ‘f0 o Prla(Id(X),Lrec(a0, f0:X * A->A))’] 
                             |> iffLR
                             |> conv_rule
 (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[App_App_o,App_Pa,Prla_def,Id_def,p12_of_Pair])
              |> rewr_rule[GSYM Prla_def]
              |> qgenl [‘A’,‘a0’,‘X’,‘f0’]
              |> store_as "Lrec_Cons_eqn";

val LENGTH_def = qdefine_fsym ("LENGTH",[‘X’])
                              ‘Lrec(O,SUC o p2(X,N))’
                           |> gen_all 
                           |> store_as "LENGTH_def";
 
val Length_def = qdefine_fsym ("Length",[‘l:mem(List(X))’])
                              ‘App(LENGTH(X),l)’
                           |> gen_all 
                           |> store_as "Length_def";

val Length_Nil = prove_store("Length_Nil",
e0
(rw[Length_def,LENGTH_def,Lrec_Nil])
(form_goal
 “!X. Length(Nil(X)) = O”));


val Length_Cons = prove_store("Length_Cons",
e0
(rw[Length_def,LENGTH_def,Lrec_Cons,App_App_o,p12_of_Pair,
    Suc_def])
(form_goal
“!A a:mem(A) l. Length(Cons(a,l)) = Suc(Length(l))”));


 
(*do Map it in induction with num. use N_ind and hd and tl.*)
