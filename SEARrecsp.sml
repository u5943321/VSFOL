
val InjN_def = proved_th $
e0
(strip_tac >> irule
 (P2fun_uex |> qspecl [‘N’,‘Pow(N * A)’] 
 |> fVar_sInst_th “P(n0:mem(N),na:mem(Pow(N * A)))”
    “(!n:mem(N) a:mem(A).IN(Pair(n,a),na) <=> n = n0)”) >>
 strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘N * A’] 
 |> fVar_sInst_th “P(na:mem(N * A))” “Fst(na:mem(N * A)) = x”
 |> conv_rule (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[Pair_def'])
)
(form_goal “!A. ?!injN:N -> Pow(N * A).
 !n0. (!n a.IN(Pair(n,a),App(injN,n0)) <=> n = n0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "InjN" [‘A’] |> gen_all 


val InjA_def = proved_th $
e0
(strip_tac >> irule
 (P2fun_uex |> qspecl [‘A’,‘Pow(N * A)’] 
 |> fVar_sInst_th “P(a0:mem(A),na:mem(Pow(N * A)))”
    “(!n:mem(N) a:mem(A).IN(Pair(n,a),na) <=> a = a0)”) >>
 strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘N * A’] 
 |> fVar_sInst_th “P(na:mem(N * A))” “Snd(na:mem(N * A)) = x”
 |> conv_rule (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[Pair_def']))
(form_goal “!A. ?!injA:A -> Pow(N * A).
 !a0. (!n a.IN(Pair(n,a),App(injA,a0)) <=> a = a0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "InjA" [‘A’] |> gen_all 

val Even_def = qdefine_psym("Even",[‘n:mem(N)’]) ‘∃n0. n = Mul(Suc(Suc(O)),n0)’
val Odd_def = qdefine_psym("Odd",[‘n:mem(N)’]) ‘~Even(n)’


(*pretend div2 is defined*)
val Div2_def = qdefine_fsym("Div2",[‘n:mem(N)’]) ‘n’


val num1_def = qdefine_fsym("num1",[]) ‘Suc(O)’
val num2_def = qdefine_fsym("num2",[]) ‘Suc(num1)’
val num3_def = qdefine_fsym("num3",[]) ‘Suc(num2)’
val num4_def = qdefine_fsym("num4",[]) ‘Suc(num3)’


                          
val InjUU_def = proved_th $
e0
(strip_tac >> irule
 (P2fun_uex |> qspecl [‘Pow(N * A) * Pow(N * A)’,‘Pow(N * A)’] 
 |> fVar_sInst_th “P(u12:mem(Pow(N * A) * Pow(N * A)), s:mem(Pow(N * A)))”
    “∀n a. IN(Pair(n,a),s:mem(Pow(N * A))) ⇔ 
    ((Even(n) & IN(Pair(Div2(n),a),Fst(u12))) | 
     (Odd(n) & IN(Pair(Div2(n),a),Snd(u12))))”
 |> conv_rule (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[Pair_def']) >>
 rpt strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘N * A’]
 |> fVar_sInst_th “P(na:mem(N * A))”
 “(Even(Fst(na)) & IN(Pair(Div2(Fst(na)),Snd(na)),a:mem(Pow(N * A)))) | 
 (Odd(Fst(na)) & IN(Pair(Div2(Fst(na)),Snd(na)),b))”
 |> conv_rule (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[Pair_def']))
(form_goal “∀A.∃!f:Pow(N * A) * Pow(N * A) -> Pow(N * A).
 ∀u1 u2. ∀n a. IN(Pair(n,a),App(f,Pair(u1,u2))) ⇔ 
  ((Even(n) & IN(Pair(Div2(n),a),u1)) | 
   (Odd(n) & IN(Pair(Div2(n),a),u2)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "InjUU" [‘A’]

val injUU_def = 
    qdefine_fsym("injUU",[‘u1:mem(Pow(N * A))’,‘u2:mem(Pow(N * A))’]) 
                ‘App(InjUU(A),Pair(u1,u2))’ 

val Even_not_Odd = prove_store("Even_not_Odd",
e0
cheat
(form_goal “!n. Even(n) <=> ~Odd(n)”));



val Odd_not_Even = prove_store("Odd_not_Even",
e0
cheat
(form_goal “!n. Odd(n) <=> ~Even(n)”));


val injUU_char = prove_store("injUU_char",
e0
(rpt strip_tac (* 2 *)
 >-- (rw[injUU_def,InjUU_def] >> arw[Odd_not_Even]) >> 
 rw[injUU_def,InjUU_def] >> arw[Even_not_Odd])
(form_goal “
 (!n. Even(n) ==> (!A u1:mem(Pow(N * A)) u2 a. IN(Pair(n,a),injUU(u1,u2)) <=> IN(Pair(Div2(n),a),u1))) & 
 (!n. Odd(n) ==> (!A u1:mem(Pow(N * A)) u2 a. IN(Pair(n,a),injUU(u1,u2)) <=> IN(Pair(Div2(n),a),u2)))”));

val injUU_Even = injUU_char |> conjE1
                            

val InjUU_Inj = prove_store("InjUU_Inj",
e0
(strip_tac >> rw[Inj_def] >> rpt strip_tac >>
 ccontra_tac >>
 qsuff_tac ‘~(App(InjUU(A), x1) = App(InjUU(A), x2))’
 >-- arw[] >>
 last_x_assum (K all_tac) >>
 qsspecl_then [‘x1’] (x_choosel_then ["u1","u2"] assume_tac) Pair_has_comp>>
 qsspecl_then [‘x2’] (x_choosel_then ["u3","u4"] assume_tac) Pair_has_comp>>
 fs[] >> fs[Pair_eq_eq] >> rw[GSYM injUU_def] >> 
 qby_tac ‘~(u1 = u3) | ~(u2 = u4)’ >-- cheat >>
 pop_assum strip_assume_tac >>
 last_x_assum (K all_tac) (* 2 *)
 >-- (fs[GSYM IN_EXT_iff] >> 
     qby_tac ‘(?n a. IN(Pair(n,a),u1) & ~(IN(Pair(n,a),u3))) | 
              (?n a. IN(Pair(n,a),u3) & ~(IN(Pair(n,a),u1)))’
     >-- cheat >> pop_assum strip_assume_tac (* 2 *)
     >-- (qsuff_tac
         ‘?n a. IN(Pair(n,a),injUU(u1,u2)) & ~IN(Pair(n,a),injUU(u3,u4))’
         >-- cheat >>
         qexistsl_tac [‘Mul(num2,n)’,‘a’] >>
         qby_tac ‘Even(Mul(num2,n))’ >-- cheat >>
         drule injUU_Even >> arw[] >>
         qby_tac ‘Div2(Mul(num2, n)) = n’ >-- cheat >> arw[])
     >-- cheat (*same*)) >>
 cheat)
(form_goal “!A. Inj(InjUU(A))”));

val injN_def = qdefine_fsym("injN",[‘A’,‘n:mem(N)’]) ‘App(InjN(A),n)’
val injA_def = qdefine_fsym("injA",[‘a:mem(A)’]) ‘App(InjA(A),a)’ 






val Lf0_def = qdefine_fsym("Lf0",[‘A’]) ‘injN(A,O)’

(*
val injN2U_def = proved_th $
e0
cheat
(form_goal “∀A.∃!f:Pow(N * N * A) -> Pow(N * A).
f = f”)
|> spec_all |> uex2ex_rule |> qSKOLEM "injN2U" [‘A’]
*)


val injN2U_def = proved_th $
e0
cheat
(form_goal “∀A f:N -> Pow(N * A).∃!f1: mem(Pow(N * A)).
f1 = f1”)
|> spec_all |> uex2ex_rule |> qSKOLEM "injN2U" [‘f’]

(*
val injN2U_def = 
    qdefine_fsym("injN2U",[‘f:mem(Pow(N * N * A))’]) 
                ‘App(InjN2U(A),f)’ 
*)

val Nd0_def = qdefine_fsym("Nd0",[‘n:mem(N)’,‘a:mem(A)’,
 ‘f:N -> Pow(N * A)’]) ‘injUU(injN(A,Suc(n)),injUU(injA(a),injN2U(f)))’ 


val f = 
 “(nas = Lf0(A) ==> IN(nas,trees)) &
  (!f. (!m.IN(App(f,m),trees)) ==>
   !n a. IN(Nd0(n,a,f),trees))”

val istree_cl = 
 “(nas = Lf0(A) ==> IN(nas,istrees)) &
  (!f n a. (!m.IN(App(f,m),istrees)) & nas = Nd0(n,a,f) ==>
   IN(nas,istrees))”


val (istree_incond,x1) = mk_incond istree_cl;
val istreef_ex = mk_fex istree_incond x1;
val istreef_def = mk_fdef "istreef" istreef_ex;
val istreef_monotone = proved_th $
e0
cheat
(form_goal
 “!s1 s2. SS(s1,s2) ==>
 SS(App(istreef(A),s1),App(istreef(A),s2))”);
val istree's_def = mk_prim istreef_def;
val istrees_def = mk_LFP (rastt "istree's(A)");
val istrees_cond = mk_cond istrees_def istree's_def;
val istrees_SS = mk_SS istrees_def istree's_def;
val istree_rules0 = mk_rules istreef_monotone istrees_SS istrees_cond;
val istree_cases0 = mk_cases istreef_monotone istree_rules0 istrees_cond;
val istree_ind0 = mk_ind istrees_cond;
val istree_ind1 = mk_ind1 istreef_def istree_ind0;
val istree_ind2 = mk_ind2 istree_ind1;
val istree_cases1 = mk_case1 istreef_def istree_cases0;
val istree_rules1 = mk_rules1 istreef_def istree_rules0;
val istree_rules2 = mk_rules2 istree_rules1;
val istree_rules3 = mk_rules3 istree_rules2;



val istree_ind = istree_ind2 |> store_as "istree_ind";
val istree_cases = istree_cases1 |> store_as "istree_cases";
val istree_rules = istree_rules3 |> store_as "istree_rules";



val Tree_def = Thm_2_4  |> qspecl [‘Pow(N * A)’]
                         |> fVar_sInst_th “P(f:mem(Pow(N * A)))”
                         “istree(f:mem(Pow(N * A)))”
                         |> qSKOLEM "Tree" [‘A’]
                         |> qSKOLEM "iT" [‘A’]
                         |> gen_all


val iT_Inj = recsp_def |> spec_all 
                      |> conjE1 |> gen_all
                      |> store_as "iT_Inj"; 


val istree_def = qdefine_psym("istree",[‘t:mem(Pow(N * A))’])
‘IN(t,istrees(A))’ |> gen_all 


val istree_induct = prove_store("istree_induct",
e0
(rw[istree_def] >> strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘Pow(N * A)’]) >> arw[] >>
 arw[istree_ind])
(form_goal 
 “!A.P(Lf0(A)) & 
  (!f n a:mem(A). (!m.P(App(f,m))) ==>
    P(Nd0(n,a,f))) ==>
  !f0:mem(Pow(N * A)). istree(f0) ==> P(f0)”));
 

val istree_Lf0 = prove_store("istree_Lf0",
e0
(rw[istree_def,istree_rules])
(form_goal
 “!A. istree(Lf0(A))”)); 


val istree_Nd0 = istree_rules |> spec_all |> conjE2 
                        |> rewr_rule[GSYM istree_def]
                        |> spec_all |> undisch 
                        |> gen_all |> disch_all
                        |> gen_all |> store_as "istree_Nd0";


val Rept_def = qdefine_fsym ("Rept",[‘t:mem(Tree(A))’])
                            ‘App(iT(A),t)’
                            |> gen_all |> store_as "Rept_def";

val Rept_eq_eq = prove_store("Rept_eq_eq",
e0
(cheat)
(form_goal “!A t1:mem(Tree(A)) t2.Rept(t1) = Rept(t2) <=> t1 = t2”));
 
val Lf_def = proved_th $
e0
(strip_tac >> uex_tac >>
 qspecl_then [‘A’] strip_assume_tac Tree_def >>
 first_assum (qspecl_then [‘Lf0(A)’] assume_tac) >>
 fs[istree_Lf0,GSYM istree_def] >>
 qexists_tac ‘b’ >> arw[Rept_def] >>
 fs[Inj_def])
(form_goal “!A. ?!t.Rept(t) = Lf0(A)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Lf" [‘A’] |> gen_all
|> store_as "Lf_def";


val istree_Rept = Tree_def |> spec_all |> conjE2
                        |> rewr_rule[GSYM istree_def,
                                     GSYM Rept_def] 
                        |> gen_all 
                        |> store_as "istree_Rept";

val Nd_def = proved_th $
e0
(rpt strip_tac >>
qsuff_tac ‘?nd0. Nd0(n,a,iT(A) o f) = Rept(nd0)’
>-- (strip_tac >> uex_tac >> qexists_tac ‘nd0’ >>
    arw[] >> rpt strip_tac >> fs[Rept_eq_eq]) >>
rw[GSYM istree_Rept] >>
irule istree_Nd0 >> rw[istree_Rept,Rept_def,App_App_o] >>
rpt strip_tac >> qexists_tac ‘App(f,m)’ >> rw[])
(form_goal
“!n a f:N -> Tree(A). ?!nd0. 
 Nd0(n,a,iT(A) o f) = Rept(nd0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Nd" [‘n’,‘a’,‘f’]

(*
val Rept_istree = prove_store("Rept_istree",
e0
()
(form_goal “!t:mem(Tree(A)). istree(Rept)”));
*)


val Rept_Lf0_uex = prove_store("Rept_Lf0_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[Lf_def] >>
 rw[GSYM Rept_eq_eq] >> arw[Lf_def])
(form_goal
 “!A t. Rept(t) = Lf0(A) <=> t = Lf(A)”));


val Tree_induct = prove_store("Tree_induct",
e0
(strip_tac >> disch_tac >>
 qsuff_tac ‘!nas:mem(Pow(N * A)). istree(nas) ==> istree(nas) &
 (!t. Rept(t) = nas ==> P(t))’
 >-- (strip_tac >>
     qby_tac ‘!nas:mem(Pow(N * A)). istree(nas) ==>
                      (!t. Rept(t) = nas ==> P(t))’ 
     >-- (rpt strip_tac >> first_x_assum drule >>
          rfs[] >> first_x_assum irule >> arw[]) >>
     strip_tac >> first_x_assum irule >>
     qexists_tac ‘Rept(t)’ >> rw[istree_Rept] >>
     qexists_tac ‘t’ >> rw[]) >>
 ind_with (istree_induct |> qspecl [‘A’]) >>
 rw[istree_Lf0] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     qsuff_tac ‘t = Lf(A)’ >-- (strip_tac >> arw[]) >>
     irule $ iffLR Rept_Lf0_uex >> arw[]) >>
 rpt gen_tac >> disch_tac >>
 pop_assum strip_assume_tac >>
 qby_tac ‘istree(Nd0(n, a, f))’ 
 >-- (irule istree_Nd0 >> arw[]) >> arw[] >>
 rpt strip_tac >>
 qby_tac ‘?f0. f = iT(A) o f0’ 
 >-- cheat (*use assumption !(m : mem(N)).
               istree(App(f, m#))  ...*)>>
 pop_assum strip_assume_tac >> 
 qsuff_tac ‘t = Nd(n,a,f0)’ 
 >-- (strip_tac  >> last_x_assum strip_assume_tac >>
      arw[] >> first_x_assum irule >> arw[] >>
      rpt strip_tac >>
      fs[App_App_o] >>
      first_x_assum (qspecl_then [‘m’] strip_assume_tac) >>
      first_x_assum irule >> rw[Rept_def]) >>
 rw[GSYM Rept_eq_eq] >> arw[GSYM Nd_def])
(form_goal
 “!A. P(Lf(A)) & 
      (!n a:mem(A) f.(!m.P(App(f,m))) ==> P(Nd(n,a,f))) ==>
  !t:mem(Tree(A)).P(t) ”));

(*tree-tuple*)
val Fnap_def = qdefine_fsym("Fnap",[‘Fn:N * A * Exp(N,Tree(A)) * Exp(N,X) ->X’,‘n:mem(N)’,‘a:mem(A)’,‘f:N->Tree(A)’,‘y:N ->X’]) ‘App(Fn,Pair(n,Pair(a,Pair(Tpm(f),Tpm(y)))))’


local
val Tind_cl = 
 “(p = Pair(Lf(A),l:mem(X)) ==> IN(p,Tind)) &
  (!n a f:N->Tree(A) y. 
   (!m.IN(Pair(App(f,m),App(y,m)),Tind)) &
   p = Pair(Nd(n,a,f),Fnap(Fn,n,a,f,y)) ==>
   IN(p,Tind))”
in
val (Tind_incond,x1) = mk_incond Tind_cl;
val Tindf_ex = mk_fex Tind_incond x1;
val Tindf_def = mk_fdef "Tindf" Tindf_ex;
val Tindf_monotone = proved_th $
e0
cheat
(form_goal
 “!s1 s2. SS(s1,s2) ==>
 SS(App(Tindf(Fn:N * A * Exp(N,Tree(A)) * Exp(N,X) ->X,l:mem(X)),s1),App(Tindf(Fn,l),s2))”);
val Tind's_def = mk_prim Tindf_def;
val Tinds_def = mk_LFP (rastt "Tind's(Fn:N * A * Exp(N,Tree(A)) * Exp(N,X) ->X,l:mem(X))");
val Tinds_cond = mk_cond Tinds_def Tind's_def;
val Tinds_SS = mk_SS Tinds_def Tind's_def;
val Tind_rules0 = mk_rules Tindf_monotone Tinds_SS Tinds_cond;
val Tind_cases0 = mk_cases Tindf_monotone Tind_rules0 Tinds_cond;
val Tind_ind0 = mk_ind Tinds_cond;
val Tind_ind1 = mk_ind1 Tindf_def Tind_ind0;
val Tind_ind2 = mk_ind2 Tind_ind1; 
val Tind_cases1 = mk_case1 Tindf_def Tind_cases0; 
val Tind_rules1 = mk_rules1 Tindf_def Tind_rules0; 
val Tind_rules2 = mk_rules2 Tind_rules1; 
val Tind_rules3 = mk_rules3 Tind_rules2;
end

val Tind_ind = Tind_ind2 |> store_as "Tind_ind";
val Tind_cases = Tind_cases1 |> store_as "Tind_cases";
val Tind_rules = Tind_rules3 |> store_as "Tind_rules";

val Nd_NONLF = prove_store("Nd_NONLF",
e0
cheat
(form_goal “!A n a f . ~(Nd(n,a,f) = Lf(A))”));

val Nd_eq_eq = prove_store("Nd_eq_eq",
e0
(cheat)
(form_goal “!A n1 a1:mem(A) f1 n2 a2 f2.
  Nd(n1,a1,f1) = Nd(n2,a2,f2) <=> n1 = n2 & a1 = a2 & f1 = f2 ”));

val Tind_uex = prove_store("Tind_uex",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 ind_with (Tree_induct |> qspecl [‘A’]) >> strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘l’ >>
      rw[Tind_rules] >> once_rw[Tind_cases] >>
      rw[Pair_eq_eq,GSYM Nd_NONLF] >> rpt strip_tac) >>
 rpt strip_tac >> uex_tac >>
 qby_tac
 ‘?j:N->X. !n. IN(Pair(App(f,n),App(j,n)),Tinds(Fn,l))’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 drule (Tind_rules |> conjE2 |> spec_all 
                   |> undisch |> gen_all
                   |> disch_all) >> 
 qexists_tac ‘Fnap(Fn, n, a, f, j)’ >> arw[] >>
 rpt strip_tac >> drule $ iffLR Tind_cases >>
 fs[Pair_eq_eq,Nd_NONLF,Nd_eq_eq] >>
 qby_tac ‘y = j’ >>
 fs[] >> cheat)
(form_goal “!X l:mem(X) A  Fn  t:mem(Tree(A)). ?!e. IN(Pair(t,e),Tinds(Fn,l))”));


val Trec_def = P2fun' |> qspecl [‘Tree(A)’,‘X’] 
                      |> fVar_sInst_th “P(t:mem(Tree(A)),
                                          x:mem(X))”
                          “IN(Pair(t:mem(Tree(A)),x),
                              Tinds(Fn,l:mem(X)))”
                      |> C mp (Tind_uex |> spec_all
                                        |> qgen ‘t’)
                      |> qSKOLEM "Trec" [‘Fn’,‘l’]
                      |> qgenl [‘X’,‘l’,‘A’,‘Fn’]
                      |> store_as "Trec_def";



val Trec_Lf = prove_store("Trec_Lf",
e0
(rpt strip_tac >>
 qsspecl_then [‘l’,‘Fn’,‘Lf(A)’] assume_tac Trec_def >>
 drule $ iffLR Tind_cases >>
 fs[Pair_eq_eq,GSYM Nd_NONLF])
(form_goal “!X l:mem(X) A  Fn. 
 App(Trec(Fn,l),Lf(A)) = l”));


val App_Trec_Tinds = prove_store("App_Trec_Tinds",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >--
(pop_assum (assume_tac o GSYM) >> arw[Trec_def]) >>
qsspecl_then [‘l’,‘Fn’,‘t’] assume_tac Trec_def >>
qsspecl_then [‘l’,‘Fn’,‘t’] assume_tac Tind_uex >>
pop_assum (strip_assume_tac o uex_expand) >>
first_assum rev_drule >> arw[] >>
first_assum irule >> arw[])
(form_goal “!X l:mem(X) A  Fn.
!t:mem(Tree(A)) x. App(Trec(Fn,l),t) = x <=> 
IN(Pair(t,x),Tinds(Fn,l))”));


val Trec_Nd = prove_store("Trec_Nd",
e0
(rpt strip_tac >>
 qsspecl_then [‘l’,‘Fn’,‘Nd(n,a,f)’] assume_tac Trec_def >>
 drule $ iffLR Tind_cases >> 
 fs[Pair_eq_eq,Nd_NONLF,Nd_eq_eq] >>
 qsuff_tac ‘y = Trec(Fn, l) o f'’ 
 >-- (strip_tac >> arw[]) >>
 flip_tac >> irule $ iffLR FUN_EXT >>
 rw[App_App_o] >>  arw[App_Trec_Tinds])
(form_goal “!X l:mem(X) A  Fn n a:mem(A) f. 
 App(Trec(Fn,l),Nd(n,a,f)) = 
 Fnap(Fn,n,a,f,Trec(Fn,l) o f)”));


val TNull_def = proved_th $
e0
cheat
(form_goal “!A. ?!f:N->Tree(A). !n. App(f,n) = Lf(A)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "TNull" [‘A’]

val Bot0_def = qdefine_fsym("Bot0",[‘A’])
‘Nd(O,NONE(A),TNull(A+1))’


val Var0_def = qdefine_fsym("Var0",[‘a:mem(A)’])
‘Nd(num1,SOME(a),TNull(A+1))’


val T1arg_def = 
proved_th $
e0
cheat
(form_goal “!A t. ?!f:N->Tree(A). 
 App(f,O) = t & 
!n. App(f,Suc(n)) = Lf(A)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "T1arg" [‘t’]

val Neg0_def = qdefine_fsym("Neg0",[‘f:mem(Tree(A + 1))’])
‘Nd(num2,NONE(A),T1arg(f))’



val T2arg_def = 
proved_th $
e0
cheat
(form_goal “!A t1 t2. ?!f:N->Tree(A). 
 App(f,O) = t1 & 
 App(f,num1) = t2 &
 (!n. ~(n = O) & ~(n = num1) ==> App(f,n) = Lf(A))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "T2arg" [‘t1’,‘t2’]


val Disj0_def = qdefine_fsym("Disj0",[‘f1:mem(Tree(A + 1))’,
                                      ‘f2:mem(Tree(A + 1))’])
‘Nd(num3,NONE(A),T2arg(f1,f2))’

val Diam0_def = qdefine_fsym("Diam0",[‘f:mem(Tree(A + 1))’])
‘Nd(num4,NONE(A),T1arg(f))’

(*
val X1arg_def = 
proved_th $
e0
cheat
(form_goal “!X x. ?!f:N->X+1. 
 App(f,O) = SOME(x) & 
!n. App(f,Suc(n)) = NONE(X)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "X1arg" [‘x’]

val X2arg_def = 
proved_th $
e0
cheat
(form_goal “!X x1 x2. ?!f:N->X + 1. 
 App(f,O) = SOME(x1) & 
 App(f,num1) = SOME(x2) &
 (!n. ~(n = O) & ~(n = num1) ==> App(f,n) = NONE(X))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "X2arg" [‘x1’,‘x2’]


val fmFn_def = proved_th $
e0
cheat
(form_goal
 “!X x0:mem(X) A vf:A->X nf:X->X djf:X*X->X dmf:X->X.
  ?!Fn:N * (A + 1) * Exp(N,Tree(A+1)) * Exp(N,X+1) -> X+1.
  Fnap(Fn,O,NONE(A),TNull(A+1),Null(X)) = SOME(x0) &
  (!a. Fnap(Fn,num1,SOME(a),TNull(A+1),Null(X)) = 
       SOME(App(vf,a))) &
  (!f0 x. Fnap(Fn,num2,NONE(A),T1arg(f0),X1arg(x)) = 
       SOME(App(nf,x))) & 
  (!f1 f2 x1 x2. 
    Fnap(Fn,num3,NONE(A),T2arg(f1,f2),X2arg(x1,x2)) = 
    SOME(App(djf,Pair(x1,x2)))) &
  (!f0 x. Fnap(Fn,num4,NONE(A),T1arg(f0),X1arg(x)) = 
       SOME(App(dmf,x))) ”)
|> spec_all |> uex2ex_rule |> qSKOLEM "fmFn" [‘x0’,‘vf’,‘nf’,‘djf’,‘dmf’]
*)

(*constant at*)
val Conat_def = proved_th $
e0
cheat
(form_goal “!X x:mem(X). ?!f:N->X.!n.App(f,n) = x”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Conat" [‘x’]


val X1arg_def = 
proved_th $
e0
cheat
(form_goal “!X x x0. ?!f:N->X. 
 App(f,O) = x & 
!n. App(f,Suc(n)) = x0”)
|> spec_all |> uex2ex_rule |> qSKOLEM "X1arg" [‘x’,‘x0’]

val X2arg_def = 
proved_th $
e0
cheat
(form_goal “!X x1 x2 x0. ?!f:N->X. 
 App(f,O) = x1 & 
 App(f,num1) = x2 &
 (!n. ~(n = O) & ~(n = num1) ==> App(f,n) = x0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "X2arg" [‘x1’,‘x2’,‘x0’]


val fmFn_def = proved_th $
e0
cheat
(form_goal
 “!X x0:mem(X) A vf:A->X nf:X->X djf:X*X->X dmf:X->X.
  ?!Fn:N * (A + 1) * Exp(N,Tree(A+1)) * Exp(N,X) -> X.
  Fnap(Fn,O,NONE(A),TNull(A+1),Conat(x0)) = x0 &
  (!a. Fnap(Fn,num1,SOME(a),TNull(A+1),Conat(x0)) = 
       App(vf,a)) &
  (!f0 x. Fnap(Fn,num2,NONE(A),T1arg(f0),X1arg(x,x0)) = 
   App(nf,x)) & 
  (!f1 f2 x1 x2. 
    Fnap(Fn,num3,NONE(A),T2arg(f1,f2),X2arg(x1,x2,x0)) = 
       App(djf,Pair(x1,x2))) &
  (!f0 x. Fnap(Fn,num4,NONE(A),T1arg(f0),X1arg(x,x0)) = 
       App(dmf,x))  ”)
|> spec_all |> uex2ex_rule |> qSKOLEM "fmFn" [‘x0’,‘vf’,‘nf’,‘djf’,‘dmf’]




val rec_NONE_TNull_Conat= prove_store("rec_NONE_TNull_Conat",
e0
(rw[GSYM FUN_EXT,App_App_o,TNull_def,Trec_Lf,Null_def,Conat_def])
(form_goal
“!A X f x0:mem(X).Trec(f, x0) o TNull(A + 1) = Conat(x0)”));


val Bot0_x0 = 
Trec_Nd |> qspecl [‘X’,‘x0:mem(X)’,‘A+1’,‘fmFn(x0:mem(X),vf:A->X,nf,djf,dmf)’,‘O’,‘NONE(A)’,‘TNull(A+1)’]
|> rewr_rule[GSYM Bot0_def,fmFn_def,rec_NONE_TNull_Conat]

val Var0_vf = 
Trec_Nd |> qspecl [‘X’,‘x0:mem(X)’,‘A+1’,‘fmFn(x0:mem(X),vf:A->X,nf,djf,dmf)’,‘num1’,‘SOME(a:mem(A))’,‘TNull(A+1)’]
|> rewr_rule[GSYM Var0_def,fmFn_def,rec_NONE_TNull_Conat]


val Fnap_Neg0 = fmFn_def |> conjE2 |> conjE2 |> conjE1


val rec_NONE_T1arg_X1arg= prove_store("rec_NONE_T1arg_X1arg",
e0
(rw[GSYM FUN_EXT,App_App_o,TNull_def,Trec_Lf] >>
 strip_tac >>
 qcases ‘a = O’ 
 >-- arw[X1arg_def,T1arg_def] >>
 fs[O_xor_Suc,T1arg_def,X1arg_def,Trec_Lf] )
(form_goal
“Trec(Fn, x0:mem(X)) o T1arg(f0:mem(Tree(A))) = 
 X1arg(App(Trec(Fn, x0),f0),x0)”));




val Neg0_nf = 
Trec_Nd |> qspecl [‘X’,‘x0:mem(X)’,‘A+1’,‘fmFn(x0:mem(X),vf:A->X,nf,djf,dmf)’,‘num2’,‘NONE(A)’,‘T1arg(f0:mem(Tree(A+1)))’]
|> rewr_rule[GSYM Neg0_def,rec_NONE_T1arg_X1arg,Fnap_Neg0]


val Diam0_dmf = 
Trec_Nd |> qspecl [‘X’,‘x0:mem(X)’,‘A+1’,‘fmFn(x0:mem(X),vf:A->X,nf,djf,dmf)’,‘num4’,‘NONE(A)’,‘T1arg(f0:mem(Tree(A+1)))’]
|> rewr_rule[GSYM Diam0_def,rec_NONE_T1arg_X1arg,fmFn_def]



val Fnap_Disj0 = fmFn_def |> conjE2 |> conjE2 |> conjE2
                          |> conjE1



val rec_NONE_T2arg_X2arg = prove_store("rec_NONE_T2arg_X2arg",
e0
(rw[GSYM FUN_EXT,App_App_o,TNull_def,Trec_Lf] >>
 strip_tac >>
 qcases ‘a = O’ 
 >-- arw[X2arg_def,T2arg_def] >>
 qcases ‘a = num1’ 
 >-- arw[X2arg_def,T2arg_def] >>
 assume_tac (gen_all T2arg_def) >>
 assume_tac (gen_all X2arg_def) >>
 qby_tac ‘ App(T2arg(f1, f2), a) = Lf(A)’ 
 >-- (first_x_assum (qsspecl_then [‘f1’,‘f2’] 
                                 strip_assume_tac) >>
     first_x_assum irule >> arw[]) >>
 arw[Trec_Lf] >>flip_tac >> 
 first_x_assum (qsspecl_then [‘x0’,‘App(Trec(Fn, x0), f1)’,‘App(Trec(Fn, x0), f2)’] 
                                 strip_assume_tac) >>
 first_x_assum irule >> arw[])
(form_goal
“Trec(Fn, x0:mem(X)) o T2arg(f1:mem(Tree(A)),f2) = 
 X2arg(App(Trec(Fn, x0),f1),App(Trec(Fn, x0),f2),x0)”));

val Disj0_djf = 
Trec_Nd |> qspecl [‘X’,‘x0:mem(X)’,‘A+1’,‘fmFn(x0:mem(X),vf:A->X,nf,djf,dmf)’,‘num3’,‘NONE(A)’,‘T2arg(f1:mem(Tree(A+1)),f2)’]
|> rewr_rule[GSYM Disj0_def,rec_NONE_T2arg_X2arg,fmFn_def]






val isfm_cl = 
  “(nas = Bot0(A) ==> IN(nas,isfms)) &
  (!p:mem(A). nas = Var0(p) ⇒ IN(nas,isfms)) &
  (∀f0.IN(f0,isfms) & nas = Neg0(f0) ⇒ IN(nas,isfms)) & 
  (∀f1 f2.IN(f1,isfms) & IN(f2,isfms) & nas = Disj0(f1,f2) ⇒ IN(nas,isfms)) &
  (∀f0.IN(f0,isfms) & nas = Diam0(f0) ⇒ IN(nas,isfms))”

val (isfm_incond,x1) = mk_incond isfm_cl;
val isfmf_ex = mk_fex isfm_incond x1;
val isfmf_def = mk_fdef "isfmf" isfmf_ex;
val isfmf_monotone = mk_monotone isfmf_def;
val isfm's_def = mk_prim isfmf_def;
val isfms_def = mk_LFP (rastt "isfm's(A)");
val isfms_cond = mk_cond isfms_def isfm's_def;
val isfms_SS = mk_SS isfms_def isfm's_def;
val isfm_rules0 = mk_rules isfmf_monotone isfms_SS isfms_cond;
val isfm_cases0 = mk_cases isfmf_monotone isfm_rules0 isfms_cond;
val isfm_ind0 = mk_ind isfms_cond;
val isfm_ind1 = mk_ind1 isfmf_def isfm_ind0;
val isfm_ind2 = mk_ind2 isfm_ind1;
val isfm_cases1 = mk_case1 isfmf_def isfm_cases0;
val isfm_rules1 = mk_rules1 isfmf_def isfm_rules0;
val isfm_rules2 = mk_rules2 isfm_rules1;
val isfm_rules3 = mk_rules3 isfm_rules2;




val isfm_ind = isfm_ind2 |> store_as "isfm_ind";
val isfm_cases = isfm_cases1 |> store_as "isfm_cases";
val isfm_rules = isfm_rules3 |> store_as "isfm_rules";


val isfm_def = qdefine_psym("isfm",[‘f:mem(Tree(A+1))’])
‘IN(f,isfms(A))’ |> gen_all 

val form_def = Thm_2_4  |> qspecl [‘Tree(A+1)’]
                        |> fVar_sInst_th “P(f:mem(Tree(A+1)))”
                        “isfm(f:mem(Tree(A+1)))”
                        |> qSKOLEM "form" [‘A’]
                        |> qSKOLEM "repf" [‘A’]

val isfm_clauses = isfm_rules |> rewr_rule[GSYM isfm_def]


val isfm_induct = prove_store("isfm_induct",
e0
(rw[isfm_def] >> strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘Tree(A+1)’]) >> arw[] >>
 rpt strip_tac >> irule isfm_ind >> arw[])
(form_goal 
 “!A.P(Bot0(A)) & 
  (!p:mem(A). P(Var0(p))) & 
  (!f0:mem(Tree(A + 1)). P(f0) ==> P(Neg0(f0))) &
  (!f1:mem(Tree(A + 1)) f2. P(f1) & P(f2) ==> P(Disj0(f1,f2))) &
  (!f0:mem(Tree(A + 1)). P(f0) ==> P(Diam0(f0))) ==>
  !f0:mem(Tree(A + 1)). isfm(f0) ==> P(f0)”));


val Repf_def = qdefine_fsym("Repf",[‘f:mem(form(A))’]) ‘App(repf(A),f)’
                           |> gen_all 


val repf_Inj = form_def |> conjE1 |> store_as "repf_Inj";

val Bot_def = proved_th $
e0
(rw[Repf_def] >> assume_tac repf_Inj >>
 assume_tac Inj_ex_uex >>
 first_x_assum (qsspecl_then [‘repf(A)’] assume_tac) >>
 rfs[] >> 
 flip_tac >> rw[GSYM form_def] >> rw[isfm_clauses])
(form_goal “?!f. Repf(f) = Bot0(A)”)
|> uex2ex_rule |> qSKOLEM "Bot" [‘A’]


val VAR0_def = fun_tm_compr (dest_var (rastt "a:mem(A)")) (rastt "Var0(a:mem(A))")
                            |> qSKOLEM "VAR0" [‘A’]


val NEG0_def = fun_tm_compr (dest_var (rastt "t:mem(Tree(A+1))")) (rastt "Neg0(t:mem(Tree(A+1)))")
                            |> qSKOLEM "NEG0" [‘A’]


val DIAM0_def = fun_tm_compr (dest_var (rastt "t:mem(Tree(A+1))")) (rastt "Diam0(t:mem(Tree(A+1)))")
                            |> qSKOLEM "DIAM0" [‘A’]


val DISJ0_def = fun_tm_compr (dest_var (rastt "t12:mem(Tree(A+1) * Tree(A+1))")) (rastt "Disj0(Fst(t12:mem(Tree(A+1) * Tree(A+1))), Snd(t12:mem(Tree(A+1) * Tree(A+1))))")
                            |> qSKOLEM "DISJ0" [‘A’]
                            |> qspecl [‘Pair(t1:mem(Tree(A+1)),t2:mem(Tree(A+1)))’]
                            |> rewr_rule[Pair_def']

val DISJ0_Inj = prove_store("DISJ0_Inj",
e0
cheat
(form_goal “Inj(DISJ0(A))”));

val NEG0_Inj = prove_store("NEG0_Inj",
e0
cheat
(form_goal “Inj(NEG0(A))”));


val DIAM0_Inj = prove_store("DIAM0_Inj",
e0
cheat
(form_goal “Inj(NEG0(A))”));


val VAR0_Inj = prove_store("VAR0_Inj",
e0
cheat
(form_goal “Inj(VAR0(A))”));

val VAR_def = Inj_lift_fun |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘VAR0(A)’] 
                           |> rewr_rule[VAR0_def,GSYM form_def,
                                        isfm_clauses]
                           |> qSKOLEM "VAR" [‘A’]
                           |> rewr_rule[App_App_o,GSYM Repf_def]

val Var_def = qdefine_fsym("Var",[‘a:mem(A)’]) ‘App(VAR(A),a)’


val repf_isfm = prove_store("repf_isfm",
e0
(rw[form_def] >> rpt strip_tac >> rw[Repf_def] >>
 qexists_tac ‘f0’ >> rw[])
(form_goal “!f0:mem(form(A)).isfm(Repf(f0))”));

val isfm_Neg0 = isfm_clauses |> conjE2 |> conjE2 |> conjE1

val isfm_Diam0 = isfm_clauses |> conjE2 |> conjE2 |> conjE2
                              |> conjE2

val isfm_Disj0 = isfm_clauses |> conjE2 |> conjE2 |> conjE2
                              |> conjE1

val Neg0_Repf = proved_th $
e0
(strip_tac >> irule isfm_Neg0 >> rw[repf_isfm])
(form_goal “!f0:mem(form(A)). isfm(Neg0(Repf(f0)))”)


val Diam0_Repf = proved_th $
e0
(strip_tac >> irule isfm_Diam0 >> rw[repf_isfm])
(form_goal “!f0:mem(form(A)). isfm(Diam0(Repf(f0)))”)

val Disj0_Repf = proved_th $
e0
(rpt strip_tac >> irule isfm_Disj0 >> rw[repf_isfm])
(form_goal “!a b:mem(form(A)).isfm(Disj0(Repf(a), Repf(b)))”)


val NEG_def = Inj_lift_fun_lemma |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘NEG0(A)’] 
                           |> rewr_rule[App_App_o,NEG0_def]
                           |> rewr_rule[GSYM form_def,GSYM Repf_def]
                           |> rewr_rule[Neg0_Repf]
                           |> qSKOLEM "NEG" [‘A’]

val DIAM_def = Inj_lift_fun_lemma |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘DIAM0(A)’] 
                           |> rewr_rule[App_App_o,DIAM0_def]
                           |> rewr_rule[GSYM form_def,GSYM Repf_def]
                           |> rewr_rule[Diam0_Repf]
                           |> qSKOLEM "DIAM" [‘A’]


val form_def_uex = prove_store("form_def_uex",
e0
(strip_tac >> assume_tac repf_Inj >>
 drule Inj_ex_uex >> flip_tac >>
 rw[Repf_def] >> arw[] >>
 rw[form_def] >> lflip_tac >> rw[])
(form_goal “!a:mem(Tree(A+1)).
 (?!b. a = Repf(b)) <=> isfm(a)”));

val DISJ_def = Inj_restrict |> qsspecl [‘Prla(repf(A),repf(A))’]
                            |> C mp (Prla_Inj |> qsspecl [‘repf(A)’]
                                              |> C mp repf_Inj
                                              |> qsspecl [‘repf(A)’]
                                              |> C mp repf_Inj)
                            |> qsspecl [‘repf(A)’] 
                            |> conv_rule
                            (depth_fconv no_conv forall_cross_fconv)
                            |> C mp repf_Inj
                            |> qspecl [‘DISJ0(A)’]
                            |> rewr_rule[App_App_o,Prla_def,App_Pa_Pair]
                            |> rewr_rule[Pair_def,GSYM Repf_def]
                            |> rewr_rule[form_def_uex,DISJ0_def,Pair_def']
                            |> C mp Disj0_Repf
                            |> uex2ex_rule
                            |> qSKOLEM "DISJ" [‘A’] 
                            |> rewr_rule[GSYM FUN_EXT] 
                            |>  conv_rule
                            (depth_fconv no_conv forall_cross_fconv)
                            |> rewr_rule[App_App_o,App_Pa_Pair,Pair_def,
                                         DISJ0_def,GSYM Repf_def] |> rewr_rule[Pair_def']

val Neg_def = qdefine_fsym("Neg",[‘f:mem(form(A))’]) ‘App(NEG(A),f)’


val Diam_def = qdefine_fsym("Diam",[‘f:mem(form(A))’]) ‘App(DIAM(A),f)’


val Disj_def = qdefine_fsym("Disj",[‘f1:mem(form(A))’,‘f2:mem(form(A))’]) ‘App(DISJ(A),Pair(f1,f2))’


val fmrec_def = qdefine_fsym("fmrec",[‘x0:mem(X)’,‘vf:A->X’,‘nf:X->X’,‘djf:X*X->X’,‘dmf:X->X’])
‘Trec(fmFn(x0:mem(X), vf:A->X, nf, djf, dmf), x0) o repf(A)’



val fmrec_clauses = prove_store("fmrec_clauses",
e0
(rpt strip_tac (* 5*) 
 >-- rw[fmrec_def,App_App_o,Bot_def,GSYM Repf_def,
        Bot0_x0]
 >-- rw[fmrec_def,App_App_o,Var_def,VAR_def,GSYM Repf_def,
        Var0_vf]
 >-- rw[fmrec_def,App_App_o,Neg_def,NEG_def,GSYM Repf_def,
        Neg0_nf]
 >-- rw[fmrec_def,App_App_o,Disj_def,DISJ_def,GSYM Repf_def,
        Disj0_djf]
 >-- rw[fmrec_def,App_App_o,Diam_def,DIAM_def,GSYM Repf_def,
        Diam0_dmf])
(form_goal “!X x0 A vf:A->X nf djf:X * X->X dmf. 
 App(fmrec(x0,vf,nf,djf,dmf),Bot(A)) = x0 & 
 (!p.App(fmrec(x0,vf,nf,djf,dmf),Var(p)) = App(vf,p)) &
 (!f.App(fmrec(x0,vf,nf,djf,dmf),Neg(f)) = 
     App(nf,App(fmrec(x0,vf,nf,djf,dmf),f))) & 
 (!f1 f2.App(fmrec(x0,vf,nf,djf,dmf),Disj(f1,f2)) = 
     App(djf,Pair(App(fmrec(x0,vf,nf,djf,dmf),f1),
                  App(fmrec(x0,vf,nf,djf,dmf),f2)))) & 
 (!f.App(fmrec(x0,vf,nf,djf,dmf),Diam(f)) = 
     App(dmf,App(fmrec(x0,vf,nf,djf,dmf),f))) ”));


val form_def' = form_def |> conv_rule flip_fconv

val form_induct = prove_store("form_induct",
e0
(strip_tac >> disch_tac >>
 qsuff_tac ‘!f0:mem(Tree(A+1)). isfm(f0) ==> isfm(f0) &
 !f.Repf(f) = f0 ==> P(f)’ 
 >-- (strip_tac >>
     qby_tac ‘!f0:mem(Tree(A+1)). isfm(f0) ==>
                      (!f. Repf(f) = f0 ==> P(f))’ 
     >-- (rpt strip_tac >> first_x_assum drule >>
          rfs[] >> first_x_assum irule >> arw[]) >>
     strip_tac >> first_x_assum irule >>
     qexists_tac ‘Repf(f0)’ >> rw[repf_isfm]) >>
 ind_with (isfm_induct |> qspecl [‘A’]) >>
 rw[isfm_clauses] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     qsuff_tac ‘f = Bot(A)’ >-- (strip_tac >> arw[]) >>
     irule $ iffLR Inj_eq_eq >> qexistsl_tac [‘Tree(A+1)’,‘repf(A)’] >>
     arw[repf_Inj,Bot_def,GSYM Repf_def]) >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> 
      qsuff_tac ‘f = Var(p)’ >-- (strip_tac >> arw[]) >>
      irule $ iffLR Inj_eq_eq >> qexistsl_tac [‘Tree(A+1)’,‘repf(A)’] >>
      arw[repf_Inj,Var_def,GSYM Repf_def,GSYM VAR_def,App_App_o]) >> 
 strip_tac (* 2 *)
 >-- (rpt gen_tac >> disch_tac >> 
     pop_assum strip_assume_tac >> 
     qby_tac ‘isfm(Neg0(f0))’ >-- (irule isfm_Neg0 >> arw[]) >> arw[] >>
     rpt strip_tac >>
     qby_tac ‘?f1. Repf(f1) = f0’ 
     >-- arw[GSYM form_def',Repf_def] >>
     pop_assum strip_assume_tac >> 
     first_x_assum drule >>
     fs[] >> 
     qsuff_tac ‘f = Neg(f1)’ 
     >-- (strip_tac >> arw[] >> first_x_assum irule >> arw[]) >>
     rw[GSYM Repf_eq_eq] >> arw[Neg_def,NEG_def] >>
      arw[]) >> strip_tac (* 2 *)
>-- (rpt gen_tac >> disch_tac >> pop_assum strip_assume_tac >>
    qby_tac ‘isfm(Disj0(f1, f2))’ 
    >-- (irule isfm_Disj0 >> arw[]) >>
    arw[] >> rpt strip_tac >> 
    qby_tac ‘?f10. Repf(f10) = f1’ 
    >-- arw[GSYM form_def',Repf_def] >>
    pop_assum strip_assume_tac >> 
    qby_tac ‘?f20. Repf(f20) = f2’ 
    >-- arw[GSYM form_def',Repf_def] >>
    pop_assum strip_assume_tac >> 
    first_x_assum drule >> first_x_assum drule >> fs[] >>
    qsuff_tac ‘f = Disj(f10,f20)’ 
    >-- (rpt strip_tac >> arw[] >> first_x_assum irule >> arw[]) >>
    rw[GSYM Repf_eq_eq] >> arw[Disj_def,DISJ_def]) >>
rpt gen_tac >> disch_tac >> 
pop_assum strip_assume_tac >> 
qby_tac ‘isfm(Diam0(f0))’ >-- (irule isfm_Diam0 >> arw[]) >> arw[] >>
rpt strip_tac >>
qby_tac ‘?f1. Repf(f1) = f0’ 
>-- arw[GSYM form_def',Repf_def] >>
pop_assum strip_assume_tac >> 
first_x_assum drule >>
fs[] >> 
qsuff_tac ‘f = Diam(f1)’ 
>-- (strip_tac >> arw[] >> first_x_assum irule >> arw[]) >>
rw[GSYM Repf_eq_eq] >> arw[Diam_def,DIAM_def])
(form_goal
 “!A.P(Bot(A)) & 
  (!p:mem(A). P(Var(p))) & 
  (!f0:mem(form(A)). P(f0) ==> P(Neg(f0))) &
  (!f1:mem(form(A)) f2. P(f1) & P(f2) ==> P(Disj(f1,f2))) &
  (!f0:mem(form(A)). P(f0) ==> P(Diam(f0))) ==>
  !f0:mem(form(A)). P(f0)”));





local 
val l = proved_th $
e0
()
(form_goal “”)
Inj_restrict |> qsspecl [‘repf(A)’]
|> rewr_rule[repf_Inj]
|> qsspecl [‘Id(X)’]
|> rewr_rule[Id_Inj,Id_def]
|> qspecl [‘Trec(fmFn(x0:mem(X), vf:A->X, nf, djf, dmf), x0)’]
|> rewr_rule[App_App_o,GSYM Repf_def,IdL]

(*
Vars are 
Nd(0,NONE(A),(\n. Lf(A+1)))

Fn: N -> A -> (N -> Tree(A)) -> (N -> X) -> X

Fn: N -> A +1 -> (N -> Tree(A+1)) -> (N -> X) -> X

Fn: N -> A+1 -> (N -> Tree(A) * X + 1) -> X

*)
