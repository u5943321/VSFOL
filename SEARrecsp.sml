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
 qexists_tac ‘Fnap(Fn, n, a, f, j)’ >> arw[]
 rpt strip_tac >> drule $ iffLR Tind_cases >>
 fs[Pair_eq_eq,Nd_NONLF,Nd_eq_eq] >>
 qby_tac ‘y = j’ >>
 fs[] >> cheat)
(form_goal “!X l:mem(X) A  Fn  t:mem(Tree(A)). ?!e. IN(Pair(t,e),Tinds(Fn,l))”));
