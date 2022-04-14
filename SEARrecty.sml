(*Udef can only be abbrev since no set equality*)

val InjN_def = proved_th $
e0
(cheat)
(form_goal “!A. ?!injN:N -> Pow(N * A).
 !n0. (!n a.IN(Pair(n,a),App(injN,n0)) <=> n = n0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "InjN" [‘A’] |> gen_all 


val InjA_def = proved_th $
e0
(cheat)
(form_goal “!A. ?!injA:A -> Pow(N * A).
 !a0. (!n a.IN(Pair(n,a),App(injA,a0)) <=> a = a0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "InjA" [‘A’] |> gen_all 

val Even_def = qdefine_psym("Even",[‘n:mem(N)’]) ‘∃n0. n = Mul(Suc(Suc(O)),n0)’
val Odd_def = qdefine_psym("Odd",[‘n:mem(N)’]) ‘~Even(n)’

(*pretend we have div*)
val DIV2_def = proved_th $
e0
cheat
(form_goal “∃!f:N ->N. (∀n.Even(n) ⇔ App(f,n) = O) &
 (∀n. Odd(n) ⇔ App(f,n) = Suc(O)) ”)
|> uex2ex_rule |> qSKOLEM "DIV2" []

val Div_def = qdefine_fsym("Div2",[‘n:mem(N)’]) ‘App(DIV2,n)’

                          
val InjUU_def = proved_th $
e0
cheat
(form_goal “∀A.∃!f:Pow(N * A) * Pow(N * A) -> Pow(N * A).
 ∀u1 u2. ∀n a. IN(Pair(n,a),App(f,Pair(u1,u2))) ⇔ 
  ((Even(n) & IN(Pair(Div2(n),a),u1)) | 
   (Odd(n) & IN(Pair(Div2(n),a),u2)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "InjUU" [‘A’]

val injN_def = qdefine_fsym("injN",[‘A’,‘n:mem(N)’]) ‘App(InjN(A),n)’
val injA_def = qdefine_fsym("injA",[‘a:mem(A)’]) ‘App(InjA(A),a)’ 
val injUU_def = 
    qdefine_fsym("injUU",[‘u1:mem(Pow(N * A))’,‘u2:mem(Pow(N * A))’]) 
                ‘App(InjUU(A),Pair(u1,u2))’ 



val num1_def = qdefine_fsym("num1",[]) ‘Suc(O)’
val num2_def = qdefine_fsym("num2",[]) ‘Suc(num1)’
val num3_def = qdefine_fsym("num3",[]) ‘Suc(num2)’
val num4_def = qdefine_fsym("num4",[]) ‘Suc(num3)’

(*FALSE *)
val F0_def = qdefine_fsym("F0",[‘A’]) ‘injN(A,O)’

val VAR0_def = qdefine_fsym("VAR0",[‘A’]) ‘InjUU(A) o Pa(El(injN(A,num1)) o To1(A),InjA(A))’

val Var0_def = qdefine_fsym("Var0",[‘a:mem(A)’]) ‘App(VAR0(A),a)’

val NEG0_def = qdefine_fsym("NEG0",[‘A’]) ‘InjUU(A) o 
Pa(El(injN(A,num2)) o To1(Pow(N * A)),Id(Pow(N * A)))’


val Neg0_def = qdefine_fsym("Neg0",[‘f0:mem(Pow(N * A))’]) ‘App(NEG0(A),f0)’

 
val DISJ0_def = qdefine_fsym("DISJ0",[‘A’]) ‘InjUU(A) o 
Pa(El(injN(A,num3)) o To1(Pow(N * A) * Pow(N * A)),InjUU(A))’

val Disj0_def = qdefine_fsym("Disj0",[‘f1:mem(Pow(N * A))’,‘f2:mem(Pow(N * A))’]) ‘App(DISJ0(A),Pair(f1,f2))’

val DIAM0_def = qdefine_fsym("DIAM0",[‘A’])
‘InjUU(A) o 
Pa(El(injN(A,num4)) o To1(Pow(N * A)),Id(Pow(N * A)))’

val Diam0_def = qdefine_fsym("Diam0",[‘f0:mem(Pow(N * A))’]) ‘App(DIAM0(A),f0)’



val f = 
 “(nas = F0 ==> IN(nas,isfms)) &
  (!p:mem(A). nas = Var0(p) ⇒ IN(nas,isfms)) &
  (∀f0.IN(f0,isfms) & nas = Neg0(f0) ⇒ IN(nas,isfms)) & 
  (∀f1 f2.IN(f1,isfms) & IN(f2,isfms) & nas = Disj0(f1,f2) ⇒ IN(nas,isfms)) &
  (∀f0.IN(f0,isfms) & nas = Diam0(f0) ⇒ IN(nas,isfms))”


val isfm_cl = 
  “(nas = F0(A) ==> IN(nas,isfms)) &
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


val isfm_def = qdefine_psym("isfm",[‘f:mem(Pow(N * A))’])
‘IN(f,isfms(A))’ |> gen_all 



(*isfm_ind cannot be solved by arw with isfm_ind since the bracket of isfm_ind is weird*)
val isfm_induct = prove_store("isfm_induct",
e0
(rw[isfm_def] >> strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘Pow(N * A)’]) >> arw[] >>
 rpt strip_tac >> irule isfm_ind >> arw[])
(form_goal 
 “!A.P(F0(A)) & 
  (!p:mem(A). P(Var0(p))) & 
  (!f0:mem(Pow(N * A)). P(f0) ==> P(Neg0(f0))) &
  (!f1:mem(Pow(N * A)) f2. P(f1) & P(f2) ==> P(Disj0(f1,f2))) &
  (!f0:mem(Pow(N * A)). P(f0) ==> P(Diam0(f0))) ==>
  !f0:mem(Pow(N * A)). isfm(f0) ==> P(f0)”));
 
val isfm_F0 = prove_store("isfm_F0",
e0
(rw[isfm_def,isfm_rules])
(form_goal
 “!A. isfm(F0(A))”)); 


val isfm_Var0 = prove_store("isfm_Var0",
e0
(rw[isfm_def,isfm_rules])
(form_goal
 “!A p:mem(A). isfm(Var0(p))”)); 

val isfm_clauses = isfm_rules |> rewr_rule[GSYM isfm_def]





val isL_Ins = isL_rules |> spec_all |> conjE2 
                        |> rewr_rule[GSYM isL_def]
                        |> spec_all |> undisch 
                        |> gen_all |> disch_all
                        |> gen_all |> store_as "isL_Ins";


val form_def = Thm_2_4  |> qspecl [‘Pow(N * A)’]
                        |> fVar_sInst_th “P(f:mem(Pow(N * A)))”
                        “isfm(f:mem(Pow(N * A)))”
                        |> qSKOLEM "form" [‘A’]
                        |> qSKOLEM "repf" [‘A’]

val repf_Inj = form_def |> conjE1 |> store_as "repf_Inj"; 

val Repf_def = qdefine_fsym("Repf",[‘f:mem(form(A))’]) ‘App(repf(A),f)’
                           |> gen_all 

val Inj_ex_uex = prove_store("Inj_ex_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- first_x_assum (accept_tac o uex2ex_rule) >>
 uex_tac >> qexists_tac ‘a’ >> arw[] >> rpt strip_tac >>
 fs[Inj_def] >> first_x_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !b. (?!a.App(f,a) = b) <=> (?a.App(f,a) = b)”));

fun flip_fconv f = 
    let val eqths = List.map eq_sym (!EqSorts)
        val fc = first_fconv (List.map rewr_fconv eqths)
    in  (once_depth_fconv no_conv fc) f
    end

val form_def' = form_def |> conv_rule flip_fconv

val Bot_def = proved_th $
e0
(rw[Repf_def] >> assume_tac repf_Inj >>
 drule Inj_ex_uex >> arw[] >>
 flip_tac >> rw[GSYM form_def] >> rw[isfm_clauses])
(form_goal “?!f. Repf(f) = F0(A)”)
|> uex2ex_rule |> qSKOLEM "Bot" [‘A’]

val VAR_def = Inj_lift_fun |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘VAR0(A)’] 
                           |> rewr_rule[GSYM Var0_def,GSYM form_def,
                                        isfm_clauses]
                           |> qSKOLEM "VAR" [‘A’]

val repf_isfm = prove_store("repf_isfm",
e0
(rw[form_def] >> rpt strip_tac >> rw[Repf_def] >>
 qexists_tac ‘f0’ >> rw[])
(form_goal “!f0:mem(form(A)).isfm(Repf(f0))”));

val isfm_Neg0 = isfm_clauses |> conjE2 |> conjE2 |> conjE1 

val Neg0_Repf = proved_th $
e0
(strip_tac >> irule isfm_Neg0 >> rw[repf_isfm])
(form_goal “!f0:mem(form(A)). isfm(Neg0(Repf(f0)))”)

val NEG_def = Inj_lift_fun_lemma |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘NEG0(A)’] 
                           |> rewr_rule[App_App_o,GSYM Neg0_def]
                           |> rewr_rule[GSYM form_def,GSYM Repf_def]
                           |> rewr_rule[Neg0_Repf]
                           |> qSKOLEM "NEG" [‘A’]

val isfm_Diam0 = isfm_clauses |> conjE2 |> conjE2 |> conjE2 
                              |> conjE2

val Diam0_Repf = proved_th $
e0
(strip_tac >> irule isfm_Diam0 >> rw[repf_isfm])
(form_goal “!f0:mem(form(A)). isfm(Diam0(Repf(f0)))”)


val DIAM_def = Inj_lift_fun_lemma |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘DIAM0(A)’] 
                           |> rewr_rule[App_App_o,GSYM Diam0_def]
                           |> rewr_rule[GSYM form_def,GSYM Repf_def]
                           |> rewr_rule[Diam0_Repf]
                           |> qSKOLEM "DIAM" [‘A’]

(*think about how quo related to this*)
val Inj_restrict = prove_store("Inj_restrict",
e0
(rpt strip_tac >>
 assume_tac (P2fun_uex |> qspecl [‘D’,‘C’] 
                    |> fVar_sInst_th “P(d:mem(D),c:mem(C))”
                       “App(f0:D0->C0 o i1:D->D0, d) = App(i2:C->C0, c)”) >>
 first_x_assum drule >> flip_tac >>
 fs[GSYM App_App_o,FUN_EXT])
(form_goal 
 “!D D0 i1:D->D0. Inj(i1) ==> 
  !C C0 i2:C->C0. Inj(i2) ==>
  !f0:D0->C0.
   (!d.?!c. App(f0 o i1,d) = App(i2,c)) ==>
  ?!f:D->C.i2 o f = f0 o i1”));

val form_def_uex = prove_store("form_def_uex",
e0
(strip_tac >> assume_tac repf_Inj >>
 drule Inj_ex_uex >> flip_tac >>
 rw[Repf_def] >> arw[] >>
 rw[form_def] >> lflip_tac >> rw[])
(form_goal “!a:mem(Pow(N * A)).
 (?!b. a = Repf(b)) <=> isfm(a)”));

val isfm_Disj0 =  isfm_clauses |> conjE2 |> conjE2 
                               |> conjE2 |> conjE1

local
val l = proved_th $
e0
(rpt strip_tac >> irule isfm_Disj0 >> rw[repf_isfm])
(form_goal “!a b:mem(form(A)).isfm(Disj0(Repf(a), Repf(b)))”)
in
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
                            |> rewr_rule[form_def_uex,GSYM Disj0_def]
                            |> C mp l
                            |> uex2ex_rule
                            |> qSKOLEM "DISJ" [‘A’] 
                            |> rewr_rule[GSYM FUN_EXT] 
                            |>  conv_rule
                            (depth_fconv no_conv forall_cross_fconv)
                            |> rewr_rule[App_App_o,App_Pa_Pair,Pair_def,
                                         GSYM Disj0_def,GSYM Repf_def]
end
                          
val Var_def = qdefine_fsym("Var",[‘a:mem(A)’]) ‘App(VAR(A),a)’

val Neg_def = qdefine_fsym("Neg",[‘f:mem(form(A))’]) ‘App(NEG(A),f)’

val Diam_def = qdefine_fsym("Diam",[‘f:mem(form(A))’]) ‘App(DIAM(A),f)’

val Disj_def = qdefine_fsym("Disj",[‘f1:mem(form(A))’,‘f2:mem(form(A))’])
                           ‘App(DISJ(A),Pair(f1,f2))’

val Repf_eq_eq = prove_store("Repf_eq_eq",
e0
(cheat)
(form_goal “!f1:mem(form(A)) f2. Repf(f1) = Repf(f2) <=> f1 = f2”))

val form_induct = prove_store("form_induct",
e0
(strip_tac >> disch_tac >>
 qsuff_tac ‘!f0:mem(Pow(N * A)). isfm(f0) ==> isfm(f0) &
 !f.Repf(f) = f0 ==> P(f)’ 
 >-- (strip_tac >>
     qby_tac ‘!f0:mem(Pow(N * A)). isfm(f0) ==>
                      (!f. Repf(f) = f0 ==> P(f))’ 
     >-- (rpt strip_tac >> first_x_assum drule >>
          rfs[] >> first_x_assum irule >> arw[]) >>
     strip_tac >> first_x_assum irule >>
     qexists_tac ‘Repf(f0)’ >> rw[repf_isfm]) >>
 ind_with (isfm_induct |> qspecl [‘A’]) >>
 rw[isfm_F0,isfm_Var0] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     qsuff_tac ‘f = Bot(A)’ >-- (strip_tac >> arw[]) >>
     irule $ iffLR Inj_eq_eq >> qexistsl_tac [‘Pow(N * A)’,‘repf(A)’] >>
     arw[repf_Inj,Bot_def,GSYM Repf_def]) >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> 
      qsuff_tac ‘f = Var(p)’ >-- (strip_tac >> arw[]) >>
      irule $ iffLR Inj_eq_eq >> qexistsl_tac [‘Pow(N * A)’,‘repf(A)’] >>
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
     rw[GSYM Repf_eq_eq] >> arw[Neg_def,NEG_def]) >> strip_tac (* 2 *)
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
val fmind_cl = 
 “(p = Pair(Bot(A),x0:mem(X)) ==> IN(p,fmind)) &
  (!a:mem(A).p = Pair(Var(a),App(vf:A->X,a)) ==> IN(p,fmind)) &
  (!p0:mem(form(A) * X). IN(p0,fmind) &
   p = Pair(Neg(Fst(p0)),App(nf:X->X,Snd(p0))) ==> IN(p,fmind)) &
  (!p0:mem(form(A) * X). IN(p0,fmind) &
   p = Pair(Diam(Fst(p0)),App(dmf:X->X,Snd(p0))) ==> IN(p,fmind)) & 
  (!p1:mem(form(A) * X) p2. IN(p1,fmind) & IN(p2,fmind) & 
   p = Pair(Disj(Fst(p1),Fst(p2)),App(djf:X * X ->X,Pair(Snd(p1),Snd(p2)))) ==> IN(p,fmind))”
in
val (fmind_incond,x1) = mk_incond fmind_cl;
val fmindf_ex = mk_fex fmind_incond x1;
val fmindf_def = mk_fdef "fmindf" fmindf_ex;
val fmindf_monotone = mk_monotone fmindf_def;
val fmind's_def = mk_prim fmindf_def;
val fminds_def = mk_LFP (rastt "fmind's(djf:X*X->X, dmf:X->X, nf:X->X, vf:A->X, x0:mem(X))");
val fminds_cond = mk_cond fminds_def fmind's_def;
val fminds_SS = mk_SS fminds_def fmind's_def;
val fmind_rules0 = mk_rules fmindf_monotone fminds_SS fminds_cond;
val fmind_cases0 = mk_cases fmindf_monotone fmind_rules0 fminds_cond;
val fmind_ind0 = mk_ind fminds_cond;
val fmind_ind1 = mk_ind1 fmindf_def fmind_ind0;
val fmind_ind2 = mk_ind2 fmind_ind1; 
val fmind_cases1 = mk_case1 fmindf_def fmind_cases0; 
val fmind_rules1 = mk_rules1 fmindf_def fmind_rules0; 
val fmind_rules2 = mk_rules2 fmind_rules1; 
val fmind_rules3 = mk_rules3 fmind_rules2;
end

val fmind_ind = fmind_ind2 |> store_as "fmind_ind";
val fmind_cases = fmind_cases1 |> store_as "fmind_cases";
val fmind_rules = fmind_rules3 |> store_as "fmind_rules";

val Bot_NOT = prove_store("Bot_NOT",
e0
cheat
(form_goal “!A. (!p.~(Bot(A) = Var(p))) &
 (!f. ~(Bot(A) = Neg(f))) &
 (!f. ~(Bot(A) = Diam(f))) &
 (!f1 f2. ~(Bot(A) = Disj(f1,f2)))”));



val Var_NOT = prove_store("Bot_NOT",
e0
cheat
(form_goal “!A. (!p.~(Var(p) = Bot(A))) &
 (!p:mem(A) f. ~(Var(p) = Neg(f))) &
 (!p:mem(A) f. ~(Var(p) = Diam(f))) &
 (!p:mem(A) f1 f2. ~(Var(p) = Disj(f1,f2)))”));


val Neg_NOT = prove_store("Neg_NOT",
e0
cheat
(form_goal “!A. (!f:mem(form(A)).~(Neg(f) = Bot(A))) &
 (!f p:mem(A). ~(Neg(f) = Var(p))) &
 (!f f0:mem(form(A)). ~(Neg(f) = Diam(f0))) &
 (!f:mem(form(A)) f1 f2. ~(Neg(f) = Disj(f1,f2)))”));


val Diam_NOT = prove_store("Diam_NOT",
e0
cheat
(form_goal “!A. (!f:mem(form(A)).~(Diam(f) = Bot(A))) &
 (!f p:mem(A). ~(Diam(f) = Var(p))) &
 (!f f0:mem(form(A)). ~(Diam(f) = Neg(f0))) &
 (!f:mem(form(A)) f1 f2. ~(Diam(f) = Disj(f1,f2)))”));



val Disj_NOT = prove_store("Disj_NOT",
e0
cheat
(form_goal “!A. (!f1 f2:mem(form(A)).~(Disj(f1,f2) = Bot(A))) &
 (!f1 f2 p:mem(A). ~(Disj(f1,f2) = Var(p))) &
 (!f1 f2 f0:mem(form(A)). ~(Disj(f1,f2) = Diam(f0))) &
 (!f1 f2 f:mem(form(A)). ~(Disj(f1,f2) = Neg(f)))”));


val Var_eq_eq = prove_store("Var_eq_eq",
e0
(cheat)
(form_goal “!p1 p2:mem(A). Var(p1) = Var(p2) <=> p1 = p2”));


val Neg_eq_eq = prove_store("Neg_eq_eq",
e0
(cheat)
(form_goal “!f1 f2:mem(form(A)). Neg(f1) = Neg(f2) <=> f1 = f2”));


val Diam_eq_eq = prove_store("Diam_eq_eq",
e0
(cheat)
(form_goal “!f1 f2:mem(form(A)). Diam(f1) = Diam(f2) <=> f1 = f2”));


val Disj_eq_eq = prove_store("Disj_eq_eq",
e0
(cheat)
(form_goal “!f1 f2 g1 g2:mem(form(A)). Disj(f1,f2) = Disj(g1,g2) <=> f1 = g1 & f2 = g2”));

val fmind_Neg = fmind_rules |> conjE2 |> conjE2 |> conjE1
                            |> qspecl [‘Pair(f:mem(form(A)),x:mem(X))’]
                            |> rewr_rule[Pair_def'];
val fmind_Disj = fmind_rules |> conjE2 |> conjE2 |> conjE2|> conjE2
                             |> qspecl [‘Pair(f1:mem(form(A)),x1:mem(X))’]
                             |> rewr_rule[Pair_def']
                             |> qspecl [‘Pair(f2:mem(form(A)),x2:mem(X))’]
                             |> rewr_rule[Pair_def']
                             |> undisch  |> gen_all
                             |> disch_all |> gen_all;

val fmind_Diam = fmind_rules |> conjE2 |> conjE2 |> conjE2 |> conjE1
                             |> qspecl [‘Pair(f:mem(form(A)),x:mem(X))’]
                             |> rewr_rule[Pair_def']

(*exactly same proof as Nind_uex*)
val fmind_uex = prove_store("fmind_uex",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 strip_tac >> strip_tac >> 
 ind_with (form_induct |> qspecl [‘A’]) >> strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘x0’ >>
      rw[fmind_rules] >> once_rw[fmind_cases] >>
      rw[Pair_eq_eq,Bot_NOT] >> rpt strip_tac) >> strip_tac 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘App(vf,p)’ >>
     rw[fmind_rules] >> once_rw[fmind_cases] >>
     rw[Pair_eq_eq,Var_NOT,Var_eq_eq] >> rpt strip_tac >> rfs[])>>
 strip_tac 
 >-- (rpt strip_tac >> uex_tac >>
     pop_assum (strip_assume_tac o uex_expand) >>
     qexists_tac ‘App(nf,x)’ >>
     drule (fmind_rules |> conjE2 |> conjE2 |> conjE1) >> fs[Pair_def'] >>
     rpt strip_tac >> drule $ iffLR fmind_cases >>
     fs[Pair_eq_eq,Neg_NOT,Neg_eq_eq] >>
     qsspecl_then [‘p0’] (x_choosel_then ["f1","x1"] strip_assume_tac)
     Pair_has_comp >> fs[Pair_def'] >>
     qby_tac ‘x1 = x’ 
     >-- (first_x_assum irule >> arw[]) >>
     arw[]) >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> uex_tac >>
     last_x_assum (strip_assume_tac o uex_expand) >>
     last_x_assum (strip_assume_tac o uex_expand) >>
     qexists_tac ‘App(djf,Pair(x,x'))’ >>
     rev_drule (fmind_rules |> conjE2 |> conjE2 |> conjE2|> conjE2
                            |> spec_all |> undisch  |> gen_all
                            |> disch_all |> gen_all) >> 
     first_x_assum drule >>
     fs[Pair_def',Disj_NOT] >>
     rpt strip_tac >> drule $ iffLR fmind_cases >>
     fs[Pair_eq_eq,Disj_NOT,Disj_eq_eq] >>
     qsspecl_then [‘p1’] (x_choosel_then ["f1'","x1"] strip_assume_tac)
     Pair_has_comp >>
     qsspecl_then [‘p2’] (x_choosel_then ["f2'","x2"] strip_assume_tac)
     Pair_has_comp >> fs[Pair_def'] >>
     qby_tac ‘x1 = x’ 
     >-- (first_x_assum irule >> arw[]) >>
     qby_tac ‘x2 = x'’ 
     >-- (first_x_assum irule >> arw[]) >>
     arw[]) >>
 rpt strip_tac >> uex_tac >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘App(dmf,x)’ >>
 drule (fmind_rules |> conjE2 |> conjE2 |> conjE2 |> conjE1) >> fs[Pair_def'] >>
 rpt strip_tac >> drule $ iffLR fmind_cases >>
 fs[Pair_eq_eq,Diam_NOT,Diam_eq_eq] >>
 qsspecl_then [‘p0’] (x_choosel_then ["f1","x1"] strip_assume_tac)
 Pair_has_comp >> fs[Pair_def'] >>
 qby_tac ‘x1 = x’ 
 >-- (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal
 “!A x0:mem(X) vf nf djf dmf f:mem(form(A)). ?!x. IN(Pair(f,x),fminds(djf,dmf,nf,vf,x0))”));



val fmrec_def = P2fun' |> qspecl [‘form(A)’,‘X’] 
                      |> fVar_sInst_th “P(f:mem(form(A)),
                                          x:mem(X))”
                          “IN(Pair(f,x),
                              fminds(djf:X * X ->X,dmf,nf,vf:A->X,x0))”
                      |> C mp (fmind_uex |> spec_all
                                         |> qgen ‘f’)
                      |> qSKOLEM "fmrec" [‘x0’,‘vf’,‘nf’,‘djf’,‘dmf’]
                      |> qgenl [‘X’,‘x0’,‘A’,‘vf’,‘nf’,‘djf’,‘dmf’]
                      |> store_as "fmrec_def";


val App_fmrec_fminds = prove_store("App_fmrec_fminds",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >--
(pop_assum (assume_tac o GSYM) >> arw[fmrec_def]) >>
qsspecl_then [‘x0’,‘vf’,‘nf’,‘djf’,‘dmf’,‘f’] assume_tac fmrec_def >>
qsspecl_then [‘x0’,‘vf’,‘nf’,‘djf’,‘dmf’,‘f’] assume_tac fmind_uex >>
pop_assum (strip_assume_tac o uex_expand) >>
qby_tac ‘App(fmrec(x0, vf,nf,djf,dmf), f) = x' & x = x'’ 
>-- (strip_tac >> first_x_assum irule >> arw[]) >>
arw[])
(form_goal “!X x0 A vf:A->X nf djf:X * X->X dmf.
!f x. App(fmrec(x0,vf,nf,djf,dmf),f) = x <=> 
IN(Pair(f,x),fminds(djf,dmf,nf,vf,x0))”));

val fmrec_clauses = prove_store("fmrec_clauses",
e0
(rpt gen_tac >> rw[App_fmrec_fminds,fmind_rules] >> rpt strip_tac (* 3 *)
 >-- (irule fmind_Neg >> rw[GSYM App_fmrec_fminds])
 >-- (irule fmind_Disj >> rw[GSYM App_fmrec_fminds]) >>
 irule fmind_Diam >> rw[GSYM App_fmrec_fminds])
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


val r2f_def = proved_th $
e0
cheat
(form_goal “!R:A~>B. ?!f:A * B -> 1+1.
 !a b. App(f,Pair(a,b)) = App(i2(1,1),dot)  <=> Holds(R,a,b)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "r2f" [‘R’] |> gen_all


val true_def = qdefine_fsym("true",[]) ‘App(i2(1,1),dot)’

val false_def = qdefine_fsym("false",[]) ‘App(i1(1,1),dot)’

val tv_eq_true = prove_store("tv_eq_true",
e0
(cheat)
(form_goal “!tv1 tv2. tv1 = tv2 <=>
 (tv1 = true <=> tv2 = true)”));

val OR_def = proved_th $
e0
(cheat)
(form_goal “?f:(1+1) * (1+1) -> 1+1. 
 App(f,Pair(true,true)) = true & 
 App(f,Pair(true,false)) = true &
 App(f,Pair(false,true)) = true &
 App(f,Pair(false,false)) = false”)
|> qSKOLEM "OR" [] 


val NOT_def = proved_th $
e0
(cheat)
(form_goal “?f:1+1 -> 1+1. 
App(f,true) = false & App(f,false) = true”)
|> qSKOLEM "NOT" [] 



val f2r_def = proved_th $
e0
cheat
(form_goal “!A B f:A * B -> 1+1.?!R:A~>B.
 !a b. Holds(R,a,b) <=> App(f,Pair(a,b)) = true”)
|> spec_all |> uex2ex_rule |> qSKOLEM "f2r" [‘f’] |> gen_all


val ss2f = proved_th $
e0
(cheat)
(form_goal “!A s:mem(Pow(A)).?!f:A -> 1+1.
 !a. App(f,a) = true <=> IN(a,s)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "ss2f" [‘s’]

(*Holds at*)
val HAT_def = proved_th $
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
 ?!f:A->Pow(W). !a w. IN(w,App(f,a)) <=> IN(a,App(Vof(M),w))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "HAT" [‘M’]


val satis_dmf = proved_th $
e0
(cheat)
(form_goal
 “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
  ?!f:Pow(W) -> Pow(W). 
  (!s0 w.IN(w,App(f,s0)) <=> ?w0.IN(w0,s0) & IN(Pair(w,w0),Rof(M)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "sdmf" [‘M’]

val satisf_def = qdefine_fsym("satisf",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘fmrec(Empty(W), HAT(M), COMPL(W), UNION(W), sdmf(M))’
 
val satisf_clause = 
fmrec_clauses |> qspecl [‘Pow(W)’]
              |> qspecl [‘Empty(W)’]
              |> qspecl [‘A’]
              |> qspecl [‘HAT(M:mem(Pow(W * W) * Exp(W,Pow(A))))’]
              |> qspecl [‘COMPL(W)’]
              |> qspecl [‘UNION(W)’]
              |> qspecl [‘sdmf(M)’]
              |> rewr_rule[GSYM satisf_def]

rastt "ss2f(App(Vof(M:mem(Pow(W * W) * Exp(W,Pow(A)))),w))"
“ss2f(App(Vof(M:mem(Pow(W * W) * Exp(W,Pow(A)))),w)) = a”
(*model is a R:A~>A with a member of Pow(A * N)

type of model: Pow(A * A) * Pow(A * N)
 *)

val Vof_def = qdefine_fsym("Vof",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘tof(Snd(M))’ |> gen_all


val Rof_def = qdefine_fsym("Rof",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘Fst(M)’ |> gen_all


val satis_cheat = 
    qdefine_psym("satis",
                 [‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w:mem(W)’,‘f:mem(form(A))’])
    ‘T’


val satis_def = prove_store("satis_def",
e0
cheat
(form_goal 
“(satis(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,VAR(a:mem(A))) <=> 
 IN(a,App(Vof(M),w))) &
 (satis(M,w,NEG(f)) <=> ~ (satis(M,w,f))) & 
 (satis(M,w,DISJ(f1,f2)) <=> (satis(M,w,f1) | satis(M,w,f2)))”));

(*related*)
val Rlt_def = qdefine_psym("Rlt",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w1:mem(W)’,‘w2:mem(W)’]) ‘IN(Pair(w1,w2),Rof(M))’

val Sim_def = qdefine_psym("Sim",[‘R:W1~>W2’,‘M1:mem(Pow(W1 * W1) * Exp(W1,Pow(A)))’,‘M2:mem(Pow(W2 * W2) * Exp(W2,Pow(A)))’]) 
‘!w1 w2.Holds(R,w1,w2) ==>
 (!p.IN(p,App(Vof(M1),w1)) ==> IN(p,App(Vof(M2),w2))) & 
 (!v. Rlt(M1,w1,v) ==> ?v'. Holds(R,v,v') & Rlt(M2,w2,v'))’

val PUS_def = qdefine_psym("PUS",[‘f:mem(form(A))’])
‘!W1 W2 R:W1~>W2 M1:mem(Pow(W1 * W1) * Exp(W1,Pow(A))) M2. Sim(R,M1,M2) ==>
 !w1 w2. Holds(R,w1,w2) ==> satis(M1,w1,f) ==> satis(M2,w2,f)’

val PE_cheat = qdefine_psym("PE",[‘f:mem(form(A))’]) ‘T’

val EQV_def = qdefine_psym("EQV",[‘f1:mem(form(A))’,‘f2:mem(form(A))’])
 ‘!W M w:mem(W). satis(M,w,f1) <=> satis(M,w,f2)’

val Msat_def = qdefine_psym("Msat",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’]) ‘T’

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

val filter_def = qdefine_psym("filter",[‘L:mem(Pow(Pow(J)))’,‘J’])
‘~EMPTY(J) &
  ~(L = Empty(Pow(J))) & IN(Whole(J),L) & 
  (!X Y. IN(X,L) & IN(Y,L) ==> IN(Inter(X,Y),L)) & 
  (!X. IN(X,L) ==> !Y. SS(X,Y) ==> IN(Y,L))’


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
cheat
(form_goal “!A s a. IN(a:mem(A),Compl(s)) <=> ~IN(a,s)”));


val ufilter_def = qdefine_psym("ufilter",[‘L:mem(Pow(Pow(J)))’,‘J’])
‘filter(L,J) & 
 (!X. IN(X,L) <=> ~(IN(Compl(X),L)))’

val UFs_def = Thm_2_4 |> qspecl [‘Pow(Pow(J))’]
                      |> fVar_sInst_th “P(a:mem(Pow(Pow(J))))”
                      “ufilter(a,J)”
                      |> qSKOLEM "UFs" [‘J’]
                      |> qSKOLEM "iUF" [‘J’] 

val Repu_def = qdefine_fsym("Repu",[‘u:mem(UFs(J))’])
‘App(iUF(J),u)’

(*True at, takes a letter, gives the set of worlds it holds*)
val Tat_def = proved_th $
e0
(cheat)
(form_goal “!f0:W ->Pow(A). !a.?!ws:mem(Pow(W)).
 !w. IN(w,ws) <=> IN(a,App(f0,w))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Tat" [‘f0’,‘a’]

val ueV_def = proved_th $
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
 ?!f0:mem(Exp(UFs(W),Pow(A))).
  !u a. IN(a,App(tof(f0),u)) <=>  IN(Tat(Vof(M),a),Repu(u))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "ueV" [‘M’]

val csee_def = proved_th $
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) X. 
 ?!cs:mem(Pow(W)).
 !w. IN(w,cs) <=> ?v. IN(v,X) &IN(Pair(w,v),Rof(M)) ”)
|> spec_all |> uex2ex_rule |> qSKOLEM "csee" [‘M’,‘X’]

val ueR_def = proved_th $
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
 ?!R:mem(Pow(UFs(W) * UFs(W))).
   !u1 u2. IN(Pair(u1,u2),R) <=> 
   (!X.IN(X,Repu(u2)) ==> IN(csee(M,X),Repu(u1)))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "ueR" [‘M’]

val UE_def = qdefine_fsym("UE",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘Pair(ueR(M),ueV(M))’

val MEQ_def = 
    qdefine_psym("MEQ",[‘M1:mem(Pow(W1 * W1) * Exp(W1,Pow(A)))’,
                        ‘w1:mem(W1)’,
                        ‘M2:mem(Pow(W2 * W2) * Exp(W2,Pow(A)))’,
                        ‘w2:mem(W2)’])
    ‘!f. satis(M1,w1,f) <=> satis(M2,w2,f)’

val Pft_def = proved_th $
e0
cheat
(form_goal “!W w0:mem(W). ?!uw:mem(UFs(W)).
 !ws.IN(ws,Repu(uw)) <=> IN(w0,ws)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Pft" [‘w0’]

val Prop_5_7 = prove_store("Prop_5_7",
e0
cheat
(form_goal “!W M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
 MEQ(M,w,UE(M),Pft(w))”));

val Prop_5_9 = prove_store("Prop_5_9",
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). Msat(UE(M))”));



val Thm_6_22 = prove_store("Thm_6_22",
e0
cheat
(form_goal “!M1 M2.Msat(M1) & Msat(M2) ==> 
 !w1:mem(W1) w2:mem(W2). (!f:mem(form(A)).PE(f) ==> satis(M1,w1,f) ==> satis(M2,w2,f)) ==>
 ?R. Sim(R,M1,M2) & Holds(R,w1,w2)”));

val Thm_6_23 = prove_store("Thm_6_23",
e0
cheat
(form_goal
 “!fs:mem(Pow(form(A))).
  (!ffs. SS(ffs,fs) & Fin(ffs) ==> 
  ?W M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
   SATIS(M,w,ffs)) ==>
  ?W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
   SATIS(M,w,fs) ”));

val SATIS_def = qdefine_psym("SATIS",
[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w:mem(W)’,‘fs:mem(Pow(form(A)))’])
‘!f. IN(f,fs) ==> satis(M,w,f)’


val ENT_def = qdefine_psym("ENT",[‘phis:mem(Pow(form(A)))’,‘psi:mem(form(A))’])
‘!W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
 SATIS(M,w,phis) ==> satis(M,w,psi)’


val Thm_6_24 = prove_store("Thm_6_24",
e0
cheat
(form_goal
 “!fs:mem(Pow(form(A))) phi.ENT(fs,phi) ==>
  ?ffs. SS(ffs,fs) & Fin(ffs) & ENT(ffs,phi)”));


val Ent_def = qdefine_psym("Ent",[‘phi:mem(form(A))’,‘psi:mem(form(A))’])
‘!W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. satis(M,w,phi) ==> satis(M,w,psi)’


val PEC_def = proved_th $
e0
cheat
(form_goal “!A f:mem(form(A)). ?!pec.
 !phi. IN(phi,pec) <=> PE(phi) & Ent(f,phi)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "PEC" [‘f’]

val Fin_ENT_PE = prove_store("Fin_ENT_PE",
e0
cheat
(form_goal
 “!fs. Fin(fs) & (!f. IN(f,fs) ==> PE(f))==> 
 ?phi:mem(form(A)).PE(phi) &
       !W M w:mem(W).SATIS(M,w,fs) <=> satis(M,w,phi)”));

val SATIS_SS = prove_store("SATIS_SS",
e0
(rpt strip_tac >> fs[SS_def,SATIS_def] >> 
 rpt strip_tac >> first_x_assum irule >> first_x_assum irule >> arw[])
(form_goal “!s1 s2. SS(s1,s2) ==>
 !M:mem(Pow(W * W) * Exp(W,Pow(A))) w.SATIS(M,w,s2) ==> SATIS(M,w,s1) ”))

val SATIS_PEC = prove_store("SATIS_PEC",
e0
cheat
(form_goal “!f M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
 satis(M,w,f) ==> SATIS(M,w,PEC(f)) ”));

val satis_NEG = prove_store("satis_NEG",
e0
cheat
(form_goal
 “!M:mem(Pow(W * W) * Exp(W,Pow(A))) w.satis(M, w, NEG(f)) <=> ~satis(M, w, f)”));

val NEG_eq_eq = prove_store("NEG_eq_eq",
e0
cheat
(form_goal “!f1:mem(form(A)) f2.NEG(f1) = NEG(f2) <=> f1 = f2”));


val Thm_6_25_l2r = prove_store("Thm_6_25_l2r",
e0
(rpt strip_tac >> 
 qsuff_tac
 ‘ENT(PEC(f),f)’
 >-- (strip_tac >>
     drule Thm_6_24 >> pop_assum strip_assume_tac >>
     qby_tac ‘!f.IN(f,ffs) ==> PE(f)’ 
     >-- (fs[SS_def,PEC_def] >> rpt strip_tac >> first_x_assum drule >>
         arw[]) >>
     qsspecl_then [‘ffs’] assume_tac Fin_ENT_PE >>
     rfs[] >> qexists_tac ‘phi’ >> arw[] >>
     rw[EQV_def] >> pop_assum (assume_tac o GSYM) >> arw[] >>
     rpt strip_tac >> dimp_tac (* 2 *)
     >-- (strip_tac >> qsuff_tac ‘SATIS(M,w,PEC(f))’
          >-- (match_mp_tac SATIS_SS  >> arw[]) >>
          irule SATIS_PEC >> arw[]) >>
     qpick_x_assum ‘ENT(ffs, f)’ assume_tac >>
     fs[ENT_def]) >>
 rw[ENT_def] >> rpt strip_tac >>
 qby_tac
 ‘?G. !psi. IN(psi,G) <=>?psi0. psi = NEG(psi0) & PE(psi0) & ~(satis(M,w,psi0))’
 >-- accept_tac (IN_def_P |> qspecl [‘form(A)’]
              |> fVar_sInst_th “P(psi:mem(form(A)))”
                 “?psi0:mem(form(A)). psi = NEG(psi0) & PE(psi0) & 
                                      ~(satis(M,w:mem(W),psi0))”
              |> uex2ex_rule) >>
 pop_assum strip_assume_tac >>
 qby_tac 
 ‘!ss.SS(ss,Ins(f,G)) &  Fin(ss) ==>
  ?V M1:mem(Pow(V * V) * Exp(V,Pow(A))) v.SATIS(M1,v,ss)’
 >-- (rpt strip_tac >> ccontra_tac >>
     qby_tac
     ‘?ss0. !f0. IN(f0,ss0) <=> 
      IN(NEG(f0),Del(ss,f))’ 
     >-- accept_tac (IN_def_P |> qspecl [‘form(A)’]
              |> fVar_sInst_th “P(f0:mem(form(A)))”
                 “IN(NEG(f0),Del(ss,f:mem(form(A))))”
              |> uex2ex_rule) >> 
     pop_assum strip_assume_tac >>
     qby_tac ‘Fin(ss0)’ >-- (*FINITE_Inj*) cheat >>
     qby_tac
     ‘!psi0.IN(NEG(psi0),G) ==> PE(psi0) & ~satis(M,w,psi0)’
     >-- (arw[] >> rw[NEG_eq_eq] >> rpt strip_tac >> rfs[] >> arw[]) >>
     qby_tac ‘SS(Del(ss,f),G)’ >-- cheat >> 
     qby_tac ‘!f0. IN(f0,ss0) ==> PE(f0)’ 
     >-- (rpt strip_tac >> drule $ iffLR SS_def >> 
          first_x_assum (drule o iffLR) >> 
          qsuff_tac ‘PE(f0) & ~satis(M,w,f0)’ 
          >-- (strip_tac >> arw[]) >>
          first_x_assum irule >> 
          drule $ iffLR SS_def >> first_x_assum irule >> arw[]) >>
     qby_tac ‘?ff. PE(ff) & !V M1:mem(Pow(V * V) * Exp(V,Pow(A))) v.
              satis(M1,v,ff) <=> ?f0. IN(f0,ss0) & satis(M1,v,f0)’
     >-- cheat >> pop_assum strip_assume_tac >>
     qby_tac ‘IN(ff,PEC(f))’ 
     >-- (rw[PEC_def] >> arw[] >> rw[Ent_def] >>
          arw[] >> rpt strip_tac >> ccontra_tac >>
          qsuff_tac ‘?V M1 v:mem(V). SATIS(M1,v,ss)’
          >-- arw[] >>
          qexistsl_tac [‘W'’,‘M'’,‘w'’] >>
          qby_tac ‘!f1. IN(f1,Del(ss,f)) ==> satis(M',w',f1)’ 
          >-- (rpt strip_tac >>
              qby_tac ‘?f0. f1 = NEG(f0)’ >-- cheat >> fs[] >>
              fs[] >> ccontra_tac  >>
              qby_tac ‘?f0. IN(NEG(f0),Del(ss,f)) & satis(M',w',f0)’ 
              >-- (qexists_tac ‘f0’ >> arw[] >> fs[satis_NEG]) >>
              first_x_assum opposite_tac) >>
          rw[SATIS_def] >> rpt strip_tac >>
          qcases ‘f' = f’ 
          >-- arw[] >>
          qby_tac ‘IN(f',Del(ss,f))’ >-- arw[Del_def] >>
          first_x_assum drule >> arw[]) >>
     qby_tac ‘satis(M,w,ff)’ 
     >-- (rev_drule $ iffLR SATIS_def >>
         first_x_assum drule >> arw[]) >>
     qby_tac ‘?f0. IN(f0,ss0) & satis(M,w,f0)’ 
     >-- (first_x_assum (irule o iffLR) >> arw[]) >>
     pop_assum strip_assume_tac >> 
     qby_tac ‘!f0.IN(f0,ss0) ==> ~satis(M,w,f0)’ 
     >-- (rpt strip_tac >> 
         last_x_assum $ drule o iffLR >> 
         qby_tac ‘IN(NEG(f0'),G)’
         >-- (qsuff_tac ‘SS(Del(ss,f),G)’
             >-- (rw[SS_def] >> rpt strip_tac >>
                 first_x_assum irule >> arw[]) >>
             cheat (* SS(ss, Ins(f, G)) ==> SS(Del(ss, f), G)*)) >>
         pop_assum mp_tac >> arw[] >> strip_tac >>
         fs[NEG_eq_eq]) >>
     first_x_assum drule >> fs[])>>
 drule Thm_6_23 >> pop_assum strip_assume_tac >>
 qby_tac ‘!psi. PE(psi) ==> satis(M',w',psi) ==> satis(M,w,psi)’ 
 >-- (qsuff_tac ‘!psi.PE(psi) ==> ~satis(M,w,psi) ==> ~satis(M',w',psi)’
     >-- (rpt strip_tac >> ccontra_tac >> 
         first_x_assum drule >> first_x_assum drule >> fs[]) >>
     rpt strip_tac >>
     qby_tac ‘IN(NEG(psi),G)’ 
     >-- (first_x_assum (irule o iffRL) >>
         qexists_tac ‘psi’ >> arw[]) >> 
     drule $ iffLR SATIS_def >>
     first_x_assum (qsspecl_then [‘NEG(psi)’] assume_tac) >>
     rfs[Ins_def,satis_NEG]) >>
 qby_tac
 ‘?R. Sim(R,UE(M'),UE(M)) & Holds(R,Pft(w'),Pft(w))’
 >-- (irule Thm_6_22 >> rw[Prop_5_9] >> rpt strip_tac >>
     qby_tac ‘satis(M',w',f')’ 
     >-- (qsspecl_then [‘M'’,‘w'’] assume_tac Prop_5_7 >>
         fs[MEQ_def]) >>
     qby_tac ‘satis(M,w,f')’
     >-- (first_x_assum irule >> arw[]) >>
     qsspecl_then [‘M’,‘w’] assume_tac Prop_5_7 >>
     fs[MEQ_def]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘satis(M',w',f)’
 >-- (drule $ iffLR SATIS_def >> 
     first_x_assum (qsspecl_then [‘f’] assume_tac) >>
     fs[Ins_def]) >>
 qby_tac ‘satis(UE(M'),Pft(w'),f)’ 
 >-- (qsspecl_then [‘M'’,‘w'’] assume_tac Prop_5_7 >> fs[MEQ_def]) >>
 qby_tac ‘satis(UE(M),Pft(w),f)’ 
 >-- (drule $ iffLR PUS_def >> first_x_assum drule >>
     first_x_assum drule >> first_x_assum drule >> arw[]) >>
 qsspecl_then [‘M’,‘w’] assume_tac Prop_5_7 >> fs[MEQ_def])
(form_goal “!A f:mem(form(A)). PUS(f) ==> ?f0. PE(f0) & EQV(f,f0)”))

val Thm_6_25_r2l = prove_store("Thm_6_25_r2l",
e0
cheat
(form_goal “!A f f0:mem(form(A)). PE(f0) & EQV(f,f0) ==> PUS(f)”));

val Thm_6_25_iff = prove_store("Thm_6_25_iff",
e0
(rpt strip_tac >> dimp_tac >> disch_tac 
 >-- (drule Thm_6_25_l2r >> arw[]) >>
 irule Thm_6_25_r2l >> pop_assum strip_assume_tac >>
 qexists_tac ‘f0’ >> arw[])
(form_goal “!A f:mem(form(A)). PUS(f) <=> ?f0. PE(f0) & EQV(f,f0)”))

