(*Udef can only be abbrev since no set equality*)

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


(*
VAR not a Bot, NEG, 


*)
                          
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





(*FALSE *)
val F0_def = qdefine_fsym("F0",[‘A’]) ‘injN(A,O)’

val InjA_Inj = prove_store("InjA_Inj",
e0
(strip_tac >> rw[Inj_def] >> rw[GSYM IN_EXT_iff] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[InjA_def] >> rpt strip_tac >>
 first_x_assum (qspecl_then [‘O’,‘x1’] assume_tac) >> fs[])
(form_goal “!A. Inj(InjA(A))”));

val VAR0_def = qdefine_fsym("VAR0",[‘A’]) ‘InjUU(A) o Pa(El(injN(A,num1)) o To1(A),InjA(A))’

val Pa_Inj = prove_store("Pa_Inj",
e0
(rpt strip_tac >> rw[Inj_def] >> rw[App_Pa_Pair] >> rw[Pair_eq_eq] >>
 fs[Inj_def] >> rpt strip_tac >> first_x_assum irule >> arw[])
(form_goal “!X A f:X->A. Inj(f) ==> !B g:X->B. Inj(Pa(g,f))”));

val o_Inj_Inj = prove_store("o_Inj_Inj",
e0
cheat
(form_goal “!A B f:A->B. Inj(f) ==> !C g:B->C. Inj(g) ==> Inj(g o f)”));

val VAR0_Inj = prove_store("VAR0_Inj",
e0
(rw[VAR0_def] >> strip_tac >> irule o_Inj_Inj >>
 rw[InjUU_Inj] >> irule Pa_Inj >> rw[InjA_Inj])
(form_goal “!A.Inj(VAR0(A))”));

val Var0_def = qdefine_fsym("Var0",[‘a:mem(A)’]) ‘App(VAR0(A),a)’

val NEG0_def = qdefine_fsym("NEG0",[‘A’]) ‘InjUU(A) o 
Pa(El(injN(A,num2)) o To1(Pow(N * A)),Id(Pow(N * A)))’


val NEG0_Inj = prove_store("NEG0_Inj",
e0
(rw[NEG0_def] >> strip_tac >> irule o_Inj_Inj >>
 rw[InjUU_Inj] >> irule Pa_Inj >> rw[Id_Inj])
(form_goal “!A.Inj(NEG0(A))”));



val Neg0_def = qdefine_fsym("Neg0",[‘f0:mem(Pow(N * A))’]) ‘App(NEG0(A),f0)’

 
val DISJ0_def = qdefine_fsym("DISJ0",[‘A’]) ‘InjUU(A) o 
Pa(El(injN(A,num3)) o To1(Pow(N * A) * Pow(N * A)),InjUU(A))’


val DISJ0_Inj = prove_store("DISJ0_Inj",
e0
(rw[DISJ0_def] >> strip_tac >> irule o_Inj_Inj >>
 rw[InjUU_Inj] >> irule Pa_Inj >> rw[InjUU_Inj])
(form_goal “!A.Inj(DISJ0(A))”));


val Disj0_def = qdefine_fsym("Disj0",[‘f1:mem(Pow(N * A))’,‘f2:mem(Pow(N * A))’]) ‘App(DISJ0(A),Pair(f1,f2))’

val DIAM0_def = qdefine_fsym("DIAM0",[‘A’])
‘InjUU(A) o 
Pa(El(injN(A,num4)) o To1(Pow(N * A)),Id(Pow(N * A)))’



val DIAM0_Inj = prove_store("DIAM0_Inj",
e0
(rw[DIAM0_def] >> strip_tac >> irule o_Inj_Inj >>
 rw[InjUU_Inj] >> irule Pa_Inj >> rw[Id_Inj])
(form_goal “!A.Inj(DIAM0(A))”));


val Diam0_def = qdefine_fsym("Diam0",[‘f0:mem(Pow(N * A))’]) ‘App(DIAM0(A),f0)’


(*How to automatically prove the constructors mutually disjoint?
  *)
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


val VAR_Inj = prove_store("VAR_Inj",
e0
(cheat)
(form_goal “!A. Inj(VAR(A))”));

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






val Vof_def = qdefine_fsym("Vof",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘tof(Snd(M))’ |> gen_all


val Rof_def = qdefine_fsym("Rof",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘Fst(M)’ |> gen_all


val Rm_def = qdefine_psym("Rm",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w1:mem(W)’,‘w2:mem(W)’]) ‘IN(Pair(w1,w2),Rof(M))’;

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
  (!s0 w.IN(w,App(f,s0)) <=> ?w0.IN(w0,s0) & Rm(M,w,w0))”)
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

val satis_def0 = qdefine_psym("satis",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w:mem(W)’,‘f:mem(form(A))’]) ‘IN(w,App(satisf(M),f))’;

val satis_def = prove_store("satis_def",
e0
(rw[satis_def0] >> rw[satisf_clause,COMPL_def,UNION_def,Empty_def] >>
 rw[HAT_def] >> rw[satis_dmf] >> 
 strip_tac >> dimp_tac >> strip_tac 
 >-- (qexists_tac ‘w0’ >> arw[]) >>
 qexists_tac ‘v’ >> arw[])
(form_goal 
“(~(satis(M,w,Bot(A)))) & 
 (!a.satis(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,Var(a:mem(A))) <=> 
 IN(a,App(Vof(M),w))) &
 (!f.satis(M,w,Neg(f)) <=> ~ (satis(M,w,f))) & 
 (!f1 f2.satis(M,w,Disj(f1,f2)) <=> (satis(M,w,f1) | satis(M,w,f2))) &
 (!f.satis(M,w,Diam(f)) <=> ?v. Rm(M,w,v) & satis(M,v,f))”));


val SATIS_def = qdefine_psym("SATIS",
[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w:mem(W)’,‘fs:mem(Pow(form(A)))’])
‘!f. IN(f,fs) ==> satis(M,w,f)’

val Top_def = qdefine_fsym("Top",[‘A’]) ‘Neg(Bot(A))’;

val Conj_def = qdefine_fsym("Conj",[‘f1:mem(form(A))’,‘f2:mem(form(A))’]) 
                           ‘Neg(Disj(Neg(f1),Neg(f2)))’ 


val satis_Conj = prove_store("satis_Conj",
e0
(rpt strip_tac >> rw[Conj_def,satis_def] >> once_rw[neg_or_distr] >>
 rw[])
(form_goal “!M w:mem(W) f1:mem(form(A)) f2.
 satis(M,w,Conj(f1,f2)) <=> satis(M,w,f1) & satis(M,w,f2)
 ”));


local
val PE_cl = 
 “(f = Top(A) ==> IN(f,PEs)) &
  (f = Bot(A) ==> IN(f,PEs)) & 
  (!p.f = Var(p) ==> IN(f,PEs)) &
  (!f1 f2. IN(f1,PEs) & IN(f2,PEs) & f = Conj(f1,f2) ==> IN(f,PEs)) & 
  (!f1 f2. IN(f1,PEs) & IN(f2,PEs) & f = Disj(f1,f2) ==> IN(f,PEs)) & 
  (!f0. IN(f0,PEs) & f = Diam(f0) ==> IN(f,PEs))”
in
val (PE_incond,x1) = mk_incond PE_cl;
val PEf_ex = mk_fex PE_incond x1;
val PEf_def = mk_fdef "PEf" PEf_ex;
val PEf_monotone = mk_monotone PEf_def;
val PE's_def = mk_prim PEf_def;
val PEs_def = mk_LFP (rastt "PE's(A)");
val PEs_cond = mk_cond PEs_def PE's_def;
val PEs_SS = mk_SS PEs_def PE's_def;
val PE_rules0 = mk_rules PEf_monotone PEs_SS PEs_cond;
val PE_cases0 = mk_cases PEf_monotone PE_rules0 PEs_cond;
val PE_ind0 = mk_ind PEs_cond;
val PE_ind1 = mk_ind1 PEf_def PE_ind0;
val PE_ind2 = mk_ind2 PE_ind1; 
val PE_cases1 = mk_case1 PEf_def PE_cases0; 
val PE_rules1 = mk_rules1 PEf_def PE_rules0; 
val PE_rules2 = mk_rules2 PE_rules1; 
val PE_rules3 = mk_rules3 PE_rules2;
end

val PE_ind0 = PE_ind2 |> store_as "PE_ind";
val PE_cases0 = PE_cases1 |> store_as "PE_cases";
val PE_rules0 = PE_rules3 |> store_as "PE_rules";

val PE_def0 = qdefine_psym("PE",[‘f:mem(form(A))’]) ‘IN(f,PEs(A))’

val PE_ind = PE_ind0 |> rewr_rule[GSYM PE_def0];
val PE_cases = PE_cases0 |> rewr_rule[GSYM PE_def0];
val PE_rules = PE_rules0 |> rewr_rule[GSYM PE_def0];



val PE_induct = prove_store("PE_induct",
e0
(strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘form(A)’]) >> arw[] >>
 disch_tac >> 
 match_mp_tac PE_ind >> arw[])
(form_goal
 “!A. P(Top(A)) & P(Bot(A)) & (!p:mem(A). P(Var(p))) &
      (!f1:mem(form(A)) f2. P(f1) & P(f2) ==> P(Conj(f1,f2))) & 
      (!f1:mem(form(A)) f2. P(f1) & P(f2) ==> P(Disj(f1,f2))) & 
      (!f:mem(form(A)).P(f) ==> P(Diam(f))) ==> 
      (!f:mem(form(A)). PE(f) ==> P(f)) ”));


val satis_Bot = satis_def |> conjE1 |> gen_all

val satis_Top = prove_store("satis_Top",
e0
(rw[Top_def,satis_def,satis_Bot])
(form_goal “!A M w:mem(W). satis(M,w,Top(A))”));


val Sim_def = qdefine_psym("Sim",[‘R:W1~>W2’,‘M1:mem(Pow(W1 * W1) * Exp(W1,Pow(A)))’,‘M2:mem(Pow(W2 * W2) * Exp(W2,Pow(A)))’]) 
‘!w1 w2.Holds(R,w1,w2) ==>
 (!p.IN(p,App(Vof(M1),w1)) ==> IN(p,App(Vof(M2),w2))) & 
 (!v. Rm(M1,w1,v) ==> ?v'. Holds(R,v,v') & Rm(M2,w2,v'))’

val PUS_def = qdefine_psym("PUS",[‘f:mem(form(A))’])
‘!W1 W2 R:W1~>W2 M1:mem(Pow(W1 * W1) * Exp(W1,Pow(A))) M2. Sim(R,M1,M2) ==>
 !w1 w2. Holds(R,w1,w2) ==> satis(M1,w1,f) ==> satis(M2,w2,f)’

val PUS_Var = prove_store("PUS_Var",
e0
(rpt strip_tac >> rw[PUS_def,satis_def] >>
 rpt strip_tac >> fs[Sim_def] >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 first_x_assum irule >> arw[])
(form_goal “!A p:mem(A). PUS(Var(p))”));

val PUS_Top = prove_store("PUS_Top",
e0
(rpt strip_tac >> rw[PUS_def,satis_Top])
(form_goal “!A. PUS(Top(A))”));

val PUS_Bot = prove_store("PUS_Bot",
e0
(rpt strip_tac >> fs[PUS_def,satis_Bot])
(form_goal “!A. PUS(Bot(A))”));

val Thm_6_25_r2l0 = prove_store("Thm_6_25_r2l0",
e0
(strip_tac >> ind_with (PE_induct |> spec_all) >>
 rw[PUS_Top,PUS_Bot,PUS_Var] >> 
 once_rw[PUS_def] >> rpt strip_tac (* 3 *)
 >-- (fs[satis_Conj] >> first_x_assum drule >>
      first_x_assum drule >> first_x_assum drule >> arw[] >>
      first_x_assum drule >> first_x_assum drule >> 
      first_x_assum drule >> arw[])
 >-- (fs[satis_def] (* 2 *)
     >-- (disj1_tac >> first_x_assum irule >>
         qexistsl_tac [‘W1’,‘M1’,‘R’,‘w1’] >> arw[]) >>
     disj2_tac >> first_x_assum irule >>
     qexistsl_tac [‘W1’,‘M1’,‘R’,‘w1’] >> arw[]) >>
 fs[satis_def] >>
 drule $ iffLR Sim_def >> 
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexists_tac ‘v'’ >> arw[] >> 
 first_x_assum irule >>
 qexistsl_tac [‘W1’,‘M1’,‘R’,‘v’] >> arw[]
 )
(form_goal “!A f:mem(form(A)). PE(f) ==> PUS(f)”));


val EQV_def = qdefine_psym("EQV",[‘f1:mem(form(A))’,‘f2:mem(form(A))’])
 ‘!W M w:mem(W). satis(M,w,f1) <=> satis(M,w,f2)’


val Thm_6_25_r2l = prove_store("Thm_6_25_r2l",
e0
(rpt strip_tac >> drule Thm_6_25_r2l0 >>
 fs[PUS_def] >> fs[EQV_def])
(form_goal “!A f f0:mem(form(A)). PE(f0) & EQV(f,f0) ==> PUS(f)”));


val Sab_def = qdefine_psym
                  ("Sab",[‘fs:mem(Pow(form(A)))’,‘X:mem(Pow(W))’,‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
                  ‘?x.IN(x,X) & SATIS(M,x,fs)’


val Fsab_def = qdefine_psym
                  ("Fsab",[‘fs:mem(Pow(form(A)))’,‘X:mem(Pow(W))’,‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
                  ‘!ss. Fin(ss) & SS(ss,fs) ==> Sab(ss,X,M)’

(*successor in M*)
val Sucm_def = proved_th $
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
?!sucm. !v. IN(v,sucm) <=> Rm(M,w,v)”) 
|> spec_all |> uex2ex_rule |> qSKOLEM "Sucm" [‘M’,‘w’]

val Msat_def = qdefine_psym("Msat",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’]) 
‘!w fs. Fsab(fs,Sucm(M,w),M) ==>  Sab(fs,Sucm(M,w),M) ’

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
 !w. IN(w,cs) <=> ?v.Rm(M,w,v) &  IN(v,X) ”)
|> spec_all |> uex2ex_rule |> qSKOLEM "csee" [‘M’,‘X’]


val osee_def = proved_th $
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) X. 
 ?!cs:mem(Pow(W)).
 !w. IN(w,cs) <=> !v. Rm(M,w,v) ==> IN(v,X)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "osee" [‘M’,‘X’]

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


val Prop_5_6 = prove_store("Prop_5_6",
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) u v. Rm(UE(M),u,v) <=> 
 (!Y. IN(osee(M,Y),Repu(u)) ==> IN(Y,Repu(v)))”));

val ueR_alt = Prop_5_6

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

(*satis worlds*)
val SW_def = proved_th $
e0
(cheat)
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
 ?!sws:form(A) -> Pow(W). !f w. IN(w,App(sws,f)) <=> satis(M,w,f)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "SW" [‘M’]

val Sw_def = qdefine_fsym("Sw",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,
                                        ‘f:mem(form(A))’]) 
                          ‘App(SW(M),f)’


val Prop_5_5_2 = prove_store("Prop_5_5_2",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff] >> strip_tac >>
 rw[osee_def,Inter_def,INTER_def] >> 
 dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum drule >> arw[])
 >--  (first_x_assum drule >> arw[]) 
 >> first_x_assum irule >> arw[])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) X Y:mem(Pow(W)). osee(M,Inter(X,Y)) = Inter(osee(M,X),osee(M,Y))”));
 
val Sw_Bot = prove_store("Sw_Bot",
e0
cheat
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). Sw(M,Bot(A)) = Empty(W)”));

val Sw_Var = prove_store("Sw_Var",
e0
(rw[GSYM IN_EXT_iff,Sw_def,SW_def,HAT_def,satis_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) p. 
                  Sw(M,Var(p)) = App(HAT(M),p)”));

val Vof_UE = prove_store("Vof_UE",
e0
(rw[UE_def,Vof_def,Pair_def'])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). Vof(UE(M)) = tof(ueV(M))”));


val HAT_Tat =prove_store("HAT_Tat",
e0
(rw[GSYM IN_EXT_iff,HAT_def,Tat_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) p. App(HAT(M), p) = Tat(Vof(M), p)”));


val Sw_Neg = prove_store("Sw_Neg",
e0
(rw[GSYM IN_EXT_iff,Sw_def,SW_def,satis_def,Compl_def,COMPL_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) f. 
                  Sw(M,Neg(f)) = Compl(Sw(M,f))”));




val Sw_Disj = prove_store("Sw_Disj",
e0
(rw[GSYM IN_EXT_iff,Sw_def,SW_def,satis_def,Union_def,UNION_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). 
                  Sw(M,Disj(f1,f2)) = Union(Sw(M,f1),Sw(M,f2))”));



val Rm_UE = prove_store("Rm_UE",
e0
(rw[Rm_def,Rof_def,UE_def,Pair_def',ueR_def] >> rpt strip_tac >> rw[])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) u u'.Rm(UE(M),u,u') <=>
 !X. IN(X,Repu(u')) ==> IN(csee(M,X),Repu(u))”));

val csee_Sw_DIAM = prove_store("csee_Sw_DIAM",
e0
(rw[GSYM IN_EXT_iff,csee_def,Sw_def,SW_def,satis_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) f.csee(M,Sw(M,f)) = 
 Sw(M,Diam(f))”));

val Prop_5_8 = prove_store("Prop_5_8",
e0
(strip_tac >> strip_tac >> 
 ind_with (form_induct |> qspecl [‘A’]) >>
 rpt strip_tac 
 >-- rw[satis_Bot,Sw_Bot,Empty_NOTIN_UFs]
 >-- rw[Sw_Var,satis_def,Vof_UE,ueV_def,HAT_Tat]
 >-- arw[satis_def,Sw_Neg,Compl_Repu]
 >-- arw[Sw_Disj,satis_def,Union_Repu] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (rw[satis_def] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Prop_5_6] >>
 qby_tac ‘?u0'. !Y. IN(Y,u0') <=> IN(osee(M,Y),Repu(u))’
 >-- cheat >> pop_assum strip_assume_tac >>
 qby_tac ‘FIP(Ins(Sw(M,f0), u0'))’ >-- cheat >>
 qby_tac ‘?u'. SS(Ins(Sw(M,f0), u0'),Repu(u'))’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘u'’ >> last_x_assum (assume_tac o GSYM) >> arw[] >>
 qby_tac ‘IN(Sw(M, f0), Repu(u'))’
 >-- (fs[SS_def,Ins_def] >>
     first_x_assum (qspecl_then [‘Sw(M, f0)’] assume_tac) >> fs[]) >>
 arw[] >> rpt strip_tac >>
 last_assum (drule o iffRL) >> fs[SS_def] >>
 first_x_assum irule >> arw[Ins_def])>>
fs[satis_def] >> rw[GSYM csee_Sw_DIAM] >> 
first_x_assum (drule o iffRL) >> fs[Rm_UE] >>
first_x_assum irule >> arw[])
(form_goal “!W M:mem(Pow(W * W) * Exp(W,Pow(A))) phi u.
 IN(Sw(M,phi),Repu(u)) <=> satis(UE(M),u,phi) ”));

val Prop_5_7 = prove_store("Prop_5_7",
e0
(rpt strip_tac >> rw[MEQ_def] >> rw[GSYM Prop_5_8] >>
 rw[Pft_def,Sw_def,SW_def])
(form_goal “!W M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
 MEQ(M,w,UE(M),Pft(w))”));

(*⊢ FIP A J ∧ J ̸= ∅ ⇒ ∃ U . ultrafilter U J ∧ A ⊆ U*)
(*
(rw[FIP_def] >> rpt strip_tac >> ccontra_tac >>
 fs[GSYM IN_EXT_iff,Empty_def,BIGINTER_def] >> 
 qby_tac ‘ss = Sing(Empty(A)) | ss = Empty(Pow(A))’ >-- cheat >>
 pop_assum strip_assume_tac (* 2 *)
 >-- fs[] >> fs[IN_BIGINTER,Sing_def,Sg_def]
     first_x_assum (qspecl_then [‘Sing(Empty(A))’] assume_tac) >>
     fs[Sing_def,Sg_def,SS_def] >> fs[GSYM Sing_def] >>
     qby_tac ‘Fin(Sing(Empty(A)))’ >-- cheat >> fs[] >>
     qby_tac ‘~(!x. ~(x = Empty(A)))’ >-- cheat >> fs[] >>
     cheat (*exists x:mem(A)*) 
 fs[] )
“!A. EMPTY(A) ==> !ss:mem(Pow(Pow(A))). ~FIP(ss)”
*)

val Fin_Sing = prove_store("Fin_Sing",
e0
cheat
(form_goal “!A a:mem(A).Fin(Sing(a))”));

val SATIS_Sing = prove_store("SATIS_Sing",
e0
cheat
(form_goal “!M w:mem(W) f:mem(form(A)). SATIS(M,w,Sing(f)) <=> satis(M,w,f)”));





val Prop_5_9 = prove_store("Prop_5_9",
e0
(strip_tac >> rw[Msat_def] >> rpt strip_tac >>
 qcases ‘EMPTY(W)’ >-- cheat >>
 qby_tac
 ‘?D0. !ws. IN(ws,D0) <=>
  ?ss. Fin(ss) & SS(ss,fs) & 
       (!w. IN(w,ws) <=> SATIS(M,w,ss))’
 >-- cheat >> pop_assum strip_assume_tac >>
 qby_tac
 ‘?Ys. !Y. IN(Y,Ys) <=> IN(osee(M,Y),Repu(w))’
 >-- cheat >> pop_assum strip_assume_tac >>
 qby_tac ‘FIP(Union(D0,Ys))’ >-- 
 (irule FIP_closed_under_Inter >> rpt strip_tac (* 3 *)
  >-- cheat >-- cheat >>
  rfs[] >>
  qsuff_tac ‘?u. (!e1. IN(e1,u) ==> !e2. IN(e2,u) ==> ~(Inter(e1,e2) = Empty(W))) &IN(a,u) & IN(b,u)’
  >-- (strip_tac >> first_x_assum irule >> arw[]) >>
  qby_tac ‘?u. Rm(UE(M),w,u) & SATIS(UE(M),u,ss)’
  >-- (drule $ iffLR Fsab_def >>
      first_x_assum (qsspecl_then [‘ss’] assume_tac) >>
      rfs[] >> drule $ iffLR Sab_def >>
      pop_assum mp_tac >> rw[GSYM Sucm_def]) >>
  pop_assum strip_assume_tac >> qexists_tac ‘Repu(u)’ >>
  qby_tac ‘!e1. IN(e1,Repu(u)) ==> !e2. IN(e2,Repu(u))
  ==> ~(Inter(e1,e2) = Empty(W))’
  >-- cheat (*basic about UF*) >> 
  arw[] >>
  qby_tac ‘IN(a,Repu(u))’ 
  >-- (qsuff_tac ‘?us. SS(us,Repu(u)) & Fin(us) & SS(BIGINTER(us),a) ’
       >-- cheat >>
       qexists_tac ‘IMAGE(SW(M),ss)’ >>
       qby_tac ‘Fin(IMAGE(SW(M),ss))’ 
       >-- (irule IMAGE_FINITE >> arw[]) >> arw[] >>
       qby_tac ‘SS(IMAGE(SW(M), ss), Repu(u))’ 
       >-- (rw[SS_def] >> drule $ iffLR SATIS_def >>
           fs[GSYM Prop_5_8] >> 
           qsuff_tac ‘!a. IN(a, IMAGE(SW(M), ss)) ==>
                      ?f. IN(f,ss) & a = Sw(M,f)’
           >-- (rpt strip_tac >>
               first_x_assum drule >> fs[] >> first_x_assum irule >> arw[]) >>
           rpt strip_tac >> fs[IMAGE_def,SW_def] >>
           qexists_tac ‘a''’ >> arw[Sw_def]) >> arw[] >>
      rw[SS_def] >> rpt strip_tac >>
      arw[SATIS_def] >> rpt strip_tac >>
      fs[IN_BIGINTER] >> 
      first_x_assum (qspecl_then [‘Sw(M,f)’] assume_tac) >>
      fs[Sw_def,SW_def] >> first_x_assum irule >>
      irule IN_App_IMAGE >> arw[]) >>
  qby_tac ‘IN(b,Repu(u))’ 
  >-- (fs[Prop_5_6] >> first_x_assum irule >> arw[]) >> arw[]) >>
 qby_tac ‘?w'. SS(Union(D0,Ys),Repu(w'))’
 >-- (irule Prop_5_3 >> arw[]) >> 
 pop_assum strip_assume_tac >>     
 rw[Sab_def] >> qexists_tac ‘w'’ >>
 strip_tac (* 2 *)
 >-- (rw[Sucm_def,Prop_5_6] >> rpt strip_tac >>
     first_x_assum (drule o iffRL) >>
     qsuff_tac ‘SS(Ys,Repu(w'))’ 
     >-- (arw[SS_def] >> rpt strip_tac >> first_x_assum drule >> arw[]) >>
     irule SS_Trans >>
     qexists_tac ‘Union(D0,Ys)’ >> arw[] >>
     (* union ss lemma *) cheat) >>
 rw[SATIS_def,GSYM Prop_5_8] >> 
 rpt strip_tac >>
 qsuff_tac ‘IN(Sw(M, f), D0)’ 
 >-- cheat (*subset easy*) >>
 arw[] >>
 qexists_tac ‘Sing(f)’ >> rw[Fin_Sing] >>
 arw[SS_def,Sing_def,Sg_def] >>
 rpt strip_tac >-- arw[] >>
 rw[Sw_def,SW_def,GSYM Sing_def,SATIS_Sing])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). Msat(UE(M))”));


(* Z v1 v2 iff ∀ φ. PE φ ∧ M1, v1 􏲖 φ ⇒ M2, v2 􏲖 φ is a simulation. *)

val Thm_6_22 = prove_store("Thm_6_22",
e0
(rpt strip_tac >>
 strip_assume_tac (AX1 |> qspecl [‘W1’,‘W2’] 
 |> fVar_sInst_th “P(v1:mem(W1),v2:mem(W2))”
 “!phi:mem(form(A)). PE(phi) ==> 
          satis(M1,v1:mem(W1),phi) ==> satis(M2,v2:mem(W2),phi)”
 |> uex2ex_rule) >>
 qexists_tac ‘R’ >> arw[] >> rw[Sim_def] >>
 rpt gen_tac >> disch_tac >>
 qby_tac ‘!p. IN(p,App(Vof(M1),w1')) ==> IN(p,App(Vof(M2),w2'))’ 
 >-- (rw[GSYM satis_def] >> strip_tac >>
     first_x_assum (drule o iffLR) >>
     first_x_assum (qspecl_then [‘Var(p)’] assume_tac) >>
     fs[PE_rules]) >> arw[] >> rpt strip_tac >>
 (*qby_tac ‘?d. !phi. IN(phi,d) <=> 
              PE(phi) & satis(M,w1',phi)’ >-- cheat >>*)
 cheat)
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

val satis_Neg = prove_store("satis_Neg",
e0
cheat
(form_goal
 “!M:mem(Pow(W * W) * Exp(W,Pow(A))) w.satis(M, w, Neg(f)) <=> ~satis(M, w, f)”));

val Neg_eq_eq = prove_store("Neg_eq_eq",
e0
cheat
(form_goal “!f1:mem(form(A)) f2.Neg(f1) = Neg(f2) <=> f1 = f2”));


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
 ‘?G. !psi. IN(psi,G) <=>?psi0. psi = Neg(psi0) & PE(psi0) & ~(satis(M,w,psi0))’
 >-- accept_tac (IN_def_P |> qspecl [‘form(A)’]
              |> fVar_sInst_th “P(psi:mem(form(A)))”
                 “?psi0:mem(form(A)). psi = Neg(psi0) & PE(psi0) & 
                                      ~(satis(M,w:mem(W),psi0))”
              |> uex2ex_rule) >>
 pop_assum strip_assume_tac >>
 qby_tac 
 ‘!ss.SS(ss,Ins(f,G)) &  Fin(ss) ==>
  ?V M1:mem(Pow(V * V) * Exp(V,Pow(A))) v.SATIS(M1,v,ss)’
 >-- (rpt strip_tac >> ccontra_tac >>
     qby_tac
     ‘?ss0. !f0. IN(f0,ss0) <=> 
      IN(Neg(f0),Del(ss,f))’ 
     >-- accept_tac (IN_def_P |> qspecl [‘form(A)’]
              |> fVar_sInst_th “P(f0:mem(form(A)))”
                 “IN(Neg(f0),Del(ss,f:mem(form(A))))”
              |> uex2ex_rule) >> 
     pop_assum strip_assume_tac >>
     qby_tac ‘Fin(ss0)’ >-- (*FINITE_Inj*) cheat >>
     qby_tac
     ‘!psi0.IN(Neg(psi0),G) ==> PE(psi0) & ~satis(M,w,psi0)’
     >-- (arw[] >> rw[Neg_eq_eq] >> rpt strip_tac >> rfs[] >> arw[]) >>
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
              qby_tac ‘?f0. f1 = Neg(f0)’ >-- cheat >> fs[] >>
              fs[] >> ccontra_tac  >>
              qby_tac ‘?f0. IN(Neg(f0),Del(ss,f)) & satis(M',w',f0)’ 
              >-- (qexists_tac ‘f0’ >> arw[] >> fs[satis_Neg]) >>
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
         qby_tac ‘IN(Neg(f0'),G)’
         >-- (qsuff_tac ‘SS(Del(ss,f),G)’
             >-- (rw[SS_def] >> rpt strip_tac >>
                 first_x_assum irule >> arw[]) >>
             cheat (* SS(ss, Ins(f, G)) ==> SS(Del(ss, f), G)*)) >>
         pop_assum mp_tac >> arw[] >> strip_tac >>
         fs[Neg_eq_eq]) >>
     first_x_assum drule >> fs[])>>
 drule Thm_6_23 >> pop_assum strip_assume_tac >>
 qby_tac ‘!psi. PE(psi) ==> satis(M',w',psi) ==> satis(M,w,psi)’ 
 >-- (qsuff_tac ‘!psi.PE(psi) ==> ~satis(M,w,psi) ==> ~satis(M',w',psi)’
     >-- (rpt strip_tac >> ccontra_tac >> 
         first_x_assum drule >> first_x_assum drule >> fs[]) >>
     rpt strip_tac >>
     qby_tac ‘IN(Neg(psi),G)’ 
     >-- (first_x_assum (irule o iffRL) >>
         qexists_tac ‘psi’ >> arw[]) >> 
     drule $ iffLR SATIS_def >>
     first_x_assum (qsspecl_then [‘Neg(psi)’] assume_tac) >>
     rfs[Ins_def,satis_Neg]) >>
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

val Thm_6_25_iff = prove_store("Thm_6_25_iff",
e0
(rpt strip_tac >> dimp_tac >> disch_tac 
 >-- (drule Thm_6_25_l2r >> arw[]) >>
 irule Thm_6_25_r2l >> pop_assum strip_assume_tac >>
 qexists_tac ‘f0’ >> arw[])
(form_goal “!A f:mem(form(A)). PUS(f) <=> ?f0. PE(f0) & EQV(f,f0)”))

