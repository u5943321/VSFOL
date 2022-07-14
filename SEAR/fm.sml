(*Udef can only be abbrev since no set equality*)

val InjN_def = proved_th $
e0
(strip_tac >> irule
 (P2fun_uex |> qspecl [‘N’,‘Pow(N * (A+1))’] 
 |> fVar_sInst_th “P(n0:mem(N),na:mem(Pow(N * (A+1))))”
    “(!n:mem(N) a:mem(A+1).IN(Pair(n,a),na) <=> n = n0)”) >>
 strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘N * (A+1)’] 
 |> fVar_sInst_th “P(na:mem(N * (A+1)))” 
 “Fst(na:mem(N * (A+1))) = x”
 |> conv_rule (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[Pair_def'])
)
(form_goal “!A. ?!injN:N -> Pow(N * (A+1)).
 !n0. (!n a.IN(Pair(n,a),App(injN,n0)) <=> n = n0)”)
|> spec_all |> qsimple_uex_spec "InjN" [‘A’] |> gen_all 


val InjA_def = proved_th $
e0
(strip_tac >> irule
 (P2fun_uex |> qspecl [‘A’,‘Pow(N * (A+1))’] 
 |> fVar_sInst_th “P(a0:mem(A),na:mem(Pow(N * (A+1))))”
    “(!n:mem(N) a:mem(A+1).IN(Pair(n,a),na) <=> a = SOME(a0))”) >>
 strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘N * (A+1)’] 
 |> fVar_sInst_th “P(na:mem(N * (A+1)))” 
    “Snd(na:mem(N * (A+1))) = SOME(x)”
 |> conv_rule (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[Pair_def']))
(form_goal “!A. ?!injA:A -> Pow(N * (A+1)).
 !a0. (!n a.IN(Pair(n,a),App(injA,a0)) <=> a = SOME(a0))”)
|> spec_all |> qsimple_uex_spec "InjA" [‘A’] |> gen_all 


(*pretend div2 is defined*)




(*
VAR not a Bot, NEG, 


*)
                          
val InjUU0_def = proved_th $
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
|> spec_all |> qsimple_uex_spec "InjUU0" [‘A’]

val injUU0_def = 
    qdefine_fsym("injUU0",[‘u1:mem(Pow(N * A))’,‘u2:mem(Pow(N * A))’]) 
                ‘App(InjUU0(A),Pair(u1,u2))’ 


val injUU0_char = prove_store("injUU0_char",
e0
(rpt strip_tac (* 2 *)
 >-- (rw[injUU0_def,InjUU0_def] >> arw[Odd_not_Even]) >> 
 rw[injUU0_def,InjUU0_def] >> arw[Even_not_Odd])
(form_goal “
 (!n. Even(n) ==> (!A u1:mem(Pow(N * A)) u2 a. IN(Pair(n,a),injUU0(u1,u2)) <=> IN(Pair(Div2(n),a),u1))) & 
 (!n. Odd(n) ==> (!A u1:mem(Pow(N * A)) u2 a. IN(Pair(n,a),injUU0(u1,u2)) <=> IN(Pair(Div2(n),a),u2)))”));

val injUU0_Even = injUU0_char |> conjE1
val injUU0_Odd = injUU0_char |> conjE2
                            

val InjUU0_Inj = prove_store("InjUU0_Inj",
e0
(strip_tac >> rw[Inj_def] >> rpt strip_tac >>
 ccontra_tac >>
 qsuff_tac ‘~(App(InjUU0(A), x1) = App(InjUU0(A), x2))’
 >-- arw[] >>
 last_x_assum (K all_tac) >>
 qsspecl_then [‘x1’] (x_choosel_then ["u1","u2"] assume_tac) Pair_has_comp>>
 qsspecl_then [‘x2’] (x_choosel_then ["u3","u4"] assume_tac) Pair_has_comp>>
 fs[] >> fs[Pair_eq_eq] >> rw[GSYM injUU0_def] >> 
 qby_tac ‘~(u1 = u3) | ~(u2 = u4)’
 >-- fs[neg_and_distr] >>
 pop_assum strip_assume_tac >>
 last_x_assum (K all_tac) (* 2 *)
 >-- (fs[set_NEQ] >>
      qsspecl_then [‘a’] (x_choosel_then ["n1","a1"] assume_tac) Pair_has_comp >>
      fs[] >-- (disj1_tac >> qexists_tac ‘Pair(Mul(num2,n1),a1)’ >>
      qsspecl_then [‘Mul(num2,n1)’] assume_tac injUU0_Even >>
      fs[num2_Mul_Even] >> arw[Div2_Mul]) >>
      disj2_tac >> qexists_tac ‘Pair(Mul(num2,n1),a1)’ >>
      qsspecl_then [‘Mul(num2,n1)’] assume_tac injUU0_Even >>
      fs[num2_Mul_Even] >> arw[Div2_Mul]) >>
 fs[set_NEQ] >>
 qsspecl_then [‘a’] (x_choosel_then ["n1","a1"] assume_tac) Pair_has_comp >>
 fs[] 
 >-- (disj1_tac >> qexists_tac ‘Pair(Suc(Mul(num2,n1)),a1)’ >>
      qsspecl_then [‘Suc(Mul(num2,n1))’] assume_tac injUU0_Odd >> 
      fs[Suc_num2_Mul_Odd] >> arw[Div2_Suc_Mul_num2]) >>
disj2_tac >> qexists_tac ‘Pair(Suc(Mul(num2,n1)),a1)’ >>
qsspecl_then [‘Suc(Mul(num2,n1))’] assume_tac injUU0_Odd >> 
fs[Suc_num2_Mul_Odd] >> arw[Div2_Suc_Mul_num2])
(form_goal “!A. Inj(InjUU0(A))”));

val InjUU_def0 = qdefine_fsym("InjUU",[‘A’]) ‘InjUU0(A+1)’ 
|> gen_all

val InjUU_def = InjUU0_def |> gen_all 
                           |> qspecl [‘A+1’]
                           |> rewr_rule[GSYM InjUU_def0]

val InjUU_Inj = InjUU0_Inj |> qspecl [‘A+1’]
                           |> rewr_rule[GSYM InjUU_def0]
                           |> gen_all

val injN_def = qdefine_fsym("injN",[‘A’,‘n:mem(N)’]) ‘App(InjN(A),n)’
val injA_def = qdefine_fsym("injA",[‘a:mem(A)’]) ‘App(InjA(A),a)’ 


(*FALSE *)
val F0_def = qdefine_fsym("F0",[‘A’]) ‘injN(A,O)’

val InjA_Inj = prove_store("InjA_Inj",
e0
(strip_tac >> rw[Inj_def] >> rw[GSYM IN_EXT_iff] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[InjA_def] >> rpt strip_tac >>
 first_x_assum (qspecl_then [‘O’,‘SOME(x1)’] assume_tac) >>
 fs[SOME_eq_eq])
(form_goal “!A. Inj(InjA(A))”));

val VAR0_def = qdefine_fsym("VAR0",[‘A’]) ‘InjUU(A) o Pa(El(injN(A,num1)) o To1(A),InjA(A))’

val VAR0_Inj = prove_store("VAR0_Inj",
e0
(rw[VAR0_def] >> strip_tac >> irule o_Inj_Inj >>
 rw[InjUU_Inj] >> irule Pa_Inj >> rw[InjA_Inj])
(form_goal “!A.Inj(VAR0(A))”));

val Var0_def = qdefine_fsym("Var0",[‘a:mem(A)’]) ‘App(VAR0(A),a)’

val NEG0_def = qdefine_fsym("NEG0",[‘A’]) ‘InjUU(A) o 
Pa(El(injN(A,num2)) o To1(Pow(N * (A+1))),Id(Pow(N * (A+1))))’


val NEG0_Inj = prove_store("NEG0_Inj",
e0
(rw[NEG0_def] >> strip_tac >> irule o_Inj_Inj >>
 rw[InjUU_Inj] >> irule Pa_Inj >> rw[Id_Inj])
(form_goal “!A.Inj(NEG0(A))”));



val Neg0_def = qdefine_fsym("Neg0",[‘f0:mem(Pow(N * (A+1)))’]) ‘App(NEG0(A),f0)’

 
val DISJ0_def = qdefine_fsym("DISJ0",[‘A’]) ‘InjUU(A) o 
Pa(El(injN(A,num3)) o To1(Pow(N * (A+1)) * Pow(N * (A+1))),InjUU(A))’


val DISJ0_Inj = prove_store("DISJ0_Inj",
e0
(rw[DISJ0_def] >> strip_tac >> irule o_Inj_Inj >>
 rw[InjUU_Inj] >> irule Pa_Inj >> rw[InjUU_Inj])
(form_goal “!A.Inj(DISJ0(A))”));


val Disj0_def = qdefine_fsym("Disj0",[‘f1:mem(Pow(N * (A+1)))’,‘f2:mem(Pow(N * (A+1)))’]) ‘App(DISJ0(A),Pair(f1,f2))’

val DIAM0_def = qdefine_fsym("DIAM0",[‘A’])
‘InjUU(A) o 
Pa(El(injN(A,num4)) o To1(Pow(N * (A+1))),Id(Pow(N * (A+1))))’



val DIAM0_Inj = prove_store("DIAM0_Inj",
e0
(rw[DIAM0_def] >> strip_tac >> irule o_Inj_Inj >>
 rw[InjUU_Inj] >> irule Pa_Inj >> rw[Id_Inj])
(form_goal “!A.Inj(DIAM0(A))”));


val Diam0_def = qdefine_fsym("Diam0",[‘f0:mem(Pow(N * (A+1)))’]) ‘App(DIAM0(A),f0)’


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


val isfm_def = qdefine_psym("isfm",[‘f:mem(Pow(N * (A+1)))’])
‘IN(f,isfms(A))’ |> gen_all 



(*isfm_ind cannot be solved by arw with isfm_ind since the bracket of isfm_ind is weird*)
val isfm_induct = prove_store("isfm_induct",
e0
(rw[isfm_def] >> strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘Pow(N * (A+1))’]) >> arw[] >>
 rpt strip_tac >> irule isfm_ind >> arw[])
(form_goal 
 “!A.P(F0(A)) & 
  (!p:mem(A). P(Var0(p))) & 
  (!f0:mem(Pow(N * (A+1))). P(f0) ==> P(Neg0(f0))) &
  (!f1:mem(Pow(N * (A+1))) f2. P(f1) & P(f2) ==> P(Disj0(f1,f2))) &
  (!f0:mem(Pow(N * (A+1))). P(f0) ==> P(Diam0(f0))) ==>
  !f0:mem(Pow(N * (A+1))). isfm(f0) ==> P(f0)”));
 
val isfm_F0 = prove_store("isfm_F0",
e0
(rw[isfm_def,isfm_rules])
(form_goal
 “!A. isfm(F0(A))”)); 


val isfm_clauses = isfm_rules |> rewr_rule[GSYM isfm_def]


val isfm_Neg0 = isfm_clauses |> conjE2 |> conjE2 |> conjE1 

val isfm_Diam0 = isfm_clauses |> conjE2 |> conjE2 |> conjE2 
                              |> conjE2


val isfm_Var0 = prove_store("isfm_Var0",
e0
(rw[isfm_def,isfm_rules])
(form_goal
 “!A p:mem(A). isfm(Var0(p))”)); 


val isfm_Disj0 =  isfm_clauses |> conjE2 |> conjE2 
                               |> conjE2 |> conjE1



val form_def = Thm_2_4'  |> qspecl [‘Pow(N * (A+1))’]
                        |> fVar_sInst_th “P(f:mem(Pow(N * (A+1))))”
                        “isfm(f:mem(Pow(N * (A+1))))”
                        |> set_spec (rastt "Pow(N * (A+1))")
                        "form" "repf" [("A",set_sort)]


val repf_Inj = form_def |> conjE1 |> store_as "repf_Inj"; 

val Repf_def = qdefine_fsym("Repf",[‘f:mem(form(A))’]) ‘App(repf(A),f)’
                           |> gen_all 


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
|> qsimple_uex_spec "Bot" [‘A’]

val VAR_def = Inj_lift_fun_uex |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘VAR0(A)’] 
                           |> rewr_rule[GSYM Var0_def,GSYM form_def,
                                        isfm_clauses]
                           |> qsimple_uex_spec "VAR" [‘A’]


val repf_isfm = prove_store("repf_isfm",
e0
(rw[form_def] >> rpt strip_tac >> rw[Repf_def] >>
 qexists_tac ‘f0’ >> rw[])
(form_goal “!f0:mem(form(A)).isfm(Repf(f0))”));


val VAR_VAR0 = prove_store("VAR_VAR0",
e0
(rw[GSYM FUN_EXT,GSYM Var0_def,VAR_def])
(form_goal “!A. repf(A) o VAR(A) = VAR0(A)”));

val VAR_Inj = prove_store("VAR_Inj",
e0
(strip_tac >> irule Inj_o_Inj >>
 qexistsl_tac [‘Pow(N*(A+1))’,‘repf(A)’] >> rw[VAR_VAR0,VAR0_Inj] )
(form_goal “!A. Inj(VAR(A))”));




val Neg0_Repf = proved_th $
e0
(strip_tac >> irule isfm_Neg0 >> rw[repf_isfm])
(form_goal “!f0:mem(form(A)). isfm(Neg0(Repf(f0)))”)

val NEG_def = Inj_lift_fun_lemma' |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘NEG0(A)’] 
                           |> rewr_rule[App_App_o,GSYM Neg0_def]
                           |> rewr_rule[GSYM form_def,GSYM Repf_def]
                           |> rewr_rule[Neg0_Repf]
                           |> qsimple_uex_spec "NEG" [‘A’]


val NEG_NEG0 = prove_store("NEG_NEG0",
e0
(rw[GSYM FUN_EXT,GSYM Neg0_def,NEG_def,App_App_o,GSYM Repf_def])
(form_goal “!A. repf(A) o NEG(A) = NEG0(A) o repf(A)”));


val NEG_Inj = prove_store("NEG_Inj",
e0
(strip_tac >> irule Inj_o_Inj >>
 qexistsl_tac [‘Pow(N*(A+1))’,‘repf(A)’] >> rw[NEG_NEG0,NEG0_Inj] >>
 irule o_Inj_Inj >> rw[repf_Inj,NEG0_Inj])
(form_goal “!A. Inj(NEG(A))”));



val Diam0_Repf = proved_th $
e0
(strip_tac >> irule isfm_Diam0 >> rw[repf_isfm])
(form_goal “!f0:mem(form(A)). isfm(Diam0(Repf(f0)))”)


val DIAM_def = Inj_lift_fun_lemma' |> qsspecl [‘repf(A)’]
                           |> C mp repf_Inj
                           |> qsspecl [‘DIAM0(A)’] 
                           |> rewr_rule[App_App_o,GSYM Diam0_def]
                           |> rewr_rule[GSYM form_def,GSYM Repf_def]
                           |> rewr_rule[Diam0_Repf]
                           |> qsimple_uex_spec "DIAM" [‘A’]


val form_def_uex = prove_store("form_def_uex",
e0
(strip_tac >> assume_tac repf_Inj >>
 drule Inj_ex_uex >> flip_tac >>
 rw[Repf_def] >> arw[] >>
 rw[form_def] >> lflip_tac >> rw[])
(form_goal “!a:mem(Pow(N * (A+1))).
 (?!b. a = Repf(b)) <=> isfm(a)”));


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
                            |> qsimple_uex_spec "DISJ" [‘A’] 
                            |> rewr_rule[GSYM FUN_EXT] 
                            |>  conv_rule
                            (depth_fconv no_conv forall_cross_fconv)
                            |> rewr_rule[App_App_o,App_Pa_Pair,Pair_def,
                                         GSYM Disj0_def,GSYM Repf_def]
end

val DISJ_DISJ0 = prove_store("DISJ_DISJ0",
e0
(rw[GSYM FUN_EXT,GSYM Disj0_def,DISJ_def,App_App_o,GSYM Repf_def] >>
 strip_tac>> forall_cross_tac >> rw[App_Prla,GSYM Repf_def,DISJ_def] >>
 rw[Disj0_def])
(form_goal “!A. repf(A) o DISJ(A) = DISJ0(A) o Prla(repf(A),repf(A))”));


val DISJ_Inj = prove_store("DISJ_Inj",
e0
(strip_tac >> irule Inj_o_Inj >>
 qexistsl_tac [‘Pow(N*(A+1))’,‘repf(A)’] >> rw[DISJ_DISJ0]>> 
 irule o_Inj_Inj >> rw[DISJ0_Inj] >> irule Prla_Inj >> rw[repf_Inj])
(form_goal “!A. Inj(DISJ(A))”));


val DIAM_DIAM0 = prove_store("DIAM_DIAM0",
e0
(rw[GSYM FUN_EXT,GSYM Diam0_def,DIAM_def,App_App_o,GSYM Repf_def])
(form_goal “!A. repf(A) o DIAM(A) = DIAM0(A) o repf(A)”));


val DIAM_Inj = prove_store("DIAM_Inj",
e0
(strip_tac >> irule Inj_o_Inj >>
 qexistsl_tac [‘Pow(N*(A+1))’,‘repf(A)’] >> rw[DIAM_DIAM0,DIAM0_Inj] >>
 irule o_Inj_Inj >> rw[repf_Inj,DIAM0_Inj])
(form_goal “!A. Inj(DIAM(A))”));

            
val Var_def = qdefine_fsym("Var",[‘a:mem(A)’]) ‘App(VAR(A),a)’

val Neg_def = qdefine_fsym("Neg",[‘f:mem(form(A))’]) ‘App(NEG(A),f)’

val Diam_def = qdefine_fsym("Diam",[‘f:mem(form(A))’]) ‘App(DIAM(A),f)’

val Disj_def = qdefine_fsym("Disj",[‘f1:mem(form(A))’,‘f2:mem(form(A))’])
                           ‘App(DISJ(A),Pair(f1,f2))’




val Var_eq_eq = prove_store("Var_eq_eq",
e0
(rw[Var_def] >> rpt strip_tac >> irule Inj_eq_eq >> rw[VAR_Inj])
(form_goal “!p1 p2:mem(A). Var(p1) = Var(p2) <=> p1 = p2”));


val Neg_eq_eq = prove_store("Neg_eq_eq",
e0
(rw[Neg_def] >> rpt strip_tac >> irule Inj_eq_eq >> rw[NEG_Inj])
(form_goal “!f1 f2:mem(form(A)). Neg(f1) = Neg(f2) <=> f1 = f2”));
 

val Diam_eq_eq = prove_store("Diam_eq_eq",
e0
(rw[Diam_def] >> rpt strip_tac >> irule Inj_eq_eq >> rw[DIAM_Inj])
(form_goal “!f1 f2:mem(form(A)). Diam(f1) = Diam(f2) <=> f1 = f2”));


val Disj_eq_eq = prove_store("Disj_eq_eq",
e0
(rw[Disj_def] >> rpt strip_tac >> rw[GSYM Pair_eq_eq] >>
  irule Inj_eq_eq >> rw[DISJ_Inj])
(form_goal “!f1 f2 g1 g2:mem(form(A)). Disj(f1,f2) = Disj(g1,g2) <=> f1 = g1 & f2 = g2”));

              
val Repf_eq_eq = prove_store("Repf_eq_eq",
e0
(rw[Repf_def] >> rpt strip_tac >> irule Inj_eq_eq >> rw[repf_Inj])
(form_goal “!f1:mem(form(A)) f2. Repf(f1) = Repf(f2) <=> f1 = f2”))

val form_induct = prove_store("form_induct",
e0
(strip_tac >> disch_tac >>
 qsuff_tac ‘!f0:mem(Pow(N * (A+1))). isfm(f0) ==> isfm(f0) &
 !f.Repf(f) = f0 ==> P(f)’ 
 >-- (strip_tac >>
     qby_tac ‘!f0:mem(Pow(N * (A+1))). isfm(f0) ==>
                      (!f. Repf(f) = f0 ==> P(f))’ 
     >-- (rpt strip_tac >> first_x_assum drule >>
          rfs[] >> first_x_assum irule >> arw[]) >>
     strip_tac >> first_x_assum irule >>
     qexists_tac ‘Repf(f0)’ >> rw[repf_isfm]) >>
 ind_with (isfm_induct |> qspecl [‘A’]) >>
 rw[isfm_F0,isfm_Var0] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     qsuff_tac ‘f = Bot(A)’ >-- (strip_tac >> arw[]) >>
     irule $ iffLR Inj_eq_eq >> qexistsl_tac [‘Pow(N * (A+1))’,‘repf(A)’] >>
     arw[repf_Inj,Bot_def,GSYM Repf_def]) >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> 
      qsuff_tac ‘f = Var(p)’ >-- (strip_tac >> arw[]) >>
      irule $ iffLR Inj_eq_eq >> qexistsl_tac [‘Pow(N * (A+1))’,‘repf(A)’] >>
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

val IN_F0 = prove_store("IN_F0",
e0
(rpt strip_tac >> rw[F0_def,injN_def,InjN_def])
(form_goal “!n a. IN(Pair(n,a),F0(A)) <=> n = O”));


val IN_Var0 = prove_store("IN_Var0",
e0
(fs[Var0_def,VAR0_def,App_App_o,InjUU_def,App_Pa_Pair] >>
 fs[El_def,dot_def,injN_def,InjN_def,InjA_def]    )
(form_goal “!n a:mem(A+1). IN(Pair(n,a),Var0(a0)) <=> 
 Even(n) & Div2(n) = num1 | Odd(n) & a = SOME(a0)”));


val IN_Neg0 = prove_store("IN_Neg0",
e0
(fs[Neg0_def,NEG0_def,App_App_o,InjUU_def,App_Pa_Pair] >>
 fs[El_def,dot_def,injN_def,InjN_def,InjA_def,Id_def]    )
(form_goal “!n a:mem(A+1). IN(Pair(n,a),Neg0(f0)) <=> 
 Even(n) & Div2(n) = num2 | Odd(n) & IN(Pair(Div2(n), a), f0)”));



val IN_Diam0 = prove_store("IN_Diam0",
e0
(fs[Diam0_def,DIAM0_def,App_App_o,InjUU_def,App_Pa_Pair] >>
 fs[El_def,dot_def,injN_def,InjN_def,InjA_def,Id_def]    )
(form_goal “!n a:mem(A+1). IN(Pair(n,a),Diam0(f0)) <=> 
 Even(n) & Div2(n) = num4 | Odd(n) & IN(Pair(Div2(n), a), f0)”));


val IN_Disj0 = prove_store("IN_Disj0",
e0
(fs[Disj0_def,DISJ0_def,App_App_o,InjUU_def,App_Pa_Pair] >>
 fs[El_def,dot_def,injN_def,InjN_def,InjA_def,Id_def]    )
(form_goal “!n a:mem(A+1). IN(Pair(n,a),Disj0(f1,f2)) <=> 
 Even(n) & Div2(n) = num3 |
             Odd(n) &
             (Even(Div2(n)) & IN(Pair(Div2(Div2(n)), a), f1) |
               Odd(Div2(n)) & IN(Pair(Div2(Div2(n)), a), f2))”));


val F0_NOT_Var0 = prove_store("F0_NOT_Var0",
e0
(rw[set_NEQ] >> disj1_tac >> qexists_tac ‘Pair(O,SOME(p))’ >>
 rw[IN_F0,IN_Var0] >> rw[Div2_def,Div_of_O,Odd_not_Even,O_NEQ_num1,O_Even] )
(form_goal “~(F0(A) = Var0(p))”));


val Bot_NOT_Var = prove_store("Bot_NOT_Var",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Bot(A)) = Repf(Var(p))’ >-- arw[] >>
 fs[Bot_def,Var_def,VAR_def,F0_NOT_Var0,Repf_def,GSYM App_App_o])
(form_goal “~(Bot(A) = Var(p))”));


val F0_NOT_Disj0 = prove_store("F0_NOT_Disj0",
e0
(rw[set_NEQ] >> disj1_tac >> 
 qexists_tac ‘Pair(O,NONE(A))’ >>
 rw[IN_F0,IN_Disj0] >> rw[Div2_def,Div_of_O,Odd_not_Even,O_NEQ_num3,O_Even] )
(form_goal “~(F0(A) = Disj0(f1,f2))”));


val Bot_NOT_Disj = prove_store("Bot_NOT_Disj",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Bot(A)) = Repf(Disj(f1,f2))’ >-- arw[] >>
 fs[Bot_def,Disj_def,DISJ_def,F0_NOT_Disj0,GSYM App_App_o])
(form_goal “~(Bot(A) = Disj(f1,f2))”));


val F0_NOT_Neg0 = prove_store("F0_NOT_Neg0",
e0
(rw[set_NEQ] >> disj1_tac >> 
 qexists_tac ‘Pair(O,NONE(A))’ >>
 rw[IN_F0,IN_Neg0] >> rw[Div2_def,Div_of_O,Odd_not_Even,O_NEQ_num2,O_Even] )
(form_goal “~(F0(A) = Neg0(f0))”));


val Bot_NOT_Neg = prove_store("Bot_NOT_Neg",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Bot(A)) = Repf(Neg(f))’ >-- arw[] >>
 fs[Bot_def,Neg_def,NEG_def,F0_NOT_Neg0,GSYM App_App_o])
(form_goal “~(Bot(A) = Neg(f))”));


val F0_NOT_Diam0 = prove_store("F0_NOT_Diam0",
e0
(rw[set_NEQ] >> disj1_tac >> 
 qexists_tac ‘Pair(O,NONE(A))’ >>
 rw[IN_F0,IN_Diam0] >> rw[Div2_def,Div_of_O,Odd_not_Even,O_NEQ_num4,O_Even] )
(form_goal “~(F0(A) = Diam0(f0))”));


val Bot_NOT_Diam = prove_store("Bot_NOT_Diam",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Bot(A)) = Repf(Diam(f))’ >-- arw[] >>
 fs[Bot_def,Diam_def,DIAM_def,F0_NOT_Diam0,GSYM App_App_o])
(form_goal “~(Bot(A) = Diam(f))”));


val Bot_NOT = prove_store("Bot_NOT",
e0
(rw[Bot_NOT_Diam,Bot_NOT_Neg,Bot_NOT_Disj,Bot_NOT_Var])
(form_goal “!A. (!p.~(Bot(A) = Var(p))) &
 (!f. ~(Bot(A) = Neg(f))) &
 (!f. ~(Bot(A) = Diam(f))) &
 (!f1 f2. ~(Bot(A) = Disj(f1,f2)))”));

(*
val F0_NOT_Disj0 = prove_store("F0_NOT_Disj0",
e0
(rw[set_NEQ] >> disj1_tac >> 
 qby_tac ‘?a:mem(A). T’ >-- cheat >>
 pop_assum strip_assume_tac >> 
 qexists_tac ‘Pair(O,a)’ >>
 rw[IN_F0,IN_Disj0] >> rw[Div2_def,Div_of_O,Odd_not_Even,O_NEQ_num3,O_Even] )
(form_goal “~(F0(A) = Disj0(f1,f2))”));



val F0_NOT_Neg0 = prove_store("F0_NOT_Neg0",
e0
(rw[set_NEQ] >> disj1_tac >> 
 qby_tac ‘?a:mem(A). T’ >-- cheat >>
 pop_assum strip_assume_tac >> 
 qexists_tac ‘Pair(O,a)’ >>
 rw[IN_F0,IN_Neg0] >> rw[Div2_def,Div_of_O,Odd_not_Even,O_NEQ_num2,O_Even] )
(form_goal “~(F0(A) = Neg0(f0))”));
*)


val InjN_Inj = prove_store("InjN_Inj",
e0
(rw[Inj_def,InjN_def] >> 
 rpt strip_tac >>
 fs[GSYM IN_EXT_iff,InjN_def] >>
 qsuff_tac
 ‘!n. n = x1 <=> n = x2’ 
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘x1’] assume_tac) >> fs[]) >>
 strip_tac >>
 first_x_assum (qspecl_then [‘Pair(n,NONE(A))’] assume_tac) >>
 fs[InjN_def])
(form_goal “!A. Inj(InjN(A))”));

val Var0_NOT_Diam0 = prove_store("Var0_NOT_Diam0",
e0
(rw[Var0_def,Diam0_def,VAR0_def,DIAM0_def,App_App_o] >>
 qspecl_then [‘A’] assume_tac InjUU_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[App_Pa_Pair,App_App_o,Id_def,dot_def,El_def] >>
 rw[injN_def,Pair_eq_eq]  >> 
 qspecl_then [‘A’] assume_tac InjN_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[num1_NEQ_num4])
(form_goal “~(Var0(a:mem(A)) = Diam0(f0))”));

val VAR_def' = VAR_def |> rewr_rule[GSYM Repf_def,App_App_o]

val Var_NOT_Diam = prove_store("Var_NOT_Diam",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Var(a)) = Repf(Diam(f))’ >-- arw[] >>
 fs[Var_def,VAR_def',Diam_def,DIAM_def,Var0_NOT_Diam0,GSYM App_App_o])
(form_goal “~(Var(a:mem(A)) = Diam(f))”));


val Var0_NOT_Disj0 = prove_store("Var0_NOT_Disj0",
e0
(rw[Var0_def,Disj0_def,VAR0_def,DISJ0_def,App_App_o] >>
 qspecl_then [‘A’] assume_tac InjUU_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[App_Pa_Pair,App_App_o,Id_def,dot_def,El_def] >>
 rw[injN_def,Pair_eq_eq]  >> 
 qspecl_then [‘A’] assume_tac InjN_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[num1_NEQ_num3])
(form_goal “~(Var0(a:mem(A)) = Disj0(f1,f2))”));


val Var_NOT_Disj = prove_store("Var_NOT_Disj",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Var(a)) = Repf(Disj(f1,f2))’ >-- arw[] >>
 fs[Var_def,VAR_def',Disj_def,DISJ_def,Var0_NOT_Disj0,GSYM App_App_o])
(form_goal “~(Var(a:mem(A)) = Disj(f1,f2))”));

 
val Var0_NOT_Neg0 = prove_store("Var0_NOT_Neg0",
e0
(rw[Var0_def,Neg0_def,VAR0_def,NEG0_def,App_App_o] >>
 qspecl_then [‘A’] assume_tac InjUU_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[App_Pa_Pair,App_App_o,Id_def,dot_def,El_def] >>
 rw[injN_def,Pair_eq_eq]  >> 
 qspecl_then [‘A’] assume_tac InjN_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[num1_NEQ_num2])
(form_goal “~(Var0(a:mem(A)) = Neg0(f0))”));


val Var_NOT_Neg = prove_store("Var_NOT_Neg",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Var(a)) = Repf(Neg(f))’ >-- arw[] >>
 fs[Var_def,VAR_def',Neg_def,NEG_def,Var0_NOT_Neg0,GSYM App_App_o])
(form_goal “~(Var(a:mem(A)) = Neg(f))”));



val Var_NOT = prove_store("Bot_NOT",
e0
(rw[Var_NOT_Neg,Var_NOT_Disj,Var_NOT_Diam,GSYM Bot_NOT_Var])
(form_goal “!A. (!p.~(Var(p) = Bot(A))) &
 (!p:mem(A) f. ~(Var(p) = Neg(f))) &
 (!p:mem(A) f. ~(Var(p) = Diam(f))) &
 (!p:mem(A) f1 f2. ~(Var(p) = Disj(f1,f2)))”));


val Neg0_NOT_Diam0 = prove_store("Neg0_NOT_Diam0",
e0
(rw[Neg0_def,Diam0_def,NEG0_def,DIAM0_def,App_App_o] >>
 qspecl_then [‘A’] assume_tac InjUU_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[App_Pa_Pair,App_App_o,Id_def,dot_def,El_def] >>
 rw[injN_def,Pair_eq_eq]  >> 
 qspecl_then [‘A’] assume_tac InjN_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[num2_NEQ_num4])
(form_goal “~(Neg0(f:mem(Pow(N*(A+1)))) = Diam0(f0))”));


val Neg_NOT_Diam = prove_store("Neg_NOT_Diam",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Neg(f)) = Repf(Diam(f0))’ >-- arw[] >>
 fs[Neg_def,NEG_def,Diam_def,DIAM_def,Neg0_NOT_Diam0,GSYM App_App_o])
(form_goal “~(Neg(f:mem(form(A))) = Diam(f0))”));



val Neg0_NOT_Disj0 = prove_store("Neg0_NOT_Disj0",
e0
(rw[Neg0_def,Disj0_def,NEG0_def,DISJ0_def,App_App_o] >>
 qspecl_then [‘A’] assume_tac InjUU_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[App_Pa_Pair,App_App_o,Id_def,dot_def,El_def] >>
 rw[injN_def,Pair_eq_eq]  >> 
 qspecl_then [‘A’] assume_tac InjN_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[num2_NEQ_num3])
(form_goal “~(Neg0(f:mem(Pow(N*(A+1)))) = Disj0(f1,f2))”));


val Neg_NOT_Disj = prove_store("Neg_NOT_Disj",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Neg(f)) = Repf(Disj(f1,f2))’ >-- arw[] >>
 fs[Neg_def,NEG_def,Disj_def,DISJ_def,Neg0_NOT_Disj0,GSYM App_App_o])
(form_goal “~(Neg(f:mem(form(A))) = Disj(f1,f2))”));


val Neg_NOT = prove_store("Neg_NOT",
e0
(rw[Neg_NOT_Disj,Neg_NOT_Diam,GSYM Bot_NOT_Neg,GSYM Var_NOT_Neg])
(form_goal “!A. (!f:mem(form(A)).~(Neg(f) = Bot(A))) &
 (!f p:mem(A). ~(Neg(f) = Var(p))) &
 (!f f0:mem(form(A)). ~(Neg(f) = Diam(f0))) &
 (!f:mem(form(A)) f1 f2. ~(Neg(f) = Disj(f1,f2)))”));


val Diam0_NOT_Disj0 = prove_store("Diam0_NOT_Disj0",
e0
(rw[Diam0_def,Disj0_def,DIAM0_def,DISJ0_def,App_App_o] >>
 qspecl_then [‘A’] assume_tac InjUU_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[App_Pa_Pair,App_App_o,Id_def,dot_def,El_def] >>
 rw[injN_def,Pair_eq_eq]  >> 
 qspecl_then [‘A’] assume_tac InjN_Inj >>
 drule Inj_eq_eq >> arw[] >>
 rw[num4_NEQ_num3])
(form_goal “~(Diam0(f:mem(Pow(N*(A+1)))) = Disj0(f1,f2))”));


val Diam_NOT_Disj = prove_store("Diam_NOT_Disj",
e0
(ccontra_tac >>
 qby_tac ‘Repf(Diam(f)) = Repf(Disj(f1,f2))’ >-- arw[] >>
 fs[Diam_def,DIAM_def,Disj_def,DISJ_def,Diam0_NOT_Disj0,GSYM App_App_o])
(form_goal “~(Diam(f:mem(form(A))) = Disj(f1,f2))”));


val Diam_NOT = prove_store("Diam_NOT",
e0
(rw[Diam_NOT_Disj,GSYM Neg_NOT_Diam,GSYM Var_NOT_Diam,GSYM Bot_NOT_Diam])
(form_goal “!A. (!f:mem(form(A)).~(Diam(f) = Bot(A))) &
 (!f p:mem(A). ~(Diam(f) = Var(p))) &
 (!f f0:mem(form(A)). ~(Diam(f) = Neg(f0))) &
 (!f:mem(form(A)) f1 f2. ~(Diam(f) = Disj(f1,f2)))”));



val Disj_NOT = prove_store("Disj_NOT",
e0
(rw[GSYM Neg_NOT_Disj,GSYM Diam_NOT_Disj,GSYM Var_NOT_Disj,GSYM Bot_NOT_Disj])
(form_goal “!A. (!f1 f2:mem(form(A)).~(Disj(f1,f2) = Bot(A))) &
 (!f1 f2 p:mem(A). ~(Disj(f1,f2) = Var(p))) &
 (!f1 f2 f0:mem(form(A)). ~(Disj(f1,f2) = Diam(f0))) &
 (!f1 f2 f:mem(form(A)). ~(Disj(f1,f2) = Neg(f)))”));



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



val fmrec_def = P2fun_uex |> qspecl [‘form(A)’,‘X’] 
                      |> fVar_sInst_th “P(f:mem(form(A)),
                                          x:mem(X))”
                          “IN(Pair(f,x),
                              fminds(djf:X * X ->X,dmf,nf,vf:A->X,x0))”
                      |> C mp (fmind_uex |> spec_all
                                         |> qgen ‘f’)
                      |> qsimple_uex_spec "fmrec" [‘x0’,‘vf’,‘nf’,‘djf’,‘dmf’]
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
