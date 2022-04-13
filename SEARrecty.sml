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


val form_def = Thm_2_4  |> qspecl [‘Pow(N * A)’]
                        |> fVar_sInst_th “P(f:mem(Pow(N * A)))”
                        “isfm(f:mem(Pow(N * A)))”
                        |> qSKOLEM "form" [‘A’]
                        |> qSKOLEM "repf" [‘A’]

val Repf_def = qdefine_fsym("Repf",[‘f:mem(form(A))’]) ‘App(repf(A),f)’
                           |> gen_all 


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

val BOT_def = proved_th $
e0
cheat
(form_goal “?!f. Repf(f) = F0(A)”)
|> uex2ex_rule |> qSKOLEM "BOT" [‘A’]

val VAR_def = qdefine_fsym("VAR",[‘a:mem(A)’]) ‘BOT(A)’

val NEG_def = qdefine_fsym("NEG",[‘f:mem(form(A))’]) ‘BOT(A)’

val DISJ_def = qdefine_fsym("DISJ",[‘f1:mem(form(A))’,‘f2:mem(form(A))’])
                           ‘BOT(A)’

val DIAM_def = qdefine_fsym("DIAM",[‘f:mem(form(A))’]) ‘BOT(A)’


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
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
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
   !f. IN(f,ffs) ==> satis(M,w,f)) ==>
  ?W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
   !f. IN(f,fs) ==> satis(M,w,f) ”));

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

val Thm_6_25 = prove_store("Thm_6_25",
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
     rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
     >-- (qsuff_tac ‘SATIS(M,w,PEC(f))’
          >-- strip_tac >> fs[SS_def] >> )


(qsuff_tac ‘!c.IN(c,PEC(f)) ==> satis(M,w,c)’ 
         >-- (rpt strip_tac >> fs[SS_def] >> first_x_assum irule >>
             first_x_assum irule >> arw[]) >>
         rw[PEC_def,Ent_def] >> rpt strip_tac >> 
         first_x_assum irule >> arw[]) >>
     qpick_x_assum ‘ENT(ffs, f)’ assume_tac >>
     fs[ENT_def] >> first_x_assum irule >> arw[]) >>
 rw[ENT_def] >> rpt strip_tac >> 
 qby_tac
 ‘?G. !psi. IN(psi,G) <=> PE(psi) & ’)
(form_goal “!A f:mem(form(A)). PUS(f) ==> ?f0. PE(f0) & EQV(f,f0)”))

val Thm_6_25_iff = prove_store("Thm_6_25_iff",
e0
cheat
(form_goal “!A f:mem(form(A)). PUS(f) <=> ?f0. PE(f0) & EQV(f,f0)”))

