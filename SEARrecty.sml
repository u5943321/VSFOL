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



val Thm_6_25 = prove_store("Thm_6_25",
e0
cheat
(form_goal “!A f:mem(form(A)). PUS(f) <=> ?f0. PE(f0) & EQV(f,f0)”))

