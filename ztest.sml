
val resp_def = 
 qdefine_psym("resp",[‘f:A->B’,‘r1:A~>A’,‘r2:B~>B’])
 ‘!y z.Holds(r1,y,z) ==> Holds(r2,App(f:A->B,y),App(f,z))’
 |> gen_all |> store_as "resp_def";




val rext_ex = prove_store("rext_ex",
e0
(cheat)
(form_goal
 “!A B f:A->B r1:A~>A r2:B~>B.
 ?e:Pow(A) ~> Pow(B).
  !sa sb. Holds(e,sa,sb) <=> 
   ?a b.sa = rsi(r1,a) & sb = rsi(r2,b) &
    App(f,a) = b”));

val rext_def = rext_ex |> spec_all 
                       |> qSKOLEM "rext"
                       [‘f’,‘r1’,‘r2’]
                       |> gen_all |> store_as "rext_def";

val main = prove_store("main",
e0
cheat
(form_goal
“!A B f:A->B r1:A~>A r2:B~>B
 Q1 Q2 i1:Q1->Pow(A) i2:Q2->Pow(B). 
 ER(r1) & ER(r2) & resp(f,r1,r2) &
 (!sa. (?q1. sa = App(i1,q1)) <=> (?a. sa = rsi(r1,a))) & 
 (!sb. (?q2. sb = App(i2,q2)) <=> (?b. sb = rsi(r2,b))) ==>
 ?qf: Q1-> Q2.
 !q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1)) ”));

(* product rel *)
val prrel_ex = prove_store("prrel_ex",
e0
(cheat)
(form_goal “!A r1:A~>A B r2:B~>B. ?r:A * B ~> A * B.
 !a1 b1 a2 b2.Holds(r,Pair(a1,b1),Pair(a2,b2)) <=> 
 Holds(r1,a1,a2) & Holds(r2,b1,b2)”));

val prrel_def = prrel_ex |> spec_all |> qSKOLEM "prrel"
[‘r1’,‘r2’] |> gen_all |> store_as "prrel_def";



val main = prove_store("main",
e0
cheat
(form_goal
“!A B f:A->B r1:A~>A r2:B~>B
 Q1 Q2 i1:Q1->Pow(A) i2:Q2->Pow(B). 
 ER(r1) & ER(r2) & resp(f,r1,r2) &
 (!sa. (?q1. sa = App(i1,q1)) <=> (?a. sa = rsi(r1,a))) & 
 (!sb. (?q2. sb = App(i2,q2)) <=> (?b. sb = rsi(r2,b))) ==>
 ?qf: Q1-> Q2.
 !q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1)) ”));

(*

Pow(A) * Pow(A) -> Pow(A * A) not have in general.

 *)


val ipow2_ex = prove_store("ipow2_ex",
e0
cheat
(form_goal “!i1:Q1-> Pow(A) i2:Q2 -> Pow(B). 
 ?i: Q1 * Q2 -> Pow(A * B).
 !aq bq.
  !a1 a2.IN(Pair(a1,a2),App(i,Pair(aq,bq))) <=> 
         IN(a1,App(i1,aq)) & IN(a2,App(i2,bq))”));


val ipow2_def = ipow2_ex |> spec_all 
                         |> qSKOLEM "ipow2" [‘i1’,‘i2’]
                         |> gen_all

main |> qspecl [‘(N * N) * (N * N)’,‘N * N’,
                ‘addf0’,
                ‘prrel(ZR,ZR)’,‘ZR’,
                ‘Z * Z’,‘Z’,
                ‘ipow2(iZ,iZ)’,‘iZ’]






“Rsi(prrel(ZR,ZR)) = a”
(*lift_fun_rel*)
val Lfr_def =
    AX1 |> qspecl [‘Y’,‘Y’] |> uex2ex_rule 
        |> fVar_sInst_th “P(y1:mem(Y),y2:mem(Y))”
           “?x1 x2. y1 = App(enc1:X->Y,x1) &
                    y2 = App(enc2,x2) & App(f,x1) = x2”
        |> qSKOLEM "Lfr" [‘f’,‘enc’]
        |> gen_all
        |> store_as "Lfr_def";

