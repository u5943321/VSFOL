val ZR_def = 
AX1 |> qspecl [‘N * N’,‘N * N’] |> uex2ex_rule
    |> fVar_sInst_th “P(mn:mem(N * N),m'n':mem(N * N))”
       “Add(Fst(mn:mem(N * N)),Snd(m'n':mem(N * N))) = 
        Add(Fst(m'n'),Snd(mn))”
    |> qSKOLEM "ZR" [] |> store_as "ZR_def";


val ZR_Refl = prove_store("ZR_Refl",
e0
(rw[Refl_def,ZR_def])
(form_goal
 “Refl(ZR)”));



val ZR_ER = prove_store("ZR_ER",
e0
(cheat)
(form_goal “ER(ZR)”));


val Sg_ex = prove_store("Sg_ex",
e0
(cheat)
(form_goal “!A. ?Sg:A-> Pow(A). 
 !a a'.IN(a',App(Sg,a)) <=> a' = a”));

val Sg_def = Sg_ex |> spec_all |> qSKOLEM"Sg" [‘A’] 
                   |> gen_all
                   |> store_as "Sg_def";


val Sing_ex = prove_store("Sing_ex",
e0
(cheat)
(form_goal
 “!A a:mem(A).?sa. sa = App(Sg(A),a)”));

val Sing_def = qdefine_fsym ("Sing",[‘a:mem(A)’])
                            ‘App(Sg(A),a:mem(A))’
                            |> gen_all |> store_as "Sing_def";


val Ri_ex = prove_store("Ri_ex",
e0
(cheat)
(form_goal “!A B r:A~>B. ?Ri:Pow(A) -> Pow(B).
 !s b. IN(b,App(Ri,s)) <=> ?a. IN(a,s) & Holds(r,a,b)”));

val Ri_def = Ri_ex |> spec_all |> qSKOLEM "Ri" [‘r’] 
                   |> gen_all |> store_as "Ri_def";

(*Relational singleton image*)
val Rsi_def = qdefine_fsym ("Rsi",[‘r:A~>B’])
                            ‘Ri(r:A~>B) o Sg(A)’
                            |> gen_all |> store_as "Rsi_def";


val rsi_def = qdefine_fsym ("rsi",[‘r:A~>B’,‘a:mem(A)’])
                            ‘App(Rsi(r),a)’
                            |> gen_all |> store_as "rsi_def";



val rsi_eq_ER = prove_store("rsi_eq_ER",
e0
(cheat)
(form_goal “!A r:A~>A.ER(r) ==> 
 !a1 a2. rsi(r,a1) = rsi(r,a2) <=> Holds(r,a1,a2)”));


val Z_def = Thm_2_4 |> qspecl [‘Pow(N * N)’]
                    |> fVar_sInst_th “P(s:mem(Pow(N * N)))”
                    “?n. s = rsi(ZR,n)”
                    |> qSKOLEM "Z" []
                    |> qSKOLEM "iZ" []
                    |> store_as "Z_def";

val iZ_Inj = Z_def |> conjE1 |> store_as "iZ_Inj"
                   |> store_as "iZ_Inj";


(*as in iN_eq_eq*)
val iZ_eq_eq = iZ_Inj |> rewr_rule[Inj_def]
     

(* (?(n : mem(N * N)). a# = rsi(ZR, n#)) <=>
 ?n1 n2. ... such a conv, to corresponds to L's lambda ver *)

(*compare to iN_inNs*)
val iZ_rsi = prove_store("iZ_rsi",
e0
(strip_tac >> strip_assume_tac Z_def >>
 first_x_assum (qspecl_then [‘App(iZ,z)’] assume_tac) >>
 (*stupid step, ?(b : mem(Z)). App(iZ, z) = App(iZ, b#)*)
 qby_tac ‘?b. App(iZ,z) = App(iZ,b)’ 
 >-- (qexists_tac ‘z’ >> rw[]) >>
 first_x_assum (drule o iffRL) >>
 pop_assum strip_assume_tac >>
 qsspecl_then [‘n’] strip_assume_tac Pair_has_comp >>
 fs[] >> qexistsl_tac [‘a’,‘b’] >> arw[]
 )
(form_goal 
 “!z:mem(Z).?m n. App(iZ,z) = rsi(ZR,Pair(m,n))”));

val rsi_iZ = prove_store("rsi_iZ",
e0
(rpt strip_tac >> strip_assume_tac Z_def >>
 first_x_assum
 (qspecl_then [‘rsi(ZR,Pair(m,n))’] assume_tac) >>
 first_x_assum $ irule o iffLR >>
 qexists_tac ‘Pair(m,n)’ >> rw[])
(form_goal 
 “!m n. ?z. rsi(ZR,Pair(m,n)) = App(iZ,z)”));


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
(rpt strip_tac >> assume_tac 
 (P2fun' |> qspecl [‘Q1’,‘Q2’] 
        |> fVar_sInst_th “P(q1:mem(Q1),q2:mem(Q2))”
           “Holds(rext(f:A->B, r1, r2), 
                      App(i1:Q1->Pow(A), q1), 
                      App(i2:Q2->Pow(B), q2))”) >>
 rw[App_App_o] >> first_x_assum irule >>
 strip_tac >> 
 qby_tac
 ‘!sb.(?!q2. sb = App(i2,q2)) <=> 
       ?b. sb = rsi(r2,b)’ >-- cheat (* easy by injection*)>>
 fs[resp_def] >>
 first_x_assum (qspecl_then [‘App(i1,x)’] assume_tac) >>
 qby_tac ‘?a. App(i1,x) = rsi(r1,a)’ >-- cheat >>
 (*should be auto*)
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘App(Rsi(r2) o f,a)’] 
 assume_tac) >> fs[GSYM rsi_def,App_App_o] >>
 qby_tac
 ‘?!q2:mem(Q2). rsi(r2, App(f, a)) = App(i2, q2)’
 >-- cheat >>
 qsuff_tac ‘!q2:mem(Q2). 
  rsi(r2, App(f, a)) = App(i2, q2) <=> 
  Holds(rext(f, r1, r2), rsi(r1, a), App(i2, q2))’
 >-- cheat >>
 rw[rext_def] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexistsl_tac [‘a’,‘App(f,a)’] >> arw[]) >>
 qsuff_tac ‘?b. App(i2, q2) = rsi(r2, b) & 
 Holds(r2,b,App(f, a))’ >-- 
 (strip_tac >> 
 qpick_x_assum ‘App(i2, q2) = rsi(r2, b')’
 (assume_tac o GSYM) >> arw[] >>
 qby_tac ‘Holds(r2,b,b')’ >-- cheat (*by assum*) >>
 cheat) >>
 qexists_tac ‘b’ >> arw[] >> pop_assum (assume_tac o GSYM) >>
 arw[] >> first_x_assum irule >> cheat
 (*final cheat by assum rsi(r1, a) = rsi(r1, a') *))
(form_goal
“!A B f:A->B r1:A~>A r2:B~>B
 Q1 Q2 i1:Q1->Pow(A) i2:Q2->Pow(B). 
 ER(r1) & ER(r2) & resp(f,r1,r2) & Inj(i1) & Inj(i2) &
 (!sa. (?q1. sa = App(i1,q1)) <=> (?a. sa = rsi(r1,a))) & 
 (!sb. (?q2. sb = App(i2,q2)) <=> (?b. sb = rsi(r2,b))) ==>
 ?qf: Q1-> Q2.
 !q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1)) ”));

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



val addf0_def = proved_th $
e0
cheat
(form_goal “?f:(N * N) * N * N -> N * N. 
 !x y u v. App(f,Pair(Pair(x,y),Pair(u,v))) = 
 Pair(Add(x,u),Add(y,v))”)
|> qSKOLEM "addf0" []
|> store_as "addf0_def";


val negf0_def = fun_tm_compr (dest_var $ rastt "mn:mem(N * N)")
                         (rastt "Pair(Snd(mn:mem(N * N)),Fst(mn))") |> qSKOLEM "negf0" []
      |> store_as "negf0_def";


val negf0_def1 = 
    negf0_def |> qspecl [‘Pair(m:mem(N),n:mem(N))’]
              |> rewr_rule[Pair_def']
              |> gen_all |> store_as "negf0_def1";



val main_addz = 
main |> qspecl [‘(N * N) * (N * N)’,‘N * N’,
                ‘addf0’,
                ‘prrel(ZR,ZR)’,‘ZR’,
                ‘Z * Z’,‘Z’,
                ‘ipow2(iZ,iZ)’,‘iZ’]




val addz_ex = prove_store("addz_ex",
e0
(cheat)
(form_goal
 “?qf: Z* Z ->Z.
     !q1 : mem(Z * Z).
 Holds(rext(addf0, prrel(ZR, ZR), ZR), App(ipow2(iZ, iZ), q1),App(iZ o qf, q1))”));

val addz_def = addz_ex |> qSKOLEM "addz" []


val Addz_def = proved_th $
e0
cheat
(form_goal “!z1 z2.?z. z = App(addz,Pair(z1,z2))”)
|> spec_all |> qSKOLEM "Addz" [‘z1’,‘z2’]
|> gen_all


val addz_property = 
    addz_def |> rewr_rule[rext_def]
             |> qspecl [‘Pair(z1:mem(Z),z2:mem(Z))’]
             |> rewr_rule[App_App_o,GSYM Addz_def]

val addz_prop1 = prove_store("addz_prop1",
e0
cheat
(form_goal
 “?x y u v a b.
        App(ipow2(iZ, iZ), Pair(z1, z2)) = 
        rsi(prrel(ZR, ZR), Pair(Pair(x,y),Pair(u,v))) &
        App(iZ, Addz(z1, z2)) = rsi(ZR, Pair(a,b)) & 
        App(addf0, Pair(Pair(x,y),Pair(u,v))) = Pair(a,b)”));


val addz_prop2 = prove_store("addz_prop2",
e0
cheat
(form_goal
 “?x y u v.
        App(ipow2(iZ, iZ), Pair(z1, z2)) = 
        rsi(prrel(ZR, ZR), Pair(Pair(x,y),Pair(u,v))) &
        App(iZ, Addz(z1, z2)) = rsi(ZR, Pair(Add(x,u),Add(y,v)))”));


val addz_prop3 = prove_store("addz_prop3",
e0
cheat
(form_goal
 “?x y u v.
   (!a b c d.
            IN(Pair(Pair(a,b),Pair(c,d)), App(ipow2(iZ, iZ), Pair(z1, z2))) <=>
            IN(Pair(Pair(a,b),Pair(c,d)), rsi(prrel(ZR, ZR), Pair(Pair(x, y), Pair(u, v)))))  &
        App(iZ, Addz(z1, z2)) = rsi(ZR, Pair(Add(x,u),Add(y,v)))”));


val addz_prop4 = addz_prop3 |> rewr_rule[ipow2_def]



val addz_prop5 = prove_store("addz_prop5",
e0
cheat
(form_goal
 “!z1 z2.?x y u v.
   (!a b c d.
     IN(Pair(a, b), App(iZ, z1)) & 
     IN(Pair(c, d), App(iZ, z2)) <=>
     IN(Pair(a, b), rsi(ZR,Pair(x,y))) & 
     IN(Pair(c, d), rsi(ZR,Pair(u,v))
   ))  &
        App(iZ, Addz(z1, z2)) = rsi(ZR, Pair(Add(x,u),Add(y,v)))”));


val addz_prop6 = prove_store("addz_prop6",
e0
cheat
(form_goal
 “!z1 z2.?x y u v.
   App(iZ,z1) = rsi(ZR,Pair(x,y)) & 
   App(iZ,z2) = rsi(ZR,Pair(u,v)) &
   App(iZ, Addz(z1, z2)) = rsi(ZR, Pair(Add(x,u),Add(y,v)))”));

(*claim: 7 can be automated from 6*)
val addz_prop7 = prove_store("addz_prop7",
e0
cheat
(form_goal
 “!z1 z2 x y u v.
   App(iZ,z1) = rsi(ZR,Pair(x,y)) & 
   App(iZ,z2) = rsi(ZR,Pair(u,v)) ==> 
   App(iZ, Addz(z1, z2)) = rsi(ZR, Pair(Add(x,u),Add(y,v)))”));


val addf0_sym_cong = prove_store("addf0_sym_cong",
e0
cheat
(form_goal “!ab cd. Holds(ZR,App(addf0,Pair(ab,cd)),
                     App(addf0,Pair(cd,ab)))”));

val rsi_eq_ZR = rsi_eq_ER |> qsspecl [‘ZR’] 
                          |> C mp ZR_ER



val eq_ZR = prove_store("eq_ZR",
e0
(cheat)
(form_goal
 “!a b. a = b ==> Holds(ZR,a,b)”));

(*sym reserve for rels*)
val addz_comm = prove_store("addz_comm",
e0
(rpt strip_tac >> irule iZ_eq_eq >> rpt strip_tac >>
 qspecl_then [‘z1’,‘z2’] strip_assume_tac addz_prop6 >>
 qspecl_then [‘z2’,‘z1’] strip_assume_tac addz_prop7 >>
 (*once have cond rw test it here*)
 first_x_assum (qspecl_then [‘u’,‘v’,‘x’,‘y’] assume_tac) >>
 rfs[] >> rw[rsi_eq_ZR] >> irule eq_ZR >> cheat
 (*apply Add_sym on one side *))
(form_goal “!z1 z2. Addz(z1,z2) = Addz(z2,z1)”));

 
A r:A ~eq~>A 
Q >---i---> P(A)
Thm_2_4

A * -----f------> B
|               |
P(A) * ~~~im(f)~~> P(B)
|                |
/\               /\
Q1 ------------> Q2

:Po


L (l1 ~ l2) <=> same member 

map: A-> B |-> List(A) -> List(B)

{(0,a),(1,a')} rep of [a,a']

{} 


{(0,a),.....,(n,a),.....}

CONS h s = (0,h) INSERT (IMAGE (\(n,e). (n^+,e)) s)

colist: num -> a opt

{} colist empty
BIGUNION {x | x ⊆ f x}

iscolist(s) <=> 
?X. ... & IN(s,X)

!e:set of pairs. e in X ==> e = [] | ?h e0. e = e0 :: h0 &
                            e0 in X
