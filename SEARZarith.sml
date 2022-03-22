val ZR_def = 
AX1 |> qspecl [‘N * N’,‘N * N’] |> uex2ex_rule
    |> qSKOLEM "ZR" [] |> store_as "ZR_def";

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

val Z_def = Thm_2_4 |> qspecl [‘Pow(N * N)’]
                    |> fVar_sInst_th “P(s:mem(Pow(N * N)))”
                    “?n. s = rsi(ZR,n)”
                    |> qSKOLEM "Z" []
                    |> qSKOLEM "iZ" []
                    |> store_as "Z_def";

val iZ_Inj = Z_def |> conjE1 |> store_as "iZ_Inj"
                   |> store_as "iZ_Inj";



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

(*
val negrel_def =
    AX1 |> qspecl [‘Pow(N * N)’,‘Pow(N * N)’]
        |> fVar_sInst_th
           “P(s1:mem(Pow(N * N)),s2:mem(Pow(N * N)))”
           “?a b. s1 = rsi(ZR,Pair(a,b)) & 
                  s2 = rsi(ZR,Pair(b,a))”
        |> uex2ex_rule
        |> qSKOLEM "negrel" []
        |> store_as "negrel_def";

*)


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


val respects_def = 
 qdefine_psym("respects",[‘f:A->B’,‘r:A~>A’])
 ‘!y z.Holds(r,y,z) ==> App(f,y) = App(f,z)’
 |> gen_all |> store_as "respects_def";



val resp_def = 
 qdefine_psym("resp",[‘f:A->B’,‘r1:A~>A’,‘r2:B~>B’])
 ‘!y z.Holds(r1,y,z) ==> Holds(r2,App(f:A->B,y),App(f,z))’
 |> gen_all |> store_as "resp_def";

val resp1_def = 
 qdefine_psym("resp1",[‘f:A->A’,‘r:A~>A’])
 ‘!y z.Holds(r,y,z) ==> Holds(r,App(f:A->A,y),App(f,z))’
 |> gen_all |> store_as "resp1_def";

(*if congruent on rep, then have a relation
 R:A0~>A0 with unique condition as in Inj_list_R_lemma
 idea: do not need information about full version at all.
*)

(*have function (m,n) |-> rsi(ZR,Pair(n,m))
  respect to ZR, there exists a relation 
  between the ones that are images??
  
  (m,n) |-> rsi(ZR,Pair(n,m)) N * N -> Pow(N * N)
  (m,n) |-> rsi(ZR,Pair(m,n)) "encode"

the resultant relation will related 
rsi(ZR,Pair(m,n)) to rsi(ZR,Pair(n,m))

give information that how to embed in the natural way, and another function, there is a relation

given a function on base N * N -> N * N, and a way N * N is enbeded in something else, say A0, have an extension 

A0 ~> A0 which relates pairs where:
first is the encode of the element from N * N
the second is the encode of the element after applying the function
*)


(*lift_fun_rel*)
val Lfr_def =
    AX1 |> qspecl [‘A0’,‘A0’] |> uex2ex_rule 
        |> fVar_sInst_th “P(a1:mem(A0),a2:mem(A0))”
           “?x1 x2. a1 = App(enc:X->A0,x1) &
                    a2 = App(enc,x2) & App(f,x1) = x2”
        |> qSKOLEM "Lfr" [‘f’,‘enc’]
        |> gen_all
        |> store_as "Lfr_def";



val negf0_def = fun_tm_compr (dest_var $ rastt "mn:mem(N * N)")
                         (rastt "Pair(Snd(mn:mem(N * N)),Fst(mn))") |> qSKOLEM "negf0" []
      |> store_as "negf0_def";



val addf0_def = proved_th $
e0
cheat
(form_goal “?f:(N * N) * N * N -> N * N. 
 !x y u v. App(f,Pair(Pair(x,y),Pair(u,v))) = 
 Pair(Add(x,u),Add(y,v))”)
|> qSKOLEM "addf0" []
|> store_as "addf0_def";

val negf0_def1 = 
    negf0_def |> qspecl [‘Pair(m:mem(N),n:mem(N))’]
              |> rewr_rule[Pair_def']
              |> gen_all |> store_as "negf0_def1";


(*
val hasflift_def = qdefine_psym("hasflift",[‘R:A0~>A0’,
                                            ‘i:A->A0’])
                   ‘?f:A->A. (!a. Holds(R,App(i,a),App(i o f,a)))’
*)


(*
if enc respect to r, then related r are sent to same element in A0. need if a1 comes from base X, then there exists a unique
element come from base and 
*)




val respects_rel_App_eq = prove_store("respects_rel_App_eq",
e0
(rpt strip_tac >> 
fs[respects_def] >> first_x_assum irule >> arw[])
(form_goal “!X r:X~>X A0 enc:X->A0. respects(enc,r) ==> 
 (!x1 x2. Holds(r,x1,x2) ==>
  !a1 a2. a1 = App(enc,x1) & a2 = App(enc,x2) ==> a1 = a2)”
));

val rel2_def = proved_th $ 
e0
cheat
(form_goal “!r:A~>A. ?r2:A * A ~> A * A.
 !x y u v. Holds(r2,Pair(x,y),Pair(u,v)) <=> 
 Holds(r,x,u) & Holds(r,y,v)
 ”) |> spec_all |> qSKOLEM "rel2" [‘r’]
|> gen_all |> store_as "rel2_def";


val negf0_resp1 = prove_store("negf0_resp1",
e0
(cheat)
(form_goal “resp1(negf0,ZR)”));

val rsi_eq_ER = prove_store("rsi_eq_ER",
e0
(cheat)
(form_goal “!A r:A~>A.ER(r) ==> 
 !a1 a2. rsi(r,a1) = rsi(r,a2) <=> Holds(r,a1,a2)”));

val 
“ER(r:X~>X) & resp1(f:X->X,r) & Inj(i:A->A0) &
(!x.(?a0. a0 = rsi(r,x)) <=> (?b. a = App(i,b))) ==>
!a1. ?!a2. Holds(Lfr(f,r),App(i,a1),App(i,a2))”
(*X is N * N, A0 is Pow(N * N), A is Z*)



val liftfun_ex = prove_store("liftfun_ex",
e0
cheat
(form_goal “ER(r:A~>A) & resp1(f:A->A,r) & Inj(i:X->Pow(A)) &
(!s:mem(Pow(A)).
 (?a:mem(A). s = rsi(r,a)) <=> 
 (?x. s = App(i,x))) ==>
 ?f1:X->X. 
 (!x.Holds(Lfr(f,Rsi(r)),App(i,x),App(i o f1,x)))”));

val liftfun_ex |> rewr_rule[Lfr_def,GSYM rsi_def]



liftfun_ex |> gen_all |> qspecl [‘(N * N) * N * N’,‘addf0’]


“?f1:Z * Z -> Z. 
 (!z. Holds(Lfr(addf0,rel2(Rsi(r))),App(i,x),App(i o addf0,x)))”

addf0: (N * N) * N * N -> N * N

“Lfr(addf0,Rsi(rel2(r))) = a”
val addz_char = prove_store("addz_char",
e0
()
(form_goal “App(iZ,z1) = rsi(ZR,Pair(x,y)) & 
            App(iZ,z2) = rsi(ZR,Pair(u,v)) ==>
            App()”));



(*not need to prove char eqn, define it to be so*)
val neg_lift = prove_store("neg_lift",
e0
(strip_tac >> rw[Lfr_def] >>
qspecl_then [‘z1’] (x_choosel_then ["m","n"] assume_tac)
iZ_rsi >> 
qspecl_then [‘n’,‘m’] strip_assume_tac rsi_iZ >>
uex_tac >> qexists_tac ‘b’ >>
rpt strip_tac (* 2 *)
>-- (qexistsl_tac [‘Pair(m,n)’,‘Pair(n,m)’] >> 
    arw[GSYM rsi_def,negf0_def1]) >>
assume_tac iZ_Inj >> fs[Inj_def] >>
first_x_assum irule >> arw[] >>
qpick_x_assum ‘rsi(ZR, Pair(n, m)) = App(iZ, b)’
(assume_tac o GSYM) >> arw[] >> 
qby_tac ‘Holds(ZR,x1,Pair(m,n))’ >-- cheat >>
qsuff_tac ‘Holds(ZR,x2,Pair(n,m))’ >-- cheat >>
assume_tac negf0_resp1 >> fs[resp1_def] >>
qpick_x_assum ‘App(negf0, x1) = x2’ (assume_tac o GSYM) >>
arw[] >> 
qby_tac ‘Pair(n, m) = App(negf0, Pair(m,n))’ 
>-- rw[negf0_def1] >>
arw[] >> first_x_assum irule >> 
assume_tac ZR_ER >> drule $ GSYM rsi_eq_ER >> arw[])
(form_goal
“!z1. ?!z2. Holds(Lfr(negf0,Rsi(ZR)),App(iZ,z1),App(iZ,z2))”));

val negz_def =
    Inj_lift_R_lemma |> qsspecl [‘iZ’]
                     |> C mp iZ_Inj
                     |> qsspecl [‘Lfr(negf0,Rsi(ZR))’]
                     |> C mp neg_lift
                     |> qSKOLEM "negz" []
                     |> rewr_rule[Lfr_def,GSYM rsi_def]
                     |> store_as "negz_def";




 
val negz_char = prove_store("negz_char",
e0
(rpt strip_tac >>
 strip_assume_tac negz_def >> cheat
 )
(form_goal
 “!z m n.App(iZ,z) = rsi(ZR,Pair(m,n)) ==>
         App(iZ o negz,z) = rsi(ZR,Pair(n,m))”));

(*to prove

!z. neg (neg z ) = z

that is, the subset which satisfies above is the whole thing

sufficient to 

for every z, its rep is in the set of 
*)



val negz_negz = prove_store("negz_negz",
e0
(strip_tac >> assume_tac iZ_Inj >> fs[Inj_def] >>
 first_x_assum irule >> 
 qsspecl_then [‘z’] strip_assume_tac iZ_rsi >>
 drule negz_char >> fs[App_App_o] >>
 drule negz_char >> fs[App_App_o])
(form_goal “!z. App(negz o negz,z) = z”));









(***********)
val ZR_def = 
fVar_Inst 
[("P",([("mn",mem_sort $Cross N N),("m'n'",mem_sort $Cross N N)],
 “Add(Fst(mn:mem(N * N)),Snd(m'n':mem(N * N))) = 
 Add(Fst(m'n'),Snd(mn))”))] 
(AX1 |> qspecl [‘N * N’,‘N * N’] |> uex_expand)
|> ex2fsym0 "ZR" [] |> conjE1
|> store_as "ZR_def";

val ZR_Refl = prove_store("ZR_Refl",
e0
(rw[Refl_def,ZR_def])
(form_goal
 “Refl(ZR)”));

val Pair_Fst_Snd = Pair_component |> rewr_rule[Fst_def,Snd_def] |> store_as "Pair_Fst_Snd";

(*use add_sub*)
val ZR_Trans = prove_store("ZR_Trans",
e0
(rw[Trans_def,ZR_def] >>
 qsuff_tac
 ‘!a1 b1 a2 b2 a3 b3.
  Add(a1,b2) = Add(a2,b1) & Add(a2,b3) = Add(a3,b2) ==>
  Add(a1,b3) = Add(a3,b1)’
 >-- (rpt strip_tac >>
     first_x_assum (qspecl_then [‘Fst(a1)’,‘Snd(a1)’,‘Fst(a2)’,‘Snd(a2)’,‘Fst(a3)’,‘Snd(a3)’] assume_tac) >>
     first_x_assum irule >> arw[]) >>
 rpt strip_tac >>
 irule Add_eq_eq >> qexists_tac ‘b2’ >>
 once_rw[GSYM Add_assoc] >>
 qby_tac
 ‘Add(b3,b2) = Add(b2,b3) & Add(b1,b2) = Add(b2,b1)’ 
 >-- (strip_tac 
     >-- qspecl_then [‘b2’,‘b3’] accept_tac Add_sym
     >-- qspecl_then [‘b2’,‘b1’] accept_tac Add_sym) >>
 arw[] >>
 rw[Add_assoc] >> once_arw[] >> 
 qpick_x_assum ‘Add(a2, b3) = Add(a3, b2)’
 (assume_tac o GSYM) >> once_arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘b3’,‘b1’] assume_tac Add_sym >>
 once_arw[] >> rw[])
(form_goal
 “Trans(ZR)”));

val ZR_Sym = prove_store("ZR_Sym",
e0
(rw[ZR_def,Sym_def] >> rpt strip_tac >> flip_tac >>
 arw[])
(form_goal
 “Sym(ZR)”));

val ZR_ER = prove_store("ZR_ER",
e0
(rw[ER_def,ZR_Refl,ZR_Sym,ZR_Trans])
(form_goal “ER(ZR)”));

val toZ_def = 
Thm_2_14 |> qspecl [‘N * N’,‘ZR’]
         |> C mp ZR_ER
         |> ex2fsym0 "Z" []
         |> ex2fsym0 "toZ" []
         |> store_as "toZ_def";

val zj_ex = prove_store("zj_ex",
e0
(qexists_tac ‘Pair(O,O)’ >> rw[])
(form_goal
 “?zj.Pair(O,O) = zj”));

val zj_def = zj_ex |> ex2fsym0 "0j" []
                   |> store_as "zj_def";


val oj_ex = prove_store("oj_ex",
e0
(qexists_tac ‘Pair(Suc(O),O)’ >> rw[])
(form_goal
 “?oj.Pair(Suc(O),O) = oj”));

val oj_def = oj_ex |> ex2fsym0 "1j" []
                   |> store_as "oj_def";

val negj_def = 
fVar_Inst 
[("P",([("mn",mem_sort $Cross N N),("m'n'",mem_sort $Cross N N)],
 “Fst(mn:mem(N * N)) = Snd(m'n') & Snd(mn) = Fst(m'n')”))] 
(AX1 |> qspecl [‘N * N’,‘N * N’] |> uex_expand)
|> ex2fsym0 "negj" [] |> conjE1
|> store_as "negj_def";

val negj_Fun = prove_store("negj_Fun",
e0
(rw[Fun_expand,negj_def] >> rpt strip_tac 
 >-- (qexists_tac ‘Pair(Snd(a),Fst(a))’ >> 
     rw[Pair_def']) >>
 once_rw[Pair_component] >>
 rw[Pair_eq_eq] >> rw[Fst_def,Snd_def] >>
 pop_assum_list (map_every (assume_tac o GSYM)) >>
 arw[])
(form_goal
 “isFun(negj)”));

val Eval_negj = prove_store("Eval_negj",
e0
(rpt strip_tac >> assume_tac negj_Fun >>
 drule $GSYM Eval_def >> flip_tac >>  
 arw[] >> rw[negj_def] >>
 rw[Pair_def'])
(form_goal
 “!m n. Eval(negj,Pair(m,n)) = Pair(n,m)”));


val Negj_ex = prove_store("Negj_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(negj,mn)’ >> rw[])
(form_goal
 “!mn.?nm.Eval(negj,mn) = nm”));

val Negj_def = Negj_ex |> spec_all |> ex2fsym0 "Negj" ["mn"] |> store_as "Negj_def";

val Negj_property = Eval_negj |> rewr_rule[Negj_def]
                              |> store_as "Negj_property";





val addj_def = 
fVar_Inst 
[("P",([("abcd",mem_sort (Cross (Cross N N) $Cross N N)),("acbd",mem_sort $Cross N N)],
 “Fst(acbd) = Add(Fst(Fst(abcd:mem((N * N) * N * N))),Fst(Snd(abcd))) &
  Snd(acbd) = Add(Snd(Fst(abcd)),Snd(Snd(abcd)))”))] 
(AX1 |> qspecl [‘(N * N) * (N * N)’,‘N * N’] |> uex_expand)
|> ex2fsym0 "addj" [] |> conjE1
|> store_as "addj_def";

val Fst_Snd_eq = Pair_Eval_eq |> rewr_rule[Fst_def,Snd_def] |> store_as "Fst_Snd_eq";

val addj_Fun = prove_store("addj_Fun",
e0
(rw[Fun_expand,addj_def] >> rpt strip_tac 
 >-- (qexists_tac ‘Pair(Add(Fst(Fst(a)), Fst(Snd(a))),Add(Snd(Fst(a)), Snd(Snd(a))))’ >> 
     rw[Pair_def']) >>
 irule Fst_Snd_eq >>
 arw[])
(form_goal
 “isFun(addj)”));

val Eval_addj = prove_store("Eval_addj",
e0
(rpt strip_tac >> assume_tac addj_Fun >>
 drule $GSYM Eval_def >> flip_tac >>  
 arw[] >> rw[addj_def] >>
 rw[Pair_def'])
(form_goal
 “!a b c d. Eval(addj,Pair(Pair(a,b),Pair(c,d))) = Pair(Add(a,c),Add(b,d))”));


val Addj_ex = prove_store("Addj_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(addj,Pair(ab,cd))’ >> rw[])
(form_goal
 “!ab cd.?acbd.Eval(addj,Pair(ab,cd)) = acbd”));

val Addj_def = Addj_ex |> spec_all |> ex2fsym0 "Addj" ["ab","cd"] |> store_as "Addj_def";

val Addj_property = Eval_addj |> rewr_rule[Addj_def]
                              |> store_as "Addj_property";


val J1_i = prove_store("J1_i",
e0
(rw[Addj_property,GSYM Add_assoc,ZR_def])
(form_goal
 “!a b c d e f.
 Holds(ZR,
 Addj(Addj(Pair(a,b),Pair(c,d)),Pair(e,f)),
 Addj(Pair(a,b),Addj(Pair(c,d),Pair(e,f))))”));

val J1_ii = prove_store("J1_ii",
e0
(rw[GSYM zj_def,Addj_property,ZR_def,Add_O])
(form_goal
 “!a b.Holds(ZR,Addj(Pair(a,b),0j),Pair(a,b))”));

val J1_iii = prove_store("J1_iii",
e0
(rw[Addj_property,GSYM zj_def,Negj_property,ZR_def,
    Pair_def',Add_O,Add_O2] >>
 rpt strip_tac >>
 qspecl_then [‘b’,‘a’] assume_tac Add_sym >>
 first_x_assum accept_tac)
(form_goal
 “!a b.Holds(ZR,Addj(Pair(a,b),Negj(Pair(a,b))),0j)”));

val J1_iv = prove_store("J1_iv",
e0
(rw[Addj_property,ZR_def,Pair_def'] >>
 rpt strip_tac >>
 qspecl_then [‘c’,‘a’] assume_tac Add_sym >>
 qspecl_then [‘b’,‘d’] assume_tac Add_sym >> 
 arw[])
(form_goal
 “!a b c d.Holds(ZR,Addj(Pair(a,b),Pair(c,d)),
                    Addj(Pair(c,d),Pair(a,b)))”));


val J2_i = prove_store("J2_i",
e0
(rw[Addj_property,ZR_def,Pair_def'] >>
 rpt strip_tac >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘d'’,‘b'’] assume_tac Add_sym >> arw[] >>
 qspecl_then [‘c’,‘d'’,‘b'’] assume_tac Add_assoc >>
 arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘Add(c',Add(d,b'))’,‘a’] 
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘a’,‘b'’] assume_tac Add_sym >>
 arw[] >>
 qsspecl_then [‘Add(c', Add(b, d))’,‘a'’]
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >> 
 qsuff_tac
 ‘Add(d, Add(a', b)) = Add(b, Add(d, a'))’
 >-- (strip_tac >> arw[]) >>
 qspecl_then [‘Add(a',b)’,‘d’] assume_tac Add_sym >>
 arw[] >> 
 qspecl_then [‘a'’,‘d’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc] >>
 qspecl_then [‘a'’,‘b’] assume_tac Add_sym >> arw[])
(form_goal
 “!a b a' b' c d c' d'. Holds(ZR,Pair(a,b),Pair(a',b')) & Holds(ZR,Pair(c,d),Pair(c',d')) ==>
 Holds(ZR,Addj(Pair(a,b),Pair(c,d)),Addj(Pair(a',b'),Pair(c',d')))”));

val J2_ii = prove_store("J2_ii",
e0
(rw[ZR_def,Negj_property,Pair_def'] >> rpt strip_tac >>
 qspecl_then [‘a'’,‘b’] assume_tac Add_sym >>
 arw[] >> last_x_assum (assume_tac o GSYM) >> arw[] >>
 qspecl_then [‘b'’,‘a’] accept_tac Add_sym)
(form_goal
 “!a b a' b'. Holds(ZR,Pair(a,b),Pair(a',b')) ==>
  Holds(ZR,Negj(Pair(a,b)),Negj(Pair(a',b')))”));

val rep_ex = prove_store("rep_ex",
e0
(strip_tac >> assume_tac toZ_def >>
 fs[Surj_def] >> 
 first_x_assum $ qspecl_then [‘z’] strip_assume_tac >>
 qexists_tac ‘x’ >> arw[] >>
 qexistsl_tac [‘Fst(x)’,‘Snd(x)’] >>
 qsspecl_then [‘x’] accept_tac Pair_Fst_Snd)
(form_goal
 “!z. ?rz. Eval(toZ,rz) = z & ?a b. rz = Pair(a,b)”));

val rep_def = rep_ex |> spec_all |> ex2fsym0 "rep" ["z"] |> gen_all |> store_as "rep_def";

val Eval_rep = rep_def |> spec_all |> conjE1
                       |> gen_all |> store_as "Eval_rep";

val rcp_def = rep_def |> spec_all |> conjE2
                      |> ex2fsym0 "rfst" ["z"]
                      |> ex2fsym0 "rsnd" ["z"]
                      |> gen_all
                      |> store_as "rcp_def";

val Eval_rcp = Eval_rep |> rewr_rule[rcp_def]
                        |> store_as "Eval_rcp";

val asz_ex = prove_store("asz_ex",
e0
(strip_tac >> qexists_tac ‘Eval(toZ,ab)’ >> rw[])
(form_goal
 “!ab.?z.Eval(toZ,ab) = z”));

val asz_def = asz_ex |> spec_all |> ex2fsym0 "asz" ["ab"] |> gen_all |> store_as "asz_def";

val rep_asz = Eval_rep |> rewr_rule[asz_def];

val Z = mk_fun "Z" []
(*
val ADDz_def = 
fVar_Inst 
[("P",([("z1z2",mem_sort $Cross Z Z),("z",mem_sort Z)],
 “Holds(ZR,Addj(
  Pair(rfst(Fst(z1z2)),rsnd(Fst(z1z2))),
  Pair(rfst(Snd(z1z2)),rsnd(Snd(z1z2)))),Pair(rfst(z),rsnd(z)))”))] 
(AX1 |> qspecl [‘Z * Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "ADDz" [] |> conjE1

*)

val ADDz_def = 
fVar_Inst 
[("P",([("z1z2",mem_sort $Cross Z Z),("z",mem_sort Z)],
 “Holds(ZR,Addj(rep(Fst(z1z2)),rep(Snd(z1z2))),rep(z))”))] 
(AX1 |> qspecl [‘Z * Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "ADDz" [] |> conjE1
|> store_as "ADDz_def";


val rep_asz_ZR = prove_store("rep_asz_ZR",
e0
(rw[GSYM asz_def] >>
 assume_tac Eval_rep >>
 rw[toZ_def] >> arw[])
(form_goal
 “!ab.Holds(ZR,ab,rep(asz(ab)))”));

val corres_z_uex = prove_store("corres_z_uex",
e0
(strip_tac >> uex_tac >>
 qexists_tac ‘asz(ab)’ >> rw[rep_asz_ZR] >>
 rpt strip_tac >> 
 fs[toZ_def,asz_def] >> rw[rep_asz])
(form_goal
 “!ab.?!z.Holds(ZR,ab,rep(z))”));

val ADDz_Fun = prove_store("ADDz_Fun",
e0
(rw[Fun_expand,ADDz_def] >> rpt strip_tac >--
 (qexists_tac ‘asz(Addj(rep(Fst(a)), rep(Snd(a))))’ >>
 rw[rep_asz_ZR]) >>
 qspecl_then [‘Addj(rep(Fst(a)), rep(Snd(a)))’]
 assume_tac corres_z_uex  >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘b1 = z & b2 = z’
 >-- (strip_tac >> arw[]) >> strip_tac >>
 first_x_assum irule >> first_x_assum accept_tac)
(form_goal
 “isFun(ADDz)”));

val Addz_ex = prove_store("Addz_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Eval(ADDz,Pair(z1,z2))’ >> rw[])
(form_goal
 “!z1 z2.?z12. Eval(ADDz,Pair(z1,z2)) = z12”));

val Addz_def = Addz_ex |> spec_all 
                       |> ex2fsym0 "Addz" ["z1","z2"] 
                       |> gen_all
                       |> store_as "Addz_def";

val Addz_eqn = prove_store("Addz_eqn",
e0
(rpt strip_tac >>
 rw[GSYM Addz_def] >>
 assume_tac ADDz_Fun >>
 drule $ GSYM Eval_def >> 
 flip_tac >> arw[] >>
 rw[ADDz_def,Pair_def',rep_asz_ZR])
(form_goal
 “!z1 z2.
  Addz(z1,z2) = asz(Addj(rep(z1),rep(z2)))”));

(*rep_asz_ZR*)


val ZR_samez = prove_store("ZR_samez",
e0
(rw[toZ_def,GSYM asz_def])
(form_goal
 “!ab cd. Holds(ZR,ab,cd) <=> asz(ab) = asz(cd)”));

val Addz_sym = prove_store("Addz_sym",
e0
(rw[Addz_eqn] >> rw[GSYM ZR_samez] >> rpt strip_tac>>
 once_rw[rcp_def] >> rw[J1_iv])
(form_goal
 “!z1 z2. Addz(z1,z2) = Addz(z2,z1)”));

val rep_ZR_eq = prove_store("rep_ZR_eq",
e0
(rw[ZR_samez,rep_asz])
(form_goal
 “!z1 z2. 
  Holds(ZR,rep(z1),rep(z2)) <=> z1 = z2 ”));

val z_eq_cond = prove_store("z_eq_cond",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (qexistsl_tac [‘rep(z1)’,‘rep(z2)’] >>
      arw[rep_asz,rep_ZR_eq]) >>
 fs[ZR_samez])
(form_goal
 “!z1 z2. z1 = z2 <=>
  ?ab cd. asz(ab) = z1 & asz(cd) = z2 & Holds(ZR,ab,cd)”));

val ZR_refl = prove_store("ZR_refl",
e0
(assume_tac ZR_Refl >>fs[Refl_def])
(form_goal
 “!ab. Holds(ZR,ab,ab)”));

val ZR_sym = ZR_Sym |> rewr_rule[Sym_def]
                    |> store_as "ZR_sym"; 

val ZR_trans = ZR_Trans |> rewr_rule[Trans_def]
                        |> store_as "ZR_trans";

val ZR_cond = prove_store("ZR_cond",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (qexistsl_tac [‘ab’,‘cd’] >> 
      arw[ZR_refl]) >>
 qby_tac ‘Holds(ZR,ab,cd1)’
 >-- (irule ZR_trans >> qexists_tac ‘ab1’ >> arw[]) >>
 qby_tac ‘Holds(ZR,cd1,cd)’ 
 >-- (irule ZR_sym >> arw[]) >>
 irule ZR_trans >>
 qexists_tac ‘cd1’ >> arw[])
(form_goal
 “!ab cd. Holds(ZR,ab,cd) <=>
 ?ab1 cd1. Holds(ZR,ab,ab1) & Holds(ZR,cd,cd1) &
 Holds(ZR,ab1,cd1)”));


(*
have (a,b) ~ (a',b') 
     (c,d) ~ (c',d') 
==> addj((a,b),(c,d)) ~ addj((a',b'),(c',d'))

want (a + b) + c = a + b + c

that is ((a1,a2) + (b1,b2)) + (c1,c2)
       ~  (a1,a2) + (b1,b2) + (c1,c2)

*)

val ADDz_alt0 = prove_store("ADDz_alt0",
e0
(rpt strip_tac >>
 assume_tac ADDz_def >> 
 arw[] >> rw[Pair_def'])
(form_goal
 “!z1 z2 z12. 
  Holds(ADDz,Pair(z1,z2),z12) <=>
  Holds(ZR,Addj(rep(z1),rep(z2)),rep(z12))”));


val rep_rel_all = prove_store("rep_rel_all",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
      irule ZR_sym >> rw[rep_asz_ZR]) >>
 fs[ZR_samez,rep_asz])
(form_goal
 “!z rz.asz(rz) = z <=> Holds(ZR,rep(z),rz)”));

val ADDz_alt0' = prove_store("ADDz_alt0",
e0
(rpt strip_tac >> rw[ADDz_alt0] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexistsl_tac [‘rep(z1)’,‘rep(z2)’,‘rep(z12)’] >>
     arw[rep_asz]) >>
 irule $ iffRL ZR_cond >>
 qexistsl_tac [‘Addj(r1,r2)’,‘r12’] >>
 arw[] >> strip_tac >-- 
 (once_rw[rcp_def] >>
 qsspecl_then [‘r1’] assume_tac Pair_Fst_Snd >>
 once_arw[] >>
 qsspecl_then [‘r2’] assume_tac Pair_Fst_Snd >>
 once_arw[] >>
 irule J2_i >> rw[Pair_def'] >>
 rw[GSYM rcp_def] >> rw[GSYM Pair_Fst_Snd] >>
 strip_tac (* 2*) >>
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 fs[rep_rel_all]) >>
 fs[rep_rel_all])
(form_goal
 “!z1 z2 z12. 
  Holds(ADDz,Pair(z1,z2),z12) <=>
  ?r1 r2 r12. asz(r1) = z1 & asz(r2) = z2 & 
              asz(r12) = z12 &
  Holds(ZR,Addj(r1,r2),r12)”));


val J2_i_z = prove_store("J2_i_z",
e0
(rpt strip_tac >> assume_tac J2_i >>
 rw[GSYM Addz_def] >> assume_tac ADDz_Fun >>
 drule $ GSYM Eval_def >> flip_tac >> arw[] >>
 once_rw[ADDz_alt0'] >>
 qexistsl_tac [‘Pair(a,b)’,‘Pair(c,d)’,
                ‘Addj(Pair(a, b), Pair(c, d))’] >>
 rw[] >> rw[ZR_refl])
(form_goal
 “!z1 z2 a b c d. z1 = asz(Pair(a,b)) & z2 = asz(Pair(c,d)) ==>
 Addz(z1,z2) = asz(Addj(Pair(a,b),Pair(c,d)))”));


(*
val J1_1' = prove_store("J1_1'",
e0
()
(form_goal
 “!a b c d e f a' b' c' d' e' f'.
  Holds(ZR,Pair(a,b),Pair(a',b')) &
  Holds(ZR,Pair(c,d),Pair(c',d')) & 
  Holds(ZR,Pair(e,f),Pair(e',f')) ==>
  Holds”));

*)


val Addz_eqn' = prove_store("Addz_eqn'",
e0
(rpt strip_tac >>
 assume_tac J2_i_z >>
 first_x_assum irule >> rw[])
(form_goal
 “!a b c d.
  Addz(asz(Pair(a,b)),asz(Pair(c,d))) = 
  asz(Addj(Pair(a,b),Pair(c,d)))”));

val z_has_rep = prove_store("z_has_rep",
e0
(strip_tac >> qexistsl_tac [‘rfst(z)’,‘rsnd(z)’] >>
 rw[GSYM rcp_def,rep_asz])
(form_goal
 “!z. ?a b. z = asz(Pair(a,b))”));

val Addz_assoc = prove_store("Addz_assoc",
e0
(rpt strip_tac >> 
 qspecl_then [‘z1’] strip_assume_tac z_has_rep >>
 qspecl_then [‘z2’] strip_assume_tac z_has_rep >>
 qspecl_then [‘z3’] strip_assume_tac z_has_rep >>
 arw[] >> 
 rw[Addz_eqn'] >> rw[Addj_property] >>
 rw[Addz_eqn'] >> rw[GSYM Addj_property] >>
 assume_tac J1_i >> fs[ZR_samez])
(form_goal
 “!z1 z2 z3.Addz(Addz(z1,z2),z3) = Addz(z1,Addz(z2,z3))”));

val zz_ex = prove_store("zz_ex",
e0
(qexists_tac ‘asz(0j)’ >> rw[])
(form_goal
 “?z. asz(0j) = z”));

val zz_def = zz_ex |> ex2fsym0 "0z" []
                   |> store_as "zz_def";


val Addz_zz = prove_store("Addz_zz",
e0
(strip_tac >> once_rw[z_eq_cond] >>
 qspecl_then [‘z’] strip_assume_tac z_has_rep >> 
 arw[] >>
 assume_tac J1_ii >>
 fs[ZR_samez] >> 
 rw[GSYM zz_def] >> rw[GSYM zj_def,Addz_eqn'] >>
 rw[zj_def] >> arw[] >>
 qexistsl_tac [‘Pair(a,b)’,‘Pair(a,b)’] >> rw[])
(form_goal
 “!z. Addz(z,0z) = z”));



val NEGz_def = 
fVar_Inst 
[("P",([("z",mem_sort Z),("nz",mem_sort Z)],
 “asz(Negj(rep(z))) = nz”))] 
(AX1 |> qspecl [‘Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "NEGz" [] |> conjE1
|> store_as "NEGz_def";

val NEGz_Fun = prove_store("NEGz_Fun",
e0
(rw[Fun_expand,NEGz_def] >> rpt strip_tac >-- 
 (qexists_tac ‘asz(Negj(rep(a)))’ >> rw[]) >>
 pop_assum_list (map_every (assume_tac o GSYM)) >>
 arw[])
(form_goal
 “isFun(NEGz)”));

val Negz_ex = prove_store("Negz_ex",
e0
(strip_tac >> qexists_tac ‘Eval(NEGz,z)’ >> rw[])
(form_goal
 “!z. ?nz. Eval(NEGz,z) = nz”));

val Negz_def = Negz_ex |> spec_all 
                       |> ex2fsym0 "Negz" ["z"]
                       |> gen_all 
                       |> store_as "Negz_def";

val NEGz_alt0 = prove_store("NEGz_alt0",
e0
(rw[NEGz_def,ZR_samez,rep_asz])
(form_goal
 “!z nz. Holds(NEGz,z,nz) <=>
      Holds(ZR,Negj(rep(z)),rep(nz))”));


val NEGz_alt0' = prove_store("NEGz_alt0'",
e0
(rw[NEGz_alt0] >> rpt strip_tac >> 
 dimp_tac >> strip_tac 
 >-- (qexistsl_tac [‘rep(z)’,‘rep(nz)’] >> rw[rep_asz]
 >> arw[]) >>
 irule $ iffRL ZR_cond >>
 qexistsl_tac [‘Negj(rz)’,‘rnz’] >>
 arw[] >>
 arw[ZR_samez,rep_asz] >>
 once_rw[GSYM ZR_samez] >>
 qsspecl_then [‘rep(z)’] assume_tac Pair_Fst_Snd >>
 once_arw[] >>
 qsspecl_then [‘rz’] assume_tac Pair_Fst_Snd >>
 once_arw[] >> 
 irule J2_ii >> rw[Pair_def'] >>
 rw[GSYM Pair_Fst_Snd] >>
 arw[GSYM rep_rel_all])
(form_goal
 “!z nz. Holds(NEGz,z,nz) <=>
  (?rz rnz. asz(rz) = z & asz(rnz) = nz & 
  Holds(ZR,Negj(rz),rnz))”));

val J2_ii_z = prove_store("J2_ii_z",
e0
(rpt strip_tac >> assume_tac J2_ii >>
 rw[GSYM Negz_def] >> assume_tac NEGz_Fun >>
 drule $ GSYM Eval_def >> flip_tac >> arw[] >>
 irule $ iffRL NEGz_alt0' >>
(* once_rw[NEGz_alt0] behavior weird, use irule instead *)
 qexistsl_tac [‘Pair(a,b)’,‘Negj(Pair(a,b))’] >> rw[] >>
 rw[ZR_refl])
(form_goal
 “!z a b. z = asz(Pair(a,b)) ==>
  Negz(z) = asz(Negj(Pair(a,b)))”));

val Negz_eqn = prove_store("Negz_eqn",
e0
(rpt strip_tac >> irule J2_ii_z >> arw[])
(form_goal
 “!a b. Negz(asz(Pair(a,b))) = asz(Negj(Pair(a,b)))”));

val Z2_iii = prove_store("Z2_iii",
e0
(rpt strip_tac >>
 qspecl_then [‘z’] strip_assume_tac z_has_rep >> 
 arw[] >> rw[Negz_eqn,Addz_eqn',Negj_property,Addj_property] >> rw[GSYM zz_def]  >>
 rw[GSYM ZR_samez,ZR_def,Pair_def',GSYM zj_def,Add_O,Add_O2] >>
 qspecl_then [‘b’,‘a’] accept_tac Add_sym)
(form_goal
 “!z. Addz(z,Negz(z)) = 0z”));

val lej_def = 
fVar_Inst 
[("P",([("ab",mem_sort $ Cross N N),("cd",mem_sort $ Cross N N)],
 “Le(Add(Fst(ab),Snd(cd)),Add(Snd(ab),Fst(cd)))”))] 
(AX1 |> qspecl [‘(N * N)’, ‘N * N’] |> uex_expand)
|> ex2fsym0 "lej" [] |> conjE1
|> store_as "lej_def";

val lej_property = prove_store("lej_property",
e0
(rw[lej_def,Pair_def'])
(form_goal
 “!a b c d.Holds(lej,Pair(a,b),Pair(c,d)) <=>
 Le(Add(a,d),Add(b,c))”));

val lej_Refl = prove_store("lej_Refl",
e0
(rw[Refl_def,lej_def] >> rpt strip_tac >>
 qspecl_then [‘Fst(a)’,‘Snd(a)’] assume_tac Add_sym >>
 arw[] >> rw[Le_refl])
(form_goal
 “Refl(lej)”));

val Pair_has_comp = prove_store("Pair_has_comp",
e0
(rpt strip_tac >> 
 qexistsl_tac [‘Fst(ab)’,‘Snd(ab)’]>>
 rw[GSYM Pair_Fst_Snd])
(form_goal
 “!A B ab:mem(A * B). ?a b. ab = Pair(a,b)”));


(*LESS_EQ_LESS_EQ_MONO

LESS_EQ_MONO_ADD_EQ

LESS_EQ_TRANS
*)

(*
val LESS_EQ_LESS_EQ_MONO = prove_store("LESS_EQ_LESS_EQ_MONO",
e0
(rpt strip_tac >>
 irule )
(form_goal “!m n p q. Le(m,p) & Le(n,q) ==> Le(Add(m,n),Add(p,q)) ”));
*)


(*
Add(a, b''), Add(b, a'')

(a + b'' <= b + a''
sufficient to prove 
a + b' + a'+ b'' <= b + b' +a' + a''
a + b' + a' + b'' <= b + a' + a' + b''

)

*)

val lej_Trans = prove_store("lej_Trans",
e0
(rw[lej_def,Trans_def] >> rpt strip_tac >>
 qsspecl_then  [‘a1’] assume_tac Pair_has_comp >>
 qsspecl_then  [‘a2’] assume_tac Pair_has_comp >>
 qsspecl_then  [‘a3’] assume_tac Pair_has_comp >>
 fs[] >> fs[] >> fs[Pair_def'] >> 
 qsuff_tac ‘Le(Add(Add(a,b''),Add(a',b')),
               Add(Add(b,a''),Add(a',b')))’
 >-- rw[LESS_EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘Add(a,b')’,‘Add(a',b'')’,
               ‘Add(b,a')’,‘Add(b',a'')’]
 assume_tac Le_Add >> rfs[] >>
 qsuff_tac ‘Add(Add(a, b'), Add(a', b'')) = 
 Add(Add(a, b''), Add(a', b')) & 
 Add(Add(b, a'), Add(b', a'')) = 
 Add(Add(b, a''), Add(a', b'))’
 >-- (strip_tac >> fs[]) >> strip_tac >--
 (once_rw[Add_sym] >>
 qsspecl_then [‘b''’,‘a’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc] >> 
 qsspecl_then [‘b''’,‘Add(a',b')’] assume_tac Add_sym>>
 arw[] >> rw[GSYM Add_assoc] >>
 qsspecl_then [‘a’,‘b'’] assume_tac Add_sym >>
 once_arw[] >> rw[Add_assoc] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac Add_sym >>
 once_arw[] >> rw[]) >>
 qsspecl_then [‘Add(b',a'')’,‘Add(b,a')’]
 assume_tac Add_sym >> arw[] >>
 qsspecl_then [‘a''’,‘b'’] assume_tac Add_sym >> arw[]>>
 qsspecl_then [‘a''’,‘b’] assume_tac Add_sym >> arw[]>>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(b', Add(b, a')) = Add(b, Add(a', b'))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘b'’,‘a'’] assume_tac Add_sym >>
 arw[] >>
 rw[Add_assoc] >> 
 qsspecl_then [‘b'’,‘b’] assume_tac Add_sym >> arw[])
(form_goal
 “Trans(lej)”));


(*TODO: something like AP_TERM_TAC*)
val J1_x = prove_store("J1_x",
e0
(rw[lej_def,Pair_def',Addj_property] >>
 rpt strip_tac >> 
 qsuff_tac 
 ‘Le(Add(Add(a, d), Add(e, f)), Add(Add(b, c), Add(e,f))) &
  Add(Add(a, e), Add(d, f)) = Add(Add(a, d), Add(e, f)) & 
  Add(Add(b, f), Add(c, e)) = Add(Add(b, c), Add(e, f))’
 >-- (rpt strip_tac >> arw[]) >>
 rpt strip_tac (* 3 *)
 >-- arw[LESS_EQ_MONO_ADD_EQ]
 >-- (rw[GSYM Add_assoc] >>
      qsuff_tac ‘Add(e, Add(d, f)) = Add(d, Add(e, f))’ 
      >-- (strip_tac >> arw[]) >>
      rw[Add_assoc] >>
      qsspecl_then [‘d’,‘e’] assume_tac Add_sym >> arw[]) >>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(f, Add(c, e)) = Add(c, Add(e, f))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘Add(c,e)’,‘f’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc])
(form_goal
 “!a b c d e f. Holds(lej,Pair(a,b),Pair(c,d)) ==> 
 Holds(lej,Addj(Pair(a,b),Pair(e,f)),
           Addj(Pair(c,d),Pair(e,f)))”));

val J2_iv = prove_store("J2_iv",
e0
(once_rw[lej_def] >> once_rw[ZR_def] >> rw[Pair_def'] >>
 rpt strip_tac >> 
 qsuff_tac 
 ‘(Le(Add(a, d), Add(b, c)) <=> 
  Le(Add(Add(a,d),Add(b',d')), Add(Add(b,c),Add(b',d')))) &
  (Le(Add(Add(a,d),Add(b',d')), Add(Add(b,c),Add(b',d'))) <=> 
  Le(Add(Add(a',d'),Add(b,d)), Add(Add(b',c'),Add(b,d)))) & 
  (Le(Add(Add(a',d'),Add(b,d)), Add(Add(b',c'),Add(b,d))) <=> 
 Le(Add(a',d'), Add(b',c')))’
 >-- (rpt strip_tac >> arw[]) >> rpt strip_tac (* 2 *)
 >-- rw[LESS_EQ_MONO_ADD_EQ] 
 >-- (qsuff_tac ‘Add(Add(a, d), Add(b', d')) = 
                Add(Add(a', d'), Add(b, d)) & 
                Add(Add(b, c), Add(b', d')) = 
                Add(Add(b', c'), Add(b, d))’
     >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
     >-- (qsspecl_then [‘Add(b',d')’,‘Add(a,d)’] 
          assume_tac Add_sym >> arw[] >>
          qsspecl_then [‘d'’,‘b'’] assume_tac Add_sym >> arw[] >>
          rw[Add_assoc] >>
          qsuff_tac ‘Add(Add(d', b'), a) = 
                     Add(Add(a', d'), b)’
          >-- (strip_tac >> arw[]) >>
          qsspecl_then [‘d'’,‘a'’] assume_tac Add_sym >> arw[] >>
          rw[GSYM Add_assoc] >> 
          qsspecl_then [‘a’,‘b'’] assume_tac Add_sym >> arw[]) >>
     qsspecl_then [‘Add(b',d')’,‘Add(b,c)’] assume_tac Add_sym >>
     arw[] >> 
     qsspecl_then [‘c’,‘b’] assume_tac Add_sym >> arw[] >>
     qsspecl_then [‘d’,‘b’] assume_tac Add_sym >> arw[] >>
     rw[Add_assoc] >>
     qsuff_tac ‘Add(Add(b', d'), c) = Add(Add(b', c'), d)’ 
     >-- (strip_tac >> arw[]) >>
     rw[GSYM Add_assoc] >>
     qsspecl_then [‘c’,‘d'’] assume_tac Add_sym >> arw[]) >>
 rw[LESS_EQ_MONO_ADD_EQ]
 )
(form_goal “!a b c d a' b' c' d'. Holds(ZR,Pair(a,b),Pair(a',b')) &
 Holds(ZR,Pair(c,d),Pair(c',d')) ==> 
 (Holds(lej,Pair(a,b),Pair(c,d)) <=> Holds(lej,Pair(a',b'),Pair(c',d')))”));

val LEz_def = 
fVar_Inst 
[("P",([("z1",mem_sort Z),("z2",mem_sort Z)],
 “Holds(lej,rep(z1),rep(z2))”))] 
(AX1 |> qspecl [‘Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "LEz" [] |> conjE1
|> store_as "LEz_def";

val LEz_Refl = prove_store("LEz_Refl",
e0
(rw[Refl_def,LEz_def] >> 
 assume_tac lej_Refl >> fs[Refl_def])
(form_goal “Refl(LEz)”));

val LEz_Trans = prove_store("LEz_Trans",
e0
(assume_tac lej_Trans >> fs[Trans_def] >> rw[LEz_def] >> 
 rpt strip_tac >> 
 qsspecl_then [‘rep(a1)’] assume_tac Pair_has_comp >> 
 qsspecl_then [‘rep(a2)’] assume_tac Pair_has_comp >>
 qsspecl_then [‘rep(a3)’] assume_tac Pair_has_comp >>
 pop_assum_list (map_every strip_assume_tac) >>
 arw[] >> first_x_assum irule >> rfs[] >>
 qexists_tac ‘Pair(a',b')’ >> arw[]
 )
(form_goal “Trans(LEz)”));


val LEz_Asym = prove_store("LEz_Asym",
e0
(rw[Asym_def,LEz_def] >> strip_tac >> strip_tac >> 
 qsspecl_then [‘rep(a)’] assume_tac Pair_has_comp >> 
 qsspecl_then [‘rep(b)’] assume_tac Pair_has_comp >>
 pop_assum_list (map_every strip_assume_tac) >> arw[] >>
 rw[lej_def,Pair_def'] >>
 strip_tac >> once_rw[z_eq_cond] >>
 qexistsl_tac [‘Pair(a'',b'')’,‘Pair(a',b')’] >>
 rw[ZR_def,Pair_def'] >> rpt strip_tac 
 >-- (pop_assum_list (map_every (assume_tac o GSYM)) >>
      arw[rep_asz]) 
 >-- (pop_assum_list (map_every (assume_tac o GSYM)) >>
      arw[rep_asz]) >>
 irule Le_asym >> 
 qsspecl_then [‘a''’,‘b'’] assume_tac Add_sym >>fs[] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac Add_sym >> fs[])
(form_goal “Asym(LEz)”));

val _ = new_pred "Total" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val Total_def = store_ax("Total_def",“!A R:A~>A.Total(R)<=> !a b. Holds(R,a,b) | Holds(R,b,a)”);


val LEz_Total = prove_store("LEz_Total",
e0
(rw[Total_def,LEz_def,lej_def] >> rpt strip_tac >>
 qsspecl_then [‘rep(a)’] assume_tac Pair_has_comp >> 
 qsspecl_then [‘rep(b)’] assume_tac Pair_has_comp >>
 pop_assum_list (map_every strip_assume_tac) >> arw[Pair_def'] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac Add_sym >> arw[] >>
 qsspecl_then [‘a''’,‘b'’] assume_tac Add_sym >> arw[] >>
 rw[LESS_EQ_cases] )
(form_goal “Total(LEz)”));

val Z = mk_fun "Z" []

val _ = new_pred "Lez" [("z1",mem_sort Z),("z2",mem_sort Z)]

val Lez_def = store_ax("Lez_def",
“!z1 z2.Lez(z1,z2) <=> Holds(LEz,z1,z2)”);


(*

val Z2_x = prove_store("Z2_x",
e0
(rpt strip_tac >>
 
rw[Lez_def,Addz_eqn',Addj_property,LEz_def])
(form_goal “!z1 z2 z3.Lez(z1,z2) ==>
            Lez(Addz(z1,z3), Addz(z2,z3))”));
*)


val J2_iv' = prove_store("J2_iv'",
e0
(rpt strip_tac >> 
 qsspecl_then [‘ab’] assume_tac Pair_has_comp >>
 qsspecl_then [‘ab'’] assume_tac Pair_has_comp >>
 qsspecl_then [‘cd’] assume_tac Pair_has_comp >>
 qsspecl_then [‘cd'’] assume_tac Pair_has_comp >>
 pop_assum_list (map_every strip_assume_tac) >> rfs[] >>
 irule J2_iv >> arw[])  
(form_goal
 “!ab cd ab' cd'. Holds(ZR,ab,ab') & Holds(ZR,cd,cd') ==> 
 (Holds(lej,ab,cd) <=> Holds(lej,ab',cd'))”));

val ZR_sym_iff = prove_store("ZR_sym_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >>
 drule ZR_sym >> arw[])
(form_goal
 “!a1 a2. Holds(ZR,a1,a2) <=> Holds(ZR,a2,a1)”));

val Z2_x = prove_store("Z2_x",
e0
(rw[Lez_def,Addz_eqn',Addj_property,LEz_def] >>
 rpt strip_tac >>
 qsuff_tac 
 ‘Holds(lej,Pair(a, b),Pair(c, d)) ==> 
  Holds(lej, Pair(Add(a, e), Add(b, f)),
             Pair(Add(c, e), Add(d, f)))’ >--
 (rpt strip_tac >>
 qby_tac ‘Holds(lej, Pair(a, b), Pair(c, d)) ’
 >-- (irule $ iffLR J2_iv' >>
      qexistsl_tac 
      [‘rep(asz(Pair(a, b)))’,‘rep(asz(Pair(c, d)))’]>>
      arw[] >> rw[GSYM rep_rel_all]) >>
 first_x_assum drule >> 
 irule $ iffLR J2_iv' >> 
 qexistsl_tac
 [‘Pair(Add(a, e), Add(b, f))’,‘Pair(Add(c, e), Add(d, f))’] >>
 arw[] >> once_rw[ZR_sym_iff] >> rw[GSYM rep_rel_all]) >>
 pop_assum (K all_tac) >>
 rw[lej_property] >> rpt strip_tac >>
 qsspecl_then [‘Add(d,f)’,‘Add(a,e)’] assume_tac Add_sym >>
 arw[] >> rw[Add_assoc] >> rw[LESS_EQ_MONO_ADD_EQ] >>
 once_rw[Add_sym] >> rw[Add_assoc] >>
 rw[LESS_EQ_MONO_ADD_EQ] >> 
 qsspecl_then [‘c’,‘b’] assume_tac Add_sym >> fs[]
 )
(form_goal “!a b c d e f.Lez(asz(Pair(a,b)),asz(Pair(c,d))) ==>
            Lez(Addz(asz(Pair(a,b)),asz(Pair(e,f))),
                Addz(asz(Pair(c,d)),asz(Pair(e,f))))”));




val mulj_def = 
fVar_Inst 
[("P",([("abcd",mem_sort (Cross (Cross N N) $Cross N N)),("m",mem_sort $Cross N N)],
 “Fst(m:mem(N * N)) = 
  Add(Mul(Fst(Fst(abcd)),Fst(Snd(abcd))),
      Mul(Snd(Fst(abcd)),Snd(Snd(abcd)))) &
  Snd(m) = 
  Add(Mul(Fst(Fst(abcd)),Snd(Snd(abcd))),
      Mul(Snd(Fst(abcd)),Fst(Snd(abcd))))”))] 
(AX1 |> qspecl [‘(N * N) * (N * N)’,‘N * N’] |> uex_expand)
|> ex2fsym0 "mulj" [] |> conjE1
|> store_as "mulj_def";


val mulj_Fun = prove_store("mulj_Fun",
e0
(rw[Fun_expand,mulj_def] >> rpt strip_tac 
 >-- (qexists_tac ‘Pair(Add(Mul(Fst(Fst(a)), Fst(Snd(a))),
                  Mul(Snd(Fst(a)), Snd(Snd(a)))), Add(Mul(Fst(Fst(a)), Snd(Snd(a))),
                  Mul(Snd(Fst(a)), Fst(Snd(a)))))’ >> 
     rw[Pair_def']) >>
 irule Fst_Snd_eq >>
 arw[])
(form_goal
 “isFun(mulj)”));

val Eval_mulj = prove_store("Eval_mulj",
e0
(rpt strip_tac >> assume_tac mulj_Fun >>
 drule $GSYM Eval_def >> flip_tac >>  
 arw[] >> rw[mulj_def] >>
 rw[Pair_def'])
(form_goal
 “!a b c d. Eval(mulj,Pair(Pair(a,b),Pair(c,d))) = 
Pair(Add(Mul(a,c),Mul(b,d)),Add(Mul(a,d),Mul(b,c)))”));


val Mulj_ex = prove_store("Mulj_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(mulj,Pair(ab,cd))’ >> rw[])
(form_goal
 “!ab cd.?m.Eval(mulj,Pair(ab,cd)) = m”));

val Mulj_def = Mulj_ex |> spec_all |> ex2fsym0 "Mulj" ["ab","cd"] |> store_as "Mulj_def";

val Mulj_property = Eval_mulj |> rewr_rule[Mulj_def]
                              |> store_as "Mulj_property";


val J1_v = prove_store("J1_v",
e0
(rpt strip_tac >> rw[ZR_def,Mulj_property] >>
 rw[Pair_def'] >> rw[LEFT_DISTR] >>
 rw[RIGHT_DISTR] >> 
 rw[GSYM Add_assoc] >> rw[GSYM Mul_assoc] >> 
 qsuff_tac
 ‘Add(Mul(b, Mul(d, e)),
                 Add(Mul(a, Mul(d, f)),
                  Add(Mul(b, Mul(c, f)),
                   Add(Mul(a, Mul(c, f)),
                    Add(Mul(a, Mul(d, e)),
                     Add(Mul(b, Mul(c, e)), Mul(b, Mul(d, f)))))))) = Add(Mul(a, Mul(d, f)),
                 Add(Mul(b, Mul(c, f)),
                  Add(Mul(b, Mul(d, e)),
                   Add(Mul(a, Mul(c, f)),
                    Add(Mul(b, Mul(d, f)),
                     Add(Mul(a, Mul(d, e)), Mul(b, Mul(c, e))))))))’ >-- (strip_tac >> arw[]) >>
 qsspecl_then 
 [‘Mul(b, Mul(d, e))’,
  ‘Add(Mul(a, Mul(d, f)),
                 Add(Mul(b, Mul(c, f)),
                  Add(Mul(a, Mul(c, f)),
                   Add(Mul(a, Mul(d, e)),
                    Add(Mul(b, Mul(c, e)), Mul(b, Mul(d, f)))))))’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(a, Mul(c, f)),
                  Add(Mul(a, Mul(d, e)),
                   Add(Mul(b, Mul(c, e)),
                    Add(Mul(b, Mul(d, f)), Mul(b, Mul(d, e)))))) =
 Add(Mul(b, Mul(d, e)),
                  Add(Mul(a, Mul(c, f)),
                   Add(Mul(b, Mul(d, f)),
                    Add(Mul(a, Mul(d, e)), Mul(b, Mul(c, e))))))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then 
 [‘Mul(b, Mul(d, e))’,
  ‘Add(Mul(a, Mul(c, f)),
                 Add(Mul(b, Mul(d, f)),
                  Add(Mul(a, Mul(d, e)), Mul(b, Mul(c, e)))))’]
 assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(a, Mul(d, e)),
                 Add(Mul(b, Mul(c, e)),
                  Add(Mul(b, Mul(d, f)), Mul(b, Mul(d, e))))) = 
  Add(Mul(b, Mul(d, f)),
                 Add(Mul(a, Mul(d, e)),
                  Add(Mul(b, Mul(c, e)), Mul(b, Mul(d, e)))))’ 
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘Mul(b, Mul(d, f))’,
 ‘Add(Mul(a, Mul(d, e)),
                 Add(Mul(b, Mul(c, e)), Mul(b, Mul(d, e))))’]
 assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsspecl_then 
 [‘Mul(b, Mul(d, f))’,‘Mul(b, Mul(d, e))’]
 assume_tac Add_sym' >> arw[])
(form_goal “!a b c d e f. 
 Holds(ZR,Mulj(Mulj(Pair(a,b),Pair(c,d)),Pair(e,f)), 
          Mulj(Pair(a,b),Mulj(Pair(c,d),Pair(e,f))))”));


val ZR_def_alt = prove_store("ZR_def_alt",
e0
(rw[ZR_def] >> rpt strip_tac >>  
 qsspecl_then [‘Fst(cd)’,‘Snd(ab)’] assume_tac Add_sym' >>
 arw[])
(form_goal “!ab cd. Holds(ZR,ab,cd) <=> 
  Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))”));

val J2_iii = prove_store("J2_iii",
e0
(strip_tac >> strip_tac >>  strip_tac >>  strip_tac >>  strip_tac >>  strip_tac >>  strip_tac >>  strip_tac >>  
 rw[ZR_def_alt,Mulj_property,Pair_def'] >> 
 abbrev_tac 
 “Add(Mul(p,c),Add(Mul(q,c),Add(Mul(p,d),Mul(q,d)))) = l” >>
 strip_tac >>
 qsuff_tac 
 ‘Add(Add(Add(Mul(a, c), Mul(b, d)), Add(Mul(p, s), Mul(q, r))),l) = 
  Add(Add(Add(Mul(a, d), Mul(b, c)), Add(Mul(p, r), Mul(q, s))),l)’ 
 >-- (rw[EQ_MONO_ADD_EQ] >> rpt strip_tac >> arw[]) >> 
 qby_tac
 ‘Add(Mul(Add(a,q),c),
      Add(Mul(Add(b,p),d),
          Add(Mul(p,Add(c,s)),Mul(q,Add(d,r))))) = 
  Add(Mul(Add(b,p),c),
      Add(Mul(Add(a,q),d),
          Add(Mul(p,Add(d,r)),Mul(q,Add(c,s)))))’ 
 >-- arw[] >> 
 qsuff_tac
 ‘Add(Add(Add(Mul(a, c), Mul(b, d)), Add(Mul(p, s), Mul(q, r))), l) = 
  Add(Mul(Add(a,q),c),
      Add(Mul(Add(b,p),d),
          Add(Mul(p,Add(c,s)),Mul(q,Add(d,r))))) & 
 Add(Add(Add(Mul(a, d), Mul(b, c)), Add(Mul(p, r), Mul(q, s))), l) = 
  Add(Mul(Add(b,p),c),
      Add(Mul(Add(a,q),d),
          Add(Mul(p,Add(d,r)),Mul(q,Add(c,s)))))’
 >-- (strip_tac >> arw[]) >>
 pop_assum $ K (all_tac) >> pop_assum $ K (all_tac) >>
 pop_assum $ K (all_tac) >> strip_tac
 >-- (pop_assum mp_tac >>
     pop_assum_list (map_every (K all_tac)) >>
     strip_tac >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[GSYM Add_assoc,RIGHT_DISTR,LEFT_DISTR] >>
     qsuff_tac
     ‘Add(Mul(b, d),
                 Add(Mul(p, s),
                  Add(Mul(q, r),
                   Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d))))))) = 
     Add(Mul(q, c),
                 Add(Mul(b, d),
                  Add(Mul(p, d),
                   Add(Mul(p, c), Add(Mul(p, s), Add(Mul(q, d), Mul(q, r)))))))’
     >-- (strip_tac >> arw[]) >>
     qsspecl_then 
     [‘Mul(q,c)’,
     ‘Add(Mul(b, d),
                 Add(Mul(p, d),
                  Add(Mul(p, c), Add(Mul(p, s), Add(Mul(q, d), Mul(q, r))))))’] assume_tac Add_sym' >>
     arw[GSYM Add_assoc] >>
     qsuff_tac
     ‘Add(Mul(p, s),
                 Add(Mul(q, r),
                  Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))))) = 
      Add(Mul(p, d),
                 Add(Mul(p, c),
                  Add(Mul(p, s), Add(Mul(q, d), Add(Mul(q, r), Mul(q, c))))))’
     >-- (strip_tac >> arw[]) >>
     qsspecl_then [‘Mul(p,d)’,
     ‘Add(Mul(p, c),
      Add(Mul(p, s), Add(Mul(q, d), Add(Mul(q, r), Mul(q, c)))))’] assume_tac Add_sym' >> arw[] >>
     rw[GSYM Add_assoc] >>
     qsspecl_then 
     [‘Mul(p,c)’,
      ‘Add(Mul(p, s),
                 Add(Mul(q, d), Add(Mul(q, r), Add(Mul(q, c), Mul(p, d)))))’] assume_tac Add_sym' >>
     arw[GSYM Add_assoc] >>
     qsuff_tac 
     ‘Add(Mul(q, r),
                 Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d))))) = 
      Add(Mul(q, d),
                 Add(Mul(q, r), Add(Mul(q, c), Add(Mul(p, d), Mul(p, c)))))’
     >-- (strip_tac >> arw[]) >>
     qsspecl_then [‘Mul(q,d)’,
     ‘Add(Mul(q, r), Add(Mul(q, c), Add(Mul(p, d), Mul(p, c))))’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
     qsuff_tac
     ‘Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))) = Add(Mul(q, c), Add(Mul(p, d), Add(Mul(p, c), Mul(q, d))))’ >-- (strip_tac >> arw[]) >>
     qsspecl_then [‘Mul(p, c)’,‘Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))’] assume_tac Add_sym' >> 
     arw[GSYM Add_assoc] >>
     qsspecl_then [‘Mul(q,d)’,‘Mul(p,c)’]
     assume_tac Add_sym' >> arw[]) 
>-- (
pop_assum (mp_tac o GSYM) >> 
pop_assum_list (map_every (K all_tac)) >>
strip_tac >> arw[] >>
pop_assum (K all_tac) >>
rw[GSYM Add_assoc,LEFT_DISTR,RIGHT_DISTR] >> 
qsspecl_then [‘Mul(a,d)’,
‘Add(Mul(b, c),
                 Add(Mul(p, r),
                  Add(Mul(q, s),
                   Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))))))’] assume_tac Add_sym' >>
arw[GSYM Add_assoc] >>
qsuff_tac
‘Add(Mul(p, r),
                 Add(Mul(q, s),
                  Add(Mul(p, c),
                   Add(Mul(q, c), Add(Mul(p, d), Add(Mul(q, d), Mul(a, d))))))) = 
 Add(Mul(p, c),
                 Add(Mul(a, d),
                  Add(Mul(q, d),
                   Add(Mul(p, d), Add(Mul(p, r), Add(Mul(q, c), Mul(q, s)))))))’
>-- (strip_tac >> arw[]) >>
qsspecl_then [‘Mul(p, r)’,
‘Add(Mul(q, s),
                 Add(Mul(p, c),
                  Add(Mul(q, c), Add(Mul(p, d), Add(Mul(q, d), Mul(a, d))))))’] assume_tac Add_sym' >>
arw[GSYM Add_assoc] >>
qsspecl_then [‘Mul(q, s)’,
‘Add(Mul(p, c),
                 Add(Mul(q, c),
                  Add(Mul(p, d), Add(Mul(q, d), Add(Mul(a, d), Mul(p, r))))))’] assume_tac Add_sym' >>
arw[GSYM Add_assoc] >>
qsuff_tac
‘Add(Mul(q, c),
                 Add(Mul(p, d),
                  Add(Mul(q, d), Add(Mul(a, d), Add(Mul(p, r), Mul(q, s)))))) =
 Add(Mul(a, d),
                 Add(Mul(q, d),
                  Add(Mul(p, d), Add(Mul(p, r), Add(Mul(q, c), Mul(q, s))))))’
>-- (strip_tac >> arw[]) >>
rw[Add_assoc] >> 
qsspecl_then
[‘Add(Add(Add(Add(Mul(a, d), Mul(q, d)), Mul(p, d)),
                  Mul(p, r)), Mul(q, c))’,‘Mul(q,s)’]
assume_tac Add_sym' >> arw[] >>
rw[Add_assoc] >>
qsspecl_then 
[‘Add(Add(Add(Add(Mul(q, s), Mul(a, d)), Mul(q, d)),
                  Mul(p, d)), Mul(p, r))’,‘Mul(q,c)’]
assume_tac Add_sym' >> arw[] >>
rw[GSYM Add_assoc] >>
qsuff_tac
 ‘Add(Mul(p, d),
                 Add(Mul(q, d), Add(Mul(a, d), Add(Mul(p, r), Mul(q, s))))) = 
 Add(Mul(q, s),
                 Add(Mul(a, d), Add(Mul(q, d), Add(Mul(p, d), Mul(p, r)))))’
>-- (strip_tac >> arw[]) >>
rw[Add_assoc] >>
qsspecl_then
[‘Add(Add(Add(Mul(p, d), Mul(q, d)), Mul(a, d)), Mul(p, r))’,‘Mul(q,s)’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
qsuff_tac
‘Add(Mul(p, d), Add(Mul(q, d), Add(Mul(a, d), Mul(p, r))))=
Add(Mul(a, d), Add(Mul(q, d), Add(Mul(p, d), Mul(p, r))))’
>-- (strip_tac >> arw[]) >>
qsspecl_then
[‘Mul(p, d)’,
 ‘Add(Mul(q, d), Add(Mul(a, d), Mul(p, r)))’]
assume_tac Add_sym' >>
arw[GSYM Add_assoc] >>
qsspecl_then
[‘Mul(q, d)’,
 ‘Add(Mul(a, d), Add(Mul(p, r), Mul(p, d)))’]
assume_tac Add_sym' >>
arw[GSYM Add_assoc] >>
qsuff_tac
‘Add(Mul(p, r), Add(Mul(p, d), Mul(q, d))) = 
 Add(Mul(q, d), Add(Mul(p, d), Mul(p, r)))’
>-- (strip_tac >> arw[]) >>
qsspecl_then
[‘Mul(p, r)’,‘Add(Mul(p, d), Mul(q, d))’]
assume_tac Add_sym' >> arw[Add_assoc] >> 
qsspecl_then [‘Mul(p,d)’,‘Mul(q,d)’] assume_tac Add_sym' >>
arw[]
 ))
(form_goal
“!a b p q c d r s. Holds(ZR,Pair(a,b),Pair(p,q)) & 
Holds(ZR,Pair(c,d),Pair(r,s)) ==> 
 Holds(ZR,Mulj(Pair(a,b),Pair(c,d)),Mulj(Pair(p,q),Pair(r,s)))”));



val J2_iii' = prove_store("J2_iii'",
e0
(rpt strip_tac >>
 qsspecl_then [‘ab’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘pq’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘cd’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘rs’] strip_assume_tac Pair_has_comp >> fs[] >>
 irule J2_iii >> arw[])
(form_goal
 “!ab pq cd rs. Holds(ZR,ab,pq) & Holds(ZR,cd,rs) ==>
 Holds(ZR,Mulj(ab,cd),Mulj(pq,rs))”));


val MULz_def = 
fVar_Inst 
[("P",([("z1z2",mem_sort $Cross Z Z),("z",mem_sort Z)],
 “Holds(ZR,Mulj(rep(Fst(z1z2)),rep(Snd(z1z2))),rep(z))”))] 
(AX1 |> qspecl [‘Z * Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "MULz" [] |> conjE1
|> store_as "MULz_def";



val MULz_Fun = prove_store("MULz_Fun",
e0
(rw[Fun_expand,MULz_def] >> rpt strip_tac >--
 (qexists_tac ‘asz(Mulj(rep(Fst(a)), rep(Snd(a))))’ >>
 rw[rep_asz_ZR]) >>
 qspecl_then [‘Mulj(rep(Fst(a)), rep(Snd(a)))’]
 assume_tac corres_z_uex  >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘b1 = z & b2 = z’
 >-- (strip_tac >> arw[]) >> strip_tac >>
 first_x_assum irule >> first_x_assum accept_tac)
(form_goal
 “isFun(MULz)”));


val Mulz_ex = prove_store("Mulz_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Eval(MULz,Pair(z1,z2))’ >> rw[])
(form_goal
 “!z1 z2.?z12. Eval(MULz,Pair(z1,z2)) = z12”));

val Mulz_def = Mulz_ex |> spec_all 
                       |> ex2fsym0 "Mulz" ["z1","z2"] 
                       |> gen_all
                       |> store_as "Mulz_def";


val Mulz_eqn = prove_store("Mulz_eqn",
e0
(assume_tac J2_iii' >> rpt strip_tac >>
 rw[GSYM Mulz_def,GSYM MULz_def] >>
 assume_tac MULz_Fun >> drule $ GSYM Eval_def >>
 flip_tac >> arw[] >>
 rw[MULz_def] >>
 rw[Pair_def'] >> 
 once_rw[ZR_cond] >>
 qexistsl_tac
 [‘Mulj(Pair(a, b), Pair(c, d))’,‘Mulj(Pair(a, b), Pair(c, d))’] >>
 rw[ZR_refl] >> once_rw[ZR_sym_iff] >>
 rw[rep_asz_ZR] >>
 first_assum irule >>  rw[rep_asz_ZR])
(form_goal
“!a b c d. Mulz(asz(Pair(a,b)),asz(Pair(c,d))) = 
 asz(Mulj(Pair(a,b),Pair(c,d)))”));




val MULz_assoc = prove_store("ADDz_assoc",
e0
(rpt strip_tac >> 
 qsspecl_then [‘z1’] strip_assume_tac z_has_rep >>
 qsspecl_then [‘z2’] strip_assume_tac z_has_rep >>
 qsspecl_then [‘z3’] strip_assume_tac z_has_rep >>
 arw[] >> 
 rw[Mulz_eqn] >> rw[Mulj_property] >>
 rw[Mulz_eqn] >> rw[GSYM Mulj_property] >>
 assume_tac J1_v >> fs[ZR_samez])
(form_goal
 “!z1 z2 z3. Mulz(Mulz(z1,z2),z3) = Mulz(z1,Mulz(z2,z3))”));



val J1_vi = prove_store("J1_vi",
e0
(rw[ZR_def_alt] >> rpt strip_tac >>
 rw[Mulj_property] >> rw[Addj_property] >>
 rw[Pair_def'] >> rw[Mulj_property] >> rw[Pair_def'] >>
 rw[RIGHT_DISTR,LEFT_DISTR,GSYM Add_assoc] >> 
 qsspecl_then 
 [‘Mul(a, c)’,
  ‘Add(Mul(a, e),
                 Add(Mul(b, d),
                  Add(Mul(b, f),
                   Add(Mul(a, d), Add(Mul(b, c), Add(Mul(a, f), Mul(b, e)))))))’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsspecl_then 
 [‘Mul(a, e)’,
  ‘Add(Mul(b, d),
                 Add(Mul(b, f),
                  Add(Mul(a, d),
                   Add(Mul(b, c), Add(Mul(a, f), Add(Mul(b, e), Mul(a, c)))))))’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsspecl_then
 [‘Mul(b, d)’,
  ‘Add(Mul(b, f),
                 Add(Mul(a, d),
                  Add(Mul(b, c),
                   Add(Mul(a, f), Add(Mul(b, e), Add(Mul(a, c), Mul(a, e)))))))’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsspecl_then
 [‘Mul(b, f)’,
  ‘Add(Mul(a, d),
                 Add(Mul(b, c),
                  Add(Mul(a, f),
                   Add(Mul(b, e), Add(Mul(a, c), Add(Mul(a, e), Mul(b, d)))))))’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(b, c),
                 Add(Mul(a, f),
                  Add(Mul(b, e),
                   Add(Mul(a, c), Add(Mul(a, e), Add(Mul(b, d), Mul(b, f))))))) = 
 Add(Mul(a, f),
                 Add(Mul(b, c),
                  Add(Mul(b, e),
                   Add(Mul(a, c), Add(Mul(b, d), Add(Mul(a, e), Mul(b, f)))))))’ >-- (strip_tac >> arw[]) >>
 qsspecl_then
 [‘Mul(b, c)’,
 ‘Add(Mul(a, f),
                 Add(Mul(b, e),
                  Add(Mul(a, c), Add(Mul(a, e), Add(Mul(b, d), Mul(b, f))))))’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(b, e),
                 Add(Mul(a, c),
                  Add(Mul(a, e), Add(Mul(b, d), Add(Mul(b, f), Mul(b, c)))))) = Add(Mul(b, c),
                 Add(Mul(b, e),
                  Add(Mul(a, c), Add(Mul(b, d), Add(Mul(a, e), Mul(b, f))))))’ >-- (strip_tac >> arw[]) >>
 qsspecl_then 
 [‘Mul(b, c)’,
  ‘Add(Mul(b, e),
                 Add(Mul(a, c), Add(Mul(b, d), Add(Mul(a, e), Mul(b, f)))))’] assume_tac Add_sym' >> arw[GSYM Add_assoc] >>
 qsuff_tac
 ‘Add(Mul(a, e), Add(Mul(b, d), Add(Mul(b, f), Mul(b, c)))) = 
  Add(Mul(b, d), Add(Mul(a, e), Add(Mul(b, f), Mul(b, c))))’
 >-- (strip_tac >> arw[]) >>
 rw[Add_assoc] >>
 qsspecl_then
 [‘Mul(a, e)’,‘Mul(b, d)’] assume_tac Add_sym' >>
 arw[])
(form_goal
 “!a b c d e f.
Holds(ZR,Mulj(Pair(a, b), Addj(Pair(c, d), Pair(e, f))),
              Addj(Mulj(Pair(a, b), Pair(c, d)), Mulj(Pair(a, b), Pair(e, f))))”));



val J2_i' = prove_store("J2_i'",
e0
(rpt strip_tac >>
 qsspecl_then [‘ab’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘pq’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘cd’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘rs’] strip_assume_tac Pair_has_comp >>
 fs[] >> irule J2_i >> arw[])
(form_goal
 “!ab pq cd rs. Holds(ZR,ab,pq) & Holds(ZR,cd,rs) ==>
 Holds(ZR,Addj(ab,cd),Addj(pq,rs))”));

val J1_vi' = prove_store("J1_vi'",
e0
(rpt strip_tac >>
 qsspecl_then [‘ab’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘cd’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘ef’] strip_assume_tac Pair_has_comp >>
 fs[] >> rw[J1_vi])
(form_goal
 “!ab cd ef.
Holds(ZR,Mulj(ab, Addj(cd, ef)),
   Addj(Mulj(ab, cd), Mulj(ab, ef)))”));

val Mulz_eqn0 = prove_store("Mulz_eqn0",
e0
(rpt strip_tac >>
 assume_tac Mulz_eqn >>
 qsspecl_then [‘ab’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘cd’] strip_assume_tac Pair_has_comp >> 
 fs[])
(form_goal
 “!ab cd.Mulz(asz(ab),asz(cd)) = asz(Mulj(ab,cd))”));

val Z2_vi = prove_store("Z2_vi",
e0
(rpt strip_tac >> 
 assume_tac J1_vi' >> rw[Mulz_eqn0,Addz_eqn] >> 
 once_rw[GSYM ZR_samez] >>
 once_rw[ZR_cond] >>
 qexistsl_tac 
 [‘Mulj(Pair(a, b),
        Addj(Pair(c, d),Pair(e, f)))’,
  ‘Addj(Mulj(Pair(a, b), Pair(c, d)),
        Mulj(Pair(a, b), Pair(e, f)))’] >>
 rpt strip_tac (* 3 *)
 >-- (irule J2_iii' >> rw[ZR_refl] >> 
     irule J2_i' >> once_rw[ZR_sym_iff] >> 
     rw[rep_asz_ZR]) 
 >-- (irule J2_i' >> once_rw[ZR_sym_iff] >> rw[rep_asz_ZR]) >>
 arw[])
(form_goal
 “!a b c d e f. 
  Mulz(asz(Pair(a,b)),Addz(asz(Pair(c,d)),asz(Pair(e,f)))) = 
  Addz(Mulz(asz(Pair(a,b)),asz(Pair(c,d))),
       Mulz(asz(Pair(a,b)),asz(Pair(e,f))))”));



val J1_vii = prove_store("J1_vii",
e0
(rw[ZR_def_alt] >> rpt strip_tac >>
 rw[GSYM oj_def,Mulj_property] >> rw[Pair_def'] >>
 rw[Mul_clauses,Add_O,Add_O2] >>
 qsspecl_then [‘a’,‘b’] accept_tac Add_sym')
(form_goal
 “!a b.Holds(ZR,Mulj(Pair(a, b),1j),Pair(a,b))”));


val Z2_vii = prove_store("Z2_vii",
e0
(rpt strip_tac >> rw[Mulz_eqn0] >>
 rw[GSYM ZR_samez] >> rw[J1_vii])
(form_goal “!a b. Mulz(asz(Pair(a,b)),asz(1j)) = asz(Pair(a,b))”));


val J1_viii = prove_store("J1_vii",
e0
(rw[ZR_def_alt] >> rpt strip_tac >>
 rw[Mulj_property] >> rw[Pair_def'] >>
 qsspecl_then [‘a’,‘c’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘b’,‘d’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘a’,‘d’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘b’,‘c’] assume_tac Mul_sym >> arw[] >>
 qsspecl_then [‘Add(Mul(c, a), Mul(d, b))’,‘Add(Mul(d, a), Mul(c, b))’]
 assume_tac  Add_sym >> arw[] >>
 qsspecl_then [‘Mul(d,a)’,‘Mul(c,b)’] assume_tac Add_sym' >>
 arw[])
(form_goal
 “!a b c d.Holds(ZR,Mulj(Pair(a, b),Pair(c,d)),Mulj(Pair(c,d),Pair(a,b)))”));


val J1_xi = prove_store("J1_xi",
e0
(rw[lej_property,GSYM zj_def,Add_O2] >> rpt strip_tac >>
 rw[Mulj_property,lej_property] >> 
 rw[Add_assoc] >> once_rw[Add_sym] >>
 rw[GSYM Add_assoc] >> rw[GSYM RIGHT_DISTR] >>
 rw[Add_assoc] >> rw[GSYM RIGHT_DISTR] >> 
 drule Le_MONO_Mul' >>
 first_x_assum (qsspecl_then [‘Sub(Add(b,c),Add(a,d))’] assume_tac) >>
 fs[LEFT_SUB_DISTR] >>
 qby_tac
 ‘Le(Mul(f, Add(a, d)),Mul(f, Add(b, c)))’
 >-- (once_rw[Mul_sym] >> irule Le_MONO_Mul' >> arw[]) >>
 drule SUB_ADD >> 
 qsspecl_then [‘Sub(Mul(f, Add(b, c)), Mul(f, Add(a, d)))’,
               ‘Sub(Mul(e, Add(b, c)), Mul(e, Add(a, d)))’,
               ‘Mul(f, Add(a, d))’] 
 drule $ iffRL LESS_EQ_MONO_ADD_EQ >> rfs[] >>
 pop_assum mp_tac >> once_rw[Add_sym] >> strip_tac >>
 qsspecl_then 
 [‘Mul(f, Add(c, b))’,
  ‘Add(Mul(f, Add(a, d)),
               Sub(Mul(e, Add(b, c)), Mul(e, Add(a, d))))’,
  ‘Mul(e,Add(a,d))’] drule $ iffRL LESS_EQ_MONO_ADD_EQ >>
 fs[GSYM Add_assoc] >> 
 rev_drule Le_MONO_Mul' >>
 first_x_assum $ qspecl_then [‘e’] assume_tac >>
 pop_assum mp_tac >> once_rw[Mul_sym] >> strip_tac >>
 drule SUB_ADD >> fs[] >> once_rw[Add_sym] >> 
 qpick_x_assum
 ‘Le(Add(Mul(f, Add(c, b)), Mul(e, Add(a, d))),
              Add(Mul(f, Add(a, d)), Mul(e, Add(b, c))))’
 mp_tac >> pop_assum_list (map_every (K all_tac)) >>
 strip_tac >>
 qsspecl_then [‘b’,‘c’] assume_tac Add_sym' >> arw[] >>
 qsspecl_then [‘d’,‘a’] assume_tac Add_sym' >> arw[] >>
 fs[] >> 
 qsspecl_then [‘Mul(e, Add(a, d))’,‘Mul(f, Add(c, b))’]
 assume_tac Add_sym' >> fs[])
(form_goal “!a b c d e f. 
Holds(lej,Pair(a,b),Pair(c,d)) & 
Holds(lej,0j,Pair(e,f))  ==> 
 Holds(lej,Mulj(Pair(a,b),Pair(e,f)),Mulj(Pair(c,d),Pair(e,f))) ”));



val Z2_xi = prove_store("Z2_xi",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>  
 strip_tac >> strip_tac >>
 rw[Lez_def] >> rw[LEz_def] >>
 rpt strip_tac >>
 qby_tac ‘Holds(lej,Pair(a,b),Pair(c,d))’
 >-- (irule $ iffLR J2_iv' >>
      qexistsl_tac [‘rep(asz(Pair(a, b)))’,‘rep(asz(Pair(c, d)))’] >>
     arw[] >> once_rw[ZR_sym_iff] >> rw[rep_asz_ZR]) >>
 qby_tac ‘Holds(lej,0j,Pair(e,f))’
 >-- (fs[GSYM zj_def] >> irule $ iffLR J2_iv' >>
        qexistsl_tac [‘rep(asz(Pair(O, O)))’,‘rep(asz(Pair(e, f)))’] >>
        arw[] >> once_rw[ZR_sym_iff] >> rw[rep_asz_ZR] ) >>
irule $ iffLR J2_iv' >> 
 qexistsl_tac [‘Mulj(Pair(a,b),Pair(e,f))’,‘Mulj(Pair(c,d),Pair(e,f))’] >> 
 strip_tac (* 2 *)
 >-- (irule J1_xi >> arw[]) >> strip_tac (* 2 *)
 >> (rw[Mulz_eqn] >> rw[rep_asz_ZR]) 
)
(form_goal
 “!a b c d e f.
  Lez(asz(Pair(a,b)),asz(Pair(c,d))) & Lez(asz(0j),asz(Pair(e,f))) ==>
  Lez(Mulz(asz(Pair(a,b)),asz(Pair(e,f))),Mulz(asz(Pair(c,d)),asz(Pair(e,f))))”));
