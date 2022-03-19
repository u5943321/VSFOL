


val eqc_ex = prove_store("eqc_ex",
e0
(rpt strip_tac >>
 strip_assume_tac 
 (IN_def_P |> qspecl [‘N * N’]
         |> fVar_sInst_th “P(a:mem(N * N))”
            “Holds(ZR,ab,a)”))
(form_goal “!ab:mem(N * N). ?!cl:mem(Pow(N * N)). 
 !cd. IN(cd,cl) <=> Holds(ZR,ab,cd)”));

val cof_def = P2fun' |> qspecl [‘N * N’,‘Pow(N * N)’]
                    |> fVar_sInst_th 
                    “P(x:mem(N * N),y:mem(Pow(N * N)))”
                    “!cd. IN(cd,y) <=> Holds(ZR,x,cd)”
                    |> C mp eqc_ex
                    |> ex2fsym0 "cof" []



local
val lemma =
fVar_Inst [("P",([("sss",mem_sort $ Pow $ Pow (mk_set "A")),
                  ("ss",mem_sort $ Pow (mk_set "A"))],
“!a:mem(A).IN(a,ss) <=> ?ss0. IN(ss0,sss) & IN(a,ss0)”))] 
(AX1|> qspecl [‘Pow(Pow(A))’,‘Pow(A)’])
|> uex_expand
val lemma' = 
fVar_Inst [("P",([("a",mem_sort (mk_set "A"))],
“?ss0. IN(ss0,sss) & IN(a:mem(A),ss0)”))] 
(IN_def_P_expand|> qspecl [‘A’]) |> GSYM
in
val BIGUNION_ex = prove_store("BIGUNION_ex",
e0
(strip_tac >> 
 x_choosel_then ["BU"] strip_assume_tac lemma >>
 qexists_tac ‘BU’ >> 
 qsuff_tac ‘isFun(BU)’ >--
 (strip_tac >> arw[] >> rpt strip_tac >>
 first_x_assum $ irule o iffLR >>
 drule Holds_Eval >> arw[]) >>
 rw[Fun_expand] >> 
 qby_tac ‘!sss. ?ss. Holds(BU,sss,ss)’ >--
 (strip_tac >> once_arw[] >> 
  x_choose_then "ss" strip_assume_tac lemma' >>
  qexists_tac ‘ss’ >> once_arw[] >> rw[]) >>
 strip_tac >-- arw[] >>
 rpt strip_tac >> irule IN_EXT >> 
 rfs[])
(form_goal
 “!A. ?BU:Pow(Pow(A)) ~> Pow(A). 
  isFun(BU) & 
  !sss:mem(Pow(Pow(A))) a:mem(A). IN(a,Eval(BU,sss)) <=>
  ?ss.IN(ss,sss) & IN(a,ss)”));
end

 
val BU_def = BIGUNION_ex |> spec_all |> ex2fsym0 "BU" ["A"]
                         |> gen_all
                         |> store_as "BU_def";

val BU_isFun = BU_def |> spec_all |> conjE1 |> gen_all 
                      |> store_as "BU_isFun";


val BU_property = BU_def |> spec_all |> conjE2 |> gen_all 
                         |> store_as "BU_property";



val BIGUNION_ex = prove_store("BIGUNION_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(BU(A),sss)’ >> rw[])
(form_goal
 “!A sss:mem(Pow(Pow(A))). ?isss.Eval(BU(A),sss) = isss”))


val BIGUNION_def = BIGUNION_ex |> spec_all |> ex2fsym0 "BIGUNION" ["sss"]
                               |> store_as "BIGUNION_def";

val IN_BIGUNION = BU_def |> rewr_rule[BIGUNION_def] |> spec_all |> conjE2 |> gen_all
                         |> store_as "IN_BIGUNION";



val IMAGE_ex = prove_store("IMAGE_ex",
e0
cheat
(form_goal “!A B f: A -> B s0:mem(Pow(A)). ?im:mem(Pow(B)). 
  (!b. IN(b,im) <=> ?a. IN(a,s0) & b = App(f,a))”));

val IMAGE_def = IMAGE_ex |> spec_all |> ex2fsym0 "IMAGE" ["f","s0"]
                   |> gen_all

val Whole_ex =  prove_store("Whole_ex",
e0
(cheat)
(form_goal “!A. ?s:mem(Pow(A)). (!a:mem(A). IN(a,s))”));

val Whole_def = Whole_ex |> spec_all |> ex2fsym0 "Whole" ["A"] |> gen_all 

val IM_ex = prove_store("IM_ex",
e0
(cheat)
(form_goal
 “!A B f:A->B. ?im. im = IMAGE(f,Whole(A))”));

val IM_def = IM_ex |> spec_all |> ex2fsym0 "IM" ["f"]
                   |> gen_all

val lp_lemma = prove_store("lp_lemma",
e0
(cheat)
(form_goal
 “!A B f:A->Pow(B) a:mem(A) c. (!y:mem(A). App(f,y) = c) ==> BIGUNION(IM(f)) = c”));

val R''_ex = prove_store("R''_ex",
e0
(cheat)
(form_goal “!A B R:A~>B s0:mem(Pow(A)). ?s1:mem(Pow(B)).
 (!b. IN(b,s1) <=> ?a. IN(a,s0) & Holds(R,a,b))”));

val R''_def = R''_ex |> spec_all |> ex2fsym0 "R''" ["R","s0"]
                     |> gen_all

val Sing_ex = prove_store("Sing_ex",
e0
(cheat)
(form_goal “!A a:mem(A). ?sa:mem(Pow(A)).
 !a1. IN(a1,sa) <=> a1 = a”));

val Sing_def = Sing_ex |> spec_all |> ex2fsym0 "Sing" ["a"]
                       |> gen_all

 
val UN_equiv_class = prove_store("UN_equiv_class",
e0
(cheat)
(form_goal
 “!A  r:A~>A B f:A ->Pow(B) .ER(r) & respect(f,r) ==> 
 !a:mem(A). BIGUNION(IMAGE(f,R''(r,Sing(a)))) = App(f,a) ”));


(*curry apply first argument*)

val CA1_ex = prove_store("CA1_ex",
e0
(cheat)
(form_goal
 “!A B C f:A * B ->C a:mem(A). ?f1:B->C.
  (!b. App(f1,b) = App(f,Pair(a,b))) ”));

val CA1_def = CA1_ex |> spec_all |> ex2fsym0 "CA1" ["f","a"]
                     |> qgenl [‘f’,‘a’]
                     |> gen_all
                     |> store_as "CA1_def";

(*
“BIGUNION(
 IMAGE (\x1.BIGUNION(IMAGE(\x2.f x1 x2, R''(r,a2)))), 
 R''(r,a1))”

*)

val IMAGE2_ex = prove_store("IMAGE2_ex",
e0
cheat
(form_goal “!A B C f:A * B ->C s1:mem(Pow(A)) s2:mem(Pow(B)).
 ?s3:mem(Pow(C)). (!c.IN(c,s3) <=> ?a b. IN(a,s1) & IN(b,s2) & c = App(f,Pair(a,b)))”));

val IMAGE2_def = IMAGE2_ex |> spec_all |> ex2fsym0 "IMAGE2" ["f","s1","s2"] |> gen_all



val QUOTIENT_def = 
store_ax("QUOTIENT_def",
“!A R:A~>A Q abs:A->Q rep:Q->Pow(A).
 QUOTIENT(R:A ~> A,abs:A ->Q ,rep) <=> 
 (!q:mem(Q) a. IN(a,App(rep,q)) <=>  App(abs,a) = q) &
 (!q:mem(Q) a1 a2. IN(a1,App(rep,q)) & IN(a2,App(rep,q)) ==>
   Holds(R,a1,a2) ) &
 (!r:mem(A) s.Holds(R,r,s) <=> 
  Holds(R,r,r) & Holds(R,s,s) & (App(abs,r) = App(abs,s)))”);

val respects_def = store_ax("respects_def",
“!A B f:A->B r:A~>A. respects(f,r) <=> 
 (!y z.Holds(r,y,z) ==> App(f,y) = App(f,z))”);


val congruent2_def = store_ax("congruent2_def",
“!A r1:A~>A B r2:B~>B C f:A * B -> C.
 congruent2(r1,r2,f) <=> 
 !x y. Holds(r1,x,y) ==> !u v.Holds(r2,u,v) ==>
 App(f,Pair(x,u)) = App(f,Pair(y,v))”);


val respects2_def = store_ax("respects2_def",
“!A B f:A->B r:A~>A. respects2(f,r) <=> 
 congruent2(r,r,f)”);


lemma UN equiv class:
"[equiv A r; f respects r; a ∈ A]
  =⇒ ( 􏰀 x ∈ r ‘ ‘ { a } . f x ) = f a "



val isSing_def = define_pred
“!A s:mem(Pow(A)). isSing(s) <=> ?a. s = Sing(a)”

val Arb_ex = prove_store("Arb_def",
e0
()
(form_goal
 “!A. (?a:mem(A)) ==> ?a.mem(A)”));

val contents0_ex = prove_store("contents0_ex",
e0
cheat
(form_goal
 “!A a0:mem(A).  ?ct:Pow(A) -> A.
  (!s:mem(Pow(A)). (!a:mem(A). s = Sing(a) ==> App(ct,s) = a) & (~isSing(s) ==> App(ct,s) = a0))”));

val contents0_def = contents0_ex |> spec_all 
                                 |> ex2fsym0 "contents0"
                                 ["a0"]
                                 |> gen_all


val contents_ex = prove_store("contents_ex",
e0
cheat
(form_goal
 “!A s:mem(Pow(Pow(A))). ?s0. s0 = App(contents0(Empty(A)),s)”));

val contents_def = contents_ex |> spec_all 
                               |> ex2fsym0 "contents" ["s"]
                               |> gen_all


val contents_Sing = prove_store("contents_Sing",
e0
(cheat)
(form_goal
 “!A s:mem(Pow(A)).contents(Sing(s)) = s”));


(*
fun cases_on_with tm th : tactic =
    fn (ct,asl,w) => 
  
cannot have the rule as LP paper, since we cannot prove things about fvar unless it is a ptaut.

*)

val r''_ex = prove_store("r''_ex",
e0
()
(form_goal “!A B r: A~> B. ?r'':Pow(A) -> Pow(B). 
 !s b. IN(b,App(r'',s)) <=> ?a. IN(a,s) & Holds)”));

R'' :((A*B) * Pow(A))

(*a function turns r'' into a *)

“-z = contents(BIGUNION(IMAGE(Abs_Integ @ r''(intrel) @ (\(x,y) => (y,x)) ,z)))”

val UN_equiv_class' = 




ToIm(f:A * B-> C, b:mem(B)): f

“BIGUNION(
 IMAGE
 (\x1.BIGUNION(IMAGE(CA1(f,x1), R''(r,a2)))), 
  R''(r,a1))”

“!A B C f:A* B ->C s0:Pow(A). ?!f1s:mem(Pow(Exp(B,C))).
 !f1:B->C. IN(Tpm(f))”

val UN_equiv_class2 = prove_store("UN_equiv_class2",
e0
(cheat)
(form_goal
 “!A r1:A~>A. ER(r1) ==> !r2:A~>A. ER(r2) ==> 
  !B f:A * A ->Pow(B). congruent2(r1,r2,f) ==> 
 !a1:mem(A) a2.
  BIGUNION(IMAGE(f,R''(r,Sing(a)))) = App(f,Pair(a1,a2)) ”));

“BIGUNION(IMAGE(CA1(f:A * A -> Pow(B),a1),R''(r:A ~> A,Sing(a2)))) = b”




(*------------experiment-------------*)


val ZR_ER = prove_store("ZR_ER",
e0
(rw[ER_def,ZR_Refl,ZR_Sym,ZR_Trans])
(form_goal “ER(ZR)”));


val eqc_ex = prove_store("eqc_ex",
e0
(rpt strip_tac >>
 strip_assume_tac 
 (IN_def_P |> qspecl [‘N * N’]
         |> fVar_sInst_th “P(a:mem(N * N))”
            “Holds(ZR,ab,a)”))
(form_goal “!ab:mem(N * N). ?!cl:mem(Pow(N * N)). 
 !cd. IN(cd,cl) <=> Holds(ZR,ab,cd)”));

val cof_def = P2fun' |> qspecl [‘N * N’,‘Pow(N * N)’]
                    |> fVar_sInst_th 
                    “P(x:mem(N * N),y:mem(Pow(N * N)))”
                    “!cd. IN(cd,y) <=> Holds(ZR,x,cd)”
                    |> C mp eqc_ex
                    |> ex2fsym0 "cof" []



val QUOTIENT_def = store_ax("QUOTIENT_def",
“!A R:A~>A Q abs:A->Q rep:Q->Pow(A).
 QUOTIENT(R:A ~> A,abs:A ->Q ,rep) <=> 
 (!q:mem(Q) a. IN(a,App(rep,q)) <=>  App(abs,a) = q) &
 (!r:mem(A) s.Holds(R,r,s) <=> 
  Holds(R,r,r) & Holds(R,s,s) & (App(abs,r) = App(abs,s)))”);


val Zrep0_def = Thm_2_4 |> qspecl [‘Pow(N * N)’] 
        |> fVar_sInst_th
           “P(a:mem(Pow(N * N)))”
           “?ab:mem(N * N). a = App(cof,ab)”
        |> ex2fsym0 "Z" []
        |> ex2fsym0 "Zrep0" [];

val Zrep_def = rel2fun |> qspecl [‘Z’,‘Pow(N * N)’,‘Zrep0’]
                       |> C mp 
                       (Zrep0_def |> conjE1 |> rewr_rule[Inj_def] |> conjE1) |> uex_expand
                |> ex2fsym0 "Zrep" []


(*rep is always an inj?*)

val flip_tac = 
fconv_tac (rewr_fconv (eq_sym "mem"));


val dflip_tac = 
fconv_tac 
 (basic_once_fconv no_conv (rewr_fconv (eq_sym "mem")))

val cof_Zrep_11 = prove_store("cof_Zrep_11",
e0
(strip_tac >> uex_tac >>
strip_assume_tac Zrep_def >> 
dflip_tac >>  arw[] >>
strip_assume_tac Zrep0_def >>
first_x_assum (qspecl_then [‘App(cof,x)’] assume_tac) >>
qby_tac ‘?ab. App(cof,x) = App(cof,ab)’
>-- (qexists_tac ‘x’ >> rw[]) >>
fs[] >>
qexists_tac ‘b’ >> 
(*use injective*)
fs[Inj_def] >>
drule Holds_Eval >> arw[] >>
rpt strip_tac >> first_x_assum irule >>
drule Eval_def >> fs[])
(form_goal “!x.?!y. App(cof,x) = App(Zrep,y)”));

val Zabs_def = 
P2fun' |> qspecl [‘N * N’,‘Z’]
       |> fVar_sInst_th “P(x:mem(N * N),y:mem(Z))”
       “App(cof,x) = App(Zrep,y)”
       |> C mp cof_Zrep_11
       |> ex2fsym0 "Zabs" []



local
val l = fVar_Inst 
[("P",([("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
 “App(f:A->B,a) = b”))] 
(AX1 |> qspecl [‘A’, ‘B’] |> uex_expand)
in
val asR_ex = prove_store("asR_ex",
e0
(rpt strip_tac >> strip_assume_tac l >>
 qexists_tac ‘R’ >> arw[])
(form_goal
 “!A B f:A->B.?R.!a b. Holds(R,a,b) <=> App(f,a) = b”));
end


val asR_def = asR_ex |> spec_all |> ex2fsym0 "asR" ["f"]
                     |> gen_all

val asR_Fun = prove_store("asR_Fun",
e0
(rpt strip_tac >> rw[Fun_expand] >>
 rw[asR_def] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘App(f,a)’ >> rw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B. isFun(asR(f))”));



val o1_ex = prove_store("o1_ex",
e0
(cheat)
(form_goal
 “!A B phi:A->B C psi:B->C. ?f:A->C. 
 !a c. App(f,a) = c <=> Holds(asR(psi) o asR(phi),a,c)”));

val o1_def = o1_ex |> spec_all |> ex2fsym0 "o1" ["psi","phi"]
                   |> gen_all

val o_App = prove_store("o_App",
e0
(rpt strip_tac >> flip_tac >> rw[o1_def] >>
 rw[GSYM o_def] >>
 qexists_tac ‘App(f,a)’ >> rw[asR_def])
(form_goal
 “!A B f:A1->B C g:B->C a. App(g,(App(f,a))) = App(o1(g,f),a)”));


val UN_equiv_class = prove_store("UN_equiv_class",
e0
(cheat)
(form_goal
 “!A r:A~>A. ER(r) ==> !B f:A->B. respects(f,r) ==>
  !a.IMAGE(f,R''(r,Sing(a))) = Sing(App(f,a))”));


val UN_equiv_class2 = prove_store("UN_equiv_class2",
e0
(cheat)
(form_goal
 “!A r:A~>A. ER(r) ==> !B f:A * A ->B. respects2(f,r) ==>
  !a b.IMAGE(f,sPair(R''(r,Sing(a)),R''(r,Sing(b)))) = Sing(App(f,a))”));





“IMAGE(f:A->B,R''(R:A~>A,a:mem(A)))  = b”

val ZR_QUOTIENT = prove_store("ZR_QUOTIENT",
e0
(rw[QUOTIENT_def] >> rpt strip_tac >>
 Zabs_def)
(form_goal
 “QUOTIENT(ZR,Zabs,Zrep)”));




 “QUOTIENT(ZR,a,Zrep)”
rastt "o1(cof,Zrep)"

 cof: N * N -> Pow(N * N) ---> Z
?

 Zrep: Z -> Pow(N * N)

val neg_ex = prove_store("neg_ex",
e0
()
(form_goal
 “!z:Z .?nz. ”));



