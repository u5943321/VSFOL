
val ZR_ER = prove_store("ZR_ER",
e0
(rw[ER_def,ZR_Refl,ZR_Sym,ZR_Trans])
(form_goal “ER(ZR)”));


val Zrep0_def = Thm_2_4 |> qspecl [‘Pow(N * N)’] 
        |> fVar_sInst_th
           “P(a:mem(Pow(N * N)))”
           “?ab:mem(N * N). a = rsi(ZR,ab)”
        |> ex2fsym0 "Z" []
        |> ex2fsym0 "Zrep0" [];


val Zrep_def = rel2fun |> qspecl [‘Z’,‘Pow(N * N)’,‘Zrep0’]
                       |> C mp 
                       (Zrep0_def |> conjE1 |> rewr_rule[Inj_def] |> conjE1) |> uex_expand
                |> ex2fsym0 "Zrep" []

val dflip_tac = 
fconv_tac 
 (basic_once_fconv no_conv (rewr_fconv (eq_sym "mem")))


val ZR_Zrep_11 = prove_store("ZR_Zrep_11",
e0
(strip_tac >> uex_tac >>
strip_assume_tac Zrep_def >> 
dflip_tac >>  arw[] >>
strip_assume_tac Zrep0_def >>
first_x_assum (qspecl_then [‘rsi(ZR,x)’] assume_tac) >>
qby_tac ‘?ab. rsi(ZR,x) = rsi(ZR,ab)’
>-- (qexists_tac ‘x’ >> rw[]) >>
fs[] >>
qexists_tac ‘b’ >> 
(*use injective*)
fs[Inj_def] >>
drule Holds_Eval >> arw[] >>
rpt strip_tac >> first_x_assum irule >>
drule Eval_def >> fs[])
(form_goal “!x.?!y. rsi(ZR,x) = App(Zrep,y)”));

val Zabs0_def = 
P2fun' |> qspecl [‘N * N’,‘Z’]
       |> fVar_sInst_th “P(x:mem(N * N),y:mem(Z))”
       “rsi(ZR,x) = App(Zrep,y)”
       |> C mp ZR_Zrep_11
       |> ex2fsym0 "Zabs0" []


(*
rastt "Zabs0";sort_of it;

rastt "rsi(ZR,ab)";sort_of it
                           “ App(Zabs,s) = App(Zabs0,ab)”
val _ = new_fun "Zabs"

*)


val Zabs_ex = prove_store("Zabs_ex",
e0
(cheat)
(form_goal
 “?Zab:Pow(N * N) -> Z.
 (!s:mem(Pow(N * N)) ab. 
   s = rsi(ZR,ab) ==> App(Zab,s) = App(Zabs0,ab)) & 
 (!s. (!ab. ~(s = rsi(ZR,ab)) ==> App(Zab,s) = App(Zabs0,Pair(O,O))))”));

val Zabs_def = Zabs_ex |> ex2fsym0 "Zabs" []


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

(*
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
 “!A a:mem(Pow(A)). contents(Sing(a)) = a”));
*)


val contZ_ex = prove_store("contZ_ex",
e0
cheat
(form_goal
 “?s0. s0 = App(contents0(App(Zabs0,Pair(O,O))),s)”));

val contZ_def = contZ_ex |> ex2fsym0 "contZ" ["s"]
                               |> gen_all

val contZ_Sing = prove_store("contZ_Sing",
e0
(cheat)
(form_goal
 “!z:mem(Z). contZ(Sing(z)) = z”));


val neg0_ex = prove_store("neg0_ex",
e0
(cheat)
(form_goal “?negNN: N * N -> N * N.
            !ab.App(negNN,ab) = Pair(Snd(ab),Fst(ab))”));

val neg0_def = neg0_ex |> ex2fsym0 "neg0" []


val add0_ex = prove_store("add0_ex",
e0
(cheat)
(form_goal “?addNN: (N * N) * N * N -> N * N.
            !x y u v.App(addNN,Pair(Pair(x,y),Pair(u,v))) = Pair(Add(x,u),Add(y,v))”));

val add0_def = add0_ex |> ex2fsym0 "add0" []




(*
val negZ_ex = prove_store("negZ_ex",
e0
(cheat)
(form_goal “?nz.!z. App(nz,z) = 
  App(Zabs,
     contents(IMAGE(o1(Rsi(ZR),neg0),
              App(Zrep,z))))”));



val negZ_def = negZ_ex |> ex2fsym0 "negZ" []
*)



val negZ_ex = prove_store("negZ_ex",
e0
(cheat)
(form_goal “?nz.!z. App(nz,z) =
     contZ(IMAGE(o1(Zabs,o1(Rsi(ZR),neg0)),
              App(Zrep,z)))”));

val negZ_def = negZ_ex |> ex2fsym0 "negZ" []


val addZ_ex = prove_store("addZ_ex",
e0
(cheat)
(form_goal “?az:Z * Z -> Z.!z1 z2. App(az,Pair(z1,z2)) =
     contZ(IMAGE(o1(Zabs,o1(Rsi(ZR),add0)),
                 spair(App(Zrep,z1),App(Zrep,z2))))”));

val addZ_def = addZ_ex |> ex2fsym0 "addZ" []


(*
"-z ≡ contents
( 􏰀 (x,y) ∈Rep Integ z. { Abs Integ(intrel‘‘{(y,x)}) })"
*)

(*
lemma minus:
"- Abs Integ(intrel‘‘{(x,y)}) = Abs Integ(intrel ‘‘ {(y,x)})"
*)

val minus = prove_store("minus",
e0
(rw[negZ_def] >>
 rpt strip_tac >>
 qby_tac
 ‘respects(o1(Zabs, o1(Rsi(ZR), neg0)),ZR)’
 >-- cheat >>
 assume_tac ZR_ER >> drule UN_equiv_class >>
 first_x_assum drule >> 
 qsuff_tac
 ‘contents(IMAGE(o1(Rsi(ZR), neg0),
                  App(Zrep, App(Zabs, rsi(ZR, Pair(x, y)))))) 
  = rsi(ZR, Pair(y, x))’
 >-- (strip_tac >> arw[]) >>
 qsuff_tac ‘App(Zrep, App(Zabs, rsi(ZR, Pair(x, y)))) = 
 rsi(ZR, Pair(x, y))’
 >-- (strip_tac >> arw[] >> rw[contents_Sing] >>
     rw[GSYM o_App,neg0_def,Pair_def',rsi_def]) >>
 qby_tac ‘?z.rsi(ZR, Pair(x, y)) = App(Zrep,z)’ 
 >-- cheat >>
 pop_assum strip_assume_tac >> arw[] >>
 rw[]
 )
(form_goal
 “!x y. App(negZ,App(Zabs,rsi(ZR,Pair(x,y)))) = 
        App(Zabs,rsi(ZR,Pair(y,x)))”));



val negZ'_ex = prove_store("negZ'_ex",
e0
(cheat)
(form_goal “?nz.!z. App(nz,z) =
    App(Zabs,contents(IMAGE(o1(Rsi(ZR),neg0),
                            App(Zrep,z))))”));

val negZ'_def = negZ'_ex |> ex2fsym0 "negZ'" []



Zrep o Zabs o ZR  = I

val minus = prove_store("minus",
e0
(rw[negZ'_def] >>
 rpt strip_tac >>
 qby_tac
 ‘App(Zrep, App(Zabs, rsi(ZR, Pair(x, y)))) = 
  rsi(ZR, Pair(x, y))’
 >-- cheat >> arw[] >>
 qby_tac
 ‘respects(o1(Rsi(ZR), neg0),ZR)’
 >-- cheat >>
 assume_tac ZR_ER >> drule UN_equiv_class >>
 first_x_assum drule >> 
 arw[contents_Sing] >>
 rw[GSYM o_App,neg0_def,Pair_def',rsi_def]
 qsuff_tac
 ‘contents(IMAGE(o1(Rsi(ZR), neg0),
                  App(Zrep, App(Zabs, rsi(ZR, Pair(x, y)))))) 
  = rsi(ZR, Pair(y, x))’
 >-- (strip_tac >> arw[]) >>
 qsuff_tac ‘App(Zrep, App(Zabs, rsi(ZR, Pair(x, y)))) = 
 rsi(ZR, Pair(x, y))’
 >-- (strip_tac >> arw[] >> rw[contents_Sing] >>
     rw[GSYM o_App,neg0_def,Pair_def',rsi_def]) >>
 qby_tac ‘?z.rsi(ZR, Pair(x, y)) = App(Zrep,z)’ 
 >-- cheat >>
 pop_assum strip_assume_tac >> arw[] >>
 rw[]
 )
(form_goal
 “!x y. App(negZ',App(Zabs,rsi(ZR,Pair(x,y)))) = 
        App(Zabs,rsi(ZR,Pair(y,x)))”));


lemma add:
"Abs Integ (intrel‘‘{(x,y)}) + Abs Integ (intrel‘‘{(u,v)}) =
Abs Integ (intrel‘‘{(x+u, y+v)})" proof -
have "(λz w. (λ(x,y). (λ(u,v).
{Abs Integ (intrel ‘‘ {(x+u, y+v)})}) w) z)
respects2 intrel"
by (simp add: congruent2 def)
thus ?thesis
by (simp add: add int def UN UN split split eq
UN equiv class2 [OF equiv intrel])
qed

(*simp lemma for this:

 App(o1(Zabs, o1(Rsi(ZR), add0)), Pair(Pair(x, y), Pair(u, v))) =
               App(Zabs, rsi(ZR, Pair(Add(x, u), Add(y, v))))

*)
val add = 
rw[addZ_def] >>
qby_tac ‘App(Zrep, App(Zabs, rsi(ZR, Pair(x, y)))) = 
        rsi(ZR, Pair(x, y)) & 
        App(Zrep, App(Zabs, rsi(ZR, Pair(u, v)))) = 
        rsi(ZR, Pair(u, v))’
>-- cheat >>
arw[] >>
assume_tac UN_equiv_class2 >>
assume_tac ZR_ER >> first_x_assum drule >>
pop_assum (qsspecl_then [‘o1(Zabs, o1(Rsi(ZR), add0))’] 
 assume_tac) >>
qby_tac ‘respects2(o1(Zabs, o1(Rsi(ZR), add0)), ZR)’
>-- cheat >>
first_x_assum drule >> arw[] >>
rw[contZ_Sing]



UN_equiv_class2
“App(addZ,
     Pair(App(Zabs,rsi(ZR,Pair(x,y))),
          App(Zabs,rsi(ZR,Pair(u,v))))) = 
 App(Zabs,rsi(ZR,Pair(Add(x,u),Add(y,v))))”

(*
"-z ≡ contents
( 􏰀 (x,y) ∈Rep Integ z. { Abs Integ(intrel‘‘{(y,x)}) })"
*)

(*
lemma minus:
"- Abs Integ(intrel‘‘{(x,y)}) = Abs Integ(intrel ‘‘ {(y,x)})"
*)


(*
lemma minus:
"- Abs Integ(intrel‘‘{(x,y)}) = Abs Integ(intrel ‘‘ {(y,x)})"
proof -
have "(λ(x,y). {Abs Integ (intrel‘‘{(y,x)})}) respects intrel"
by (simp add: congruent def) thus ?thesis
by (simp add: minus int def UN equiv class [OF equiv intrel]) qed

*)

val minus = prove_store("minus",
e0
(rw[negZ_def] >>
 rpt strip_tac >>
 qby_tac
 ‘respects(o1(Zabs, o1(Rsi(ZR), neg0)),ZR)’
 >-- cheat >>
 assume_tac ZR_ER >> drule UN_equiv_class >>
 first_x_assum drule >> 

 qby_tac
 ‘respects(o1(Sg(Z),o1(Zabs, o1(Rsi(ZR), neg0))),ZR)’
 >-- cheat >>
 assume_tac ZR_ER >> drule UN_equiv_class >>
 first_x_assum drule >> 
 

 qsuff_tac
 ‘contents(IMAGE(o1(Rsi(ZR), neg0),
                  App(Zrep, App(Zabs, rsi(ZR, Pair(x, y)))))) 
  = rsi(ZR, Pair(y, x))’
 >-- (strip_tac >> arw[]) >>
 qsuff_tac ‘App(Zrep, App(Zabs, rsi(ZR, Pair(x, y)))) = 
 rsi(ZR, Pair(x, y))’
 >-- (strip_tac >> arw[] >> rw[contents_Sing] >>
     rw[GSYM o_App,neg0_def,Pair_def',rsi_def]) >>
 qby_tac ‘?z.rsi(ZR, Pair(x, y)) = App(Zrep,z)’ 
 >-- cheat >>
 pop_assum strip_assume_tac >> arw[] >>
 rw[]
 )
(form_goal
 “!x y. App(negZ,App(Zabs,rsi(ZR,Pair(x,y)))) = 
        App(Zabs,rsi(ZR,Pair(y,x)))”));



val zminus_zminus = prove_store("zminus_zminus",
e0
(strip_tac >> qby_tac ‘?a b. z = App(Zabs,rsi(ZR,Pair(a,b)))’
(*tactic to automate this cases on*)
>-- cheat >>
pop_assum strip_assume_tac >>
arw[] >> rw[minus])
(form_goal “!z.App(negZ,App(negZ,z)) = z”));



val ZR_QUOTIENT = prove_store("ZR_QUOTIENT",
e0
(rw[QUOTIENT_def] >> rpt strip_tac >>
 assume_tac Zrep_def >>
 first_x_assum (qspecl_then [‘q’] assume_tac) )
(form_goal
 “QUOTIENT(ZR,Zabs,Zrep)”));


