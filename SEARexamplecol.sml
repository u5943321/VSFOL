(*naive application of collection, give the existence of a set which is larger then any power set.*)



val isset_def = 
qdefine_psym("isset",[‘i:A->B’,‘bs:mem(Pow(B))’])
‘Inj(i) & IMAGE(i,Whole(A)) = bs’


val AX5 = store_ax("AX5",
“!A.?B p:B->A Y M:B~>Y.  
 (!S i:S->Y b. 
  isset(i,rsi(M,b)) ⇒
  P(App(p,b),S)) & 
 !a:mem(A) X. P(a,X) ==> ?b. App(p,b) = a”)



val cardeq_def = 
qdefine_psym("cardeq",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(B))’])
‘∃R:A~>B. 
 (∀a. IN(a,s1) ⇒ ?!b:mem(B). IN(b,s2) & Holds(R,a,b)) &
 (∀b. IN(b,s2) ⇒ ?!a:mem(A). IN(a,s1) & Holds(R,a,b))’

val cardeq_REFL = prove_store("cardeq_REFL",
e0
(rw[cardeq_def] >>
 rpt strip_tac >> qexists_tac ‘id(A)’ >> rw[id_def] >>
 rpt strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘a’ >> arw[] >> rpt strip_tac >> arw[]) >>
 uex_tac >> qexists_tac ‘b’ >> arw[] >> rpt strip_tac >> arw[])
(form_goal “!A s:mem(Pow(A)). cardeq(s,s)”));


val cardeq_SYM = prove_store("cardeq_SYM",
e0
(rw[cardeq_def] >> rpt strip_tac >>
 qexists_tac ‘op(R)’ >> arw[op_def])
(form_goal
 “∀A s1 B s2. cardeq(s1:mem(Pow(A)),s2:mem(Pow(B))) ==> cardeq(s2,s1)”));


val restrict_def = 
    AX1 |> qspecl [‘A’,‘B’]
        |> fVar_sInst_th “P(a:mem(A),b:mem(B))”
           “IN(a:mem(A),s1) & IN(b:mem(B),s2) & Holds(R,a,b) ”
        |> qsimple_uex_spec "restrict" [‘R’,‘s1’,‘s2’]
        |> gen_all

val cardeq_TRANS = prove_store("cardeq_TRANS",
e0
(rw[cardeq_def] >> rpt strip_tac >>
 qexists_tac ‘restrict(R',s2,s3) @ restrict(R,s1,s2)’ >>
 rw[GSYM ao_def,restrict_def] >> rpt strip_tac (* 2 *)
 >-- (uex_tac >> first_assum drule >>
     pop_assum (strip_assume_tac o uex_expand) >>
     first_assum drule >>
     pop_assum (assume_tac o uex_expand) >>
     pop_assum (x_choose_then "c" strip_assume_tac) >>
     qexists_tac ‘c’ >> arw[] >>
     strip_tac (* 2 *)
     >-- (qexists_tac ‘b’ >> arw[]) >>
     rpt strip_tac >> 
     qby_tac
     ‘b'' = b’ 
     >-- (first_assum irule >> arw[]) >> fs[] >>
     first_assum irule >> arw[]) >>
 uex_tac >> first_assum drule >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum (x_choose_then "b0" strip_assume_tac) >>
 last_x_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘a’ >> arw[] >>
 strip_tac (* 2 *)
 >-- (qexists_tac ‘b0’ >> arw[]) >>
 rpt strip_tac >> 
 qby_tac
 ‘b' = b0’ 
 >-- (first_assum irule >> arw[]) >> fs[] >>
 first_assum irule >> arw[])
(form_goal “!A s1:mem(Pow(A)) B s2:mem(Pow(B)).
 cardeq(s1,s2) ==>
 !C s3:mem(Pow(C)).cardeq(s2,s3) ==>
 cardeq(s1,s3)”));

val cardeq_Whole_Inj_ex = prove_store("cardeq_Whole_Inj_ex",
e0
(rpt strip_tac >>
 fs[cardeq_def,Whole_def] >>
 drule  (P2fun |> qspecl [‘B’,‘A’]
               |> fVar_sInst_th “P(b:mem(B),a:mem(A))”
                  “IN(a,s) & Holds(R:A~>B,a,b)”) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >>
 qby_tac ‘Inj(f)’ 
 >-- (rw[Inj_def] >> rpt strip_tac >>
      first_assum $ drule o iffLR >>
      first_assum (qspecl_then [‘x2’,‘App(f,x2)’] assume_tac) >>
      fs[] >>
      first_assum drule >>
      pop_assum (strip_assume_tac o uex_expand) >>
      qsuff_tac
      ‘x1 = b & x2 = b’ >-- (strip_tac >> arw[]) >>
      strip_tac >> first_assum irule >> arw[]) >>
 arw[] >>
 rw[GSYM IN_EXT_iff,IMAGE_def] >>
 strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (pop_assum (assume_tac o GSYM) >> rfs[]) >>
 first_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘b’ >> rw[Whole_def] >> flip_tac >> arw[])
(form_goal
 “∀A s:mem(Pow(A)) B. 
  cardeq(s,Whole(B)) ⇒
  ∃i:B ->A. Inj(i) & IMAGE(i,Whole(B)) = s”));

val cardeq_Inj_IMAGE = prove_store("cardeq_Inj_IMAGE",
e0
(rpt strip_tac >>
 rw[cardeq_def] >>
 qexists_tac ‘asR(f)’ >> rw[asR_def,Whole_def,IMAGE_def] >>
 rpt strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘App(f,a)’ >> rw[] >>
     rpt strip_tac (* 2 *)
     >-- (qexists_tac ‘a’ >> rw[]) >> arw[]) >>
 arw[] >> uex_tac >> qexists_tac ‘a’ >> arw[] >>
 rpt strip_tac >> fs[Inj_def] >> first_assum irule >> arw[])
(form_goal
 “∀A B f:A->B. Inj(f) ⇒
 cardeq(Whole(A),IMAGE(f,Whole(A)))”));


val cardeq_Inj_IMAGE_gen = prove_store("cardeq_Inj_IMAGE_gen",
e0
(cheat)
(form_goal
 “∀A B f:A->B. Inj(f) ⇒
 ∀s.cardeq(s,IMAGE(f,s))”));

val Inj_Image = prove_store("Inj_Image",
e0
(rpt strip_tac >>
 rw[Inj_def] >> rw[Image_def,GSYM IN_EXT_iff] >>
 rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (first_assum (qspecl_then [‘App(f,x)’] assume_tac) >>
     qby_tac ‘∃a. IN(a,x1) & App(f,x) = App(f,a)’ 
     >-- (qexists_tac ‘x’ >> arw[]) >>
     first_assum (drule o iffLR) >>
     pop_assum strip_assume_tac >>
     fs[Inj_def] >> first_assum drule >> fs[]) >>
 first_assum (qspecl_then [‘App(f,x)’] assume_tac) >>
 qby_tac ‘∃a. IN(a,x2) & App(f,x) = App(f,a)’ 
 >-- (qexists_tac ‘x’ >> arw[]) >>
 first_assum (drule o iffRL) >> 
 pop_assum strip_assume_tac >>
 fs[Inj_def] >> first_assum drule >> fs[])
(form_goal
 “∀A B f:A-> B. Inj(f) ⇒ Inj(Image(f))”));


val INJ_def = 
    qdefine_psym("INJ",
                 [‘f:A->B’,‘s:mem(Pow(A))’,‘t:mem(Pow(B))’])
                ‘(!x. IN(x,s) ==> IN(App(f,x),t)) &
                 (!x y. IN(x,s) & IN(y,s) ==> 
                     App(f,x) = App(f,y) ==>
                                   x = y)’ |> gen_all


val IMAGE_INJ_cardeq = 
prove_store("IMAGE_INJ_cardeq",
e0
cheat
(form_goal
 “!A s1 B s2 f:A->B.INJ(f,s1,s2) ==>
  !s01. SS(s01,s1) ==> cardeq(s01,IMAGE(f,s01))”));


val POW_def = IN_def_P |> qspecl [‘Pow(A)’] 
                       |> fVar_sInst_th “P(s:mem(Pow(A)))”
                          “SS(s,s0:mem(Pow(A)))”
                       |> qsimple_uex_spec "POW" [‘s0’]
                       |> gen_all

val cardeq_POW_Whole_Pow = prove_store("cardeq_POW_Whole_Pow",
e0
cheat
(form_goal
 “∀A.cardeq(POW(Whole(A)),Whole(Pow(A)))”));


val nPow_def = qdefine_psym("nPow",[‘n:mem(N)’,‘A’,‘B’])
‘?X f:X->N. cardeq(FIB(f,O),Whole(A)) & 
            cardeq(FIB(f,n),Whole(B)) &
  (!n0. Lt(n0,n) ==>
   cardeq(POW(FIB(f,n0)),FIB(f,Suc(n0))))’
|> gen_all



val FIB_constf = prove_store("FIB_constf",
e0
(rw[GSYM IN_EXT_iff,FIB_def,Whole_def,constf_def,PREIM_def,IN_Sing] >>
 rpt strip_tac >> qexists_tac ‘b’ >> rw[])
(form_goal
 “∀A B b:mem(B). FIB(constf(A,b),b) = Whole(A)”));

val nPow_O = prove_store("nPow_O",
e0
(rw[nPow_def] >> strip_tac >>
 rw[NOT_Lt_O] >> qexistsl_tac [‘A’,‘constf(A,O)’] >>
 rw[FIB_constf,cardeq_REFL])
(form_goal “∀A. nPow(O,A,A)”));


val Sgf_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?sf:Pow(A)-> B.
   (∀a. App(sf,Sing(a)) = App(f,a)) &
   (∀s. (∀a. ~(s = Sing(a))) ⇒ App(sf,s) = b0)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘sf’ >> arw[] >>
     rpt strip_tac >>
     rw[GSYM FUN_EXT] >> rpt strip_tac >>
     qcases ‘∃a0. a = Sing(a0)’ (* 2 *)
     >-- fs[] >>
     qby_tac
     ‘∀a0. ~(a = Sing(a0))’
     >-- (strip_tac >> ccontra_tac >>
         qby_tac ‘∃a0. a = Sing(a0)’ 
         >-- (qexists_tac ‘a0’ >> arw[]) >>
         rfs[]) >>
     first_x_assum drule >> first_x_assum drule>> fs[]) >>
 qby_tac
 ‘∀s:mem(Pow(A)).
  ?!b. (∃a. s = Sing(a) & b = App(f,a))|
       (∀a. ~(s = Sing(a))) & b = b0’
 >-- (strip_tac >>
     qcases ‘∃a. s = Sing(a)’ 
     >-- (uex_tac >> pop_assum strip_assume_tac >>
         qexists_tac ‘App(f,a)’ >> arw[] >>
         rpt strip_tac (* 3 *)
         >-- (disj1_tac >> qexists_tac ‘a’ >> rw[])
         >-- fs[Sing_eq_eq] >>
         fs[Sing_eq_eq] >>
         first_x_assum (qspecl_then [‘a’] assume_tac) >> fs[]) >>
     uex_tac >> qexists_tac ‘b0’ >>
     rpt strip_tac (* 2 *)
     >-- 
     (disj2_tac >> rw[] >> strip_tac >> ccontra_tac >>
     qby_tac
     ‘∃a. s = Sing(a)’
     >-- (qexists_tac ‘a’ >> arw[]) >> rfs[]) >>
     qby_tac
     ‘∃a. s = Sing(a)’
     >-- (qexists_tac ‘a’ >> arw[]) >> rfs[]) >>
 drule
 (P2fun |> qspecl [‘Pow(A)’,‘B’] 
 |> fVar_sInst_th “P(s:mem(Pow(A)),b:mem(B))”
    “(∃a. s = Sing(a) & b = App(f:A->B,a))|
     (∀a. ~(s = Sing(a))) & b = b0”) >>
 pop_assum strip_assume_tac >> 
 qexists_tac ‘f'’ >>
 arw[] >> rpt strip_tac (* 2 *)
 >-- (disj1_tac >> qexists_tac ‘a’ >> rw[]) >>
 disj2_tac >> arw[])
(form_goal
 “∀A B f:A->B b0:mem(B). 
  ?!sf:Pow(A)-> B.
   (∀a. App(sf,Sing(a)) = App(f,a)) &
   (∀s. (∀a. ~(s = Sing(a))) ⇒ App(sf,s) = b0 )”)
|> spec_all
|> qsimple_uex_spec "Sgf" [‘f’,‘b0’] 



(*
val Sgf_FIB_BIJ = prove_store("Sgf_FIB_BIJ",
e0
(cheat)
(form_goal
 “∀A B f:A->B b0.
  ~IN(b0,IMAGE(f,Whole(A))) ⇒
  ∀b. IN(b,IMAGE(f,Whole(A))) ⇒ 
      BIJ(Sg(A),FIB(f,b),FIB(Sgf(f,b0),b))”));
val INJ_def = 
qdefine_psym("INJ",
[‘f:A->B’,‘s:mem(Pow(A))’,‘t:mem(Pow(B))’])
‘(!x. IN(x,s) ==> IN(App(f,x),t)) &
(!x y. IN(x,s) & IN(y,s) ==> App(f,x) = App(f,y) ==>
 x = y)’ |> gen_all

val SURJ_def = 
qdefine_psym("SURJ",
[‘f:A->B’,‘s:mem(Pow(A))’,‘t:mem(Pow(B))’])
‘(!x. IN(x,s) ==> IN(App(f,x),t)) &
(!x. IN(x,t) ==> ?y. IN(y,s) & App(f,y) = x)’ |> gen_all

val BIJ_def = 
qdefine_psym
("BIJ",[‘f:A->B’,‘s:mem(Pow(A))’,‘t:mem(Pow(B))’])
‘INJ(f,s,t) & SURJ(f,s,t)’ |> gen_all

*)


val Sgf_cardeq = prove_store("Sgf_cardeq",
e0
(cheat)
(form_goal
 “∀A B f:A->B b0.
  ~IN(b0,IMAGE(f,Whole(A))) ⇒
  ∀b. IN(b,IMAGE(f,Whole(A))) ⇒ 
      cardeq(FIB(f,b),FIB(Sgf(f,b0),b))”));

(*
val same_FIB_cardeq = prove_store("same_FIB_cardeq",
e0
()
(form_goal
 “∀A B f1:A->B f2:A->B.
  ”));
*)

(*option extension*)
val OE_def = 
qdefine_fsym("OE",[‘f:A->B’,‘b0:mem(B)’])
‘coPa(f,El(b0))’

val nPow_Suc = prove_store("nPow_Suc",
e0
(rpt strip_tac >>
 rw[nPow_def] >> rw[Lt_Suc_Le] >> 
 fs[nPow_def] >>
 qexistsl_tac [‘Pow(X+1)’] >>
 qby_tac ‘cardeq(Whole(An),FIB(f, n))’ >-- cheat >>
 drule $ iffLR cardeq_def  >>
 pop_assum strip_assume_tac >> 
 qby_tac
 ‘INJ(OE(f,))’
 qby_tac
 ‘Inj(Image(f'))’ 
 >-- cheat >>
 

 qby_tac
 ‘∃i:Pow(An) -> Pow(X). Inj(i)’
 define_lambda
 “∀px1.
   (∃x. px1 = Sing(SOME(x))) ⇒
   App(f1,px1) = App(Sgf(OE(f,Suc(n)),Suc(Suc(n))),px1) &
   (∃x. px1 = Ins(NONE(X),Sing(SOME(x)))) ⇒
   App(f1,px1) = )”
 
 rastt "App(Sgf(coPa(f:X->N,El(Suc(n))),NONE(X)),px1)"
 qexists_tac ‘Sg(X+1) o ’
 qsuff_tac
 ‘∃f:Pow(X+1) -> N.
   cardeq(FIB(f,O),Whole(A)) & 
   cardeq(F)’
 
 )
(form_goal “∀A An. nPow(n,A,An) ⇒ nPow(Suc(n),A,Pow(An))”));

val Inj_IMAGE_cardeq = proved_th $
e0
cheat
(form_goal
 “∀A B f:A->B. Inj(f) ⇒
  ∀s.cardeq(IMAGE(f,s),s)”)

 

val INS_def = 
qfun_compr ‘s:mem(Pow(X))’ ‘Ins(x0:mem(X),s)’ 
|> qsimple_uex_spec "INS" [‘x0’] |> gen_all


(*content*)
val content_def = proved_th $
e0
cheat
(form_goal 
 “!X x0.?!f:Pow(X) ->X. 
  !s x. s = Sing(x) ==> App(f,s) = x &
        (!x. ~(s = Sing(x)) ==> App(f,s) = x0)”)
|> spec_all |> qsimple_uex_spec "content" [‘x0’] 
|> gen_all 

val content_Sing = content_def 
|> qsspecl [‘x0:mem(X)’,‘Sing(x:mem(X))’,‘x:mem(X)’]
|> rewr_rule[] |> qgenl [‘X’,‘x0’,‘x’] 


val ctt_def = qdefine_fsym("ctt",[‘s:mem(Pow(X))’,‘x0:mem(X)’])
‘App(content(x0),s)’ |> gen_all

val nPow_Suc_ex_lemma = proved_th $
e0
(rpt strip_tac >> cheat
 (*define_lambda
 “∀x1s. 
    ((∃s0:mem(Pow(An)). 
        x1s = Ins(NONE(X),App(Image(i1(X,1)) o i,s0))) ⇒
     App(f1,x1s) = Suc(n)) &
    ((∃x. 
       x1s = Sing(SOME(x)) & App(f,x) = n) ⇒
    App(f1,x1s) = ctt(IMAGE(f,PREIM(i1(X,1),x1s)),O)) &
    (ELSE ⇒ App(f1,x1s) = Suc(Suc(n)))”*) )
(form_goal
 “∀C X i:C-> Pow(X). Inj(i) ⇒
  ∀B f:X->B bs:mem(Pow(B)) b0. 
  ~IN(b0,bs) ⇒
  ∃f1: Pow(X+1) -> B.
  (∀b. IN(b,bs) ⇒ FIB(f1,b) = IMAGE(Sg(X+1) o i1(X,1),FIB(f,b))) & 
  FIB(f1,b0) = IMAGE(INS(NONE(X)) o Image(i1(X, 1)) o i,Whole(C)) ”)

val biunique_def = 
qdefine_psym("biunique",[‘R:A~>B’,‘s1:mem(Pow(A))’,‘s2:mem(Pow(B))’])
‘(∀a. IN(a,s1) ⇒ ?!b:mem(B). IN(b,s2) & Holds(R,a,b)) &
  (∀b. IN(b,s2) ⇒ ?!a:mem(A). IN(a,s1) & Holds(R,a,b))’

val biunique_Ri_restrict = prove_store("biunique_Ri_restrict",
e0
()
(form_goal
 “biunique(R,s1,s2) ⇒
  ∀s t. SS(s,s1) & SS(t,s2) ⇒
       t = App(Ri(restrict(R)),s) = t = App(Ri(restrict(R)),s) ”)); 


val SS_Ri_restrict = prove_store("SS_Ri_restrict",
e0
cheat
(form_goal
 “∀A s1 a. SS(a, s1) ⇒ ∀B R s2.  SS(App(Ri(restrict(R:A~>B, s1, s2)), a), s2)”));

val biunique_op = prove_store("biunique_op",
e0
()
(form_goal
 “”));

val cardeq_POW = prove_store("cardeq_POW",
e0
(rpt strip_tac >> fs[cardeq_def] >>
 (assume_tac o uex2ex_rule)
 (AX1 |> qspecl [‘Pow(A)’,‘Pow(B)’]
      |> fVar_sInst_th “P(s:mem(Pow(A)),t:mem(Pow(B)))”
      “SS(s,s1) & SS(t,s2) & t = App(Ri(restrict(R:A~>B,s1,s2)),s)”) >>
 pop_assum (x_choose_then "R1" assume_tac) >>
 qexists_tac ‘R1’ >>
 rw[POW_def] >> arw[] >> rpt strip_tac (* 2 *)
 >-- (uex_tac >>
     qexists_tac ‘App(Ri(restrict(R, s1, s2)), a)’ >>
     drule SS_Ri_restrict >> arw[] >>
     rpt strip_tac >> arw[]) >>
 uex_tac >>
 qexists_tac ‘App(Ri(restrict(op(R), s2, s1)), b)’ >>
 drule SS_Ri_restrict >> arw[] >>
 qsuff_tac
 ‘App(Ri(restrict(R, s1, s2)), App(Ri(restrict(op(R), s2, s1)), b)) = b’
 >-- (strip_tac >> arw[] >> rpt strip_tac >> arw[] 
 )
(form_goal
 “∀A s1:mem(Pow(A)) B s2:mem(Pow(B)).
  cardeq(s1,s2) ⇒ cardeq(POW(s1),POW(s2))”));

val cardeq_BITRANS = prove_store("cardeq_BITRANS",
e0
(rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (irule cardeq_TRANS >>
     qexistsl_tac [‘C’,‘s3’] >> arw[] >> irule cardeq_TRANS >>
     qexistsl_tac [‘A’,‘s1’] >> arw[] >> irule cardeq_SYM >>
     arw[]) >>
 irule cardeq_TRANS >>
 qexistsl_tac [‘B’,‘s2’] >> arw[] >>
 irule cardeq_TRANS >> qexistsl_tac [‘D’,‘s4’] >> arw[] >>
 irule cardeq_SYM >> arw[])
(form_goal
 “∀A s1:mem(Pow(A)) B s2:mem(Pow(B)). 
    cardeq(s1,s2) ⇒
    ∀C s3:mem(Pow(C)) D s4:mem(Pow(D)). 
      cardeq(s3,s4) ⇒
    (cardeq(s1,s3) ⇔ cardeq(s2,s4))”));

val nPow_Suc = prove_store("nPow_Suc",
e0
(rpt strip_tac >>
 rw[nPow_def] >> rw[Lt_Suc_Le] >> 
 fs[nPow_def] >>
 qexistsl_tac [‘Pow(X+1)’] >>
 drule cardeq_Whole_Inj_ex >>
 pop_assum strip_assume_tac >>
 drule Inj_Image >> 
 drule nPow_Suc_ex_lemma >>
 strip_assume_tac
 (IN_def_P_ex |> qspecl [‘N’] 
 |> fVar_sInst_th “P(n0:mem(N))” “Le(n0,n)”
 |> GSYM) >>
 first_x_assum (qsspecl_then [‘f’,‘s’,‘Suc(n)’] assume_tac) >>
 qby_tac
 ‘~IN(Suc(n),s)’ 
 >-- arw[NOT_LESS_EQ,Lt_Suc]  >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f1’ >> rfs[] >> 
 qby_tac
 ‘Inj(Sg(X+1) o i1(X,1))’
 >-- (irule o_Inj_Inj >> rw[i1_Inj,Sg_Inj]) >> 
 qby_tac
 ‘∀b. Le(b,n) ⇒ 
      cardeq(FIB(f1,b),FIB(f,b))’
 >-- (rpt strip_tac >> first_x_assum drule >> arw[] >>
     irule cardeq_SYM >> irule cardeq_Inj_IMAGE_gen >>
     arw[]) >>
 qby_tac
 ‘cardeq(FIB(f1, O), Whole(A))’
 >-- (first_x_assum (qspecl_then [‘O’] assume_tac) >>
     fs[O_LESS_EQ] >>
     drule cardeq_TRANS >>
     first_x_assum irule >> fs[]) >> arw[] >>  
 qby_tac
 ‘cardeq(IMAGE(INS(NONE(X)) o Image(i1(X, 1)) o Image(i), Whole(Pow(An))),
              Whole(Pow(An)))’
 >-- cheat >> arw[] >>
 rpt strip_tac >>
 drule Le_cases >> pop_assum strip_assume_tac (* 2 *)
 >-- (first_x_assum drule >> last_x_assum drule >>
     qby_tac ‘Le(Suc(n0),n)’ >-- arw[GSYM Lt_Le_Suc] >>
     first_assum drule >>
     arw[] >> first_x_assum rev_drule >> arw[] >>
     qby_tac
     ‘cardeq(POW(IMAGE(Sg(X + 1) o i1(X, 1), FIB(f, n0))), 
             POW(FIB(f, n0)))’   
     >-- (irule cardeq_POW >> irule cardeq_SYM  >>
         irule cardeq_Inj_IMAGE_gen >> arw[]) >>
     drule cardeq_BITRANS >>
     qby_tac
     ‘cardeq(IMAGE(Sg(X + 1) o i1(X, 1), FIB(f, Suc(n0))),
             FIB(f, Suc(n0)))’ 
     >-- (irule cardeq_SYM >> irule cardeq_Inj_IMAGE_gen >> arw[]) >>
     first_x_assum drule >>
     fs[]) >> fs[] >>
 qby_tac
 ‘cardeq(POW(Whole(An)),Whole(Pow(An)))’
 >-- rw[cardeq_POW_Whole_Pow] >> 
 qby_tac
 ‘cardeq(POW(FIB(f1, n)),POW(Whole(An)))’ 
 >-- (irule cardeq_POW >> last_x_assum drule >> arw[] >>
      irule cardeq_TRANS >> qexistsl_tac [‘X’,‘FIB(f,n)’] >>
      arw[] >> irule cardeq_SYM >> irule cardeq_Inj_IMAGE_gen >> arw[]) >>
 drule cardeq_BITRANS >>
 first_x_assum 
 (qsspecl_then [‘IMAGE(INS(NONE(X)) o Image(i1(X, 1)) o Image(i), Whole(Pow(An)))’, ‘Whole(Pow(An))’] assume_tac) >>
 first_x_assum drule >> arw[])
(form_goal “∀A An. nPow(n,A,An) ⇒ nPow(Suc(n),A,Pow(An))”));


val nPow_Suc = prove_store("nPow_Suc",
e0
(rpt strip_tac >>
 rw[nPow_def] >> rw[Lt_Suc_Le] >> 
 fs[nPow_def] >>
 qexistsl_tac [‘Pow(X+1)’] >>
 drule $ iffLR cardeq_char >>
 qby_tac
 ‘’
 qby_tac
 ‘∃i:Pow(An) -> Pow(X). Inj(i)’
 >-- cheat >> pop_assum strip_assume_tac >> 
 
 define_lambda
 “∀x1s. 
    ((∃s0:mem(Pow(An)). 
        x1s = Ins(NONE(X),App(Image(i1(X,1)) o i,s0))) ⇒
     App(f1,x1s) = Suc(n)) &
    ((∃x. 
       x1s = Sing(SOME(x)) & App(f,x) = n) ⇒
    App(f1,x1s) = ctt(IMAGE(f,PREIM(i1(X,1),x1s)),O)) &
    (ELSE ⇒ App(f1,x1s) = Suc(Suc(n)))” >>

rastt "ctt(IMAGE(f,FIB(i1(X,1),x1s)),O)" 

 qsuff_tac
 ‘∃f1:Pow(X+1) ->N.
  (∀x1s x. Le(App(f,x),n) ⇒
           (App(f1,x1s) = App(f,x) ⇔ x1s = Sing(SOME(x)))) &
  (∀x1s. App(f1,x1s) = Suc(n) ⇔
         ∃s0:mem(Pow(An)). 
           x1s = Ins(NONE(X),App(Image(i1(X,1)) o i,s0)))’ 
 >-- strip_tac >>
     qexists_tac ‘f1’ >>
     qby_tac
     ‘∀n0.Le(n0,n) ⇒ FIB(f1,n0) = IMAGE(Sg(X+1) o i1(X,1),FIB(f,n0))’
     >-- cheat >> 
     qby_tac 
     ‘cardeq(FIB(f1, O), Whole(A))’
     >-- (first_x_assum (qspecl_then [‘O’] assume_tac) >>
         fs[O_LESS_EQ] >> 
         qby_tac ‘Inj(Sg(X + 1) o i1(X, 1))’ 
         >-- cheat >>
         drule Inj_IMAGE_cardeq >> 
         first_x_assum (qspecl_then [‘FIB(f,O)’] assume_tac) >>
         drule cardeq_TRANS >>
         first_x_assum drule >> arw[]) >>
     arw[] >>
     qby_tac
     ‘cardeq(FIB(f1, Suc(n)), Whole(Pow(An)))’
     >-- qby_tac
         ‘FIB(f1, Suc(n)) = 
          IMAGE(INS(NONE(X)) o Image(i1(X, 1)) o i,Whole(Pow(An)))’
         >-- cheat >>
         arw[] >>
         
     qby_tac
     ‘∀n0. Le(n0,n) ⇒
      cardeq(POW(FIB(f1, n0)), FIB(f1, Suc(n0)))’
     >-- rpt strip_tac >>
         first_assum drule >>
         arw[] >>
         drule Le_cases >>
         pop_assum strip_assume_tac (* 2 *)
         >-- (last_x_assum drule >> 
             qby_tac
             ‘Le(Suc(n0),n)’
             >-- arw[GSYM Lt_Le_Suc] >>
             first_assum drule >>
             arw[] >> cheat) >>
             (*then use inj and trans*) 
         arw[] >>
         (*need to prove pow(An) before prove this *)

          “x1s = Ins(NONE(X),App(Image(i1(X,1)) o i,s0:mem(Pow(An))))”
 qsuff_tac
 ‘∃f1:Pow(X+1) ->N.
   (∀x. App(f1,Sing(SOME(x))) = App(f,x)) &
   (∀x1s s0.   ⇔ App(f1,xs) = Suc(n)) &
   ()’
 qby_tac
 ‘’)
(form_goal “∀A An. nPow(n,A,An) ⇒ nPow(Suc(n),A,Pow(An))”));


val nPow_ex = prove_store("nPow_ex",
e0
(strip_tac >> Nind_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘A’ >> rw[nPow_O]) >>
 qexists_tac ‘Pow(An)’ >>
 drule nPow_Suc>> arw[] )
(form_goal “!A n. ?An. nPow(n,A,An)”));

val large_ex = prove_store("large_ex",
e0
(rpt strip_tac >>
 assume_tac
 (AX5 |> qspecl [‘N’] 
 |> fVar_sInst_th “P(n:mem(N),An)”
     “nPow(n,A,An)”) >>
 pop_assum strip_assume_tac >> qexists_tac ‘Y’ >> 
 rpt strip_tac >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 first_x_assum (qsspecl_then [‘b’] assume_tac) >> 
 rw[cardleq_def] >> 
 f


 qsspecl_then [‘n’] assume_tac nPow_ex >>
 pop_assum strip_assume_tac >> )
(form_goal 
 “!A. 
    ?P. 
      !n An. nPow(n,A,An) ==> cardleq(Whole(An),Whole(P)) ”));


