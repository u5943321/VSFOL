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

(*
{} ⊆ {*}
 ~
{} ⊆ {}
'a -> 'b

R: 'a ~>'b

*)


val cardeq_def = 
qdefine_psym("cardeq",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(B))’])
‘∃R:A~>B. 
 (∀a. IN(a,s1) ⇒ ?!b. IN(b,s2) & Holds(R,a,b)) &
 (∀b. IN(b,s2) ⇒ ?!a. IN(a,s1) & Holds(R,a,b))’

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


val IMAGE_INJ_cardeq = prove_store("IMAGE_INJ_cardeq",
e0
(rpt strip_tac >>
 rw[cardeq_def] >>
 strip_assume_tac 
 (AX1 |> qspecl [‘A’,‘B’] 
      |> fVar_sInst_th “P(a:mem(A),b:mem(B))”
         “IN(a,s1)& b = App(f:A->B,a)”
      |> uex2ex_rule) >> 
 qexists_tac ‘R’ >> arw[IMAGE_def] >>
 rpt strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘App(f,a)’ >> 
     fs[SS_def] >> first_assum drule >> arw[] >>
     rpt strip_tac >>
     qexists_tac ‘a’ >> arw[]) >>
     arw[] >> fs[INJ_def] >> uex_tac >>
     qexists_tac ‘a’ >> arw[] >> fs[SS_def] >> 
     first_x_assum drule >> arw[] >> rpt strip_tac >>
     first_x_assum irule >> arw[])
(form_goal
 “!A s1 B s2 f:A->B.INJ(f,s1,s2) ==>
  !s01. SS(s01,s1) ==> cardeq(s01,IMAGE(f,s01))”));

val Inj_INJ = prove_store("Inj_INJ",
e0
(rpt strip_tac >> fs[Inj_def,INJ_def] >> rpt strip_tac (* 2 *)
 >-- (rw[IMAGE_def] >> qexists_tac ‘x’ >> arw[]) >>
 first_x_assum irule >> arw[])
(form_goal
 “∀A B f:A->B. Inj(f) ⇒
  ∀s.INJ(f,s,IMAGE(f,s))”));


val INJ_SS_dom = prove_store("INJ_SS_dom",
e0
(rw[SS_def,INJ_def] >> rpt strip_tac (* 2 *)
 >-- (first_x_assum drule >> first_x_assum drule >> arw[]) >>
 first_x_assum irule >> arw[] >> strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “∀A B f:A->B s1 s2. INJ(f,s1,s2) ⇒
  ∀s. SS(s,s1) ⇒ INJ(f,s,s2)”));


val INJ_SS_cod = prove_store("INJ_SS_cod",
e0
(rw[SS_def,INJ_def] >> rpt strip_tac (* 2 *)
 >-- (first_x_assum drule >> first_x_assum drule >> arw[]) >>
 first_x_assum irule >> arw[] >> strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “∀A B f:A->B s1 s2. INJ(f,s1,s2) ⇒
  ∀s. SS(s2,s) ⇒ INJ(f,s1,s)”));

val o_INJ_INJ = prove_store("o_INJ_INJ",
e0
(rpt strip_tac >> fs[INJ_def] >>
 rpt strip_tac (* 2 *)
 >-- (rw[App_App_o] >> first_x_assum irule >> first_x_assum irule >> arw[]) >>
 first_x_assum irule >> arw[] >>
 fs[App_App_o] >> first_x_assum irule >> arw[] >>
 strip_tac >>
 first_x_assum irule >> arw[])
(form_goal
 “∀A B f:A->B s1 s2. INJ(f,s1,s2) ⇒
 ∀C g:B->C s3. INJ(g,s2,s3) ⇒ INJ(g o f, s1,s3)”));

val cardeq_Inj_IMAGE_gen = prove_store("cardeq_Inj_IMAGE_gen",
e0
(rpt strip_tac >> irule IMAGE_INJ_cardeq >>
 drule Inj_INJ >> 
 first_x_assum (qspecl_then [‘s’] assume_tac) >>
 qexistsl_tac [‘s’,‘IMAGE(f,s)’] >> arw[SS_Refl])
(form_goal
 “∀A B f:A->B. Inj(f) ⇒
  ∀s.cardeq(s,IMAGE(f,s))”));


val INS_def = 
qfun_compr ‘s:mem(Pow(X))’ ‘Ins(x0:mem(X),s)’ 
|> qsimple_uex_spec "INS" [‘x0’] |> gen_all


val INJ_INS_NONE = prove_store("INJ_INS_NONE",
e0
(rpt strip_tac >>
 rw[INJ_def] >> rpt strip_tac (* 2 *)
 >-- (rw[IMAGE_def] >> qexists_tac ‘x’ >> arw[]) >>
 fs[GSYM IN_EXT_iff,INS_def,Ins_def] >>
 strip_tac >> 
 first_assum drule >> first_assum drule >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum (qspecl_then [‘x'’] assume_tac) >> rfs[] >>
     fs[] >> first_x_assum rev_drule >> fs[]) >>
 first_x_assum (qspecl_then [‘x'’] assume_tac) >>
 rfs[] >> fs[])
(form_goal
 “∀X s:mem(Pow(Pow(X+1))). 
   (∀s0.IN(s0,s) ⇒ ~IN(NONE(X),s0)) ⇒
   INJ(INS(NONE(X)),s,IMAGE(INS(NONE(X)),s))”));

val POW_def = IN_def_P |> qspecl [‘Pow(A)’] 
                       |> fVar_sInst_th “P(s:mem(Pow(A)))”
                          “SS(s,s0:mem(Pow(A)))”
                       |> qsimple_uex_spec "POW" [‘s0’]
                       |> gen_all

val POW_Whole_Pow = prove_store("POW_Whole_Pow",
e0
(rw[GSYM IN_EXT_iff,Whole_def,POW_def,SS_def] )
(form_goal “∀A. POW(Whole(A)) = Whole(Pow(A))”));

val cardeq_POW_Whole_Pow = prove_store("cardeq_POW_Whole_Pow",
e0
(rw[POW_Whole_Pow,cardeq_REFL])
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

(*

val Sgf_cardeq = prove_store("Sgf_cardeq",
e0
(cheat)
(form_goal
 “∀A B f:A->B b0.
  ~IN(b0,IMAGE(f,Whole(A))) ⇒
  ∀b. IN(b,IMAGE(f,Whole(A))) ⇒ 
      cardeq(FIB(f,b),FIB(Sgf(f,b0),b))”));
*)

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


(*content*)
val content_def = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?f:Pow(X) ->X. 
  (!s x. s = Sing(x) ==> App(f,s) = x) &
  (∀s.(!x. ~(s = Sing(x))) ==> App(f,s) = x0)’
 >-- (rpt strip_tac >> uex_tac >> qexists_tac ‘f’ >>
     arw[] >> rpt strip_tac >>
     irule $ iffLR FUN_EXT >> strip_tac >>
     qcases ‘∃x. a = Sing(x)’ (* 2 *)
     >-- (fs[] >>
         first_x_assum drule >> first_x_assum drule >> rfs[]) >>
     qby_tac
     ‘∀x. ~(a = Sing(x))’
     >-- (rpt strip_tac >> 
         ccontra_tac >>
         qby_tac ‘∃x. a = Sing(x)’
         >-- (qexists_tac ‘x’ >> arw[]) >> rfs[]) >>
     first_x_assum drule >> first_x_assum drule >> fs[]) >>
 strip_assume_tac
 (P2fun |> qspecl [‘Pow(X)’,‘X’] 
 |> fVar_sInst_th “P(s:mem(Pow(X)),x:mem(X))”
    “s = Sing(x) |
     (∀x:mem(X). ~(s = Sing(x))) & x = x0”) >>
 qby_tac
 ‘∀s. ?!x.s = Sing(x) |
     (∀x:mem(X). ~(s = Sing(x))) & x = x0 ’
 >-- (strip_tac >> uex_tac >>
     qcases ‘∃x. s = Sing(x)’ (* 2 *)
     >-- (pop_assum strip_assume_tac >>
         qexists_tac ‘x’ >> arw[] >> rw[Sing_eq_eq] >>
         rpt strip_tac >> fs[] >> 
         first_x_assum (qspecl_then [‘x’] assume_tac) >> fs[]) >>
      qby_tac
     ‘∀x. ~(s = Sing(x))’
     >-- (rpt strip_tac >> 
         ccontra_tac >>
         qby_tac ‘∃x. s = Sing(x)’
         >-- (qexists_tac ‘x’ >> arw[]) >> rfs[]) >>
     arw[] >> qexists_tac ‘x0’ >> rw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac>> qexists_tac ‘f’ >> arw[] >>
 rpt strip_tac >> arw[]
)
(form_goal 
 “!X x0.?!f:Pow(X) ->X. 
  (!s x. s = Sing(x) ==> App(f,s) = x) &
  (∀s. (!x. ~(s = Sing(x))) ==> App(f,s) = x0)”)
|> spec_all |> qsimple_uex_spec "content" [‘x0’] 
|> gen_all 

val content_Sing = 
content_def |> qsspecl [‘x0:mem(X)’] 
            |> conjE1
            |> qsspecl [‘Sing(x:mem(X))’,‘x:mem(X)’]
|> rewr_rule[] |> qgenl [‘X’,‘x0’,‘x’] 


val ctt_def = qdefine_fsym("ctt",[‘s:mem(Pow(X))’,‘x0:mem(X)’])
‘App(content(x0),s)’ |> gen_all

val Sg_Sing = prove_store("Sg_Sing",
e0
(rw[Sing_def])
(form_goal “∀A a.Sing(a)  = App(Sg(A),a)”));

val PREIM_i1_Sing_SOME = prove_store("PREIM_i1_Sing_SOME",
e0
(rw[GSYM IN_EXT_iff,PREIM_def,IN_Sing,GSYM SOME_def] >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- rfs[SOME_eq_eq] >>
 qexists_tac ‘SOME(x)’ >> arw[])
(form_goal
 “PREIM(i1(X, 1), Sing(SOME(x0))) = Sing(x0)”));


val IMAGE_Sing  = prove_store("IMAGE_Sing",
e0
(rw[GSYM IN_EXT_iff,IMAGE_def,IN_Sing] >>
 strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- arw[] >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “IMAGE(f:A->B,Sing(a)) = Sing(App(f,a))”));


val ctt_Sing = prove_store("ctt_Sing",
e0
(rw[ctt_def,content_Sing])
(form_goal
 “∀A a0:mem(A) a.ctt(Sing(a),a0) = a”));


val Sing_SOME_NEQ_Ins_NONE = prove_store("Sing_SOME_NEQ_Ins_NONE",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,Ins_def,IN_Sing] >>
 rpt strip_tac >> ccontra_tac >>
 first_x_assum (qspecl_then [‘NONE(A)’] assume_tac) >>
 fs[GSYM SOME_NOTNONE])
(form_goal “∀A a s.~(Sing(SOME(a)) = Ins(NONE(A),s))”));

(*

val nPow_Suc_ex_lemma = proved_th $
e0
(cheat)
(form_goal
 “∀C X i:C-> Pow(X). Inj(i) ⇒
  ∀B f:X->B bs:mem(Pow(B)) b0. 
  ~IN(b0,bs) ⇒
  ∀b1. ~(b1 = b0) & ~IN(b1,bs) ⇒ 
  ∃f1: Pow(X+1) -> B.
  (∀b. IN(b,bs) ⇒ FIB(f1,b) = IMAGE(Sg(X+1) o i1(X,1),FIB(f,b))) & 
  FIB(f1,b0) = IMAGE(INS(NONE(X)) o Image(i1(X, 1)) o i,Whole(C)) ”)

*)


val nPow_Suc_ex_lemma = proved_th $
e0
(rpt strip_tac >> 
 x_choose_then "f1" assume_tac
 (define_lambda
 “∀x1s. 
    ((∃s0. 
        x1s = Ins(NONE(X),App(Image(i1(X,1)) o i:C->Pow(X),s0))) ⇒
     App(f1,x1s) = b0) &
    ((∃x. 
       x1s = Sing(SOME(x))) ⇒
       App(f1,x1s) = ctt(IMAGE(f:X->B,PREIM(i1(X,1),x1s)),b0)) &
    (ELSE ⇒ App(f1,x1s) = b1)”
 |> uex2ex_rule) >> 
 qexists_tac ‘f1’ >> rpt strip_tac (* 2 *) >--
 (rw[GSYM IN_EXT_iff,FIB_def,PREIM_def,IN_Sing,IMAGE_def] >>
 rw[IN_EXT_iff] >> strip_tac >>
 dimp_tac >> rpt strip_tac >> arw[] (* 2 *)
 >-- (rfs[] >>
     qcases
     ‘(∃s0. 
        x = Ins(NONE(X),App(Image(i1(X,1)) o i:C->Pow(X),s0)))’ (* 2 *)
     >-- (first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
         first_x_assum drule >>
         qsuff_tac
         ‘b1 = b0’ >-- arw[] >>
         pop_assum (assume_tac o GSYM) >> 
         qpick_x_assum ‘~(b1 = b0)’ (K all_tac) >> fs[]) >>
     qcases 
     ‘∃x0. x = Sing(SOME(x0))’ 
     >-- (first_x_assum (qspecl_then [‘x’] strip_assume_tac) >> 
         qby_tac
         ‘App(f1, x) = ctt(IMAGE(f, PREIM(i1(X, 1), x)), b0)’
         >-- (first_x_assum irule >> arw[]) >> 
         fs[] >> qexists_tac ‘x0’ >> 
         arw[App_App_o,GSYM SOME_def,Sg_Sing] >>
         qexists_tac ‘App(f1,x)’ >> arw[] >>  
         fs[] >> fs[PREIM_i1_Sing_SOME,ctt_Sing,IMAGE_Sing]) >>
     qsuff_tac ‘b = b1’ >-- (strip_tac >> fs[]) >>
     first_x_assum (qspecl_then [‘x’] strip_assume_tac) >> rfs[]) >>
 qexists_tac ‘b’ >> fs[] >> rfs[] >>
 qsuff_tac
 ‘App(f1, x) = ctt(IMAGE(f, PREIM(i1(X, 1), x)), b0)’ 
 >-- (strip_tac >> arw[] >> rfs[] >>
     rw[App_App_o,GSYM SOME_def,GSYM Sg_Sing,PREIM_i1_Sing_SOME,
        IMAGE_Sing,ctt_Sing] >> arw[]) >>
 first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 first_x_assum irule >> fs[App_App_o,GSYM SOME_def,GSYM Sg_Sing]>>
 rw[Sing_eq_eq,SOME_eq_eq,Sing_SOME_NEQ_Ins_NONE] >>
 rpt strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[]) >>
 qexists_tac ‘a’ >> rw[]) >>
 rw[GSYM IN_EXT_iff,FIB_def,PREIM_def,IN_Sing,IMAGE_def,Whole_def]  >>
 rw[IN_EXT_iff,App_App_o,INS_def] >> rw[GSYM App_App_o] >> strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *) 
 >-- (rfs[] >> ccontra_tac >>
     qsuff_tac
     ‘App(f1,x) = b1’ 
     >-- (strip_tac >> fs[]) >>
     first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
     first_x_assum irule >> arw[] >> ccontra_tac >>
     qby_tac
     ‘ App(f1, x) = ctt(IMAGE(f, PREIM(i1(X, 1), x)), b0)’
     >-- first_x_assum irule >> arw[] >>
     fs[] >> rfs[] >> fs[] >>
     fs[PREIM_i1_Sing_SOME,IMAGE_Sing,ctt_Sing] >> rfs[]) >>
 qexists_tac ‘b0’ >> arw[] >>
 first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 rfs[] >> first_x_assum irule >> qexists_tac ‘a’ >> rw[])
(form_goal
 “∀C X i:C-> Pow(X). Inj(i) ⇒
  ∀B f:X->B bs:mem(Pow(B)) b0. 
  (∀x. ~(App(f,x) = b0)) ⇒
  ~IN(b0,bs) ⇒
  ∀b1. ~(b1 = b0) & ~IN(b1,bs) ⇒ 
  ∃f1: Pow(X+1) -> B.
  (∀b. IN(b,bs) ⇒ FIB(f1,b) = IMAGE(Sg(X+1) o i1(X,1),FIB(f,b))) & 
  FIB(f1,b0) = IMAGE(INS(NONE(X)) o Image(i1(X, 1)) o i,Whole(C)) ”)


val biunique_def = 
qdefine_psym("biunique",[‘R:A~>B’,‘s1:mem(Pow(A))’,‘s2:mem(Pow(B))’])
‘(∀a. IN(a,s1) ⇒ ?!b:mem(B). IN(b,s2) & Holds(R,a,b)) &
  (∀b. IN(b,s2) ⇒ ?!a:mem(A). IN(a,s1) & Holds(R,a,b))’
 
val SS_Ri_restrict = prove_store("SS_Ri_restrict",
e0
(rpt strip_tac >> rw[SS_def,Ri_def,restrict_def] >>
 rpt strip_tac)
(form_goal
 “∀A s1 a B R s2.  SS(App(Ri(restrict(R:A~>B, s1, s2)), a), s2)”));

val biunique_op = prove_store("biunique_op",
e0
(rpt strip_tac >> fs[biunique_def,op_def])
(form_goal
 “∀R:A~>B s1 s2. biunique(R,s1,s2) ⇒ biunique(op(R),s2,s1)”));


val biunique_Ri_restrict = prove_store("biunique_Ri_restrict",
e0
(rpt strip_tac >>
 arw[] >>
 rw[GSYM IN_EXT_iff] >> rw[Ri_def,restrict_def,op_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qsuff_tac ‘x = a'’ >-- (strip_tac >> arw[]) >>
     fs[biunique_def] >>
     first_x_assum drule >>
     pop_assum (assume_tac o uex_expand) >>
     pop_assum (x_choose_then "a0" strip_assume_tac) >>
     qsuff_tac
     ‘x = a0 & a' = a0’
     >-- (strip_tac >> arw[]) >> strip_tac >> first_x_assum irule >>
     arw[]) >>
 fs[SS_def] >> first_x_assum drule >>
 fs[biunique_def] >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘b’ >> arw[] >>
 qexists_tac ‘x’ >> arw[])
(form_goal
 “biunique(R:A~>B,s1,s2) ⇒
  ∀s. SS(s,s1) (*& SS(t,s2)*) ⇒
   App(Ri(restrict(op(R),s2,s1)),App(Ri(restrict(R,s1,s2)),s)) = s”)); 


val cardeq_biunique = cardeq_def |> rewr_rule[GSYM biunique_def]

 (*App(Ri(restrict(R, s1, s2)), App(Ri(restrict(op(R), s2, s1)), b)) = b*)



val cardeq_POW = prove_store("cardeq_POW",
e0
(rpt strip_tac >> fs[cardeq_biunique] >>
 (assume_tac o uex2ex_rule)
 (AX1 |> qspecl [‘Pow(A)’,‘Pow(B)’]
      |> fVar_sInst_th “P(s:mem(Pow(A)),t:mem(Pow(B)))”
      “SS(s,s1) & SS(t,s2) & t = App(Ri(restrict(R:A~>B,s1,s2)),s)”) >>
 pop_assum (x_choose_then "R1" assume_tac) >>
 qexists_tac ‘R1’ >>
 rw[POW_def,biunique_def] >> arw[] >> rpt strip_tac (* 2 *)
 >-- (uex_tac >>
     qexists_tac ‘App(Ri(restrict(R, s1, s2)), a)’ >>
     rw[SS_Ri_restrict] >>
     rpt strip_tac >> arw[]) >>
 uex_tac >>
 qexists_tac ‘App(Ri(restrict(op(R), s2, s1)), b)’ >>
 rw[SS_Ri_restrict] >> arw[] >>
 drule biunique_op >>
 drule biunique_Ri_restrict >>
 first_x_assum drule >> fs[op_op] >>
 rpt strip_tac  >> arw[] >>
 rev_drule biunique_Ri_restrict >>
 first_x_assum drule >> arw[] )
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

val NONE_NOTIN_IMAGE_i1 = prove_store("NONE_NOTIN_IMAGE_i1",
e0
(rpt strip_tac >> fs[IMAGE_def,Image_def,GSYM SOME_def,GSYM SOME_NOTNONE] >>
 ccontra_tac >> fs[] )
(form_goal
 “∀X s. (∀s0.IN(s0,IMAGE(Image(i1(X,1)),s)) ⇒ ~IN(NONE(X),s0))”));


val shrink_def = 
define_lambda
 “∀x. (IN(App(f0:X->B,x),s) ⇒ App(f,x) = App(f0,x)) &
      (ELSE ⇒ App(f,x) = b0)”
|> qsimple_uex_spec "shrink" [‘f0’,‘s’,‘b0’]

(*
val shrink_IMAGE_ex = prove_store("shrink_IMAGE_ex",
e0
(rpt strip_tac >>
 strip_assume_tac
 (define_lambda
 “∀x. (IN(App(f0:X->B,x),s) ⇒ App(f,x) = App(f0,x)) &
      (ELSE ⇒ App(f,x) = b0)”
 |> uex2ex_rule) >>
 qexists_tac ‘f’ >> arw[] >>
 rpt strip_tac >>
 rw[GSYM IN_EXT_iff,FIB_def,PREIM_def,IN_Sing] >>
 strip_tac >> 
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rfs[] >> qexists_tac ‘b’ >> arw[] >>
     first_x_assum (assume_tac o  GSYM) >> arw[] >>
     flip_tac >>
     first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
     first_x_assum irule >> ccontra_tac >>
     first_x_assum drule >>
     fs[]) >>
 qexists_tac ‘b’ >> arw[] >> rfs[] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 first_x_assum irule >> ccontra_tac >> first_x_assum drule >>
 fs[])
(form_goal
 “∀X B f0:X->B s:mem(Pow(B)) b0.
  ~IN(b0,s) ⇒
  ∃f: X->B. 
   (∀b. IN(b,s) ⇒ FIB(f,b) = FIB(f0,b)) &
    ∀x. ~IN(App(f0,x),s) ⇒ App(f,x) = b0”));
*)



val shrink_IMAGE = prove_store("shrink_IMAGE",
e0
(rpt gen_tac >>
 assume_tac shrink_def >> 
 rw[GSYM IN_EXT_iff,FIB_def,PREIM_def,IN_Sing] >> arw[] >>
 rpt strip_tac >> 
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rfs[] >> qexists_tac ‘b’ >> arw[] >>
     first_x_assum (assume_tac o  GSYM) >> arw[] >>
     flip_tac >>
     first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
     first_x_assum irule >> ccontra_tac >>
     first_x_assum drule >>
     fs[]) >>
 qexists_tac ‘b’ >> arw[] >> rfs[] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 first_x_assum irule >> ccontra_tac >> first_x_assum drule >>
 fs[])
(form_goal
 “∀X B f0:X->B s:mem(Pow(B)) b0.
  ~IN(b0,s) ⇒
   (∀b. IN(b,s) ⇒ FIB(shrink(f0,s,b0),b) = FIB(f0,b)) &
    ∀x. ~IN(App(f0,x),s) ⇒ App(shrink(f0,s,b0),x) = b0”));

val nPow_shrink_IMAGE_ex = prove_store("nPow_shrink_IMAGE_ex",
e0
(rpt strip_tac >>
 fs[nPow_def] >>
 strip_assume_tac
 (IN_def_P_ex |> qspecl [‘N’] 
 |> fVar_sInst_th “P(n0:mem(N))” “Le(n0,n)”
 |> GSYM) >>
 qsspecl_then [‘f’,‘s’,‘Suc(Suc(n))’] strip_assume_tac 
 shrink_IMAGE >>
 rfs[] >>
 fs[NOT_LESS_EQ] >>
 qby_tac
 ‘Lt(n, Suc(Suc(n)))’
 >-- (irule Lt_trans >> qexists_tac ‘Suc(n)’ >> rw[Lt_Suc]) >>
 first_x_assum drule >>
 qexistsl_tac [‘X’,‘shrink(f,s,Suc(Suc(n)))’] >>
 pop_assum strip_assume_tac >> 
 rpt strip_tac (* 4 *)
 >-- (first_x_assum (qspecl_then [‘O’] assume_tac) >>
     fs[O_LESS_EQ])
 >-- (first_x_assum (qspecl_then [‘n’] assume_tac) >>
     fs[Le_refl]) 
 >-- (qby_tac ‘Le(Suc(n0),n)’ 
     >-- fs[Lt_Le_Suc] >>
     first_assum drule >>
     drule Lt_Le >> first_assum drule >> fs[] >>
     first_assum irule >> arw[]) >>
 qsspecl_then [‘Suc(Suc(n))’,‘s’,‘f’,‘x’]
 strip_assume_tac (shrink_def |> gen_all) >>
 rfs[] >>
 qcases ‘Le(App(f, x), n)’  (* 2 *)
 >-- (first_x_assum drule >> arw[] >> ccontra_tac >> fs[] >>
     fs[GSYM Lt_Le_Suc,Lt_def]) >>
 first_x_assum drule >>
 arw[] >> rw[GSYM Suc_NEQ] )
(form_goal
 “nPow(n,A,An) ⇒ 
  ?X f:X->N. cardeq(FIB(f,O),Whole(A)) & 
            cardeq(FIB(f,n),Whole(An)) &
  (!n0. Lt(n0,n) ==>
   cardeq(POW(FIB(f,n0)),FIB(f,Suc(n0)))) &
  ∀x. ~(App(f,x) = Suc(n))”));





val nPow_Suc = prove_store("nPow_Suc",
e0
(rpt strip_tac >>
 rw[nPow_def] >> rw[Lt_Suc_Le] >> 
 drule nPow_shrink_IMAGE_ex >> 
 pop_assum strip_assume_tac >> 
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
 rfs[] >> 
 first_x_assum drule >>
 first_x_assum (qspecl_then [‘Suc(Suc(n))’] assume_tac) >>
 fs[Suc_eq_eq,GSYM Suc_NEQ] >>
 qby_tac
 ‘~Le(Suc(Suc(n)), n)’
 >-- (rw[NOT_LESS_EQ] >>
     irule Lt_trans >> qexists_tac ‘Suc(n)’ >> rw[Lt_Suc]) >>
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
 >-- (irule cardeq_SYM >> irule IMAGE_INJ_cardeq >>
      qexistsl_tac [‘Whole(Pow(An))’,‘Whole(Pow(X + 1))’] >>
      rw[SS_Refl] >> irule o_INJ_INJ >>
      qexists_tac ‘IMAGE(Image(i1(X, 1)) o Image(i),Whole(Pow(An)))’ >>
      strip_tac (* 2 *)
      >-- (rw[IMAGE_o] >> 
          qspecl_then 
          [‘X’,‘IMAGE(Image(i), Whole(Pow(An)))’] assume_tac 
          NONE_NOTIN_IMAGE_i1 >>
          drule INJ_INS_NONE >>
          irule INJ_SS_cod >> 
          qexists_tac ‘IMAGE(INS(NONE(X)),
                    IMAGE(Image(i1(X, 1)), IMAGE(Image(i), Whole(Pow(An)))))’>>
          arw[SS_def,Whole_def]) >>
      irule Inj_INJ >> irule o_Inj_Inj >> arw[] >>
      irule Inj_Image >> rw[i1_Inj]) >> arw[] >>
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




val nPow_ex = prove_store("nPow_ex",
e0
(strip_tac >> Nind_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘A’ >> rw[nPow_O]) >>
 qexists_tac ‘Pow(An)’ >>
 drule nPow_Suc>> arw[] )
(form_goal “!A n. ?An. nPow(n,A,An)”));

val nPowf_def = 
qdefine_psym("nPowf",[‘n:mem(N)’,‘A’,‘B’,‘f:X->N’])
‘cardeq(FIB(f,O),Whole(A)) & 
            cardeq(FIB(f,n),Whole(B)) &
  (!n0. Lt(n0,n) ==>
   cardeq(POW(FIB(f,n0)),FIB(f,Suc(n0))))’ |> gen_all

val m2s_def = 
Thm_2_4' |> qspecl [‘A’] 
         |> fVar_sInst_th “P(a:mem(A))” “IN(a,s:mem(Pow(A)))” 
         |> set_spec (rastt "A") "m2s" "minc" 
         [("s",mem_sort (rastt "Pow(A)"))]


val cardeq_m2s = prove_store("cardeq_m2s",
e0
(cheat)
(form_goal
 “∀A s:mem(Pow(A)). cardeq(s,Whole(m2s(s)))”));

val nPowf_Preds = prove_store("nPowf_Preds",
e0
(strip_tac >> 
 rpt gen_tac >> disch_tac >>
 Nind_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘A’ >> fs[nPowf_def,NOT_Lt_O]) >>
 qby_tac ‘Le(n',n)’ 
 >-- (irule Le_trans >> qexists_tac ‘Suc(n')’ >> arw[] >>
     irule Lt_Le >> rw[Lt_Suc]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 fs[nPowf_def] >> 
 qexists_tac ‘m2s(FIB(f,Suc(n')))’ >> rw[cardeq_m2s] >>
 rpt strip_tac >>
 last_x_assum irule >> irule Lt_Le_Lt >>
 qexists_tac ‘Suc(n')’ >> arw[])
(form_goal
 “∀A n B f:X->N. nPowf(n,A,B,f) ⇒
   ∀n0. Le(n0,n) ⇒ ∃B0. nPowf(n0,A,B0,f)”));


val nPowf_Preds_FIB = prove_store("nPowf_Preds_FIB",
e0
(strip_tac >> 
 rpt gen_tac >> disch_tac >>
 Nind_tac >> rpt strip_tac (* 2 *)
 >-- (cheat) >>
 qby_tac ‘Le(n',n)’ 
 >-- (irule Le_trans >> qexists_tac ‘Suc(n')’ >> arw[] >>
     irule Lt_Le >> rw[Lt_Suc]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 fs[nPowf_def] >> rw[cardeq_m2s] >>
 rpt strip_tac >>
 last_x_assum irule >> irule Lt_Le_Lt >>
 qexists_tac ‘Suc(n')’ >> arw[])
(form_goal
 “∀A n B f:X->N. nPowf(n,A,B,f) ⇒
   ∀n0. Le(n0,n) ⇒ nPowf(n0,A,m2s(FIB(f,n0)),f)”));

val nPow_nPowf = prove_store("nPow_nPowf",
e0
(rpt strip_tac >> rw[nPow_def,nPowf_def] )
(form_goal
 “∀A n B. nPow(n,A,B) ⇔ ∃X f:X->N.nPowf(n,A,B,f)”));

val nPow_unique = prove_store("nPow_unique",
e0
(strip_tac >>
 Nind_tac >> rpt strip_tac (* 2 *)
 >-- (fs[nPow_def] >>
     irule cardeq_TRANS >> qexistsl_tac [‘A’,‘Whole(A)’] >>
     strip_tac (* 2 *)
     >-- (irule cardeq_TRANS >> qexistsl_tac [‘X'’,‘FIB(f',O)’] >> 
         arw[] >> irule cardeq_SYM >> arw[]) >>
     irule cardeq_TRANS >> qexistsl_tac [‘X’,‘FIB(f,O)’] >> 
     arw[] >> irule cardeq_SYM >> arw[]) >>
 drule $ iffLR nPow_nPowf >>
 pop_assum strip_assume_tac >>
 rev_drule $ iffLR nPow_nPowf >>
 pop_assum strip_assume_tac >>
 rev_drule nPowf_Preds >>
 drule nPowf_Preds >>
 last_x_assum (qspecl_then [‘n’] assume_tac) >> fs[LESS_EQ_SUC] >>
  last_x_assum (qspecl_then [‘n’] assume_tac) >> fs[LESS_EQ_SUC] >> 
 qspecl_then [‘A’,‘An1’,‘X'’,‘f'’,‘Suc(n)’] assume_tac nPowf_def >>
 qspecl_then [‘A’,‘An2’,‘X’,‘f’,‘Suc(n)’] assume_tac nPowf_def >> rfs[] >>
 qsuff_tac
 ‘cardeq(FIB(f', Suc(n)),FIB(f, Suc(n)))’
 >-- (strip_tac >>
     irule $ iffLR cardeq_BITRANS >>
     qexistsl_tac [‘X'’,‘FIB(f', Suc(n))’,‘X’,‘FIB(f, Suc(n))’] >> arw[]) >>
 qsuff_tac
 ‘cardeq(POW(FIB(f',n)),POW(FIB(f,n)))’
 >-- (strip_tac >>
     irule $ iffLR cardeq_BITRANS >>
     qexistsl_tac [‘Pow(X')’,‘POW(FIB(f', n))’,
                   ‘Pow(X)’,‘POW(FIB(f, n))’] >> arw[] >> strip_tac >> 
     first_x_assum irule >> rw[Lt_Suc]) >>
 irule cardeq_POW >>  
 qsuff_tac
 ‘cardeq(Whole(m2s(FIB(f',n))),Whole(m2s(FIB(f,n))))’
 >-- (rpt strip_tac >> irule $ iffLR cardeq_BITRANS >>
     qexistsl_tac [‘m2s(FIB(f',n))’,‘Whole(m2s(FIB(f',n)))’,
                   ‘m2s(FIB(f,n))’,‘Whole(m2s(FIB(f,n)))’] >>
      arw[] >> strip_tac >> irule cardeq_SYM >> rw[cardeq_m2s]) >>
 first_x_assum irule >>
 strip_tac (* 2 *)
 >-- (rw[nPow_nPowf] >> qexistsl_tac [‘X'’,‘f'’] >>
     irule nPowf_Preds_FIB >> qexistsl_tac [‘B0'’,‘n’] >>
     arw[Le_refl]) >>
 rw[nPow_nPowf] >> qexistsl_tac [‘X’,‘f’] >>
  irule nPowf_Preds_FIB >> qexistsl_tac [‘B0’,‘n’] >> arw[Le_refl] )
(form_goal
 “∀A n An1 An2. nPow(n,A,An1) & nPow(n,A,An2) ⇒ cardeq(Whole(An1),Whole(An2))”));

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


