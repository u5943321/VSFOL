

val Ins_ex = 
fVar_Inst 
[("P",([("x",mem_sort (mk_set "X"))],
“x:mem(X) = x0 | IN(x,s0)”))] 
(IN_def_P_expand |> qspecl [‘X’]) |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
|> store_as "Ins_ex";


val Ins_def = Ins_ex |> spec_all |> ex2fsym0 "Ins" ["x0","s0"]
                     |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
                     |> store_as "Ins_def";

val Ins_property = Ins_def |> spec_all |> conjE1
                           |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
                           |> store_as "Ins_property";


val Empty_ex = 
fVar_Inst 
[("P",([("x",mem_sort (mk_set "X"))],
“F”))] 
(IN_def_P_expand |> qspecl [‘X’]) |> gen_all
|> store_as "Empty_ex";

val Empty_def = Empty_ex |> spec_all |> ex2fsym0 "Empty" ["X"] 
                         |> gen_all |> store_as "Empty_def";

val Empty_property = Empty_def |> spec_all |> conjE1 |> GSYM 
                               |> gen_all |> store_as "Empty_property";


val cFins_ex = 
fVar_Inst 
[("P",([("xss",mem_sort $ Pow $Pow (mk_set "X"))],
“IN(Empty(X),xss) & !xs0. IN(xs0,xss) ==> !x0. IN(Ins(x0,xs0),xss)”))] 
(IN_def_P_expand |> qspecl [‘Pow(Pow(X))’]) |> gen_all
|> store_as "cFins_ex";

val cFins_def =  cFins_ex |> spec_all |> ex2fsym0 "cFins" ["X"]
                       |> gen_all
                       |> store_as "cFins_def";

val cFins_property = cFins_def |> spec_all |> conjE1
                             |> gen_all |> store_as "cFins_property";   

val Fin_lemma = 
fVar_Inst 
[("P",([("xs",mem_sort $ Pow (mk_set "X"))],
“IN(xs,Eval(BI(Pow(X)),cFins(X)))”))]
(Thm_2_4 |> qspecl [‘Pow(X)’]) |> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all BI_property) 
|>conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all $ GSYM cFins_property) 
|> ex2fsym0 "Fins" ["X"] |> ex2fsym0 "FI" ["X"]


val Fin_lemma' = Fin_lemma |> conjE2 |> iffRL
                       |> allE (rastt "Eval(FI(X),b)")
                       |> C mp
                       (existsI ("b'",mem_sort (rastt "Fins(X)")) (rastt "b:mem(Fins(X))")
                                “Eval(FI(X), b) = Eval(FI(X), b')”
                                (refl (rastt "Eval(FI(X), b)")))
                       |> strip_all_and_imp
                       |> gen_all
                       |> disch_all
                       |> gen_all


val _ = new_pred "Fin" [("A",mem_sort $ Pow (mk_set "X"))]

val Fin_def = store_ax("Fin_def",
“!X A:mem(Pow(X)). Fin(A) <=> ?b:mem(Fins(X)). A = Eval(FI(X),b)”)

val Fin_property = prove_store("Fin_property",
e0
(rw[Fin_def] >> once_rw[GSYM Fin_lemma] >> rpt strip_tac >> 
 first_assum irule >> first_assum irule >> arw[])
(form_goal
 “!X. Fin(Empty(X)) & !A:mem(Pow(X)). Fin(A) ==> !x. Fin(Ins(x,A))”));

val Fin_ind = prove_store("Fin_ind",
e0
(strip_tac >> strip_tac >> disch_tac >> drule Fin_lemma' >>
 rw[Fin_def] >> rpt strip_tac >> arw[])
(form_goal
 “!X ss. (IN(Empty(X),ss) & 
  !xs0. IN(xs0,ss) ==> !x0. IN(Ins(x0,xs0),ss)) ==>
  !A. Fin(A) ==> IN(A,ss)”));


local
val l0 = 
(IN_def_P_expand |> qspecl [‘Pow(X)’]) 
in
val Fin_ind_P = prove_store("Fin_ind_P",
e0
(rpt strip_tac >> strip_assume_tac l0 >> pop_assum (K all_tac) >>
 qsuff_tac ‘IN(A,s)’
 >-- (strip_tac >> first_assum (qspecl_then [‘A’] assume_tac) >>
      accept_tac (dimp_mp_r2l (assume “P(A:mem(Pow(X))) <=> IN(A, s)”)
                              (assume “IN(A:mem(Pow(X)), s)”))) >>
 irule Fin_ind >> strip_tac (* 2 *)
 >-- first_assum accept_tac >>
 strip_tac >-- (first_assum (irule o iffLR) >> first_assum accept_tac) >>
 rpt strip_tac >> first_assum (irule o iffLR) >> 
 qsuff_tac ‘!x0. P(Ins(x0,xs0))’
 >-- (strip_tac >> first_assum (qspecl_then [‘x0’] accept_tac)) >>
 first_assum irule >> first_assum (irule o iffRL) >>
 first_assum accept_tac)
(form_goal
 “!X.(P(Empty(X)) & !xs0:mem(Pow(X)). P(xs0) ==> !x0. P(Ins(x0,xs0))) ==> 
  !A:mem(Pow(X)). Fin(A) ==> P(A)”));


(*union is finite <=> A and B are finite*)

end
