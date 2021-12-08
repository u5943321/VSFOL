
val lemma = 
 


(*

[1,2]


{(0,1),(1,2)}


[2,1]


{(0,2),(1,1)}


N -> (A + 1)


eq_psym


a = c & b = d
---------
P(a,b) <=> P(c,d)




fun eq_Pred p  = 



?P




()

*)



val lemma = 
fVar_Inst 
[("P",([("sets",mem_sort$ Pow $ Pow $ Cross N (mk_set "A"))],
“IN(Empty(N * A),sets:mem(Pow(Pow(N * A)))) & 
 !l. IN(l,sets) ==> !a:mem(A).IN(Ins(Pair(Card(l),a),l),sets)”))] 
(IN_def_P_expand |> qspecl [‘Pow(Pow(N * A))’]) 

(*make Ins Pair as Cons0 *)

(*set of subsets of that contains the set of lists*)
val As_def = lemma |> ex2fsym0 "As" ["A"] |> conjE1 
                   |> gen_all |> GSYM



val U_ex_lemma = fVar_Inst 
[("P",([("ls",mem_sort $ Pow $ Cross N (mk_set "A"))],
“IN(ls,BIGINTER(As(A)))”))]
(Thm_2_4 |> qspecl [‘(Pow(N * A))’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all IN_BIGINTER)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all As_def)




(*f:A->B. is inj, then ?g:B->A. g o f = id(A).
  
have this function. 


*)

val U_i_def = U_ex_lemma |> ex2fsym0 "U" ["A"] |>ex2fsym0 "i" ["A"]



val IN_U = U_i_def |> conjE2 |> gen_all |> 
conv_rule $ basic_once_fconv no_conv (rewr_fconv (eq_sym "mem"))
|> GSYM


val List0 = IN_U  |> allE (rastt "A") |>  allE (rastt "Eval(i(A),b)")
                       |> dimp_mp_l2r
                       (existsI ("b'",mem_sort (rastt "U(A)")) 
                                (rastt "b:mem(U(A))")
                                “Eval(i(A), b') = Eval(i(A), b)”
                                (refl (rastt "Eval(i(A), b)")))
                       |> gen_all
                       |> disch_all
                       |> gen_all

val List_lemma = prove_store("List_lemma",
e0
()
(form_goal
 “!A b. ”));


val _ = new_pred "hasCard" [("xs",mem_sort $Pow (mk_set "X")),("n",mem_sort N)]
val hasCard_def = store_ax("hasCard_def",
“!X xs:mem(Pow(X)) n.hasCard(xs,n) <=> Holds(Card(X),xs,n)”)

val Card_def' = Card_lemma |> rewr_rule[GSYM hasCard_def]
