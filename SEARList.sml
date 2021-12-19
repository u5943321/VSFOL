


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


(*exists a set of "sets of sets of  pairs (n,a)"
  (each member of such set is a subset of Pow(N * A), so each such set is  an element of Pow(Pow(N * A)))
  which satisfies the condition that
  {} is in the set, and ... *)

val lemma = 
fVar_Inst 
[("P",([("sets",mem_sort$ Pow $ Pow $ Cross N (mk_set "A"))],
“IN(Empty(N * A),sets:mem(Pow(Pow(N * A)))) & 
 !l. IN(l,sets) ==> !a:mem(A).IN(Ins(Pair(CARD(l),a),l),sets)”))] 
(IN_def_P_expand |> qspecl [‘Pow(Pow(N * A))’]) 

(*make Ins Pair as Cons0 *)

(*set of subsets of that contains the set of lists*)
val As_def = lemma |> ex2fsym0 "As" ["A"] |> conjE1 
                   |> gen_all |> GSYM



val List_ex_lemma = fVar_Inst 
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

val List_LI_def = List_ex_lemma |> ex2fsym0 "List" ["A"] |>ex2fsym0 "LI" ["A"]

val LI_Inj = conjE1 List_LI_def |> gen_all |> store_as "LI_Inj";

val LI_Fun = LI_Inj |> rewr_rule[Inj_def] |> spec_all |> conjE1
                    |> gen_all |> store_as "LI_Fun";


val IN_List = List_LI_def |> conjE2 |> gen_all |> 
conv_rule $ basic_once_fconv no_conv (rewr_fconv (eq_sym "mem"))
|> GSYM


val List_ind0 = IN_List |> allE (rastt "A") |>  allE (rastt "Eval(LI(A),b)")
                       |> dimp_mp_l2r
                       (existsI ("b'",mem_sort (rastt "List(A)")) 
                                (rastt "b:mem(List(A))")
                                “Eval(LI(A), b') = Eval(LI(A), b)”
                                (refl (rastt "Eval(LI(A), b)")))
                       |> strip_all_and_imp
                       |> gen_all
                       |> disch_all
                       |> gen_all


val isList_Empty = prove_store("isList_Empty",
e0
(strip_tac >> rw[IN_List] >>
 rpt strip_tac >> arw[])
(form_goal
 “!A. ?e. Eval(LI(A),e) = Empty(N * A)”));

val Nil_def = isList_Empty |> spec_all |> ex2fsym0 "Nil" ["A"]
                           |> gen_all
                           |> store_as "Nil_def";

val isList_cons = prove_store("isList_cons",
e0
(rw[IN_List] >> rpt strip_tac >>
 first_assum irule >> last_x_assum irule >> arw[])
(form_goal
 “!A l. (?l0.Eval(LI(A),l0) = l) ==> !a.?al.Eval(LI(A),al) = Ins(Pair(CARD(l),a),l)”));

(*set of list, takes a list, gives a ser of pairs*)

val sof_ex = prove_store("sof_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(LI(A),l)’ >> rw[])
(form_goal
 “!A l. ?ss. Eval(LI(A),l) = ss”));
 
val sof_def = sof_ex |> spec_all |> ex2fsym0 "sof" ["l"]
                     |> gen_all |> store_as "sof_def"; 

val Inj_eq = Inj_def |> iffLR |> spec_all |> undisch |> conjE2
                     |> disch_all |> gen_all
                     |> store_as "Inj_eq";

local
val l = 
fVar_Inst 
[("P",([("a0l0",mem_sort $ Cross (mk_set "A") (rastt "List(A)")),
        ("l",mem_sort (rastt "List(A)"))],
“Ins(Pair(CARD(sof(Snd(a0l0))), Fst(a0l0:mem(A * List(A)))),sof(Snd(a0l0))) = sof(l)”))]
(AX1 |> qspecl [‘A * List(A)’,‘List(A)’])
|> uex_expand  
in
val Cons_ex = prove_store("Cons_ex",
e0
(strip_tac >> strip_assume_tac l >>
 pop_assum (K all_tac) >> qexists_tac ‘R’ >>
 arw[Pair_def'] >> rw[Fun_expand] >>
 arw[] >> rpt strip_tac (* 2 *)
 >-- (assume_tac isList_cons >>
     fs[sof_def] >> 
     pop_assum (qsspecl_then [‘sof(Snd(a))’] assume_tac) >>
     qby_tac
     ‘(?l0 : mem(List(A)). sof(l0) = sof(Snd(a)))’ 
     >-- (qexists_tac ‘Snd(a)’ >> rw[]) >>
     first_x_assum drule >> 
     first_x_assum (qspecl_then [‘Fst(a)’] assume_tac) >>
     pop_assum strip_assume_tac >> qexists_tac ‘al’ >> arw[]) >>
 irule Inj_eq >> 
 qexistsl_tac [‘Pow(N * A)’,‘LI(A)’] >> 
 rw[LI_Inj] >> rw[sof_def] >>
 pop_assum_list (map_every (assume_tac o GSYM)) >> arw[])
(form_goal
 “!A. ?cons:A * List(A) -> List(A).
  isFun(cons) & 
  (!a0 l0 l. Holds(cons,Pair(a0,l0),l) <=> 
  Ins(Pair(CARD(sof(l0)), a0),sof(l0)) = sof(l))”));
end

val Cons_def = Cons_ex |> spec_all |> ex2fsym0 "Cons" ["A"]
                       |> gen_all |> store_as "Cons_def";


val CONS_ex = prove_store("CONS_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(Cons(A),Pair(a0,l0))’ >> rw[])
(form_goal
 “!A a0 l0. ?l.Eval(Cons(A),Pair(a0,l0)) = l”));

val CONS_def = CONS_ex |> spec_all |> ex2fsym0 "CONS" ["a0","l0"]
                       |> gen_all |> store_as "CONS_def";

val Eval_Cons = prove_store("Eval_Cons",
e0
(rpt strip_tac >>
 assume_tac Cons_def >> 
 first_x_assum (qspecl_then [‘A’] strip_assume_tac) >>
 drule $ GSYM Eval_def >> flip_tac >>
 arw[] >> lflip_tac >> rw[])
(form_goal
 “!A a0 l0 l. Eval(Cons(A), Pair(a0,l0)) = l <=> 
  Ins(Pair(CARD(sof(l0)),a0),sof(l0)) = sof(l)”));

val Cons_eqn = prove_store("Cons_eqn",
e0
(rpt strip_tac >>
 qsspecl_then [‘a0’,‘l0’,‘Eval(Cons(A), Pair(a0,l0))’] assume_tac
 Eval_Cons >> fs[])
(form_goal
 “!A a0 l0. Ins(Pair(CARD(sof(l0)),a0),sof(l0)) = sof(Eval(Cons(A), Pair(a0,l0)))”));

val CONS_eqn = Cons_eqn |> rewr_rule[CONS_def]
                        |> store_as "CONS_eqn";

val sof_Nil = Nil_def |> rewr_rule[sof_def] |> store_as "sof_Nil";

val CONS_NOTNIL = prove_store("CONS_NOTNIL",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac ‘sof(CONS(a,l)) = sof(Nil(A))’ >-- arw[] >>
 fs[GSYM CONS_eqn,sof_Nil,Ins_NONEMPTY])
(form_goal
 “!A a l. ~(CONS(a,l) = Nil(A))”));

val sof_eq_eq = prove_store("sof_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 fs[GSYM sof_def] >> irule Inj_eq >>
 qexistsl_tac [‘Pow(N * A)’,‘LI(A)’] >> arw[LI_Inj] )
(form_goal
 “!A l1:mem(List(A)) l2.sof(l1) = sof(l2) <=> l1 = l2”));

local
val l = 
 fVar_Inst 
[("P",([("nas",mem_sort$ Pow $ Cross N (mk_set "A"))],
“?l:mem(List(A)). P(l) & sof(l) = nas”))] 
(IN_def_P_expand |> qspecl [‘Pow(N * A)’]) 
in
val List_ind = prove_store("List_ind",
e0
(assume_tac List_ind0 >>
 rpt strip_tac >>
 qby_tac
 ‘?ss. !nas. IN(nas,ss) <=> ?l:mem(List(A)). P(l) & sof(l) = nas’
 >-- (strip_assume_tac l >> pop_assum (K all_tac) >>
     qexists_tac ‘s’ >> strip_tac >> pop_assum (assume_tac o GSYM) >>
     first_x_assum (qspecl_then [‘nas’] accept_tac)) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘!b. IN(Eval(LI(A),b),ss)’
 >-- (rpt strip_tac >> 
     first_x_assum (qspecl_then [‘l’] assume_tac) >>
     first_x_assum $ drule o iffLR >>
     pop_assum strip_assume_tac >>
     pop_assum mp_tac >> once_rw[sof_def] >> once_rw[sof_eq_eq] >>
     strip_tac >> 
     assume_tac (EQ_fVar "P" [assume “l' = l:mem(List(A))”]) >>
     first_x_assum $ irule o iffLR >> 
     first_x_assum accept_tac) >>
 (*first_x_assum irule gives err wrong concl*)
 last_x_assum irule >> rpt strip_tac (* 2 *)
 >-- (first_assum $ drule o iffLR >> pop_assum strip_assume_tac >>
     last_assum drule >> 
     first_assum $ irule o iffRL >>
     qexists_tac ‘CONS(a',l'')’ >> strip_tac
     >-- first_assum (qspecl_then [‘a'’] accept_tac) >>
     qsuff_tac
     ‘sof(CONS(a', l'')) = Ins(Pair(CARD(sof(l'')), a'), sof(l''))’
     >-- (qpick_x_assum ‘sof(l'') = l'’ (mp_tac o GSYM) >>
         pop_assum_list (map_every (K all_tac)) >> rpt strip_tac >>
         arw[]) >>
     once_rw[CONS_eqn]  >> rw[]) >>
 first_assum $ irule o iffRL >>
 qexists_tac ‘Nil(A)’ >> strip_tac 
 >-- first_assum accept_tac >>
 once_rw[GSYM Nil_def] >> rw[sof_def]
 )
(form_goal
 “!A. P(Nil(A)) & 
      (!l:mem(List(A)). P(l) ==> !a. P(CONS(a,l))) ==>
     !l:mem(List(A)).P(l) ”));
end




local 
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“Fin(sof(l:mem(List(A))))”))] 
(List_ind |> qspecl [‘A’]) 
in
val LI_Fin = prove_store("LI_Fin",
e0
(strip_tac >> match_mp_tac l >>
 rw[sof_Nil,Fin_Empty] >> rpt strip_tac >>
 rw[GSYM CONS_eqn] >> drule Fin_Ins >> arw[])
(form_goal
 “!A l:mem(List(A)). Fin(sof(l))”));
end


local
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“!n a:mem(A). IN(Pair(n,a),sof(l)) ==> Lt(n,CARD(sof(l)))”))] 
(List_ind |> qspecl [‘A’])
in
val isList_CARD_NOTIN0 = prove_store("isList_CARD_NOTIN0",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> match_mp_tac l >>
 rpt strip_tac (* 2 *)
 >-- fs[sof_Nil,Empty_property] >>
 fs[GSYM CONS_eqn,IN_Ins] (* 2 *)
 >-- (fs[Pair_eq_eq] >> 
     qby_tac ‘~IN(Pair(CARD(sof(l')), a'),sof(l'))’ 
     >-- (ccontra_tac >> first_x_assum drule  >>
         fs[Lt_def]) >>
     qsspecl_then [‘l'’] assume_tac LI_Fin >>
     drule CARD_Ins >> first_x_assum drule >> 
     arw[] >> rw[Lt_Suc]) >>
 first_x_assum drule >> 
 cases_on “IN(Pair(CARD(sof(l')), a':mem(A)),sof(l'))” 
 >-- (drule Ins_absorb >> arw[]) >>
 qsspecl_then [‘l'’] assume_tac LI_Fin >>
 drule CARD_Ins >> first_x_assum drule >> arw[] >>
 irule Lt_trans >>
 qexists_tac ‘CARD(sof(l'))’ >> arw[Lt_Suc])
(form_goal
 “!A l n a:mem(A). IN(Pair(n,a),sof(l)) ==> Lt(n,CARD(sof(l)))”));
end


val Cons_Inj = prove_store("Cons_Inj",
e0
(strip_tac >> rw[Inj_def,Cons_def] >> 
 rpt strip_tac >>
 qsspecl_then [‘x1’]
 (x_choosel_then ["a1","l1"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘x2’] 
 (x_choosel_then ["a2","l2"] assume_tac) Pair_has_comp >>
 fs[] >> fs[CONS_def] >> 
 qby_tac
 ‘sof(CONS(a1, l1)) = sof(CONS(a2, l2))’
 >-- arw[] >>
 fs[GSYM CONS_eqn] >>
 qsuff_tac
 ‘Pair(CARD(sof(l1)), a1) = Pair(CARD(sof(l2)), a2) & 
  sof(l1) = sof(l2)’
 >-- (rw[Pair_eq_eq,sof_eq_eq] >> rpt strip_tac >> arw[]) >>
 irule Ins_eq_eq >>
 arw[] >>
 qby_tac
 ‘~IN(Pair(CARD(sof(l1)), a1), sof(l1))’
 >-- (ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def]) >>
 qby_tac
 ‘~IN(Pair(CARD(sof(l2)), a2), sof(l2))’
 >-- (ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def]) >>
 arw[] >>
 qby_tac ‘CARD(sof(l2)) = CARD(sof(l1))’ 
 >-- (drule $ GSYM Del_Ins >> rev_drule $ GSYM Del_Ins >>  
     once_arw[] >> pop_assum (K all_tac) >>
     pop_assum (K all_tac) >>
     qsspecl_then [‘l2’] assume_tac LI_Fin >>
     drule CARD_Ins >>
     first_x_assum drule >> 
     drule Fin_Ins >>
     first_x_assum (qspecl_then [‘Pair(CARD(sof(l2)), a2)’] assume_tac)>>
     drule CARD_Del >>
     first_x_assum (qspecl_then [‘Pair(CARD(sof(l2)), a2)’] assume_tac) >>
     pop_assum mp_tac >> rw[IN_Ins] >>
     strip_tac >> 
     qsuff_tac
     ‘Pre(CARD(Ins(Pair(CARD(sof(l2)), a2), sof(l2)))) = 
      CARD(Del(Ins(Pair(CARD(sof(l1)), a1), sof(l1)),
                 Pair(CARD(sof(l1)), a1)))’
     >-- (strip_tac >> arw[]) >>
     pop_assum (K all_tac) >> pop_assum (K all_tac) >>
     pop_assum (K all_tac) >> pop_assum (K all_tac) >>
     qsspecl_then [‘l1’] assume_tac LI_Fin >>
     drule CARD_Ins >> 
     first_x_assum drule >>
     drule Fin_Ins >>
     first_x_assum (qspecl_then [‘Pair(CARD(sof(l1)), a1)’] assume_tac)>>
     drule CARD_Del >>
     first_x_assum (qspecl_then [‘Pair(CARD(sof(l1)), a1)’] assume_tac) >>
     pop_assum mp_tac >> rw[IN_Ins] >>
     strip_tac >> once_arw[] >>
     qpick_x_assum
     ‘Ins(Pair(CARD(sof(l1)), a1), sof(l1)) =
               Ins(Pair(CARD(sof(l2)), a2), sof(l2))’ mp_tac >>
     pop_assum_list (map_every (K all_tac)) >>
     strip_tac >> arw[]) >>
 strip_tac (* 2 *)
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def]) >>
 arw[] >> ccontra_tac >> drule isList_CARD_NOTIN0 >> fs[Lt_def]
 )
(form_goal
 “!A. isInj(Cons(A))”));


val CONS_eq_eq = prove_store("CONS_eq_eq",
e0
(rw[GSYM CONS_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 irule $ iffLR Pair_eq_eq >>
 irule Inj_eq >>
 qexistsl_tac [‘List(A)’,‘Cons(A)’] >> arw[Cons_Inj])
(form_goal
 “!A a1:mem(A) l1 a2 l2.CONS(a1,l1) = CONS(a2,l2) <=> (a1 = a2 & l1 = l2)”));




local
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“l = Nil(A) | ?a0 l0. l = CONS(a0, l0)”))] 
(List_ind |> qspecl [‘A’])
in
val CONS_or_Nil = prove_store("CONS_or_Nil",
e0
(strip_tac >> irule l >> rw[] >>
 rpt strip_tac >--
 (rw[CONS_NOTNIL] >> qexistsl_tac [‘a’,‘l'’] >> rw[]) >>
 rw[CONS_NOTNIL] >> 
 qexistsl_tac [‘a’,‘l'’] >> arw[])
(form_goal
 “!A l:mem(List(A)). l = Nil(A) | ?a0 l0. l = CONS(a0,l0)”));
end

local
val l = 
 fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)"))],
“Eval(f1:List(A) ->X, l) = Eval(f2, l)”))] 
(List_ind |> qspecl [‘A’])
in
val from_List_eq = prove_store("from_List_eq",
e0
(rpt strip_tac >> irule $ iffRL FUN_EXT >> arw[] >>
 irule l >> arw[])
(form_goal
 “!A X f1:List(A) ->X f2. isFun(f1) & isFun(f2) &
 Eval(f1, Nil(A)) = Eval(f2,Nil(A)) &
 (!l. Eval(f1,l) = Eval(f2,l) ==> 
  !a. Eval(f1,CONS(a,l)) = Eval(f2,CONS(a,l))) ==> f1 = f2”));
end



val cRf_def = 
fVar_Inst 
[("P",([("ss",mem_sort$ Pow $ Cross (rastt "List(A)") (mk_set "X"))],
“IN(Pair(Nil(A),x:mem(X)),ss)& 
 !l x. IN(Pair(l,x),ss) ==> 
    !a:mem(A).IN(Pair(CONS(a,l),Eval(t,Pair(a,x))),ss)”))] 
(IN_def_P_expand |> qspecl [‘Pow(List(A) * X)’]) 
|> ex2fsym0 "cRf" ["x","t"] |> conjE1 
|> qgen ‘t’ |> qgen ‘A’
|> gen_all |> GSYM

local
val Rf0_ex = 
fVar_Inst 
[("P",([("lx",mem_sort $ Cross (rastt "List(A)") (mk_set "X"))],
“IN(lx,BIGINTER(cRf(x:mem(X),t:A * X->X)))”))]
(Thm_2_4 |> qspecl [‘List(A) * X’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all IN_BIGINTER)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all cRf_def) |> GSYM
val R = 
fVar_Inst 
[("P",([("l",mem_sort (rastt "List(A)")),("x",mem_sort (mk_set "X"))],
“?r.Eval(i:B-> List(A) * X,r) = Pair(l,x)”))]
(AX1 |> qspecl [‘List(A)’,‘X’]) |> uex_expand
val ss = fVar_Inst 
[("P",([("lx",mem_sort $ Cross (rastt "List(A)") (mk_set "X"))],
“Holds(P:List(A) ->X,Fst(lx),Snd(lx))”))] 
(IN_def_P_expand |> qspecl [‘List(A) * X’]) 
in
val Rf_ex = prove_store("Rf_ex",
e0
(rpt strip_tac >> strip_assume_tac Rf0_ex >>
 strip_assume_tac R >>
 pop_assum (K all_tac) >>
 qexists_tac ‘R’ >>
 strip_tac (* 2 *)
 >-- (arw[] >> flip_tac >> arw[] >>
     rpt strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (arw[] >> flip_tac >> arw[] >> rpt strip_tac >>
     first_assum irule >> first_assum irule >> arw[]) >>
 arw[] >> flip_tac >>
 arw[] >> rpt strip_tac >>
 strip_assume_tac ss >> pop_assum (K all_tac) >>
 first_x_assum (qspecl_then [‘s’] assume_tac) >>
 first_assum (qspecl_then [‘Pair(l,x0)’] assume_tac) >>
 fs[Pair_def'] >>
 first_assum irule >> strip_tac (* 2 *)
 >-- (strip_tac >> strip_tac >> 
     first_assum (qspecl_then [‘Pair(l',x')’] (assume_tac o GSYM)) >> 
     once_arw[] >> rw[Pair_def'] >> 
     rpt strip_tac >> first_x_assum drule >>
     qpick_x_assum
     ‘!a. Holds(P, Fst(a), Snd(a)) <=> IN(a, s)’ (assume_tac o GSYM) >>
     once_arw[] >> rw[Pair_def'] >> once_arw[]) >>
 qpick_x_assum
     ‘!a. Holds(P, Fst(a), Snd(a)) <=> IN(a, s)’ (assume_tac o GSYM) >> 
  once_arw[] >> rw[Pair_def'] >> 
 first_x_assum accept_tac
 )
(form_goal
 “!X x A t:A * X ->X. ?Rf:List(A) ->X.
 Holds(Rf,Nil(A),x) & 
 (!l x0. Holds(Rf,l,x0) ==> !a. Holds(Rf,CONS(a,l),Eval(t,Pair(a,x0)))) &
 (!P.
 (Holds(P,Nil(A),x) & 
  (!l x0. Holds(P,l,x0) ==> !a. Holds(P,CONS(a,l),Eval(t,Pair(a,x0)))))
  ==> !l x0.Holds(Rf,l,x0) ==> Holds(P,l,x0))”));
end

val Rf_def = Rf_ex |> spec_all
                   |> ex2fsym0 "Rf" ["x","t"]
                   |> qgen ‘t’ |> qgen ‘A’
                   |> gen_all |> store_as "Rf_def";

val Rf_property = conjI (Rf_def |> spec_all |> conjE1)
                        (Rf_def |> spec_all |> conjE2 |> conjE1)
                        |> qgen ‘t’ |> qgen ‘A’
                        |> gen_all |> store_as "Rf_property";

val Rf_min = Rf_def |> spec_all |> conjE2 |> conjE2
                    |> qgen ‘t’ |> qgen ‘A’
                    |> gen_all |> store_as "Rf_property";

local
val P = 
fVar_Inst 
[("P",([("l1",mem_sort (rastt "List(A)")),("x1",mem_sort (mk_set "X"))],
“Holds(Rf(x,t:A * X->X),l1,x1) & ~(l1 = Nil(A) & x1 = x0)”))]
(AX1 |> qspecl [‘List(A)’,‘X’]) |> uex_expand
in
val Rf_Nil_unique = prove_store("Rf_Nil_unique",
e0
(rpt strip_tac >> ccontra_tac >>
 qsuff_tac
 ‘?P. Holds(P,Nil(A),x) & 
     (!l x0. Holds(P,l,x0) ==>
      !a. Holds(P,CONS(a,l),Eval(t,Pair(a,x0)))) & 
     ~Holds(P,Nil(A),x0)’ 
 >-- (strip_tac >> qsspecl_then [‘x’,‘t’,‘P’] assume_tac Rf_min >>
     qsuff_tac ‘Holds(P, Nil(A), x0)’ >--arw[] >>
     first_x_assum irule >> arw[Rf_property]) >>
 qsuff_tac
 ‘?P. !l1 x1. Holds(P,l1,x1) <=> 
  Holds(Rf(x,t),l1,x1) & ~(l1 = Nil(A) & x1 = x0)’
 >-- (strip_tac >> qexists_tac ‘P’ >> arw[] >>
     rw[Rf_property] >> flip_tac >> arw[] >>
     (*do not understand why need strip*)
     strip_tac >> strip_tac >> arw[] >> 
     rw[CONS_NOTNIL] >> rpt strip_tac >>  
     qsspecl_then [‘x’,‘t’] strip_assume_tac Rf_property >>
      last_x_assum (K all_tac) >>
      first_x_assum rev_drule >> arw[]) >>
 strip_assume_tac P >> 
 qexists_tac ‘R’ >> arw[]
 )
(form_goal
 “!X x A t:A * X ->X x0. 
  Holds(Rf(x,t),Nil(A),x0) ==> x0 = x”));
end

val Rf_CONS = Rf_property |> spec_all |> conjE2
                          |> qgen ‘t’ |> qgen ‘A’
                          |> gen_all
                          |> store_as "Rf_CONS";


local
val P = 
fVar_Inst 
[("P",([("l0",mem_sort (rastt "List(A)")),("x0",mem_sort (mk_set "X"))],
“Holds(Rf(x,t:A * X ->X),l0,x0) & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Holds(Rf(x,t),l1,x1) & x0 = Eval(t,Pair(a,x1))”))]
(AX1 |> qspecl [‘List(A)’,‘X’]) |> uex_expand
in
val Rf_Cons_back = prove_store("Rf_Cons_back",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 qby_tac
 ‘?P. !l0 x0. Holds(P,l0,x0) <=>
  Holds(Rf(x,t),l0,x0) & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Holds(Rf(x,t),l1,x1) & x0 = Eval(t,Pair(a,x1))’ 
 >-- (strip_assume_tac P >> qexists_tac ‘R’ >> arw[]) >>
 pop_assum strip_assume_tac >>
  qsuff_tac
 ‘!l0 x0.Holds(Rf(x, t),l0, x0) ==> Holds(P,l0,x0)’
 >-- arw[] >>
 match_mp_tac Rf_min >>
 arw[] >> rw[GSYM CONS_NOTNIL] >> rpt strip_tac (* 3 *)
 >-- rw[Rf_property]
 >-- (drule Rf_CONS >> arw[]) >>
 qsspecl_then [‘l’] strip_assume_tac CONS_or_Nil >-- (* 2 *)
 (fs[CONS_eq_eq] >> qexists_tac ‘x0'’ >> arw[]) >>
 fs[CONS_eq_eq] >> qexists_tac ‘x0'’ >> arw[]
)
(form_goal
 “!X x A t:A * X ->X l0 x0. Holds(Rf(x,t),l0,x0) ==>
  Holds(Rf(x,t),l0,x0) & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Holds(Rf(x,t),l1,x1) & x0 = Eval(t,Pair(a,x1))”));
end




local
val P = 
fVar_Inst 
[("P",([("l0",mem_sort (rastt "List(A)")),("x0",mem_sort (mk_set "X"))],
“(!x'. Holds(Rf(x,t:A * X ->X),l0,x')  ==> x' = x0)”))]
(AX1 |> qspecl [‘List(A)’,‘X’]) |> uex_expand
in
val Rf_unique = prove_store("Rf_unique",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 qby_tac
 ‘?P. !l0 x0. Holds(P,l0,x0) <=>
 (!x'. Holds(Rf(x,t),l0,x')  ==> x' = x0)’
 >-- (strip_assume_tac P >> qexists_tac ‘R’ >> arw[]) >> 
 pop_assum strip_assume_tac >>
 qsuff_tac 
 ‘!l0 x0. Holds(Rf(x,t),l0,x0) ==> Holds(P,l0,x0)’ 
 >-- arw[] >>
 match_mp_tac Rf_min >> arw[] >> 
 strip_tac (* 2 *)
 >-- rw[Rf_Nil_unique] >> rpt strip_tac >>
 drule Rf_Cons_back >> 
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘a’,‘l’] assume_tac) >> fs[] >>
 first_x_assum drule >> arw[])
(form_goal
 “!X x A t:A * X ->X l0 x0. 
  Holds(Rf(x,t),l0,x0) ==>
  !x'. Holds(Rf(x,t),l0,x') ==> x' = x0”));
end

local 
val l = 
 fVar_Inst 
[("P",([("l0",mem_sort (rastt "List(A)"))],
“?!x0. Holds(Rf(x, t:A * X ->X), l0, x0)”))] 
(List_ind |> qspecl [‘A’]) 
in
val Rf_uex = prove_store("Rf_uex",
e0
(rpt strip_tac >>
 irule l >> rpt strip_tac (* 2 *)
 >-- (pop_assum (strip_assume_tac o uex_expand) >>
     drule Rf_CONS >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 uex_tac >> qexists_tac ‘Eval(t, Pair(a,x0))’ >> arw[] >> drule Rf_unique >> arw[]) >>
 uex_tac >> qexists_tac ‘x’ >> rw[Rf_property] >>
 rw[Rf_Nil_unique])
(form_goal
 “!X x A t:A * X ->X l0.?!x0. Holds(Rf(x,t),l0,x0)”));
end



val List_rec = prove_store("List_rec",
e0
(rpt strip_tac >> uex_tac >> 
 assume_tac Rf_uex >> qexists_tac ‘Rf(x,t)’ >>
 qby_tac
 ‘isFun(Rf(x,t))’
 >-- arw[Fun_def] >>
 arw[] >> 
 qby_tac
 ‘Eval(Rf(x, t), Nil(A)) = x &
               Rf(x, t) o Cons(A) = t o
                 Pa(p1(A, List(A)), Rf(x, t) o p2(A, List(A)))’
 >-- (drule $GSYM Eval_def >> flip_tac >> arw[Rf_property] >>
     irule $ iffRL FUN_EXT >>
     qby_tac ‘isFun(Rf(x, t) o Cons(A))’
     >-- (irule o_Fun >> arw[Cons_def]) >> arw[] >>
     qby_tac ‘isFun(t o Pa(p1(A, List(A)), Rf(x, t) o p2(A, List(A))))’
     >-- (irule o_Fun >> arw[] >> irule Pa_Fun >>
         rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
     arw[] >> strip_tac >>
     assume_tac Rf_CONS >>
     qsspecl_then [‘a’] (x_choosel_then ["l","x0"] assume_tac)
     Pair_has_comp >> fs[] >>
     irule $ iffRL Eval_o_l >> rw[CONS_def] >>
     arw[Cons_def] >> flip_tac >>
     irule $ iffRL Eval_o_l >>
     arw[] >> rpt strip_tac  (* 2 *)
     >-- (qby_tac
         ‘isFun(p1(A, List(A))) & 
          isFun(Rf(x, t) o p2(A, List(A)))’
         >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
         drule Eval_Pa_Pair >> arw[] >> rw[Eval_p1_Pair] >>
         qby_tac ‘isFun(p2(A, List(A))) & isFun(Rf(x,t))’
         >-- arw[p2_Fun] >>
         drule$ GSYM o_Eval' >> arw[] >> rw[Eval_p2_Pair] >>
         first_x_assum irule >> 
         irule Holds_Eval >> arw[]) >>
     irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >>
     arw[p2_Fun]) >>
 arw[] >> rpt strip_tac >>
 irule from_List_eq >>
 arw[] >> rpt strip_tac >>
 rw[GSYM CONS_def] >>
 irule $ iffLR Eval_o_l >> arw[] >> 
 rw[Cons_def] >>
 irule $ iffRL Eval_o_l >> arw[] >> 
 qby_tac
 ‘isFun(p1(A, List(A))) & isFun(f' o p2(A, List(A)))’
 >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
 drule Eval_Pa_Pair >> arw[] >> rw[Eval_p1_Pair] >>
 qby_tac ‘isFun(p2(A,List(A))) & isFun(f')’ 
 >-- arw[p2_Fun] >>
 drule $GSYM o_Eval' >> arw[] >> rw[Eval_p2_Pair] >>
 arw[] >> strip_tac (* 2 *)
 >-- (flip_tac >> irule $ iffLR Eval_o_l >> arw[Cons_def] >>
     irule $ iffRL Eval_o_l >> arw[] >>
     strip_tac (* 2 *)
     >-- (irule Eval_input_eq >> 
         qby_tac ‘isFun(p1(A, List(A))) & isFun(Rf(x,t) o p2(A, List(A)))’
         >-- (rw[p1_Fun] >> irule o_Fun >> arw[p2_Fun]) >>
         drule Eval_Pa_Pair >> arw[] >>
         rw[Eval_p1_Pair] >> rw[Pair_eq_eq] >>
         irule $ iffRL Eval_o_l >> arw[p2_Fun,Eval_p2_Pair]) >>
     irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >>
     arw[p2_Fun]) >>
 irule Pa_Fun >> rw[p1_Fun] >> irule o_Fun >>
 arw[p2_Fun])
(form_goal
 “!X x A t:A * X ->X. isFun(t) ==> 
  ?!f:List(A) -> X. isFun(f) & Eval(f,Nil(A)) = x &
      f o Cons(A) = t o Pa(p1(A,List(A)), f o p2(A,List(A)))”));


(*
val Rf_ex = prove_store("Rf_ex",
e0
()
(form_goal
 “!X x:1->X A t:A * X ->X 
  ?Rf. 

!l0 x0.Holds(Rf,l0,x0) = TRUE ==>
  Rf(x,t) o Pa(l0,x0) = TRUE & 
  !a l1. l0 = CONS(a,l1) ==> 
  ?x1. Rf(x,t) o Pa(l1,x1) = TRUE & x0 = t o Pa(a,x1)”));

val Rf_def  = 

*)

val isList_property = prove_store("isList_property",
e0
()
(form_goal “!A l:List(A). 
 !
 ”));




