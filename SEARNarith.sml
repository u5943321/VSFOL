local
val lemma = 
 fVar_Inst 
[("P",([("A",mem_sort$ Pow $ Cross N (mk_set "X"))],
“IN(Pair(O,a:mem(X)),A) &
 (!n x.IN(Pair(n,x),A) ==> IN(Pair(Eval(SUC,n),Eval(f,x)),A))”))] 
(IN_def_P_expand |> qspecl [‘Pow(N * X)’]) 
val As_def = lemma |> ex2fsym0 "As" ["a","f"] |> conjE1 
                   |> gen_all |> GSYM
val U_ex_lemma = fVar_Inst 
[("P",([("nx",mem_sort $ Cross N (mk_set "X"))],
“IN(nx,Eval(BI(N * X),As(a0,f)))”))]
(Thm_2_4 |> qspecl [‘N * X’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all BI_property)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all As_def) |> gen_all
val rel_ex_lemma = 
fVar_Inst 
[("P",([("n",mem_sort N),("x",mem_sort (mk_set "X"))],
“?r.Eval(u0:U-> N * X,r) = Pair(n,x)”))]
(AX1 |> qspecl [‘N’,‘X’]) |> uex_expand
val imp_ind_l = 
fVar_Inst 
[("P",([("n",mem_sort N)],
“!x.Holds(R:N->X,n,x) ==> Holds(R,Eval(SUC,n),Eval(f,x))”))]
N_ind_P
val O_case_u_l = 
fVar_Inst 
[("P",([("nx",mem_sort $ Cross N (mk_set "X"))],
“Holds(R,Eval(pi1(N,X),nx),Eval(pi2(N,X),nx)) & 
 ~(Eval(pi1(N,X),nx) = O & Eval(pi2(N,X),nx) = x)”))] 
(IN_def_P_expand |> qspecl [‘(N * X)’]) 
val ex_R_ss = 
fVar_Inst 
[("P",([("mr",mem_sort $ Cross N (mk_set "X"))],
“Holds(R,Eval(pi1(N,X),mr),Eval(pi2(N,X),mr)) &
 !n. Eval(pi1(N,X),mr) = Eval(SUC,n) ==>
 ?r0.Holds(R,n,r0) & Eval(pi2(N,X),mr) = Eval(f:X->X,r0)”))] 
(IN_def_P_expand |> qspecl [‘(N * X)’]) 
val u_R_ss1 = 
fVar_Inst 
[("P",([("mr",mem_sort $ Cross N (mk_set "X"))],
“Holds(R,Eval(pi1(N,X),mr),Eval(pi2(N,X),mr)) &
 (!x'.Holds(R,Eval(pi1(N,X),mr),x') ==> x' = Eval(pi2(N,X),mr))”))] 
(IN_def_P_expand |> qspecl [‘(N * X)’]) 
val ex_ind_l = 
fVar_Inst 
[("P",([("n",mem_sort N)],
“?x.Holds(R:N->X,n,x)”))]
N_ind_P
in
val Nind_ex = prove_store("Nind_ex",
e0
(rpt strip_tac >> 
 qspecl_then [‘X’,‘a’,‘f’] (x_choosel_then ["U","u0"] 
 strip_assume_tac) U_ex_lemma >>
 strip_assume_tac rel_ex_lemma >> pop_assum (K all_tac) >>
 (*qexists_tac ‘R’ >> *)
 qby_tac 
 ‘!n x. Holds(R,n,x) <=>
  !ss. IN(Pair(O,a),ss) &
       (!n x. IN(Pair(n,x),ss) ==>
              IN(Pair(Eval(SUC,n),Eval(f,x)),ss)) ==>
        IN(Pair(n,x),ss)’
 >-- (arw[] >> rpt strip_tac >>
 fconv_tac 
 (rand_fconv no_conv 
 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "mem"))) >> rw[]) >>
 pop_assum mp_tac >> pop_assum (K all_tac) >> 
 pop_assum (K all_tac) >> strip_tac >>
 qby_tac 
 ‘Holds(R,O,a)’ >-- (arw[] >> rpt strip_tac) >>
 qby_tac
 ‘!n x. Holds(R,n,x) ==> Holds(R,Eval(SUC,n),Eval(f,x))’
 >-- (match_mp_tac imp_ind_l (* irule bug *)>> strip_tac (* 2 *)
     (*0 case*)
     >-- (rpt strip_tac >>
         qsuff_tac ‘Holds(R, O, x') ==>
         Holds(R, Eval(SUC, O), Eval(f, x'))’ 
         >-- (rpt strip_tac >> first_assum drule >> arw[]) >>
         arw[] >> rpt strip_tac >> first_assum irule >>
         last_assum $ irule o iffLR >> arw[]) >>
     rpt strip_tac >> arw[] >> 
     rpt strip_tac >> first_assum irule >>
     qpick_x_assum ‘Holds(R, Eval(SUC, n'), x')’ mp_tac >> 
     arw[] >> rpt strip_tac >> first_assum irule >> arw[]) >>
 qby_tac ‘!x. Holds(R,O,x) ==> x = a’
 >-- (rpt strip_tac >> ccontra_tac >>
      qsuff_tac ‘?ss. IN(Pair(O,a),ss) & 
      (!n x.IN(Pair(n,x),ss) ==> IN(Pair(Eval(SUC,n),Eval(f,x)),ss)) &
      ~(IN(Pair(O,x),ss))’
      >-- (last_assum (drule o iffLR) >> rpt strip_tac >>
          qsuff_tac ‘IN(Pair(O, x), ss)’
          >-- arw[] >>
          first_x_assum irule >> arw[]) >>
      x_choose_then "ss" strip_assume_tac O_case_u_l >>
      pop_assum (K all_tac) >>
      qby_tac ‘~(IN(Pair(O,x),ss))’
      >-- (pop_assum (assume_tac o GSYM) >> once_arw[] >>
          rw[Pair_def]) >>
      qby_tac ‘IN(Pair(O,a),ss)’
      >-- (pop_assum (K all_tac) >> pop_assum (assume_tac o GSYM) >>
           once_arw[] >> rw[Pair_def] >> arw[] >>
           flip_tac >> first_x_assum accept_tac) >>
      qexists_tac ‘ss’ >> arw[] >>
      pop_assum (K all_tac) >> pop_assum (K all_tac) >>
      pop_assum (assume_tac o GSYM) >> strip_tac >> strip_tac >> 
      once_arw[] >> rw[Pair_def] >> rpt strip_tac >-- 
      (first_x_assum irule >> arw[]) >>
      rw[SUC_NONZERO]) >>
 qby_tac ‘!ss.IN(Pair(O,a),ss) &
      (!n x.IN(Pair(n,x),ss) ==> IN(Pair(Eval(SUC,n),Eval(f,x)),ss)) ==>
      !n x. Holds(R,n,x) ==> IN(Pair(n,x),ss)’
 >-- (once_arw[] >> rpt strip_tac >> first_x_assum irule >>
     arw[]) >>
 x_choose_then "ss" strip_assume_tac ex_R_ss >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >>
 qby_tac ‘!n x. Holds(R,n,x) ==> IN(Pair(n,x),ss)’
 >-- (first_x_assum match_mp_tac >> once_arw[] >>
      rw[Pair_def] >> strip_tac (* 2 *)
      >-- (strip_tac >-- first_x_assum accept_tac >>
           flip_tac >> rw[SUC_NONZERO]) >>
      rpt strip_tac (*2  *)
      >-- (first_x_assum irule >> first_x_assum accept_tac) >>
      qexists_tac ‘x'’ >> rw[] >>
      fs[SUC_eq_eq]) >>
 pop_assum mp_tac >>
 last_x_assum mp_tac >> last_x_assum mp_tac >> 
 last_x_assum (assume_tac o GSYM) >> once_arw[] >>
 rw[Pair_def] >> rpt strip_tac >>
 qby_tac
 ‘!n x. Holds(R,Eval(SUC,n),x) ==> 
  ?x0. Holds(R,n,x0) & x = Eval(f,x0)’
 >-- (rpt strip_tac >> first_x_assum drule >>
     pop_assum strip_assume_tac >> 
     first_x_assum (qspecl_then [‘n’] assume_tac) >> fs[] >>
     qexists_tac ‘r0’ >> arw[]) >>
 x_choose_then "ss1" strip_assume_tac u_R_ss1 >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >>
 qby_tac 
 ‘!n x. Holds(R,n,x) ==> IN(Pair(n,x),ss1)’
 >-- (first_x_assum match_mp_tac >> once_arw[] >>
      rw[Pair_def] >> strip_tac (* 2 *)
      >-- (strip_tac (*2*)>> first_x_assum accept_tac) >>
      rpt strip_tac (* 2 *)
      >-- (first_x_assum irule >> first_x_assum accept_tac) >>
      first_assum (qspecl_then [‘n'’,‘x''’] assume_tac) >>
      first_x_assum drule >> pop_assum strip_assume_tac >> 
      once_arw[] >>
      qsuff_tac ‘x0 = x'’
      >-- (strip_tac >> arw[]) >>
      first_x_assum irule >> first_x_assum accept_tac) >>
 pop_assum mp_tac >> once_arw[] >> rw[Pair_def] >>
 rpt strip_tac >> 
 qby_tac
 ‘!n x.Holds(R,n,x) ==>
  !x'. Holds(R,n,x') ==> x' = x’
 >-- (rpt strip_tac >> first_assum drule >>
      first_x_assum drule >> pop_assum strip_assume_tac >>
      flip_tac >> first_x_assum irule >>
      first_x_assum accept_tac) >>
 qby_tac
 ‘!n.?x. Holds(R,n,x)’
 >-- (irule ex_ind_l >> rpt strip_tac >--
     (last_x_assum drule >> qexists_tac ‘Eval(f,x)’ >> arw[]) >>
     qexists_tac ‘a’ >> arw[]) >>
 qby_tac
 ‘isFun(R)’
 >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac >>
      first_x_assum drule >> first_x_assum irule >> arw[]) >>
 qexists_tac ‘R’ >> arw[] >>
 drule $ GSYM Eval_def >> flip_tac >> once_arw[] >>
 strip_tac >-- first_x_assum accept_tac >>
 strip_tac >>
 drule Holds_Eval >> 
 first_x_assum (qspecl_then [‘n’] assume_tac) >> 
 last_x_assum irule >> first_x_assum accept_tac
 )
(form_goal
 “!X a:mem(X) f:X->X. isFun(f) ==>
 ?u:N->X. isFun(u) & Eval(u,O) = a & 
 !n:mem(N).Eval(u,Eval(SUC,n)) = Eval(f,Eval(u,n))”));
end








val lemma = 
 fVar_Inst 
[("P",([("A",mem_sort$ Pow $ Cross N (mk_set "X"))],
“IN(Pair(O,a:mem(X)),A) &
 (!n x.IN(Pair(n,x),A) ==> IN(Pair(Eval(SUC,n),Eval(f,x)),A))”))] 
(IN_def_P_expand |> qspecl [‘Pow(N * X)’]) 

val As_def = lemma |> ex2fsym0 "As" ["a","f"] |> conjE1 
                   |> gen_all |> GSYM

val U_ex_lemma = fVar_Inst 
[("P",([("nx",mem_sort $ Cross N (mk_set "X"))],
“IN(nx,Eval(BI(N * X),As(a0,f)))”))]
(Thm_2_4 |> qspecl [‘N * X’]) 
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all BI_property)
|> conv_rule $ once_depth_fconv no_conv 
$ rewr_fconv (spec_all As_def) |> gen_all

val rel_ex_lemma = 
fVar_Inst 
[("P",([("n",mem_sort N),("x",mem_sort (mk_set "X"))],
“?r.Eval(u0:U-> N * X,r) = Pair(n,x)”))]

(AX1 |> qspecl [‘N’,‘X’]) |> uex_expand


