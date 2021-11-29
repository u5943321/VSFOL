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



local 
val ind_l = 
fVar_Inst 
[("P",([("n",mem_sort N)],
“Eval(u1:N->X,n) = Eval(u2,n)”))]
N_ind_P
in
val Nind_unique = prove_store("Nind_unique",
e0
(rpt strip_tac >> 
 irule $ iffRL FUN_EXT >> 
 arw[] >> irule ind_l >> arw[] >> rpt strip_tac >> arw[])
(form_goal
 “!X a:mem(X) f:X->X. isFun(f) ==>
  (!u1:N->X u2. (isFun(u1) & Eval(u1,O) = a & 
               (!n:mem(N).Eval(u1,Eval(SUC,n)) = Eval(f,Eval(u1,n))) & 
               isFun(u2) & Eval(u2,O) = a & 
               (!n:mem(N).Eval(u2,Eval(SUC,n)) = Eval(f,Eval(u2,n))))==>
  u1 = u2)”));
end


val Nind_uex = prove_store("Nind_uex",
e0
(rpt strip_tac >> uex_tac >>
 drule Nind_ex >> pop_assum strip_assume_tac >>
 qexists_tac ‘u’ >> arw[] >> rpt strip_tac >>
 irule Nind_unique >> 
 arw[] >> strip_tac 
 >-- (qexists_tac ‘f’ >> arw[]) >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!X a:mem(X) f:X->X. isFun(f) ==>
 ?!u:N->X. isFun(u) & Eval(u,O) = a & 
 !n:mem(N).Eval(u,Eval(SUC,n)) = Eval(f,Eval(u,n))”));



val Nind_def = Nind_uex |> spec_all |> undisch
                        |> uex_expand
                        |> ex2fsym0 "Nind" ["a","f"]
                        |> qgen ‘a’
                        |> disch_all
                        |> gen_all
                        |> store_as "Nind_def";

val Nind_property = Nind_def |> spec_all |> undisch |> spec_all
                        |> conjE1 |> qgen ‘a’
                        |> disch_all |> gen_all
                        |> store_as "Nind_property";

val Nind_Fun = Nind_property |> strip_all_and_imp |> conjE1
                             |> gen_all |> disch_all |> gen_all
                             |> store_as "Nind_Fun";


val Nind_eqns = Nind_property |> strip_all_and_imp |> conjE2
                             |> gen_all |> disch_all |> gen_all
                             |> store_as "Nind_Fun";

val SUC_Fun = SUC_isFun; 

val Eval_o_eq0 = prove_store("Eval_o_eq",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘Eval(g1, Eval(f1, a)) = Eval(g1 o f1, a) &
  Eval(g2, Eval(f2, a)) = Eval(g2 o f2, a)’
 >-- (strip_tac >> arw[]) >> strip_tac >> irule o_Eval >>
 arw[])
(form_goal
 “!A B f1:A->B C f2:A->C D g1:B->D g2:C->D.
  isFun(f1) ==> isFun(f2) ==> isFun(g1) ==> isFun(g2) ==>
  !a.Eval(g1,Eval(f1,a)) = Eval(g2,Eval(f2,a)) <=> 
     Eval(g1 o f1,a) = Eval(g2 o f2,a)”));

val Eval_o_eq = Eval_o_eq0 |> strip_all_and_imp |> gen_all
                           |> disch “isFun(g2:C->D)”
                           |> gen_all
                           |> disch “isFun(g1:B->D)”
                           |> gen_all
                           |> disch “isFun(f2:A->C)”
                           |> gen_all
                           |> disch “isFun(f1:A->B)”
                           |> gen_all
                           |> store_as "Eval_o_eq";

val Eval_eq_o = GSYM Eval_o_eq |> store_as "Eval_eq_o";




val Nind_alt = prove_store("Nind_O",
e0
(rpt strip_tac >> uex_tac >> qexists_tac ‘Nind(a,f)’ >> 
 drule Nind_def >> arw[] >>
 rpt strip_tac (* 2 *)
 >-- (irule $ iffRL FUN_EXT >> 
     first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
     qby_tac ‘isFun(Nind(a,f) o SUC) & isFun(f o Nind(a, f))’
     >-- (strip_tac >> irule o_Fun >> arw[SUC_isFun]) >>
     arw[] >> strip_tac >> irule $ iffRL Eval_eq_o >>
     arw[SUC_Fun])
 (*irule does not work without strip*) >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 first_x_assum irule >> arw[] >> 
 strip_tac >> irule $ iffLR Eval_eq_o >>
 arw[SUC_Fun]
 )
(form_goal
 “!X a:mem(X) f:X->X. isFun(f) ==>
 ?!u:N->X. isFun(u) & Eval(u,O) = a & 
 u o SUC = f o u”));


val Thm1_case1_comm_condition_left = prove_store(
"Thm1_case1_comm_condition_left",
e0
(rpt strip_tac >> rw[Pa_distr,idL] >> dimp_tac >> strip_tac
 >-- arw[] >>
 fs[Pa_eq_eq])
(form_goal
 “!B f:N->B g:1->B. Eval(Pa(id(N),f),O) = Pa(O,g) <=> Eval(f,O) = Eval(g,dot)”));
 
val Thm1_case1_comm_condition_right = prove_store(
"Thm1_case1_comm_condition_right",
e0
(rpt strip_tac >> 
 rw[Pa_distr,o_assoc,p1_of_Pa,idL,idR,Pa_eq_eq])
(form_goal
 “!B f:N->B h:N * B ->B.
 Pa(SUC o p1(N,B),h) o Pa(id(N),f) = Pa(id(N),f) o SUC <=>
 h o Pa(id(N),f) = f o SUC”));

val Thm1_case1_comm_condition = prove_store(
"Thm1_case1_comm_condition",
e0
(rpt strip_tac >> 
 rw[Thm1_case1_comm_condition_left,
 Thm1_case1_comm_condition_right] >> dimp_tac >> strip_tac >> arw[])
(form_goal
 “!B f0:N->B g:1->B h:N * B -> B. f0 o O = g & f0 o SUC = h o Pa(id(N),f0) <=>
 Pa(id(N),f0) o O = Pa(O,g) &
 Pa(SUC o p1(N,B),h) o Pa(id(N),f0) = Pa(id(N),f0) o SUC”));


val comm_with_SUC_id = prove_store("comm_with_SUC_id",
e0
(qspecl_then [‘N’,‘SUC’] strip_assume_tac Nind_def >>
 assume_tac SUC_isFun >> first_x_assum drule >>
 first_x_assum (qspecl_then [‘O’] strip_assume_tac) >> 
 rpt strip_tac >>
 qsuff_tac ‘f = Nind(O,SUC) & id(N) = Nind(O,SUC)’
 >-- (strip_tac >> arw[]) >> 
 strip_tac >> first_x_assum irule
 >-- (arw[] >> strip_tac >> 
      qby_tac 
      ‘Eval(f, Eval(SUC, n)) = Eval(f o SUC, n) & 
       Eval(SUC, Eval(f, n)) = Eval(SUC o f, n)’
      >-- (strip_tac >> irule o_Eval >> arw[]) >>
      arw[]) >>
 rw[Eval_id,id_Fun]
 )
(form_goal
 “!f:N->N. isFun(f) ==>Eval(f,O) = O & f o SUC = SUC o f ==> f = id(N)”));

val is_Nind = Nind_def |> spec_all |> undisch |> conjE2
                       |> disch_all |> gen_all
                       |> store_as "is_Nind";

val o_assoc = Thm_2_7_assoc

val o_Fun = Thm_2_7_o_Fun

val Thm1_case_1 = prove_store("Thm1_case_1",
e0
(rpt strip_tac >> uex_tac >>
 assume_tac SUC_isFun >>
 qspecl_then [‘N’,‘B’] strip_assume_tac pi12_Fun >>
 qby_tac ‘isFun(SUC o pi1(N,B))’
 >-- (irule o_Fun >> arw[]) >>
 drule Nind_def
 assume_tac 
 abbrev_tac “Nind(Pair(O,g),Pa(SUC o pi1(N,B),h:N*B->B)) = f'” >>
 abbrev_tac “pi2(N,B) o f':N -> N * B = f” >>
 qby_tac ‘pi1(N,B) o f' = id(N)’
 >-- irule comm_with_SUC_id >> 
     qpick_x_assum ‘Nind(Pair(O, g), Pa(SUC o pi1(N, B), h)) = f'’
     (assume_tac o GSYM) >> arw[] >>
     Nind_def
 qexists_tac ‘pi2(N,B) o Nind(Pair(O,g),Pa(SUC o pi1(N,B),h))’ >>
 )
(form_goal
 “!B g:mem(B) h:N * B -> B. 
  isFun(h) ==> ?!f:N->B. Eval(f,O) = g & f o SUC = h o Pa(id(N),f)”)));
