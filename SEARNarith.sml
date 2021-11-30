val o_assoc = Thm_2_7_assoc

val o_Fun = Thm_2_7_o_Fun

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

local
val l = 
(fVar_Inst [("P",([("d",mem_sort ONE),("x",mem_sort $ mk_set ("A"))],
“d = dot & x = a:mem(A)”))] (AX1 |> qspecl [‘1’,‘A’])) 
|> uex_expand
in
val El_ex = prove_store("El_ex",
e0
(rpt strip_tac >> strip_assume_tac l >>
 qexists_tac ‘R’ >> 
 qby_tac ‘isFun(R)’ >-- (rw[Fun_expand] >> arw[] >>
 rpt strip_tac >-- (qexists_tac ‘a’ >> rw[dot_def]) >> arw[]) >>
 arw[] >> drule $ GSYM Eval_def >> flip_tac >> arw[])
(form_goal
 “!A a:mem(A).?el:1->A.isFun(el) & Eval(el,dot) = a”))
end


val El_def = El_ex |> spec_all |> ex2fsym0 "El" ["a"]
                   |> gen_all
                   |> store_as "El_def";


val Eval_El = prove_store("Eval_El",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘a’] strip_assume_tac El_def >> 
 rw[dot_def] >> arw[]
 )
(form_goal
 “!A a:mem(A) x. Eval(El(a),x) = a”));

val El_Fun = El_def |> spec_all |> conjE1 |> gen_all
                    |> store_as "El_Fun";


val Nind_alt = prove_store("Nind_O",
e0
(rpt strip_tac >--
 (drule Nind_def >> arw[]) >-- (drule Nind_def >> arw[]) 
 >-- (drule Nind_def >> irule $ iffRL FUN_EXT >> 
     first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
     qby_tac ‘isFun(Nind(a,f) o SUC) & isFun(f o Nind(a, f))’
     >-- (strip_tac >> irule o_Fun >> arw[SUC_isFun]) >>
     arw[] >> strip_tac >> irule $ iffRL Eval_eq_o >>
     arw[SUC_Fun])
 (*irule does not work without strip*) >>
 drule Nind_def >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 first_x_assum irule >> arw[] >> 
 strip_tac >> irule $ iffLR Eval_eq_o >>
 arw[SUC_Fun]
 )
(form_goal
 “!X  f:X->X. isFun(f) ==>
 !a:mem(X).isFun(Nind(a,f)) & Eval(Nind(a,f),O) = a & 
 Nind(a,f) o SUC = f o Nind(a,f) &
 (!u. (isFun(u) & Eval(u,O) = a & u o SUC = f o u) ==> u = Nind(a,f))”));


val is_Nind = Nind_alt |> strip_all_and_imp
                       |> conjE2
                       |> conjE2
                       |> conjE2 |> gen_all
                       |> disch_all |> gen_all
                       |> store_as "is_Nind";

val El_eq_eq = prove_store("El_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (qby_tac ‘isFun(El(a)) & isFun(El(b))’
     >-- rw[El_Fun] >> 
     drule FUN_EXT >> fs[] >> 
     last_x_assum (qspecl_then [‘dot’] assume_tac) >>
     fs[El_def]) >> 
 arw[])
(form_goal
 “!A a:mem(A) b. El(a) = El(b) <=> a = b”));




val Eval_o_l = prove_store("Eval_o_l",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘Eval(g o f, a) = Eval(g, Eval(f, a))’
 >-- (strip_tac >> arw[])
  >> irule $ GSYM o_Eval >> arw[])
(form_goal
 “!A B f:A->B.isFun(f) ==> !C g:B->C.isFun(g) ==>
  !a c. Eval(g o f,a) = c <=>
 Eval(g,Eval(f,a)) = c”));

val Eval_o_El = prove_store("Eval_o_El",
e0
(rpt strip_tac >> flip_tac >> irule $ iffRL Eval_o_l >>
 arw[El_Fun] >> rw[El_def])
(form_goal
 “!A B f:A->B.isFun(f) ==>
  !a. Eval(f,a) = Eval(f o El(a),dot)”));

val Nind_El = prove_store("Nind_el",
e0
(strip_tac >> strip_tac >> strip_tac >>
 drule Nind_def >> strip_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 arw[] >> rpt strip_tac (* 3 *)
 >-- irule $ iffRL FUN_EXT >> rpt strip_tac (* 3 *)
     >-- (irule $ iffRL Eval_o_l >> arw[Eval_El,El_Fun])
     >-- (irule o_Fun >> arw[El_Fun] (* arw bug that does not use El_Fun *)
         >> rw[El_Fun]) >>
     rw[El_Fun]
 >-- (irule $ iffRL FUN_EXT >> rpt strip_tac (*3*)
     >-- (irule $ iffLR Eval_o_eq >> 
          arw[SUC_Fun]) 
     >-- (irule o_Fun >> arw[SUC_Fun]) >>
     irule o_Fun >> arw[]) >>
 first_x_assum irule >> arw[] >> rpt strip_tac (* 2 *)
 >-- (irule $ iffRL Eval_o_eq >> arw[] >> rw[SUC_Fun]) >>
 drule Eval_o_El >> arw[] >> rw[El_def])
(form_goal
 “!X  f:X->X. isFun(f) ==>
 !a:mem(X).isFun(Nind(a,f)) & Nind(a,f) o El(O) = El(a) & 
 Nind(a,f) o SUC = f o Nind(a,f) &
 (!u. (isFun(u) & u o El(O) = El(a) & u o SUC = f o u) ==> u = Nind(a,f))”));



val Eval_El_mem = prove_store("Eval_El_mem",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (irule $iffRL FUN_EXT >> rpt strip_tac (* 3 *)
     >-- (rw[Eval_El] >> irule $iffRL Eval_o_l >>
         arw[Eval_El,El_Fun]) 
     >-- (irule o_Fun >> arw[El_Fun]) >>
     rw[El_Fun]) >>
 qby_tac ‘Eval(f o El(a),dot) = Eval(El(b),dot)’ 
 >-- arw[] >>
 pop_assum mp_tac >> rw[Eval_El] >> strip_tac >>
 qsuff_tac ‘Eval(f o El(a), dot) = Eval(f,a)’ 
 >-- (strip_tac >> arw[] >> fs[]) >>
 irule $ iffRL Eval_o_l >>
 arw[El_def])
(form_goal
 “!A B f:A->B. isFun(f) ==> !a b. Eval(f,a) = b <=>
 f o El(a) = El(b)”));



val comm_with_SUC_id0 = prove_store("comm_with_SUC_id0",
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
 “!f:N->N. isFun(f) ==> Eval(f,O) = O & f o SUC = SUC o f ==> f = id(N)”));


val comm_with_SUC_id = prove_store("comm_with_SUC_id",
e0
(strip_tac >> strip_tac >> 
 drule comm_with_SUC_id0 >> drule Eval_El_mem >>
 fs[])
(form_goal
 “!f:N->N. isFun(f) ==> f o El(O) = El(O) & f o SUC = SUC o f ==> f = id(N)”));


val Pa_distr = prove_store("Pa_distr",
e0
(rpt strip_tac >> irule is_Pa >> 
 qspecl_then [‘A’,‘X’,‘a1’,‘B’,‘a2’] strip_assume_tac pi12_of_Pa >>
 rfs[] >> rw[GSYM o_assoc] >> arw[] >> 
 qspecl_then [‘A’,‘X’,‘a1’,‘B’,‘a2’] strip_assume_tac Pa_Fun >>
 rfs[] >> rpt strip_tac >>
 irule o_Fun >> arw[])
(form_goal
“!A X a1:X ->A . isFun(a1) ==> !B a2:X->B.isFun(a2) ==>
  !X0 x:X0->X.isFun(x) ==> Pa(a1,a2) o x = 
Pa(a1 o x,a2 o x) ”));


fun sspecl tl th = 
    let val (b,vs) = strip_forall $ concl th
        val ars = List.filter (fn (n,s) => not (on_ground o fst o dest_sort o snd $ (n,s))) vs
        val env = match_tl essps (List.map mk_var ars) tl emptyvd
        val tl' = List.map (inst_term env) (List.map mk_var vs)
    in specl tl' th
    end


fun sspecl_then tl (ttac: thm_tactic): thm_tactic = 
    fn th => ttac (aspecl tl th)

val qsspecl_then = qterml_tcl aspecl_then

val Pa_eq_eq = prove_store("Pa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘pi1(A,B) o Pa(f1, g1) = pi1(A,B) o Pa(f2, g2) &
          pi2(A,B) o Pa(f1, g1) = pi2(A,B) o Pa(f2, g2)’
 >-- arw[] >>
 qsspecl_then [‘f1’,‘g1’] assume_tac pi12_of_Pa >> 
 qsspecl_then [‘f2’,‘g2’] assume_tac pi12_of_Pa >> 
 rfs[])
(form_goal
 “!A X f1:X->A.isFun(f1) ==> !f2:X->A.isFun(f2) ==>
  !B g1:X->B. isFun(g1) ==> !g2:X->B. isFun(g2) ==> 
  (Pa(f1,g1) = Pa(f2,g2) <=> f1 = f2 & g1 = g2)”));



val Pa_eq_eq' = prove_store("Pa_eq_eq'",
e0
(rpt strip_tac >> irule Pa_eq_eq >> arw[])
(form_goal
 “!A X f1:X->A f2 B g1:X->B g2.isFun(f1) & isFun(f2) & isFun(g1) & isFun(g2) ==> 
  (Pa(f1,g1) = Pa(f2,g2) <=> f1 = f2 & g1 = g2)”));


val Thm1_case1_comm_condition_left = prove_store(
"Thm1_case1_comm_condition_left",
e0
(rpt strip_tac >> qspecl_then [‘N’] assume_tac id_Fun >>
 drule Pa_distr >> first_x_assum rev_drule >>
 qspecl_then [‘N’,‘O’] assume_tac El_Fun >>
 first_x_assum drule >> arw[idL] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (drule Pa_eq_eq >> 
     qby_tac ‘isFun(f o El(O))’ 
     >-- (irule o_Fun >> arw[El_Fun]) >>
     first_x_assum drule >> 
     first_x_assum drule >> first_x_assum rev_drule >>
     fs[]) >>
 arw[])
(form_goal
 “!B f:N->B. isFun(f) ==> !g:1->B. isFun(g) ==>
 (Pa(id(N),f) o El(O) = Pa(El(O),g) <=> f o El(O) = g)”));


val Thm1_case1_comm_condition_right = prove_store(
"Thm1_case1_comm_condition_right",
e0
(rpt strip_tac >> 
 qsspecl_then [‘SUC o pi1(N,B)’,‘h’,‘Pa(id(N),f)’] assume_tac Pa_distr'>>
 qsspecl_then [‘id(N)’,‘f’,‘SUC’] assume_tac Pa_distr' >>
 rfs[] >> 
 assume_tac SUC_Fun >> 
 qspecl_then [‘N’] assume_tac id_Fun >>
 qspecl_then [‘N’,‘B’] assume_tac pi1_Fun >>
 qsspecl_then [‘id(N)’,‘f’] assume_tac Pa_Fun >>
 qsspecl_then [‘pi1(N,B)’,‘SUC’] assume_tac o_Fun >>
 fs[] >> rfs[] >> fs[] >> rw[o_assoc,idL,idR] >>
 qsspecl_then [‘id(N)’,‘f’] assume_tac pi1_of_Pa >> rfs[] >>
 rw[idR] >>
 qsspecl_then [‘SUC’,‘SUC’,‘h o Pa(id(N),f)’,‘f o SUC’] assume_tac Pa_eq_eq' >> 
 qsspecl_then [‘SUC’,‘f’] assume_tac o_Fun >>
 qsspecl_then [‘Pa(id(N),f)’,‘h’] assume_tac o_Fun >>
 fs[] >> rfs[] >> fs[])
(form_goal
 “!B f:N->B. isFun(f) ==> !h:N * B ->B.isFun(h) ==>
 (Pa(SUC o pi1(N,B),h) o Pa(id(N),f) = Pa(id(N),f) o SUC <=>
 h o Pa(id(N),f) = f o SUC)”));

val Thm1_case1_comm_condition = prove_store(
"Thm1_case1_comm_condition",
e0
(rpt strip_tac >>  
 drule Thm1_case1_comm_condition_left >> first_x_assum drule >>
 drule Thm1_case1_comm_condition_right >> first_x_assum drule >>
 arw[] >> dimp_tac >> strip_tac >> arw[])
(form_goal
 “!B f0:N->B g:1->B h:N * B -> B.
  isFun(f0) & isFun(g) & isFun(h) ==> (f0 o El(O) = g & f0 o SUC = h o Pa(id(N),f0) <=>
 Pa(id(N),f0) o El(O) = Pa(El(O),g) &
 Pa(SUC o pi1(N,B),h) o Pa(id(N),f0) = Pa(id(N),f0) o SUC)”));



val Dot_ex = prove_store("Dot_ex",
e0
(rpt strip_tac >> fs[Fun_expand] >>
 first_x_assum (qspecl_then [‘dot’] strip_assume_tac) >>
 last_x_assum (qspecl_then [‘dot’] strip_assume_tac) >>
 rw[dot_def] >> qexists_tac ‘b’ >> arw[] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal
 “!A f:1->A.isFun(f) ==> ?a. !d.Holds(f,d,a) &
   (!a0 d. Holds(f,d,a0) ==> a0 = a)”)); 

val Dot_def = Dot_ex |> spec_all |> ex2fsym "Dot" ["f"] 
                     |> gen_all |> store_as "Dot_def";


val Holds_El = prove_store("Holds_El",
e0
(rpt strip_tac >>  
 qspecl_then [‘A’,‘a’] strip_assume_tac El_def >>
 drule Eval_def >> arw[] >> flip_tac >> arw[dot_def])
(form_goal
 “!A a:mem(A) d. Holds(El(a),d,a)”));

 
val Dot_of_El = prove_store("Dot_of_El",
e0
(rpt strip_tac >> qspecl_then [‘A’,‘a’] assume_tac El_Fun >> 
 drule Dot_def >> first_x_assum (qspecl_then [‘dot’] strip_assume_tac) >>
 flip_tac >> first_x_assum irule >> qexists_tac ‘dot’ >>
 rw[Holds_El])
(form_goal
 “!A a:mem(A).Dot(El(a)) = a”));

val Thm1_case_1 = prove_store("Thm1_case_1",
e0
(rpt strip_tac >> uex_tac >> 
 abbrev_tac “Nind(Pa(El(O),g:1->B),Pa(SUC o pi1(N,B),h:N * B->B)) = f'” >>
 abbrev_tac “pi2(N,B) o f':N->N * B = f” >>
 qby_tac ‘p1(N,B) o f' = id(N)’ >--
 (irule comm_with_SUC_id >> 
  qpick_x_assum ‘Nind(Pa(O, g), Pa(SUC o p1(N, B), h)) = f'’
  (assume_tac o GSYM) >> arw[] >>
  rw[o_assoc,Nind_def,p1_of_Pa] >> 
  rw[GSYM o_assoc,p1_of_Pa]) >>
 qby_tac ‘f' = Pa(id(N),f)’ >--
 (once_rw[to_P_component] >> rw[p12_of_Pa] >> arw[]) >>
 qexists_tac ‘f’ >>
 qby_tac ‘f' o O = Pa(O,g) & 
  f' o SUC = Pa(SUC o p1(N, B), h) o f'’ 
 >-- (qpick_x_assum 
     ‘Nind(Pa(O, g), Pa(SUC o p1(N, B), h)) = f'’
     (assume_tac o GSYM) >> once_arw[] >>
     rw[Nind_def]) >>
 qby_tac ‘f o O = g & f o SUC = h o Pa(id(N), f)’
 >-- (qpick_x_assum ‘p2(N, B) o f' = f’ (assume_tac o GSYM)>>
      once_arw[] >> rw[o_assoc] >> once_arw[] >>
      rw[GSYM o_assoc,p2_of_Pa] >>
      pop_assum (K all_tac) >>
      pop_assum (K all_tac) >> arw[]) >>
 once_arw[] >> rw[] >>
 rpt strip_tac >> 
 qsuff_tac ‘Pa(id(N), f'') = Pa(id(N), f)’ 
 >-- rw[Pa_eq_eq] >>
 qsuff_tac ‘Pa(id(N), f'') = f'’ >-- arw[] >>
 qsuff_tac ‘Pa(id(N), f'') = 
  Nind(Pa(O, g), Pa(SUC o p1(N, B), h))’ >-- arw[] >>
 irule is_Nind >> 
 rw[Pa_distr,p1_of_Pa,o_assoc,idL,idR] >> once_arw[] >>
 rw[])
(form_goal
 “!B g:1->B h:N * B -> B. ?!f:N->B. f o El(O) = g & f o SUC = h o Pa(id(N),f)”));


val is_Nind = Nind_El |> spec_all |> undisch |>spec_all |> conjE2
                      |> conjE2 |> conjE2
                      |> disch_all |> gen_all
                      |> store_as "is_Nind";




val o_eq_l = prove_store("o_eq_l",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!B C g1:B->C g2:B->C. g1 = g2 ==>
  !A f:A->B. g1 o f = g2 o f”));


val o_eq_r = prove_store("o_eq_r",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!A B f1:A->B f2:A->B. f1 = f2 ==>
  !C g:B->C. g o f1 = g o f2”));




val Pa_distr' = Pa_distr |> strip_all_and_imp |> conj_all_assum
                         |> disch_all
                         |> gen_all
                         |> store_as "Pa_distr'"; 




val pi1_Fun = pi12_Fun |> spec_all |> conjE1 |> gen_all
                       |> store_as "pi1_Fun";



val pi2_Fun = pi12_Fun |> spec_all |> conjE2 |> gen_all
                       |> store_as "pi2_Fun";




(*
define the set of lists
Eval(f:A(set of A->B functions)->B(set of A list -> B list function),a)

induction recursion

!P. P [] & (!t h.P(t) ==> P(h :: t)) ==> !l. P(l)

recursion :

!n c:'a -> 'b -> 'b. ?!f:'a list -> 'b. f [] = n & !h t. f(h :: t) = c h (f t)


map fold


Map(f:A->B): 'a list set -> 'b list set





*)




val ADD_def0 = Nind_def |> specl [rastt "N"]
                        |> specl [rastt "SUC"]
                        |> C mp SUC_Fun 
                        


(*
pre0 
pre0 n = (n,pre n)

f: (n,pre n) |-> (suc n, n)


(1, pre 1 = pre 0) |-> 
*)


val PRE_def0 = Nind_def |> specl [rastt "N * N"]
                        |> specl [rastt "SUC"]
                        |> C mp SUC_Fun 
                        
