
local
val Nind_cl = 
 “(nx = Pair(O,x0:mem(X)) ==> IN(nx,Nind)) &
  (!nx0. IN(nx0,Nind) & nx = Pair(Suc(Fst(nx0)),App(f0:X->X,Snd(nx0)))
    ==> IN(nx,Nind))”
in
val (Nind_incond,x1) = mk_incond Nind_cl;
val Nindf_ex = mk_fex Nind_incond x1;
val Nindf_def = mk_fdef "Nindf" Nindf_ex;
val Nindf_monotone = mk_monotone Nindf_def;
val Nind's_def = mk_prim Nindf_def;
val Ninds_def = mk_LFP (rastt "Nind's(f0:X->X,x0)");
val Ninds_cond = mk_cond Ninds_def Nind's_def;
val Ninds_SS = mk_SS Ninds_def Nind's_def;
val Nind_rules0 = mk_rules Nindf_monotone Ninds_SS Ninds_cond;
val Nind_cases0 = mk_cases Nindf_monotone Nind_rules0 Ninds_cond;
val Nind_ind0 = mk_ind Ninds_cond;
val Nind_ind1 = mk_ind1 Nindf_def Nind_ind0;
val Nind_ind2 = mk_ind2 Nind_ind1; 
val Nind_cases1 = mk_case1 Nindf_def Nind_cases0; 
val Nind_rules1 = mk_rules1 Nindf_def Nind_rules0; 
val Nind_rules2 = mk_rules2 Nind_rules1; 
val Nind_rules3 = mk_rules3 Nind_rules2;
end

val Nind_ind = Nind_ind2 |> store_as "Nind_ind";
val Nind_cases = Nind_cases1 |> store_as "Nind_cases";
val Nind_rules = Nind_rules3 |> store_as "Nind_rules";

(* !(x' : mem(X)). x'# = x0 | (?(nx0 : mem(N * X)). F) ==> x'# = x0
 simp out the F*)
val Nind_uex = prove_store("Nind_uex",
e0
(strip_tac >> strip_tac >> strip_tac >> 
 ind_with N_induct >> strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘x0’ >>
     rw[Nind_rules] >> once_rw[Nind_cases] >> rw[Pair_eq_eq,GSYM Suc_NONZERO] >>
     rpt strip_tac) >>
 rpt strip_tac >> uex_tac >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘App(f0,x)’ >>  
 drule (Nind_rules |> conjE2) >> fs[Pair_def'] >>
 rpt strip_tac >> drule $ iffLR Nind_cases >>
 fs[Pair_eq_eq,Suc_NONZERO] >>
 qsspecl_then [‘nx0’] (x_choosel_then ["n1","x1"] strip_assume_tac) 
 Pair_has_comp >> fs[Pair_def',Suc_eq_eq] >>
 qby_tac ‘x1 = x’ 
 >-- (first_x_assum irule >> arw[]) >> 
 arw[])
(form_goal “!X x0:mem(X) f0:X->X. !n:mem(N).?!x. IN(Pair(n,x),Ninds(f0,x0))”));

val Nrec_def = P2fun' |> qspecl [‘N’,‘X’] 
                      |> fVar_sInst_th “P(n:mem(N),x:mem(X))”
                          “IN(Pair(n,x),Ninds(f0:X->X,x0))”
                      |> C mp (Nind_uex |> spec_all
                                        |> qgen ‘n’)
                      |> qSKOLEM "Nrec" [‘x0’,‘f0’]
                      |> qgenl [‘X’,‘x0’,‘f0’]
                      |> store_as "Nrec_def";



val Nrec_O = prove_store("Nrec_O",
e0
(rpt strip_tac >>
 qsspecl_then [‘x0’,‘f0’,‘O’] assume_tac Nrec_def >>
 drule $ iffLR Nind_cases >> fs[Pair_eq_eq,GSYM Suc_NONZERO])
(form_goal “!X x0 f0:X->X. App(Nrec(x0,f0),O) = x0”));

val App_Nrec_Ninds = prove_store("App_Nrec_Ninds",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >--
(pop_assum (assume_tac o GSYM) >> arw[Nrec_def]) >>
qsspecl_then [‘x0’,‘f0’,‘n’] assume_tac Nrec_def >>
qsspecl_then [‘x0’,‘f0’,‘n’] assume_tac Nind_uex >>
pop_assum (strip_assume_tac o uex_expand) >>
qby_tac ‘App(Nrec(x0, f0), n) = x' & x = x'’ 
>-- (strip_tac >> first_x_assum irule >> arw[]) >>
arw[])
(form_goal “!X x0 f0:X->X.!n x. App(Nrec(x0,f0),n) = x <=> IN(Pair(n,x),Ninds(f0,x0))”));


val Nrec_Suc = prove_store("Nrec_Suc",
e0
(rpt strip_tac >>
 qsspecl_then [‘x0’,‘f0’,‘Suc(n)’] assume_tac Nrec_def >>
 drule $ iffLR Nind_cases >> fs[Pair_eq_eq,Suc_NONZERO,Suc_eq_eq] >>
 qsspecl_then [‘nx0’] (x_choosel_then ["n1","x1"] assume_tac) 
 Pair_has_comp >> fs[Pair_def'] >>
 qsuff_tac ‘x1 = App(Nrec(x0, f0), n1)’ 
 >-- (strip_tac >> arw[]) >>
 flip_tac >> arw[App_Nrec_Ninds])
(form_goal “!X x0 f0:X->X n. App(Nrec(x0,f0),Suc(n)) = 
 App(f0,App(Nrec(x0,f0),n))”));

val Nrec_unique = prove_store("Nrec_unique",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT] >> ind_with N_induct >>
 arw[Nrec_O,Nrec_Suc] >> rpt strip_tac >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[GSYM App_App_o,Suc_def] >> arw[])
(form_goal
 “!X x0 f:X->X r:N->X. App(r,O) = x0 & 
  r o SUC = f o r ==> r = Nrec(x0,f)”));



val Nrec_Suc_eqn = Nrec_Suc |> rewr_rule[GSYM App_App_o,Suc_def] 
                            |> spec_all
                            |> qgen ‘n’
                            |> mp (FUN_EXT |> qspecl
                                           [‘N’,‘X’,‘Nrec(x0, f0:X->X) o SUC’,
                                            ‘f0 o Nrec(x0, f0:X->X)’] 
                                           |> iffLR) |> qgenl [‘X’,‘x0’,‘f0’]
                            |> store_as "Nrec_Suc_eqn";

val El_def = 
    fun_tm_compr (dest_var (rastt "d:mem(1)")) (rastt "a:mem(A)")
                 |> qSKOLEM "El" [‘a’]
                 |> allE (rastt "dot")
                 |> gen_all |> store_as "El_def";



val El_eq_eq = prove_store("El_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 drule $ iffRL FUN_EXT >>
 first_x_assum (qspecl_then [‘dot’] assume_tac) >>
 fs[El_def])
(form_goal
 “!A a:mem(A) b. El(a) = El(b) <=> a = b”));


val App_o_El = prove_store("App_o_El",
e0
(rpt strip_tac >> rw[App_App_o,El_def])
(form_goal
 “!A B f:A->B.
  !a. App(f,a) = App(f o El(a),dot)”));

val Nrec_El = prove_store("Nind_el",
e0
(rpt strip_tac (* 3 *)
 >-- rw[GSYM FUN_EXT,App_App_o,dot_def,El_def,Nrec_O]  
 >-- (rw[GSYM FUN_EXT,App_App_o,dot_def,El_def,Nrec_Suc] >>
     rw[GSYM App_App_o,Nrec_Suc_eqn]) >>
 irule Nrec_unique >> arw[] >>
 rev_drule $ iffRL FUN_EXT >>
 first_x_assum (qspecl_then [‘dot’] assume_tac) >>
 fs[App_App_o,El_def])
(form_goal
 “!X a f:X->X.  Nrec(a,f) o El(O) = El(a) & 
   Nrec(a,f) o SUC = f o Nrec(a,f) &
 (!u. (u o El(O) = El(a) & u o SUC = f o u) ==> u = Nrec(a,f))”));


 
val App_El_mem = prove_store("App_El_mem",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (irule $ iffLR FUN_EXT >> strip_tac >> 
     arw[App_App_o,El_def,dot_def]) >>
 qby_tac ‘App(f o El(a),dot) = App(El(b),dot)’ 
 >-- arw[] >>
 pop_assum mp_tac >> rw[App_App_o,El_def])
(form_goal
 “!A B f:A->B.!a b. App(f,a) = b <=>
 f o El(a) = El(b)”));



val Nrec_O_SUC = prove_store("Nrec_O_SUC",
e0
(flip_tac >> irule Nrec_unique >> rw[IdL,IdR,Id_def])
(form_goal
 “Nrec(O,SUC) = Id(N)”));
 
val comm_with_SUC_id0 = prove_store("comm_with_SUC_id0",
e0
(rpt strip_tac >> rw[GSYM Nrec_O_SUC] >> 
 irule Nrec_unique >> arw[])
(form_goal
 “!f:N->N. App(f,O) = O & f o SUC = SUC o f ==> f = Id(N)”));


val comm_with_SUC_id = prove_store("comm_with_SUC_id",
e0
(rpt strip_tac >> irule comm_with_SUC_id0 >> arw[] >>
 rev_drule $ iffRL FUN_EXT >> 
 first_x_assum (qspecl_then [‘dot’] assume_tac) >>
 fs[App_App_o,El_def])
(form_goal
 “!f:N->N. f o El(O) = El(O) & f o SUC = SUC o f ==> f = Id(N)”));




val Thm1_case1_comm_condition = prove_store(
"Thm1_case1_comm_condition",
e0
(rw[Pa_distr,Pa_eq_eq,IdL,o_assoc,p12_of_Pa,IdL,IdR] >>
(*stupid*)
rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal
 “!B f0:N->B g:1->B h:N * B -> B.
 (f0 o El(O) = g & f0 o SUC = h o Pa(Id(N),f0) <=>
 Pa(Id(N),f0) o El(O) = Pa(El(O),g) &
 Pa(SUC o p1(N,B),h) o Pa(Id(N),f0) = Pa(Id(N),f0) o SUC)”));




val Dot_def = qdefine_fsym ("Dot",[‘f:1->A’]) ‘App(f:1->A,dot)’
                           |> gen_all |> store_as "Dot_def";


val Dot_of_El = prove_store("Dot_of_El",
e0
(rw[El_def,Dot_def])
(form_goal
 “!A a:mem(A).Dot(El(a)) = a”));


val El_of_Dot = prove_store("El_of_Dot",
e0
(rw[El_def,Dot_def,dot_def,GSYM FUN_EXT])
(form_goal
 “!X f:1->X. El(Dot(f)) = f”));


 
val to_P_component = prove_store("to_P_component",
e0
(rpt strip_tac >> flip_tac >> irule is_Pa >> rw[])
(form_goal
 “!A B X f:X->A * B.  Pa(p1(A,B) o f,p2(A,B) o f) = f”));


val is_Nrec = Nrec_unique 


val Thm1_case_1 = prove_store("Thm1_case_1",
e0
(rpt strip_tac >> uex_tac >> 
 qabbrev_tac ‘Nrec(Dot(Pa(El(O),g:1->B)),Pa(SUC o p1(N,B),h:N * B->B)) = f'’ >>
 qabbrev_tac ‘p2(N,B) o f':N->N * B = f’ >>
 qexists_tac ‘f’ >>
 qsspecl_then [‘Dot(Pa(El(O), g))’,‘Pa(SUC o p1(N, B), h)’] strip_assume_tac
 Nrec_El >> rfs[] >>
 qby_tac ‘p1(N,B) o f' = Id(N)’ >--
 (irule comm_with_SUC_id >> arw[o_assoc,p12_of_Pa,El_of_Dot,Pa_distr]) >>
 qby_tac ‘f' = Pa(Id(N),f)’ >-- 
 (irule is_Pa >> arw[]) >>
 qby_tac ‘f o El(O) = g & f o SUC = h o Pa(Id(N), f)’
 >-- (qpick_x_assum ‘p2(N, B) o f' = f’ (assume_tac o GSYM) >>
      once_arw[] >> pop_assum (K all_tac) >> rw[o_assoc] >> once_arw[] >>
      rw[GSYM o_assoc] >> arw[p12_of_Pa,El_of_Dot]) >>
 once_arw[] >> rw[] >>  
 rpt strip_tac >>  
 qsuff_tac ‘Pa(Id(N), f'') = Pa(Id(N), f)’ 
 >-- rw[Pa_eq_eq] >>
 qsuff_tac ‘Pa(Id(N), f'') = f'’ >-- arw[] >>
 qsuff_tac ‘Pa(Id(N), f'') = 
  Nrec(Dot(Pa(El(O), g)), Pa(SUC o p1(N, B), h))’ >-- arw[] >>
 irule Nrec_unique >>  
 arw[Pa_distr,o_assoc,IdL,Dot_def,p12_of_Pa,IdR] >>
 rw[App_Pa_distr,Pair_eq_eq,Id_def,El_def] >>
 qby_tac ‘App(f'' o El(O),dot) = App(g,dot)’
 >-- arw[] >> pop_assum mp_tac >>
 rw[App_App_o,El_def])
(form_goal
 “!B g:1->B h:N * B -> B. 
   ?!f:N->B. f o El(O) = g & f o SUC = h o Pa(Id(N),f)”));





val Tp1_ex = prove_store("Tp1_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(f o p1(A,1))’ >> rw[])
(form_goal
“!A B f:A->B.?tpf:1->Exp(A,B).Tp(f o p1(A,1)) = tpf”));

val Tp1_def = Tp1_ex |> spec_all |> qSKOLEM "Tp1" [‘f’]
                     |> gen_all
                     |> store_as "Tp1_def";


val Ev_of_Tp = prove_store("Ev_of_Tp",
e0
(rw[Tp_def])
(form_goal
 “!A B X f:A * X ->B. 
  Ev(A,B) o Pa(p1(A,X),Tp(f) o p2(A,X)) = f”));


val Tp_eq = prove_store("Tp_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qsspecl_then [‘f’] assume_tac Ev_of_Tp >>
 qsspecl_then [‘g’] assume_tac Ev_of_Tp >>
 rfs[])
(form_goal
 “!A B X f:A * X ->B g:A * X ->B.(Tp(f) = Tp(g) <=> f = g)”));





val Ev_eq_eq = prove_store("Ev_eq_eq",
e0
(rpt strip_tac >> 
 qsuff_tac ‘f = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X))) & 
  g = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X)))’
 >-- (rpt strip_tac >> once_arw[] >> rw[]) >> strip_tac 
 >> irule is_Tp >> arw[])
(form_goal
 “!A B X f g. (Ev(A,B) o Pa(p1(A,X),f o p2(A,X)) = 
              Ev(A,B) o Pa(p1(A,X),g o p2(A,X)) ==> f = g)”));


val to_P_eq = prove_store("to_P_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f = Pa(p1(A,B) o g,p2(A,B) o g) &
            g = Pa(p1(A,B) o g,p2(A,B) o g)’ >--
 (strip_tac >> once_arw[] >> rw[]) >>
 strip_tac >> irule is_Pa >> arw[])
(form_goal
 “!A B X f:X->A * B g:X->A * B.  p1(A,B) o f = p1(A,B) o g &
 p2(A,B) o f = p2(A,B) o g ==> f = g”));



val Pa_o_split = prove_store("Pa_o_split",
e0
(rpt strip_tac >> irule to_P_eq >>
 rw[p12_of_Pa,Pa_distr,o_assoc])
(form_goal
 “!B X f:B->X Y g:X->Y.  !A.Pa(p1(A,B),g:X->Y o f o p2(A,B)) = 
  Pa(p1(A,X), g o p2(A,X)) o Pa(p1(A,B),f o p2(A,B))”));


val Thm1_comm_eq_left = prove_store(
"Thm1_comm_eq_left",
e0
(rpt strip_tac >> 
 qby_tac ‘Pa(p1(A,1), Tp(f) o El(O) o p2(A,1)) = 
 Pa(p1(A,N),Tp(f) o p2(A,N)) o Pa(p1(A,1),El(O) o p2(A,1))’
 >-- rw[Pa_o_split] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qsuff_tac ‘f o Pa(p1(A, 1), El(O) o p2(A, 1)) = 
                 Ev(A,B) o Pa(p1(A,1),(Tp(f) o El(O)) o p2(A,1)) &
             g o p1(A, 1) = 
                 Ev(A,B) o Pa(p1(A,1),Tp1(g) o p2(A,1))’
     >-- (strip_tac >> fs[]) >> strip_tac (* 2 *)
     >-- (arw[o_assoc] >> 
         qsspecl_then [‘f’] assume_tac Ev_of_Tp >> rfs[GSYM o_assoc]) >>
     rw[GSYM Tp1_def] >>
     qsspecl_then [‘g o p1(A,1)’] assume_tac Ev_of_Tp >> rfs[]) >>
 rw[GSYM Tp1_def] >> irule is_Tp >>
 arw[o_assoc] >> rw[GSYM o_assoc] >>
 qsspecl_then [‘f’] assume_tac Ev_of_Tp >> rfs[])
(form_goal
 “!A B f: A * N ->B g:A->B.
  (Tp(f) o El(O) = Tp1(g) <=> f o Pa(p1(A,1),El(O) o p2(A,1)) = g o p1(A,1))”));



val Pa_p1_p2 = prove_store("Pa_p1_p2",
e0
(rpt strip_tac >> flip_tac >> irule is_Pa >> rw[IdR])
(form_goal
 “!A B. Pa(p1(A,B),p2(A,B)) = Id(A * B)”));


val Thm1_comm_eq_right = prove_store("Thm1_comm_eq_right",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘Tp(h o l) o Pa(Id(N),Tp(f)) = Tp(h o Pa(Id(A * N),f)) & 
  Tp(f o Pa(p1(A,N), SUC o p2(A,N))) = Tp(f) o SUC’
 >-- (strip_tac >> dimp_tac >> strip_tac (* 2 *)
      >-- arw[] >>
      irule $ iffLR Tp_eq >> arw[] >>
      qpick_x_assum
      ‘Tp((h o l)) o Pa(Id(N), Tp(f)) =
       Tp(h o Pa(Id(A * N), f))’
      (assume_tac o GSYM) >> arw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Tp >> 
        qby_tac
        ‘Pa(p1(A, N), (Tp((h o l)) o Pa(Id(N), Tp(f))) o p2(A, N))=
  Pa(p1(A,N * Exp(A,B)), Tp(h o l) o p2(A,N * Exp(A,B))) o 
  Pa(p1(A,N),Pa(Id(N),Tp(f)) o p2(A,N))’ >-- 
  rw[o_assoc,Pa_o_split] >> 
  once_arw[] >> rw[GSYM o_assoc] >>
  qsspecl_then [‘h o l’] assume_tac Ev_of_Tp >> rfs[] >>
  rw[o_assoc] >> 
  qsuff_tac
  ‘l o Pa(p1(A, N), Pa(Id(N), Tp(f)) o p2(A, N)) = 
   Pa(Id(A * N), f)’ >--
  (strip_tac >> arw[]) >>
  irule to_P_eq >> arw[] >> 
  qpick_x_assum
  ‘Pa(Pa(p1(A, N * Exp(A, B)), p1(N, Exp(A, B)) o p2(A, N * Exp(A, B))),
                Ev(A, B) o
                Pa(p1(A, N * Exp(A, B)), p2(N, Exp(A, B)) o
                 p2(A, N * Exp(A, B)))) = l’
  (assume_tac o GSYM) >> arw[] >>
  rw[GSYM o_assoc] >>
  rw[p12_of_Pa,Pa_distr,o_assoc,Ev_of_Tp,IdL,Pa_p1_p2]) >>
 flip_tac >> irule is_Tp >> arw[] >> 
 qby_tac
 ‘Pa(p1(A, N), (Tp(f) o SUC) o p2(A, N)) = 
  Pa(p1(A, N), Tp(f) o p2(A,N)) o Pa(p1(A,N),SUC o p2(A,N))’
 >-- rw[o_assoc,Pa_o_split] >>
 arw[GSYM o_assoc] >> 
 qsspecl_then [‘f’] assume_tac Ev_of_Tp >> rfs[]
 )
(form_goal
 “!A B f:A * N ->B h: (A * N) * B ->B. !l . 
Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l
 ==>
 (h o Pa(Id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N)) <=>
 Tp(h o l) o Pa(Id(N),Tp(f)) = Tp(f) o SUC)”));


val Ev_of_Tp_el = prove_store("Ev_of_Tp_el",
e0
(rpt strip_tac >>
 assume_tac Ev_of_Tp >> 
 first_x_assum (qspecl_then [‘A’,‘B’,‘X’,‘f’] assume_tac) >>
 qby_tac 
 ‘Pa(a, Tp(f) o x) = Pa(p1(A, X), Tp(f) o p2(A, X)) o Pa(a,x)’ >--
 (irule to_P_eq >> rw[p12_of_Pa] >> 
  rw[p12_of_Pa,GSYM o_assoc] >> rw[o_assoc,p12_of_Pa]) >>
 arw[GSYM o_assoc])
(form_goal
 “!A B X f:A * X ->B P a:P->A x: P ->X. 
  Ev(A,B) o Pa(a, Tp(f) o x) = f o Pa(a,x)”));



val Ev_of_Tp_el' = prove_store("Ev_of_Tp_el'",
e0
(rpt strip_tac >> 
 qby_tac ‘Tp(f) = Tp(f) o Id(P)’ >-- rw[IdR] >>
 once_arw[] >> rw[Ev_of_Tp_el])
(form_goal
“!A B P f:A * P -> B  a:P -> A.
Ev(A, B) o Pa(a, Tp(f)) = f o Pa(a, Id(P))”));


val Tp_of_Ev = prove_store("Tp_of_Ev",
e0
(flip_tac >> irule is_Tp >> rw[])
(form_goal
 “Tp((Ev(A, B) o Pa(p1(A, X), f o p2(A, X)))) = f”));


val Thm1 = prove_store("Thm1",
e0
(rpt strip_tac >>
 abbrev_tac “Tp(g:A->B o p1(A,1)) = g'” >>
 abbrev_tac “Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l” >>
 abbrev_tac “Tp(h:(A * N) * B->B o l:A * N * Exp(A,B) -> (A * N) * B) = h'” >>
 qspecl_then [‘Exp(A,B)’,‘g'’,‘h'’] assume_tac Thm1_case_1 >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum (x_choose_then "fb" assume_tac) >> 
 qexists_tac ‘Ev(A,B) o Pa(p1(A,N),fb o p2(A,N)) ’ >>
 rw[GSYM Thm1_comm_eq_left] >>
 qspecl_then [‘A’,‘B’,‘Ev(A,B) o Pa(p1(A,N),fb o p2(A,N))’] assume_tac
 Thm1_comm_eq_right >> first_x_assum drule >>
 rpt strip_tac >> dimp_tac >> strip_tac >--
 (qspecl_then [‘A’,‘B’,‘f0’] assume_tac 
 Thm1_comm_eq_right >> first_x_assum drule >> rfs[] >>
 qsuff_tac ‘fb = Tp(f0)’ 
 >-- (strip_tac >> arw[Ev_of_Tp]) >>
 qsspecl_then [‘g'’,‘h'’] assume_tac Thm1_case_1 >>
 pop_assum (assume_tac o uex_expand) >> 
 pop_assum strip_assume_tac >>
 qsuff_tac ‘fb = f & Tp(f0 ) = f’
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[GSYM Tp1_def]) >> 
 once_arw[] >> strip_tac (* 2 *)
 >-- (rw[GSYM Tp1_def] >> irule is_Tp >> 
 rw[Pa_o_split,o_assoc,Ev_of_Tp_el] >>
 rw[Pa_o_split,GSYM o_assoc,Ev_of_Tp_el] >>
 rw[o_assoc,p12_of_Pa,Pa_distr] >> irule $ iffLR Tp_eq >>
 flip_tac >> arw[GSYM o_assoc] >> irule is_Tp >> rw[]) >>
 first_x_assum $ irule o iffRL >> rw[Tp_of_Ev] >> arw[])
(form_goal
 “!A B g:A->B h:(A * N) * B ->B. 
 ?f:A * N ->B. !f0.
 (f0 o Pa(p1(A,1),El(O) o p2(A,1)) = g o p1(A,1) & 
  h o Pa(Id(A * N),f0) = f0 o Pa(p1(A,N), SUC o p2(A,N))) <=> f0 = f”));

val PRE_def0 = 
    Thm1_case_1 |> specl (List.map rastt ["N","El(O)","p1(N,N)"])
                |> uex_expand 
                |> qSKOLEM "PRE" []


val Pre_def = qdefine_fsym ("Pre",[‘n:mem(N)’]) ‘App(PRE,n)’ 
                           |> gen_all |> store_as "Pre_def";


val PRE_def = prove_store("PRE_def",
e0
(assume_tac PRE_def0 >> fs[p12_of_Pa])
(form_goal
 “ PRE o El(O) = El(O) & PRE o SUC = Id(N)”));


val Pre_eqn = prove_store("Pre_eqn",
e0
(strip_assume_tac PRE_def >> 
 qby_tac
 ‘App(PRE o El(O),dot) = App(El(O),dot)’ 
 >-- arw[] >> fs[El_def] >>
 fs[App_App_o,El_def,Pre_def] >> strip_tac >>
 qby_tac ‘App(PRE o SUC,n) = App(Id(N),n)’ 
 >-- arw[] >>
 fs[App_App_o,Pre_def,Suc_def,Id_def])
(form_goal
 “Pre(O) = O & !n. Pre(Suc(n)) = n”));



val ADD_def = 
 Thm1 |> sspecl (List.map rastt ["Id(N)","SUC o p2(N * N,N)"])
      |> qSKOLEM "ADD" []
      |> rewr_rule[o_assoc,p12_of_Pa,IdL]
      |> qspec ‘ADD’ |> rewr_rule[To1_def]
      |> store_as "ADD_def";
        

val Add_def = qdefine_fsym ("Add",[‘n1:mem(N)’,‘n2:mem(N)’]) ‘App(ADD,Pair(n1,n2))’ |> gen_all |> store_as "Add_def";


val App_input_eq =prove_store("App_input_eq",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!A B f:A->B a1 a2.a1 = a2 ==> App(f,a1) = App(f,a2)”))




(* (∀n. 0 + n = n) ∧ ∀m n. SUC m + n = SUC (m + n)*)
val Add_O = prove_store("Add_O",
e0
(strip_tac >> 
 assume_tac ADD_def >>
 qby_tac ‘App(ADD o Pa(p1(N, 1), El(O) o To1(N * 1)),Pair(n,dot)) = 
  App(p1(N, 1),Pair(n,dot))’
 >-- arw[] >>
 pop_assum mp_tac >> 
 rw[p12_of_Pair,App_App_o,App_Pa_distr,dot_def,El_def,Add_def])
(form_goal
 “!n. Add(n,O) = n”));


val Add_Suc = prove_store("Add_Suc",
e0
(rpt strip_tac >> assume_tac ADD_def >>
 qby_tac ‘App(SUC o ADD,Pair(m,n)) =
          App(ADD o Pa(p1(N, N), SUC o p2(N, N)),Pair(m,n))’
 >-- arw[] >>
 pop_assum mp_tac >> rw[App_App_o,App_Pa_distr,p12_of_Pair,Suc_def,Add_def] >>
 strip_tac >> arw[])
(form_goal
 “(!m n.Add(m,Suc(n)) = Suc(Add(m,n)))”));

val Pre_O = conjE1 Pre_eqn |> store_as "Pre_O";

val Pre_Suc = conjE2 Pre_eqn |> store_as "Pre_Suc";


val SUB_def = Thm1 |> specl
(List.map rastt ["N","N","Id(N)","PRE o p2(N * N,N)"])
|> qSKOLEM "SUB" []
|> qspec ‘SUB’ |> rewr_rule[IdL,o_assoc,p12_of_Pa]
|> store_as "SUB_def";



val o_eq_r = prove_store("o_eq_r",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!A B f1:A->B f2:A->B. f1 = f2 ==>
  !C g:B->C. g o f1 = g o f2”));


val Sub_def = qdefine_fsym ("Sub",[‘n1:mem(N)’,‘n2:mem(N)’]) ‘App(SUB,Pair(n1,n2))’ |> gen_all |> store_as "Sub_def";



val Sub_O = prove_store("Sub_O",
e0
(strip_tac >> strip_assume_tac SUB_def >>
 qby_tac 
 ‘App(SUB o Pa(p1(N, 1), El(O) o p2(N, 1)),Pair(n,dot)) = 
      App(p1(N, 1),Pair(n,dot))’
 >-- arw[] >> 
 pop_assum mp_tac >>
 rw[App_App_o,p12_of_Pair,App_Pa_distr,El_def,Sub_def])
(form_goal
 “!n. Sub(n,O) = n”));


val Sub_Suc = prove_store("Sub_Suc",
e0
(rpt strip_tac >> strip_assume_tac SUB_def >> 
 qby_tac
 ‘App(PRE o SUB,Pair(m,n)) =
  App(SUB o Pa(p1(N, N), SUC o p2(N, N)),Pair(m,n))’ 
 >-- arw[] >> pop_assum mp_tac >>
 rw[App_App_o,App_App_o,p12_of_Pair,App_Pa_distr,Pre_def,Sub_def,Suc_def] >>
 strip_tac >> arw[])
(form_goal
 “!m n. Sub(m,Suc(n)) = Pre(Sub(m,n))”));



val Pre_O_cases = prove_store("Pre_O_case",
e0
(strip_tac >> cases_on “n = O” >> arw[Pre_O] >>
 fs[O_xor_Suc] >> dimp_tac >> strip_tac (* 2 *)
 >> fs[Pre_Suc] >> fs[Suc_eq_eq])
(form_goal
 “!n. Pre(n) = O <=> (n = O | n = Suc(O))”));

val Pre_eq_O = Pre_O_cases


val Le_def = qdefine_psym ("Le",[‘m:mem(N)’,‘n:mem(N)’])
                          ‘Sub(m,n) = O’
             |> gen_all |> store_as "Le_def";

val Lt_def = qdefine_psym ("Lt",[‘m:mem(N)’,‘n:mem(N)’])
                          ‘Le(m,n) & ~(m = n)’
             |> gen_all |> store_as "Lt_def";



(*val SUB_EQ_00 = Le_def*)

val Le_O = prove_store("Le_O",
e0
(rw[Le_def,Sub_O])
(form_goal
 “!n. Le(n,O) ==> n = O”));


val Lt_Le = prove_store("Lt_Le",
e0
(once_rw[Lt_def] >> rpt strip_tac >> arw[])
(form_goal
 “!m n. Lt(m,n) ==> Le(m,n)”));

val Lt_NE = prove_store("Lt_NEQ",
e0
(rw[Lt_def] >> rpt strip_tac >> arw[])
(form_goal
 “!m n. Lt(m,n) ==> ~(m = n)”));

val Le_NE_Lt = prove_store("Le_NE_Lt",
e0
(rw[Lt_def])
(form_goal
 “!m n. Le(m,n) & ~(m = n) ==> Lt(m,n)”));

val Lt_Le_NE = Lt_def

val NOT_Lt_O = prove_store("NOT_Lt_O",
e0
(rw[Lt_def] >> rpt strip_tac  >> ccontra_tac  >> fs[] >> drule Le_O >> fs[])
(form_goal
 “!n.~(Lt(n,O))”));

val Sub_mono_eq = prove_store("Sub_mono_eq",
e0
(strip_tac >>
 ind_with N_induct >> rw[Sub_O,Sub_Suc] >> 
 rpt strip_tac (* 2 *) >-- rw[Pre_Suc] >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!m n. Sub(Suc(m),Suc(n)) = Sub(m,n)”));


val Add_Sub = prove_store("Add_Sub",
e0
(ind_with N_induct >-- rw[Add_O,Sub_O] >> rpt strip_tac >>
 arw[Add_Suc,Sub_mono_eq])
(form_goal
 “!c a. Sub(Add(a,c),c) = a”));

val Add_O2 = prove_store("Add_O2",
e0
(ind_with N_induct >-- rw[Add_Suc,Add_O] >> 
 rpt strip_tac >> arw[])
(form_goal
 “!n. Add(O,n) = n”));


val Sub_EQ_O = prove_store("Sub_EQ_O",
e0
(rpt strip_tac >>
 qsspecl_then [‘n’,‘O’] assume_tac Add_Sub >> fs[Add_O2])
(form_goal
 “!n.Sub(n,n) = O”));

val Le_refl = prove_store("Le_refl",
e0
(rw[Le_def,Sub_EQ_O])
(form_goal
 “!n. Le(n,n)”));

val Le_O_O = Le_O;


val o_eq_l = prove_store("o_eq_l",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!B C g1:B->C g2:B->C. g1 = g2 ==>
  !A f:A->B. g1 o f = g2 o f”));

val Le_cases = prove_store("Le_cases",
e0
(rw[Lt_def] >> rpt strip_tac >> arw[] >> 
 cases_on “m:mem(N) = n” >> arw[])
(form_goal
 “!m n. Le(m,n) ==> (Lt(m,n) | m = n)”));

val Le_Sub = Le_def;

(*“!p n m.((p <= n) /\ (p <= m)) ==> (((n - p) = (m - p)) = (n = m))”*)

val Suc_NONZERO = SUC_NONZERO |> rewr_rule[GSYM Suc_def]
                              |> store_as "Suc_NONZERO";

val th = N_induct 

val cancel_Sub = prove_store("cancel_Sub",
e0
(ind_with N_induct >> rw[Sub_O] >> 
 strip_tac >> strip_tac >> 
 ind_with N_induct >> strip_tac >--
 (rpt strip_tac >> fs[Le_Sub,Sub_O,Suc_NONZERO]) >>
 strip_tac>> strip_tac >> 
 ind_with N_induct >> strip_tac
 >-- fs[Le_def,Sub_O,Suc_NONZERO] >>
 rw[Sub_mono_eq,Le_def] >> rpt strip_tac >> rw[Suc_eq_eq] >>
 first_x_assum irule >> arw[Le_def])
(form_goal
 “!a b c.Le(a,b) & Le(a,c) ==>(Sub(b,a) = Sub(c,a) <=> b = c)”));


val Sub_of_O = prove_store("Sub_of_O",
e0
(ind_with N_induct >> rw[Sub_O,Sub_Suc] >> rpt strip_tac>>
 arw[Pre_O])
(form_goal
 “!n.Sub(O,n) = O”));


val O_LESS_EQ = prove_store("O_LESS_EQ",
e0
(rw[Le_def,Sub_of_O])
(form_goal
 “!x. Le(O,x)”));

val LESS_EQ_MONO = prove_store("LESS_EQ_MONO",
e0
(rw[Le_def,Sub_mono_eq])
(form_goal
 “!m n. Le(Suc(m),Suc(n)) <=> Le(m,n)”));


val LESS_O = prove_store("LESS_O",
e0
(rw[Lt_def,GSYM Suc_NONZERO,O_LESS_EQ])
(form_goal
 “!n. Lt(O,Suc(n))”));

val LESS_MONO_EQ = prove_store("LESS_MONO_EQ",
e0
(rw[Lt_def,LESS_EQ_MONO,Suc_eq_eq])
(form_goal
 “!m n. Lt(Suc(m),Suc(n)) <=> Lt(m,n)”));


val LE_O_iff = prove_store("LE_O_iff",
e0
(strip_tac >> dimp_tac >> strip_tac  
 >-- (drule Le_O>> arw[]) >>
 arw[Le_def,Sub_O])
(form_goal
 “!n. Le(n,O) <=> n = O”));

val LESS_cases = prove_store("LESS_cases",
e0
(ind_with N_induct >> strip_tac (* 2 *)
 >-- (rw[LE_O_iff] >> rw[Lt_def,O_LESS_EQ] >> strip_tac >>
     cases_on “O = b” >> arw[]) >>
 strip_tac >> strip_tac >>
 ind_with N_induct >> 
 rw[O_LESS_EQ] >> rw[LESS_MONO_EQ,LESS_EQ_MONO] >> arw[])
(form_goal
 “!a b. Lt(a,b) | Le(b,a)”));

 
val LESS_EQ_cases = prove_store("LESS_EQ_cases",
e0
(assume_tac LESS_cases >> fs[Lt_def] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘m’,‘n’] strip_assume_tac) >> arw[])
(form_goal
 “!m n. Le(m,n) | Le(n,m)”));


val Add_Suc1 = prove_store("Add_Suc1",
e0
(ind_with N_induct >> strip_tac >> rw[Add_O] >>
 rpt strip_tac >> rw[Add_Suc] >> arw[])
(form_goal
 “!b a. Add(Suc(a),b) = Suc(Add(a,b))”));

val Add_comm = prove_store("Add_comm",
e0
(ind_with N_induct >> rw[Add_O,Add_O2] >> rpt strip_tac >>
 rw[Add_Suc] >> arw[] >> rw[Add_Suc1] )
(form_goal
 “!b a. Add(a,b) = Add(b,a)”));


val Suc_Sub = prove_store("Suc_Sub",
e0
(strip_tac >> qspecl_then [‘n’,‘Suc(O)’] assume_tac Add_Sub >> 
 fs[Add_Suc1,Add_O,Add_O2])
(form_goal “!n.Sub(Suc(n),n) = Suc(O)”));




val Sub_DIFF_1 = prove_store("Sub_DIFF_1",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule $ iffLR cancel_Sub >> qexists_tac ‘b’ >>
      assume_tac Suc_Sub >> once_arw[] >> rw[] >>
      qsuff_tac ‘~(Le(a,b)) & ~ (Le(Suc(b),b))’ 
      >-- (strip_tac >> assume_tac LESS_EQ_cases >> 
          first_assum (qspecl_then [‘a’,‘b’] assume_tac) >> fs[] >>
          first_assum (qspecl_then [‘Suc(b)’,‘b’] assume_tac) >> fs[]) >>
      rw[Le_def] >> arw[Suc_Sub] >> rw[Suc_NONZERO]) >>
 arw[] >> rw[Suc_Sub])
(form_goal
 “!a b.Sub(a,b) = Suc(O) <=> a = Suc(b)”));


val Pre_O_cases = prove_store("Pre_O_cases",
e0
(strip_tac >> cases_on “n = O” (* 2 *)
 >-- arw[Pre_O] >>
 arw[] >> dimp_tac >> strip_tac (* 2 *) 
 >-- (fs[O_xor_Suc,Suc_eq_eq] >> rfs[Pre_Suc]) >>
 arw[Pre_Suc])
(form_goal
“!n. Pre(n) = O <=> (n = O | n = Suc(O))”));

val Sub_Suc_O_cases = prove_store("Sub_Suc_O_cases",
e0
(rpt strip_tac >> fs[Sub_Suc,Pre_O_cases,Sub_DIFF_1])
(form_goal
 “!a b. Sub(a,Suc(b)) = O ==> a = Suc(b) | Sub(a,b) = O”));

val Le_cases_iff = prove_store("LE_cases_iff",
e0
(rw[Lt_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[Le_refl] >>
 cases_on “a = b:mem(N)” >> arw[])
(form_goal
 “!a b. Le(a,b) <=> Lt(a,b) | a = b”));

val Sub_EQ_O1 = GSYM Le_def

val Lt_Suc_Le = prove_store("Lt_Suc_Le",
e0
(rw[Le_cases_iff] >> rw[Lt_def,Le_def,Sub_Suc,Pre_O_cases,Sub_DIFF_1] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] (* 4 *)
 >-- (cases_on “a = b:mem(N)” >> arw[]) 
 >-- (ccontra_tac >> fs[Suc_Sub] >> fs[Suc_NONZERO]) 
 >-- (disj1_tac >> rw[GSYM Le_def,Le_refl]) >>
 qspecl_then [‘Suc(b)’,‘b’] assume_tac Sub_DIFF_1 >> fs[] >>
 ccontra_tac >> pop_assum (assume_tac o GSYM) >> fs[] >>
 fs[Sub_EQ_O] >> qpick_x_assum ‘O = Suc(O)’ (assume_tac o GSYM) >>
 fs[Suc_NONZERO])
(form_goal
 “!a b. Lt(a,Suc(b)) <=> Le(a,b)”));

(*
fun thml_eq_pairs (th:thm,(ll,rl,asml)) = 
    if is_eq (concl th) then  
        let 
            val (l,r) = dest_eq (concl th)
            val asm = ant th
        in 
            (l::ll,r::rl,asml_U [asm,asml])
        end
    else 
        raise ERR ("thml_eq_pairs.input thm is not an equality: ",
                   [],[],[concl th])


fun EQ_fVar P thml = 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in 
            mk_thm (contl_U (List.map cont thml),asml,
                 mk_dimp (mk_fvar P ll) (mk_fvar P rl))
        end
*)

val NOT_Lt_O = prove_store("NOT_Lt_O",
e0
(rw[Lt_def] >> rpt strip_tac >> ccontra_tac >>
 pop_assum (strip_assume_tac) >> drule Le_O >> fs[])
(form_goal
 “!n. ~(Lt(n,O))”));


val strong_ind = prove_store("strong_ind",
e0
(rpt strip_tac >>
 suffices_tac
 “!a:mem(N). (!a0:mem(N). Le(a0,a) ==> P(a0))”
 >-- (strip_tac >> 
      pop_assum (qspecl_then [‘a:mem(N)’,‘a’] assume_tac) >>
      first_assum irule >> rw[Le_refl]) >>
 ind_with N_induct >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> drule Le_O >>  
      assume_tac $ EQ_psym "P" [assume “a0 = O”] >>
      first_assum $ irule o iffRL >>
      first_assum irule >> rpt strip_tac >>
      pop_assum mp_tac >> rw[NOT_Lt_O]) >>
 rpt strip_tac >> drule Le_cases >> pop_assum mp_tac >>
 rw[Lt_Suc_Le] >> strip_tac
 >-- (first_assum irule >> first_assum accept_tac) >>
 assume_tac $ EQ_psym "P" [assume “a0 = Suc(n)”] >>
 first_assum $ irule o iffRL >>
 last_x_assum irule  >> rw[Lt_Suc_Le] >> first_x_assum accept_tac)
(form_goal
 “(!a:mem(N).(!a0. Lt(a0,a) ==> P(a0)) ==> P(a)) ==> !a:mem(N). P(a)”));

val WOP = prove_store("WOP",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac ‘!l:mem(N). P(l) ==> ?n:mem(N). P(n) & ~(Le(l,n))’
 >-- (rpt strip_tac >> ccontra_tac >>
      qsuff_tac ‘?a0:mem(N). P(a0) & !a1:mem(N). P(a1)==> Le(a0,a1)’ 
     >-- (rw[]>> first_x_assum accept_tac) >>
     qexists_tac ‘l’ >> strip_tac (* 2 *)
     >-- first_x_assum accept_tac >>
     rpt strip_tac >> ccontra_tac >>
     qby_tac ‘?n:mem(N). P(n) & ~(Le(l,n))’ 
     >-- (qexists_tac ‘a1’ >> strip_tac >> first_x_assum accept_tac) >>
     first_x_assum opposite_tac ) >>
 qsuff_tac ‘!n:mem(N). ~(P(n))’ >-- (rpt strip_tac >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >> 
 first_x_assum opposite_tac) >>
 qsuff_tac ‘!n:mem(N) n0:mem(N). Le(n0,n) ==> ~P(n0)’
 >-- (strip_tac >> rpt strip_tac >> first_x_assum irule >>
     qexists_tac ‘n’ >> rw[Le_refl]) >>
 ind_with N_induct >> rpt strip_tac (* 2 *) >--
 (drule Le_O >>
 assume_tac $ EQ_psym "P" [assume “n0 = O”] >>
 ccontra_tac >> 
 first_x_assum $ drule o iffLR >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >> pop_assum mp_tac >> 
 rw[Le_def,Sub_of_O]) >>
 pop_assum mp_tac >> strip_tac >>
 drule Le_cases >> pop_assum mp_tac >> rw[Lt_Suc_Le] >> strip_tac (* 2 *)
 >-- (first_x_assum drule >> first_x_assum accept_tac) >>
 ccontra_tac >>
 assume_tac $ EQ_psym "P" [assume “n0 = Suc(n)”] >>
 first_x_assum $ drule o iffLR >> 
 last_x_assum drule >> pop_assum strip_assume_tac >>
 qspecl_then [‘n'’,‘Suc(n)’] assume_tac LESS_cases >> 
 cases_on “Lt(n',Suc(n))” >--
 (pop_assum mp_tac >> rw[Lt_Suc_Le] >> ccontra_tac >> first_x_assum drule>>
 first_x_assum opposite_tac) >>
 pop_assum mp_tac >> pop_assum strip_assume_tac >> strip_tac 
 )
(form_goal
 “!a. P(a:mem(N)) ==> ?a0. P(a0) & !a1.P(a1) ==> Le(a0,a1)”));


val MUL_def0 = Thm1 |> qspecl [‘N’,‘N’,‘El(O) o To1(N)’,
                               ‘ADD o Pa(p2(N * N,N),p1(N, N) o p1(N * N,N))’]
                    |> qSKOLEM "MUL" [] |> iffRL
                    |> allE (rastt "MUL") 
                    |> rewr_rule[o_assoc,To1_def,Pa_distr,p12_of_Pa,IdR] 
                    |> store_as "MUL_def0";



val Mul_def = qdefine_fsym ("Mul",[‘n1:mem(N)’,‘n2:mem(N)’]) ‘App(MUL,Pair(n1,n2))’ |> gen_all |> store_as "Mul_def";

val App_Pa2 = App_Pa |> qspecl [‘A’,‘A’,‘Id(A)’]
                     |> rewr_rule[IdL] |> gen_all
                     |> store_as "App_Pa2";

val App_p1_Pair = prove_store("App_p1_Pair",
e0
(rw[Fst_def,Pair_def'])
(form_goal
 “!A B a b. App(p1(A,B),Pair(a,b)) = a”));


val App_p2_Pair = prove_store("App_p2_Pair",
e0
(rw[Snd_def,Pair_def'])
(form_goal
 “!A B a b. App(p2(A,B),Pair(a,b)) = b”));

val Mul_O = prove_store("Mul_O",
e0
(strip_tac >> rw[Mul_def] >> 
 assume_tac MUL_def0 >>
 qby_tac
 ‘App(MUL o Pa(p1(N, 1), El(O) o To1(N * 1)),Pair(n,dot)) =
  App(El(O) o To1(N * 1),Pair(n,dot))’ 
 >-- arw[] >>
 pop_assum mp_tac >> 
 rw[App_App_o,App_Pa_distr,p12_of_Pair,dot_def,El_def])
(form_goal “!n. Mul(n,O) = O”));


val Mul_Suc = prove_store("Mul_Suc",
e0
(rpt strip_tac >> rw[Mul_def,Suc_def] >>
 assume_tac MUL_def0 >>
 qby_tac
 ‘App(ADD o Pa(MUL, p1(N, N)),Pair(n,n0)) = 
  App(MUL o Pa(p1(N, N), SUC o p2(N, N)),Pair(n,n0))’
 >-- arw[] >>
 pop_assum mp_tac >> rw[App_App_o,App_Pa_Pair,p12_of_Pair,Add_def] >>
 strip_tac >> arw[])
(form_goal “!n n0. Mul(n,Suc(n0)) = Add(Mul(n,n0),n)”));

val Mul_LEFT_O = prove_store("Mul_LEFT_O",
e0
(ind_with N_induct >> rw[Mul_O,Mul_Suc,Add_O])
(form_goal “!m. Mul(O,m) = O”));


val Mul_LEFT_1 = prove_store("Mul_LEFT_1",
e0
(ind_with N_induct >> rw[Mul_O,Mul_Suc] >> rpt strip_tac >>
 arw[Add_Suc,Add_O])
(form_goal “!m.Mul(Suc(O),m) = m”));


val Mul_RIGHT_1 = prove_store("Mul_RIGHT_1",
e0
(rw[Mul_Suc,Add_O2,Mul_O])
(form_goal “!m. Mul(m,Suc(O)) = m”));

val Add_comm' = GSYM Add_comm |> store_as "Add_comm'";

val Add_assoc = prove_store("Add_assoc",
e0
(ind_with N_induct >> rw[Add_O,Add_Suc,Add_Suc1,Add_O2] >>
 rpt strip_tac >>arw[])
(form_goal
 “!m n0 p. Add(m,Add(n0,p)) = Add(Add(m,n0),p)”));


val Add_eq_eq = prove_store("Add_eq_eq",
e0
(rpt strip_tac >> 
 qby_tac
 ‘Sub(Add(m,a),a) = Sub(Add(n,a),a)’
 >-- arw[] >>
 fs[Add_Sub])
(form_goal
 “!m n a. Add(m,a) = Add(n,a) ==> m = n”));
 

val Mul_Suc1 = prove_store("Mul_Suc1",
e0
(ind_with N_induct >> 
 rw[Mul_O,Add_O] >> rw[Mul_Suc] >> rpt strip_tac >>
 arw[] >> arw[Add_Suc] >>
 qsspecl_then [‘Suc(n)’,‘ Add(Mul(n', n), n')’] assume_tac Add_comm' >> 
 arw[Add_Suc] >> 
 qsspecl_then [‘n’,‘Mul(n',n)’] assume_tac Add_comm' >> arw[] >>
 rw[GSYM Add_assoc] >> 
 qsspecl_then [‘n’,‘n'’] assume_tac Add_comm' >> arw[])
(form_goal
 “!m n. Mul(Suc(n),m) = Add(m,Mul(n,m))”));


val Mul_clauses = prove_store("Mul_clauses",
e0
(rw[Mul_O,Mul_Suc,Mul_Suc1,Mul_LEFT_1,Mul_RIGHT_1,Mul_LEFT_O] >>
 rpt strip_tac >--
 qsspecl_then [‘n’,‘Mul(m,n)’] accept_tac Add_comm' >> 
 qsspecl_then [‘Mul(m,n)’,‘m’] accept_tac Add_comm')
(form_goal “(!m. (Mul(O,m) = O) & (Mul(m,O) = O) & 
                  (Mul(Suc(O),m) = m) & (Mul(m,Suc(O)) = m)) &
                !m n.(Mul(Suc(m),n) = Add(Mul(m,n),n)) &
                  (Mul(m,Suc(n)) = Add(m,Mul(m,n)))”));


val Mul_comm = prove_store("Mul_comm",
e0
(ind_with N_induct >> rw[Mul_clauses,Suc_def] >>
 rpt strip_tac >> arw[] >>
 qsspecl_then [‘Mul(n',n)’,‘n'’] accept_tac Add_comm')
(form_goal
 “!m n. Mul(m,n) = Mul(n,m)”));


val Add_clauses = prove_store("Add_clauses",
e0
(rw[Add_O,Add_O2,Add_Suc,Add_Suc1])
(form_goal “((!m. Add(O,m) = m & Add(m,O) = m)) & 
            !m n.Add(Suc(m),n) = Suc(Add(m,n)) &
                 Add(m,Suc(n)) = Suc(Add(m,n))”));


val Nind_tac = ind_with N_induct

val RIGHT_DISTR = prove_store("RIGHT_DISTR",
e0
(strip_tac >> strip_tac >> Nind_tac >> rw[Mul_clauses,Add_clauses] >>
 strip_tac >> arw[] >>
 rw[Mul_clauses,Add_clauses,GSYM Add_assoc] >> strip_tac >>
 arw[]>> 
 qsuff_tac ‘Add(n, Add(Mul(m, n'), Mul(n, n'))) = 
            Add(Mul(m, n'), Add(n, Mul(n, n')))’ 
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘Mul(m, n')’,‘Add(n, Mul(n, n'))’] assume_tac Add_comm' >>
 arw[] >> 
 rw[GSYM Add_assoc] >>
 qsspecl_then [‘Mul(m, n')’,‘Mul(n, n')’] assume_tac Add_comm' >> arw[]
 )
(form_goal “!m n p. Mul(Add(m,n),p) = Add(Mul(m,p),Mul(n,p))”));



val LEFT_DISTR = prove_store("LEFT_DISTR",
e0
(rpt strip_tac >>
 qsspecl_then [‘p’,‘Add(m,n)’] assume_tac Mul_comm >> arw[RIGHT_DISTR] >>
 qsspecl_then [‘p’,‘m’] assume_tac Mul_comm >> arw[] >>
 qsspecl_then [‘p’,‘n’] assume_tac Mul_comm >> arw[])
(form_goal “!m n p. Mul(p,Add(m,n)) = Add(Mul(p,m),Mul(p,n))”));



val Mul_assoc = prove_store("Mul_assoc",
e0
(Nind_tac>>
 rw[Mul_clauses,RIGHT_DISTR] >> rpt strip_tac >>
 arw[] >> rw[GSYM Add_assoc])
(form_goal “!m n p. Mul(m,Mul(n,p)) = Mul(Mul(m,n),p)”));


val Sub_Add = prove_store("SUB_Add",
e0
(Nind_tac >> rw[Sub_of_O] >> strip_tac >>
 strip_tac >> Nind_tac >>
 rw[Add_O2,Sub_O] >> strip_tac >> strip_tac >>
 Nind_tac  >> rw[Sub_O,Add_O] >> rpt strip_tac >>
 rw[Add_Suc1] >> rw[Sub_mono_eq] >> arw[])
(form_goal “!a b c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”));


val Le_O_iff = prove_store("Le_O_iff",
e0
(strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (drule Le_O >> arw[]) >>
 arw[O_LESS_EQ])
(form_goal “!a. Le(a,O) <=> a = O”));

val Le_Suc = prove_store("Le_Suc",
e0
(rpt strip_tac >> drule Le_cases >> 
 pop_assum strip_assume_tac (* 2 *)
 >-- (drule $ iffLR Lt_Suc_Le >> arw[]) >>
 arw[])
(form_goal “!a b. Le(a,Suc(b)) ==> (Le(a,b) | a = Suc(b))”));

val Le_Add_ex = prove_store("Le_Add_ex",
e0
(Nind_tac >> rw[Le_O_iff] >>
 rpt strip_tac (* 2 *)
 >-- (arw[] >> qexists_tac ‘O’ >> rw[Add_O]) >>
 rpt strip_tac >> drule Le_Suc >> 
 pop_assum strip_assume_tac 
 >-- (first_x_assum drule >> 
     pop_assum strip_assume_tac >>
     qexists_tac ‘Suc(p)’ >> arw[Add_Suc1]) >>
 arw[] >> qexists_tac ‘O’ >> rw[Add_O2])
(form_goal
 “!m n. Le(n,m) ==> ?p. Add(p,n) = m”));




val LE_def = 
AX1 |> qspecl [‘N’, ‘N’] |> uex2ex_rule
|> fVar_sInst_th “P(m:mem(N),n:mem(N))” “Sub(m,n) = O”
|> qSKOLEM "LE" []
|> store_as "LE_def";


val LT_def = 
AX1 |> qspecl [‘N’, ‘N’] |> uex2ex_rule
|> fVar_sInst_th “P(m:mem(N),n:mem(N))” “Holds(LE,m,n) & ~(m = n)”
|> qSKOLEM "LT" []
|> store_as "LT_def";


val LE_Le = prove_store("LE_Le",
e0
(rw[LE_def,Le_def])
(form_goal “!a b. Holds(LE,a,b) <=> Le(a,b)”));


val LT_Lt = prove_store("LT_Lt",
e0
(rw[LT_def,Lt_def,LE_Le])
(form_goal “!a b. Holds(LT,a,b) <=> Lt(a,b)”));

(*a <= b <=> ?c. a + c = b
  a <= 0 , the c is 0.
  a <= suc n. *)

val LE_Trans = prove_store("LE_Trans",
e0
(rw[Trans_def,LE_Le] >> rpt strip_tac >>
 rw[Le_def] >> drule Le_Add_ex >>
 pop_assum (strip_assume_tac o GSYM) >> arw[] >>
 qsspecl_then [‘a2’,‘p’] assume_tac Add_comm >> 
 once_arw[] >> rw[Sub_Add] >> fs[Le_def] >>
 rw[Sub_of_O])
(form_goal “Trans(LE)”));


val LESS_MONO_ADD = prove_store("LESS_MONO_ADD",
e0
(strip_tac >> strip_tac >> Nind_tac >>
 rw[Add_O,Add_Suc,LESS_MONO_EQ])
(form_goal “!m n p. Lt(m,n) <=> Lt(Add(m,p),Add(n,p))”));

val EQ_MONO_ADD_EQ = prove_store("EQ_MONO_ADD_EQ",
e0
(strip_tac >> strip_tac >> Nind_tac >> 
 rw[Add_O,Add_Suc] >> rpt strip_tac >> 
 arw[Suc_eq_eq])
(form_goal “!m n p.(Add(m,p) = Add(n,p)) <=> m = n”));


val LESS_MONO_ADD_EQ = GSYM LESS_MONO_ADD
                            |> store_as 
                            "LESS_MONO_ADD_EQ";

val LESS_OR_EQ = prove_store("LESS_OR_EQ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >--
 (drule Le_cases >> arw[]) 
 >-- fs[Lt_def] >>
 arw[Le_def,Sub_EQ_O])
(form_goal “Le(m,n)<=> (Lt(m,n) | m = n)”));


val LESS_EQ_MONO_ADD_EQ = prove_store("LESS_EQ_MONO_ADD_EQ",
e0
(rw[LESS_OR_EQ,LESS_MONO_ADD_EQ,EQ_MONO_ADD_EQ])
(form_goal “!m n p. Le(Add(m,p),Add(n,p)) <=> Le(m,n)”));


val Le_trans = LE_Trans |> rewr_rule[Trans_def,LE_Le]



val Le_Add = prove_store("Le_Add",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(a,d)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘b’,‘a’] assume_tac Add_comm >>
 arw[] >>
 qsspecl_then [‘d’,‘a’] assume_tac Add_comm >>
 arw[] >> arw[LESS_EQ_MONO_ADD_EQ])
(form_goal
 “!a b c d. Le(a,c) & Le(b,d) ==> 
   Le(Add(a,b),Add(c,d))”));





val _ = new_pred "Asym" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val Asym_def = qdefine_psym("Asym",[‘R:A~>A’]) ‘!a b. Holds(R,a,b) & Holds(R,b,a) ==> a = b’ |> gen_all |> store_as "Asym_def";



local
val l = 
 fVar_Inst_th
("P",([("a",mem_sort (rastt "N"))],
 “a = Suc(a)”))
 WOP 
in
val Suc_NEQ = prove_store("Add_Suc_NEQ",
e0
(strip_tac >> ccontra_tac >> drule l >>
 pop_assum strip_assume_tac >>
 cases_on “a0 = O” >-- fs[GSYM Suc_NONZERO] >>
 fs[O_xor_Suc] >> fs[] >>
 fs[Suc_eq_eq] >>
 first_x_assum drule >> 
 drule $ iffRL Lt_Suc_Le >> fs[Lt_def])
(form_goal “!a. ~(a = Suc(a))”));
end



val Lt_Suc = prove_store("Lt_Suc",
e0
(rw[Lt_def,Le_def,Sub_Suc,Suc_NEQ,Sub_EQ_O,Pre_O])
(form_goal “!a. Lt(a,Suc(a))”));


val Add_Suc_Lt = prove_store("Add_Suc_NEQ",
e0
(strip_tac >> Nind_tac >> strip_tac    
 >-- (rw[Lt_def,Le_def,Add_Suc,Add_O,Sub_Suc,Pre_O,O_xor_Suc,
        Suc_NEQ,Pre_O,Sub_EQ_O]) >>
 rpt strip_tac >> rw[Add_Suc] >> rw[Lt_Suc_Le] >>
 rw[GSYM Add_Suc] >> fs[Lt_def])
(form_goal “!a b. Lt(a,Add(a,Suc(b)))”));
 



val LT_Trans = prove_store("LT_Trans",
e0
(rw[Trans_def] >> rw[LT_Lt] >> rw[Lt_def] >>
 assume_tac Le_trans >> rpt strip_tac >--
 (first_x_assum irule >> qexists_tac ‘a2’ >> arw[]) >>
 qby_tac ‘(?p1. Add(a1,Suc(p1)) = a2) & 
          ?p2. Add(a2,Suc(p2)) = a3’ >-- 
 (drule Le_Add_ex >> rev_drule Le_Add_ex >> fs[] >>
  qby_tac ‘~(p = O)’ >-- 
  (ccontra_tac >> fs[Add_O2]) >>
  qby_tac ‘~(p' = O)’ >-- 
  (ccontra_tac >> fs[Add_O2]) >>
  fs[O_xor_Suc] >> strip_tac
 >-- (qexists_tac ‘pn'’ >> once_rw[Add_comm] >> fs[]) >>
 qexists_tac ‘pn’ >> once_rw[Add_comm] >> fs[]) >>
 pop_assum (strip_assume_tac o GSYM) >>
 fs[] >> rw[GSYM Add_assoc] >> once_rw[Add_Suc] >>
 assume_tac Add_Suc_Lt >> fs[Lt_def])
(form_goal “Trans(LT)”));

val Lt_trans = LT_Trans |> rewr_rule[LT_Lt,Trans_def]
                        |> store_as "Lt_trans";

val LE_Asym = prove_store("Le_Asym",
e0
(rw[Asym_def] >> rpt strip_tac >> fs[LE_Le] >> 
 drule Le_cases >> pop_assum strip_assume_tac >> arw[] >>
 rev_drule Le_cases >> pop_assum strip_assume_tac >> arw[] >>
 qby_tac ‘Lt(a,a)’ >-- (irule Lt_trans >>
 qexists_tac ‘b’ >> arw[]) >> fs[Lt_def])
(form_goal “Asym(LE)”));

val Le_Asym = LE_Asym |> rewr_rule[LE_Le,Asym_def]
                      |> store_as "Le_Asym";



val LESS_EQ_LESS_EQ_MONO = prove_store("LESS_EQ_LESS_EQ_MONO",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(m,q)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 once_rw[Add_comm] >> arw[LESS_EQ_MONO_ADD_EQ])
(form_goal “!m n p q. (Le(m,p) & Le(n,q)) ==> Le(Add(m,n),Add(p,q))”));




val Le_MONO_Mul = prove_store("Le_MONO_Mul",
e0
(strip_tac >> strip_tac >> Nind_tac >>
 rw[Mul_O,Le_refl] >> strip_tac >> arw[] >>
 rw[Mul_Suc] >> rpt strip_tac >>
 first_x_assum drule >> irule LESS_EQ_LESS_EQ_MONO >> arw[])
(form_goal “!m n p. Le(m,n) ==> Le(Mul(m,p),Mul(n,p))”));



val Le_MONO_Mul' = Le_MONO_Mul |> strip_all_and_imp
                               |> gen_all
                               |> disch_all
                               |> gen_all
                               |> store_as "Le_MONO_Mul'";

val Le_MONO_Mul2 = prove_store("Le_MONO_Mul2",
e0
(rpt strip_tac >> 
 irule Le_trans >> qexists_tac ‘Mul(m,j)’ >> 
 rev_drule Le_MONO_Mul' >> arw[] >>
 drule Le_MONO_Mul' >> once_rw[Mul_comm] >> arw[])
(form_goal “!m n i j. Le(m,i) & Le(n,j) ==> Le(Mul(m,n),Mul(i,j))”));


val Le_MONO = LESS_EQ_MONO |> store_as "Le_MONO";

val Le_O' = prove_store("Le_O'",
e0
(rw[Le_def,Sub_of_O])
(form_goal “!x. Le(O,x)”));

val Sub_Suc1 = prove_store("Sub_Suc1",
e0
(Nind_tac >> 
 rw[Le_O_iff,Sub_of_O] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> arw[Sub_O]) >>
 strip_tac >> strip_tac >> 
 Nind_tac >> 
 arw[] >> rw[Le_O,Sub_O] >> strip_tac >>
 arw[] >>
 rw[Le_MONO] >> rw[Sub_Suc] >> rpt strip_tac >>
 qby_tac ‘Le(n',Suc(n))’ 
 >-- (irule Le_trans >> qexists_tac ‘n’ >> arw[] >>
     assume_tac Lt_Suc >> fs[Lt_def]) >>
 first_x_assum drule >> arw[] >>
 last_x_assum drule >> arw[] >> rw[Pre_Suc])
(form_goal
 “!a b. Le(b,a) ==> Sub(Suc(a),b) = Suc(Sub(a,b))”));



val SUB_ADD = prove_store("SUB_ADD",
e0
(Nind_tac >> 
 rw[Sub_of_O,Add_O2,Le_O_iff] >> strip_tac >>
 strip_tac >>
 Nind_tac >> 
 rw[Sub_O,Add_Suc1,Add_O] >> strip_tac >> arw[] >>
 rw[Sub_mono_eq] >> rw[Add_Suc] >> 
 rw[Suc_eq_eq] >> rw[Le_MONO] >> 
 rpt strip_tac >> 
 qby_tac ‘Le(n',Suc(n))’ 
 >-- (irule Le_trans >> qexists_tac ‘n’ >> arw[] >>
     assume_tac Lt_Suc >> fs[Lt_def]) >>
 first_x_assum drule >> rev_drule Sub_Suc1 >> fs[] >> 
 first_x_assum irule >> arw[])
(form_goal “!m n. Le(n,m) ==> Add(Sub(m,n),n) = m”));




val ADD_EQ_SUB = prove_store("ADD_EQ_SUB",
e0
(strip_tac >> Nind_tac >>
 rw[Le_O_iff,Add_O,Sub_O] >> strip_tac >> strip_tac >>
 Nind_tac >>
 rw[Le_def,Sub_O,Suc_NONZERO] >> strip_tac >> arw[] >>
 rw[Add_Suc,Suc_eq_eq,Le_MONO,Sub_mono_eq] >>rpt strip_tac >>
 fs[GSYM Le_def] >>
 first_x_assum drule >> arw[])
(form_goal
 “!m n p. Le(n,p) ==> (Add(m,n) = p <=> m = Sub(p,n))”));


val NOT_SUC_LESS_EQ_O = prove_store("NOT_SUC_LESS_EQ_O",
e0
(rw[Le_def,Sub_O,Suc_NONZERO])
(form_goal
 “!n. ~(Le(Suc(n),O))”));

val NOT_SUC_LT_O = prove_store("NOT_SUC_LT_O",
e0
(rw[Lt_def,NOT_SUC_LESS_EQ_O])
(form_goal
 “!n. ~(Lt(Suc(n),O))”));

val Lt_MONO = LESS_MONO_EQ |> store_as "Lt_MONO";

val Lt_trichotomy = prove_store("Lt_trichotomy",
e0
(rpt strip_tac >>
 qcases ‘Lt(a,b)’ >> arw[] >>
 qsspecl_then [‘a’,‘b’] assume_tac LESS_cases >> rfs[] >>
 drule Le_cases >> pop_assum strip_assume_tac >> arw[])
(form_goal “!a b. Lt(a,b) | a = b | Lt(b,a)”));

val NEQ_O_Lt = prove_store("NEQ_O_Lt",
e0
(strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[O_xor_Suc] >> 
     qsspecl_then [‘O’,‘Suc(pn)’] assume_tac Lt_trichotomy >>
     fs[GSYM Suc_NONZERO,NOT_SUC_LT_O]) >>
 fs[Lt_def] >> ccontra_tac >> fs[])
(form_goal “!a. ~(a = O) <=> Lt(O,a)”));


val Add_eq_O = prove_store("Add_eq_O",
e0
(rw[Lt_def,NOT_SUC_LESS_EQ_O] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[Add_clauses] >>
 qcases ‘m = O’ >> qcases ‘n = O’ >> fs[Add_clauses] >>
 fs[NEQ_O_Lt] >>
 qsspecl_then [‘O’,‘n’,‘m’] assume_tac LESS_MONO_ADD >>
 rfs[Add_clauses] >> 
 qsspecl_then [‘O’,‘m’,‘Add(n,m)’] assume_tac Lt_trans >>
 rfs[] >> fs[Lt_def] >>
 qsspecl_then [‘n’,‘m’] assume_tac Add_comm >> fs[] >> rfs[])
(form_goal
 “!m n. Add(m,n) = O <=> m = O & n = O”));

val MULT_MONO_EQ = prove_store("MULT_MONO_EQ",
e0
((*rw[Mul_clauses] >> Nind_tac >> strip_tac (* 2 *)
 >-- (rw[Mul_clauses,Add_clauses] >> rpt strip_tac >>
     dimp_tac >> strip_tac >> arw[] (* 2 *)
     >-- (pop_assum (assume_tac o GSYM) >>
         fs[Add_eq_O]) >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[Add_clauses,Mul_clauses]) >>
 strip_tac >> strip_tac >>
 rw[Mul_clauses]
 Nind_tac >> rw[Mul_clauses,Add_clauses] >>
 rpt strip_tac *) cheat
 )
(form_goal
 “!m i n. Mul(Suc(n),m) = Mul(Suc(n),i) <=> m = i”));


val Mul_eq_O = prove_store("Mul_eq_O",
e0
(Nind_tac >> rw[Mul_clauses,Suc_NONZERO] >>
 rpt strip_tac >>
 rw[Add_eq_O] >> dimp_tac >> strip_tac >> arw[Mul_clauses])
(form_goal “!a. ~(a = O) ==>
 !b. Mul(a,b) = O <=> b = O”));


val Sub_Sub_O_eq = prove_store("Sub_Sub_O_eq",
e0
(rw[GSYM Le_def] >> rw[Le_Asym])
(form_goal “!a b. Sub(a,b) = O & Sub(b,a) = O ==>
 a = b”));

val MULT_MONO_EQ = prove_store("MULT_MONO_EQ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 irule Sub_Sub_O_eq >> strip_tac (* 2 *)
 >-- (irule $ iffLR Mul_eq_O >>
     qexists_tac ‘Suc(n)’ >> rw[Suc_NONZERO] >>
     qsspecl_then [‘Mul(Suc(n), i)’] assume_tac Sub_EQ_O >>
     qby_tac ‘Sub(Mul(Suc(n), m), Mul(Suc(n), i)) = O’
     >-- arw[] >>
     pop_assum mp_tac>> rw[GSYM LEFT_SUB_DISTR]) >>
 irule $ iffLR Mul_eq_O >>
 qexists_tac ‘Suc(n)’ >> rw[Suc_NONZERO] >>
 qsspecl_then [‘Mul(Suc(n), i)’] assume_tac Sub_EQ_O >>
 qby_tac ‘Sub(Mul(Suc(n), i), Mul(Suc(n), m)) = O’
 >-- arw[] >>
 pop_assum mp_tac>> rw[GSYM LEFT_SUB_DISTR])
(form_goal
 “!n m i. Mul(Suc(n),m) = Mul(Suc(n),i) <=> m = i”));


val Mul_eq_eq_l = prove_store("Mul_eq_eq_l",
e0
((*strip_tac >> strip_tac >> Nind_tac >> 
 rw[Mul_O,Mul_Suc] >> rpt strip_tac >> 
 qcases ‘n' = O’ (* 2 *)
 >-- arw[Mul_O,Add_O2] >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 arw[Suc_eq_eq] *) cheat)
(form_goal “!m n p. ~(p = O) ==>
 (Mul(m, p) = Mul(n, p) <=> m = n)”));


val Lt_MONO_Mul = prove_store("Lt_MONO_Mul",
e0
(rpt strip_tac >>
 rw[Lt_def] >> strip_tac (* 2 *)
 >-- (irule Le_MONO_Mul' >> fs[Lt_def]) >>
 fs[GSYM NEQ_O_Lt,O_xor_Suc] >>
 once_rw[Mul_comm] >>
 rw[MULT_MONO_EQ] >> fs[Lt_def])
(form_goal “!p. Lt(O,p) ==> !m n. Lt(m,n) ==> Lt(Mul(m,p),Mul(n,p))”));


val Lt_MONO_Mul2 =  prove_store("Le_MONO_Mul2",
e0
(cheat)
(form_goal “!m n i j. Lt(m,i) & Lt(n,j) ==> Lt(Mul(m,n),Mul(i,j))”));



val NOT_LESS = prove_store("NOT_LESS",
e0
(Nind_tac >> rw[Le_O_iff] >> strip_tac (* 2 *)
 >-- (strip_tac >> dimp_tac >> strip_tac >>
     ccontra_tac >> fs[O_xor_Suc] >> fs[Lt_def,GSYM Suc_NONZERO]>>
     fs[Le_def,Sub_Suc,Sub_of_O,Pre_O] >> rfs[] >>
     last_x_assum (assume_tac o GSYM) >> fs[Suc_NONZERO]) >>
 strip_tac >> strip_tac >>
 Nind_tac >> rw[NOT_SUC_LT_O,Le_O'] >>
 strip_tac >> arw[] >>
 rw[Le_MONO,Lt_MONO] >> arw[])
(form_goal “!m n. ~(Lt(m,n)) <=> Le(n,m)”));



 
val RIGHT_SUB_DISTR = prove_store("RIGHT_SUB_DISTR",
e0
(rpt strip_tac >>
 qsspecl_then [‘Mul(Sub(m,n),p)’,‘Mul(n,p)’,‘Mul(m,p)’]
 assume_tac ADD_EQ_SUB >> 
 cases_on “Le(n,m)” >--
 (drule Le_MONO_Mul' >> fs[] >>
 fs[GSYM RIGHT_DISTR] >> drule SUB_ADD >> fs[]) >>
 fs[GSYM NOT_LESS] >> fs[Lt_def] >>
 fs[Le_def,Mul_clauses] >> flip_tac >> rw[GSYM Le_def] >>
 irule Le_MONO_Mul' >> arw[Le_def])
(form_goal “!m n p. Mul(Sub(m,n),p) = Sub(Mul(m,p),Mul(n,p))”));


val LEFT_SUB_DISTR = prove_store("LEFT_SUB_DISTR",
e0
(rpt strip_tac >> once_rw[Mul_comm] >>
 rw[RIGHT_SUB_DISTR])
(form_goal “!m n p. Mul(p,Sub(m,n)) = Sub(Mul(p,m),Mul(p,n))”));


val LESS_ADD_NONZERO = prove_store("LESS_ADD_NONZERO",
e0
(strip_tac >> ind_with N_induct >> rw[] >>
rpt strip_tac >> cases_on “n = O” 
 >-- arw[Add_Suc,Add_O,Lt_Suc] >>
 first_x_assum drule >>
 rw[Add_Suc] >> irule Lt_trans >>
 qexists_tac ‘Add(m,n)’ >> arw[Lt_Suc])
(form_goal
 “!m n. ~(n = O) ==> Lt(m,Add(m,n))”));


val SUB_LESS = prove_store("SUB_LESS",
e0
(rpt strip_tac >>
 drule Le_Add_ex >> pop_assum (strip_assume_tac o GSYM)>>
 arw[] >>
 rw[Add_Sub] >> 
 irule LESS_ADD_NONZERO >> fs[Lt_def] >> flip_tac >> arw[])
(form_goal
 “!m n. Lt(O,n) & Le(n,m) ==> Lt(Sub(m,n),m)”));
 

val Add_leq = prove_store("Add_leq",
e0
(rpt strip_tac >> arw[])
(form_goal “!a1 a2 b. a1 = a2 ==> Add(a1,b) = Add(a2,b)”));


val Add_req = prove_store("Add_req",
e0
(rpt strip_tac >> arw[])
(form_goal “!a b1 b2. b1 = b2 ==> Add(a,b1) = Add(a,b2)”));


val Add_middle = prove_store("Add_middle",
e0
(rw[GSYM Add_assoc])
(form_goal “!a b c d. Add(a,Add(b,Add(c,d))) = Add(Add(a,b),Add(c,d))”));


(*
define the set of lists
App(f:A(set of A~>B functions)~>B(set of A list ~> B list function),a)

induction recursion

!P. P [] & (!t h.P(t) ==> P(h :: t)) ==> !l. P(l)

recursion :

!n c:'a ~> 'b ~> 'b. ?!f:'a list ~> 'b. f [] = n & !h t. f(h :: t) = c h (f t)


map fold

Map(f:A~>B): 'a list set ~> 'b list set





*)

(*


val ADD_def0 = Nind_def |> specl [rastt "N"]
                        |> specl [rastt "SUC"]
                        |> C mp SUC_Fun 
                        


(*
pre0 
pre0 n = (n,pre n)

f: (n,pre n) |~> (suc n, n)


(1, pre 1 = pre 0) |~> 
*)


val PRE_def0 = Nind_def |> specl [rastt "N * N"]
                        |> specl [rastt "SUC"]
                        |> C mp SUC_Fun 
*)                        


val Add_eq_eq_l = EQ_MONO_ADD_EQ


val Add_eq_eq_r = prove_store("Add_eq_eq_r",
e0
(once_rw[Add_comm] >> rw[Add_eq_eq_l])
(form_goal “!a m n.Add(a,m) = Add(a,n) <=> m = n”));



val Lt_Sub_O = prove_store("Lt_Sub_O",
e0
cheat
(form_goal “!a b. Lt(a,b) <=> Lt(O,Sub(b,a))”));


