use "ETCSind_tac.sml";
 
val to_P_component = prove_store("to_P_component",
e0
(rpt strip_tac >> flip_tac >> irule is_Pa >> rw[])
(form_goal
 “!A B X f:X->A * B.  Pa(p1(A,B) o f,p2(A,B) o f) = f”));


val Tp1_def = qdefine_fsym("Tp1",[‘f:A->B’]) 
‘Tp(f o p1(A,1))’ |> gen_all |> store_as "Tp1_def";


val Tp_of_Ev = prove_store("Tp_of_Ev",
e0
(flip_tac >> irule is_Tp >> rw[])
(form_goal
 “Tp((Ev(A, B) o Pa(p1(A, X), f o p2(A, X)))) = f”));




val Suc_def = qdefine_fsym("Suc",[‘n:X->N’]) ‘SUC o n’
|> gen_all |> store_as "Suc_def";





val Pre_eqn = prove_store("Pre_eqn",
e0
(strip_assume_tac PRE_def >> arw[Pre_def,Suc_def,GSYM o_assoc,idL])
(form_goal
 “Pre(O) = O & !n. Pre(Suc(n)) = n”));


val INV_SUC_EQ = prove_store("INV_SUC_EQ",
e0
(assume_tac Thm2_2 >> fs[Mono_def] >> 
 rpt strip_tac >> dimp_tac >> strip_tac >--
 (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal 
“!m n:1->N. SUC o m = SUC o n <=> m = n”));


val Suc_eq_eq = INV_SUC_EQ |> rewr_rule[GSYM Suc_def] |> store_as "Suc_eq_eq";



val ADD_def = 
 Thm1 |> sspecl (List.map rastt ["id(N)","SUC o p2(N * N,N)"])
      |> uex2ex_rule
      |> qSKOLEM "ADD" []
      |> rewr_rule[o_assoc,p12_of_Pa,idL]
      |> store_as "ADD_def";
        

val Add_def = qdefine_fsym ("Add",[‘n1:1->N’,‘n2:1->N’]) ‘ADD o Pa(n1,n2)’ |> gen_all |> store_as "Add_def";

val _ = new_fsym2IL1 ("Add",mk_fun "ADD" [])

val App_input_eq =prove_store("App_input_eq",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!A B f:A->B X a1:X->A a2.a1 = a2 ==> f o a1 = f o a2”))



val Add_O = prove_store("Add_O",
e0
(strip_tac >> rw[Add_def] >> assume_tac ADD_def >>
 qby_tac 
 ‘ADD o Pa(p1(N, 1), O o p2(N, 1)) o Pa(n,id(1)) = 
                                     p1(N, 1) o Pa(n,id(1))’
 >-- arw[GSYM o_assoc] >>
 fs[Pa_distr,p12_of_Pa,idR,o_assoc])
(form_goal
 “!n. Add(n,O) = n”));


val Add_Suc = prove_store("Add_Suc",
e0
(rpt strip_tac >> assume_tac ADD_def >>
 qby_tac ‘SUC o ADD o Pa(m,n) =
          ADD o Pa(p1(N, N), SUC o p2(N, N)) o Pa(m,n)’
 >-- arw[GSYM o_assoc] >>
 fs[Pa_distr,p12_of_Pa,Suc_def,Add_def,o_assoc])
(form_goal
 “(!m:1->N n.Add(m,Suc(n)) = Suc(Add(m,n)))”));




val Pre_O = conjE1 Pre_eqn |> store_as "Pre_O";

val Pre_Suc = conjE2 Pre_eqn |> store_as "Pre_Suc";


val SUB_def = Thm1 |> specl
(List.map rastt ["N","N","id(N)","PRE o p2(N * N,N)"])
|> uex2ex_rule
|> qSKOLEM "SUB" []
|> rewr_rule[idL,o_assoc,p12_of_Pa]
|> store_as "SUB_def";



val o_eq_r = prove_store("o_eq_r",
e0
(rpt strip_tac >> arw[])
(form_goal
 “!A B f1:A->B f2:A->B. f1 = f2 ==>
  !C g:B->C. g o f1 = g o f2”));


val Sub_def = qdefine_fsym ("Sub",[‘n1:1->N’,‘n2:1->N’]) ‘SUB o Pa(n1,n2)’ |> gen_all |> store_as "Sub_def";

val _ = new_fsym2IL1 ("Suc",mk_fun "SUC" [])
val _ = new_fsym2IL1 ("Sub",mk_fun "SUB" [])

val Sub_O = prove_store("Sub_O",
e0
(strip_tac >> strip_assume_tac SUB_def >>
 qby_tac 
 ‘SUB o Pa(p1(N, 1), O o p2(N, 1)) o Pa(n,id(1)) 
  = p1(N, 1) o Pa(n,id(1))’
 >-- arw[GSYM o_assoc] >> 
 fs[Sub_def,o_assoc,Pa_distr,idR,p12_of_Pa])
(form_goal
 “!n. Sub(n,O) = n”));


val Sub_Suc = prove_store("Sub_Suc",
e0
(rpt strip_tac >> strip_assume_tac SUB_def >> 
 qby_tac
 ‘PRE o SUB o Pa(m,n) = 
  SUB o Pa(p1(N, N), SUC o p2(N, N)) o Pa(m,n)’ 
 >-- arw[GSYM o_assoc] >> 
 fs[o_assoc,p12_of_Pa,Pa_distr,o_assoc,Sub_def,Suc_def,Pre_def])
(form_goal
 “!m n. Sub(m,Suc(n)) = Pre(Sub(m,n))”));




val SoE_lemma_2_5_5 = proved_th $
e0
(rw[iscoPr_def] >> rpt strip_tac >>
 uex_tac >> 
 qexists_tac 
 ‘p2(N,X) o Nrec(Pa(O, f), Pa(SUC, g) o p1(N,X))’ >>
 rw[o_assoc,Nrec_def,p12_of_Pa] >>
 rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc] >>
 qby_tac ‘p1(N, X) o Nrec(Pa(O, f), Pa(SUC, g) o p1(N, X)) = 
 id(N)’ >-- 
 (irule comm_with_SUC_id >>
  rw[Nrec_def,o_assoc,p1_of_Pa] >> 
  rw[GSYM o_assoc,p1_of_Pa]) >> 
 arw[idR] >> 
 qsuff_tac 
 ‘!fg:N->X. fg o O = f:1->X & fg o SUC = g ==>
   Pa(id(N),fg) = Nrec(Pa(O, f), Pa(SUC, g) o p1(N,X))’
 >-- (strip_tac >> strip_tac >> disch_tac >>
     first_assum drule >> 
     qby_tac 
     ‘p2(N,X) o Pa(id(N), fg') = 
      p2(N,X) o Nrec(Pa(O, f), Pa(SUC, g) o p1(N, X))’
     >-- arw[] >> fs[p2_of_Pa]) >>
 rpt strip_tac >> 
 assume_tac Nrec_def >>
 first_assum (qspecl_then [‘N * X’,‘Pa(SUC, g) o p1(N, X)’,‘Pa(O, f)’] strip_assume_tac) >>
 first_assum irule >> rw[o_assoc,p12_of_Pa,Pa_distr,idR] >>
 rw[Pa_eq_eq] >> arw[idL])
(form_goal “iscoPr(O,SUC)”);


val O_xor_SUC = prove_store("O_xor_SUC",
e0
(strip_tac >> assume_tac SoE_lemma_2_5_5 >>
 drule copr_disjoint >>
 first_x_assum (qspecl_then [‘n’] assume_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 cases_on “n = O” >> arw[] >>
 ccontra_tac >> fs[] >> pop_assum mp_tac >>
 rw[] >> once_rw[one_to_one_id] >>
 arw[idR] >> qexists_tac ‘id(1)’ >> rw[]
 )
(form_goal
“!n:1->N. ~(n = O) <=> ?n0:1->N. n = SUC o n0”));

val O_xor_Suc = O_xor_SUC |> rewr_rule[GSYM Suc_def]
                          |> store_as "O_xor_Suc";


val Pre_O_cases = prove_store("Pre_O_case",
e0
(strip_tac >> cases_on “n = O” >> arw[Pre_O] >>
 fs[O_xor_Suc] >> dimp_tac >> strip_tac (* 2 *)
 >> fs[Pre_Suc] >> fs[Suc_eq_eq])
(form_goal
 “!n. Pre(n) = O <=> (n = O | n = Suc(O))”));

val Pre_eq_O = Pre_O_cases


val Le_def = qdefine_psym ("Le",[‘m:1->N’,‘n:1->N’])
                          ‘Sub(m,n) = O’
             |> gen_all |> store_as "Le_def";

val Lt_def = qdefine_psym ("Lt",[‘m:1->N’,‘n:1->N’])
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


val ind_principle = prove_store("ind_principle",
e0
(rpt strip_tac >> 
 qspecl_then [‘N’,‘1+1’,‘pred’,‘1’,‘TRUE’] 
 (x_choosel_then ["A","a","At1"] assume_tac) isPb_ex >>
 drule Pb_fac_iff_1 >> 
 qby_tac ‘!u. (?a':1->A. u = a o a') <=> pred o u = TRUE’
 >-- (strip_tac >> 
     (pop_assum (assume_tac o GSYM)) >> arw[] >>
     fconv_tac 
     (rand_fconv no_conv 
                 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "ar"))) >> arw[]) >>
 qby_tac ‘Mono(a)’
 >-- (drule Pb_Mono_Mono >> first_x_assum irule >>
      once_rw[from_one_Mono]) >>
 qby_tac ‘pred = TRUE o To1(N) <=> Iso(a)’ >-- 
 (dimp_tac >> strip_tac >--
  (irule Thm2_3' >> arw[] >> drule $ iffLR isPb_expand >>
  pop_assum strip_assume_tac >> rw[o_assoc] >>
  once_rw[one_to_one_id] >> rw[idR]) >>
  fs[Iso_def] >> irule FUN_EXT >> strip_tac >>
  rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR] >>
  drule $ iffLR isPb_def >> pop_assum strip_assume_tac >>
  qby_tac 
  ‘pred o (a o f') o a' = TRUE o At1 o f' o a'’
  >-- (rw[GSYM o_assoc] >> arw[]) >>
  rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
  fs[True_def] >>
  dimp_tac >> strip_tac (* 2 *) >--
  (fs[Iso_def] >> drule $ iffLR isPb_def >> 
   pop_assum strip_assume_tac >> 
   qby_tac 
   ‘!n0:1->N. pred o (a o f') o n0 = TRUE o At1 o f' o n0’
   >-- (strip_tac >> arw[GSYM o_assoc]) >>
   rpt strip_tac (* 2 *)
   >-- (first_x_assum (qspecl_then [‘O’] assume_tac) >> 
       rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
   first_x_assum (qspecl_then [‘SUC o n’] assume_tac) >> 
  rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
 irule Thm2_3' >> arw[])
(form_goal
“!pred:N->1 + 1. pred = True(N) <=>
 (pred o O = TRUE & 
  (!n:1->N. pred o n = TRUE ==> pred o SUC o n = TRUE))”));


val ind_principle_elements = prove_store
("ind_principle_elements",
e0
(rpt strip_tac >> 
 qspecl_then [‘pred’] assume_tac ind_principle >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule FUN_EXT >> rpt strip_tac >> 
      rw[True_def,o_assoc] >>
      once_rw[one_to_one_id] >> rw[idR] >> arw[]) >>
 arw[True_def] >> rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!pred:N->1+1. (!n.pred o n = TRUE) <=>
 (pred o O = TRUE & (!n:1->N. pred o n = TRUE ==> pred o SUC o n = TRUE))”));


val N_induct = ind_principle_elements 
                   |> rewr_rule[GSYM Suc_def] 
                   |> iffRL
                   |> store_as "N_induct";



fun qform2IL qvl qf = 
    let val tl = List.map (qparse_term_with_cont essps)
                          qvl
        val vl = List.map dest_var tl
        val ct = fvtl tl
        val f = qparse_form_with_cont ct qf
    in form2IL vl f
    end


val TWO = mk_fun "+" [ONE,ONE];

val IL_tac: tactic = fn (ct,asl,w) =>
    let val (bv as (bn,bs),b) = dest_forall w
        val predon = bs |> dest_sort |> #2 |> el 2
        val psort = ar_sort predon TWO
        val predt = pvariantt ct (mk_var ("P",psort))
        val (pn,ps) = dest_var predt
        val predtrue = mk_eq (mk_o predt (mk_var bv)) truth
        val subgoal = 
            mk_exists pn ps
                      (mk_forall bn bs (mk_dimp b predtrue))
    in by_tac subgoal (ct,asl,w)
    end 

val IL_ex_tac: tactic = fn (ct,asl,w) =>
    let val (pv as (pn,ps),b0) = dest_exists w
        val (bv as (bn,bs),b) = dest_forall b0
        val lhs = b |> dest_dimp |> #1
        val ILpred = form2IL [bv] lhs
    in exists_tac ILpred (ct,asl,w)
    end

fun ind_with0 th = 
 pop_assum strip_assume_tac >>
 arw[] >> irule th >>
 pop_assum (assume_tac o GSYM) >> arw[]

val Sub_mono_eq = prove_store("Sub_mono_eq",
e0
(strip_tac >> IL_tac 
 >-- (IL_ex_tac >> 
     rw[Pa_distr,o_assoc,idL,one_to_one_id,idR,
        Eq_property_TRUE,Sub_def,Suc_def]) >>
 ind_with0 N_induct >> 
 rw[Sub_O,Sub_Suc] >> 
 rpt strip_tac (* 2 *) >-- rw[Pre_Suc] >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!m n. Sub(Suc(m),Suc(n)) = Sub(m,n)”));


val Add_Sub = prove_store("Add_Sub",
e0
(IL_tac >-- (IL_ex_tac >> 
             rw[All_def,Pa_distr,p12_of_Pa,Eq_property_TRUE,o_assoc,Sub_def,Add_def]) >>
 ind_with0 N_induct >> 
 rw[Add_O,Sub_O] >> rpt strip_tac >>
 arw[Add_Suc,Sub_mono_eq])
(form_goal
 “!c a. Sub(Add(a,c),c) = a”));

val Add_O2 = prove_store("Add_O2",
e0
(IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,Pa_distr,one_to_one_id,idL,idR,o_assoc,CONJ_def,Add_def]) >>
 ind_with0 N_induct >> rw[Add_Suc,Add_O] >> 
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
 cases_on “m:1->N = n” >> arw[])
(form_goal
 “!m n. Le(m,n) ==> (Lt(m,n) | m = n)”));

val Le_Sub = Le_def;

(*“!p n m.((p <= n) /\ (p <= m)) ==> (((n - p) = (m - p)) = (n = m))”*)

val Suc_NONZERO = prove_store("Suc_NONZERO",
e0
(rw[O_xor_SUC] >> 
 strip_tac >> qexists_tac ‘n’ >> rw[Suc_def])
(form_goal
 “!n. ~(Suc(n) =O)”));


val LE_def = define_fsym("LE",[])
(form2IL [dest_var $ rastt "n1:1->N",dest_var $ rastt "n2:1->N"]
“Sub(n1,n2) = O”) |> store_as "LE_def";

val _ = new_psym2IL ("Le",(mk_fun "LE" [],[]))

val LT_def = define_fsym("LT",[])
(form2IL [dest_var $ rastt "n1:1->N",dest_var $ rastt "n2:1->N"]
“Le(n1:1->N,n2) & ~(n1 = n2)”) |> store_as "LT_def";

val _ = new_psym2IL ("Lt",(mk_fun "LT" [],[]))



val LE_Le = prove_store("LE_Le",
e0
(rw[Le_def,LE_def,Pa_distr,p12_of_Pa,
    Eq_property_TRUE,o_assoc,one_to_one_id,idR,Sub_def])
(form_goal “!a b. LE o Pa(a,b) = TRUE <=> Le(a,b)”));


val LT_Lt = prove_store("LT_Lt",
e0
(rw[Lt_def,LT_def,Pa_distr,p12_of_Pa,CONJ_def,NEG_def',
    Eq_property_TRUE,o_assoc,one_to_one_id,idR,Sub_def,
    LE_Le])
(form_goal “!a b. LT o Pa(a,b) = TRUE <=> Lt(a,b)”));

val cancel_Sub = prove_store("cancel_Sub",
e0
(IL_tac 
 >-- (IL_ex_tac >> strip_tac >>
     rw[p31_def,p32_def,p33_def] >>
     rw[o_assoc,All_def,p12_of_Pa,IMP_def,CONJ_def,IFF_def,
        Eq_property_TRUE,Pa_distr] >>
     rw[LE_Le,Sub_def]) >>
 ind_with0 N_induct >> 
 rw[Sub_O] >> 
 strip_tac >> strip_tac >>  
 IL_tac >--
 (IL_ex_tac >>
  rw[All_def,IMP_def,CONJ_def,Eq_property_TRUE,Pa_distr,p12_of_Pa,o_assoc,IFF_def,one_to_one_id,idL,idR] >>
  rw[LE_Le,Sub_def,Suc_def]) >>
 ind_with0 N_induct >> strip_tac >--
 (rpt strip_tac >> fs[Le_Sub,Sub_O,Suc_NONZERO]) >>
 strip_tac>> strip_tac >> 
 IL_tac >--
 (IL_ex_tac >>
 rw[IMP_def,CONJ_def,IFF_def,Eq_property_TRUE,Pa_distr,o_assoc,p12_of_Pa,idL,idR,one_to_one_id] >>
 rw[LE_Le,Sub_def,Suc_def]) >>
 ind_with0 N_induct >> strip_tac
 >-- fs[Le_def,Sub_O,Suc_NONZERO] >>
 rw[Sub_mono_eq,Le_def] >> rpt strip_tac >> rw[Suc_eq_eq] >>
 first_x_assum irule >> arw[Le_def])
(form_goal
 “!a b c.Le(a,b) & Le(a,c) ==>(Sub(b,a) = Sub(c,a) <=> b = c)”));


val Sub_of_O = prove_store("Sub_of_O",
e0
(IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,o_assoc,Pa_distr,one_to_one_id,idL,Sub_def,idR]) >>
 ind_with0 N_induct >> rw[Sub_O,Sub_Suc] >> rpt strip_tac>>
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
(IL_tac >-- 
 (IL_ex_tac >> 
  rw[All_def,DISJ_def,o_assoc,Pa_distr,p12_of_Pa,
     Lt_def,LE_Le,NEG_def',LT_Lt]) >>
 ind_with0 N_induct >> strip_tac (* 2 *)
 >-- (rw[LE_O_iff] >> rw[Lt_def,O_LESS_EQ] >> strip_tac >>
     cases_on “O = b” >> arw[]) >>
 strip_tac >> strip_tac >>
 IL_tac >--
 (IL_ex_tac >>
  rw[DISJ_def,Pa_distr,idL,idR,one_to_one_id,LT_Lt,LE_Le,
     o_assoc,Suc_def]) >>
 ind_with0 N_induct >> 
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
(IL_tac >-- (IL_ex_tac >> 
 rw[All_def,o_assoc,Pa_distr,p12_of_Pa,Eq_property_TRUE,
    Suc_def,Add_def]) >>
ind_with0 N_induct >> strip_tac >> rw[Add_O] >>
 rpt strip_tac >> rw[Add_Suc] >> arw[])
(form_goal
 “!b a. Add(Suc(a),b) = Suc(Add(a,b))”));


val Add_comm = prove_store("Add_comm",
e0
(IL_tac >-- (IL_ex_tac >> 
rw[All_def,o_assoc,Pa_distr,p12_of_Pa,Eq_property_TRUE,
  Add_def]) >>
ind_with0 N_induct >> rw[Add_O,Add_O2] >> rpt strip_tac >>
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
 cases_on “a = b:1->N” >> arw[])
(form_goal
 “!a b. Le(a,b) <=> Lt(a,b) | a = b”));

val Sub_EQ_O1 = GSYM Le_def

val Lt_Suc_Le = prove_store("Lt_Suc_Le",
e0
(rw[Le_cases_iff] >> rw[Lt_def,Le_def,Sub_Suc,Pre_O_cases,Sub_DIFF_1] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] (* 4 *)
 >-- (cases_on “a = b:1->N” >> arw[]) 
 >-- (ccontra_tac >> fs[Suc_Sub] >> fs[Suc_NONZERO]) 
 >-- (disj1_tac >> rw[GSYM Le_def,Le_refl]) >>
 qspecl_then [‘Suc(b)’,‘b’] assume_tac Sub_DIFF_1 >> fs[] >>
 ccontra_tac >> pop_assum (assume_tac o GSYM) >> fs[] >>
 fs[Sub_EQ_O] >> qpick_x_assum ‘O = Suc(O)’ (assume_tac o GSYM) >>
 fs[Suc_NONZERO])
(form_goal
 “!a b. Lt(a,Suc(b)) <=> Le(a,b)”));

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
 “!a. (!a0. Le(a0,a) ==> p o a0 = TRUE)”
 >-- (strip_tac >> 
      pop_assum (qspecl_then [‘n’,‘n’] assume_tac) >>
      first_assum irule >> rw[Le_refl]) >>
 IL_tac
 >-- (IL_ex_tac >> 
      rw[All_def,o_assoc,IMP_def,Pa_distr,p12_of_Pa,
        Eq_property_TRUE,one_to_one_id,idR,LE_Le]) >>
 ind_with0 N_induct >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> drule Le_O >> arw[] >>
      first_assum irule >> rpt strip_tac >>
      pop_assum mp_tac >> rw[NOT_Lt_O]) >>
 rpt strip_tac >> drule Le_cases >> pop_assum mp_tac >>
 rw[Lt_Suc_Le] >> strip_tac
 >-- (first_assum irule >> first_assum accept_tac) >>
 arw[] >> last_x_assum irule >>
 rw[Lt_Suc_Le] >> first_x_assum accept_tac)
(form_goal 
“!p:N->1+1.
 (!n:1->N. 
  (!n0:1->N. 
    Lt(n0,n) ==> p o n0 = TRUE) ==> p o n = TRUE) ==> 
  !n. p o n = TRUE”));

(*
val strong_ind = prove_store("strong_ind",
e0
(rpt strip_tac >> 
 qsuff_tac ‘!’

irule strong_ind0

)
(form_goal 
“!P p0:P->N. Mono(p0) ==>
 (!n:1->N. 
  (!n0:1->N. 
    LT o Pa(n0,n) = TRUE ==> Char(p0) o n0 = TRUE) ==> Char(p0) o n = TRUE) ==> Iso(p0)”));
*)


val WOP = prove_store("WOP",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac ‘!l. P o l = TRUE ==> ?n. P o n = TRUE & ~(Le(l,n))’
 >-- (rpt strip_tac >> ccontra_tac >>
      qsuff_tac ‘?a0. P o a0 = TRUE & 
                     !a1. P o a1 = TRUE ==> Le(a0,a1)’ 
     >-- (rw[]>> first_x_assum accept_tac) >>
     qexists_tac ‘l’ >> strip_tac (* 2 *)
     >-- first_x_assum accept_tac >>
     rpt strip_tac >> ccontra_tac >>
     qby_tac ‘?n. P o n = TRUE & ~(Le(l,n))’ 
     >-- (qexists_tac ‘a1’ >> strip_tac >> first_x_assum accept_tac) >>
     first_x_assum opposite_tac ) >>
 qsuff_tac ‘!n. ~(P o n = TRUE)’ >-- (rpt strip_tac >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >> 
 first_x_assum opposite_tac) >>
 qsuff_tac ‘!n n0. Le(n0,n) ==> ~(P o n0 = TRUE)’
 >-- (strip_tac >> rpt strip_tac >> first_x_assum irule >>
     qexists_tac ‘n’ >> rw[Le_refl]) >>
 IL_tac
 >-- (IL_ex_tac >> rw[All_def,IMP_def,NEG_def',Eq_property_TRUE,o_assoc,Pa_distr,one_to_one_id,idR,p12_of_Pa,LE_Le]) >>
 ind_with0 N_induct >> rpt strip_tac (* 2 *) >--
 (drule Le_O >> arw[] >> ccontra_tac >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 pop_assum mp_tac >>  rw[Le_def,Sub_of_O]) >>
 pop_assum mp_tac >> strip_tac >>
 drule Le_cases >> pop_assum mp_tac >> rw[Lt_Suc_Le] >> strip_tac (* 2 *)
 >-- (first_x_assum drule >> first_x_assum accept_tac) >>
 arw[] >> ccontra_tac >> 
 last_x_assum drule >> pop_assum strip_assume_tac >>
 qspecl_then [‘n'’,‘Suc(n)’] assume_tac LESS_cases >> 
 cases_on “Lt(n',Suc(n))” >--
 (pop_assum mp_tac >> rw[Lt_Suc_Le] >> ccontra_tac >> first_x_assum drule>>
 first_x_assum opposite_tac) >>
 pop_assum mp_tac >> pop_assum strip_assume_tac >> strip_tac 
)
(form_goal
 “!P a. P o a = TRUE ==> ?a0. P o a0 = TRUE & 
       !a1.P o a1 = TRUE ==> Le(a0,a1)”));

(*
(form_goal
 “!P:N->1+1. ~(P = False(N)) ==> 
  ?l:1->N. P o l = TRUE &
  !n:1->N. P o n = TRUE ==>
  LE o Pa(l,n) = TRUE”));
*)

val MUL_def0 = Thm1 |> qspecl [‘N’,‘N’,‘O o To1(N)’,
                               ‘ADD o Pa(p2(N * N,N),p1(N, N) o p1(N * N,N))’] |> uex2ex_rule
                    |> qSKOLEM "MUL" [] 
                    |> rewr_rule[o_assoc,To1_def,Pa_distr,p12_of_Pa,idR] 
                    |> store_as "MUL_def0";



val Mul_def = qdefine_fsym ("Mul",[‘n1:1->N’,‘n2:1->N’]) ‘MUL o Pa(n1,n2)’ |> gen_all |> store_as "Mul_def";

val _ = new_fsym2IL1 ("Mul",mk_fun "MUL" []);

val Mul_O = prove_store("Mul_O",
e0
(strip_tac >> rw[Mul_def] >> 
 assume_tac MUL_def0 >>
 qby_tac
 ‘MUL o Pa(p1(N, 1), O o To1(N * 1)) o Pa(n,id(1)) = O o To1(N * 1) o Pa(n,id(1))’ 
 >-- arw[GSYM o_assoc] >>
 fs[Pa_distr,p12_of_Pa,idR,one_to_one_id,o_assoc])
(form_goal “!n. Mul(n,O) = O”));


val Mul_Suc = prove_store("Mul_Suc",
e0
(rpt strip_tac >> rw[Mul_def,Suc_def,Add_def] >>
 assume_tac MUL_def0 >>
 qby_tac
 ‘ADD o Pa(MUL, p1(N, N)) o Pa(n,n0) = MUL o Pa(p1(N, N), SUC o p2(N, N)) o Pa(n,n0)’
 >-- arw[GSYM o_assoc] >>
 fs[Pa_distr,p12_of_Pa,o_assoc])
(form_goal “!n n0. Mul(n,Suc(n0)) = Add(Mul(n,n0),n)”));

val Mul_LEFT_O = prove_store("Mul_LEFT_O",
e0
(IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,o_assoc,Pa_distr,one_to_one_id,idR,idL,Mul_def]) >>
 ind_with0 N_induct >> rw[Mul_O,Mul_Suc,Add_O])
(form_goal “!m. Mul(O,m) = O”));


val Mul_LEFT_1 = prove_store("Mul_LEFT_1",
e0
(IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,o_assoc,Pa_distr,one_to_one_id,idR,idL,Mul_def,Suc_def]) >>
 ind_with0 N_induct >> rw[Mul_O,Mul_Suc] >> rpt strip_tac >>
 arw[Add_Suc,Add_O])
(form_goal “!m.Mul(Suc(O),m) = m”));


val Mul_RIGHT_1 = prove_store("Mul_RIGHT_1",
e0
(rw[Mul_Suc,Add_O2,Mul_O])
(form_goal “!m. Mul(m,Suc(O)) = m”));

val Add_comm' = GSYM Add_comm |> store_as "Add_comm'";

(*Add_assoc slow, and the one with three layers slow*)
val Add_assoc = prove_store("Add_assoc",
e0
(IL_tac >-- (IL_ex_tac >> strip_tac >>
rw[Eq_property_TRUE,o_assoc,Pa_distr,one_to_one_id,idR,idL,Mul_def,Suc_def,All_def,p32_def,p33_def,p31_def,p12_of_Pa,Add_def]) >>
 ind_with0 N_induct >> rw[Add_O,Add_Suc,Add_Suc1,Add_O2] >>
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
(IL_tac 
 >-- (IL_ex_tac >> rw[All_def,Eq_property_TRUE,o_assoc,Pa_distr,p12_of_Pa,Mul_def,Suc_def,Add_def]) >>
 ind_with0 N_induct >> 
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
(IL_tac >-- (IL_ex_tac >> rw[All_def,Eq_property_TRUE,o_assoc,Pa_distr,p12_of_Pa,Mul_def]) >>
 ind_with0 N_induct >> rw[Mul_clauses,Suc_def] >>
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
(strip_tac >> strip_tac >>
 IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,Mul_def,Add_def,Pa_distr,p12_of_Pa,o_assoc,one_to_one_id,idL,idR] ) >>
 ind_with0 N_induct >>
 rw[Mul_clauses,Add_clauses] >>
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
(IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,Mul_def,Add_def,Pa_distr,p12_of_Pa,o_assoc,one_to_one_id,idL,idR,All_def,p31_def,p32_def,p33_def] ) >>
 ind_with0 N_induct >>
 rw[Mul_clauses,RIGHT_DISTR] >> rpt strip_tac >>
 arw[] >> rw[GSYM Add_assoc])
(form_goal “!m n p. Mul(m,Mul(n,p)) = Mul(Mul(m,n),p)”));


val Sub_Add = prove_store("SUB_Add",
e0
(IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,Mul_def,Add_def,Pa_distr,p12_of_Pa,o_assoc,one_to_one_id,idL,idR,All_def,p31_def,p32_def,p33_def,Sub_def] ) >>
 ind_with0 N_induct >>
 rw[Sub_of_O] >> strip_tac >>
 strip_tac >>
IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,Mul_def,Add_def,Pa_distr,p12_of_Pa,o_assoc,one_to_one_id,idL,idR,All_def,p31_def,p32_def,p33_def,Sub_def,Suc_def] ) >>
 ind_with0 N_induct >>
 rw[Add_O2,Sub_O] >> strip_tac >> strip_tac >>
IL_tac >-- (IL_ex_tac >> rw[Eq_property_TRUE,Mul_def,Add_def,Pa_distr,p12_of_Pa,o_assoc,one_to_one_id,idL,idR,All_def,p31_def,p32_def,p33_def,Sub_def,Suc_def] ) >>
 ind_with0 N_induct >> rw[Sub_O,Add_O] >> rpt strip_tac >>
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
(IL_tac >--
 (IL_ex_tac >> rw[Eq_property_TRUE,Mul_def,Add_def,Pa_distr,p12_of_Pa,o_assoc,one_to_one_id,All_def,p31_def,p32_def,p33_def,LE_Le,IMP_def,Ex_def] ) >>
 ind_with0 N_induct >>
 rw[Le_O_iff] >>
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



val Holds_def =
 qdefine_psym("Holds",[‘R:A * B -> 1+1’,‘a:1->A’,‘b:1->B’])
‘R o Pa(a,b) = TRUE’ |> gen_all |> store_as "Holds_def";

val SYM_def = qdefine_psym("SYM",[‘R:A * A -> 1+1’])
‘!a b. Holds(R,a,b) ==> Holds(R,b,a)’ |> gen_all
|> store_as "SYM_def";


val REFL_def = qdefine_psym("REFL",[‘R:A * A -> 1+1’])
‘!a. Holds(R,a,a)’ |> gen_all
|> store_as "REFL_def";

 
val TRANS_def = qdefine_psym("TRANS",[‘R:A * A -> 1+1’])
‘!a1 a2 a3. Holds(R,a1,a2) & Holds(R,a2,a3) ==> Holds(R,a1,a3)’ |> gen_all
|> store_as "TRANS_def";


val HLE_Le = prove_store("HLE_Le",
e0
(rw[LE_Le,Holds_def])
(form_goal “!a b. Holds(LE,a,b) <=> Le(a,b)”));


val HLT_Lt = prove_store("HLT_Lt",
e0
(rw[LT_Lt,Holds_def])
(form_goal “!a b. Holds(LT,a,b) <=> Lt(a,b)”));

(*a <= b <=> ?c. a + c = b
  a <= 0 , the c is 0.
  a <= suc n. *)

val LE_TRANS = prove_store("LE_TRANS",
e0
(rw[TRANS_def,HLE_Le] >> rpt strip_tac >>
 rw[Le_def] >> drule Le_Add_ex >>
 pop_assum (strip_assume_tac o GSYM) >> arw[] >>
 qsspecl_then [‘a2’,‘p’] assume_tac Add_comm >> 
 once_arw[] >> rw[Sub_Add] >> fs[Le_def] >>
 rw[Sub_of_O])
(form_goal “TRANS(LE)”));


val default = rw[p31_def,p32_def,p33_def,
o_assoc,All_def,Ex_def,p12_of_Pa,IMP_def,CONJ_def,IFF_def,NEG_def',Eq_property_TRUE,Pa_distr,DISJ_def,LT_Lt,LE_Le,Sub_def,Mul_def,Add_def,Suc_def,Pre_def,one_to_one_id,idL,idR]

val LESS_MONO_ADD = prove_store("LESS_MONO_ADD",
e0
(strip_tac >> strip_tac >>
 IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >>
 rw[Add_O,Add_Suc,LESS_MONO_EQ])
(form_goal “!m n p. Lt(m,n) <=> Lt(Add(m,p),Add(n,p))”));

val EQ_MONO_ADD_EQ = prove_store("EQ_MONO_ADD_EQ",
e0
(strip_tac >> strip_tac >> 
 IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >>
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


val Le_trans = LE_TRANS |> rewr_rule[TRANS_def,HLE_Le]



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


val ASYM_def = qdefine_psym("ASYM",[‘R:A*A -> 1+1’]) ‘!a b. Holds(R,a,b) & Holds(R,b,a) ==> a = b’ |> gen_all |> store_as "ASYM_def";


(*use WOP*)

val Suc_NEQ = prove_store("Add_Suc_NEQ",
e0
(strip_tac >> ccontra_tac >>
 assume_tac (WOP |> specl[qform2IL [‘a:1->N’] ‘a = Suc(a)’])>>
fs[Eq_property_TRUE,o_assoc,Pa_distr,idL,idR,GSYM Suc_def]>>
 first_x_assum drule >> 
 pop_assum strip_assume_tac >>
 cases_on “a0 = O” >-- fs[GSYM Suc_NONZERO] >>
 fs[O_xor_Suc] >> fs[] >>
 fs[Suc_eq_eq] >>
 first_x_assum drule >> 
 drule $ iffRL Lt_Suc_Le >> fs[Lt_def])
(form_goal “!a:1->N. ~(a = Suc(a))”));




val Lt_Suc = prove_store("Lt_Suc",
e0
(rw[Lt_def,Le_def,Sub_Suc,Suc_NEQ,Sub_EQ_O,Pre_O])
(form_goal “!a. Lt(a,Suc(a))”));


val Add_Suc_Lt = prove_store("Add_Suc_NEQ",
e0
(strip_tac >> IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >> strip_tac    
 >-- (rw[Lt_def,Le_def,Add_Suc,Add_O,Sub_Suc,Pre_O,O_xor_Suc,
        Suc_NEQ,Pre_O,Sub_EQ_O]) >>
 rpt strip_tac >> rw[Add_Suc] >> rw[Lt_Suc_Le] >>
 rw[GSYM Add_Suc] >> fs[Lt_def])
(form_goal “!a b. Lt(a,Add(a,Suc(b)))”));
 



val LT_TRANS = prove_store("LT_TRANS",
e0
(rw[TRANS_def] >> rw[HLT_Lt] >> rw[Lt_def] >>
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
 >-- (qexists_tac ‘n0'’ >> once_rw[Add_comm] >> fs[]) >>
 qexists_tac ‘n0’ >> once_rw[Add_comm] >> fs[]) >>
 pop_assum (strip_assume_tac o GSYM) >>
 fs[] >> rw[GSYM Add_assoc] >> once_rw[Add_Suc] >>
 assume_tac Add_Suc_Lt >> fs[Lt_def])
(form_goal “TRANS(LT)”));

val Lt_trans = LT_TRANS |> rewr_rule[HLT_Lt,TRANS_def]
                        |> store_as "Lt_trans";

val LE_ASYM = prove_store("Le_ASYM",
e0
(rw[ASYM_def] >> rpt strip_tac >> fs[HLE_Le] >> 
 drule Le_cases >> pop_assum strip_assume_tac >> arw[] >>
 rev_drule Le_cases >> pop_assum strip_assume_tac >> arw[] >>
 qby_tac ‘Lt(a,a)’ >-- (irule Lt_trans >>
 qexists_tac ‘b’ >> arw[]) >> fs[Lt_def])
(form_goal “ASYM(LE)”));

val Le_Asym = LE_ASYM |> rewr_rule[HLE_Le,ASYM_def]
                      |> store_as "Le_Asym";



val LESS_EQ_LESS_EQ_MONO = prove_store("LESS_EQ_LESS_EQ_MONO",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(m,q)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 once_rw[Add_comm] >> arw[LESS_EQ_MONO_ADD_EQ])
(form_goal “!m n p q. (Le(m,p) & Le(n,q)) ==> Le(Add(m,n),Add(p,q))”));

val Le_MONO_Mul = prove_store("Le_MONO_Mul",
e0
(strip_tac >> strip_tac >> 
 IL_tac >-- (IL_ex_tac >> default) >> 
 ind_with0 N_induct >>
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
(IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >>
 rw[Le_O_iff,Sub_of_O] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> arw[Sub_O]) >>
 strip_tac >> strip_tac >> 
 IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >>
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
(IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >> 
 rw[Sub_of_O,Add_O2,Le_O_iff] >> strip_tac >>
 strip_tac >>
 IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >> 
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
(strip_tac >>
 IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >> 
 rw[Le_O_iff,Add_O,Sub_O] >> strip_tac >> strip_tac >> 
 IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >> 
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


val NOT_LESS = prove_store("NOT_LESS",
e0
(IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >> rw[Le_O_iff] >> strip_tac (* 2 *)
 >-- (strip_tac >> dimp_tac >> strip_tac >>
     ccontra_tac >> fs[O_xor_Suc] >> fs[Lt_def,GSYM Suc_NONZERO]>>
     fs[Le_def,Sub_Suc,Sub_of_O,Pre_O] >> rfs[] >>
     last_x_assum (assume_tac o GSYM) >> fs[Suc_NONZERO]) >>
 strip_tac >> strip_tac >>
 IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >> 
 rw[NOT_SUC_LT_O,Le_O'] >>
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
(strip_tac >>
 IL_tac >-- (IL_ex_tac >> default) >>
 ind_with0 N_induct >>  rw[] >>
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
 irule LESS_ADD_NONZERO >> fs[Lt_def] >> ccontra_tac >> fs[])
(form_goal
 “!m n. Lt(O,n) & Le(n,m) ==> Lt(Sub(m,n),m)”));
 

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



val _ = new_fsym2IL1 ("Pre",mk_fun "PRE" [])
