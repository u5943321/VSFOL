


(*

val bvs = List.map (dest_var o rastt) ["a:1->A","s:1->Exp(A,1+1)"] 
val t = rastt "Ins(a:1->A,s:1->Exp(A,1+1))"


val bvs = List.map (dest_var o rastt) ["n:1->N","m:1->N"] 
val t = rastt "Sub(n:1->N,m)"
val (f,s,tl) = dest_fun t




fn finfo =>  binop_t "o" (corres_fterm finfo [])
Binarymap.peek(!fsym2IL,"Ins")

corres_fterm finfo (List.map mk_var bvs

val f = “IN(a:1->A,f:Exp(A,1+1)->Exp(A,1+1) o s:1->Exp(A,1+1))”
val (P,tl) = dest_pred f
val p = rastt "In(A)";
val l = List.map (dest_var o rastt) ["a:X->A","ss:X->Exp(A,1+1)"]


qform2IL [‘s:1-> Exp(Exp(X,1+1),1+1)’] ‘!a.IN(a:1->Exp(X,1+1),f o s) ==> IN(a,s)’


pain point of form2IL
*)




(*
qform2IL [‘a:1->A’,‘s:1-> Exp(A,1+1)’] ‘IN(a:1->A,s)’

val bvs = List.map (dest_var o rastt) ["a:1->A","s:1->Exp(A,1+1)"] 
val f = “IN(a:1->A,s)”
val (P,tl) = dest_pred f
val p = rastt "In(A)";
val l = List.map (dest_var o rastt) ["a:1->A","ss:1->Exp(A,1+1)"]


‘!a:1->A.IN(a, f o s) ==> IN(a,s)’

 rw[SS_def] >> strip_tac >>
 strip_tac >>
 qexists_tac 
 ‘ALL(Imp(In(A) o Pa(p1(A,Exp(A,1+1)), f o p2(A,Exp(A,1+1))),In(A)))’ >>
*)  

val prim_lemma = prove_store("SS_lemma",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?p:Exp(A,1+1) ->1+1.
  !a.p o a = TRUE <=> SS(f o a,a)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘p’ >> arw[] >> rpt strip_tac >>
     irule FUN_EXT >> strip_tac >> irule $ iffLR pred_ext >> arw[]) >>
 rw[SS_def] >>
 exists_tac 
 (qform2IL [‘sa:1->Exp(A,1+1)’] ‘!a:1->A.IN(a,f o sa) ==> IN(a,sa)’) >>
 strip_tac >> rw[o_assoc,All_def,Pa_distr,IMP_def,p12_of_Pa,IN_def])
(form_goal
“!A f:Exp(A,1+1)->Exp(A,1+1). ?!p:Exp(A,1+1) ->1+1.
  !a.p o a = TRUE <=> SS(f o a,a)”));



val prim_lemma' = prove_store("SS_lemma'",
e0
(rpt strip_tac >> 
 qsuff_tac
 ‘?p:1-> Exp(Exp(A,1+1),1+1).!a.IN(a,p)<=> SS(f o a,a)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘p’ >> arw[] >>
      rpt strip_tac >> irule $ iffLR IN_EXT >> arw[]) >>
 qsspecl_then [‘f’] (strip_assume_tac o uex2ex_rule) prim_lemma >>  
 qexists_tac ‘Tp1(p)’ >> arw[IN_Tp1])
(form_goal
“!A f:Exp(A,1+1)->Exp(A,1+1). ?!p:1-> Exp(Exp(A,1+1),1+1).
  !a.IN(a,p)<=> SS(f o a,a)”));

use "ETCSreln.sml";
(* the pred used in FI's_def is 
   \a.FIs(X) o a ⊆ a*)
(*Rel2Ar is the thing corresponds to P2fun*)

val _ = new_fsym2IL("Fst",(rastt "p1(A,B)",[dest_var (rastt "ab:X->A * B")]));

val _ = new_fsym2IL("Snd",(rastt "p2(A,B)",[dest_var (rastt "ab:X->A * B")]));


local
val FI_cl = 
 “(xs = Empty(X) ==> IN(xs,FIs)) &
  (!xs0 x:1->X. IN(xs0,FIs) & xs = Ins(x,xs0) ==> IN(xs,FIs))”
in
val (FI_incond,x1) = mk_incond FI_cl;
val FIr_def = define_fsym("FIr",[("X",ob_sort)]) (qform2IL [‘a : 1->Exp(Exp(X,1+1),1+1)’,‘a' : 1->Exp(Exp(X,1+1),1+1)’]
 ‘!xs. IN(xs,a') <=> 
       (xs = Empty(X) |
       ?xs0  x:1->X.
        IN(xs0, a) & xs = Ins(x, xs0))’)
val IL_lemma = 
proved_th $
e0
(rpt strip_tac  >>
 rw[o_assoc,Pa_distr,DISJ_def,p12_of_Pa,Eq_property_TRUE,
             one_to_one_id,idR,FIr_def] >>
 rw[Ex_def,o_assoc] >> rw[CONJ_def,Pa_distr] >>
 rw[p31_def,p32_def,p33_def] >>
 once_rw[p52_def] >> once_rw[p51_def] >> once_rw[p53_def] >>
 once_rw[p54_def] >> once_rw[p55_def] >> 
 once_rw[All_def] >> rw[o_assoc,IFF_def,Pa_distr] >>
 rw[DISJ_def,o_assoc,Pa_distr] >>
 rw[Ex_def,o_assoc] >> rw[CONJ_def,Pa_distr] >>
 rw[o_assoc,p12_of_Pa,Pa_distr] >>
 rw[one_to_one_id] >> rw[idR,Eq_property_TRUE] >>
 rw[IN_def,Ins_def])
(form_goal “!a:1->Exp(Exp(X,1+1),1+1) a'.
 FIr(X) o Pa(a,a') =TRUE <=>
  (!xs. IN(xs,a') <=> 
       (xs = Empty(X) |
       ?xs0  x:1->X.
        IN(xs0, a) & xs = Ins(x, xs0)))”);
(* given a: 1-> Exp(Exp(X,1+1),1+1)
    want a': 1-> Exp(Exp(X,1+1),1+1), which is an arrow:
   Exp(X,2) -> 2,saying that "is" in the set a', then its transpose is the set 
   a'*)
val FIsi_def = 
define_fsym("FIsi",[dest_var (rastt "a : 1->Exp(Exp(X,1+1),1+1)")]) (qform2IL [‘xs : 1->Exp(X,2)’]
 ‘xs = Empty(X) |
          ?xs0  x:1->X.
            IN(xs0, a) & xs = Ins(x, xs0)’);
val FIsi_property = proved_th $
e0
(rw[FIsi_def] >> rpt strip_tac >>
 rw[o_assoc,DISJ_def,Pa_distr] >> 
 once_rw[Ex_def] >> rw[o_assoc,Ex_def] >>
 rw[CONJ_def,Pa_distr,o_assoc] >>
 rw[one_to_one_id,idR] >>
 once_rw[p31_def,p32_def,p33_def] >>
 rw[p12_of_Pa,o_assoc,Pa_distr] >>
 rw[Eq_property_TRUE,IN_def,Ins_def,idL])
(form_goal 
“!a: 1->Exp(Exp(X,1+1),1+1) xs. FIsi(a) o xs = TRUE <=>
 xs = Empty(X) |
          ?xs0  x:1->X.
            IN(xs0, a) & xs = Ins(x, xs0) ”);
val FIf_precond = proved_th $
e0
(strip_tac >>
 qsuff_tac
 ‘?a'.
 (!xs. IN(xs,a') <=> 
       (xs = Empty(X) |
       ?xs0  x:1->X.
        IN(xs0, a) & xs = Ins(x, xs0)))’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘a'’ >>
      arw[] >> rpt strip_tac >> irule $ iffLR IN_EXT >> arw[]) >>
 qexists_tac ‘Tp1(FIsi(a))’ >>
 rw[IN_Tp1] >> rw[FIsi_property])
(form_goal “!a. ?!a'.
 (!xs. IN(xs,a') <=> 
       (xs = Empty(X) |
       ?xs0  x:1->X.
        IN(xs0, a) & xs = Ins(x, xs0)))”)
val FIf_def = 
Rel2Ar_uex
|> sspecl [rastt "FIr(X)"]
|> rewr_rule[IL_lemma]
|> C mp FIf_precond
|> qsimple_uex_spec "FIf" [‘X’]
|> spec_all |> qgen ‘b’
|> qspecl [‘FIf(X) o a’]
|> rewr_rule[] |> qgen ‘a’
val FIf_monotone = mk_monotone FIf_def;
val FI's_def = mk_prim FIf_def;
val FIs_def = mk_LFP (rastt "FI's(X)");
val FIs_cond = mk_cond FIs_def FI's_def;
val FIs_SS = mk_SS FIs_def FI's_def;
val FI_rules0 = mk_rules FIf_monotone FIs_SS FIs_cond;
val FI_cases0 = mk_cases FIf_monotone FI_rules0 FIs_cond;
val FI_ind0 = mk_ind FIs_cond;
val FI_ind1 = mk_ind1 FIf_def FI_ind0;
val FI_ind2 = mk_ind2 FI_ind1;
val FI_cases1 = mk_case1 FIf_def FI_cases0;
val FI_rules1 = mk_rules1 FIf_def FI_rules0;
val FI_rules2 = mk_rules2 FI_rules1;
val FI_rules3 = mk_rules3 FI_rules2;
end

val FI_ind = FI_ind2 |> store_as "FI_ind";
val FI_cases = FI_cases1 |> store_as "FI_cases";
val FI_rules = FI_rules3 |> store_as "FI_rules";




(*TODO: tactic that detect is IN ... and show suffices to show exists*)
val DEL_def = proved_th $
e0
(strip_tac >>
 qsuff_tac
 ‘?DEL:Exp(X,1+1) * X -> Exp(X,1 + 1).
 !x0 xs x. IN(x,DEL o Pa(xs,x0)) <=> IN(x,xs) & ~(x = x0)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘DEL’ >> arw[] >> rpt strip_tac >>
      irule FUN_EXT >> strip_tac >> 
      qsspecl_then [‘a’] strip_assume_tac Pair_has_comp >> arw[] >>
      irule $ iffLR  IN_EXT >> arw[]) >>
 exists_tac (Tp (qform2IL [‘x:1->X’,‘xs:1->Exp(X,1+1)’,‘x0:1->X’]
 ‘IN(x,xs) & ~(x = x0)’)) >>
 rw[IN_def,In_def] >> rw[Ev_of_Tp_el] >>
 rw[CONJ_def,Pa_distr,o_assoc,NEG_def'] >>
 once_rw[p31_def,p32_def,p33_def] >>
 rw[Pa_distr,o_assoc,p12_of_Pa,Eq_property_TRUE])
(form_goal “!X.?!DEL:Exp(X,1+1) * X -> Exp(X,1 + 1).
 !x0 xs x. IN(x,DEL o Pa(xs,x0)) <=> IN(x,xs) & ~(x = x0)”)
|> spec_all 
|> qsimple_uex_spec  "DEL" [‘X’]
|> gen_all
|> store_as "DEL_def";


val Del_def = qdefine_fsym("Del",[‘s0:1-> Exp(X,1+1)’,‘x0:1->X’])
‘DEL(X) o Pa(s0,x0)’ |> qgen ‘x0’ |> qgen ‘s0’ |> qgen ‘X’
|> store_as "Del_def";


val Ins_def1 = INS_def |> rewr_rule[GSYM Ins_def] |> store_as "Ins_def1";
val Del_def1 = DEL_def |> rewr_rule[GSYM Del_def] |> store_as "Del_def1";


val _ = new_fsym2IL("Del",(rastt "DEL(X)",[dest_var (rastt "s0:A->Exp(X,1+1)"),dest_var (rastt "x0:A->X")]));

val Del_Ins = prove_store("Del_Ins",
e0
(rpt strip_tac >> irule $ iffLR IN_EXT >> 
 arw[Ins_def1,Del_def1] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >> ccontra_tac >> fs[])
(form_goal “!X x0:1->X xs0. (~IN(x0,xs0)) ==> Del(Ins(x0,xs0),x0) =xs0”));




val Ins_absorb = prove_store("Ins_absorb",
e0
(rpt strip_tac >> irule $ iffLR IN_EXT >> rw[Ins_def1] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal “!X x0:1->X xs0. IN(x0,xs0) ==> Ins(x0,xs0) =xs0”));


val Fin_def = qdefine_psym("Fin",[‘A:1->Exp(X,1+1)’]) ‘IN(A,FIs(X))’
                          |> gen_all |> store_as "Fin_def"; 




local
val Cd_cl = 
 “(xsn = Pa(Empty(X),O) ==> IN(xsn,Cds)) &
  (!xsn0 x. IN(xsn0,Cds) & ~(IN(x,Fst(xsn0))) & 
            xsn = Pa(Ins(x,Fst(xsn0)),Suc(Snd(xsn0))) ==> IN(xsn,Cds))”
in
val (Cd_incond,x1) = mk_incond Cd_cl;
val Cdr_def = define_fsym("Cdr",[("X",ob_sort)]) (qform2IL [‘a : 1->Exp(Exp(X,1+1) * N,1+1)’,‘a' : 1->Exp(Exp(X,1+1) * N,1+1)’]
 ‘!xsn : 1 -> Exp(X, 1+1) * N.
     IN(xsn, a') <=>
     xsn = Pa(Empty(X), O) |
     ?xsn0: 1 -> Exp(X,1+1) * N  x:1->X.
       IN(xsn0, a) &
       ~IN(x, Fst(xsn0)) & xsn = Pa(Ins(x, Fst(xsn0)), Suc(Snd(xsn0)))’)
val IL_lemma = 
proved_th $
e0
(rpt strip_tac  >>
 rw[o_assoc,Pa_distr,DISJ_def,p12_of_Pa,Eq_property_TRUE,
             one_to_one_id,idR,Cdr_def] >>
 rw[one_to_one_id,idL,idR] >>
 once_rw[All_def,o_assoc,Pa_distr] >>
 rw[IFF_def,o_assoc,Pa_distr] >>
 rw[DISJ_def,o_assoc,Pa_distr] >>
 once_rw[Ex_def] >> rw[o_assoc] >> once_rw[Ex_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[o_assoc] >> once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[p52_def] >> once_rw[p51_def] >> once_rw[p53_def] >>
 once_rw[p54_def] >> once_rw[p55_def] >> 
 once_rw[p31_def] >> once_rw[p32_def] >> once_rw[p33_def] >>
 once_rw[o_assoc] >> once_rw[NEG_def'] >>
 once_rw[Pa_distr] >> once_rw[Eq_property_TRUE] >>
 once_rw[p12_of_Pa] >> once_rw[p12_of_Pa] >> 
 rw[Pa_distr] >> rw[p12_of_Pa,o_assoc] >> rw[Pa_distr] >>
 rw[p12_of_Pa] >> rw[one_to_one_id] >> rw[idR] >>
 once_rw[o_assoc] >> once_rw[p12_of_Pa] >>
 once_rw[o_assoc] >> once_rw[p12_of_Pa] >>
 rw[p12_of_Pa] >>
 rw[GSYM Fst_def,GSYM Snd_def] >>
 rw[Ins_def,IN_def] >> rw[Suc_def])
(form_goal “!a:1->Exp(Exp(X,1+1)* N,1+1) a'.
 Cdr(X) o Pa(a,a') =TRUE <=>
  (!xsn : 1 -> Exp(X, 1+1) * N.
     IN(xsn, a') <=>
     xsn = Pa(Empty(X), O) |
     ?xsn0: 1 -> Exp(X,1+1) * N  x:1->X.
       IN(xsn0, a) &
       ~IN(x, Fst(xsn0)) & xsn = Pa(Ins(x, Fst(xsn0)), Suc(Snd(xsn0))))”);
(* given a: 1-> Exp(Exp(X,1+1),1+1)
    want a': 1-> Exp(Exp(X,1+1),1+1), which is an arrow:
   Exp(X,2) -> 2,saying that "is" in the set a', then its transpose is the set 
   a'*)
val Cdsi_def = 
define_fsym("Cdsi",[dest_var (rastt "a : 1->Exp(Exp(X,1+1)*N,1+1)")]) (qform2IL [‘xsn : 1->Exp(X,2) * N’]
 ‘xsn = Pa(Empty(X), O) |
     ?xsn0: 1 -> Exp(X,1+1) * N  x:1->X.
       IN(xsn0, a) &
       ~IN(x, Fst(xsn0)) & xsn = Pa(Ins(x, Fst(xsn0)), Suc(Snd(xsn0)))’);
val Cdsi_property = proved_th $
e0
(rw[Cdsi_def] >> rpt strip_tac >>
 rw[o_assoc,DISJ_def,Pa_distr] >> 
 once_rw[Ex_def] >> rw[o_assoc,Ex_def] >>
 rw[CONJ_def,Pa_distr,o_assoc] >>
 rw[one_to_one_id,idR] >>
 once_rw[p31_def,p32_def,p33_def] >>
 rw[p12_of_Pa,o_assoc,Pa_distr] >>
 rw[Eq_property_TRUE,IN_def,Ins_def,NEG_def'] >>
 rw[GSYM Fst_def,GSYM Snd_def,Suc_def,idL])
(form_goal 
“!a: 1->Exp(Exp(X,1+1) * N,1+1) xsn. Cdsi(a) o xsn = TRUE <=>
 xsn = Pa(Empty(X), O) |
     ?xsn0: 1 -> Exp(X,1+1) * N  x:1->X.
       IN(xsn0, a) &
       ~IN(x, Fst(xsn0)) & xsn = Pa(Ins(x, Fst(xsn0)), Suc(Snd(xsn0))) ”);
val Cdf_precond = proved_th $
e0
(strip_tac >>
 qsuff_tac
 ‘?a'.
 !xsn. IN(xsn,a') <=> 
       (xsn = Pa(Empty(X), O) |
     ?xsn0: 1 -> Exp(X,1+1) * N  x:1->X.
       IN(xsn0, a) &
       ~IN(x, Fst(xsn0)) & xsn = Pa(Ins(x, Fst(xsn0)), Suc(Snd(xsn0))))’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘a'’ >>
      arw[] >> rpt strip_tac >> irule $ iffLR IN_EXT >> arw[]) >>
 qexists_tac ‘Tp1(Cdsi(a))’ >>
 rw[IN_Tp1] >> rw[Cdsi_property])
(form_goal “!a. ?!a'.
 !xsn. IN(xsn,a') <=> 
 (xsn = Pa(Empty(X), O) |
     ?xsn0: 1 -> Exp(X,1+1) * N  x:1->X.
       IN(xsn0, a) &
       ~IN(x, Fst(xsn0)) & xsn = Pa(Ins(x, Fst(xsn0)), Suc(Snd(xsn0))))”)
val Cdf_def = 
Rel2Ar_uex 
|> sspecl [rastt "Cdr(X)"]
|> rewr_rule[IL_lemma]
|> C mp Cdf_precond
|> qsimple_uex_spec "Cdf" [‘X’]
|> spec_all |> qgen ‘b’
|> qspecl [‘Cdf(X) o a’]
|> rewr_rule[] |> qgen ‘a’;
val Cdf_monotone = mk_monotone Cdf_def;
val Cd's_def = mk_prim Cdf_def;
val Cds_def = mk_LFP (rastt "Cd's(X)");
val Cds_cond = mk_cond Cds_def Cd's_def;
val Cds_SS = mk_SS Cds_def Cd's_def;
val Cd_rules0 = mk_rules Cdf_monotone Cds_SS Cds_cond;
val Cd_cases0 = mk_cases Cdf_monotone Cd_rules0 Cds_cond;
val Cd_ind0 = mk_ind Cds_cond;
val Cd_ind1 = mk_ind1 Cdf_def Cd_ind0;
val Cd_ind2 = mk_ind2 Cd_ind1;
val Cd_cases1 = mk_case1 Cdf_def Cd_cases0;
val Cd_rules1 = mk_rules1 Cdf_def Cd_rules0;
val Cd_rules2 = mk_rules2 Cd_rules1;
val Cd_rules3 = mk_rules3 Cd_rules2;
end

val Cd_ind = Cd_ind2 |> store_as "Cd_ind";
val Cd_cases = Cd_cases1 |> store_as "Cd_cases";
val Cd_rules = Cd_rules3 |> store_as "Cd_rules";



fun dest_cross t = 
    case view_term t of 
        vFun("*",_,[A,B])=> (A,B)
      | _ => raise simple_fail "dest_cross.not a cross";
               

fun mk_Pair a b = mk_fun "Pa" [a,b] 


fun forall_cross_fconv f = 
    let val (pv as (n,s),b) = dest_forall f 
        val pset = s |> dest_sort |> #2  |> el 2
        val (A,B) = dest_cross pset 
        val pt = mk_var pv
        val eth = Pair_has_comp |> specl [A,B,pt]
        val (ocv1 as (ocn1,ocs1),ob1) = dest_exists (concl eth) 
        val (ocv2 as (ocn2,ocs2),ob2) = dest_exists ob1
        val avoids = fvf b
        val ct1 = pvariantt avoids (mk_var ocv1)
        val ct2 = pvariantt avoids (mk_var ocv2)
        val (cv1 as (cn1,cs1)) = dest_var ct1
        val (cv2 as (cn2,cs2)) = dest_var ct2
        val b1 = substf (ocv1,ct1) ob1
        val b2 = substf (ocv2,ct2) (substf (ocv1,ct1) ob2)
        val pair = mk_Pair ct1 ct2 
        val b' = substf (pv,pair) b
        val new = mk_forall cn1 cs1 (mk_forall cn2 cs2 b')
        val l2r = f |> assume |> allE pair 
                    |> simple_genl [cv1,cv2]
                    |> disch f
        val eth1 = b1 |> assume 
        val r2l = new |> assume |> specl [ct1,ct2]
                      |> rewr_rule[GSYM $ assume b2]
                      |> existsE cv2 eth1 
                      |> existsE cv1 eth
                      |> allI pv
                      |> disch new
    in dimpI l2r r2l 
    end

val Pair_def' = Pa_def |> rewr_rule[GSYM Fst_def,GSYM Snd_def]
                       |> spec_all |> conjE1 |> gen_all
                       |> store_as "Pair_def'";

val Cds_ind = prove_store("Cds_ind",
e0
(rpt gen_tac >> disch_tac >>
 qsuff_tac
 ‘!xsn. IN(xsn,Cds(X)) ==> IN(xsn,ss)’
 >-- (fconv_tac (depth_fconv no_conv forall_cross_fconv) >> rw[]) >>
 match_mp_tac Cd_ind (* irule does not work *) >>
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >> 
 rw[Pair_def'] >> arw[]
 )
(form_goal 
 “!X ss.IN(Pa(Empty(X),O),ss) & 
 (!xs0 n0 x. IN(Pa(xs0,n0),ss)  & ~(IN(x,xs0)) ==> 
  IN(Pa(Ins(x,xs0),Suc(n0)),ss)) ==> 
 !xs n. IN(Pa(xs,n),Cds(X)) ==> IN(Pa(xs,n),ss)”));


val Cd_induct0 = prove_store("Cd_induct0",
e0
(rpt strip_tac >>
 qsspecl_then [‘Tp1(P)’] assume_tac Cds_ind >>
 fs[IN_Tp1] >> first_x_assum irule >> arw[])
(form_goal 
 “!X P .P o Pa(Empty(X),O) = TRUE & 
 (!xs0 n0 x:1->X. P o Pa(xs0,n0) = TRUE & ~(IN(x,xs0)) ==> 
  P o Pa(Ins(x,xs0),Suc(n0)) = TRUE) ==> 
 !xs n. IN(Pa(xs,n),Cds(X)) ==> P o Pa(xs,n) = TRUE ”));

(*
val Cd_induct = prove_store("Cd_induct",
e0
(strip_tac >> assume_tac (Cd_induct0 |> qspecl [‘X’] 
            |> fVar_sInst_th “P(xsn:mem(Pow(X) * N))”
               “P(Fst(xsn:mem(Pow(X) * N)),Snd(xsn))”
            |> rewr_rule[Pair_def']) >> arw[])
(form_goal 
 “!X.P(Empty(X),O) & 
 (!xs0 n0 x:mem(X). P(xs0,n0) & ~(IN(x,xs0)) ==> 
  P(Ins(x,xs0),Suc(n0))) ==> 
 !xs n. IN(Pair(xs,n),Cds(X)) ==> P(xs,n)”));
*) 



val Fin_induct = prove_store("Fin_induct",
e0
(rw[Fin_def] >> rpt strip_tac >>
 qsspecl_then [‘Tp1(P)’] assume_tac FI_ind >>
 fs[IN_Tp1] >> first_x_assum irule >> arw[])
(form_goal 
 “!X P. P o Empty(X) = TRUE & 
 (!xs0 x:1->X. P o xs0 = TRUE ==> P o Ins(x,xs0) = TRUE) ==> 
 !xs. Fin(xs) ==> P o xs = TRUE”));
 

(*Card rel*)
val Cdr_def = qdefine_psym("Cdr",[‘xs:1->Exp(X,1+1)’,‘n:1->N’])
‘IN(Pa(xs,n),Cds(X))’ |> qgenl[‘X’,‘xs’,‘n’] 
|> store_as "Cdr_def";


val _ = new_psym2IL("Cdr",(rastt "Tp0(Cds(X))",List.map (dest_var o rastt) ["xs:A->Exp(X,1+1)","n:A->N"]))

val Cdr_induct = Cd_induct0 |> rewr_rule[GSYM Cdr_def]
                           |> store_as "Cdr_induct";


val Cdr_Empty = prove_store("Cdr_Empty",
e0
(rw[Cdr_def,Cd_rules])
(form_goal
 “!X.Cdr(Empty(X),O)”));

val Cdr_Ins = Cd_rules |> conjE2 |> spec_all |> undisch |> gen_all |> disch_all
                       |> gen_all
                       |> qspecl [‘X’,‘Pa(xs0: 1->Exp(X,1+1),n:1->N)’]
                       |> rewr_rule[GSYM Cdr_def,Pair_def']
                       |> gen_all
                       |> store_as "Cdr_Ins";



val Ins_NONEMPTY = prove_store("Ins_NONEMPTY",
e0
(rpt strip_tac >> rw[GSYM IN_EXT,Ins_def1,Empty_def] >>
 ccontra_tac >> first_x_assum (qspecl_then [‘x0’] assume_tac) >> fs[])
(form_goal
 “!X x0 xs:1-> Exp(X,1+1).~(Ins(x0,xs) = Empty(X))”));

val IN_Ins_SND = prove_store("IN_Ins_SND",
e0
(rw[Ins_def1] >> rpt strip_tac)
(form_goal “!X x0 xs0:1->Exp(X,1+1) x. IN(x, Ins(x0, xs0)) & (~(x = x0)) ==> IN(x,xs0)”));

val Cdr_Empty_unique = prove_store("Cdr_Empty_unique",
e0
(rw[Cdr_def] >> once_rw[Cd_cases] >> rpt strip_tac >>
 fs[Pa_eq_eq,GSYM Ins_NONEMPTY])
(form_goal
 “!X n.Cdr(Empty(X),n) ==> n = O”));




val Del_Ins_SWAP = prove_store("Del_Ins_SWAP",
e0
(rpt strip_tac >> rw[GSYM IN_EXT,Ins_def1,Del_def1] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[])
(form_goal
 “!X x0 x:1->X.(~(x0 = x)) ==> !xs.Del(Ins(x0, xs), x) = Ins(x0,Del(xs,x))”));


fun exists_cross_fconv f = 
    let val (pv as (n,s),b) = dest_exists f 
        val pset = s |> dest_sort |> #2  |> el 2
        val (A,B) = dest_cross pset 
        val pt = mk_var pv
        val eth = Pair_has_comp |> specl [A,B,pt]
        val (ocv1 as (ocn1,ocs1),ob1) = dest_exists (concl eth) 
        val (ocv2 as (ocn2,ocs2),ob2) = dest_exists ob1
        val avoids = fvf b
        val ct1 = pvariantt avoids (mk_var ocv1)
        val ct2 = pvariantt avoids (mk_var ocv2)
        val (cv1 as (cn1,cs1)) = dest_var ct1
        val (cv2 as (cn2,cs2)) = dest_var ct2
        val b1 = substf (ocv1,ct1) ob1
        val b2 = substf (ocv2,ct2) (substf (ocv1,ct1) ob2)
        val pair = mk_Pair ct1 ct2 
        val b' = substf (pv,pair) b
        val new0 = (mk_exists cn2 cs2 b')
        val new = mk_exists cn1 cs1 (mk_exists cn2 cs2 b')
        val l2r = b |> assume 
                    |> conv_rule (basic_fconv (rewr_conv (assume b2)) no_fconv)
                    |> existsI cv2 ct2 b'
                    |> existsI cv1 ct1 new0
                    |> existsE cv2 (assume b1)
                    |> existsE cv1 eth
                    |> existsE pv (assume f)
                    |> disch f
        val r2l = b'|> assume 
                    |> existsI pv pair b
                    |> existsE cv2 (assume new0)
                    |> existsE cv1 (assume new)
                    |> disch new
    in dimpI l2r r2l
    end

val Cdr_Ins = 
Cd_cases |> qspecl [‘Pa(Ins(x0:1->X,xs0),n:1->N)’]
|> rewr_rule[Pa_eq_eq,Ins_NONEMPTY] 
|> conv_rule (depth_fconv no_conv exists_cross_fconv)
|> rewr_rule[Pair_def',GSYM Cdr_def]
|> gen_all |> store_as "Cdr_Ins";

val Cdr_Empty = Cd_rules |> conjE1 |> gen_all |> rewr_rule[GSYM Cdr_def] 
                         |> store_as "Cdr_Empty";


fun ind_with1 th = 
 pop_assum strip_assume_tac >>
 arw[] >> match_mp_tac th >>
 pop_assum (assume_tac o GSYM) >> arw[]


val Cdr_Tp0_Cds = proved_th $
e0
(rw[Cdr_def] >> rpt strip_tac >>
 qsuff_tac ‘IN(Pa(xs, n), Tp1(Tp0(Cds(X)))) <=> Tp0(Cds(X)) o Pa(xs, n) = TRUE’
 >-- rw[Tp1_Tp0_inv] >>
 rw[IN_Tp1])
(form_goal “!xs n:1->N. Cdr(xs,n) <=> Tp0(Cds(X)) o Pa(xs,n) = TRUE”)


val Cdr_Del_IL = proved_th $
e0
(exists_tac $ qform2IL [‘xs:1->Exp(X,1+1)’,‘n:1->N’] ‘Cdr(xs,n) & !x. IN(x,xs) ==> Cdr(Del(xs,x),Pre(n))’ >>
 rw[o_assoc,Pa_distr,CONJ_def,All_def,IMP_def] >>
 once_rw[p31_def,p32_def,p33_def] >> rw[p12_of_Pa,Pa_distr,o_assoc] >>
 rw[Cdr_Tp0_Cds] >> rw[Del_def,Pre_def,IN_def])
(form_goal “?P. !xs:1->Exp(X,1+1) n. (Cdr(xs,n) & !x. IN(x,xs) ==> Cdr(Del(xs,x),Pre(n))) <=> P o Pa(xs,n) = TRUE ”)




val Cdr_Del = prove_store("Cdr_Del",
e0
(strip_tac >> assume_tac Cdr_Del_IL >>
 ind_with1 (Cdr_induct |> qspecl [‘X’]) >>
 rw[Cdr_Empty,Empty_def] >> rpt strip_tac (* 2 *)
 >-- (irule $ iffRL Cdr_Ins >>
     qexistsl_tac [‘xs0’,‘n0’,‘x’] >> arw[]) >>
 rw[Pre_Suc] >>
 qcases ‘x' = x’ >> fs[] (* 2 *)
 >-- (drule Del_Ins >> arw[]) >>
 qby_tac ‘IN(x',xs0)’ >-- (irule IN_Ins_SND >> qexists_tac ‘x’ >> arw[]) >>
 first_x_assum drule >> 
 qcases ‘n0 = O’ 
 >-- (fs[] >> qsuff_tac ‘xs0 = Empty(X)’ >-- (strip_tac >> fs[Empty_def]) >>
      qpick_x_assum ‘Cdr(xs0, O)’ mp_tac >>
      rw[Cdr_def] >> once_rw[Cd_cases] >> rw[Pa_eq_eq,GSYM Suc_NONZERO] >>
      rpt strip_tac) >>
 fs[O_xor_Suc] >> fs[Pre_Suc] >> 
 qby_tac ‘Del(Ins(x, xs0), x') = Ins(x, Del(xs0,x'))’
 >-- (irule Del_Ins_SWAP >> ccontra_tac >> fs[]) >>
 arw[] >> irule $ iffRL Cdr_Ins >> 
 qexistsl_tac [‘Del(xs0, x')’,‘n0'’,‘x’] >> arw[Del_def1])
(form_goal
 “!X xs:1->Exp(X,1+1) n.Cdr(xs,n) ==> 
  Cdr(xs,n) & !x. IN(x,xs) ==> Cdr(Del(xs,x),Pre(n))”));

val E1_def1 = prove_store ("E1_def1",
e0
(rpt strip_tac >> rw[E1_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘x’ >> arw[]) >>
 pop_assum (assume_tac o uex_expand) >> arw[])
(form_goal “!X Y pxy:X * Y->1+1 y. E1(X) o Tp(pxy) o y = TRUE <=> 
 ?!x. pxy o Pa(x,y) = TRUE”));

val Fin_Card_IL = proved_th $
e0
(exists_tac $ qform2IL [‘xs:1->Exp(X,1+1)’] ‘?!n.Cdr(xs,n)’ >>
 rw[E1_def1,o_assoc,p12_of_Pa,Pa_distr,Cdr_Tp0_Cds])
(form_goal “?P. !xs:1->Exp(X,1+1). P o xs = TRUE <=> ?!n.Cdr(xs,n)”)

val Fin_Card = prove_store("Card_Fun",
e0
(strip_tac >> assume_tac (GSYM Fin_Card_IL) >>
 ind_with1 Fin_induct >> rpt strip_tac (* 2 *)
 >-- (uex_tac >> qexists_tac ‘O’ >> rw[Cdr_Empty,Cdr_Empty_unique]) >>
 pop_assum (strip_assume_tac o uex_expand) >> uex_tac >>
 qcases ‘IN(x,xs0)’ 
 >-- (drule Ins_absorb >> arw[] >> qexists_tac ‘n’ >> arw[]) >>
 qexists_tac ‘Suc(n)’ >> rpt strip_tac (* 2 *)
 >-- (irule $ iffRL Cdr_Ins >> qexistsl_tac [‘xs0’,‘n’,‘x’] >> arw[]) >>
 drule Cdr_Del >> fs[] >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 fs[Ins_def1] >> drule Del_Ins >> fs[] >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >> arw[] >>
 qsuff_tac ‘~(n' = O)’ >-- (rw[O_xor_Suc] >> strip_tac >> arw[Pre_Suc]) >>
 rw[O_xor_Suc] >> qpick_x_assum ‘Cdr(Ins(x, xs0), n')’ mp_tac >>
 strip_tac >> drule $ iffLR Cdr_Ins >> pop_assum strip_assume_tac >>
 qexists_tac ‘b’ >> arw[])
(form_goal
 “!X xs:1->Exp(X,1+1).Fin(xs) ==> ?!n.Cdr(xs,n)”));


val Fin_Tp0_FIs = proved_th $
e0
(rw[Fin_def] >> rpt strip_tac >>
 qsuff_tac ‘IN(xs, Tp1(Tp0(FIs(X)))) <=> Tp0(FIs(X)) o xs = TRUE’
 >-- rw[Tp1_Tp0_inv] >>
 rw[IN_Tp1])
(form_goal “!xs. Fin(xs) <=> Tp0(FIs(X)) o xs = TRUE”)

val _ = new_psym2IL("Fin",(rastt "Tp0(FIs(X))",List.map (dest_var o rastt) ["xs:A->Exp(X,1+1)"]))


val CARD_def0 = define_fsym("CARD",[("X",ob_sort)])
    (qform2IL [‘xs:1->Exp(X,1+1)’,‘n:1->N’]
    ‘(Fin(xs) & Cdr(xs,n)) | (~Fin(xs) & n = O)’) |> gen_all
    |> store_as "CARD_def0";

val CARD_def = prove_store("CARD_def",
e0
(rpt strip_tac >> rw[Holds_def,CARD_def0] >>
 rw[o_assoc,DISJ_def,Pa_distr,p12_of_Pa,CONJ_def,NEG_def',Eq_property_TRUE] >>
 rw[Fin_Tp0_FIs,Cdr_Tp0_Cds,one_to_one_id,idR])
(form_goal “!xs:1->Exp(X,1+1) n. Holds(CARD(X),xs,n) <=> 
 (Fin(xs) & Cdr(xs,n)) | (~Fin(xs) & n = O)”));


val CARD_unique = proved_th $
e0
(rpt strip_tac >> rw[CARD_def] >> 
 qcases ‘Fin(xs)’ 
 >-- (drule Fin_Card >> pop_assum (strip_assume_tac o uex_expand) >>
      uex_tac >> qexists_tac ‘n’ >> arw[]) >>
 uex_tac >> qexists_tac ‘O’ >> arw[])
(form_goal “!X xs:1-> Exp(X,1+1). ?!n. Holds(CARD(X),xs,n)”)
 


val Cd0_def = P2fun_uex |> qsspecl [‘CARD(X)’]
                    |> C mp (CARD_unique |> qspecl [‘X’]) 
                    |> qsimple_uex_spec "Cd0" [‘X’]
                    |> gen_all |> store_as "Cd0_def";


val Card_def = qdefine_fsym ("Card",[‘xs:1->Exp(X,1+1)’])
                            ‘Cd0(X) o xs’
                            |> gen_all |> store_as "Card_def";

val Del_Empty = prove_store("Del_Empty",
e0
(rw[GSYM IN_EXT,Del_def1,Empty_def])
(form_goal
 “!X x. Del(Empty(X),x) = Empty(X)”));

val Ins_eq_eq = prove_store("Ins_eq_eq",
e0
(rpt strip_tac >-- (ccontra_tac >>
 qsuff_tac ‘~(IN(a2,Ins(a2,s2)))’
 >-- rw[Ins_def1] >>
 qsuff_tac ‘~(IN(a2,Ins(a1,s1)))’
 >-- arw[] >>
 arw[Ins_def1] >> flip_tac >> first_x_assum accept_tac) >>
 irule $ iffLR IN_EXT >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘IN(x,Ins(a1,s1))’ >-- arw[Ins_def1] >> rfs[] >>
      fs[Ins_def1] >> pop_assum (assume_tac o GSYM) >> fs[]) >>
 qpick_x_assum ‘Ins(a1, s1) = Ins(a2, s2)’ (assume_tac o GSYM) >>
 qby_tac ‘IN(x,Ins(a2,s2))’ >-- arw[Ins_def1] >>
 rfs[] >> fs[Ins_def1] >> pop_assum (assume_tac o GSYM) >> fs[])
(form_goal
 “!A a1:1->A s1 a2 s2. ~(IN(a1,s1)) & ~(IN(a2,s2)) & ~(IN(a1,s2)) & ~(IN(a2,s1)) & 
 Ins(a1,s1) = Ins(a2,s2) ==> a1 = a2 & s1 = s2”));

val Fin_Empty = FI_rules |> conjE1 |> rewr_rule[GSYM Fin_def] 
                         |> gen_all |> store_as "Fin_Empty";

val Fin_Ins = FI_rules |> conjE2 |> rewr_rule[GSYM Fin_def]
                       |> spec_all |> undisch |> gen_all |> disch_all 
                       |> gen_all |> store_as "Fin_Ins";

val Fin_Del0_IL = proved_th $
e0
(exists_tac $ qform2IL [‘xs:1->Exp(X,1+1)’] ‘Fin(xs) & !x. Fin(Del(xs,x))’ >>
 rw[CONJ_def,o_assoc,Pa_distr,p12_of_Pa,idL,All_def] >>
 rw[Fin_Tp0_FIs,Del_def])
(form_goal “?P.!xs:1->Exp(X,1+1). (Fin(xs) &  !x. Fin(Del(xs,x))) <=> P o xs = TRUE”)

val Fin_Del0 = prove_store("Fin_Del",
e0
(strip_tac >> 
 assume_tac Fin_Del0_IL >> ind_with1 (Fin_induct |> qspecl [‘X’]) >> 
 rw[Fin_Empty,Del_Empty] >> rpt strip_tac (* 2 *)
 >-- (drule Fin_Ins >> arw[]) >>
 qcases ‘x = x'’ (* 2 *)
 >-- (arw[] >> qcases ‘IN(x',xs0)’ (* 2 *)
     >-- (drule Ins_absorb >> arw[]) >>
     drule Del_Ins >> arw[]) >>
 drule Del_Ins_SWAP >> arw[] >>
 irule Fin_Ins >> arw[])
(form_goal
 “!X xs:1->Exp(X,1+1).Fin(xs) ==> Fin(xs) &  !x. Fin(Del(xs,x)) ”));
 
val Fin_Del = prove_store("Fin_Del",
e0
(rpt strip_tac >> drule Fin_Del0 >> arw[])
(form_goal “!X xs:1->Exp(X,1+1).Fin(xs) ==> !x. Fin(Del(xs,x))”));

val Card_Fin = prove_store("Card_Fin",
e0
(rpt strip_tac >> arw[Card_def,Cd0_def,CARD_def])
(form_goal
 “!X xs:1->Exp(X,1+1). Fin(xs) ==>
  (!n. Card(xs) = n <=> Cdr(xs,n))”));


val Card_Empty = prove_store("Card_Empty",
e0
(strip_tac >> qspecl_then [‘X’] assume_tac Fin_Empty >>
 drule Card_Fin >> arw[Cdr_Empty])
(form_goal
 “!X. Card(Empty(X)) = O”));


val Cdr_Card = prove_store("Cdr_Card",
e0
(rpt strip_tac >> drule Card_Fin >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal “!X xs:1-> Exp(X,1+1). Fin(xs) ==> 
 Cdr(xs, Card(xs))”));


val Card_Ins = prove_store("Card_Ins",
e0
(rpt strip_tac >> drule Fin_Ins >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Card_Fin >> arw[] >> irule $ iffRL Cdr_Ins >>
 qexistsl_tac [‘xs’,‘Card(xs)’,‘x’] >> arw[] >>
 (* Cdr(xs, Card(xs))*)
 rw[Card_def] >> 
 qsspecl_then [‘xs’,‘Cd0(X) o xs’] assume_tac Cd0_def >>
 fs[] >> fs[CARD_def])
(form_goal
 “!X xs:1-> Exp(X,1+1). 
  Fin(xs) ==> !x.~(IN(x,xs)) ==> Card(Ins(x,xs)) = Suc(Card(xs))”));



val Card_Del = prove_store("Card_Del",
e0
(rpt strip_tac >> drule Fin_Del >> 
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 drule Card_Fin >> arw[] >>
 irule (Cdr_Del |> spec_all |> undisch |> conjE2 |> disch_all |> gen_all) >>
 arw[] >> irule Cdr_Card >> arw[])
(form_goal
 “!X xs:1->Exp(X,1+1). Fin(xs) ==> 
  !x. IN(x,xs) ==> Card(Del(xs,x)) = Pre(Card(xs))”));
 

