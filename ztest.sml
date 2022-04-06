

val ZR_def = 
AX1 |> qspecl [‘N * N’,‘N * N’] |> uex2ex_rule
    |> fVar_sInst_th “P(mn:mem(N * N),m'n':mem(N * N))”
       “Add(Fst(mn:mem(N * N)),Snd(m'n':mem(N * N))) = 
        Add(Fst(m'n'),Snd(mn))”
    |> qSKOLEM "ZR" [] 
    |> qspecl [‘Pair(x:mem(N),y:mem(N))’,
               ‘Pair(u:mem(N),v:mem(N))’] 
    |> qgenl [‘x’,‘y’,‘u’,‘v’]  
    |> rewr_rule[Pair_def']
    |> store_as "ZR_def";



fun dest_cross t = 
    case view_term t of 
        vFun("*",_,[A,B])=> (A,B)
      | _ => raise simple_fail "dest_cross.not a cross";
               

fun mk_Pair a b = mk_fun "Pair" [a,b]

(*
fun forall_cross_fconv f = 
    let val (pv as (n,s),b) = dest_forall f 
        val pset = s |> dest_sort |> #2  |> hd
        val (A,B) = dest_cross pset 
        val pt = mk_var pv
        val eth = Pair_has_comp |> specl [A,B,pt]
        val (cv1 as (cn1,cs1),b1) = dest_exists (concl eth) 
        val (cv2 as (cn2,cs2),b2) = dest_exists b1
        val ct1 = mk_var cv1
        val ct2 = mk_var cv2
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



val f = “∀b':mem(N * N).P(a:mem(N),b:mem(N),b')”; 
val f = “∀a1 a2 a3. Holds(ZR,a1,a2) & Holds(ZR,z2,z3)”;
*)

fun forall_cross_fconv f = 
    let val (pv as (n,s),b) = dest_forall f 
        val pset = s |> dest_sort |> #2  |> hd
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

(*
pred_fconv ((try_conv (rewr_conv (GSYM $ assume “b' = Pair(a':mem(N), b'':mem(N))”))))
 “P(a:mem(N), b:mem(N), Pair(a':mem(N), b'':mem(N)))”

 (redepth_fconv no_conv exists_cross_fconv)
 val f = “∃a:mem(A) b:mem(A* B).P(a,b)”
val f = “∃b:mem(A* B).P(a,b)”
exists_cross_fconv “∃b:mem(A* B).P(a:mem(A),b)”
 
 “∃a:mem(A) b b':mem(A * B) b'':mem(A  * B). P(a,b,b',b'')”


fun exists_cross_fconv f = 
    let val (pv as (n,s),b) = dest_exists f 
        val pset = s |> dest_sort |> #2  |> hd
        val (A,B) = dest_cross pset 
        val pt = mk_var pv
        val eth = Pair_has_comp |> specl [A,B,pt]
        val (cv1 as (cn1,cs1),b1) = dest_exists (concl eth) 
        val (cv2 as (cn2,cs2),b2) = dest_exists b1
        val ct1 = mk_var cv1
        val ct2 = mk_var cv2
        val pair = mk_Pair ct1 ct2 
        val b' = substf (pv,pair) b
        val new0 = mk_exists cn2 cs2 b'
        val new = mk_exists cn1 cs1 new0
        val l2r = b |> assume |> rewr_rule[assume b2]
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


 val f = “∃b:mem(A* B).P(a:mem(A),b)”;
*)
 
fun exists_cross_fconv f = 
    let val (pv as (n,s),b) = dest_exists f 
        val pset = s |> dest_sort |> #2  |> hd
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


(*depth_fconv no_conv forall_cross_fconv “!a:mem(N * N) b:mem(N * N). P(a,b)”
not doing the desired thing *)


val ZR_Refl = prove_store("ZR_Refl",
e0
(rw[Refl_def,ZR_def] >> fconv_tac forall_cross_fconv >>
 rw[ZR_def])
(form_goal
 “Refl(ZR)”));


fun basic_fconv_tac c fc = fconv_tac $ basic_fconv c fc
fun depth_fconv_tac c fc = fconv_tac $ depth_fconv c fc

(*use add_sub*)
val ZR_Trans = prove_store("ZR_Trans",
e0
(rw[Trans_def] >> depth_fconv_tac no_conv forall_cross_fconv >>
 rw[ZR_def] >> 
 qsuff_tac
 ‘!a1 b1 a2 b2 a3 b3.
  Add(a1,b2) = Add(a2,b1) & Add(a2,b3) = Add(a3,b2) ==>
  Add(a1,b3) = Add(a3,b1)’
 >-- rw[] >>
 rpt strip_tac >>
 irule Add_eq_eq >> qexists_tac ‘b2’ >>
 once_rw[GSYM Add_assoc] >>
 qby_tac
 ‘Add(b3,b2) = Add(b2,b3) & Add(b1,b2) = Add(b2,b1)’ 
 >-- (strip_tac 
     >-- qspecl_then [‘b2’,‘b3’] accept_tac Add_comm
     >-- qspecl_then [‘b2’,‘b1’] accept_tac Add_comm) >>
 arw[] >>
 rw[Add_assoc] >> once_arw[] >> 
 qpick_x_assum ‘Add(a2, b3) = Add(a3, b2)’
 (assume_tac o GSYM) >> once_arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘b3’,‘b1’] assume_tac Add_comm >>
 once_arw[] >> rw[])
(form_goal
 “Trans(ZR)”));

 
val ZR_Sym = prove_store("ZR_Sym",
e0
(rw[Sym_def] >> depth_fconv_tac no_conv forall_cross_fconv >>
 rw[ZR_def] >>  rpt strip_tac >> arw[])
(form_goal
 “Sym(ZR)”));


val ZR_ER = prove_store("ZR_ER",
e0
(rw[ER_def,ZR_Sym,ZR_Refl,ZR_Trans])
(form_goal “ER(ZR)”));



val Sg_def = P2fun'|> qspecl [‘A’,‘Pow(A)’] 
                   |> fVar_sInst_th “P(a:mem(A),s:mem(Pow(A)))”
                      “!a0. IN(a0,s) <=> a0 = a:mem(A)”
                   |> C mp 
                      (IN_def_P |> spec_all
                                |> fVar_sInst_th “P(a0:mem(A))”
                                   “a0 = a:mem(A)”
                                |> qgen ‘a’)
                   |> qSKOLEM "Sg" [‘A’] |> gen_all
                   |> store_as "Sg_def";

val Sing_def = qdefine_fsym ("Sing",[‘a:mem(A)’])
                            ‘App(Sg(A),a:mem(A))’
                            |> gen_all |> store_as "Sing_def";


val Ri_def = P2fun'|> qspecl [‘Pow(A)’,‘Pow(B)’] 
                   |> fVar_sInst_th “P(sa:mem(Pow(A)),sb:mem(Pow(B)))”
                      “!b. IN(b,sb) <=> ∃a. IN(a,sa) & Holds(r:A~>B,a,b)”
                   |> C mp 
                      (IN_def_P |> qspecl [‘B’]
                                |> fVar_sInst_th “P(b:mem(B))”
                                   “∃a. IN(a,sa) & Holds(r:A~>B,a,b)”
                                |> qgen ‘sa’)
                   |> qSKOLEM "Ri" [‘r’] |> gen_all
                   |> qspecl [‘A’,‘B’,‘r:A~>B’,‘s:mem(Pow(A))’]
                   |> qgenl [‘A’,‘B’,‘r’,‘s’]
                   |> store_as "Ri_def";




(*Relational singleton image*)
val Rsi_def = qdefine_fsym ("Rsi",[‘r:A~>B’])
                            ‘Ri(r:A~>B) o Sg(A)’
                            |> gen_all |> store_as "Rsi_def";


val rsi_def = qdefine_fsym ("rsi",[‘r:A~>B’,‘a:mem(A)’])
                            ‘App(Rsi(r),a)’
                            |> gen_all |> store_as "rsi_def";

val IN_rsi = prove_store("IN_rsi",
e0
(rw[rsi_def,Rsi_def,Ri_def,App_App_o,Sg_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> rfs[] >>
 qexists_tac ‘a1’ >> arw[])
(form_goal “∀A r:A~>A a1 a2. IN(a2,rsi(r,a1)) ⇔ Holds(r,a1,a2) ”));


val ER_Holds = prove_store("ER_Holds",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum (qspecl_then [‘a2’] assume_tac) >> fs[ER_def,Refl_def]) >>
 dimp_tac >> strip_tac >> fs[ER_def,Sym_def,Trans_def] (* 2 *)
 >-- (first_x_assum irule >> qexists_tac ‘a1’ >> arw[] >> first_x_assum irule >>
     arw[]) >>
 first_x_assum irule >> qexists_tac ‘a2’ >> arw[])
(form_goal “∀A r:A~>A. ER(r) ⇒ ∀a1 a2. 
 ((∀x.Holds(r,a1,x) ⇔ Holds(r,a2,x)) ⇔ Holds(r,a1,a2))”));
 
val rsi_eq_ER = prove_store("rsi_eq_ER",
e0
(rw[GSYM IN_EXT_iff,IN_rsi] >> 
 rpt strip_tac >> drule ER_Holds >> arw[])
(form_goal “!A r:A~>A.ER(r) ==> 
 !a1 a2. rsi(r,a1) = rsi(r,a2) <=> Holds(r,a1,a2)”));



val Z_def = Thm_2_4 |> qspecl [‘Pow(N * N)’]
                    |> fVar_sInst_th “P(s:mem(Pow(N * N)))”
                    “?n. s = rsi(ZR,n)”
                    |> qSKOLEM "Z" []
                    |> qSKOLEM "iZ" []
                    |> store_as "Z_def";

val iZ_Inj = Z_def |> conjE1 |> store_as "iZ_Inj"
                   |> store_as "iZ_Inj";


(*as in iN_eq_eq*)
val iZ_eq_eq = iZ_Inj |> rewr_rule[Inj_def]
     

(* (?(n : mem(N * N)). a# = rsi(ZR, n#)) <=>
 ?n1 n2. ... such a conv, to corresponds to L's lambda ver *)

(*compare to iN_inNs*)
val iZ_rsi = prove_store("iZ_rsi",
e0
(strip_tac >> strip_assume_tac Z_def >>
 first_x_assum (qspecl_then [‘App(iZ,z)’] assume_tac) >>
 (*stupid step, ?(b : mem(Z)). App(iZ, z) = App(iZ, b#)*)
 qby_tac ‘?b. App(iZ,z) = App(iZ,b)’ 
 >-- (qexists_tac ‘z’ >> rw[]) >>
 first_x_assum (drule o iffRL) >>
 pop_assum strip_assume_tac >>
 qsspecl_then [‘n’] strip_assume_tac Pair_has_comp >>
 fs[] >> qexistsl_tac [‘a’,‘b’] >> arw[])
(form_goal 
 “!z:mem(Z).?m n. App(iZ,z) = rsi(ZR,Pair(m,n))”));

val rsi_iZ = prove_store("rsi_iZ",
e0
(rpt strip_tac >> strip_assume_tac Z_def >>
 first_x_assum
 (qspecl_then [‘rsi(ZR,Pair(m,n))’] assume_tac) >>
 first_x_assum $ irule o iffLR >>
 qexists_tac ‘Pair(m,n)’ >> rw[])
(form_goal 
 “!m n. ?z. rsi(ZR,Pair(m,n)) = App(iZ,z)”));


val resp_def = 
 qdefine_psym("resp",[‘f:A->B’,‘r1:A~>A’,‘r2:B~>B’])
 ‘!y z.Holds(r1,y,z) ==> Holds(r2,App(f:A->B,y),App(f,z))’
 |> gen_all |> store_as "resp_def";


val rext_def = AX1 |> qspecl [‘Pow(A)’,‘Pow(B)’] 
                   |> fVar_sInst_th “P(sa:mem(Pow(A)),sb:mem(Pow(B)))”
                      “?a b.sa = rsi(r1:A~>A,a) & sb = rsi(r2:B~>B,b) & 
                            App(f,a) = b”
                   |> uex2ex_rule
                   |> qSKOLEM "rext" [‘f’,‘r1’,‘r2’]
                   |> gen_all |> store_as "rext_def";                       


val prrel_def = AX1 |> qspecl [‘A * B’,‘A * B’]
                    |> fVar_sInst_th “P(ab1:mem(A * B),ab2:mem(A * B))”
                       “Holds(r1:A~>A,Fst(ab1),Fst(ab2)) &
                        Holds(r2:B~>B,Snd(ab1),Snd(ab2))”
                    |> uex2ex_rule |> qSKOLEM "prrel" [‘r1’,‘r2’]
                    |> qspecl [‘Pair(a1:mem(A),b1:mem(B))’,
                               ‘Pair(a2:mem(A),b2:mem(B))’]
                    |> rewr_rule[Pair_def']
                    |> qgenl [‘A’,‘r1’,‘B’,‘r2’,‘a1’,‘b1’,‘a2’,‘b2’]
                    |> store_as "prrel_def";


(*
we really want to check only resp, not biresp, so 
  App(Image(f#), rsi(r1#, a#)) = rsi(r2#, App(f#, a#)) 
is wrong, it is only:
  App(Image(f#), rsi(r1#, a#)) ⊆ rsi(r2#, App(f#, a#)):
 Larry is not claiming it as well, Larry is using Abs_Integ o Image(f), which is only one direction of the implication

*)




val main = prove_store("main",
e0
(rpt strip_tac >> assume_tac 
 (P2fun' |> qspecl [‘Q1’,‘Q2’] 
        |> fVar_sInst_th “P(q1:mem(Q1),q2:mem(Q2))”
           “Holds(rext(f:A->B, r1, r2), 
                      App(i1:Q1->Pow(A), q1), 
                      App(i2:Q2->Pow(B), q2))”) >>
 rw[App_App_o] >> first_x_assum irule >>
 strip_tac >> 
 qby_tac
 ‘!sb.(?!q2. sb = App(i2,q2)) <=> 
       ?b. sb = rsi(r2,b)’ >-- 
 (strip_tac >> dimp_tac >> disch_tac 
 >-- (pop_assum (assume_tac o uex2ex_rule) >> 
     first_x_assum (drule o iffLR) >> arw[]) >>
 uex_tac >> first_x_assum (drule o iffRL) >>
 pop_assum strip_assume_tac >> qexists_tac ‘q2’ >> arw[] >>
 rpt strip_tac >> fs[Inj_def] >> first_x_assum irule >> arw[])
 (* easy by injection*)>>
 fs[resp_def] >>
 first_x_assum (qspecl_then [‘App(i1,x)’] assume_tac) >>
 qby_tac ‘?a. App(i1,x) = rsi(r1,a)’ >-- 
 (first_x_assum (irule o iffLR) >> qexists_tac ‘x’ >> rw[]) >>
 (*should be auto*)
 pop_assum strip_assume_tac >> 
 first_x_assum (qspecl_then [‘App(Rsi(r2) o f,a)’] 
 assume_tac) >> fs[GSYM rsi_def,App_App_o] >>
 qby_tac
 ‘?!q2:mem(Q2). rsi(r2, App(f, a)) = App(i2, q2)’
 >-- (first_x_assum (irule o iffRL) >> qexists_tac ‘App(f,a)’ >> rw[]) >>
 qsuff_tac ‘!q2:mem(Q2). 
  rsi(r2, App(f, a)) = App(i2, q2) <=> 
  Holds(rext(f, r1, r2), rsi(r1, a), App(i2, q2))’
 >-- (strip_tac >> pop_assum (assume_tac o GSYM) >> arw[]) >>
 rw[rext_def] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexistsl_tac [‘a’,‘App(f,a)’] >> arw[]) >> 
 qsuff_tac ‘?b. App(i2, q2) = rsi(r2, b) & 
 Holds(r2,b,App(f, a))’ >-- 
 (strip_tac >> 
 qpick_x_assum ‘App(i2, q2) = rsi(r2, b')’
 (assume_tac o GSYM) >> arw[] >>
 drule rsi_eq_ER >> arw[] >>
 rev_drule rsi_eq_ER >> fs[] >> last_x_assum drule >>
 rfs[]) >>
 qexists_tac ‘b’ >> arw[] >> pop_assum (assume_tac o GSYM) >>
 arw[] >> first_x_assum irule >> 
 rev_drule rsi_eq_ER >> fs[ER_def,Sym_def] >> 
 first_x_assum irule >> arw[])
(form_goal
“!A B f:A->B r1:A~>A r2:B~>B
 Q1 Q2 i1:Q1->Pow(A) i2:Q2->Pow(B). 
 ER(r1) & ER(r2) & resp(f,r1,r2) & Inj(i1) & Inj(i2) &
 (!sa. (?q1. sa = App(i1,q1)) <=> (?a. sa = rsi(r1,a))) & 
 (!sb. (?q2. sb = App(i2,q2)) <=> (?b. sb = rsi(r2,b))) ==>
 ?qf: Q1-> Q2.
 !q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1)) ”));



(* Pow(A) * Pow(A) -> Pow(A * A) not have in general. *)

val ipow2_def = P2fun' |> qspecl [‘Q1 * Q2’,‘Pow(A * B)’] 
                     |> fVar_sInst_th “P(aqbq:mem(Q1 * Q2),s:mem(Pow(A * B)))”
                        “!a1 a2.IN(Pair(a1,a2),s:mem(Pow(A * B))) <=> 
                         IN(a1,App(i1:Q1-> Pow(A),Fst(aqbq))) & 
                         IN(a2,App(i2:Q2-> Pow(B),Snd(aqbq)))”
                     |> C mp 
                     (IN_def_P |> qspecl [‘A * B’] 
                               |> fVar_sInst_th “P(ab:mem(A * B))”
                               “IN(Fst(ab),App(i1:Q1->Pow(A),Fst(aqbq))) & 
                               IN(Snd(ab),App(i2:Q2->Pow(B),Snd(aqbq)))”
                               |> conv_rule (depth_fconv no_conv 
                                                         forall_cross_fconv)
                               |> rewr_rule[Pair_def']
                               |> qgen ‘aqbq’)
                     |> qSKOLEM "ipow2" [‘i1’,‘i2’]
                     |> conv_rule (depth_fconv no_conv forall_cross_fconv)
                     |> rewr_rule[Pair_def']
                     |> qspecl [‘aq:mem(Q1)’,‘bq:mem(Q2)’,
                                ‘a:mem(A)’,‘b:mem(B)’] 
                     |> gen_all |> store_as "ipow2_def";

(*
val ipow2_ex = prove_store("ipow2_ex",
e0
(rpt strip_tac >> irule l >> rpt strip_tac >>
 uex_tac)
(form_goal “!i1:Q1-> Pow(A) i2:Q2 -> Pow(B). 
 ?i: Q1 * Q2 -> Pow(A * B).
 !aq bq.
  !a1 a2.IN(Pair(a1,a2),App(i,Pair(aq,bq))) <=> 
         IN(a1,App(i1,aq)) & IN(a2,App(i2,bq))”));
end

val ipow2_def = ipow2_ex |> spec_all 
                         |> qSKOLEM "ipow2" [‘i1’,‘i2’]
                         |> gen_all
*)
 
local 
val l = P2fun' |> qspecl [‘(N * N) * N * N’,‘N * N’]
       |> fVar_sInst_th “P(xyuv:mem((N * N) * N * N),ab:mem(N * N))”
                        “ab  = Pair(Add(Fst(Fst(xyuv)),Fst(Snd(xyuv))),
                                   Add(Snd(Fst(xyuv)),Snd(Snd(xyuv))))”
       |> conv_rule (depth_fconv no_conv forall_cross_fconv) 
       |> conv_rule (basic_fconv no_conv forall_cross_fconv) 
       |> rewr_rule[Pair_def']
in    
val addf0_def = proved_th $
e0
(irule l >> rpt strip_tac >> uex_tac >>
 qexists_tac ‘Pair(Add(a', a), Add(b, b''))’ >> rw[])
(form_goal “?f:(N * N) * N * N -> N * N. 
 !x y u v. App(f,Pair(Pair(x,y),Pair(u,v))) = 
 Pair(Add(x,u),Add(y,v))”)
|> qSKOLEM "addf0" []
|> store_as "addf0_def";
end



val prrel_ER_ER = prove_store("prrel_ER_ER",
e0
(rpt strip_tac >> fs[ER_def,Sym_def,Trans_def,Refl_def] >> 
 depth_fconv_tac no_conv forall_cross_fconv >> once_rw[prrel_def] >>
 rpt strip_tac >> arw[] (* 4 *)
 >-- (last_x_assum drule >> arw[]) 
 >-- (first_x_assum drule >> arw[])
 >-- (first_x_assum irule >> qexists_tac ‘a'’ >> arw[]) >>
 first_x_assum irule >> qexists_tac ‘b'’ >> arw[])
(form_goal “∀A r1:A~>A B r2:B~>B. ER(r1) & ER(r2) ⇒ ER(prrel(r1,r2))”));


val forall_cross_tac =  depth_fconv_tac no_conv forall_cross_fconv;


val Pow_conj_eq0 = prove_store("Pow_conj_eq0",
e0
(rpt strip_tac >>
rw[GSYM IN_EXT_iff] >> strip_tac >> cases_on “IN(x,s1:mem(Pow(A)))”
>-- (arw[] >> 
    qsuff_tac ‘IN(x,s3) & IN(b0,s4)’ 
    >-- (strip_tac >> arw[]) >>
    first_x_assum (irule o iffLR) >> arw[]) >>
arw[] >> ccontra_tac >>
qby_tac ‘IN(b0,s4)’ 
>-- (qsuff_tac ‘IN(a0,s3) & IN(b0,s4)’ 
     >-- (strip_tac >> arw[]) >>
     first_x_assum (irule o iffLR) >> arw[]) >>
first_x_assum (qspecl_then [‘x’,‘b0’] assume_tac) >>
rfs[])
(form_goal “∀A B s1:mem(Pow(A)) s2:mem(Pow(B)) s3 s4 a0 b0. IN(a0,s1) & IN(b0,s2) ⇒  (∀a b. IN(a,s1) & IN(b,s2) ⇔ IN(a,s3) & IN(b,s4)) ⇒
 s1 = s3”) );

val Pow_conj_eq = prove_store("Pow_conj_eq",
e0
(rpt strip_tac 
 >-- (irule Pow_conj_eq0 (* irule weird behaviour *)>>
     rpt strip_tac >-- (qexists_tac ‘a0’ >> arw[]) >>
     qexistsl_tac [‘B’,‘b0’,‘s2’,‘s4’] >> arw[]) >>
 irule Pow_conj_eq0 >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘b0’ >> arw[]) >>
 qexistsl_tac [‘A’,‘a0’,‘s1’,‘s3’] >> arw[] >> 
 rpt strip_tac >> dimp_tac >> disch_tac (* 2 *)
 >-- (qsuff_tac ‘IN(b, s3) & IN(a, s4)’ >-- (strip_tac >> arw[]) >>
      first_x_assum (irule o iffLR) >> arw[]) >>
 qsuff_tac ‘IN(b, s1) & IN(a,s2)’ >-- (strip_tac >> arw[]) >>
 first_x_assum (irule o iffRL) >> arw[])
(form_goal “∀A B s1:mem(Pow(A)) s2:mem(Pow(B)) s3 s4 a0 b0. IN(a0,s1) & IN(b0,s2) ⇒  (∀a b. IN(a,s1) & IN(b,s2) ⇔ IN(a,s3) & IN(b,s4)) ⇒
 s1 = s3 & s2 = s4”));


(*
e0

(rpt strip_tac >> rw[GSYM IN_EXT_iff] (* 2 *) >> strip_tac >--
 (first_assum (qsspecl_then [‘x’,‘b0’] assume_tac) >> fs[] >>
 cases_on “IN(x:mem(A), s1)” >-- fs[] >>
 arw[] >> ccontra_tac >> rfs[] >> 
 cases_on “IN(a0:mem(A),s3)” (* 2 *) >-- cheat
>-- (first_assum (qsspecl_then [‘a0’,‘b0’] assume_tac) >>
     qby_tac ‘IN(a0, s3) & IN(b0,s4)’
     >-- (first_x_assum (irule o iffLR) >> strip_tac >> 
                        first_x_assum accept_tac) >>
     BUGBUGBUGBUGBUG!!!!!!!!!!!!!!!!!!!! CANNOT DO THE fs[], can finish the qby. if do the fs, complains
ERR
     ("disjE.first disjunct not in the formula list: ", [], [],
      [Pred ("IN", true, [a0, s3])]) raised


     fs[] >> first_x_assum (qspecl_then [‘x’,‘b0’] assume_tac) >> 
     pop_assum mp_tac >> arw[]rfs[]) >>
cheat)

(form_goal “∀A B s1:mem(Pow(A)) s2:mem(Pow(B)) s3 s4 a0 b0. IN(a0,s1) & IN(b0,s2) ⇒  (∀a b. IN(a,s1) & IN(b,s2) ⇔ IN(a,s3) & IN(b,s4)) ⇒
 s1 = s3 & s2 = s4”)

*)

val ipow2_Inj_Inj = prove_store("ipow2_Inj_Inj",
e0
(rpt strip_tac >> fs[Inj_def] >> 
 depth_fconv_tac no_conv forall_cross_fconv >>
 rw[GSYM IN_EXT_iff] >>
 forall_cross_tac >> rpt strip_tac >> fs[ipow2_def] >>
 rw[Pair_eq_eq] >> 
 qsuff_tac ‘App(i1,a) = App(i1,a') & App(i2,b) = App(i2,b')’ 
 >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
 irule Pow_conj_eq >> arw[])
(form_goal “∀Q1 A i1:Q1 -> Pow(A) Q2 B i2:Q2->Pow(B). 
 (∀q1. ∃a. IN(a,App(i1,q1))) &
 (∀q2. ∃b. IN(b,App(i2,q2))) & 
 Inj(i1) & Inj(i2) ⇒ Inj(ipow2(i1,i2))”));



val Quo_def = qdefine_psym ("Quo",[‘r:A~>A’,‘i:Q->Pow(A)’])
‘!s. (?!q. s = App(i:Q->Pow(A),q)) <=> (?a. s = rsi(r:A~>A,a))’
|> gen_all |> store_as "Quo_def";

val Inj_Quo = prove_store("Inj_Quo",
e0
(dimp_tac >> strip_tac >> arw[] (* 2 *)
>-- (rw[Quo_def] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
    >-- (pop_assum (assume_tac o uex2ex_rule) >>
        first_x_assum (drule o iffLR) >> arw[]) >>
    uex_tac >> 
    qby_tac ‘∃a. s = rsi(r,a)’ >-- (qexists_tac ‘a’ >> arw[]) >>
    first_x_assum (drule o iffRL) >> pop_assum strip_assume_tac >>
    qexists_tac ‘q’ >> fs[Inj_def] >> rpt strip_tac >>
    first_x_assum irule >> arw[]) >>
fs[Quo_def] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
>-- (qby_tac ‘∃!q.s = App(i,q)’
    >-- (uex_tac >> qexists_tac ‘q’ >> arw[] >> rpt strip_tac >>
        fs[Inj_def] >> first_x_assum irule >> arw[]) >>
    first_x_assum (drule o iffLR) >> arw[]) >>
qsuff_tac ‘∃!q. s = App(i,q)’ 
>-- (strip_tac >> pop_assum (assume_tac o uex2ex_rule) >> arw[]) >>
first_x_assum (irule o iffRL) >> qexists_tac ‘a’ >> arw[])
(form_goal
“(Inj(i) & !s. (?q. s = App(i:Q->Pow(A),q)) <=> (?a. s = rsi(r:A~>A,a)))
 ⇔ Inj(i) & Quo(r,i)”));

val ER_rsi_nonempty = prove_store("ER_rsi_nonempty",
e0
(rpt strip_tac >> rw[IN_rsi] >> fs[ER_def,Refl_def])
(form_goal “∀A r:A~>A a:mem(A).ER(r) ⇒ IN(a,rsi(r,a)) ”));

val Quo_cong = prove_store("Quo_cong",
e0
(rpt strip_tac >> fs[Quo_def] >> 
 depth_fconv_tac no_conv exists_cross_fconv >>
 rw[GSYM IN_EXT_iff] >>
 depth_fconv_tac no_conv forall_cross_fconv >> 
 rw[IN_rsi,prrel_def,ipow2_def] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac
     ‘∀a. ∃!q.rsi(r1,a) = App(i1,q)’
     >-- (strip_tac >>
         qby_tac ‘∃a1. rsi(r1,a) = rsi(r1,a1)’ 
         >-- (qexists_tac ‘a’ >> rw[]) >>
         first_x_assum (drule o iffRL) >> arw[]) >>
     qby_tac
     ‘∀b. ∃!q.rsi(r2,b) = App(i2,q)’
     >-- (strip_tac >>
         qby_tac ‘∃b1. rsi(r2,b) = rsi(r2,b1)’ 
         >-- (qexists_tac ‘b’ >> rw[]) >>
         first_x_assum (drule o iffRL) >> arw[])  >>
     first_x_assum (assume_tac o uex_expand) >>
     pop_assum (x_choose_then "q12" strip_assume_tac) >>
     arw[] >> 
     qsspecl_then [‘q12’] (x_choosel_then ["q1","q2"] assume_tac) 
     Pair_has_comp >> fs[] >>
     rw[ipow2_def] >> rw[GSYM IN_rsi] >>
     qsuff_tac ‘∃a1 b1. App(i1, q1) = rsi(r1, a1) & App(i2,q2) = rsi(r2, b1)’ 
     >-- (strip_tac >> qexistsl_tac [‘a1’,‘b1’] >> arw[]) >>
     qby_tac ‘∃!q. App(i1,q1) = App(i1,q)’ 
     >-- (uex_tac >> qexists_tac ‘q1’ >> rw[] >> fs[Inj_def] >>
         rpt strip_tac >> first_x_assum irule >> arw[]) >>
     first_x_assum (drule o iffLR) >> pop_assum strip_assume_tac >>
     qby_tac ‘∃!q. App(i2,q2) = App(i2,q)’ 
     >-- (uex_tac >> qexists_tac ‘q2’ >> rw[] >> fs[Inj_def] >>
         rpt strip_tac >> first_x_assum irule >> arw[]) >>
     first_x_assum (drule o iffLR) >> pop_assum strip_assume_tac >>
     qexistsl_tac [‘a’,‘a'’] >> arw[]) >>
qsuff_tac ‘∃!q:mem(Q1 * Q2).
 (∀a1 b1. Holds(r1, a', a1) & Holds(r2, b, b1) ⇔ 
  IN(Pair(a1, b1), App(ipow2(i1, i2), q)))’
>-- (strip_tac >> pop_assum (strip_assume_tac o  uex_expand) >>
    uex_tac >> qexists_tac ‘q’ >> rpt strip_tac >> arw[] >>
    first_x_assum irule >> fs[]) 
(*this qsuff not automatic, MAY HAVE BUG IN FORALL_FCONV!!!!!!*) >>
qby_tac ‘∃a. rsi(r1,a') = rsi(r1,a)’ 
>-- (qexists_tac ‘a'’ >> rw[]) >>
first_x_assum (drule o iffRL) >> 
pop_assum (assume_tac o uex_expand) >>
pop_assum (x_choose_then "q1" strip_assume_tac) >>
qby_tac ‘∃b1. rsi(r2,b) = rsi(r2,b1)’ 
>-- (qexists_tac ‘b’ >> rw[]) >>
first_x_assum (drule o iffRL) >> 
pop_assum (assume_tac o uex_expand) >>
pop_assum (x_choose_then "q2" strip_assume_tac) >>
uex_tac >> qexists_tac ‘Pair(q1,q2)’ >> 
depth_fconv_tac no_conv forall_cross_fconv >>
rw[ipow2_def,GSYM IN_rsi,Pair_eq_eq] >>
qsuff_tac ‘rsi(r1, a') = App(i1, q1) & rsi(r2, b) = App(i2, q2)’
>-- (strip_tac >> arw[] >> rpt gen_tac >> disch_tac >>
    qsuff_tac ‘App(i1, q1) = App(i1, a) & 
               App(i2, q2) = App(i2, b')’ 
    >-- (rpt strip_tac >> fs[Inj_def] >> first_x_assum irule >> arw[]) >>
    irule Pow_conj_eq >>
    arw[] >> strip_tac (* 2 *)
    >-- (qexists_tac ‘b’ >> 
        qpick_x_assum ‘rsi(r2, b) = App(i2, q2)’ (assume_tac o GSYM) >>
        arw[] >> irule ER_rsi_nonempty >> arw[]) >>
    qexists_tac ‘a'’ >> 
    qpick_x_assum ‘rsi(r1, a') = App(i1, q1)’ (assume_tac o GSYM) >>
    arw[] >> irule ER_rsi_nonempty >> arw[]) >>
arw[])
(form_goal “∀A r1:A~>A Q1 i1:Q1-> Pow(A) B r2:B~>B Q2 i2:Q2 -> Pow(B). 
 ER(r1) & ER(r2) & Inj(i1) & Inj(i2) &
 Quo(r1,i1) & Quo(r2,i2) ⇒
 Quo(prrel(r1,r2),ipow2(i1,i2))”));


val Quo_fun = prove_store("Quo_fun",
e0
(rpt strip_tac >> 
 irule main >> arw[] >> strip_tac (* 2 *)
 >-- (qby_tac ‘Inj(i1) & Quo(r1,i1)’ 
     >-- arw[] >>
     drule (iffRL Inj_Quo) >> arw[]) >>
 qby_tac ‘Inj(i2) & Quo(r2,i2)’ 
 >-- arw[] >>
 drule (iffRL Inj_Quo) >> arw[])
(form_goal
“!A B f:A->B r1:A~>A r2:B~>B
 Q1 Q2 i1:Q1->Pow(A) i2:Q2->Pow(B). 
 ER(r1) & ER(r2) & resp(f,r1,r2) & Inj(i1) & Inj(i2) &
 Quo(r1,i1) & Quo(r2,i2) ==>
 ?qf: Q1-> Q2.
 !q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1)) ”))




(*

val Quo_fun_uex = prove_store("Quo_fun",
e0
(easy to prove unique since the "main" uses P2fun', can use unique P2fun_uex)
(form_goal
“!A B f:A->B r1:A~>A r2:B~>B
 Q1 Q2 i1:Q1->Pow(A) i2:Q2->Pow(B). 
 ER(r1) & ER(r2) & resp(f,r1,r2) & Inj(i1) & Inj(i2) &
 Quo(r1,i1) & Quo(r2,i2) ==>
 ?!qf: Q1-> Q2.
 !q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1)) ”))
*)


val Inj_Quo_Z = prove_store("Inj_Quo_Z",
e0
(rw[GSYM Inj_Quo,iZ_Inj] >>
 rw[GSYM Z_def])
(form_goal “Inj(iZ) & Quo(ZR, iZ)”));


val addf0_resp = prove_store("addf0_resp",
e0
(rw[resp_def,prrel_def] >> rpt strip_tac >>
 qsspecl_then [‘z’] (x_choosel_then ["ab","cd"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘ab’] (x_choosel_then ["a","b"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘cd’] (x_choosel_then ["c","d"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘y’] (x_choosel_then ["xy","uv"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘xy’] (x_choosel_then ["x1","y1"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘uv’] (x_choosel_then ["u","v"] assume_tac) Pair_has_comp >>
 fs[addf0_def,prrel_def,ZR_def] >> 
 qspecl_then [‘u’,‘x1’] assume_tac Add_comm >> arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘x1’,‘b’,‘d’] assume_tac Add_assoc >> arw[] >>
 qspecl_then [‘a’,‘y1’,‘d’] assume_tac (GSYM Add_assoc) >> arw[] >>
 qspecl_then [‘Add(y1,d)’,‘a’] assume_tac Add_comm >> arw[] >>
 qspecl_then [‘d’,‘y1’] assume_tac Add_comm >> arw[] >>
 arw[Add_assoc] >> cheat (*tedious*))
(form_goal “resp(addf0, prrel(ZR, ZR), ZR)”));

val addz_conds = proved_th $
e0
(assume_tac Inj_Quo_Z >> assume_tac ZR_ER >> arw[] >> rpt strip_tac (* 4 *)
 >-- (irule prrel_ER_ER >> arw[])
 >-- rw[addf0_resp] (*hard one*)
 >-- irule ipow2_Inj_Inj >> arw[] >> cheat (* *) >>
 irule Quo_cong >> arw[])
(form_goal
“ER(prrel(ZR, ZR)) &
      ER(ZR) &
      resp(addf0, prrel(ZR, ZR), ZR) &
      Inj(ipow2(iZ, iZ)) &
      Inj(iZ) & Quo(prrel(ZR, ZR), ipow2(iZ, iZ)) & Quo(ZR, iZ)”)




(*
 (redepth_fconv no_conv exists_cross_fconv)
 “∃a:mem(A) b:mem(B) b':mem(A * B) b'':mem(A  * B). P(a,b,b',b'')”

ispositive: 

(N * N) -> Bool

Z -> bool

<= 
define relations
*)


val main_addz = 
Quo_fun |> qspecl [‘(N * N) * (N * N)’,‘N * N’,
                ‘addf0’,
                ‘prrel(ZR,ZR)’,‘ZR’,
                ‘Z * Z’,‘Z’,
                ‘ipow2(iZ,iZ)’,‘iZ’]
        |> conv_rule (depth_fconv no_conv forall_cross_fconv)
        |> C mp addz_conds
        |> qSKOLEM "addz" []
        |> qspecl [‘z1:mem(Z)’,‘z2:mem(Z)’]
        |> rewr_rule[rext_def,App_App_o,GSYM IN_EXT_iff,IN_rsi] 




(*CANNOT GET ALL forall_cross_fconv expanded...
  BUT ANYWAY GET UGLY VAR NAMES...
  NEED TO RENAME BY HAND anyway,
  therefore doing it by hand as follows...
*)


(*TODO: let genvar not add "'" but add numbers *)
val main_addz1 = proved_th $
e0
(strip_assume_tac main_addz >>
 qsspecl_then [‘b’] (x_choosel_then ["b1","b2"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a’] (x_choosel_then ["a12","a34"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a12’] (x_choosel_then ["a1","a2"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a34’] (x_choosel_then ["a3","a4"] assume_tac) Pair_has_comp >>
 once_arw[] >> qexistsl_tac [‘a1’,‘a2’,‘a3’,‘a4’,‘b1’,‘b2’] >>
 arw[] >>
 qsuff_tac ‘Pair(Pair(a1, a2), Pair(a3, a4))  = a & Pair(b1,b2) = b’ 
 >-- (qpick_x_assum ‘App(addf0, a) = b’ mp_tac >>
      pop_assum_list (K all_tac) >> rpt strip_tac >> arw[]) >> 
 arw[])
(form_goal
 “?a1 a2 a3 a4 b1 b2.
     (!x1 x2 x3 x4.
            IN(Pair(Pair(x1,x2),Pair(x3,x4)), 
               App(ipow2(iZ, iZ), Pair(z1, z2))) <=>
            Holds(prrel(ZR, ZR), Pair(Pair(a1,a2),Pair(a3,a4)), Pair(Pair(x1,x2),Pair(x3,x4)))) &
        (!n1 n2.
            IN(Pair(n1,n2), App(iZ, App(addz, Pair(z1, z2)))) <=> 
            Holds(ZR, Pair(b1,b2), Pair(n1,n2))) &
        App(addf0, Pair(Pair(a1,a2),Pair(a3,a4))) = Pair(b1,b2)”)
|> rewr_rule[ipow2_def,prrel_def,GSYM IN_rsi]


(*may need con rw for simplifying main_addz'*)
val iZ_nonempty = prove_store("iZ_nonempty",
e0
(strip_tac >> strip_assume_tac Z_def >> 
 qsuff_tac ‘∃n. App(iZ,z) = rsi(ZR,n)’ 
 >-- (strip_tac >> arw[] >> qexists_tac ‘n’ >> irule ER_rsi_nonempty >>
     rw[ZR_ER]) >>
 first_x_assum (irule o iffRL) >> qexists_tac ‘z’ >> rw[])
(form_goal “∀z. ∃ab. IN(ab,App(iZ,z))”));

val main_addz2 = proved_th $
e0
(strip_assume_tac main_addz1 >>
 qexistsl_tac [‘a1’,‘a2’,‘a3’,‘a4’,‘b1’,‘b2’] >>
 qby_tac ‘App(iZ,z1) = rsi(ZR,Pair(a1,a2)) & App(iZ,z2) = rsi(ZR,Pair(a3,a4))’ 
 >-- (irule Pow_conj_eq >> rw[iZ_nonempty] >> 
     depth_fconv_tac no_conv forall_cross_fconv >> arw[]) >>
 arw[] >> rw[GSYM IN_EXT_iff] >> fconv_tac forall_cross_fconv >> arw[])
(form_goal
 “∃a1 a2 a3 a4 b1 b2.
  App(iZ,z1) = rsi(ZR,Pair(a1,a2)) & App(iZ,z2) = rsi(ZR,Pair(a3,a4)) &
  App(iZ,App(addz,Pair(z1,z2))) = rsi(ZR,Pair(b1,b2)) &
  App(addf0, Pair(Pair(a1, a2), Pair(a3, a4))) = Pair(b1, b2)”)


val main_addz3 = main_addz2 |> rewr_rule[addf0_def] 
                            |> store_as "main_addz3";



val Inj_Quo_rep = prove_store("Inj_Quo_rep",
e0
(fs[Quo_def] >> rpt strip_tac >>
 first_x_assum (irule o iffLR) >> uex_tac >>
 qexists_tac ‘q’ >> rw[] >> fs[Inj_def] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal “∀A r:A~>A Q i:Q->Pow(A). Inj(i) & Quo(r,i) ⇒
 ∀q.∃a. App(i,q) = rsi(r,a)”));

val Z_has_rep = prove_store("Z_has_rep",
e0
(assume_tac Inj_Quo_Z >> drule Inj_Quo_rep >>
 pop_assum (assume_tac o (conv_rule (depth_fconv no_conv exists_cross_fconv)))>>
 arw[] )
(form_goal “∀z. ∃n1 n2. App(iZ,z) = rsi(ZR,Pair(n1,n2))”));


val Addz_def = qdefine_fsym ("Addz",[‘z1:mem(Z)’,‘z2:mem(Z)’])
                            ‘App(addz,Pair(z1,z2))’
                            |> gen_all |> store_as "Addz_def";

val Repz_def = qdefine_fsym ("Repz",[‘z:mem(Z)’])
                            ‘App(iZ,z)’
                            |> gen_all |> store_as "Repz_def";



val Repz_rsi = Z_has_rep |> rewr_rule[GSYM Repz_def] 
                         |> store_as "Repz_rsi";

(*ZR class*)
val ZC_def = qdefine_fsym ("ZC",[‘ab:mem(N * N)’])
                            ‘rsi(ZR,ab)’
                            |> gen_all |> store_as "ZC_def";

val Repz_ZC = Z_has_rep |> rewr_rule[GSYM Repz_def,GSYM ZC_def] 
                         |> store_as "Repz_ZC";


val Addz_char0 = main_addz3 |> rewr_rule[GSYM Addz_def,GSYM Repz_def,
                                         GSYM ZC_def]
                            |> gen_all
                            |> store_as "Addz_char0";

val ZC_ZR = prove_store("ZC_ZR",
e0
(rw[ZC_def] >> irule rsi_eq_ER >> rw[ZR_ER])
(form_goal “∀ab cd. ZC(ab) = ZC(cd) ⇔ Holds(ZR,ab,cd)”));

val Addz_char = prove_store("Addz_char",
e0
(rpt strip_tac >>
 qsspecl_then [‘z1’,‘z2’] strip_assume_tac Addz_char0 >>
 arw[ZC_ZR] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 assume_tac addf0_resp >> fs[resp_def,prrel_def] >>
 first_x_assum (qsspecl_then [‘Pair(Pair(a1',a2'),Pair(a3',a4'))’,
               ‘Pair(Pair(a1,a2),Pair(a3,a4))’] assume_tac)  >>
 fs[addf0_def] >> first_x_assum irule >>
 arw[prrel_def,GSYM ZC_ZR])
(form_goal
 “∀z1 a1 a2.
  Repz(z1) = ZC(Pair(a1,a2)) ⇒
  ∀z2 a3 a4. 
  Repz(z2) = ZC(Pair(a3,a4)) ⇒
  Repz(Addz(z1,z2)) = ZC(Pair(Add(a1, a3), Add(a2, a4)))”));

val Repz_eq_eq = iZ_eq_eq |> rewr_rule[GSYM Repz_def] |> store_as "Repz_eq_eq";


val Repz_eq_ZR = rsi_eq_ER |> qsspecl [‘ZR’] |> C mp ZR_ER 
                           |> rewr_rule[GSYM ZC_def]
                           |> store_as "Repz_eq_ZR";


val eq_ZR = prove_store("eq_ZR",
e0
(rpt strip_tac >> assume_tac ZR_Refl >> fs[Refl_def])
(form_goal
 “!a b. a = b ==> Holds(ZR,a,b)”));

val Addz_comm = prove_store("Addz_comm",
e0
((*qby_tac
 ‘∀a b c d. 
  Holds(ZR,App(addf0,Pair(Pair(a,b),Pair(c,d))),
           App(addf0,Pair(Pair(c,d),Pair(a,b))))’
 >-- cheat >> do not need it, but an option *)
 rpt strip_tac >> irule Repz_eq_eq >> rpt strip_tac >>
 qsspecl_then [‘z1’] (x_choosel_then ["a","b"] assume_tac) Repz_ZC >>
 qsspecl_then [‘z2’] (x_choosel_then ["c","d"] assume_tac) Repz_ZC >>
 qby_tac ‘Repz(Addz(z1, z2)) = ZC(Pair(Add(a, c), Add(b, d)))’
 >-- (irule Addz_char >> arw[]) >>
 qby_tac ‘Repz(Addz(z2, z1)) = ZC(Pair(Add(c, a), Add(d, b)))’
 >-- (irule Addz_char >> arw[]) >>
 arw[] >> rw[ZC_ZR] >> 
 qsuff_tac ‘Add(a,c) = Add(c,a) & Add(b,d) = Add(d,b)’ 
 >-- (strip_tac >> arw[] >> irule eq_ZR >> arw[]) >> 
 qspecl_then [‘a’,‘c’] assume_tac Add_comm' >>
 qspecl_then [‘b’,‘d’] assume_tac Add_comm' >> arw[])
(form_goal “!z1 z2. Addz(z1,z2) = Addz(z2,z1)”));



val negf0_def = fun_tm_compr (dest_var $ rastt "mn:mem(N * N)")
                         (rastt "Pair(Snd(mn:mem(N * N)),Fst(mn))") |> qSKOLEM "negf0" []
      |> store_as "negf0_def";


val negf0_def1 = 
    negf0_def |> qspecl [‘Pair(m:mem(N),n:mem(N))’]
              |> rewr_rule[Pair_def']
              |> gen_all |> store_as "negf0_def1";



val negf0_resp = prove_store("negf0_resp",
e0
(cheat)
(form_goal “resp(negf0, ZR, ZR)”));

val main_negz = 
Quo_fun |> qspecl [‘N * N’,‘N * N’,
                ‘negf0’,
                ‘ZR’,‘ZR’,
                ‘Z’,‘Z’,
                ‘iZ’,‘iZ’]
        |> rewr_rule[Inj_Quo_Z,ZR_ER,negf0_resp]
        |> qSKOLEM "negz" []
        |> qspecl [‘z:mem(Z)’]
        |> rewr_rule[rext_def,App_App_o,GSYM Repz_def,GSYM ZC_def] 


val Negz_def = qdefine_fsym ("Negz",[‘z:mem(Z)’])
                            ‘App(negz,z)’
                            |> gen_all |> store_as "Negz_def";

val main_negz1 = proved_th $ 
e0
(strip_assume_tac main_negz >>
 qsspecl_then [‘a’] (x_choosel_then ["a1","a2"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘b’] (x_choosel_then ["b1","b2"] assume_tac) Pair_has_comp >>
 fs[] >>
 qexistsl_tac [‘a1’,‘a2’] >> arw[] >>
 fs[negf0_def1])
(form_goal “?a1 a2.
 Repz(z) = ZC(Pair(a1,a2)) & Repz(App(negz, z)) = ZC(Pair(a2,a1))”)
|> rewr_rule[GSYM Negz_def]

val Negz_char = prove_store("Neg_char",
e0
(rpt strip_tac >>
 strip_assume_tac main_negz1 >> arw[ZC_ZR] >>
 assume_tac negf0_resp >>
 fs[resp_def] >>
 first_x_assum (qsspecl_then [‘Pair(a,b)’,‘Pair(a1,a2)’] assume_tac) >>
 fs[negf0_def,Pair_def'] >>
 assume_tac ZR_ER >> fs[ER_def,Sym_def] >> first_x_assum irule >>
 first_x_assum irule >>
 qpick_x_assum ‘ZC(Pair(a1, a2)) = ZC(Pair(a, b))’ (assume_tac o GSYM) >>
 fs[ZC_ZR])
(form_goal “!z a b. Repz(z) = ZC(Pair(a,b)) ==>
 Repz(Negz(z)) = ZC(Pair(b,a))”));


local 
val l = P2fun' |> qspecl [‘(N * N) * N * N’,‘N * N’]
       |> fVar_sInst_th “P(abcd:mem((N * N) * N * N),mn:mem(N * N))”
                        “mn  = Pair(Add(Mul(Fst(Fst(abcd)),Fst(Snd(abcd))),
      Mul(Snd(Fst(abcd)),Snd(Snd(abcd)))),Add(Mul(Fst(Fst(abcd)),Snd(Snd(abcd))),
      Mul(Snd(Fst(abcd)),Fst(Snd(abcd)))))”
       |> conv_rule (depth_fconv no_conv forall_cross_fconv) 
       |> conv_rule (basic_fconv no_conv forall_cross_fconv) 
       |> rewr_rule[Pair_def']
in    
val mulf0_def = proved_th $
e0
(irule l >> rpt strip_tac >> uex_tac >>
 qexists_tac ‘Pair(Add(Mul(a', a), Mul(b, b'')), Add(Mul(a', b''), Mul(b, a)))’ >> rw[])
(form_goal “?f:(N * N) * N * N -> N * N. 
 !a b c d. App(f,Pair(Pair(a,b),Pair(c,d))) = 
 Pair(Add(Mul(a,c),Mul(b,d)),Add(Mul(a,d),Mul(b,c)))”)
|> qSKOLEM "mulf0" []
|> store_as "mulf0_def";
end


val mulf0_resp = prove_store("mulf0_resp",
e0
(cheat)
(form_goal “resp(mulf0, prrel(ZR, ZR), ZR)”));

val main_mulz = 
Quo_fun |> qspecl [‘(N * N) * (N * N)’,‘N * N’,
                ‘mulf0’,
                ‘prrel(ZR,ZR)’,‘ZR’,
                ‘Z * Z’,‘Z’,
                ‘ipow2(iZ,iZ)’,‘iZ’]
        |> rewr_rule[addz_conds,mulf0_resp]
        |> conv_rule (depth_fconv no_conv forall_cross_fconv)
        |> qSKOLEM "mulz" []
        |> qspecl [‘z1:mem(Z)’,‘z2:mem(Z)’]
        |> rewr_rule[rext_def,App_App_o,GSYM IN_EXT_iff,IN_rsi] 



(* main_addz1, main_mulz1 exactly same *)
val main_mulz1 = proved_th $
e0
(strip_assume_tac main_mulz >>
 qsspecl_then [‘b’] (x_choosel_then ["b1","b2"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a’] (x_choosel_then ["a12","a34"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a12’] (x_choosel_then ["a1","a2"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a34’] (x_choosel_then ["a3","a4"] assume_tac) Pair_has_comp >>
 once_arw[] >> qexistsl_tac [‘a1’,‘a2’,‘a3’,‘a4’,‘b1’,‘b2’] >>
 arw[] >>
 qsuff_tac ‘Pair(Pair(a1, a2), Pair(a3, a4))  = a & Pair(b1,b2) = b’ 
 >-- (qpick_x_assum ‘App(mulf0, a) = b’ mp_tac >>
      pop_assum_list (K all_tac) >> rpt strip_tac >> arw[]) >> 
 arw[])
(form_goal
 “?a1 a2 a3 a4 b1 b2.
     (!x1 x2 x3 x4.
            IN(Pair(Pair(x1,x2),Pair(x3,x4)), 
               App(ipow2(iZ, iZ), Pair(z1, z2))) <=>
            Holds(prrel(ZR, ZR), Pair(Pair(a1,a2),Pair(a3,a4)), Pair(Pair(x1,x2),Pair(x3,x4)))) &
        (!n1 n2.
            IN(Pair(n1,n2), App(iZ, App(mulz, Pair(z1, z2)))) <=> 
            Holds(ZR, Pair(b1,b2), Pair(n1,n2))) &
        App(mulf0, Pair(Pair(a1,a2),Pair(a3,a4))) = Pair(b1,b2)”)
|> rewr_rule[ipow2_def,prrel_def,GSYM IN_rsi]



val main_mulz2 = proved_th $
e0
(strip_assume_tac main_mulz1 >>
 qexistsl_tac [‘a1’,‘a2’,‘a3’,‘a4’,‘b1’,‘b2’] >>
 qby_tac ‘App(iZ,z1) = rsi(ZR,Pair(a1,a2)) & App(iZ,z2) = rsi(ZR,Pair(a3,a4))’ 
 >-- (irule Pow_conj_eq >> rw[iZ_nonempty] >> 
     depth_fconv_tac no_conv forall_cross_fconv >> arw[]) >>
 arw[] >> rw[GSYM IN_EXT_iff] >> fconv_tac forall_cross_fconv >> arw[])
(form_goal
 “∃a1 a2 a3 a4 b1 b2.
  App(iZ,z1) = rsi(ZR,Pair(a1,a2)) & App(iZ,z2) = rsi(ZR,Pair(a3,a4)) &
  App(iZ,App(mulz,Pair(z1,z2))) = rsi(ZR,Pair(b1,b2)) &
  App(mulf0, Pair(Pair(a1, a2), Pair(a3, a4))) = Pair(b1, b2)”)
 



val main_mulz3 = main_mulz2 |> rewr_rule[mulf0_def] 
                            |> store_as "main_mulz3";



val Mulz_def = qdefine_fsym ("Mulz",[‘z1:mem(Z)’,‘z2:mem(Z)’])
                            ‘App(mulz,Pair(z1,z2))’
                            |> gen_all |> store_as "Mulz_def";



val Mulz_char0 = main_mulz3 |> rewr_rule[GSYM Mulz_def,GSYM Repz_def,
                                         GSYM ZC_def]
                            |> gen_all
                            |> store_as "Mulz_char0";



val Mulz_char = prove_store("Mulz_char",
e0
(rpt strip_tac >>
 qsspecl_then [‘z1’,‘z2’] strip_assume_tac Mulz_char0 >>
 arw[ZC_ZR] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 assume_tac mulf0_resp >> fs[resp_def,prrel_def] >>
 first_x_assum (qsspecl_then [‘Pair(Pair(a1',a2'),Pair(a3',a4'))’,
               ‘Pair(Pair(a1,a2),Pair(a3,a4))’] assume_tac)  >>
 fs[mulf0_def] >> first_x_assum irule >>
 arw[prrel_def,GSYM ZC_ZR])
(form_goal
 “∀z1 a1 a2.
  Repz(z1) = ZC(Pair(a1,a2)) ⇒
  ∀z2 a3 a4. 
  Repz(z2) = ZC(Pair(a3,a4)) ⇒
  Repz(Mulz(z1,z2)) = 
  ZC(Pair(Add(Mul(a1, a3), Mul(a2, a4)),
          Add(Mul(a1, a4), Mul(a2, a3))))”));

(*can obtain an abs function, not from set of eq classes:
rep :Z -> Pow(N * N) if to N * N, then use choice
abs: N * N ->Z, if from Pow(N * N), then ill-behaved on non-eqcs.*)
val ZC_Repz = prove_store("ZC_Repz",
e0
(rpt strip_tac >> strip_assume_tac Z_def >>
 fs[GSYM Repz_def,GSYM ZC_def] >> 
 qby_tac ‘?n.  ZC(Pair(a, b)) = ZC(n)’ 
 >-- (qexists_tac ‘Pair(a,b)’ >> rw[]) >>
 first_x_assum (drule o iffLR) >>
 pop_assum strip_assume_tac >> uex_tac >>
 qexists_tac ‘b'’ >> arw[] >> rpt strip_tac >> irule Repz_eq_eq >>
 arw[])
(form_goal
 “!a b.?!z. Repz(z) = ZC(Pair(a,b))”));


val ZC_Repz' = prove_store("ZC_Repz'",
e0
(strip_tac >>
 qsspecl_then [‘ab’] strip_assume_tac Pair_has_comp >>
 arw[ZC_Repz])
(form_goal
 “!ab.?!z. Repz(z) = ZC(ab)”));

val absz_def = P2fun |> qspecl [‘N * N’,‘Z’] 
                   |> fVar_sInst_th “P(ab:mem(N * N),y:mem(Z))”
                      “Repz(y) = ZC(ab)”
                   |> conv_rule (top_depth_fconv no_conv forall_cross_fconv)
                   |> C mp ZC_Repz
                   |> qSKOLEM "absz" []
                   |> store_as "absz_def";

val Absz_def = qdefine_fsym ("Absz",[‘ab:mem(N * N)’])
                            ‘App(absz,ab)’
                            |> gen_all |> store_as "Absz_def";


val Asz_def = qdefine_fsym ("Asz",[‘a:mem(N)’,‘b:mem(N)’])
                            ‘Absz(Pair(a,b))’
                            |> gen_all |> store_as "Asz_def";


val Zc_def = qdefine_fsym ("Zc",[‘a:mem(N)’,‘b:mem(N)’])
                            ‘ZC(Pair(a,b))’
                            |> gen_all |> store_as "Zc_def";


val Absz_Repz = absz_def |> qspecl [‘a:mem(N)’,‘b:mem(N)’,‘Absz(Pair(a,b))’]
                         |> rewr_rule[GSYM Absz_def]
                         |> gen_all |> store_as "Absz_Repz";


val Asz_Repz = Absz_Repz |> rewr_rule[GSYM Asz_def,GSYM Zc_def] |> store_as "Asz_Repz";

val Oz_def = qdefine_fsym ("Oz",[])
                            ‘Asz(O,O)’
                            |> gen_all |> store_as "Oz_def";


val En_def = qdefine_fsym ("En",[])
                            ‘Suc(O)’
                            |> gen_all |> store_as "En_def";

val Ez_def = qdefine_fsym ("Ez",[]) ‘Asz(En,O)’
                            |> gen_all |> store_as "Ez_def";

val Addz_th0 = Addz_char |> rewr_rule[GSYM Zc_def]
                         |> store_as "Addz_th0";

val Addz_Asz = prove_store("Addz_Asz",
e0
(rpt strip_tac >>
 qby_tac ‘Repz(Asz(a,b)) = Zc(a,b)’ >-- rw[Asz_Repz] >>
 drule Addz_th0 >>
 qby_tac ‘Repz(Asz(c,d)) = Zc(c,d)’ >-- rw[Asz_Repz] >>
 first_x_assum drule >> irule Repz_eq_eq >> 
 arw[Asz_Repz])
(form_goal “!a b c d.Addz(Asz(a,b), Asz(c,d)) = Asz(Add(a,c),Add(b,d))”));

val Mulz_th0 = Mulz_char |> rewr_rule[GSYM Zc_def]
                         |> store_as "Mulz_th0";

(*[a, b][c, d] = [ac + bd, ad + bc]*)
val Mulz_Asz = prove_store("Mulz_Absz",
e0
(rpt strip_tac >> 
 qby_tac ‘Repz(Asz(a,b)) = Zc(a,b)’ >-- rw[Asz_Repz] >>
 drule Mulz_th0 >>
 qby_tac ‘Repz(Asz(c,d)) = Zc(c,d)’ >-- rw[Asz_Repz] >>
 first_x_assum drule >> irule Repz_eq_eq >> 
 arw[Asz_Repz])
(form_goal “!a b c d.Mulz(Asz(a,b), Asz(c,d)) =
 Asz(Add(Mul(a,c),Mul(b,d)),Add(Mul(a,d),Mul(b,c)))”));

val Negz_th0 = Negz_char |> rewr_rule[GSYM Zc_def]
                         |> store_as "Negz_th0";


val Negz_Asz = prove_store("Negz_Absz",
e0
(rpt strip_tac >> 
 qby_tac ‘Repz(Asz(a,b)) = Zc(a,b)’ >-- rw[Asz_Repz] >>
 drule Negz_th0 >> irule Repz_eq_eq >> arw[Asz_Repz])
(form_goal “!a b.Negz(Asz(a,b)) = Asz(b,a)”));


(*tactic of cases on z, like in Isabelle
([a,b]+[c,d])+[e,f]=[a,b]+([c,d]+[e,f])*)

val cases_z = prove_store("cases_z",
e0
(strip_tac >> 
 qspecl_then [‘z’] assume_tac Z_has_rep >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘n1’,‘n2’] >> fs[GSYM ZC_def,GSYM Zc_def,GSYM Repz_def] >>
 irule Repz_eq_eq>> arw[Asz_Repz])
(form_goal “!z.?a b. z = Asz(a,b)”));

val Addz_assoc = prove_store("Addz_assoc",
e0
(qsuff_tac
 ‘!a b c d e f. 
  Addz(Addz(Asz(a,b),Asz(c,d)),Asz(e,f)) = 
  Addz(Asz(a,b),Addz(Asz(c,d),Asz(e,f)))’
 >-- (rpt strip_tac >>
      qspecl_then [‘z1’] strip_assume_tac cases_z >>
      qspecl_then [‘z2’] strip_assume_tac cases_z >>
      qspecl_then [‘z3’] strip_assume_tac cases_z >> 
      arw[]) >>
 rw[Addz_Asz] >> rpt strip_tac >> rw[Add_assoc])
(form_goal “!z1 z2 z3. Addz(Addz(z1,z2),z3) = Addz(z1,Addz(z2,z3))”));

(*[a,b]+0Z=[a,b]*)
val casesz = prove_store("casesz",
e0
(dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qspecl_then [‘z’] strip_assume_tac cases_z >>
     arw[]) >>
 arw[])
(form_goal “(!a b. P(Asz(a,b))) <=> (!z:mem(Z). P(z))”));
(*not such easy to apply since there maybe many vars, need a conv for this*)

fun casez_tac (ct,asl,w) : goal list * validation = 
    let val (zv as (zn,zs),b) = dest_forall w
        val th = casesz |> fVar_sInst_th 
                         (mk_fvar "P" [mk_var zv]) b
        val new = th |> concl |> dest_dimp |> #1
    in ([(ct,asl,new)],fn [th0] => dimp_mp_l2r th0 th)
    end
  
val Addz_Oz = prove_store("Addz_Oz",
e0
(casez_tac >> rw[Oz_def,Addz_Asz,Add_O])
(form_goal “!z. Addz(z,Oz) = z”));

val Asz_eq_ZR = prove_store("Asz_eq_ZR",
e0
(rw[GSYM Repz_eq_ZR] >> rw[GSYM Zc_def] >> rpt strip_tac >> dimp_tac >>
 strip_tac
 >-- arw[GSYM Asz_Repz]  >>
 irule Repz_eq_eq >> arw[Asz_Repz])
(form_goal “!a b c d. Asz(a,b) = Asz(c,d) <=> Holds(ZR,Pair(a,b),Pair(c,d))”));

(*[a,b]+(−[a,b])=0Z*)

val Addz_Negz_Oz = prove_store("Addz_Negz_Oz",
e0
(casez_tac >> rw[Negz_Asz,Addz_Asz,Oz_def] >> rpt strip_tac >>
 rw[Asz_eq_ZR] >> rw[ZR_def,Add_O,Add_O2] >>
 qspecl_then [‘a’,‘b’] assume_tac Add_comm >> arw[])
(form_goal “!z. Addz(z,Negz(z)) = Oz”));


(*([a, b][c, d])[e, f ] = [a, b]([c, d][e, f ])*)

val Mulz_assoc = prove_store("Mulz_assoc",
e0
(qsuff_tac
 ‘!a b c d e f.Mulz(Mulz(Asz(a,b),Asz(c,d)),Asz(e,f)) = 
  Mulz(Asz(a,b),Mulz(Asz(c,d),Asz(e,f)))’ 
 >-- cheat >>
 rpt strip_tac >> 
 rw[Mulz_Asz,Asz_eq_ZR,LEFT_DISTR,RIGHT_DISTR,Mul_assoc,GSYM Add_assoc] >>
 irule eq_ZR >> rw[Pair_eq_eq] >> strip_tac (* 2 *)
 >-- cheat >> 
 cheat (*tedious*) )
(form_goal “!z1 z2 z3. Mulz(Mulz(z1,z2),z3) = Mulz(z1,Mulz(z2,z3))”));

(*[a,b]([c,d]+[e,f])=[a,b][c,d]+[a,b][e,f]*)
val LDISTR_Z = prove_store("LDISTR_Z",
e0
(qsuff_tac
 ‘!a b c d e f. Mulz(Asz(a,b),Addz(Asz(c,d),Asz(e,f))) = 
  Addz(Mulz(Asz(a,b),Asz(c,d)),Mulz(Asz(a,b),Asz(e,f)))’ 
 >-- cheat >>
 rpt strip_tac >> rw[Mulz_Asz,Addz_Asz,LEFT_DISTR] >>
 qsuff_tac 
‘Add(Add(Mul(a, c), Mul(a, e)), Add(Mul(b, d), Mul(b, f))) =
 Add(Add(Mul(a, c), Mul(b, d)), Add(Mul(a, e), Mul(b, f))) & 
 Add(Add(Mul(a, d), Mul(a, f)), Add(Mul(b, c), Mul(b, e))) = 
 Add(Add(Mul(a, d), Mul(b, c)), Add(Mul(a, f), Mul(b, e)))’
 >-- (strip_tac >> arw[]) >>
 cheat (*tedious*))
(form_goal
 “!z1 z2 z3. Mulz(z1,Addz(z2,z3)) = Addz(Mulz(z1,z2),Mulz(z1,z3))”));

(*[a, b].1Z = [a, b]*)

val Mulz_Ez = prove_store("Mulz_Ez",
e0
(casez_tac >> 
 rw[Ez_def,En_def,Mulz_Asz,Mul_RIGHT_1,Mul_LEFT_O,Mul_clauses,
    Add_O,Add_O2])
(form_goal “!z. Mulz(z,Ez) = z”));


(*[a, b][c, d] = [c, d][a, b]*)

val Mulz_comm = prove_store("Mulz_comm",
e0
(qsuff_tac ‘!a b c d. Mulz(Asz(a,b),Asz(c,d)) = Mulz(Asz(c,d),Asz(a,b))’
 >-- cheat >>
 rpt strip_tac >> rw[Mulz_Asz] >>
 qsuff_tac
 ‘Add(Mul(a, c), Mul(b, d)) = Add(Mul(c, a), Mul(d, b)) &
  Add(Mul(a, d), Mul(b, c)) = Add(Mul(c, b), Mul(d, a))’ 
 >-- (strip_tac >> arw[]) >>
 cheat (* tedious *))
(form_goal “!z1 z2. Mulz(z1,z2) = Mulz(z2,z1)”));


(*[a,b]≤[c,d] ⇔ a+d≤b+c (⇔ ⟨a,b⟩≤⟨c,d⟩).*)

val le0_def = qdefine_psym ("le0",[‘ab:mem(N * N)’,‘cd:mem(N * N)’])
‘Le(Add(Fst(ab),Snd(cd)),Add(Snd(ab),Fst(cd)))’
|> gen_all |> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[Pair_def'] |> store_as "le0_def"; 


val Lez_def = qdefine_psym ("Lez",[‘z1:mem(Z)’,‘z2:mem(Z)’])
‘!a b c d.Repz(z1) = Zc(a,b) & Repz(z2) = Zc(c,d) ==>
 Le(Add(a,d),Add(b,c))’ |> gen_all |> store_as "Lez_def";

(*
val iscoPr_def = qdefine_psym("iscoPr",[‘i1:A->AB’,‘i2:B->AB’])
‘!X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g’
|> qgenl [‘A’,‘B’,‘AB’,‘i1’,‘i2’]
|> store_as "iscoPr_def";



val iscoPr_ex = prove_store("iscoPr_ex",
e0
cheat
(form_goal “!A B.?AB i1:A->AB i2:B->AB.iscoPr(i1,i2)”));



val coPo_def = iscoPr_ex |> spec_all 
                         |> qSKOLEM "+" [‘A’,‘B’] |> gen_all
                         |> store_as "coPo_def";

val i1_def = coPo_def |> spec_all 
                      |> qSKOLEM "i1" [‘A’,‘B’] |> gen_all
                      |> store_as "i1_def";

val i2_def = i1_def |> spec_all |> qSKOLEM "i2" [‘A’,‘B’] |> gen_all
                    |> store_as "i2_def";

val coPa_def = i2_def |> rewr_rule[iscoPr_def] |> spec_all
                      |> uex_expand 
                      |> qSKOLEM "coPa" [‘f’,‘g’]
                      |> gen_all
                      |> store_as "coPa_def";

val r2f_def = proved_th $
e0
cheat
(form_goal “!R:A~>B. ?!f:A * B -> 1+1.
 !a b. App(f,Pair(a,b)) = App(i2(1,1),dot)  <=> Holds(R,a,b)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "r2f" [‘R’] |> gen_all

val true_def = qdefine_fsym("true",[]) ‘App(i2(1,1),dot)’

val id_ER = prove_store("id_ER",
e0
(rw[id_def,ER_def,Refl_def,Sym_def,Trans_def] >> rpt strip_tac >> arw[])
(form_goal “!A. ER(id(A))”));


(*
val le0_def = qdefine_psym ("le0",[‘ab:mem(N * N)’,‘cd:mem(N * N)’])
‘Le(Add(Fst(ab),Snd(cd)),Add(Snd(ab),Fst(cd)))’
|> gen_all |> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[Pair_def'] |> store_as "le0_def"; 
*)

val ler0_def = proved_th $
e0
cheat
(form_goal “?lef0:(N * N) ~> (N * N). !a b c d.Holds(lef0,Pair(a,b),Pair(c,d))<=> Le(Add(a,d),Add(b,c))
 ”) |> qSKOLEM "ler0" []

val Sg_Inj = prove_store("Sg_Inj",
e0
(rw[Inj_def] >> rw[GSYM IN_EXT_iff,Sg_def] >> rpt strip_tac >>
 first_x_assum (qspecl_then [‘x1’] assume_tac) >> fs[] )
(form_goal “!A. Inj(Sg(A))”));

val resp_lef0 = prove_store("resp_lef0",
e0
(cheat)
(form_goal “resp(r2f(ler0), prrel(ZR, ZR), id(1 + 1))”));

val Quo_id_Sg = prove_store("Quo_id_Sg",
e0
(rw[Quo_def,GSYM IN_EXT_iff,Sg_def,IN_rsi,id_def] >> 
 rpt strip_tac >> dimp_tac >> rpt strip_tac(* 2 *)
 >-- (pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘q’ >> arw[] >> strip_tac >> lflip_tac >> rw[]) >>
 uex_tac >> qexists_tac ‘a’ >> flip_tac >> arw[] >>
 rpt strip_tac >> first_x_assum (qspecl_then [‘q'’] assume_tac) >> fs[])
(form_goal “!A.Quo(id(A),Sg(A))”));

val main_LEzf = 
Quo_fun |> qspecl [‘(N * N) * (N * N)’,‘1+1’,
                ‘r2f(ler0)’,
                ‘prrel(ZR,ZR)’,‘id(1+1)’,
                ‘Z * Z’,‘1+1’,
                ‘ipow2(iZ,iZ)’,‘Sg(1+1)’]
|> rewr_rule[addz_conds,id_ER,Sg_Inj,Quo_id_Sg,resp_lef0]
|> qSKOLEM "LEzf" []
|> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[rext_def]



val Pow_conj_eq' = proved_th $
e0
(rpt gen_tac >> disch_tac >> drule Pow_conj_eq >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum drule >> arw[])
 >-- (first_x_assum drule >> arw[]) >>
 arw[])
(form_goal “∀A B s1:mem(Pow(A)) s2:mem(Pow(B)) s3 s4 a0 b0. IN(a0,s1) & IN(b0,s2) ⇒ ( (∀a b. IN(a,s1) & IN(b,s2) ⇔ IN(a,s3) & IN(b,s4)) <=> 
 s1 = s3 & s2 = s4)”) |> spec_all |> undisch
|> gen_all |> disch_all|> gen_all


val Repz_iff_Asz = prove_store("Repz_iff_Asz",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (irule Repz_eq_eq >> arw[Asz_Repz]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 arw[Asz_Repz])
(form_goal “!z a b. Repz(z) = Zc(a, b) <=> Asz(a,b) = z”));

val ipow2_prrel_ZR = prove_store("ipow2_prrel_ZR",
e0
(rw[ipow2_def,GSYM IN_EXT_iff,IN_rsi] >>
fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
fconv_tac (depth_fconv no_conv forall_cross_fconv) >> 
rw[prrel_def,ipow2_def] >>
rw[GSYM IN_rsi] >>
qby_tac ‘?xy uv.IN(xy,Repz(z1)) & IN(uv,Repz(z2))’
>-- (qspecl_then [‘z1’] strip_assume_tac iZ_nonempty >>
    qspecl_then [‘z2’] strip_assume_tac iZ_nonempty >>
    rw[Repz_def] >> qexistsl_tac [‘ab’,‘ab'’] >> arw[]) >>
pop_assum (x_choosel_then ["xy","uv"] assume_tac) >>
drule Pow_conj_eq' >> rw[GSYM Repz_def] >> 
first_x_assum (qspecl_then [‘rsi(ZR, Pair(a, b))’,‘rsi(ZR, Pair(c, d))’] assume_tac)>> (*why arw does not work*)
arw[] >>
pop_assum mp_tac >> 
fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
strip_tac >> arw[] (*why must I use the cross fconv*)>>
rw[GSYM Zc_def,GSYM ZC_def,Repz_iff_Asz])
(form_goal
“App(ipow2(iZ, iZ), Pair(z1, z2)) = rsi(prrel(ZR, ZR), Pair(Pair(a,b),Pair(c,d))) <=> Asz(a,b) = z1 & Asz(c,d) = z2”));


val main_LEzf1 = 
main_LEzf |> rewr_rule[App_App_o,GSYM IN_EXT_iff,IN_rsi,id_def]
|> rewr_rule[IN_EXT_iff,Sg_def]
|> rewr_rule[GSYM IN_rsi,IN_EXT_iff]

val main_LEzf2 = prove_store("main_LEzf2",
e0
(rpt strip_tac >> 
 qspecl_then [‘z1’,‘z2’] assume_tac main_LEzf1 >>
 pop_assum (x_choosel_then ["abcd","tv"] assume_tac) >>
 qsspecl_then [‘abcd’] (x_choosel_then ["ab","cd"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘ab’] (x_choosel_then ["a","b"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘cd’] (x_choosel_then ["c","d"] assume_tac) Pair_has_comp >> 
 fs[ipow2_prrel_ZR] >> qexistsl_tac [‘a’,‘b’,‘c’,‘d’] >>
 arw[] >> 
 first_x_assum (qspecl_then [‘App(LEzf, Pair(z1, z2))’] assume_tac) >>
 fs[])
(form_goal “!z1 z2.?a b c d.
  Asz(a,b) = z1 & Asz(c,d) = z2 & 
  App(LEzf, Pair(z1, z2)) = App(r2f(ler0), Pair(Pair(a,b),Pair(c,d)))”));


val tv_eq_true = prove_store("tv_eq_true",
e0
(cheat)
(form_goal “!tv1 tv2. tv1 = tv2 <=>
 (tv1 = true <=> tv2 = true)”));


val main_LEzf3 = prove_store("main_LEzf3",
e0
(rpt strip_tac >> 
 qspecl_then [‘z1’,‘z2’] strip_assume_tac main_LEzf2 >>
 qexistsl_tac [‘a’,‘b’,‘c’,‘d’] >> arw[] >>
 rw[GSYM tv_eq_true])
(form_goal “!z1 z2.?a b c d.
  Asz(a,b) = z1 & Asz(c,d) = z2 & 
  (App(LEzf, Pair(z1, z2)) = true <=> 
  App(r2f(ler0), Pair(Pair(a,b),Pair(c,d))) = true)”));

val main_LEzf4 = main_LEzf3 |> rewr_rule[true_def,r2f_def,ler0_def] 
           |> rewr_rule[GSYM true_def]

val f2r_def = proved_th $
e0
cheat
(form_goal “!A B f:A * B -> 1+1.?!R:A~>B.
 !a b. Holds(R,a,b) <=> App(f,Pair(a,b)) = true”)
|> spec_all |> uex2ex_rule |> qSKOLEM "f2r" [‘f’] |> gen_all

val LEz_def0 = qdefine_fsym("LEz",[]) ‘f2r(LEzf)’;
*)

val LEz_def = AX1 |> qspecl [‘Z’,‘Z’] |> fVar_sInst_th “P(a:mem(Z),b:mem(Z))”
                  “Lez(a,b)”
                  |> uex2ex_rule |> qSKOLEM "LEz" []
                  |> store_as "LEz_def";

val LEz_Refl = prove_store("LEz_Refl",
e0
(rw[Refl_def,LEz_def,Lez_def] >>
 rpt strip_tac >> 
 qsuff_tac ‘Add(a', d) = Add(b, c)’
 >-- (strip_tac >> arw[Le_refl]) >>
 qsuff_tac ‘Holds(ZR,Pair(a',b),Pair(c,d))’
 >-- (rw[ZR_def] >> strip_tac >> arw[] >>
      qspecl_then [‘b’,‘c’] assume_tac Add_comm >> arw[]) >>
 irule $ iffLR ZC_ZR >> fs[Zc_def])
(form_goal “Refl(LEz)”));

val Repz_Zc = rewr_rule[GSYM Zc_def] Repz_ZC |> store_as "Repz_Zc";

val LEz_Trans = prove_store("LEz_Trans",
e0
(rw[Trans_def,LEz_def,Lez_def] >>
 rpt strip_tac >> 
 qspecl_then [‘a2’] strip_assume_tac Repz_Zc >>
 first_x_assum (qspecl_then [‘n1’,‘n2’,‘c’,‘d’] assume_tac) >> rfs[] >>
 first_x_assum (qspecl_then [‘a’,‘b’,‘n1’,‘n2’] assume_tac) >> rfs[] >>
 (qspecl_then [‘Add(n1, d)’,‘Add(a, n2)’,
                ‘Add(n2, c)’,‘Add(b, n1)’] assume_tac) Le_Add >> rfs[] >>
 fs[Add_assoc] >>
(*
 qby_tac ‘Add(Add(Add(n1, d), a), n2)  = Add(Add(Add(n1, n2), a), d)’
 qspecl_then [‘d’,‘n1’] assume_tac Add_comm >> fs[] >>
 qspecl_then [‘a’,‘Add(d,n1)’] assume_tac Add_comm >> fs[] >> 
 qspecl_then [‘a’,‘Add(d,n1)’] assume_tac Add_comm >> fs[] >> 
 fs[GSYM Add_assoc] >>
 qsspecl_then [‘Add(b, n1)’,‘Add(n2, c)’] assume_tac Add_comm >>*)
 cheat)
(form_goal “Trans(LEz)”));


val LEz_Asym = prove_store("LEz_Asym",
e0
(rw[Asym_def,LEz_def,Lez_def] >>
 rpt strip_tac >> cheat (*should easy  prove equal*))
(form_goal “Asym(LEz)”));





val Total_def = qdefine_psym("Total",[‘R:A~>A’])
‘!a b. Holds(R,a,b) | Holds(R,b,a)’ |> gen_all |> store_as "Total_def";

val LEz_Total = prove_store("LEz_Total",
e0
(rw[Total_def,LEz_def,Lez_def] >>
 rpt strip_tac >> 
 rw[Le_def] >> cheat (*should easy *))
(form_goal “Total(LEz)”));


(*[a,b]≤[c,d] ⇒ [a,b]+[e,f]≤[c,d]+[e,f]*)

val Lez_Addz = prove_store("Lez_Addz",
e0
(qsuff_tac
 ‘!a b c d e f.
 Lez(Asz(a,b),Asz(c,d)) ==>
 Lez(Addz(Asz(a,b),Asz(e,f)),Addz(Asz(c,d),Asz(e,f)))’
 >-- cheat >>
 rw[Lez_def] >> rpt strip_tac >> cheat)
(form_goal “!z1 z2 z3. Lez(z1,z2) ==> Lez(Addz(z1,z3),Addz(z2,z3))”));


(*[a,b] ≤ [c,d] and 0Z ≤ [e,f] ⇒ [a,b][e,f] ≤ [c,d][e,f]*)
val Lez_Mulz = prove_store("Lez_Mulz",
e0
(qsuff_tac
 ‘!a b c d e f.
 Lez(Asz(a,b),Asz(c,d)) ==>
 Lez(Addz(Asz(a,b),Asz(e,f)),Addz(Asz(c,d),Asz(e,f)))’
 >-- cheat >>
 rw[Lez_def] >> rpt strip_tac >> cheat)
(form_goal “!z1 z2 z3. Lez(z1,z2) & Lez(Oz,z3)==> 
 Lez(Mulz(z1,z3),Mulz(z2,z3))”));

(*
?a b c . f(a,b,c) = f(d,e,f) & ...


*)

(*

A r:A ~eq~>A 
Q >---i---> P(A)
Thm_2_4

A * -----f------> B
|               |
P(A) * ~~~im(f)~~> P(B)
|                |
/\               /\
Q1 ------------> Q2

:Po


L (l1 ~ l2) <=> same member 

map: A-> B |-> List(A) -> List(B)

{(0,a),(1,a')} rep of [a,a']

{} 


{(0,a),.....,(n,a),.....}

CONS h s = (0,h) INSERT (IMAGE (\(n,e). (n^+,e)) s)

colist: num -> a opt

{} colist empty
BIGUNION {x | x ⊆ f x}

iscolist(s) <=> 
?X. ... & IN(s,X)

!e:set of pairs. e in X ==> e = [] | ?h e0. e = e0 :: h0 &
                            e0 in X
*)
