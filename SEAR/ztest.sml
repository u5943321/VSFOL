
val ZR_def = 
AX1 |> qspecl [‘N * N’,‘N * N’] 
    |> fVar_sInst_th “P(mn:mem(N * N),m'n':mem(N * N))”
       “Add(Fst(mn:mem(N * N)),Snd(m'n':mem(N * N))) = 
        Add(Fst(m'n'),Snd(mn))”
    |> qsimple_uex_spec "ZR" [] 
    |> qspecl [‘Pair(x:mem(N),y:mem(N))’,
               ‘Pair(u:mem(N),v:mem(N))’] 
    |> qgenl [‘x’,‘y’,‘u’,‘v’]  
    |> rewr_rule[Pair_def']
    |> store_as "ZR_def";


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
 

(*depth_fconv no_conv forall_cross_fconv “!a:mem(N * N) b:mem(N * N). P(a,b)”
not doing the desired thing *)


val ZR_Refl = prove_store("ZR_Refl",
e0
(rw[Refl_def,ZR_def] >> fconv_tac forall_cross_fconv >>
 rw[ZR_def])
(form_goal
 “Refl(ZR)”));

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



val Ri_def = 
P2fun_uex'|> qspecl [‘Pow(A)’,‘Pow(B)’] 
                   |> fVar_sInst_th “P(sa:mem(Pow(A)),sb:mem(Pow(B)))”
                      “!b. IN(b,sb) <=> ∃a. IN(a,sa) & Holds(r:A~>B,a,b)”
                   |> C mp 
                      (IN_def_P |> qspecl [‘B’]
                                |> fVar_sInst_th “P(b:mem(B))”
                                   “∃a. IN(a,sa) & Holds(r:A~>B,a,b)”
                                |> qgen ‘sa’)
                   |> qsimple_uex_spec "Ri" [‘r’] |> gen_all
                   |> qspecl [‘A’,‘B’,‘r:A~>B’,‘s:mem(Pow(A))’]
                   |> qgenl [‘A’,‘B’,‘r’,‘s’]

(*
val Ri_def = proved_th $
e0
(rw[Ri_def0])
(form_goal “∀A B r:A~>B s b. IN(b,App(Ri(r),s)) ⇔ 
 ∃a. IN(a,s) & Holds(r,a,b)”)
                   |> store_as "Ri_def";


*)
(*

val Ri_def = P2fun_uex'|> qspecl [‘Pow(A)’,‘Pow(B)’] 
                   |> fVar_sInst_th “P(sa:mem(Pow(A)),sb:mem(Pow(B)))”
                      “!b. IN(b,sb) <=> ∃a. IN(a,sa) & Holds(r:A~>B,a,b)”
                   |> C mp 
                      (IN_def_P |> qspecl [‘B’]
                                |> fVar_sInst_th “P(b:mem(B))”
                                   “∃a. IN(a,sa) & Holds(r:A~>B,a,b)”
                                |> qgen ‘sa’)
                   |> qsimple_uex_spec "Ri" [‘r’] |> gen_all
                   |> qspecl [‘A’,‘B’,‘r:A~>B’,‘s:mem(Pow(A))’]
                   |> qgenl [‘A’,‘B’,‘r’,‘s’]


P2fun'|> qspecl [‘Pow(A)’,‘Pow(B)’] 
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
*)



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



val Z_def = Thm_2_4'|> qspecl [‘Pow(N * N)’]
                    |> fVar_sInst_th “P(s:mem(Pow(N * N)))”
                    “?n. s = rsi(ZR,n)”
                    |> set_spec (rastt "Pow(N*N)") "Z" "iZ" []
                    |> store_as "Z_def";

(*
Thm_2_4 |> qspecl [‘Pow(N * N)’]
                    |> fVar_sInst_th “P(s:mem(Pow(N * N)))”
                    “?n. s = rsi(ZR,n)”
                    |> qSKOLEM "Z" []
                    |> qSKOLEM "iZ" []
                    |> store_as "Z_def";
*)

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


val rext_def0 =  AX1 |> qspecl [‘Pow(A)’,‘Pow(B)’] 
                   |> fVar_sInst_th “P(sa:mem(Pow(A)),sb:mem(Pow(B)))”
                      “?a b.sa = rsi(r1:A~>A,a) & sb = rsi(r2:B~>B,b) & 
                            App(f,a) = b”
                   |> qsimple_uex_spec "rext" [‘f’,‘r1’,‘r2’]
                   |> gen_all 

val rext_def = proved_th $
e0
(rw[rext_def0])
(form_goal
 “!A r1:A~>A B f:A->B r2 a0 b0.
   Holds(rext(f, r1, r2), a0, b0) <=>
   ?a b.
   a0 = rsi(r1, a) & b0 = rsi(r2, b) & App(f, a) = b”)
|> store_as "rext_def";

(*rext_def and def0 due to var name broken issue,maybe let qspecl leave all the 
bounded vars*)
(*


AX1 |> qspecl [‘Pow(A)’,‘Pow(B)’] 
                   |> fVar_sInst_th “P(sa:mem(Pow(A)),sb:mem(Pow(B)))”
                      “?a b.sa = rsi(r1:A~>A,a) & sb = rsi(r2:B~>B,b) & 
                            App(f,a) = b”
                   |> uex2ex_rule
                   |> qSKOLEM "rext" [‘f’,‘r1’,‘r2’]
                   |> gen_all |> store_as "rext_def";          

*)             


val prrel_def = AX1 |> qspecl [‘A * B’,‘A * B’]
                    |> fVar_sInst_th “P(ab1:mem(A * B),ab2:mem(A * B))”
                       “Holds(r1:A~>A,Fst(ab1),Fst(ab2)) &
                        Holds(r2:B~>B,Snd(ab1),Snd(ab2))”
                    |> qsimple_uex_spec "prrel" [‘r1’,‘r2’]
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

val ipow2_def = P2fun_uex' |> qspecl [‘Q1 * Q2’,‘Pow(A * B)’] 
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
                     |> qsimple_uex_spec "ipow2" [‘i1’,‘i2’]
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
val l = P2fun_uex' |> qspecl [‘(N * N) * N * N’,‘N * N’]
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
(form_goal “?!f:(N * N) * N * N -> N * N. 
 !x y u v. App(f,Pair(Pair(x,y),Pair(u,v))) = 
 Pair(Add(x,u),Add(y,v))”)
|> qsimple_uex_spec "addf0" []
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
 cases_on “IN(a0:mem(A),s3)” (* 2 *) >-- chet
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
chet)

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


val main_uex = prove_store("main_uex",
e0
(rpt strip_tac >> assume_tac 
 (P2fun_uex|> qspecl [‘Q1’,‘Q2’] 
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
 ?!qf: Q1-> Q2.
 !q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1)) ”));





val Quo_fun_uex = prove_store("Quo_fun",
e0
(rpt strip_tac >> 
 irule main_uex >> arw[] >> strip_tac (* 2 *)
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
 ?!qf: Q1-> Q2.
 !q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1)) ”))



val Inj_Quo_Z = prove_store("Inj_Quo_Z",
e0
(rw[GSYM Inj_Quo,iZ_Inj] >>
 rw[GSYM Z_def])
(form_goal “Inj(iZ) & Quo(ZR, iZ)”));



(*may need con rw for simplifying main_addz'*)
val iZ_nonempty = prove_store("iZ_nonempty",
e0
(strip_tac >> strip_assume_tac Z_def >> 
 qsuff_tac ‘∃n. App(iZ,z) = rsi(ZR,n)’ 
 >-- (strip_tac >> arw[] >> qexists_tac ‘n’ >> irule ER_rsi_nonempty >>
     rw[ZR_ER]) >>
 first_x_assum (irule o iffRL) >> qexists_tac ‘z’ >> rw[])
(form_goal “∀z. ∃ab. IN(ab,App(iZ,z))”));

 
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
 arw[Add_assoc] >> 
 qspecl_then [‘c’,‘a’] assume_tac Add_comm >> arw[] >>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(v, Add(y1, a)) = Add(a, Add(y1, v))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘Add(y1,v)’,‘a’] assume_tac Add_comm >> arw[] >>
 rw[Add_assoc] >>
 qspecl_then [‘y1’,‘v’] assume_tac Add_comm >> arw[])
(form_goal “resp(addf0, prrel(ZR, ZR), ZR)”));
 
val addz_conds = proved_th $
e0
(assume_tac Inj_Quo_Z >> assume_tac ZR_ER >> arw[] >> rpt strip_tac (* 4 *)
 >-- (irule prrel_ER_ER >> arw[])
 >-- rw[addf0_resp] (*hard one*)
 >-- (irule ipow2_Inj_Inj >> arw[] >> 
     rw[iZ_nonempty]) >>
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
Quo_fun_uex |> qspecl [‘(N * N) * (N * N)’,‘N * N’,
                ‘addf0’,
                ‘prrel(ZR,ZR)’,‘ZR’,
                ‘Z * Z’,‘Z’,
                ‘ipow2(iZ,iZ)’,‘iZ’]
        |> conv_rule (depth_fconv no_conv forall_cross_fconv)
        |> C mp addz_conds
        |> qsimple_uex_spec "addz" []
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
 >-- >> do not need it, but an option *)
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



val negf0_def = 
qfun_compr ‘mn:mem(N*N)’ ‘Pair(Snd(mn:mem(N * N)),Fst(mn))’
|> qsimple_uex_spec "negf0" []
      |> store_as "negf0_def";



val negf0_def1 = 
    negf0_def |> qspecl [‘Pair(m:mem(N),n:mem(N))’]
              |> rewr_rule[Pair_def']
              |> gen_all |> store_as "negf0_def1";



val negf0_resp = prove_store("negf0_resp",
e0
(rw[resp_def] >>
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[negf0_def1] >> rpt strip_tac >>
 fs[ZR_def] >>
 qspecl_then [‘b’,‘a'’] assume_tac Add_comm >>
 qspecl_then [‘a’,‘b'’] assume_tac Add_comm >> fs[])
(form_goal “resp(negf0, ZR, ZR)”));

val main_negz = 
Quo_fun_uex |> qspecl [‘N * N’,‘N * N’,
                ‘negf0’,
                ‘ZR’,‘ZR’,
                ‘Z’,‘Z’,
                ‘iZ’,‘iZ’]
        |> rewr_rule[Inj_Quo_Z,ZR_ER,negf0_resp]
        |> qsimple_uex_spec "negz" []
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
 x_choosel_then ["a1","a2"] assume_tac main_negz1
 (*strip_assume_tac main_negz1*) >> arw[ZC_ZR] >>
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
val l = P2fun_uex' |> qspecl [‘(N * N) * N * N’,‘N * N’]
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
(form_goal “?!f:(N * N) * N * N -> N * N. 
 !a b c d. App(f,Pair(Pair(a,b),Pair(c,d))) = 
 Pair(Add(Mul(a,c),Mul(b,d)),Add(Mul(a,d),Mul(b,c)))”)
|> qsimple_uex_spec "mulf0" []
|> store_as "mulf0_def";
end


(*
Holds(ZR,Pair(a,b),Pair(p,q)) & 
Holds(ZR,Pair(c,d),Pair(r,s)) ==> 
 Holds(ZR,Mulj(Pair(a,b),Pair(c,d)),Mulj(Pair(p,q),Pair(r,s)))
*)
val mulf0_resp = prove_store("mulf0_resp",
e0
(rw[resp_def,prrel_def] >>
 rpt strip_tac >>
 qsspecl_then [‘z’] (x_choosel_then ["pq","rs"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘pq’] (x_choosel_then ["p","q"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘rs’] (x_choosel_then ["r","s"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘y’] (x_choosel_then ["ab","cd"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘ab’] (x_choosel_then ["a","b"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘cd’] (x_choosel_then ["c","d"] assume_tac) Pair_has_comp >>
 fs[mulf0_def,prrel_def,ZR_def] >>
 abbrev_tac 
 “Add(Mul(p,c),Add(Mul(q,c),Add(Mul(p,d),Mul(q,d)))) = l” >>
 qsuff_tac 
 ‘Add(Add(Add(Mul(a, c), Mul(b, d)), Add(Mul(p, s), Mul(q, r))),l) = 
  Add(Add(Add(Mul(p, r), Mul(q, s)), Add(Mul(a, d), Mul(b, c))),l)’ 
 >-- (rw[EQ_MONO_ADD_EQ] >> rpt strip_tac >> arw[]) >>
 qby_tac
 ‘Add(Add(Add(Mul(a, c), Mul(b, d)), Add(Mul(p, s), Mul(q, r))), l) =
  Add(Mul(Add(a,q),c),Add(Mul(Add(b,p),d),Add(Mul(p,Add(c,s)),Mul(q,Add(d,r)))))’
 >-- (pop_assum mp_tac >> pop_assum_list (map_every (K all_tac)) >>
     strip_tac>>
     rw[RIGHT_DISTR,GSYM Add_assoc] >> irule Add_req >>
     qspecl_then [‘Add(Mul(b, d),
                 Add(Mul(p, d), Add(Mul(p, Add(c, s)), Mul(q, Add(d, r)))))’,
                 ‘Mul(q,c)’] assume_tac Add_comm >> 
     arw[GSYM Add_assoc] >> irule Add_req >>
     qspecl_then [‘Add(Mul(p, Add(c, s)), Add(Mul(q, Add(d, r)), Mul(q, c)))’,
                  ‘Mul(p, d)’] assume_tac Add_comm >>
     arw[] >> qspecl_then [‘s’,‘c’] assume_tac Add_comm >> arw[] >>
     rw[LEFT_DISTR,GSYM Add_assoc] >> irule Add_req >>
     qspecl_then [‘Add(Mul(q, d), Add(Mul(q, r), Add(Mul(q, c), Mul(p, d))))’,
                   ‘Mul(p,c)’] assume_tac Add_comm >> arw[] >>
     qspecl_then [‘Add(Mul(q, r), Add(Mul(q, c), Mul(p, d)))’,‘Mul(q,d)’]
     assume_tac Add_comm >> arw[] >> rw[GSYM Add_assoc] >>
     irule Add_req >> last_x_assum mp_tac >>
     pop_assum_list (map_every (K all_tac)) >> strip_tac >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qspecl_then [‘Add(Mul(p, d), Add(Mul(q, d), Mul(p, c)))’,‘Mul(q,c)’]
     assume_tac Add_comm >> arw[] >>  rw[GSYM Add_assoc] >>
     rw[Add_middle] >> rw[] >>
     qspecl_then [‘Add(Mul(p, d), Mul(q, d))’,‘Add(Mul(p, c), Mul(q, c))’]
     assume_tac Add_comm >> arw[]) >>
 qby_tac
 ‘Add(Add(Add(Mul(p, r), Mul(q, s)), Add(Mul(a, d), Mul(b, c))), l) =
  Add(Mul(Add(b,p),c),Add(Mul(Add(a,q),d),Add(Mul(p,Add(d,r)),Mul(q,Add(c,s)))))’
 >-- (qpick_x_assum 
     ‘Add(Mul(p, c), Add(Mul(q, c), Add(Mul(p, d), Mul(q, d)))) = l’ mp_tac >>
     pop_assum_list (map_every (K all_tac)) >>
     strip_tac>>
     qspecl_then [‘Mul(b,c)’,‘Mul(a, d)’] assume_tac Add_comm >> arw[] >>
     qspecl_then [‘Add(Mul(b, c), Mul(a, d))’,‘Add(Mul(p, r), Mul(q, s))’] 
     assume_tac Add_comm >> arw[] >> 
     rw[RIGHT_DISTR] >> rw[GSYM Add_assoc] >> irule Add_req >>
     qspecl_then [‘Add(Mul(a, d),
                 Add(Mul(q, d), Add(Mul(p, Add(d, r)), Mul(q, Add(c, s)))))’,
                 ‘Mul(p, c)’] assume_tac Add_comm >> arw[] >>
     rw[GSYM Add_assoc] >> irule Add_req >>
     qspecl_then [‘r’,‘d’] assume_tac Add_comm >> arw[] >> 
     qspecl_then [‘Add(Mul(p, Add(r, d)), Add(Mul(q, Add(c, s)), Mul(p, c)))’,
                  ‘Mul(q, d)’] assume_tac Add_comm >> arw[] >>
     rw[LEFT_DISTR] >> rw[GSYM Add_assoc] >> irule Add_req >>
     qspecl_then [‘Add(Mul(q, s), Add(Mul(p, c), Mul(q, d)))’,‘Mul(q, c)’]
     assume_tac Add_comm >> arw[] >>
     qspecl_then [‘Add(Add(Mul(q, s), Add(Mul(p, c), Mul(q, d))), Mul(q, c))’,
                  ‘Mul(p, d)’] assume_tac Add_comm >> 
     arw[] >> rw[GSYM Add_assoc] >> irule Add_req >>
     last_x_assum mp_tac >>
     pop_assum_list (map_every (K all_tac)) >> strip_tac >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     irule Add_req >> 
     qspecl_then [‘Add(Mul(q, c), Mul(p, d))’,‘Mul(q, d)’] assume_tac
     Add_comm >> arw[] >> rw[Add_assoc]) >>
 arw[] >>
 qspecl_then [‘b’,‘p’] assume_tac Add_comm >> arw[] >>
 qspecl_then [‘d’,‘r’] assume_tac Add_comm >> arw[])
(form_goal “resp(mulf0, prrel(ZR, ZR), ZR)”));

val main_mulz = 
Quo_fun_uex |> qspecl [‘(N * N) * (N * N)’,‘N * N’,
                ‘mulf0’,
                ‘prrel(ZR,ZR)’,‘ZR’,
                ‘Z * Z’,‘Z’,
                ‘ipow2(iZ,iZ)’,‘iZ’]
        |> rewr_rule[addz_conds,mulf0_resp]
        |> conv_rule (depth_fconv no_conv forall_cross_fconv)
        |> qsimple_uex_spec "mulz" []
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



val absz_def = 
    P2fun_uex0
        |> qspecl [‘N * N’,‘Z’] 
        |> fVar_sInst_th “P(ab:mem(N * N),y:mem(Z))”
                      “Repz(y) = ZC(ab)”
        |> conv_rule (top_depth_fconv no_conv forall_cross_fconv)
        |> C mp ZC_Repz
        |> qsimple_uex_spec  "absz" []
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
 pop_assum (x_choosel_then ["n1","n2"] assume_tac) >>
 (*pop_assum strip_assume_tac >> *)
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
 >-- (rpt strip_tac >>
      qspecl_then [‘z1’] strip_assume_tac cases_z >>
      qspecl_then [‘z2’] strip_assume_tac cases_z >>
      qspecl_then [‘z3’] strip_assume_tac cases_z >>
      fs[]) >>
 rpt strip_tac >> 
 rw[Mulz_Asz,Asz_eq_ZR,LEFT_DISTR,RIGHT_DISTR,Mul_assoc,GSYM Add_assoc] >>
 irule eq_ZR >> rw[Pair_eq_eq] >> strip_tac (* 2 *)
 >-- (irule Add_req >>  
     qspecl_then [‘Add(Mul(Mul(a, d), f), Mul(Mul(b, c), f))’,
                   ‘Mul(Mul(b, d), e)’] assume_tac Add_comm >>
     arw[] >> rw[Add_assoc]) >>
 irule Add_req >>
 qspecl_then [‘Add(Mul(Mul(a, d), e), Mul(Mul(b, c), e))’,
              ‘Mul(Mul(b, d), f)’] assume_tac Add_comm >>
 arw[] >> rw[Add_assoc])
(form_goal “!z1 z2 z3. Mulz(Mulz(z1,z2),z3) = Mulz(z1,Mulz(z2,z3))”));

(*[a,b]([c,d]+[e,f])=[a,b][c,d]+[a,b][e,f]*)
val LDISTR_Z = prove_store("LDISTR_Z",
e0
(qsuff_tac
 ‘!a b c d e f. Mulz(Asz(a,b),Addz(Asz(c,d),Asz(e,f))) = 
  Addz(Mulz(Asz(a,b),Asz(c,d)),Mulz(Asz(a,b),Asz(e,f)))’ 
 >-- (rpt strip_tac >>
     qspecl_then [‘z1’] strip_assume_tac cases_z >>
     qspecl_then [‘z2’] strip_assume_tac cases_z >>
     qspecl_then [‘z3’] strip_assume_tac cases_z >>
     fs[]) >>
 rpt strip_tac >> rw[Mulz_Asz,Addz_Asz,LEFT_DISTR] >>
 qsuff_tac 
‘Add(Add(Mul(a, c), Mul(a, e)), Add(Mul(b, d), Mul(b, f))) =
 Add(Add(Mul(a, c), Mul(b, d)), Add(Mul(a, e), Mul(b, f))) & 
 Add(Add(Mul(a, d), Mul(a, f)), Add(Mul(b, c), Mul(b, e))) = 
 Add(Add(Mul(a, d), Mul(b, c)), Add(Mul(a, f), Mul(b, e)))’
 >-- (strip_tac >> arw[]) >>
 strip_tac (* 2 *)
 >-- (rw[GSYM Add_assoc] >> irule Add_req >>
     qspecl_then [‘Add(Mul(b, d), Mul(b, f))’,‘Mul(a, e)’]
     assume_tac Add_comm >> arw[] >>
     rw[GSYM Add_assoc] >> irule Add_req >>
     qspecl_then [‘Mul(a, e)’,‘Mul(b,f)’] assume_tac Add_comm >> arw[]) >>
 rw[GSYM Add_assoc] >> irule Add_req >>
 qspecl_then [‘Add(Mul(b, c), Mul(b, e))’,‘Mul(a, f)’]
 assume_tac Add_comm >> arw[] >>
 rw[GSYM Add_assoc] >> irule Add_req >>
 qspecl_then [‘Mul(b, e)’,‘Mul(a,f)’] assume_tac Add_comm >> arw[])
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
 >-- (rpt strip_tac >>
     qspecl_then [‘z1’] strip_assume_tac cases_z >>
     qspecl_then [‘z2’] strip_assume_tac cases_z >>
     once_arw[] >>
     first_x_assum (qspecl_then [‘a’,‘b’,‘a'’,‘b'’] assume_tac) >> arw[]) >>
 rpt strip_tac >> rw[Mulz_Asz] >>
 qsuff_tac
 ‘Add(Mul(a, c), Mul(b, d)) = Add(Mul(c, a), Mul(d, b)) &
  Add(Mul(a, d), Mul(b, c)) = Add(Mul(c, b), Mul(d, a))’ 
 >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (qspecl_then [‘a’,‘c’] assume_tac Mul_comm >>
     qspecl_then [‘d’,‘b’] assume_tac Mul_comm >> arw[]) >>
 qspecl_then [‘a’,‘d’] assume_tac Mul_comm >>
 qspecl_then [‘c’,‘b’] assume_tac Mul_comm >> arw[] >>
 qspecl_then [‘Mul(d, a)’,‘Mul(b, c)’] assume_tac Add_comm >> arw[])
(form_goal “!z1 z2. Mulz(z1,z2) = Mulz(z2,z1)”));


val RDISTR_Z = prove_store("RDISTR_Z",
e0
(rpt strip_tac >>
 once_rw[Mulz_comm] >> rw[LDISTR_Z])
(form_goal
 “!z1 z2 z3. Mulz(Addz(z2,z3),z1) = Addz(Mulz(z2,z1),Mulz(z3,z1))”));


(*[a,b]≤[c,d] ⇔ a+d≤b+c (⇔ ⟨a,b⟩≤⟨c,d⟩).*)

val le0_def = qdefine_psym ("le0",[‘ab:mem(N * N)’,‘cd:mem(N * N)’])
‘Le(Add(Fst(ab),Snd(cd)),Add(Snd(ab),Fst(cd)))’
|> gen_all |> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[Pair_def'] |> store_as "le0_def"; 


val Lez_def = qdefine_psym ("Lez",[‘z1:mem(Z)’,‘z2:mem(Z)’])
‘!a b c d.Repz(z1) = Zc(a,b) & Repz(z2) = Zc(c,d) ==>
 Le(Add(a,d),Add(b,c))’ |> gen_all |> store_as "Lez_def";

(*



val r2f_def = proved_th $
e0
cheat
(form_goal “!R:A~>B. ?!f:A * B -> 1+1.
 !a b. App(f,Pair(a,b)) = App(i2(1,1),dot)  <=> Holds(R,a,b)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "r2f" [‘R’] |> gen_all


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


val resp_lef0 = prove_store("resp_lef0",
e0
(cheat)
(form_goal “resp(r2f(ler0), prrel(ZR, ZR), id(1 + 1))”));


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

val LEz_def0 = qdefine_fsym("LEz",[]) ‘f2r(LEzf)’;
*)

val LEz_def = AX1 |> qspecl [‘Z’,‘Z’] |> fVar_sInst_th “P(a:mem(Z),b:mem(Z))”
                  “Lez(a,b)”
                  |> qsimple_uex_spec "LEz" []
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
 qspecl_then [‘a2’] assume_tac Repz_Zc >>
 pop_assum (x_choosel_then ["n1","n2"] assume_tac) >> 
(* qspecl_then [‘a2’] strip_assume_tac Repz_Zc >> *)
 first_x_assum (qspecl_then [‘n1’,‘n2’,‘c’,‘d’] assume_tac) >> rfs[] >>
 first_x_assum (qspecl_then [‘a’,‘b’,‘n1’,‘n2’] assume_tac) >> rfs[] >>
 (qspecl_then [‘Add(n1, d)’,‘Add(a, n2)’,
                ‘Add(n2, c)’,‘Add(b, n1)’] assume_tac) Le_Add >> rfs[] >>
 fs[Add_assoc] >>
 qby_tac ‘Add(Add(Add(n1, d), a), n2)  = Add(Add(a,d),Add(n1,n2))’
 >-- (qspecl_then [‘n2’,‘Add(Add(n1, d), a)’] assume_tac Add_comm >>
     arw[] >> rw[GSYM Add_assoc] >> rw[Add_middle] >>
     qspecl_then [‘Add(d,a)’,‘Add(n2,n1)’] assume_tac Add_comm >> arw[] >>
     qspecl_then [‘d’,‘a’] assume_tac Add_comm >>
     qspecl_then [‘n1’,‘n2’] assume_tac Add_comm >> arw[]) >>
 qby_tac ‘Add(Add(Add(n2, c), b), n1)  = Add(Add(b,c),Add(n1,n2))’
 >-- (qspecl_then [‘n1’,‘Add(Add(n2, c), b)’] assume_tac Add_comm >> 
     arw[] >> rw[GSYM Add_assoc] >> rw[Add_middle] >> 
     qspecl_then [‘Add(c,b)’,‘Add(n1,n2)’] assume_tac Add_comm >> arw[] >>
     qspecl_then [‘c’,‘b’] assume_tac Add_comm >> arw[]) >>
 fs[] >> fs[LESS_EQ_MONO_ADD_EQ])
(form_goal “Trans(LEz)”));


val LEz_Asym = prove_store("LEz_Asym",
e0
(rw[Asym_def,LEz_def,Lez_def] >>
 rpt strip_tac >> 
 irule Repz_eq_eq >> 
 qspecl_then [‘a’] (x_choosel_then ["x","y"] assume_tac) Repz_Zc >>
 qspecl_then [‘b’] (x_choosel_then ["u","v"] assume_tac) Repz_Zc >>
 arw[] >>
 rw[Zc_def,ZC_def] >> 
 assume_tac ZR_ER >> drule rsi_eq_ER >> arw[] >>
 rw[ZR_def] >> irule Le_Asym >> strip_tac (* 2 *)>-- 
 (last_x_assum (qspecl_then [‘x’,‘y’,‘u’,‘v’] assume_tac) >>
  rfs[] >> 
  qspecl_then [‘y’,‘u’] assume_tac Add_comm >> arw[]) >>
 first_x_assum (qspecl_then [‘u’,‘v’,‘x’,‘y’] assume_tac) >>
 rfs[] >>
 qspecl_then [‘v’,‘x’] assume_tac Add_comm >> arw[])
(form_goal “Asym(LEz)”));





val Total_def = qdefine_psym("Total",[‘R:A~>A’])
‘!a b. Holds(R,a,b) | Holds(R,b,a)’ |> gen_all |> store_as "Total_def";

val Lez_resp0 = prove_store("Lez_resp0",
e0
(qsuff_tac
 ‘!a b c d a' b' c' d'. Holds(ZR,Pair(a,b),Pair(a',b')) &
 Holds(ZR,Pair(c,d),Pair(c',d')) ==> 
 (Le(Add(a,d),Add(b,c)) <=> Le(Add(a',d'), Add(b',c')))’
 >-- strip_tac >> arw[] >>
 rpt strip_tac >> 
 qsuff_tac 
 ‘(Le(Add(a, d), Add(b, c)) <=> 
  Le(Add(Add(a,d),Add(b',d')), Add(Add(b,c),Add(b',d')))) &
  (Le(Add(Add(a,d),Add(b',d')), Add(Add(b,c),Add(b',d'))) <=> 
  Le(Add(Add(a',d'),Add(b,d)), Add(Add(b',c'),Add(b,d)))) & 
  (Le(Add(Add(a',d'),Add(b,d)), Add(Add(b',c'),Add(b,d))) <=> 
 Le(Add(a',d'), Add(b',c')))’
 >-- (rpt strip_tac >> arw[]) >> rpt strip_tac (* 3 *)
 >-- rw[LESS_EQ_MONO_ADD_EQ]
 >-- (qsuff_tac ‘Add(Add(a, d), Add(b', d')) = 
                Add(Add(a', d'), Add(b, d)) & 
                Add(Add(b, c), Add(b', d')) = 
                Add(Add(b', c'), Add(b, d))’
     >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
     >-- (fs[ZR_def] >> qsspecl_then [‘Add(b',d')’,‘Add(a,d)’] 
          assume_tac Add_comm >> arw[] >>
          qsspecl_then [‘d'’,‘b'’] assume_tac Add_comm >> arw[] >>
          rw[Add_assoc] >>
          qsuff_tac ‘Add(Add(d', b'), a) = 
                     Add(Add(a', d'), b)’
          >-- (strip_tac >> arw[]) >>
          qsspecl_then [‘d'’,‘a'’] assume_tac Add_comm >> arw[] >>
          rw[GSYM Add_assoc] >> 
          qsspecl_then [‘a’,‘b'’] assume_tac Add_comm >> arw[]) >>
     fs[ZR_def] >>
     qsspecl_then [‘Add(b',d')’,‘Add(b,c)’] assume_tac Add_comm >>
     arw[] >> 
     qsspecl_then [‘c’,‘b’] assume_tac Add_comm >> arw[] >>
     qsspecl_then [‘d’,‘b’] assume_tac Add_comm >> arw[] >>
     rw[Add_assoc] >>
     qsuff_tac ‘Add(Add(b', d'), c) = Add(Add(b', c'), d)’ 
     >-- (strip_tac >> arw[]) >>
     rw[GSYM Add_assoc] >>
     qsspecl_then [‘c’,‘d'’] assume_tac Add_comm >> arw[]) >>
 rw[LESS_EQ_MONO_ADD_EQ])
(form_goal “!a b c d e f g h.Holds(ZR,Pair(a,b),Pair(c,d)) & 
 Holds(ZR,Pair(e,f),Pair(g,h)) ==>
 (Le(Add(a,f),Add(b,e)) <=> Le(Add(c,h),Add(d,g)))”));





val LEz_Total = prove_store("LEz_Total",
e0
(rw[Total_def,LEz_def,Lez_def] >>
 rpt strip_tac >> 
 qcases ‘!x y u v.Repz(a) = Zc(x,y) & Repz(b) = Zc(u,v) ==>
 Le(Add(x,v),Add(y,u))’
 >-- arw[] >>
 disj2_tac >> rpt strip_tac >>
 ccontra_tac >>
 qspecl_then [‘Add(a', d)’,‘Add(b', c)’] assume_tac LESS_EQ_cases >>
 qby_tac ‘Le(Add(b', c), Add(a', d))’ >-- fs[] >>
 qsuff_tac ‘!x y u v.Repz(a) = Zc(x,y) & Repz(b) = Zc(u,v) ==>
 Le(Add(x,v),Add(y,u))’
 >-- arw[] >>
 rpt strip_tac >> irule $ iffLR Lez_resp0 >>
 qexistsl_tac [‘c’,‘d’,‘a'’,‘b'’] >> rpt strip_tac >-- 
 (qspecl_then [‘b'’,‘c’] assume_tac Add_comm >>
 qspecl_then [‘a'’,‘d’] assume_tac Add_comm >>arw[]) 
 >-- (assume_tac ZR_ER >> drule $ GSYM rsi_eq_ER >>
     arw[] >> rw[GSYM ZC_def,GSYM Zc_def] >>
     qpick_x_assum ‘Repz(a) = Zc(x, y)’ (assume_tac o GSYM) >> arw[]) >>
 assume_tac ZR_ER >> drule $ GSYM rsi_eq_ER >>
 arw[] >> rw[GSYM ZC_def,GSYM Zc_def] >>
 qpick_x_assum ‘Repz(b) = Zc(u, v)’ (assume_tac o GSYM) >> arw[])
(form_goal “Total(LEz)”));

val Lez_Asz = prove_store("Lez_Asz",
e0
(rpt strip_tac >>
 rw[Lez_def] >> dimp_tac >>rpt strip_tac(* 2 *)
 >-- (first_x_assum irule >> rw[Asz_Repz]) >>
 irule$ iffLR Lez_resp0 >>
 qexistsl_tac [‘a’,‘b’,‘c’,‘d’] >> arw[] >>
 assume_tac ZR_ER >> drule $ GSYM rsi_eq_ER >>
 arw[] >> rw[GSYM ZC_def,GSYM Zc_def] >>
 qpick_x_assum ‘Repz(Asz(a, b)) = Zc(a', b')’ (assume_tac o GSYM) >>
 qpick_x_assum ‘Repz(Asz(c, d)) = Zc(c', d')’ (assume_tac o GSYM) >>
 arw[] >> rw[Asz_Repz])
(form_goal “!a b c d.Lez(Asz(a,b),Asz(c,d)) <=> Le(Add(a,d),Add(b,c))”));


(*[a,b]≤[c,d] ⇒ [a,b]+[e,f]≤[c,d]+[e,f]*)

val Lez_Addz = prove_store("Lez_Addz",
e0
(qsuff_tac
 ‘!a b c d e f.
 Lez(Asz(a,b),Asz(c,d)) ==>
 Lez(Addz(Asz(a,b),Asz(e,f)),Addz(Asz(c,d),Asz(e,f)))’
 >-- (rpt strip_tac >>
     qspecl_then [‘z1’] strip_assume_tac cases_z >>
     qspecl_then [‘z2’] strip_assume_tac cases_z >>
     qspecl_then [‘z3’] strip_assume_tac cases_z >> fs[] >>
     first_x_assum irule >> arw[]) >>
 rpt strip_tac >> rw[Addz_Asz] >> fs[Lez_def] >>
 rpt strip_tac >> irule $ iffLR Lez_resp0 >>
 qexistsl_tac [‘Add(a,e)’,‘Add(b,f)’,‘Add(c, e)’,‘Add(d,f)’] >>
 rpt strip_tac (* 3 *)
 >-- (first_x_assum (qspecl_then [‘a’,‘b’,‘c’,‘d’] assume_tac) >>
     fs[Asz_Repz] >>
     qsuff_tac ‘Add(Add(a, e), Add(d, f)) = Add(Add(a, d), Add(e, f)) & 
                Add(Add(b, f), Add(c, e)) = Add(Add(b, c), Add(e, f))’
     >-- (strip_tac >> arw[LESS_EQ_MONO_ADD_EQ]) >>
     strip_tac (*2 *)
     >-- (rw[GSYM Add_assoc] >> irule Add_req >> rw[Add_assoc] >>
         irule Add_leq >>
         qspecl_then [‘e’,‘d’] assume_tac Add_comm >> arw[]) >>
     rw[GSYM Add_assoc] >> irule Add_req >> rw[Add_assoc] >>
     qspecl_then [‘f’,‘Add(c, e)’] assume_tac Add_comm >> arw[] >>
     rw[Add_assoc])
 >-- (assume_tac ZR_ER >> drule $ GSYM rsi_eq_ER >> arw[] >>
     rw[GSYM ZC_def,GSYM Zc_def] >>
     qpick_x_assum ‘Repz(Asz(Add(a, e), Add(b, f))) = Zc(a', b')’
     (assume_tac o GSYM) >> arw[Asz_Repz]) >>
assume_tac ZR_ER >> drule $ GSYM rsi_eq_ER >> arw[] >>
rw[GSYM ZC_def,GSYM Zc_def] >>
qpick_x_assum ‘Repz(Asz(Add(c, e), Add(d, f))) = Zc(c', d')’
 (assume_tac o GSYM) >> arw[Asz_Repz])
(form_goal “!z1 z2. Lez(z1,z2) ==> !z3.Lez(Addz(z1,z3),Addz(z2,z3))”));



(*[a,b] ≤ [c,d] and 0Z ≤ [e,f] ⇒ [a,b][e,f] ≤ [c,d][e,f]*)
val Lez_Mulz = prove_store("Lez_Mulz",
e0
(qsuff_tac
 ‘!a b c d e f.
 Lez(Asz(a,b),Asz(c,d)) & Lez(Asz(O,O),Asz(e,f))==>
 Lez(Mulz(Asz(a,b),Asz(e,f)),Mulz(Asz(c,d),Asz(e,f)))’
 >-- (rpt strip_tac >>
     qspecl_then [‘z1’] strip_assume_tac cases_z >>
     qspecl_then [‘z2’] strip_assume_tac cases_z >>
     qspecl_then [‘z3’] strip_assume_tac cases_z >> fs[Oz_def] >>
     first_x_assum irule >> arw[]) >>
 rpt strip_tac >> fs[Lez_def] >>
 rpt strip_tac >>
 irule $ iffLR Lez_resp0 >> fs[Mulz_Asz] >>
 qexistsl_tac [‘Add(Mul(a, e), Mul(b, f))’,‘Add(Mul(a, f), Mul(b, e))’,
‘Add(Mul(c, e), Mul(d, f))’,‘Add(Mul(c, f), Mul(d, e))’] >>
 rpt strip_tac (* 3 *)
 >-- (qby_tac
     ‘Add(Add(Mul(a, e), Mul(b, f)), Add(Mul(c, f), Mul(d, e))) = 
      Add(Mul(f,Add(b,c)),Mul(e,Add(a,d))) & 
      Add(Add(Mul(a, f), Mul(b, e)), Add(Mul(c, e), Mul(d, f))) = 
      Add(Mul(f,Add(a,d)),Mul(e,Add(b,c)))’
     >-- (rw[LEFT_DISTR] >> strip_tac (* 2 *)
          >-- (qspecl_then [‘d’,‘e’] assume_tac Mul_comm >> arw[] >>
              rw[Add_assoc] >> irule Add_leq >>
              qspecl_then [‘Mul(e,a)’,‘Add(Mul(f, b), Mul(f, c))’] 
              assume_tac Add_comm >> arw[GSYM Add_assoc] >>
              qspecl_then [‘e’,‘a’] assume_tac Mul_comm >> arw[] >>
              irule Add_req >>
              qspecl_then [‘b’,‘f’] assume_tac Mul_comm >> arw[] >>
              irule Add_req >> 
              qspecl_then [‘c’,‘f’] assume_tac Mul_comm >> arw[]) >>
          rw[GSYM Add_assoc] >>
          qspecl_then [‘f’,‘a’] assume_tac Mul_comm >> arw[] >>
          irule Add_req >>
          qspecl_then [‘Add(Mul(e, b), Mul(e, c))’,‘Mul(f, d)’]
          assume_tac Add_comm >> arw[] >>
          qspecl_then [‘d’,‘f’] assume_tac Mul_comm >> arw[] >>
          rw[Add_assoc] >> irule Add_leq >>
          qspecl_then [‘e’,‘b’] assume_tac Mul_comm >> arw[] >>
          qspecl_then [‘e’,‘c’] assume_tac Mul_comm >> arw[])  >>
     arw[] >> pop_assum (K all_tac) >>
     qsuff_tac
     ‘Le(Sub(Mul(e, Add(a, d)),Mul(f, Add(a, d))),
         Sub(Mul(e, Add(b, c)),Mul(f, Add(b, c))))’
     >-- (strip_tac >>
         qby_tac ‘Le(f,e)’ 
         >-- (first_x_assum (qspecl_then [‘O’,‘O’,‘e’,‘f’] assume_tac) >>
              fs[Asz_Repz,Add_O2]) >>
         drule Le_MONO_Mul' >>
         first_assum (qspecl_then [‘Add(a,d)’] assume_tac) >>
         drule SUB_ADD >> 
         first_x_assum (qspecl_then [‘Add(b,c)’] assume_tac) >> 
         drule SUB_ADD >>
         qby_tac
         ‘Le(Add(Sub(Mul(e, Add(a, d)), Mul(f, Add(a, d))),Mul(f, Add(a, d))),
             Add(Sub(Mul(e, Add(b, c)), Mul(f, Add(b, c))),Mul(f, Add(a, d))))’
         >-- (irule $ iffRL LESS_EQ_MONO_ADD_EQ >> arw[]) >>
         rfs[] >>
         qby_tac
         ‘Le(Add(Mul(e, Add(a, d)),Mul(f, Add(b, c))),
             Add(Add(Sub(Mul(e, Add(b, c)), Mul(f, Add(b, c))),
               Mul(f, Add(a, d))),Mul(f, Add(b, c))))’
         >-- (irule $ iffRL LESS_EQ_MONO_ADD_EQ >> arw[]) >>
         pop_assum mp_tac >> rw[GSYM Add_assoc] >>
         qspecl_then [‘Mul(f, Add(b, c))’,‘Mul(f, Add(a, d))’] assume_tac
         Add_comm >> arw[] >> 
         qspecl_then [‘Mul(f, Add(b, c))’,‘Mul(e, Add(a, d))’] assume_tac
         Add_comm >> arw[] >>
         strip_tac >>
         qsuff_tac ‘Add(Sub(Mul(e, Add(b, c)), Mul(f, Add(b, c))),
               Add(Mul(f, Add(b, c)), Mul(f, Add(a, d)))) = 
               Add(Mul(f, Add(a, d)), Mul(e, Add(b, c)))’
         >-- (strip_tac >> fs[]) >>
         rw[Add_assoc] >> arw[] >>
         qspecl_then [‘Mul(f, Add(a, d))’,‘Mul(e, Add(b, c))’] accept_tac
         Add_comm) >>
     rw[GSYM RIGHT_SUB_DISTR] >>
     once_rw[Mul_comm] >> irule Le_MONO_Mul' >>
     last_x_assum irule >> rw[Asz_Repz]) 
 >-- (assume_tac ZR_ER >> drule $ GSYM rsi_eq_ER >> arw[] >>
     rw[GSYM ZC_def,GSYM Zc_def] >>
     qpick_x_assum ‘Repz(Asz(Add(Mul(a, e), Mul(b, f)), Add(Mul(a, f), Mul(b, e)))) = Zc(a', b')’ (assume_tac o GSYM) >> arw[Asz_Repz]) >>
 assume_tac ZR_ER >> drule $ GSYM rsi_eq_ER >> arw[] >>
 rw[GSYM ZC_def,GSYM Zc_def] >>
 qpick_x_assum ‘Repz(Asz(Add(Mul(c, e), Mul(d, f)), Add(Mul(c, f), Mul(d, e)))) = Zc(c', d')’ (assume_tac o GSYM) >> arw[Asz_Repz]
(* ae + bf + cf + de <= af + be + ce + df
        f(c+b) + e(a+d) <= f(a+d) + e(b+c)*)
)
(form_goal “!z1 z2 z3. Lez(z1,z2) & Lez(Oz,z3)==> 
 Lez(Mulz(z1,z3),Mulz(z2,z3))”));





val EVEN_def = Thm1_case_1 |> qspecl [‘1+1’,‘El(true)’,‘NOT o p2(N,1+1)’]
                   |> rewr_rule[GSYM FUN_EXT,App_App_o,El_def,
                                App_Pa_Pair,Id_def,Pair_def,GSYM Suc_def,
                                dot_def]
                   |> qsimple_uex_spec "EVEN" []

val Even_def = qdefine_psym("Even",[‘n:mem(N)’])
               ‘App(EVEN,n) = true’

val O_Even = EVEN_def |> conjE1 |> qspecl [‘dot’] 
                      |> rewr_rule[GSYM Even_def] 

val Suc_Even = prove_store("Suc_Even",
e0
(rw[Even_def,EVEN_def,NOT_def] >> strip_tac >>
 qspecl_then [‘App(EVEN,n)’] strip_assume_tac (GSYM true_xor_false) >>
 qcases ‘App(EVEN, n) = false’ >> arw[NOT_def,GSYM true_ne_false] >>
 fs[false_xor_true,NOT_def,GSYM true_ne_false])
(form_goal “!n. Even(Suc(n)) <=> ~Even(n)”));

val Odd_def = qdefine_psym("Odd",[‘n:mem(N)’]) ‘~Even(n)’


val Even_not_Odd = prove_store("Even_not_Odd",
e0
(rw[Odd_def])
(form_goal “!n. Even(n) <=> ~Odd(n)”));



val Odd_not_Even = prove_store("Odd_not_Even",
e0
(rw[Even_not_Odd])
(form_goal “!n. Odd(n) <=> ~Even(n)”));

val id_ER = prove_store("id_ER",
e0
(rw[id_def,ER_def,Refl_def,Sym_def,Trans_def] >> rpt strip_tac >> arw[])
(form_goal “!A. ER(id(A))”));


val Sg_Inj = prove_store("Sg_Inj",
e0
(rw[Inj_def] >> rw[GSYM IN_EXT_iff,Sg_def] >> rpt strip_tac >>
 first_x_assum (qspecl_then [‘x1’] assume_tac) >> fs[] )
(form_goal “!A. Inj(Sg(A))”));


val Quo_id_Sg = prove_store("Quo_id_Sg",
e0
(rw[Quo_def,GSYM IN_EXT_iff,Sg_def,IN_rsi,id_def] >> 
 rpt strip_tac >> dimp_tac >> rpt strip_tac(* 2 *)
 >-- (pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘q’ >> arw[] >> strip_tac >> lflip_tac >> rw[]) >>
 uex_tac >> qexists_tac ‘a’ >> flip_tac >> arw[] >>
 rpt strip_tac >> first_x_assum (qspecl_then [‘q'’] assume_tac) >> fs[])
(form_goal “!A.Quo(id(A),Sg(A))”));


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


(*

val even0_def = qdefine_psym ("even0",[‘ab:mem(N * N)’])
‘(Even(Fst(ab)) & (Even(Snd(ab)))) | (Odd(Fst(ab)) & Odd(Snd(ab)))’
|> gen_all |> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[Pair_def'] |> store_as "even0_def"; 

val evenf0_def = proved_th $
e0
(cheat)
(form_goal “?!evenf0:N * N-> 1+1.
 !a b. App(evenf0,Pair(a,b)) = true <=> even0(Pair(a,b))”)
|> uex2ex_rule |> qSKOLEM "evenf0" []

val resp_evenf0 = prove_store("resp_evenf0",
e0
(rw[resp_def] >>
fconv_tac (depth_fconv no_conv forall_cross_fconv) >> 
rpt strip_tac >> rw[id_def] >> 
fs[ZR_def] >>
once_rw[tv_eq_true] >> rw[evenf0_def,even0_def] >>
qcases ‘Even(a) & Even(b)’ >> arw[] >> cheat >> cheat 
(*does smart proof exist?*))
(form_goal “resp(evenf0, ZR, id(1 + 1))”));


val IN_rsi_id = prove_store("IN_rsi_id",
e0
(rpt strip_tac >> rw[rsi_def,Rsi_def,id_def,Ri_def,App_App_o,Sg_def] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qpick_x_assum ‘a' = a0’ (assume_tac o GSYM) >> arw[]) >>
 qexists_tac ‘a’ >> arw[])
(form_goal “!A a:mem(A) a0. IN(a0,rsi(id(A),a)) <=> a0 = a”));
 
val EQ_EXT = prove_store("EQ_EXT",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 first_x_assum (qspecl_then [‘a1’] assume_tac) >> fs[] )
(form_goal “!A a1:mem(A) a2. (!a. a = a1 <=> a = a2) <=> a1 = a2”));


val main_EVENzf = 
Quo_fun |> qspecl [‘N * N’,‘1+1’,
                ‘evenf0’,
                ‘ZR’,‘id(1+1)’,
                ‘Z’,‘1+1’,‘iZ’,‘Sg(1+1)’]
        |> rewr_rule[id_ER,Sg_Inj,Quo_id_Sg,resp_evenf0,ZR_ER,Inj_Quo_Z]
        |> qSKOLEM "EVENzf" []
        |> rewr_rule[rext_def,GSYM IN_EXT_iff,IN_rsi_id,App_App_o,Sg_def] 
        |> rewr_rule[IN_EXT_iff,GSYM Repz_def]
        |> conv_rule (depth_fconv no_conv exists_cross_fconv) 
        |> rewr_rule[GSYM ZC_def,GSYM Zc_def,Repz_iff_Asz,EQ_EXT]

*)


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




val N2Z_def = qfun_compr ‘n:mem(N)’ ‘Asz(n,O)’
|> qsimple_uex_spec "N2Z" []

val n2z_def = qdefine_fsym("n2z",[‘n:mem(N)’]) ‘App(N2Z,n)’ |> gen_all

val Ltz_def = qdefine_psym("Ltz",[‘a:mem(Z)’,‘b:mem(Z)’])
‘Lez(a,b) & ~(a = b)’ |> gen_all



val Asz_eq_eq_r = prove_store("Asz_eq_eq_r",
e0
(rpt strip_tac >> rw[Asz_eq_ZR,ZR_def] >> once_rw[Add_comm] >>
 rw[Add_eq_eq_l] >> lflip_tac >> rw[])
(form_goal “!a b c.Asz(a,b) = Asz(a,c) <=> b = c”));


val Asz_eq_eq_l = prove_store("Asz_eq_eq_l",
e0
(rpt strip_tac >> rw[Asz_eq_ZR,ZR_def] >>
 rw[Add_eq_eq_l])
(form_goal “!a b c.Asz(a,c) = Asz(b,c) <=> a = b”));



val N2Z_Inj = prove_store("N2Z_Inj",
e0
(rw[Inj_def,N2Z_def,Asz_eq_eq_l])
(form_goal “Inj(N2Z)”));

(*give a imp theorem automatically drive trivial direction by substitution*)

fun prove_dimp_th th = 
    let val c = concl th
        val (l,r) = dest_imp c
        val r2l = basic_fconv (rewr_conv (assume r)) no_fconv l
                              |> rewr_rule[]
                              |> disch r
    in dimpI th r2l 
    end


val Repz_eq_eq_iff = prove_dimp_th (spec_all Repz_eq_eq)
|> store_as "Repz_eq_eq_iff";

val Abv_positive_ex0 = proved_th $
e0
(rpt strip_tac >>
 qsspecl_then [‘z’] strip_assume_tac cases_z >> 
 arw[Asz_eq_ZR,ZR_def,Add_O] >>
 irule Le_Add_ex >> fs[Lez_def] >> fs[Repz_iff_Asz] >>
 first_x_assum (qspecl_then [‘O’,‘O’,‘a’,‘b’] assume_tac) >>
 fs[Add_O2,Oz_def])
(form_goal “!z. Lez(Oz,z) ==> ?n. Asz(n,O) = z”)


val Lez_Negz = prove_store("Lez_Negz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Negz_Asz] >> rpt strip_tac >>
 rw[Lez_Asz] >> 
 fconv_tac 
 (rand_fconv no_conv
  (once_depth_fconv (rewr_conv (spec_all Add_comm)) no_fconv)) >>
 rw[])
(form_goal “!a b. Lez(Negz(a),Negz(b)) <=> Lez(b,a)”));


val Negz_eq_eq = prove_store("Negz_eq_eq",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Negz_Asz] >> rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘Negz(Asz(b, a)) = Negz(Asz(b', a'))’ 
     >-- arw[] >>
     fs[Negz_Asz]) >>
 qby_tac ‘Negz(Asz(a, b)) = Negz(Asz(a', b'))’ 
 >-- arw[] >>
 fs[Negz_Asz])
(form_goal “!a b. Negz(a) = Negz(b) <=> a = b”));
 

val Negz_Oz = prove_store("Negz_Oz",
e0
(rw[Oz_def,Negz_Asz])
(form_goal “Negz(Oz) = Oz”));



val Abv_negative_ex0 = proved_th $
e0
(rpt strip_tac >>
 drule $ iffRL Lez_Negz >> fs[Negz_Oz] >>
 drule Abv_positive_ex0 >> 
 pop_assum strip_assume_tac >>
 qexists_tac ‘n’ >> 
 irule $ iffLR Negz_eq_eq >> arw[Negz_Asz] >>
 fs[Add_O2,Oz_def])
(form_goal “!z. Lez(z,Oz) ==> ?n. Asz(O,n) = z”)

(*from LESS_EQ_cases*)

val Lez_dichotomy = prove_store("Lez_dichotomy",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >> 
 rw[Lez_Asz] >> rpt strip_tac >>
 fconv_tac 
 (rand_fconv no_conv
  (once_depth_fconv (rewr_conv (spec_all Add_comm)) no_fconv))>>
 rw[LESS_EQ_cases])
(form_goal “!a b.Lez(a,b) | Lez(b,a)”));

val Ltz_Asz = prove_store("Ltz_Asz",
e0
(rw[Ltz_def,Lez_Asz,Asz_eq_ZR,ZR_def,Lt_def] >>  
 qsspecl_then [‘b’,‘c’] assume_tac Add_comm >> arw[])
(form_goal “Ltz(Asz(a,b),Asz(c,d)) <=> Lt(Add(a,d),Add(b,c))”));


val NOT_Lez_Ltz = prove_store("NOT_Lez_Ltz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Lez_Asz,Ltz_Asz] >> rpt strip_tac >> 
  fconv_tac 
 (rand_fconv no_conv
  (once_depth_fconv (rewr_conv (spec_all Add_comm)) no_fconv))>> 
 rw[GSYM NOT_LESS])
(form_goal “!a b. ~Lez(a,b) <=> Ltz(b,a)”));


val Abv_uex = proved_th $
e0
(strip_tac >> qcases ‘Lez(Oz,z)’ (* 2 *)
 >-- (drule Abv_positive_ex0 >>
     pop_assum strip_assume_tac >> uex_tac >>
     qexists_tac ‘n’ >> arw[] >> arw[GSYM NOT_Lez_Ltz] >>
     rpt strip_tac >> irule $ iffLR Asz_eq_eq_l >> 
     qexists_tac ‘O’ >> arw[]) >>
 qsspecl_then [‘Oz’,‘z’] assume_tac Lez_dichotomy >> rfs[] >>
 drule Abv_negative_ex0 >>
 fs[NOT_Lez_Ltz] >> uex_tac >> qexists_tac ‘n’ >> arw[] >>
 rpt strip_tac >>
 irule $ iffLR Asz_eq_eq_r >> qexists_tac ‘O’ >> arw[])
(form_goal 
 “!z. ?!n. (Lez(Oz,z) &  Asz(n,O) = z) | 
           (Ltz(z,Oz) &  Asz(O,n) = z)”)

val Abv_def = Abv_uex 
|> spec_all |> qsimple_uex_spec "Abv" [‘z’] 
|> gen_all

val Abv_nonneg = prove_store("Abv_nonneg",
e0
(rpt strip_tac >>
 qsspecl_then [‘z’] assume_tac Abv_def >>
 pop_assum strip_assume_tac >>
 fs[GSYM NOT_Lez_Ltz])
(form_goal 
 “!z. Lez(Oz,z) ==> Asz(Abv(z),O) = z”));


val n2z_Abv = prove_store("n2z_Abv",
e0
(rpt strip_tac >> rw[n2z_def,N2Z_def] >>
 irule Abv_nonneg >> arw[])
(form_goal “!a.Lez(Oz, a) ==> n2z(Abv(a)) = a”));

val Oz_Mulz = prove_store("Oz_Mulz",
e0
(casez_tac >> rw[Oz_def,Mulz_Asz,Mul_clauses,Add_clauses])
(form_goal “!z.Mulz(Oz, z) = Oz”));


val Addz_Oz = prove_store("Addz_Oz",
e0
(casez_tac >> rw[Addz_Asz,Oz_def,Add_clauses])
(form_goal “!z.Addz(z,Oz) = z”));

(*ZERO_LESS_MULT as for num*)
val Oz_Ltz_Mulz = prove_store("Oz_Ltz_Mulz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >> rw[Oz_def] >>
 rw[Mulz_Asz,Ltz_Asz,Add_clauses,Mul_clauses] >>
 rpt strip_tac >>
 qby_tac ‘Lt(O,Sub(b',a'))’ 
 >-- arw[GSYM Lt_Sub_O] >>
 qsuff_tac
 ‘Lt(Mul(a,Sub(b',a')), Mul(b,Sub(b',a')))’ 
 >-- (rw[LEFT_SUB_DISTR] >>   
     qsspecl_then [‘Sub(Mul(a, b'), Mul(a, a'))’,‘Sub(Mul(b, b'), Mul(b, a'))’,
                   ‘Add(Mul(a,a'),Mul(b,a'))’]
     assume_tac LESS_MONO_ADD >>
     arw[] >> rw[Add_assoc] >>
     qby_tac ‘Add(Sub(Mul(a, b'), Mul(a, a')), Mul(a, a')) = Mul(a,b')’ 
     >-- (irule SUB_ADD >> irule Le_MONO_Mul2 >>
         fs[Lt_def,Le_refl]) >>
     arw[] >> rw[GSYM Add_assoc] >>
     qsspecl_then [‘Mul(b, a')’,‘Mul(a,a')’] assume_tac Add_comm >> arw[] >>
     rw[Add_assoc] >>
     qby_tac ‘Add(Sub(Mul(b, b'), Mul(b, a')), Mul(b, a')) = Mul(b,b')’
     >-- (irule SUB_ADD >> irule Le_MONO_Mul2 >>
         fs[Lt_def,Le_refl]) >>
     arw[] >>
     qsspecl_then [‘Mul(b,b')’,‘Mul(a,a')’] assume_tac Add_comm >> arw[]) >>
 qsspecl_then [‘a'’,‘b'’] assume_tac Lt_Sub_O >>
 rfs[] >>
 drule Lt_MONO_Mul >>
 first_x_assum rev_drule >> arw[])
(form_goal “!a b. Ltz(a,Oz) & Ltz(b,Oz) ==> Ltz(Oz,Mulz(a,b))”));



val int1_def = qdefine_fsym("int1",[]) ‘n2z(Suc(O))’

val int1_NONZERO = prove_store("int1_NONZERO",
e0
(rw[int1_def,n2z_def,N2Z_def] >>
 rw[Oz_def,Asz_eq_eq_l,Suc_NONZERO])
(form_goal “~(int1 = Oz)”));
 
(*TODO conv which just apply to RHS once
fconv_tac 
 (rand_fconv
  (once_depth_conv (rewr_conv (spec_all Add_comm))) no_fconv)
seems maybe stupid
*)

val Negz_Mulz = prove_store("Negz_Mulz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >> 
 rw[Negz_Asz,Mulz_Asz] >> rpt strip_tac >>
 fconv_tac 
 (rand_fconv
  (once_depth_conv (rewr_conv (spec_all Add_comm))) no_fconv) >> rw[])
(form_goal “!a b.Mulz(Negz(a),b) = Negz(Mulz(a,b))”));

val Mulz_Negz = prove_store("Mulz_Negz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >> 
 rw[Negz_Asz,Mulz_Asz])
(form_goal “!a b.Mulz(a,Negz(b)) = Negz(Mulz(a,b))”))

val Mulz_int1 = prove_store("Mulz_int1",
e0
(casez_tac >> rw[int1_def,n2z_def,N2Z_def,Mulz_Asz,Add_clauses,Mul_clauses])
(form_goal “!a.Mulz(a,int1) = a”))

val Ltz_Addz_Negz = prove_store("Ltz_Addz_Negz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>  
 rw[Ltz_Asz,Addz_Asz,Negz_Asz,Oz_def,Add_clauses])
(form_goal
“!a b.Ltz(a,b) <=> Ltz(Addz(a,Negz(b)),Oz)”));

val Ltz_Lez = prove_store("Ltz_Lez",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>  
 rw[Ltz_Asz,Lez_Asz] >> rw[Lt_Le])
(form_goal
“!a b.Ltz(a,b) ==> Lez(a,b)”));

val n2z_Oz_Lez = prove_store("n2z_Oz_Lez",
e0
(rw[Oz_def,Lez_Asz,n2z_def,N2Z_def,Add_clauses,O_LESS_EQ])
(form_goal “!a.Lez(Oz,n2z(a))”));

val Negz_Addz_Oz = prove_store("Negz_Addz_Oz",
e0
(casez_tac >> rw[Oz_def,Negz_Asz,Addz_Asz] >>
 rpt strip_tac >> rw[Asz_eq_ZR,ZR_def,Add_clauses] >>
 qsspecl_then [‘a’,‘b’] assume_tac Add_comm >> arw[] )
(form_goal “!z. Addz(Negz(z), z) = Oz”));

(*use Le_Add_ex *)


val Lez_Addz_ex = prove_store("Lez_Addz_ex",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Oz_def,Lez_Asz,Addz_Asz] >>
 rpt strip_tac >> 
 drule Le_Add_ex >>
 pop_assum strip_assume_tac >>  
 qsuff_tac
 ‘?a1 b1. Lez(Asz(O, O), Asz(a1,b1)) & Addz(Asz(a1,b1), Asz(a, b)) = Asz(a', b')’
 >-- (strip_tac >> qexists_tac ‘Asz(a1,b1)’ >> arw[]) >>
 rw[Lez_Asz,Addz_Asz,Add_clauses] >>  
 rw[Asz_eq_ZR,ZR_def] >> qexistsl_tac [‘p’,‘O’] >>
 rw[O_LESS_EQ] >> arw[Add_clauses,GSYM Add_assoc] >>
 qsspecl_then [‘a'’,‘b’] assume_tac Add_comm >> arw[] )
(form_goal
“!n m.Lez(n, m) ==> ?p. Lez(Oz,p) & Addz(p, n) = m” ));

(*Le_Add*)
val Lez_Addz_2 = prove_store("Lez_Addz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 strip_tac >> strip_tac >> casez_tac >> strip_tac >> strip_tac >>
 casez_tac >> rw[Lez_Asz,Addz_Asz] >> rpt strip_tac >>
 qsspecl_then [‘Add(a, b'')’,‘Add(a', b''')’,‘Add(b, a'')’,‘Add(b', a''')’]
 assume_tac LESS_EQ_LESS_EQ_MONO >> rfs[] >>
 qsuff_tac 
 ‘Add(Add(a, b''), Add(a', b''')) = Add(Add(a, a'), Add(b'', b''')) &
  Add(Add(b, a''), Add(b', a''')) = Add(Add(b, b'), Add(a'', a'''))’
 >-- (strip_tac >> fs[]) >> strip_tac (* 2 *)
 >-- (rw[GSYM Add_assoc] >>
     rw[Add_split_middle] >>
     qsspecl_then [‘b''’,‘a'’] assume_tac Add_comm >> arw[]) >>
 rw[GSYM Add_assoc] >>
 rw[Add_split_middle] >>
 qsspecl_then [‘b'’,‘a''’] assume_tac Add_comm >> arw[])
(form_goal “!a b c d. 
 Lez(a,c) & Lez(b,d) ==> Lez(Addz(a,b),Addz(c,d))”));


(*Le_Add*)
val Oz_Lez_Addz = prove_store("Oz_Lez_Addz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >> 
 rw[Oz_def,Lez_Asz,Addz_Asz,Add_clauses] >>
 rpt strip_tac (* 2 *) 
 >-- (rw[Add_assoc] >>
      qsspecl_then [‘a’,‘b’] assume_tac Add_comm >> 
      once_rw[Add_comm] >> arw[LESS_EQ_MONO_ADD_EQ]) >>
 once_rw[Add_comm]>> rw[GSYM Add_assoc] >>
 qsspecl_then [‘b'’,‘a'’] assume_tac Add_comm >> arw[] >>
 arw[LESS_EQ_MONO_ADD_EQ] )
(form_goal “!a b.
 Lez(Oz,a) & Lez(Oz,b) ==> Lez(a,Addz(a,b)) & Lez(b,Addz(a,b))”));



val Oz_Ltz_Addz = prove_store("Oz_Ltz_Addz",
e0
(casez_tac >> rw[Oz_def,Ltz_Asz,Addz_Asz,Add_clauses] >>rpt gen_tac >>
 strip_tac >> casez_tac >> rw[Addz_Asz,Ltz_Asz] >>
 rpt strip_tac >>
 once_rw[Add_comm] >> rw[GSYM Add_assoc] >>
 qsspecl_then [‘b'’,‘a'’] assume_tac Add_comm >> arw[] >>
 arw[GSYM LESS_MONO_ADD])
(form_goal “!a.
 Ltz(Oz,a) ==> !b.Ltz(b,Addz(a,b))”));


val int1_Asz = prove_store("int1_Asz",
e0
(rw[n2z_def,N2Z_def,int1_def])
(form_goal “int1 = Asz(Suc(O),O)”));

val Ltz_int1_Lez_Oz = prove_store("Ltz_int1_Lez_Oz",
e0
(casez_tac >> rw[Oz_def,int1_Asz,Ltz_Asz,Add_clauses,Lez_Asz] >>
 rpt strip_tac >> irule Le_Lt_Le >>
 qexists_tac ‘Suc(b)’ >> arw[LESS_EQ_SUC])
(form_goal “!a.Ltz(int1,a) ==> Lez(Oz,a)”));


val Lez_Oz_Addz_Lez = prove_store("Lez_Oz_Addz_Lez",
e0
(casez_tac >> rw[Oz_def,Lez_Asz,Addz_Asz,Add_clauses] >>
 rpt gen_tac >> disch_tac >> casez_tac >> rw[Addz_Asz,Lez_Asz] >>
 rpt strip_tac >> rw[GSYM Add_assoc] >> 
 once_rw[Add_Rarr] >> 
 qsspecl_then [‘a'’,‘b'’] assume_tac Add_comm >> arw[] >>
 arw[LESS_EQ_MONO_ADD_EQ])
(form_goal “!b.Lez(b,Oz) ==> !a.Lez(Addz(a,b),a)”));



val Lez_Ltz_TRANS_Ltz = prove_store("Lez_Ltz_TRANS_Ltz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Lez_Asz] >> rpt gen_tac >> disch_tac >> casez_tac >>
 rw[Ltz_Asz] >> rpt strip_tac >>
 qsspecl_then [‘Add(a, b')’,‘Add(b, a')’,‘Add(a', b'')’,‘Add(b', a'')’] 
 assume_tac Le_Lt_Lt_MONO_Add2 >> rfs[] >> 
 qsuff_tac
 ‘Add(Add(a, b'), Add(a', b'')) = Add(Add(a, b''),Add(a', b')) &
  Add(Add(b, a'), Add(b', a'')) = Add(Add(b, a''),Add(a', b'))’
 >-- (strip_tac >> fs[GSYM LESS_MONO_ADD]) >>
 strip_tac (* 2 *) 
 >-- (qsspecl_then [‘Add(a',b')’,‘Add(a,b'')’] assume_tac Add_comm >> arw[] >>
     rw[GSYM Add_assoc] >>
     qsspecl_then [‘a’,‘b'’,‘a'’,‘b''’] assume_tac Add_split_middle >>
     arw[] >> 
     qsspecl_then [‘ Add(Add(b', a'), b'')’,‘a’] assume_tac Add_comm >>
     arw[] >>
     qsspecl_then [‘a'’,‘b'’] assume_tac Add_comm >> arw[] >>
     qsspecl_then [‘b''’,‘a’] assume_tac Add_comm >> arw[] >>
     rw[GSYM Add_assoc]) >>
 rw[GSYM Add_assoc] >> once_rw[Add_comm] >>
 rw[EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘Add(a',b')’,‘a''’] assume_tac Add_comm >> 
 arw[GSYM Add_assoc])
(form_goal “!a b. Lez(a,b) ==> !c. Ltz(b,c) ==> Ltz(a,c)”));


val Ltz_trans = prove_store("Ltz_trans",
e0
(rpt strip_tac >> rev_drule Ltz_Lez >>
 drule Lez_Ltz_TRANS_Ltz >> first_x_assum drule >> arw[])
(form_goal “!a b. Ltz(a,b) ==> !c. Ltz(b,c) ==> Ltz(a,c)”));

(*similar for cases like option constructors, and i12, need a little tool for such theorems directly 

conv_rule (once_depth_fconv no_conv neg_fconv)  ?*)

val NOT_Ltz_Lez = prove_store("NOT_Ltz_Lez",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Lez_Asz,Ltz_Asz] >> rpt strip_tac  >>
 qsspecl_then [‘a'’,‘b’] assume_tac Add_comm >> 
 qsspecl_then [‘a’,‘b'’] assume_tac Add_comm >> arw[] >>
 rw[GSYM NOT_LESS_EQ])
(form_goal “!a b. ~Ltz(a,b) <=> Lez(b,a)”));

(*rearrange*)
val Addz_Rarr = prove_store("Addz_Rarr",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 strip_tac >> strip_tac >> casez_tac >> rw[Addz_Asz,Negz_Asz] >>
 rpt strip_tac >> rw[Asz_eq_ZR,ZR_def] >>
 qsuff_tac 
 ‘Add(Add(a, a'), b'') =  Add(a, Add(b'', a')) &
  Add(a'', Add(b, b')) = Add(Add(a'', b'), b)’ 
 >-- (strip_tac >> arw[]) >>
 rw[GSYM Add_assoc] >> once_rw[Add_comm] >>
 rw[EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘b'’,‘b’] assume_tac Add_comm >>
 qsspecl_then [‘b''’,‘a'’] assume_tac Add_comm >> arw[])
(form_goal “!a b c. Addz(a,b) = c <=> a = Addz(c,Negz(b))”));

(*Add_eq_eq*)
val Addz_eq_eq = prove_store("Addz_eq_eq",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 strip_tac >> strip_tac >> casez_tac >> 
 rw[Addz_Asz,Asz_eq_ZR,ZR_def] >> rpt strip_tac >>
 rw[GSYM Add_assoc] >> once_rw[Add_comm] >> rw[EQ_MONO_ADD_EQ] >>
 once_rw[Add_comm] >> rw[GSYM Add_assoc] >> 
 once_rw[Add_comm] >> rw[EQ_MONO_ADD_EQ])
(form_goal “!a b c.Addz(a,b) = Addz(a,c) <=> b = c”))

val Negz_Addz = prove_store("Negz_Addz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >> 
 rw[Negz_Asz,Addz_Asz])
(form_goal “!a b. Negz(Addz(a,b)) = Addz(Negz(a),Negz(b))”));


val Lez_refl = LEz_Refl |> rewr_rule[Refl_def] 
                        |> rewr_rule[LEz_def]

val Lez_cases = prove_store("Lez_cases",
e0
(rw[Ltz_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (qcases ‘a = b’ >> arw[]) >>
 rw[Lez_refl])
(form_goal “!a b. Lez(a,b) <=> Ltz(a,b) | a = b”));


val Lez_REFL = prove_store("Lez_REFL",
e0
(casez_tac >> rw[Lez_Asz] >> rpt strip_tac >>
 qsspecl_then [‘a’,‘b’] assume_tac Add_comm >> 
 arw[Le_refl] )
(form_goal “!z. Lez(z,z)”));

val Oz_Lez_int1 = prove_store("Oz_Lez_int1",
e0
(rw[Oz_def,int1_Asz,Lez_Asz,Add_clauses,O_LESS_EQ])
(form_goal “Lez(Oz,int1)”));


val Oz_Ltz_int1 = prove_store("Oz_Ltz_int1",
e0
(rw[Oz_def,int1_Asz,Ltz_Asz,Add_clauses,LESS_O])
(form_goal “Ltz(Oz,int1)”));



val Ltz_Negz = prove_store("Ltz_Negz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Negz_Asz,Ltz_Asz] >> rpt strip_tac >>
 qsspecl_then [‘b’,‘a'’] assume_tac Add_comm >>
 qsspecl_then [‘a’,‘b'’] assume_tac Add_comm >> arw[])
(form_goal “!a b.Ltz(Negz(a),Negz(b)) <=> Ltz(b,a)”));
 
val NEQ_Ltz = prove_store("NEQ_Ltz",
e0
(rw[Ltz_def,Ltz_def] >> rpt strip_tac >>
 qsspecl_then [‘a’,‘b’] assume_tac Lez_dichotomy >>
 pop_assum strip_assume_tac >> arw[] (* 2 *)
 >-- (dimp_tac >> strip_tac >> arw[] >> ccontra_tac >> fs[]) >>
 dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (disj2_tac >> ccontra_tac >> fs[]) >>
 ccontra_tac >> fs[] )
(form_goal 
 “!a b. ~(a = b) <=> Ltz(a,b) | Ltz(b,a)”));

val Ltz_iff_Lez_int1  = prove_store("Ltz_iff_Lez_int1",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[int1_Asz,Ltz_Asz,Lez_Asz,Addz_Asz,Add_clauses] >> 
 rw[Lt_Le_Suc])
(form_goal “!a b. Ltz(a,b) <=> Lez(Addz(a,int1),b)”));


val Negz_Mulz_Negz = prove_store("Negz_Mulz_Negz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Mulz_Asz,Negz_Asz] >> rpt strip_tac >>
 qsspecl_then [‘Mul(a,a')’,‘Mul(b,b')’] assume_tac Add_comm >> arw[] >>
 qsspecl_then [‘Mul(b,a')’,‘Mul(a,b')’] assume_tac Add_comm >> arw[])
(form_goal “!a b. Mulz(Negz(a),b) = Mulz(a,Negz(b))”));



val Oz_Addz = prove_store("Oz_Addz",
e0
(casez_tac >> rw[Oz_def,Addz_Asz,Add_clauses])
(form_goal “!z.Addz(Oz,z) = z”));



val Addz_eq_eq' = prove_store("Addz_eq_eq'",
e0
(once_rw[Addz_comm] >> rw[Addz_eq_eq])
(form_goal 
“!a b c.Addz(a,c) = Addz(b,c) <=> a = b”));

(*
(*MULT_MONO_EQ*)
val Mulz_eq_eq = prove_store("Mulz_eq_eq",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 strip_tac >> strip_tac >> casez_tac >> rw[Mulz_Asz,Oz_def] >>
 rw[Asz_eq_ZR,ZR_def,Add_clauses] >> 
 rpt strip_tac >>
 once_rw[Add_Add_Rarr] >> rw[GSYM LEFT_DISTR] >>
 qsspecl_then [‘a''’,‘b'’] assume_tac Add_comm >>
 qsspecl_then [‘a'’,‘b''’] assume_tac Add_comm >> arw[] >>
 qsspecl_then [‘Mul(b, Add(a'', b'))’,‘Mul(a, Add(a', b''))’]
 assume_tac Add_comm >>
 arw[] >> need to fix(*not used but good to have*)
 )
(form_goal 
“!a b c.~(a = Oz) ==> 
 (Mulz(a,b) = Mulz(a,c) <=> b = c)”));
*)

(*


val Mulz_eq_eq' = prove_store("Mulz_eq_eq'",
e0
(once_rw[Mulz_comm] >> rw[Mulz_eq_eq])
(form_goal 
“!a b c.~(c = Oz) ==>
 (Mulz(a,c) = Mulz(b,c) <=> a = b)”));
*)
 
val between_int1_Oz = prove_store("between_int1_Oz",
e0
(casez_tac >> 
 rw[int1_Asz,Oz_def,Ltz_Asz,
    Negz_Asz,Asz_eq_ZR,ZR_def,Add_clauses,Lt_Suc_Le,Le_Le_iff_eq] >>
 rpt strip_tac >> rflip_tac >> rw[])
(form_goal “!z.Ltz(Negz(int1),z) & Ltz(z,int1) <=> z = Oz”));

val Addz_Negz_Oz_eq = prove_store("Addz_Negz_Oz_eq",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Oz_def,Addz_Asz,Negz_Asz,Asz_eq_ZR,ZR_def,Add_clauses] >>
 rpt strip_tac >>
 qsspecl_then [‘b’,‘a'’] assume_tac Add_comm >> arw[] )
(form_goal “!z1 z2.Addz(z1,Negz(z2)) = Oz <=> z1 = z2”));

(*
(*aa' + bb' + ab'' + ba'' < ab' + ba' + aa'' + bb'' <=> 
 a' + b'' < b' + a'' *)
val Mulz_Ltz_Ltz = prove_store("Mulz_Ltz_Ltz",
e0
(casez_tac >> rw[Oz_def,Ltz_Asz,Add_clauses] >> rpt gen_tac >> disch_tac >>
 casez_tac >> strip_tac >> strip_tac >> casez_tac >> 
 rw[Mulz_Asz,Ltz_Asz] >> rpt strip_tac >> 
 drule Mulz_Ltz_Ltz_lemma >> arw[])
(form_goal 
 “!a. Ltz(Oz,a) ==> 
      !b c. (Ltz(Mulz(a,b),Mulz(a,c)) <=> Ltz(b,c))”));

*)

val Negz_Negz = prove_store("Negz_Negz",
e0
(casez_tac >> rw[Negz_Asz])
(form_goal “!z. Negz(Negz(z)) = z”));


val Ltz_iff_O_Ltz_Sub = prove_store("Ltz_iff_O_Ltz_Sub",
e0
(rpt strip_tac >>
 qsspecl_then [‘Addz(b,Negz(a))’,‘Oz’] assume_tac Ltz_Negz >>
 fs[Negz_Addz,Negz_Negz,Negz_Oz] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 once_rw[Addz_comm] >> rw[GSYM Ltz_Addz_Negz])
(form_goal “!a b. Ltz(a,b) <=> Ltz(Oz,Addz(b,Negz(a)))”));


val Ltz_Ltz_Mulz_Ltz = prove_store("Ltz_Ltz_Mulz_Ltz",
e0
(casez_tac >> rpt gen_tac >> strip_tac >> casez_tac >>  
 fs[Oz_def,Ltz_Asz,Mulz_Asz,Add_clauses] >>
 rpt strip_tac >> ccontra_tac >>
 fs[NOT_LESS] >>
 qby_tac ‘Le(Mul(a',Sub(a,b)),Mul(b',Sub(a,b)))’ >-- 
 (irule Le_MONO_Mul >> arw[]) >>
 fs[LEFT_SUB_DISTR] >>
 qsspecl_then [‘Sub(Mul(a', a), Mul(a', b))’,
               ‘Sub(Mul(b', a), Mul(b', b))’,
               ‘Mul(b,Add(a',b'))’] assume_tac LESS_EQ_MONO_ADD_EQ >>
 first_x_assum (drule o iffRL) >>
 drule $ iffRL NOT_LESS_EQ >>
 qsuff_tac
 ‘Add(Sub(Mul(a', a), Mul(a', b)), Mul(b, Add(a', b'))) =
 Add(Mul(a, a'), Mul(b, b')) &
  Add(Sub(Mul(b', a), Mul(b', b)), Mul(b, Add(a', b'))) = 
 Add(Mul(a, b'), Mul(b, a'))’
 >-- (rpt strip_tac >> fs[]) >>
 once_rw[LEFT_DISTR] >> 
 qby_tac
 ‘Le(Mul(b', b),Mul(b',a))’ 
 >-- (once_rw[Mul_comm] >> irule Le_MONO_Mul >> irule Lt_Le >> arw[]) >>
 drule SUB_ADD >>
 qsspecl_then [‘Mul(b,b')’,‘Mul(b,a')’] assume_tac Add_comm >>
 arw[] >> rw[Add_assoc] >> arw[] >>
 qsspecl_then [‘b'’,‘b’] assume_tac Mul_comm >> fs[] >>
 qsspecl_then [‘b'’,‘a’] assume_tac Mul_comm >> arw[] >> 
 qby_tac 
 ‘Le(Mul(a', b),Mul(a',a))’
 >-- (once_rw[Mul_comm] >> irule Le_MONO_Mul >> irule Lt_Le >> arw[]) >>
 drule SUB_ADD >> 
 rw[GSYM Add_assoc] >>
 qpick_x_assum ‘Add(Mul(b, a'), Mul(b, b')) = Add(Mul(b, b'), Mul(b, a'))’
 (assume_tac o GSYM) >> arw[] >>
 qspecl_then [‘a'’,‘b’] assume_tac Mul_comm >> arw[] >>
 rw[Add_assoc] >> fs[] >>
 qspecl_then [‘a'’,‘a’] assume_tac Mul_comm >> arw[])
(form_goal “!a. Ltz(Oz,a) ==> !b. Ltz(Oz,Mulz(a,b)) ==> Ltz(Oz,b) ”));



val Ltz_Ltz_Mulz_pos = prove_store("Ltz_Ltz_Mulz_pos",
e0
(casez_tac >> rpt gen_tac >> strip_tac >> casez_tac >>  
 fs[Oz_def,Ltz_Asz,Mulz_Asz,Add_clauses] >>
 rpt strip_tac >>
 rev_drule Lt_cross_lemma >> first_x_assum drule  >>
 once_rw[Add_comm] >> arw[])
(form_goal “!a. Ltz(Oz,a) ==> !b. Ltz(Oz,b) ==> Ltz(Oz,Mulz(a,b)) ”));

(*aa' + bb' + ab'' + ba'' < ab' + ba' + aa'' + bb'' <=> 
 a' + b'' < b' + a'' *)
val Mulz_Ltz_Ltz = prove_store("Mulz_Ltz_Ltz",
e0
(rpt strip_tac >>
 once_rw[Ltz_iff_O_Ltz_Sub] >> dimp_tac (* 2 *)
>-- (rw[GSYM Negz_Mulz] >> rw[Negz_Mulz_Negz] >>
 rw[GSYM LDISTR_Z] >> rpt strip_tac >>
 rev_drule Ltz_Ltz_Mulz_Ltz >> first_x_assum irule >> arw[]) >>
 rpt strip_tac >> rev_drule Ltz_Ltz_Mulz_pos >>
 rw[GSYM Negz_Mulz] >> rw[Negz_Mulz_Negz] >>
 rw[GSYM LDISTR_Z] >> first_x_assum irule >> arw[])
(form_goal 
 “!a. Ltz(Oz,a) ==> 
      !b c. (Ltz(Mulz(a,b),Mulz(a,c)) <=> Ltz(b,c))”));





val Ltz_Oz_Lez_int1 = prove_store("Ltz_Oz_Lez_int1",
e0
(casez_tac >> rw[Oz_def,int1_Asz,Ltz_Asz,Lez_Asz,Add_clauses] >>
 rw[Lt_Le_Suc])
(form_goal “!z.Ltz(Oz,z) <=> Lez(int1,z)”));

(*have tool distinguish once from top and from depth*)

val Addz_Rarr_both_sides =  prove_store("Addz_Rarr_both_sides",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 strip_tac >> strip_tac >> casez_tac >> 
 strip_tac >> strip_tac >> casez_tac >> 
 rw[Addz_Asz,Negz_Asz,Asz_eq_ZR,ZR_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (flip_tac >> rw[GSYM Add_assoc] >> 
     rw[Add_last_middle_split] >> arw[] >>
     qsspecl_then [‘a''’,‘a'''’] assume_tac Add_comm >> arw[] >>
     qsspecl_then [‘b’,‘b'’] assume_tac Add_comm >> arw[]) >>
 flip_tac >> once_rw[Add_Add_Rarr] >>
 once_rw[Add_comm] >>
 qsspecl_then [‘b’,‘a''’] assume_tac Add_comm >> arw[] >>
 qsspecl_then [‘b'''’,‘a'’] assume_tac Add_comm >> arw[] >>
 qsspecl_then [‘Add(b''', a')’,‘Add(a, b'')’] accept_tac Add_comm)
(form_goal “!a b c d. 
 Addz(a,b) = Addz(c,d) <=> Addz(d,Negz(b)) = Addz(a,Negz(c))”));


 
val Lez_Ltz_Addz_Ltz = prove_store("Lez_Ltz_Addz_Ltz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >> 
 rpt gen_tac >> disch_tac >> 
 casez_tac >> strip_tac >> strip_tac >> casez_tac >> 
 rw[Ltz_Asz,Addz_Asz] >> rpt strip_tac >>  
 fs[Lez_Asz] >> 
 once_rw[Add_Add_Rarr] >>
 qabbrev_tac ‘Add(a, b') = x1’ >>
 qabbrev_tac ‘Add(b, a') = x2’ >>
 qabbrev_tac ‘Add(a'', b''') = x3’ >>
 qabbrev_tac ‘Add(b'', a''') = x4’ >> fs[] >>
 irule Le_Lt_Lt_MONO_Add2 >> arw[])
(form_goal “!a b. Lez(a,b) ==> !c d. Ltz(c,d) ==>
 Ltz(Addz(a,c),Addz(b,d))”));


val Mulz_Negz_Negz = prove_store("Mulz_Negz_Negz",
e0
(casez_tac >> strip_tac >> strip_tac >> casez_tac >>
 rw[Negz_Asz,Mulz_Asz] >> rpt strip_tac >> 
 fconv_tac 
 (rand_fconv
  (once_depth_conv (rewr_conv (spec_all Add_comm))) no_fconv) >>
 rw[])
(form_goal “!a b. Mulz(Negz(a),Negz(b)) = Mulz(a,b)”));

val Lez_asym = LEz_Asym |> rewr_rule[Asym_def,LEz_def]
 
val Ltz_NOT_Ltz = prove_store("Ltz_NOT_Ltz",
e0
(rpt strip_tac >> ccontra_tac >>
 drule Ltz_trans >> first_x_assum drule >>
 fs[Ltz_def])
(form_goal “!a b. Ltz(a,b) ==> ~Ltz(b,a)”));


val Abv_Negz = prove_store("Abv_Negz",
e0
(rpt strip_tac >> irule $ iffLR Inj_eq_eq >>
 qexistsl_tac [‘Z’,‘N2Z’] >> rw[N2Z_Inj] >>
 rw[N2Z_def] >>
 qcases ‘Lez(Oz,z)’ (* 2 *)
 >-- (qsspecl_then [‘z’] assume_tac Abv_def >> fs[GSYM NOT_Lez_Ltz] >>
     qsspecl_then [‘Negz(z)’] assume_tac Abv_def >>
     fs[GSYM NOT_Lez_Ltz] (* 2 *)
     >-- (qsuff_tac ‘z = Oz’ >-- (strip_tac >> arw[Negz_Oz]) >>
         drule $ iffRL Lez_Negz >> fs[Negz_Oz,Negz_Negz] >>
         irule Lez_asym >> arw[]) >>
     qby_tac ‘Negz(Asz(O, Abv(Negz(z)))) = Negz(Negz(z))’ 
     >-- arw[] >>
     fs[Negz_Asz,Negz_Negz]) >>
 fs[NOT_Lez_Ltz] >>
 qsspecl_then [‘z’] assume_tac Abv_def >> fs[GSYM NOT_Lez_Ltz] >> 
 fs[NOT_Lez_Ltz] >>
 drule $ iffRL Ltz_Negz >> fs[Negz_Oz] >>
 qsspecl_then [‘Negz(z)’] assume_tac Abv_def >> 
 drule $ Ltz_Lez >> 
 drule Ltz_NOT_Ltz >> fs[] >> 
 irule $ iffLR Negz_eq_eq >> arw[Negz_Asz,Negz_Negz])
(form_goal “!z. Abv(Negz(z)) = Abv(z)”));

val Abv_Oz = prove_store("Abv_Oz",
e0
(qsspecl_then [‘Oz’] assume_tac Abv_def >>
 fs[Ltz_def] >>
 qby_tac ‘Asz(Abv(Oz), O) = Asz(O,O)’ >-- arw[GSYM Oz_def] >>
 fs[Asz_eq_eq_l])
(form_goal “Abv(Oz) = O”));

val n2z_Abv_Negz = prove_store("n2z_Abv_Negz",
e0
(rpt strip_tac >>
 qcases ‘z = Oz’ 
 >-- (arw[Abv_Oz,n2z_def,N2Z_def,Negz_Oz] >> rw[Oz_def]) >>
 fs[GSYM NOT_Ltz_Lez] >> 
 rw[n2z_def,N2Z_def] >> 
 qsspecl_then [‘z’] assume_tac Abv_def >> fs[] (* 2 *)
 >-- (fs[NOT_Ltz_Lez] >> qsuff_tac ‘z = Oz’ >-- (strip_tac >> fs[]) >>
     irule Lez_asym >> arw[]) >>
 irule $ iffLR Negz_eq_eq >> arw[Negz_Asz,Negz_Negz])
(form_goal “!z.Lez(z,Oz) ==> n2z(Abv(z)) = Negz(z)”));


val n2z_is_Abv = prove_store("n2z_is_Abv",
e0
(rpt strip_tac >>
 irule $ iffLR Inj_eq_eq >>
 qexistsl_tac [‘Z’,‘N2Z’] >> rw[N2Z_Inj] >>
 rw[N2Z_def] >> 
 qby_tac ‘Lez(Oz,z)’
 >-- (pop_assum (assume_tac o GSYM) >> arw[n2z_Oz_Lez]) >>
 drule n2z_Abv >> fs[n2z_def,N2Z_def])
(form_goal “!n z. n2z(n) = z ==> n = Abv(z)”));

val Le_Abv_Abv = prove_store("Le_Abv_Abv",
e0
(rpt strip_tac >> 
 drule Abv_nonneg >> rev_drule Abv_nonneg >>
 qsuff_tac
 ‘Le(Abv(a), Abv(b)) <=> Lez(Asz(Abv(a), O), Asz(Abv(b), O))’
 >-- arw[] >>
 rw[Lez_Asz,Add_clauses])
(form_goal “!a b.Lez(Oz,a) & Lez(Oz,b) ==>
 (Le(Abv(a), Abv(b)) <=> Lez(a,b))”));


val division_theorem_ex0 = prove_store("division_theorem_ex0",
e0
(rpt strip_tac >> x_choosel_then ["s"] strip_assume_tac
 (IN_def_P_ex |> qspecl [‘N’] |> GSYM
 |> fVar_sInst_th “P(n:mem(N))”
    “?k. n2z(n) = Addz(a,Negz(Mulz(k,d)))” ) >>
 qby_tac ‘~(s = Empty(N))’ 
 >-- (rw[GSYM IN_NONEMPTY] >> 
     qcases ‘Lez(Oz,a)’ (* 2 *)
     >-- (arw[] >> qexistsl_tac [‘Abv(a)’,‘Oz’] >>
         drule n2z_Abv >> arw[] >> 
         rw[Oz_Mulz,Negz_Oz,Addz_Oz]) >> 
     arw[] >> 
     qby_tac ‘Ltz(Oz,Addz(a, Negz(Mulz(a, d))))’
     >-- (qby_tac ‘Addz(a, Negz(Mulz(a, d))) = Mulz(a,Addz(int1,Negz(d)))’
          >-- rw[GSYM Mulz_Negz,LDISTR_Z,Mulz_int1] >> arw[] >> 
          irule Oz_Ltz_Mulz >> fs[NOT_Lez_Ltz] >> 
          arw[GSYM Ltz_Addz_Negz]) >>
     qexistsl_tac [‘Abv(Addz(a, Negz(Mulz(a, d))))’,‘a’] >>
     drule Ltz_Lez >> drule n2z_Abv >> arw[]) >>
 drule WOP'     >>
 pop_assum strip_assume_tac >>
 rfs[] >> qexistsl_tac [‘k’,‘Addz(a, Negz(Mulz(k, d)))’] >> 
 qby_tac ‘Lez(Oz, Addz(a, Negz(Mulz(k, d))))’ 
 >-- (qpick_x_assum ‘n2z(a0) = Addz(a, Negz(Mulz(k, d)))’ 
      (assume_tac o GSYM) >> arw[n2z_Oz_Lez]) >>
 arw[] >> once_rw[Addz_comm] >> rw[Addz_assoc,Negz_Addz_Oz,Addz_Oz] >>
 rw[] >> once_rw[Addz_comm] >> ccontra_tac >>  
 qabbrev_tac ‘Addz(a, Negz(Mulz(k, d))) = r’ >>  
 fs[] >>
 fs[GSYM NOT_Lez_Ltz] >>
 qby_tac ‘Ltz(Oz,d)’ 
 >-- (fs[NOT_Lez_Ltz] >> 
      irule Ltz_trans >> qexists_tac ‘int1’ >> arw[] >>
      rw[Oz_Ltz_int1]) >>
 drule n2z_Abv >> fs[] >>  
 drule $ iffLR Ltz_def >> pop_assum strip_assume_tac >>
 drule n2z_Abv >> fs[] >>
 qpick_x_assum ‘Lez(d, r)’ assume_tac >> 
 drule Lez_Addz_ex >> 
 pop_assum (x_choosel_then ["r'"] strip_assume_tac) >> 
 qby_tac ‘Ltz(r',r)’ 
 >-- (pop_assum (mp_tac o GSYM) >> once_rw[Addz_comm] >> strip_tac >> 
     arw[] >> irule Oz_Ltz_Addz >> arw[]) >>
 first_x_assum (qspecl_then [‘Abv(r')’] assume_tac) >>
 qby_tac ‘a0 = Abv(r)’
 >-- (irule n2z_is_Abv >> arw[]) >> fs[] >>
 qsspecl_then [‘r’,‘r'’] assume_tac Le_Abv_Abv >>
 rfs[] >> fs[] >> drule $ iffRL NOT_Lez_Ltz >>
 drule n2z_Abv >> fs[] >>
 qsuff_tac ‘r' = Addz(a,Negz(Mulz(Addz(k,int1),d)))’ 
 >-- (strip_tac >> 
      qby_tac ‘?k. r' = Addz(a, Negz(Mulz(k, d)))’ 
      >-- (qexists_tac ‘Addz(k,int1)’ >> arw[]) >>
      rfs[]) >> 
 drule $ iffLR Addz_Rarr >> arw[] >>
 qpick_x_assum ‘Addz(a, Negz(Mulz(k, d))) = r’
 (assume_tac o GSYM) >>
 arw[] >> rw[Addz_assoc,Addz_eq_eq,RDISTR_Z] >>
 rw[GSYM Negz_Addz,Negz_eq_eq,Addz_eq_eq] >> 
 once_rw[Mulz_comm] >> rw[Mulz_int1])
(form_goal 
“!a d:mem(Z). Ltz(int1,d) ==>
  ?q r. a = Addz(Mulz(q,d),r) & 
  Lez(Oz,r) & Ltz(r,n2z(Abv(d)))”));


val division_theorem_ex1 = prove_store("division_theorem_ex1",
e0
(rpt strip_tac >> drule $ iffLR Lez_cases >> 
 pop_assum strip_assume_tac
 >-- (drule division_theorem_ex0 >> arw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 qexistsl_tac [‘a’,‘Oz’] >> rw[Mulz_int1,Addz_Oz,Lez_REFL] >>
 assume_tac Oz_Lez_int1 >> drule n2z_Abv >> arw[] >>
 rw[Oz_Ltz_int1])
(form_goal 
“!a d:mem(Z). Lez(int1,d) ==>
  ?q r. a = Addz(Mulz(q,d),r) & 
  Lez(Oz,r) & Ltz(r,n2z(Abv(d)))”));



val Lez_trans = LEz_Trans |> rewr_rule[Trans_def,LEz_def] 


val division_theorem_ex = prove_store("division_theorem_ex",
e0
(rpt strip_tac >> fs[NEQ_Ltz] 
 >-- (fs[Ltz_iff_Lez_int1] >>
     qby_tac ‘Lez(d,Negz(int1))’ 
     >-- (drule Lez_Addz >> 
         first_x_assum (qsspecl_then [‘Negz(int1)’] assume_tac) >>
         fs[Oz_Addz,Addz_assoc,Addz_Negz_Oz,Addz_Oz]) >>
     qby_tac ‘Lez(int1,Negz(d))’ 
     >-- (once_rw[GSYM Lez_Negz] >> arw[Negz_Negz]) >>
     drule division_theorem_ex1 >> 
     pop_assum strip_assume_tac >>
     qexistsl_tac [‘Negz(q)’,‘r’] >> arw[Negz_Mulz_Negz] >>
     qby_tac ‘Lez(d,Oz)’
     >-- (irule Lez_trans >> qexists_tac ‘Negz(int1)’ >>
         arw[] >> once_rw[GSYM Lez_Negz] >> rw[Negz_Oz,Negz_Negz] >>
         rw[Oz_Lez_int1]) >>
     qby_tac ‘Lez(Oz,Negz(d))’ 
     >-- (once_rw[GSYM Lez_Negz] >> arw[Negz_Negz,Negz_Oz])>>
     drule n2z_Abv_Negz >> arw[] >>
     qby_tac ‘n2z(Abv(Negz(d))) = Negz(d)’ 
     >-- (irule n2z_Abv >> arw[]) >>
     fs[] >> arw[GSYM Ltz_iff_Lez_int1]) >>
 fs[Ltz_iff_Lez_int1,Oz_Addz] >> 
 drule division_theorem_ex1 >> arw[GSYM Ltz_iff_Lez_int1])
(form_goal 
“!d:mem(Z). ~(d = Oz) ==>
  !a.?q r. a = Addz(Mulz(q,d),r) & 
  Lez(Oz,r) & Ltz(r,n2z(Abv(d)))”));

val division_theorem_unique0 = prove_store
("division_theorem_unique0",
e0
(rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 qsuff_tac ‘q1 = q2’ 
 >-- (rpt strip_tac >> arw[] >> 
      fs[Addz_eq_eq]) >>
 flip_tac >>
 irule $ iffLR Addz_Negz_Oz_eq >> irule $ iffLR between_int1_Oz >>
 qsuff_tac 
 ‘Ltz(Mulz(d,Negz(int1)),Mulz(d, Addz(q2, Negz(q1)))) & 
  Ltz(Mulz(d,Addz(q2, Negz(q1))),Mulz(d,int1))’ 
 >-- (fs[GSYM Ltz_Oz_Lez_int1] >> 
     drule Mulz_Ltz_Ltz >> arw[]) >>
 drule $ iffRL Ltz_Oz_Lez_int1 >> drule $ iffLR Ltz_def >>
 pop_assum strip_assume_tac >>
 drule n2z_Abv >> fs[] >>
 rw[Mulz_int1,Mulz_Negz] >> 
 qby_tac ‘Addz(r1,Negz(r2)) = Addz(Mulz(q2, d),Negz(Mulz(q1,d))) ’
 >-- (rw[GSYM Addz_Rarr_both_sides] >> arw[]) >>
 qby_tac ‘Ltz(Negz(d),Negz(r2))’ 
 >-- arw[Ltz_Negz] >> 
 fs[GSYM RDISTR_Z,GSYM Negz_Mulz] >> once_rw[Mulz_comm] >>
 qpick_x_assum 
 ‘Addz(r1, Negz(r2)) = Mulz(Addz(q2, Negz(q1)), d)’
 (assume_tac o GSYM) >> arw[] >>
 qsuff_tac
 ‘Ltz(Addz(Oz,Negz(d)), Addz(r1, Negz(r2))) & 
  Ltz(Addz(r1, Negz(r2)), Addz(d,Oz))’
 >-- rw[Oz_Addz,Addz_Oz] >> 
 strip_tac (* 2 *)
 >-- (irule Lez_Ltz_Addz_Ltz >> arw[Ltz_Negz]) >>
 once_rw[Addz_comm] >>
 irule Lez_Ltz_Addz_Ltz >> arw[] >>
 once_rw[GSYM Negz_Oz] >> arw[Lez_Negz])
(form_goal 
 “!a d:mem(Z). 
  Lez(int1,d) ==>
  !q1 r1 q2 r2. 
  a = Addz(Mulz(q1,d),r1) & 
  Lez(Oz,r1) & Ltz(r1,n2z(Abv(d))) & 
  a = Addz(Mulz(q2,d),r2) & 
  Lez(Oz,r2) & Ltz(r2,n2z(Abv(d))) ==>
  q1 = q2 & r1 = r2”));


val division_theorem_unique1 = prove_store
("division_theorem_unique1",
e0
(rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 drule $ iffLR NEQ_Ltz >>
 pop_assum strip_assume_tac (* 2 *)
 >-- (qby_tac ‘Lez(int1,Negz(d))’ 
      >-- (qsspecl_then [‘Oz’,‘Negz(d)’] assume_tac Ltz_iff_Lez_int1 >>
          fs[Oz_Addz] >>
          first_x_assum (irule o iffLR) >> 
          once_rw[GSYM Ltz_Negz] >> arw[Negz_Oz,Negz_Negz]) >>
     drule division_theorem_unique0 >>
     first_x_assum 
     (qspecl_then [‘Negz(q1)’,‘r1’,‘Negz(q2)’,‘r2’] strip_assume_tac) >>
     qsuff_tac ‘Negz(q1) = Negz(q2) & r1 = r2’ 
     >-- (rw[Negz_eq_eq] >> strip_tac >> arw[]) >>
     first_x_assum irule >> arw[Mulz_Negz_Negz] >>
     qpick_x_assum ‘a = Addz(Mulz(q2, d), r2)’ 
     (assume_tac o GSYM) >> arw[] >>
     arw[Abv_Negz]) >>
 qby_tac ‘Lez(int1,d)’ 
 >-- (qsspecl_then [‘Oz’,‘d’] assume_tac Ltz_iff_Lez_int1 >>
     fs[Oz_Addz]) >>
 drule division_theorem_unique0 >>
 qsuff_tac ‘q1 = q2 & r1 = r2’ 
 >-- (strip_tac >> arw[]) >>
 first_x_assum irule >> arw[] >>
 fs[]) 
(form_goal 
 “!a d:mem(Z). 
  ~(d = Oz) ==>
  !q1 r1 q2 r2. 
  a = Addz(Mulz(q1,d),r1) & 
  Lez(Oz,r1) & Ltz(r1,n2z(Abv(d))) & 
  a = Addz(Mulz(q2,d),r2) & 
  Lez(Oz,r2) & Ltz(r2,n2z(Abv(d))) ==>
  q1 = q2 & r1 = r2”));



val division_theorem = prove_store("division_theorem",
e0
(rpt strip_tac >>
 uex_tac >> fconv_tac exists_cross_fconv >> 
 rw[Pair_def'] >> 
 fconv_tac (redepth_fconv no_conv forall_cross_fconv) >>
 rw[Pair_def'] >>
 drule division_theorem_ex >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 qexistsl_tac [‘q’,‘r’] >>
 arw[] >> rpt strip_tac >>
 rw[Pair_eq_eq] >> drule division_theorem_unique1 >>
 first_x_assum irule >> arw[])
(form_goal 
“!a d:mem(Z).~(d = Oz) ==>
  ?!qr:mem(Z * Z). a = Addz(Mulz(Fst(qr),d),Snd(qr)) & 
  Lez(Oz,Snd(qr)) & Ltz(Snd(qr),n2z(Abv(d)))”));



val DIVRz_def = 
P2fun_uex |> qspecl [‘Z*Z’,‘Z*Z’]  
          |> fVar_sInst_th “P(ad:mem(Z*Z),qr:mem(Z*Z))”
             “(Snd(ad) = Oz & qr = Pair(Oz,Oz)) |
  (~(Snd(ad) = Oz) &
   Fst(ad) = Addz(Mulz(Fst(qr),Snd(ad)),Snd(qr)) & 
   Lez(Oz,Snd(qr)) & Ltz(Snd(qr),n2z(Abv(Snd(ad)))))”
|> C mp
(proved_th $
e0
(rpt strip_tac >>
 qsspecl_then [‘ad’] (x_choosel_then ["a","d"] assume_tac)
 Pair_has_comp >> arw[Pair_def'] >> 
 qcases ‘d = Oz’ >> arw[] (* 2 *) >--
 (uex_tac >> qexists_tac ‘Pair(Oz,Oz)’ >> 
 rw[] >> rpt strip_tac >> arw[]) >>
 drule division_theorem >> arw[] )
(form_goal
 “!ad.
  ?!qr:mem(Z * Z). 
  (Snd(ad) = Oz & qr = Pair(Oz,Oz)) |
  (~(Snd(ad) = Oz) &
   Fst(ad) = Addz(Mulz(Fst(qr),Snd(ad)),Snd(qr)) & 
   Lez(Oz,Snd(qr)) & Ltz(Snd(qr),n2z(Abv(Snd(ad))))) ”))
|> qsimple_uex_spec "DIVRz" [] 
 
val Divrz_def = qdefine_fsym("Divrz",[‘a:mem(Z)’,‘d:mem(Z)’])
‘App(DIVRz,Pair(a,d))’

val Divrz_property0 =
    DIVRz_def |> qspecl [‘Pair(a:mem(Z),d:mem(Z))’] 
              |> rewr_rule[Pair_def'] 
              |> rewr_rule[GSYM Divrz_def]
              |> gen_all
 
val Divrz_Oz = prove_store("Divrz_Oz",
e0
(rpt strip_tac >>
 qsspecl_then [‘a’,‘d’] assume_tac Divrz_property0 >>
 rfs[])
(form_goal 
 “(!d.d = Oz ==> !a.Divrz(a,d) = Pair(Oz,Oz))”));

val Divrz_NONZERO = prove_store("Divrz_NONZERO",
e0
(rpt strip_tac >>
 qsspecl_then [‘a’,‘d’] assume_tac (GSYM Divrz_property0) >>
 rfs[] >> fs[])
(form_goal 
 “!d.~(d = Oz) ==> 
    !a. Addz(Mulz(Fst(Divrz(a, d)), d), 
             Snd(Divrz(a, d))) = a  &
        Lez(Oz, Snd(Divrz(a, d))) & 
        Ltz(Snd(Divrz(a, d)), n2z(Abv(d)))”));


val Divz_def = qdefine_fsym("Divz",[‘a:mem(Z)’,‘d:mem(Z)’])
‘Fst(Divrz(a,d))’

val Remz_def = qdefine_fsym("Remz",[‘a:mem(Z)’,‘d:mem(Z)’])
‘Snd(Divrz(a,d))’

val Divz_Remz_NONZERO = 
    Divrz_NONZERO 
        |> rewr_rule[GSYM Divz_def,GSYM Remz_def] 

val Divz_Remz_Oz = prove_store("Divz_Remz_Oz",
e0
(strip_tac >>
 qsspecl_then [‘Oz’] assume_tac Divrz_Oz >> fs[] >>
 arw[Divz_def,Remz_def,Pair_def'] )
(form_goal
 “!a. Divz(a,Oz) = Oz & Remz(a,Oz) = Oz”));

(*
val Oz_Ltz_Mulz_iff = prove_store("Oz_Ltz_Mulz_iff",
e0
(cheat)
(form_goal
 “!a. Ltz(Oz,a) ==>
   !b. Ltz(Oz,Mulz(a,b)) <=> Ltz(Oz,b)”));
*)


(*
a = qd + r 

0< d, 0 <= r < d

then 0 <= q

if q > 0, then qd negtive, qd < 0, r = a + qd 

if a = 0, then r = qd, if r = O, then qd = O, since d <> 0, must have q = O, 

if a > 0, then r > qd



*)




(*
val division_theorem_ex0 = prove_store("division_theorem_ex0",
e0
(rpt strip_tac >> x_choosel_then ["s"] strip_assume_tac
 (IN_def_P_ex |> qspecl [‘N’] |> GSYM
 |> fVar_sInst_th “P(n:mem(N))”
    “?k. n2z(n) = Addz(a,Negz(Mulz(k,d)))” ) >>
 qby_tac ‘~(s = Empty(N))’ 
 >-- (rw[GSYM IN_NONEMPTY] >> 
     qcases ‘Lez(Oz,a)’ (* 2 *)
     >-- (arw[] >> qexistsl_tac [‘Abv(a)’,‘Oz’] >>
         drule n2z_Abv >> arw[] >> 
         rw[Oz_Mulz,Negz_Oz,Addz_Oz]) >> 
     arw[] >> 
     qby_tac ‘Ltz(Oz,Addz(a, Negz(Mulz(a, d))))’
     >-- (qby_tac ‘Addz(a, Negz(Mulz(a, d))) = Mulz(a,Addz(int1,Negz(d)))’
          >-- rw[GSYM Mulz_Negz,LDISTR_Z,Mulz_int1] >> arw[] >> 
          irule Oz_Ltz_Mulz >> fs[NOT_Lez_Ltz] >> 
          arw[GSYM Ltz_Addz_Negz]) >>
     qexistsl_tac [‘Abv(Addz(a, Negz(Mulz(a, d))))’,‘a’] >>
     drule Ltz_Lez >> drule n2z_Abv >> arw[]) >>
 drule WOP'     >>
 pop_assum strip_assume_tac >>
 rfs[] >> qexistsl_tac [‘k’,‘Addz(a, Negz(Mulz(k, d)))’] >> 
 qby_tac ‘Lez(Oz, Addz(a, Negz(Mulz(k, d))))’ 
 >-- (qpick_x_assum ‘n2z(a0) = Addz(a, Negz(Mulz(k, d)))’ 
      (assume_tac o GSYM) >> arw[n2z_Oz_Lez]) >>
 arw[] >> once_rw[Addz_comm] >> rw[Addz_assoc,Negz_Addz_Oz,Addz_Oz] >>
 rw[] >> once_rw[Addz_comm] >> 
 qby_tac ‘ Ltz(Addz(a, Negz(Mulz(k, d))), n2z(Abv(d)))’
 >-- (ccontra_tac >>  
 qabbrev_tac ‘Addz(a, Negz(Mulz(k, d))) = r’ >>  
 fs[] >>
 fs[GSYM NOT_Lez_Ltz] >>
 qby_tac ‘Ltz(Oz,d)’ 
 >-- (fs[NOT_Lez_Ltz] >> 
      irule Ltz_trans >> qexists_tac ‘int1’ >> arw[] >>
      rw[Oz_Ltz_int1]) >>
 drule n2z_Abv >> fs[] >>  
 drule $ iffLR Ltz_def >> pop_assum strip_assume_tac >>
 drule n2z_Abv >> fs[] >>
 qpick_x_assum ‘Lez(d, r)’ assume_tac >> 
 drule Lez_Addz_ex >> 
 pop_assum (x_choosel_then ["r'"] strip_assume_tac) >> 
 qby_tac ‘Ltz(r',r)’ 
 >-- (pop_assum (mp_tac o GSYM) >> once_rw[Addz_comm] >> strip_tac >> 
     arw[] >> irule Oz_Ltz_Addz >> arw[]) >>
 first_x_assum (qspecl_then [‘Abv(r')’] assume_tac) >>
 qby_tac ‘a0 = Abv(r)’
 >-- (irule n2z_is_Abv >> arw[]) >> fs[] >>
 qsspecl_then [‘r’,‘r'’] assume_tac Le_Abv_Abv >>
 rfs[] >> fs[] >> drule $ iffRL NOT_Lez_Ltz >>
 drule n2z_Abv >> fs[] >>
 qsuff_tac ‘r' = Addz(a,Negz(Mulz(Addz(k,int1),d)))’ 
 >-- (strip_tac >> 
      qby_tac ‘?k. r' = Addz(a, Negz(Mulz(k, d)))’ 
      >-- (qexists_tac ‘Addz(k,int1)’ >> arw[]) >>
      rfs[]) >> 
 drule $ iffLR Addz_Rarr >> arw[] >>
 qpick_x_assum ‘Addz(a, Negz(Mulz(k, d))) = r’
 (assume_tac o GSYM) >>
 arw[] >> rw[Addz_assoc,Addz_eq_eq,RDISTR_Z] >>
 rw[GSYM Negz_Addz,Negz_eq_eq,Addz_eq_eq] >> 
 once_rw[Mulz_comm] >> rw[Mulz_int1]) >> arw[] >>
 ccontra_tac >> )
(form_goal 
“!a d:mem(Z). Ltz(int1,d) ==>
  ?q r. a = Addz(Mulz(q,d),r) & 
  Lez(Oz,r) & Ltz(r,n2z(Abv(d)))&
  (Lez(Oz,a) ==> Lez(Oz,q))”));
*)

val Subz_def = qdefine_fsym("Subz",[‘a:mem(Z)’,‘b:mem(Z)’])
‘Addz(a,Negz(b))’
 
val Subz_Addz = prove_store("Subz_Addz",
e0
(rw[Subz_def] >> rw[Addz_assoc,Negz_Addz_Oz,Addz_Oz])
(form_goal “!m n.Addz(Subz(m,n),n) = m”));

val Mulz_Oz = prove_store("Mulz_Oz",
e0
(once_rw[Mulz_comm] >> rw[Oz_Mulz])
(form_goal “!z.Mulz(z,Oz) = Oz”));

val Oz_Ltz_Negz = prove_store("Oz_Ltz_Negz",
e0
(strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (drule $ iffRL Ltz_Negz >> fs[Negz_Oz]) >>
 irule $ iffLR Ltz_Negz >> arw[Negz_Oz])
(form_goal “!a. Ltz(Oz,a) <=> Ltz(Negz(a),Oz)”));


val Ltz_Oz_Negz = prove_store("Ltz_Oz_Negz",
e0
(once_rw[Oz_Ltz_Negz] >> rw[Negz_Negz])
(form_goal “!a. Ltz(a,Oz) <=> Ltz(Oz,Negz(a))”));


(*Mulz_Ltz_Ltz Oz_Ltz_Mulz*)
val Mulz_Ltz_Ltz_Oz = prove_store("Mulz_Ltz_Ltz_Oz",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 3 *)
 >-- (qcases ‘Ltz(Oz,a)’ 
     >-- (drule Mulz_Ltz_Ltz >>
         first_x_assum (qsspecl_then [‘b’,‘Oz’] assume_tac) >>
         fs[Mulz_Oz]) >>
     qby_tac ‘~(a = Oz)’ 
     >-- (ccontra_tac >> fs[Oz_Mulz,Ltz_def]) >>
     fs[NEQ_Ltz] >> fs[Ltz_Oz_Negz] >>
     drule Mulz_Ltz_Ltz >>
     first_x_assum (qspecl_then [‘Oz’,‘b’] assume_tac) >>
     fs[Mulz_Oz,Mulz_Negz] >> rfs[Negz_Mulz]) 
 >-- (drule Mulz_Ltz_Ltz >>
     first_x_assum (qsspecl_then [‘b’,‘Oz’] assume_tac) >> fs[Mulz_Oz]) >>
 drule Mulz_Ltz_Ltz >> once_rw[Mulz_comm] >>
 first_x_assum (qspecl_then [‘a’,‘Oz’] assume_tac) >> fs[Mulz_Oz])
(form_goal 
“!a b. Ltz(Mulz(a,b),Oz) <=> (Ltz(Oz,a) & Ltz(b,Oz)) |
 (Ltz(Oz,b) & Ltz(a,Oz)) ”));

val Mulz_Oz_iff_Oz = prove_store("Mulz_Oz_iff_Oz",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] (* 3 *)
 >-- (ccontra_tac >> fs[NEQ_Ltz,neg_or_distr] (* 4 *)
     >-- (qsspecl_then [‘a’,‘b’] assume_tac Oz_Ltz_Mulz >> rfs[Ltz_def]) 
     >-- (qsspecl_then [‘a’,‘b’] assume_tac Mulz_Ltz_Ltz_Oz >> rfs[Ltz_def])
     >-- (qsspecl_then [‘a’,‘b’] assume_tac Mulz_Ltz_Ltz_Oz >> rfs[Ltz_def]) >>
     rev_drule Ltz_Ltz_Mulz_pos >> first_x_assum drule >>
     fs[Ltz_def] >> rfs[])
 >-- rw[Oz_Mulz] >> rw[Mulz_Oz])
(form_goal “!a b.Mulz(a,b) = Oz <=> a = Oz | b = Oz”));

val division_theorem' = division_theorem |> strip_all_and_imp 
                                         |>  qgen ‘a’ |> disch_all
                                         |> gen_all

val Divz_Remz_unique = prove_store("Divz_Remz_unique",
e0
(strip_tac >> disch_tac >> drule division_theorem' >> 
 rpt gen_tac >> disch_tac >>
 first_x_assum (qsspecl_then [‘a’] (strip_assume_tac o uex_expand)) >> 
 qpick_x_assum ‘a = Addz(Mulz(Fst(qr), d), Snd(qr))’
 (assume_tac o GSYM) >> 
 drule Divz_Remz_NONZERO  >>
 first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
 fs[Pair_def'] >> 
 rw[GSYM Pair_eq_eq] >>
 qsuff_tac
 ‘Pair(q,r) = qr &  Pair(Divz(a, d), Remz(a, d)) = qr’ 
 >-- (rpt strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (first_x_assum irule >> arw[Pair_def']) >>
 first_x_assum irule >> arw[Pair_def']  )
(form_goal “!d. ~(d = Oz) ==>
 !a q r. Addz(Mulz(q,d),r) = a & Lez(Oz,r) & Ltz(r,n2z(Abv(d))) ==> q = Divz(a,d) & r = Remz(a,d)”));

val Ltz_Subz = prove_store("Ltz_Subz",
e0
(rw[Subz_def] >> once_rw[GSYM Ltz_Negz] >> rw[Negz_Oz] >> 
 rw[Negz_Addz] >> rw[Negz_Negz] >> once_rw[Addz_comm] >>
 once_rw[GSYM Ltz_Addz_Negz] >> rw[Ltz_Negz])
(form_goal “!a b. Ltz(a,b) <=> Ltz(Oz,Subz(b,a))”));

val Subz_Ltz = prove_store("Ltz_Subz",
e0
(rpt strip_tac >> once_rw[Ltz_Subz] >> rw[Subz_def] >>
 rw[Negz_Addz] >> rw[GSYM Addz_assoc] >> rw[Addz_Negz_Oz] >>
 rw[Oz_Addz,Negz_Negz] >> arw[])
(form_goal “!a. Ltz(Oz,a) ==> !b.Ltz(Subz(b,a),b)”));

val int1_Mulz = prove_store("int1_Mulz",
e0
(once_rw[Mulz_comm] >> rw[Mulz_int1])
(form_goal “!z. Mulz(int1,z) = z”));

val Addz_Subz_Rarr = prove_store("Addz_Subz_Rarr",
e0
(rw[Addz_assoc] >> rpt strip_tac >>  
 qsspecl_then [‘b’,‘Subz(c,b)’] assume_tac Addz_comm >> arw[] >>
 rw[Subz_Addz])
(form_goal “!a b c. Addz(Addz(a,b),Subz(c,b)) = Addz(a,c)”));


val Divz_pos_Remz = prove_store("Divz_pos_Remz",
e0
(rpt strip_tac >> 
 drule $ iffLR Ltz_def >> fs[] >>
 pop_assum (assume_tac o GSYM) >>
 drule Divz_Remz_NONZERO >> 
 first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >> 
 qsspecl_then [‘d’] assume_tac n2z_Abv >>
 rfs[] >> fs[])
(form_goal
 “!a d. Ltz(Oz,a) & Ltz(Oz,d) ==>
        Ltz(Remz(a,d),d)”));

val n2z_eq_eq = prove_store("n2z_eq_eq",
e0
(rpt strip_tac >> rw[n2z_def] >> irule Inj_eq_eq >> rw[N2Z_Inj])
(form_goal “!a b. n2z(a) = n2z(b) <=> a = b”));

val n2z_Asz = prove_store("n2z_Asz",
e0
(rw[n2z_def,N2Z_def])
(form_goal “!n. n2z(n) = Asz(n,O)”));

val n2z_Oz = prove_store("n2z_Oz",
e0
(rw[n2z_Asz,Oz_def])
(form_goal “n2z(O) = Oz”));

val Lez_n2z = prove_store("Lez_n2z",
e0
(rw[n2z_Asz,Lez_Asz,Add_clauses])
(form_goal “!a b. Lez(n2z(a),n2z(b)) <=> Le(a,b)”));


val Ltz_n2z = prove_store("Ltz_n2z",
e0
(rw[n2z_Asz,Ltz_Asz,Add_clauses])
(form_goal “!a b. Ltz(n2z(a),n2z(b)) <=> Lt(a,b)”));

val Oz_Lez_n2z = prove_store("Oz_Lez_n2z",
e0
(rw[GSYM n2z_Oz,Lez_n2z,O_LESS_EQ])
(form_goal “!n. Lez(Oz,n2z(n))”));

val Mulz_n2z = prove_store("Mulz_n2z",
e0
(rw[n2z_Asz,Mulz_Asz,Mul_clauses,Add_clauses])
(form_goal “!a b.Mulz(n2z(a),n2z(b)) = n2z(Mul(a,b))”));


val Addz_n2z = prove_store("Addz_n2z",
e0
(rw[n2z_Asz,Addz_Asz,Add_clauses])
(form_goal “!a b.Addz(n2z(a),n2z(b)) = n2z(Add(a,b))”));

val n2z_Oz_O = prove_store("n2z_Oz_O",
e0
(strip_tac >> dimp_tac >> strip_tac (*2*)
 >-- (irule $ iffLR n2z_eq_eq  >> fs[n2z_Oz]) >> arw[n2z_Oz])
(form_goal “!n. n2z(n) = Oz <=> n = O”));


val Le_num1_Lt_O = prove_store("Le_num1_Lt_O",
e0
(rw[num1_def,Lt_Le_Suc])
(form_goal “!a. Le(num1,a) <=> Lt(O,a)”));


val division_theorem_N_uex = prove_store("division_theorem_N_uex",
e0
(rpt strip_tac >>
 qby_tac ‘~(n2z(d) = Oz)’ 
 >-- (fs[Le_num1_Lt_O,Lt_def] >> ccontra_tac >> fs[n2z_Oz_O]) >>
 drule  division_theorem' >>
 first_x_assum (qsspecl_then [‘n2z(a)’] assume_tac) >>
 drule division_theorem_N_ex >> 
 pop_assum strip_assume_tac >> 
 uex_tac >> qexists_tac ‘Pair(q,r)’ >> rw[Pair_def'] >> arw[] >>
 first_x_assum (strip_assume_tac o uex_expand) >>
 forall_cross_tac >> rw[Pair_def'] >> rw[Pair_eq_eq] >>
 rw[GSYM n2z_eq_eq] >> rw[GSYM Pair_eq_eq] >> rw[n2z_eq_eq] >>
 rpt strip_tac >>
 qsuff_tac
 ‘Pair(n2z(a'), n2z(b)) = qr & Pair(n2z(q), n2z(r)) = qr’ 
 >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (first_x_assum irule >> rw[Pair_def'] >>  
     qsspecl_then [‘d’] assume_tac Oz_Lez_n2z >> drule n2z_Abv >>
     arw[Lez_n2z] >> rw[Ltz_n2z] >> arw[Oz_Lez_n2z] >>
     qpick_x_assum ‘n2z(a) = Addz(Mulz(Fst(qr), n2z(d)), Snd(qr))’
     (assume_tac o GSYM) >> arw[] >>
     rw[Mulz_n2z,Addz_n2z]) >>
 first_x_assum irule >> rw[Pair_def'] >>  
 qsspecl_then [‘d’] assume_tac Oz_Lez_n2z >> drule n2z_Abv >>
 arw[Lez_n2z] >> rw[Ltz_n2z] >> arw[Oz_Lez_n2z] >>
 qpick_x_assum ‘n2z(a) = Addz(Mulz(Fst(qr), n2z(d)), Snd(qr))’
                             (assume_tac o GSYM) >> arw[] >>
 rw[Mulz_n2z,Addz_n2z] >> arw[])
(form_goal 
“!d:mem(N). Le(num1,d) ==>
  !a.?!qr. a = Add(Mul(Fst(qr),d),Snd(qr)) & 
           Lt(Snd(qr),d)”));




fun qfun_compr qv qt = 
    let val vt = qparse_term_with_cont essps qv
        val v = dest_var vt
        val t = qparse_term_with_cont (fvt vt) qt
    in fun_tm_compr_uex v t
    end;

use "quo.sml";

val NONZERO_O_Lt = prove_store("NONZERO_O_Lt",
e0
(strip_tac >> dimp_tac >> strip_tac 
 >-- (fs[Lt_def,O_LESS_EQ] >> flip_tac >> arw[]) >>
 fs[Lt_def] >> ccontra_tac >> fs[])
(form_goal “!n. ~(n = O) <=> Lt(O,n)”));

val DIVR_def = 
P2fun_uex |> qspecl [‘N*N’,‘N*N’]  
          |> fVar_sInst_th “P(ad:mem(N*N),qr:mem(N*N))”
             “(Snd(ad) = O & qr = Pair(O,O)) |
  (~(Snd(ad) = O) &
   Fst(ad) = Add(Mul(Fst(qr),Snd(ad)),Snd(qr)) & 
   Lt(Snd(qr),Snd(ad)))”
|> C mp
(proved_th $
e0
(rpt strip_tac >>
 qsspecl_then [‘ad’] (x_choosel_then ["a","d"] assume_tac)
 Pair_has_comp >> arw[Pair_def'] >> 
 qcases ‘d = O’ >> arw[] (* 2 *) >--
 (uex_tac >> qexists_tac ‘Pair(O,O)’ >> 
 rw[] >> rpt strip_tac >> arw[]) >>
 fs[NONZERO_O_Lt,GSYM Le_num1_Lt_O] >>
 drule division_theorem_N_uex >> arw[] )
(form_goal
 “!ad.
  ?!qr:mem(N * N). 
  (Snd(ad) = O & qr = Pair(O,O)) |
  (~(Snd(ad) = O) &
   Fst(ad) = Add(Mul(Fst(qr),Snd(ad)),Snd(qr)) & 
   Lt(Snd(qr),Snd(ad))) ”))
|> qsimple_uex_spec "DIVR" [] 


val Z2N_def = qdefine_fsym("Z2N",[]) ‘LINV(N2Z,O)’


val Divr_def = qdefine_fsym("Divr",[‘a:mem(N)’,‘d:mem(N)’])
‘App(DIVR,Pair(a,d))’ 


val Divr_property0 =
    DIVR_def |> qspecl [‘Pair(a:mem(N),d:mem(N))’] 
              |> rewr_rule[Pair_def'] 
              |> rewr_rule[GSYM Divr_def]
              |> gen_all


val Divr_O = prove_store("Divr_O",
e0
(rpt strip_tac >>
 qsspecl_then [‘a’,‘d’] assume_tac Divr_property0 >>
 rfs[])
(form_goal 
 “(!d.d = O ==> !a.Divr(a,d) = Pair(O,O))”));

val Divr_NONZERO = prove_store("Divr_NONZERO",
e0
(rpt strip_tac >>
 qsspecl_then [‘a’,‘d’] assume_tac (GSYM Divr_property0) >>
 rfs[] >> fs[])
(form_goal 
 “!d.~(d = O) ==> 
    !a. Add(Mul(Fst(Divr(a, d)), d), 
             Snd(Divr(a, d))) = a  &
        Lt(Snd(Divr(a, d)), d)”));


val Div_def = qdefine_fsym("Div",[‘a:mem(N)’,‘d:mem(N)’])
‘Fst(Divr(a,d))’ 

val Rem_def = qdefine_fsym("Rem",[‘a:mem(N)’,‘d:mem(N)’])
‘Snd(Divr(a,d))’ 

 
val Div_Rem_NONZERO = 
    Divr_NONZERO 
        |> rewr_rule[GSYM Div_def,GSYM Rem_def] 



val Div2_def = qdefine_fsym("Div2",[‘n:mem(N)’]) ‘Div(n,num2)’

val num2_NONZERO = prove_store("num2_NONZERO",
e0
(rw[num2_def,Suc_NONZERO])
(form_goal “~(num2 = O)”));

val Mul_num2 = prove_store("Mul_num2",
e0
(rw[num2_def,num1_def,Mul_clauses,Add_clauses])
(form_goal “!a. Mul(num2,a) = Add(a,a)”));

val Div_Rem_num2 = Div_Rem_NONZERO |> qspecl [‘num2’]
                                   |> rewr_rule[num2_NONZERO]
                                   |> rewr_rule[GSYM Div2_def]


val division_theorem_N_uex' = 
    division_theorem_N_uex |> rewr_rule[Le_num1_Lt_O,GSYM NONZERO_O_Lt]

val Div_Rem_unique = prove_store("Div_Rem_unique",
e0
(strip_tac >> disch_tac >> drule division_theorem_N_uex' >> 
 rpt gen_tac >> disch_tac >>
 first_x_assum (qsspecl_then [‘a’] (strip_assume_tac o uex_expand)) >>  
 qpick_x_assum ‘a = Add(Mul(Fst(qr), d), Snd(qr))’
 (assume_tac o GSYM) >> 
 drule Div_Rem_NONZERO  >>
 first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
 fs[Pair_def'] >> 
 rw[GSYM Pair_eq_eq] >>
 qsuff_tac
 ‘Pair(q,r) = qr &  Pair(Div(a, d), Rem(a, d)) = qr’ 
 >-- (rpt strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (first_x_assum irule >> arw[Pair_def']) >>
 first_x_assum irule >> arw[Pair_def']  )
(form_goal “!d. ~(d = O) ==>
 !a q r. Add(Mul(q,d),r) = a & 
         Lt(r,d) ==> q = Div(a,d) & r = Rem(a,d)”));



val Div_Rem_Mul = prove_store("Div_Rem_Mul",
e0
(rpt gen_tac >> disch_tac >> strip_tac >>
 flip_tac >>
 irule Div_Rem_unique >> arw[Add_clauses] >>
 qsspecl_then [‘a’,‘d’] assume_tac Mul_comm >> arw[] >>
 fs[NONZERO_O_Lt])
(form_goal “!d. ~(d = O) ==> 
               !a. Div(Mul(d,a),d) = a & Rem(Mul(d,a),d) = O”));

val Div2_Mul = prove_store("Div2_Mul",
e0
(assume_tac num2_NONZERO >> drule Div_Rem_Mul >> arw[Div2_def])
(form_goal “!n.Div2(Mul(num2, n)) = n”));

val num1_Lt_num2 = prove_store("num1_Lt_num2",
e0
(rw[num2_def,Lt_Suc])
(form_goal “Lt(num1,num2)”)); 


val Div2_Suc_Mul_num2 = prove_store
("Div2_Suc_Mul_num2",
e0
(assume_tac num2_NONZERO >> drule Div_Rem_unique >>
 flip_tac >> strip_tac >> rw[Div2_def] >>
 first_x_assum irule >> rw[num1_def,Add_clauses,num1_Lt_num2] >>
 qsspecl_then [‘n’,‘num2’] assume_tac Mul_comm >> arw[])
(form_goal “!n.Div2(Suc(Mul(num2, n))) = n & Rem(Suc(Mul(num2, n)),num2) = num1”)); 


val Even_Suc = 
EVEN_def |> conjE2 |> rewr_rule[Suc_def,GSYM App_App_o,FUN_EXT,tf_eq_true] 
         |> rewr_rule[App_App_o,GSYM Suc_def,NOT_def,NOT_true_iff_false] 
         |> rewr_rule[GSYM Even_def,GSYM true_xor_false] 

val num2_Mul_Even = prove_store("num2_Mul_Even",
e0
(Nind_tac >> rw[Mul_clauses,O_Even] >> rpt strip_tac >>
 rw[Add_clauses,num2_def,num1_def,Even_Suc] >> arw[GSYM num1_def,GSYM num2_def] )
(form_goal “!a. Even(Mul(num2,a))”));


val Suc_num2_Mul_Odd = prove_store("Suc_num2_Mul_Odd",
e0
(rw[Odd_not_Even] >> rw[Even_Suc,num2_Mul_Even])
(form_goal “!a. Odd(Suc(Mul(num2,a)))”));




val O_Even = prove_store("O_Even",
e0
(rw[Even_def] >> 
 assume_tac (conjE1 EVEN_def) >>
 first_x_assum $ qspecl_then [‘dot’] assume_tac >> arw[])
(form_goal “Even(O)”));

val O_NEQ_num1 = prove_store("O_NEQ_num1",
e0
(rw[num1_def,GSYM Suc_NONZERO])
(form_goal “~(O = num1)”));



val O_NEQ_num2 = prove_store("O_NEQ_num2",
e0
(rw[num2_def,GSYM Suc_NONZERO])
(form_goal “~(O = num2)”));


val O_NEQ_num3 = prove_store("O_NEQ_num3",
e0
(rw[num3_def,GSYM Suc_NONZERO])
(form_goal “~(O = num3)”));


val O_NEQ_num4 = prove_store("O_NEQ_num4",
e0
(rw[num4_def,GSYM Suc_NONZERO])
(form_goal “~(O = num4)”));



val num1_NEQ_num4 = prove_store("num1_NEQ_num4",
e0
(rw[num1_def,num4_def,Suc_eq_eq,O_NEQ_num3])
(form_goal “~(num1 = num4)”));


val num1_NEQ_num3 = prove_store("num1_NEQ_num3",
e0
(rw[num1_def,num3_def,Suc_eq_eq,O_NEQ_num2])
(form_goal “~(num1 = num3)”));


val num1_NEQ_num2 = prove_store("num1_NEQ_num2",
e0
(rw[num1_def,num2_def,Suc_eq_eq,GSYM Suc_NONZERO])
(form_goal “~(num1 = num2)”));


val num2_NEQ_num3 = prove_store("num2_NEQ_num3",
e0
(rw[num2_def,num3_def,num1_def,Suc_eq_eq,GSYM Suc_NONZERO])
(form_goal “~(num2 = num3)”));


val num2_NEQ_num4 = prove_store("num2_NEQ_num4",
e0
(rw[num2_def,num4_def,Suc_eq_eq,num1_NEQ_num3])
(form_goal “~(num2 = num4)”));


val num4_NEQ_num3 = prove_store("num4_NEQ_num3",
e0
(rw[num4_def,GSYM Suc_NEQ])
(form_goal “~(num4 = num3)”));


val Div_of_O = prove_store("Div_of_O",
e0
(strip_tac >> qcases ‘n = O’ (* 2 *)
 >-- (arw[] >> drule Divr_O >> rw[Div_def,Rem_def] >> rfs[Pair_def']) >>
 drule Div_Rem_unique >> flip_tac >> first_x_assum irule  >>
 rw[Add_clauses,Mul_clauses] >> fs[NONZERO_O_Lt])
(form_goal “!n.Div(O,n) = O & Rem(O,n) = O”));





val Even_Sub_num2 = prove_store("Even_Sub_num2",
e0
(rpt strip_tac >>
 qcases ‘Le(num2,a)’ 
 >-- (drule SUB_ADD >> ccontra_tac >>
     drule $ iffRL Suc_Even >> fs[Add_clauses,num2_def,num1_def] >>
     fs[GSYM num2_def,GSYM num1_def] >>
     qby_tac ‘Even(Suc(Suc(Sub(a, num2))))’ >-- arw[] >> 
     drule $ iffLR Suc_Even >> fs[]) >>
 fs[NOT_LESS_EQ] >> drule Lt_imp_Sub_O >> arw[O_Even]) 
(form_goal “!a. Even(a) ==> Even(Sub(a,num2))”));

val Odd_num1 = prove_store("Odd_num1",
e0
(rw[Odd_def,num1_def,Even_Suc,O_Even])
(form_goal “Odd(num1)”));

val Lt_num2 = prove_store("Lt_num2",
e0
(rw[num2_def] >> rw[Lt_Suc_Le] >>
 rw[num1_def] >> strip_tac >> dimp_tac >> rpt strip_tac >>
 arw[Le_refl,O_LESS_EQ] >>
 drule Le_Suc >> pop_assum strip_assume_tac >> arw[] >>
 drule Le_O_O >> arw[])
(form_goal “!a. Lt(a,num2) <=> a = O | a = num1”));

val Even_Div2 = prove_store("Even_Div2",
e0
(strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (assume_tac num2_NONZERO >> drule Div_Rem_NONZERO >>
     first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
     qsuff_tac ‘Rem(a, num2) = O’ 
     >-- (strip_tac >> fs[Add_clauses,Div2_def]) >>
     fs[Lt_num2] >> fs[num1_def,Add_clauses] >>
     qby_tac ‘Even(Mul(Div(a, num2), num2))’ 
     >-- (once_rw[Mul_comm] >> rw[num2_Mul_Even]) >>
     qby_tac ‘Even(Suc(Mul(Div(a, num2), num2)))’ 
     >-- arw[] >>
     fs[Even_Suc]) >> 
 qsuff_tac ‘Even(Mul(Div2(a), num2))’ 
 >-- arw[] >> once_rw[Mul_comm] >> rw[num2_Mul_Even])
(form_goal “!a. Even(a) <=> Mul(Div2(a),num2) = a & Rem(a,num2) = O”));


val Odd_Div2 = prove_store("Odd_Div2",
e0
(strip_tac >> dimp_tac >> strip_tac >--
 (assume_tac num2_NONZERO >>
 drule Div_Rem_NONZERO >> 
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 qsuff_tac ‘Rem(a, num2) = num1’ 
 >-- (strip_tac >> arw[] >>
     fs[num1_def,Add_clauses,Div2_def]) >>
 fs[Lt_num2] >>
 fs[Add_clauses] >>
 qby_tac ‘Odd(Mul(Div(a, num2), num2))’ >-- arw[] >>
 fs[Odd_def] >>
 qsspecl_then [‘Div(a, num2)’,‘num2’] assume_tac Mul_comm >> fs[] >>
 fs[num2_Mul_Even]) >>
 qsuff_tac ‘Odd(Suc(Mul(Div2(a), num2)))’ >-- arw[] >>
 once_rw[Mul_comm] >> rw[Suc_num2_Mul_Odd])
(form_goal “!a. Odd(a) <=> Suc(Mul(Div2(a),num2)) = a & Rem(a,num2) = num1”));
