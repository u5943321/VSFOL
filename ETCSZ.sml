
(*ZR is the relation (N * N) * N * N -> 2*)
val ZR_def0 = define_fsym("ZR",[])
(qform2IL [‘mn:1->N * N’,‘m'n':1-> N * N’]
‘Add(Fst(mn),Snd(m'n')) = Add(Fst(m'n'),Snd(mn))’)

val ZR_def = prove_store("ZR_def",
e0
(rpt strip_tac >> rw[Holds_def,ZR_def0] >>
 rw[o_assoc,Pa_distr,p12_of_Pa,Eq_property_TRUE,Add_def])
(form_goal
 “!x:1->N y u v.Holds(ZR,Pa(x,y),Pa(u,v)) <=> 
  Add(x,v) = Add(u,y)”));

val ZR_REFL = prove_store("ZR_REFL",
e0
(rw[REFL_def,ZR_def] >> fconv_tac forall_cross_fconv >>
 rw[ZR_def])
(form_goal
 “REFL(ZR)”));


fun basic_fconv_tac c fc = fconv_tac $ basic_fconv c fc
fun depth_fconv_tac c fc = fconv_tac $ depth_fconv c fc

(*use add_sub*)
val ZR_TRANS = prove_store("ZR_TRANS",
e0
(rw[TRANS_def] >> depth_fconv_tac no_conv forall_cross_fconv >>
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
 “TRANS(ZR)”));

 
val ZR_SYM = prove_store("ZR_SYM",
e0
(rw[SYM_def] >> depth_fconv_tac no_conv forall_cross_fconv >>
 rw[ZR_def] >>  rpt strip_tac >> arw[])
(form_goal
 “SYM(ZR)”));

val ER_def = qdefine_psym("ER",[‘R:A * A->1+1’])
‘REFL(R) & SYM(R) & TRANS(R)’ |> gen_all |> store_as "ER_def";

val ZR_ER = prove_store("ZR_ER",
e0
(rw[ER_def,ZR_SYM,ZR_REFL,ZR_TRANS])
(form_goal “ER(ZR)”));

(*Relational singleton image*)
val Rsi_uex = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac ‘?s:1->Exp(B,1+1).
 (!b.IN(b,s) <=> Holds(R,a,b))’
 >-- (strip_tac >> uex_tac >> 
     qexists_tac ‘s’ >> arw[] >> rpt strip_tac >> 
     irule $ iffLR IN_EXT >> arw[]) >>
 rw[Holds_def] >> 
 exists_tac 
(Tp1 (qform2IL [‘b:1->B’] ‘R o Pa(a:1->A,b:1->B) = TRUE’)) >>
 rw[IN_Tp1] >> rw[Eq_property_TRUE,o_assoc,Pa_distr,one_to_one_id,idR,idL])
(form_goal “!A B R:A * B ->1+1 a:1->A.?!s:1->Exp(B,1+1).
 (!b.IN(b,s) <=> Holds(R,a,b))”)
|> rewr_rule[Holds_def]
|> spec_all |> qgen ‘a’

val Rsi_def = 
P2fun_uex |> qspecl [‘A’,‘Exp(B,1+1)’]
|> specl[qform2IL [‘a:1->A’,‘s:1->Exp(B,1+1)’]
   ‘!b.IN(b,s) <=> R o Pa(a,b) = TRUE’]
|> rewr_rule[Holds_def,All_def,o_assoc,p12_of_Pa,Pa_distr,
    IFF_def,p31_def,p32_def,p33_def,one_to_one_id,idL,idR,
    Eq_property_TRUE]
|> rewr_rule[GSYM IN_def]
|> C mp Rsi_uex
|> rewr_rule[GSYM Holds_def]
|> qsimple_uex_spec "Rsi" [‘R’]
|> qspecl [‘a:1->A’,‘Rsi(R:A * B->1+1) o a:1->A’] 
|> rewr_rule[]
|> gen_all |> store_as "Rsi_def";


val rsi_def = qdefine_fsym ("rsi",[‘r:A *B -> 1+1’,‘a:1->A’])
                            ‘Rsi(r) o a’
                            |> gen_all |> store_as "rsi_def";

val IN_rsi = prove_store("IN_rsi",
e0
(rw[rsi_def,Rsi_def])
(form_goal “∀A r:A * A -> 1+1 a1 a2. IN(a2,rsi(r,a1)) ⇔ Holds(r,a1,a2) ”));


val ER_Holds = prove_store("ER_Holds",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum (qspecl_then [‘a2’] assume_tac) >> fs[ER_def,REFL_def]) >>
 dimp_tac >> strip_tac >> fs[ER_def,SYM_def,TRANS_def] (* 2 *)
 >-- (first_x_assum irule >> qexists_tac ‘a1’ >> arw[] >> first_x_assum irule >>
     arw[]) >>
 first_x_assum irule >> qexists_tac ‘a2’ >> arw[])
(form_goal “∀A r:A * A -> 1+1. ER(r) ⇒ ∀a1 a2. 
 ((∀x.Holds(r,a1,x) ⇔ Holds(r,a2,x)) ⇔ Holds(r,a1,a2))”));
 
val rsi_eq_ER = prove_store("rsi_eq_ER",
e0
(rw[GSYM IN_EXT,IN_rsi] >> 
 rpt strip_tac >> drule ER_Holds >> arw[])
(form_goal “!A r:A * A-> 1+1.ER(r) ==> 
 !a1 a2. rsi(r,a1) = rsi(r,a2) <=> Holds(r,a1,a2)”));

val _ = new_fsym2IL("rsi",(rastt "Rsi(R:A * B-> 1+1)",
List.map (dest_var o rastt) ["r:A * B -> 1+1","a:X->A"]))


(*
val _ = new_fsym2IL("rsi",(rastt "Rsi(R:A * B-> 1+1)",
List.map (dest_var o rastt) ["r:A * B -> 1+1","a:X->A"]))

term2IL [dest_var (rastt "n:1->N")]
 (rastt " rsi(ZR,n:1->N)") cannot build, may require more complex dict

*)

val Z_def = 
Thm_2_4' |> qspecl [‘Exp(N * N,1+1)’]
                    |> specl[qform2IL [‘s:1->Exp(N * N,1+1)’]
                    ‘?n. s = Rsi(ZR) o n’]
|> rewr_rule[o_assoc,Pa_distr,p12_of_Pa,Ex_def,Eq_property_TRUE,GSYM rsi_def]
|> set_spec (rastt "Exp(N * N,1+1)") "Z" "iZ" []
|> store_as "Z_def";

(*
Thm_2_4 |> qspecl [‘Exp(N * N,1+1)’]
                    |> specl[qform2IL [‘s:1->Exp(N * N,1+1)’]
                    ‘?n. s = Rsi(ZR) o n’]
|> rewr_rule[o_assoc,Pa_distr,p12_of_Pa,Ex_def,Eq_property_TRUE,GSYM rsi_def]
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
 first_x_assum (qspecl_then [‘iZ o z’] assume_tac) >>
 (*stupid step, ?(b : mem(Z)). App(iZ, z) = App(iZ, b#)*)
 qby_tac ‘?b. iZ o z = iZ o b’ 
 >-- (qexists_tac ‘z’ >> rw[]) >>
 first_x_assum (drule o iffRL) >>
 pop_assum strip_assume_tac >>
 qsspecl_then [‘x’] strip_assume_tac Pair_has_comp >>
 fs[] >> qexistsl_tac [‘a’,‘b’] >> arw[])
(form_goal 
 “!z:1->Z.?m n. iZ o z = rsi(ZR,Pa(m,n))”));

val rsi_iZ = prove_store("rsi_iZ",
e0
(rpt strip_tac >> strip_assume_tac Z_def >>
 first_x_assum
 (qspecl_then [‘rsi(ZR,Pa(m,n))’] assume_tac) >>
 first_x_assum $ irule o iffLR >>
 qexists_tac ‘Pa(m,n)’ >> rw[])
(form_goal 
 “!m n. ?z. rsi(ZR,Pa(m,n)) = iZ o z”));


val resp_def = 
 qdefine_psym("resp",[‘f:A->B’,‘r1:A * A-> 1+1’,‘r2:B * B-> 1+1’])
 ‘!y z.Holds(r1,y,z) ==> Holds(r2,f:A->B o y,f o z)’
 |> gen_all |> store_as "resp_def";


val rext_def0 = define_fsym("rext",
List.map (dest_var o rastt) 
["f:A->B","r1:A*A->1+1","r2:B * B -> 1+1"])
(qform2IL [‘sa:1->Exp(A,1+1)’,‘sb:1->Exp(B,1+1)’]
‘?a b.
 sa = Rsi(r1:A * A->1+1) o a & 
 sb = Rsi(r2:B * B->1+1) o b & 
 f o a = b’) |> gen_all |> store_as "rext_def";   

                    
val rext_def1 = prove_store("rext_def1",
e0
(rpt strip_tac >> rw[Holds_def,rext_def0] >>
 once_rw[p41_def,p42_def,p43_def,p44_def] >>
 rw[Ex_def,CONJ_def,Pa_distr,p12_of_Pa,o_assoc,
    Eq_property_TRUE])
(form_goal 
 “!A r1:A * A->1+1 B f:A->B r2.
  !sa sb. Holds(rext(f,r1,r2),sa,sb) <=>
 ?a b.
 sa = Rsi(r1) o a & sb = Rsi(r2) o b & 
 f o a = b ”));

val rext_def = rext_def1 |> rewr_rule[GSYM rsi_def]
                         |> store_as "rext_def";

val prrel_def0 = define_fsym("prrel",
List.map (dest_var o rastt) 
["r1:A * A->1+1","r2:B * B-> 1+1"]) 
(qform2IL [‘ab1:1->A * B’,‘ab2:1->A* B’]
‘r1 o Pa(Fst(ab1),Fst(ab2)) = TRUE &
 r2 o Pa(Snd(ab1),Snd(ab2)) = TRUE’)


(*if not strip, then very very very slow prrel_def.*)

val prrel_def = prove_store("prrel_def",
e0
(rpt strip_tac >> rw[Holds_def,prrel_def0,Eq_property_TRUE,p12_of_Pa,o_assoc,CONJ_def,
Pa_distr,one_to_one_id,idL,idR]
 )
(form_goal
 “!A r1 B r2 a1:1->A b1:1->B a2:1->A b2.
  Holds(prrel(r1,r2),Pa(a1,b1),Pa(a2,b2)) <=> 
  Holds(r1,a1,a2) & Holds(r2,b1,b2)”));


val P2fun' = prove_store("P2fun'",
e0
(rpt strip_tac >> drule P2fun >>
 pop_assum strip_assume_tac >>
 uex_tac >> qexists_tac ‘f’ >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rpt strip_tac >>
 irule FUN_EXT >> arw[])
(form_goal 
 “!A B R:A*B->1+1.
  (!x:1->A.?!y:1->B. Holds(R,x,y)) ==>
  ?!f:A->B. !x:1->A.
  Holds(R,x,f o x)”));

val main = prove_store("main",
e0
(rpt strip_tac >> assume_tac 
 (P2fun' |> qspecl [‘Q1’,‘Q2’] 
        |> specl
[qform2IL [‘q1:1->Q1’,‘q2:1->Q2’]
‘rext(f:A->B, r1:A * A->1+1, r2:B*B->1+1) o 
 Pa(i1:Q1->Exp(A,1+1) o q1, i2 o q2) = TRUE’]) >>
 pop_assum mp_tac >>
 rw[Holds_def,Eq_property_TRUE,Pa_distr,p12_of_Pa,o_assoc] >>
 rw[one_to_one_id,idR] >> rw[GSYM Holds_def] >>
 rpt strip_tac >>
 first_x_assum irule >> 
 strip_tac >> 
 qby_tac (*a bit slow here*)
 ‘!sb.(?!q2. sb = i2 o q2) <=> 
       ?b. sb = rsi(r2,b)’ >-- 
 (strip_tac >> dimp_tac >> disch_tac 
 >-- (pop_assum (assume_tac o uex2ex_rule) >> 
     first_x_assum (drule o iffLR) >> arw[]) >>
 uex_tac >> first_x_assum (drule o iffRL) >>
 pop_assum strip_assume_tac >> qexists_tac ‘q2’ >> arw[] >>
 rpt strip_tac >> fs[Inj_def] >> first_x_assum irule >> arw[])
 (* easy by injection*)>>
 fs[resp_def] >>
 first_x_assum (qspecl_then [‘i1 o x’] assume_tac) >>
 qby_tac ‘?a. i1 o x = rsi(r1,a)’ >-- 
 (first_x_assum (irule o iffLR) >> qexists_tac ‘x’ >> rw[]) >>
 (*should be auto*)
 pop_assum strip_assume_tac >> 
 first_x_assum (qspecl_then [‘Rsi(r2) o f o a’] 
 assume_tac) >> fs[GSYM rsi_def] >>
 qby_tac
 ‘?!q2:1->Q2. rsi(r2, f o a) = i2 o q2’
 >-- (first_x_assum (irule o iffRL) >> qexists_tac ‘f o a’ >> rw[]) >>
 qsuff_tac ‘!q2:1->Q2. 
  rsi(r2, f o a) = i2 o q2 <=> 
  Holds(rext(f, r1, r2), rsi(r1, a),i2 o q2)’
 >-- (strip_tac >> pop_assum (assume_tac o GSYM) >> arw[]) >>
 rw[rext_def] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexistsl_tac [‘a’,‘f o a’] >> arw[]) >> 
 qsuff_tac ‘?b. i2 o q2 = rsi(r2, b) & 
 Holds(r2,b,f o a)’ >-- 
 (strip_tac >> 
 qpick_x_assum ‘i2 o q2 = rsi(r2, b')’
 (assume_tac o GSYM) >> arw[] >>
 drule rsi_eq_ER >> arw[] >>
 rev_drule rsi_eq_ER >> fs[] >> last_x_assum drule >>
 rfs[]) >>
 qexists_tac ‘b’ >> arw[] >> pop_assum (assume_tac o GSYM) >>
 arw[] >> first_x_assum irule >> 
 rev_drule rsi_eq_ER >> fs[ER_def,SYM_def] >> 
 first_x_assum irule >> arw[])
(form_goal
“!A B f:A->B r1:A*A->1+1 r2:B*B->1+1
 Q1 Q2 i1:Q1->Exp(A,1+1) i2:Q2->Exp(B,1+1). 
 ER(r1) & ER(r2) & resp(f,r1,r2) & Inj(i1) & Inj(i2) &
 (!sa. (?q1. sa = i1 o q1) <=> (?a. sa = rsi(r1,a))) & 
 (!sb. (?q2. sb = i2 o q2) <=> (?b. sb = rsi(r2,b))) ==>
 ?!qf: Q1-> Q2.
 !q1:1->Q1. Holds(rext(f,r1,r2),i1 o q1,i2 o qf o q1) ”));



(* Pow(A) * Pow(A) -> Pow(A * A) not have in general. *)


val ipow2IL_def =
define_fsym("ipow2IL",List.map (dest_var o rastt)
["i1:Q1->Exp(A,1+1)","i2:Q2->Exp(B,1+1)"])
(qform2IL [‘aqbq:1->Q1*Q2’,‘s:1->Exp(A*B,1+1)’]
 ‘!a1 a2.IN(Pa(a1,a2),s) <=> 
  IN(a1,i1:Q1-> Exp(A,1+1) o Fst(aqbq)) & 
  IN(a2,i2:Q2-> Exp(B,1+1) o Snd(aqbq))’)

val ipow2_IL = 
proved_th $
e0
(rw[ipow2IL_def] >>
 rpt strip_tac >>
 rw[Holds_def] >>
 rw[o_assoc,All_def,IFF_def,CONJ_def,Pa_distr] >>
 once_rw[p41_def,p42_def,p43_def,p44_def] >>
 rw[Pa_distr,o_assoc,p12_of_Pa] >>
 rw[IN_def,Fst_def,Snd_def])
(form_goal
 “!aqbq:1->Q1*Q2 s:1->Exp(A*B,1+1).
 Holds(ipow2IL(i1:Q1->Exp(A,1+1),i2:Q2->Exp(B,1+1)),
 aqbq,s) <=>
 !a1 a2.IN(Pa(a1,a2),s) <=> 
  IN(a1,i1:Q1-> Exp(A,1+1) o Fst(aqbq)) & 
  IN(a2,i2:Q2-> Exp(B,1+1) o Snd(aqbq))
 ”)

val IN_def_P = prove_store("IN_def_P",
e0
(rpt strip_tac >> uex_tac >>
 qsspecl_then [‘P’] strip_assume_tac IN_def_P_ex >>
 qexists_tac ‘s’>> arw[] >>
 rpt strip_tac >> rw[GSYM IN_EXT] >>
 arw[])
(form_goal
 “!A P:A->1+1.?!s:1->Exp(A,1+1).
  (!a:1->A. P o a = TRUE <=> IN(a,s))”));


val ipow2IL1_def =
define_fsym("ipow2IL1",List.map (dest_var o rastt)
["i1:Q1->Exp(A,1+1)","i2:Q2->Exp(B,1+1)",
 "aqbq:1-> Q1*Q2"])
(qform2IL [‘ab:1->A*B’]
 ‘IN(Fst(ab),i1:Q1-> Exp(A,1+1) o Fst(aqbq:1->Q1*Q2)) & 
  IN(Snd(ab),i2:Q2-> Exp(B,1+1) o Snd(aqbq))’)

val ipow2_IL1 = 
proved_th $
e0
(rw[ipow2IL1_def] >>
 rpt strip_tac >>
 rw[o_assoc,All_def,IFF_def,CONJ_def,Pa_distr] >>
 rw[Pa_distr,o_assoc,p12_of_Pa,one_to_one_id,idL,idR] >>
 rw[IN_def,Fst_def,Snd_def])
(form_goal
 “!ab:1->A*B.
 ipow2IL1(i1:Q1->Exp(A,1+1),i2:Q2->Exp(B,1+1),
 aqbq) o ab = TRUE <=>
 IN(Fst(ab),i1:Q1-> Exp(A,1+1) o Fst(aqbq:1->Q1*Q2)) & 
  IN(Snd(ab),i2:Q2-> Exp(B,1+1) o Snd(aqbq))
 ”)


val ipow2_def = 
P2fun' |> qspecl [‘Q1 * Q2’,‘Exp(A * B,1+1)’,‘ipow2IL(i1:Q1->Exp(A,1+1),i2:Q2->Exp(B,1+1))’]
|> rewr_rule[ipow2_IL]
|> C mp
   (IN_def_P 
    |> qspecl [‘A * B’,
       ‘ipow2IL1(i1:Q1->Exp(A,1+1),i2:Q2->Exp(B,1+1),
                aqbq:1->Q1*Q2)’]
    |> rewr_rule[ipow2_IL1]
    |> conv_rule (depth_fconv no_conv 
                                                         forall_cross_fconv)
    |> rewr_rule[Pair_def']
    |> qgen ‘aqbq’ |> GSYM)
|> qsimple_uex_spec "ipow2" [‘i1’,‘i2’]
|> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[Pair_def']
|> qspecl [‘aq:1->Q1’,‘bq:1->Q2’,
            ‘a:1->A’,‘b:1->B’] 
|> gen_all |> store_as "ipow2_def";

local 
val l = P2fun' |> qspecl [‘(N * N) * N * N’,‘N * N’]
|> specl[qform2IL [‘xyuv:1-> (N * N) * N * N’,‘ab:1->N * N’]
   ‘ab  = Pa(Add(Fst(Fst(xyuv)),Fst(Snd(xyuv))),
             Add(Snd(Fst(xyuv)),Snd(Snd(xyuv))))’]
|> conv_rule (depth_fconv no_conv forall_cross_fconv) 
|> conv_rule (basic_fconv no_conv forall_cross_fconv)
|> rewr_rule[Holds_def,o_assoc]
|> rewr_rule[Eq_property_TRUE,o_assoc,Pa_distr,p12_of_Pa]
|> rewr_rule[GSYM Add_def]
in    
val addf0_def = proved_th $
e0
(irule l >> rpt strip_tac >> uex_tac >>
 qexists_tac ‘Pa(Add(a', a), Add(b, b''))’ >> rw[])
(form_goal “?!f:(N * N) * N * N -> N * N. 
 !x y u v. f o Pa(Pa(x,y),Pa(u,v)) = 
 Pa(Add(x,u),Add(y,v))”)
|> qsimple_uex_spec "addf0" []
|> store_as "addf0_def";
end

(*addf0 does not need unique since no free variable, is this axiom of choice regarding FOL expressions?,addf0 slow*)



val prrel_ER_ER = prove_store("prrel_ER_ER",
e0
(rpt strip_tac >> fs[ER_def,SYM_def,TRANS_def,REFL_def] >> 
 depth_fconv_tac no_conv forall_cross_fconv >> once_rw[prrel_def] >>
 rpt strip_tac >> arw[] (* 4 *)
 >-- (last_x_assum drule >> arw[]) 
 >-- (first_x_assum drule >> arw[])
 >-- (first_x_assum irule >> qexists_tac ‘a'’ >> arw[]) >>
 first_x_assum irule >> qexists_tac ‘b'’ >> arw[])
(form_goal “∀A r1:A * A->1+1 B r2:B*B->1+1. ER(r1) & ER(r2) ⇒ ER(prrel(r1,r2))”));


val forall_cross_tac =  depth_fconv_tac no_conv forall_cross_fconv;


val Pow_conj_eq0 = prove_store("Pow_conj_eq0",
e0
(rpt strip_tac >>
rw[GSYM IN_EXT] >> strip_tac >> 
cases_on “IN(x,s1:1->Exp(A,1+1))”
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
(form_goal “∀A B s1:1->Exp(A,1+1) s2:1->Exp(B,1+1) s3 s4 a0 b0. IN(a0,s1) & IN(b0,s2) ⇒  (∀a b. IN(a,s1) & IN(b,s2) ⇔ IN(a,s3) & IN(b,s4)) ⇒
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
(form_goal “∀A B s1:1->Exp(A,1+1) s2:1->Exp(B,1+1) s3 s4 a0 b0. IN(a0,s1) & IN(b0,s2) ⇒  (∀a b. IN(a,s1) & IN(b,s2) ⇔ IN(a,s3) & IN(b,s4)) ⇒
 s1 = s3 & s2 = s4”));


val ipow2_Inj_Inj = prove_store("ipow2_Inj_Inj",
e0
(rpt strip_tac >> fs[Inj_def] >> 
 depth_fconv_tac no_conv forall_cross_fconv >>
 rw[GSYM IN_EXT] >>
 forall_cross_tac >> rpt strip_tac >> fs[ipow2_def] >>
 rw[Pa_eq_eq] >> 
 qsuff_tac ‘i1 o a = i1 o a' & i2 o b = i2 o b'’ 
 >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
 irule Pow_conj_eq >> arw[])
(form_goal “∀Q1 A i1:Q1 -> Exp(A,1+1) Q2 B i2:Q2->Exp(B,1+1). 
 (∀q1. ∃a. IN(a,i1 o q1)) &
 (∀q2. ∃b. IN(b,i2 o q2)) & 
 Inj(i1) & Inj(i2) ⇒ Inj(ipow2(i1,i2))”));



val Quo_def = qdefine_psym ("Quo",[‘r:A*A->1+1’,‘i:Q->Exp(A,1+1)’])
‘!s. (?!q. s =i:Q->Exp(A,1+1) o q) <=> 
(?a. s = rsi(r:A * A -> 1+1,a))’
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
>-- (qby_tac ‘∃!q.s = i o q’
    >-- (uex_tac >> qexists_tac ‘q’ >> arw[] >> rpt strip_tac >>
        fs[Inj_def] >> first_x_assum irule >> arw[]) >>
    first_x_assum (drule o iffLR) >> arw[]) >>
qsuff_tac ‘∃!q. s = i o q’ 
>-- (strip_tac >> pop_assum (assume_tac o uex2ex_rule) >> arw[]) >>
first_x_assum (irule o iffRL) >> qexists_tac ‘a’ >> arw[])
(form_goal
“(Inj(i) & !s. (?q. s = i:Q->Exp(A,1+1) o q) <=> (?a. s = rsi(r:A*A->1+1,a)))
 ⇔ Inj(i) & Quo(r,i)”));

val ER_rsi_nonempty = prove_store("ER_rsi_nonempty",
e0
(rpt strip_tac >> rw[IN_rsi] >> fs[ER_def,REFL_def])
(form_goal “∀A r:A*A->1+1 a:1->A.ER(r) ⇒ IN(a,rsi(r,a)) ”));

val Quo_cong = prove_store("Quo_cong",
e0
(rpt strip_tac >> fs[Quo_def] >> 
 depth_fconv_tac no_conv exists_cross_fconv >>
 rw[GSYM IN_EXT] >>
 depth_fconv_tac no_conv forall_cross_fconv >> 
 rw[IN_rsi,prrel_def,ipow2_def] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac
     ‘∀a. ∃!q.rsi(r1,a) = i1 o q’
     >-- (strip_tac >>
         qby_tac ‘∃a1. rsi(r1,a) = rsi(r1,a1)’ 
         >-- (qexists_tac ‘a’ >> rw[]) >>
         first_x_assum (drule o iffRL) >> arw[]) >>
     qby_tac
     ‘∀b. ∃!q.rsi(r2,b) = i2 o q’
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
     qsuff_tac ‘∃a1 b1. i1 o q1 = rsi(r1, a1) & i2 o q2 = rsi(r2, b1)’ 
     >-- (strip_tac >> qexistsl_tac [‘a1’,‘b1’] >> arw[]) >>
     qby_tac ‘∃!q. i1 o q1 = i1 o q’ 
     >-- (uex_tac >> qexists_tac ‘q1’ >> rw[] >> fs[Inj_def] >>
         rpt strip_tac >> first_x_assum irule >> arw[]) >>
     first_x_assum (drule o iffLR) >> pop_assum strip_assume_tac >>
     qby_tac ‘∃!q.i2 o q2 = i2 o q’ 
     >-- (uex_tac >> qexists_tac ‘q2’ >> rw[] >> fs[Inj_def] >>
         rpt strip_tac >> first_x_assum irule >> arw[]) >>
     first_x_assum (drule o iffLR) >> pop_assum strip_assume_tac >>
     qexistsl_tac [‘a’,‘a'’] >> arw[]) >>
qsuff_tac ‘∃!q:1->Q1 * Q2.
 (∀a1 b1. Holds(r1, a', a1) & Holds(r2, b, b1) ⇔ 
  IN(Pa(a1, b1), ipow2(i1, i2) o q))’
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
uex_tac >> qexists_tac ‘Pa(q1,q2)’ >> 
depth_fconv_tac no_conv forall_cross_fconv >>
rw[ipow2_def,GSYM IN_rsi,Pa_eq_eq] >>
qsuff_tac ‘rsi(r1, a') = i1 o q1 & rsi(r2, b) = i2 o q2’
>-- (strip_tac >> arw[] >> rpt gen_tac >> disch_tac >>
    qsuff_tac ‘i1 o q1 = i1 o a & 
               i2 o q2 = i2 o b'’ 
    >-- (rpt strip_tac >> fs[Inj_def] >> first_x_assum irule >> arw[]) >>
    irule Pow_conj_eq >>
    arw[] >> strip_tac (* 2 *)
    >-- (qexists_tac ‘b’ >> 
        qpick_x_assum ‘rsi(r2, b) = i2 o q2’ (assume_tac o GSYM) >>
        arw[] >> irule ER_rsi_nonempty >> arw[]) >>
    qexists_tac ‘a'’ >> 
    qpick_x_assum ‘rsi(r1, a') = i1 o q1’ (assume_tac o GSYM) >>
    arw[] >> irule ER_rsi_nonempty >> arw[]) >>
arw[])
(form_goal “∀A r1:A*A-> 1+1 Q1 i1:Q1-> Exp(A,1+1) B r2:B*B->1+1 Q2 i2:Q2 -> Exp(B,1+1). 
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
“!A B f:A->B r1:A*A->1+1 r2:B*B->1+1
 Q1 Q2 i1:Q1->Exp(A,1+1) i2:Q2->Exp(B,1+1). 
 ER(r1) & ER(r2) & resp(f,r1,r2) & Inj(i1) & Inj(i2) &
 Quo(r1,i1) & Quo(r2,i2) ==>
 ?!qf: Q1-> Q2.
 !q1:1->Q1. Holds(rext(f,r1,r2),i1 o q1,i2 o qf o q1) ”))



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
 arw[Add_assoc] >> 
 qspecl_then [‘c’,‘a’] assume_tac Add_comm >> arw[] >>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(v, Add(y1, a)) = Add(a, Add(y1, v))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘Add(y1,v)’,‘a’] assume_tac Add_comm >> arw[] >>
 rw[Add_assoc] >>
 qspecl_then [‘y1’,‘v’] assume_tac Add_comm >> arw[])
(form_goal “resp(addf0, prrel(ZR, ZR), ZR)”));



(*may need con rw for simplifying main_addz'*)
val iZ_nonempty = prove_store("iZ_nonempty",
e0
(strip_tac >> strip_assume_tac Z_def >> 
 qsuff_tac ‘∃n. iZ o z = rsi(ZR,n)’ 
 >-- (strip_tac >> arw[] >> qexists_tac ‘n’ >> irule ER_rsi_nonempty >>
     rw[ZR_ER]) >>
 first_x_assum (irule o iffRL) >> qexists_tac ‘z’ >> rw[])
(form_goal “∀z. ∃ab. IN(ab,iZ o z)”));


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




val main_addz = 
Quo_fun |> qspecl [‘(N * N) * (N * N)’,‘N * N’,
                ‘addf0’,
                ‘prrel(ZR,ZR)’,‘ZR’,
                ‘Z * Z’,‘Z’,
                ‘ipow2(iZ,iZ)’,‘iZ’]
        |> conv_rule (depth_fconv no_conv forall_cross_fconv)
        |> C mp addz_conds
        |> qsimple_uex_spec "addz" []
        |> qspecl [‘z1:1->Z’,‘z2:1->Z’]
        |> rewr_rule[rext_def,GSYM IN_EXT,IN_rsi] 


val main_addz1 = proved_th $
e0
(strip_assume_tac main_addz >>
 qsspecl_then [‘b’] (x_choosel_then ["b1","b2"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a’] (x_choosel_then ["a12","a34"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a12’] (x_choosel_then ["a1","a2"] assume_tac) Pair_has_comp >>
 qsspecl_then [‘a34’] (x_choosel_then ["a3","a4"] assume_tac) Pair_has_comp >>
 once_arw[] >> qexistsl_tac [‘a1’,‘a2’,‘a3’,‘a4’,‘b1’,‘b2’] >>
 arw[] >>
 qsuff_tac ‘Pa(Pa(a1, a2), Pa(a3, a4))  = a & Pa(b1,b2) = b’ 
 >-- (qpick_x_assum ‘addf0 o  a = b’ mp_tac >>
      pop_assum_list (K all_tac) >> rpt strip_tac >> arw[]) >> 
 arw[])
(form_goal
 “?a1 a2 a3 a4 b1 b2.
     (!x1 x2 x3 x4.
            IN(Pa(Pa(x1,x2),Pa(x3,x4)), 
               ipow2(iZ, iZ) o Pa(z1, z2)) <=>
            Holds(prrel(ZR, ZR), Pa(Pa(a1,a2),Pa(a3,a4)), Pa(Pa(x1,x2),Pa(x3,x4)))) &
        (!n1 n2.
            IN(Pa(n1,n2), iZ o addz o Pa(z1, z2)) <=> 
            Holds(ZR, Pa(b1,b2), Pa(n1,n2))) &
        addf0 o Pa(Pa(a1,a2),Pa(a3,a4)) = Pa(b1,b2)”)
|> rewr_rule[ipow2_def,prrel_def,GSYM IN_rsi]


val main_addz2 = proved_th $
e0
(strip_assume_tac main_addz1 >>
 qexistsl_tac [‘a1’,‘a2’,‘a3’,‘a4’,‘b1’,‘b2’] >>
 qby_tac ‘iZ o z1 = rsi(ZR,Pa(a1,a2)) & iZ o z2 = rsi(ZR,Pa(a3,a4))’ 
 >-- (irule Pow_conj_eq >> rw[iZ_nonempty] >> 
     depth_fconv_tac no_conv forall_cross_fconv >> arw[]) >>
 arw[] >> rw[GSYM IN_EXT] >> fconv_tac forall_cross_fconv >> arw[])
(form_goal
 “∃a1 a2 a3 a4 b1 b2.
  iZ o z1 = rsi(ZR,Pa(a1,a2)) & iZ o z2 = rsi(ZR,Pa(a3,a4)) &
  iZ o addz o Pa(z1,z2) = rsi(ZR,Pa(b1,b2)) &
  addf0 o Pa(Pa(a1, a2), Pa(a3, a4)) = Pa(b1, b2)”)


val main_addz3 = main_addz2 |> rewr_rule[addf0_def] 
                            |> store_as "main_addz3";



val Inj_Quo_rep = prove_store("Inj_Quo_rep",
e0
(fs[Quo_def] >> rpt strip_tac >>
 first_x_assum (irule o iffLR) >> uex_tac >>
 qexists_tac ‘q’ >> rw[] >> fs[Inj_def] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal “∀A r:A*A->1+1 Q i:Q->Exp(A,1+1). Inj(i) & Quo(r,i) ⇒
 ∀q.∃a. i o q = rsi(r,a)”));

val Z_has_rep = prove_store("Z_has_rep",
e0
(assume_tac Inj_Quo_Z >> drule Inj_Quo_rep >>
 pop_assum (assume_tac o (conv_rule (depth_fconv no_conv exists_cross_fconv)))>>
 arw[] )
(form_goal “∀z. ∃n1 n2. iZ o z = rsi(ZR,Pa(n1,n2))”));


val Addz_def = qdefine_fsym ("Addz",[‘z1:1->Z’,‘z2:1->Z’])
                            ‘addz o Pa(z1,z2)’
                            |> gen_all |> store_as "Addz_def";

val _ = new_fsym2IL1("Addz",rastt "addz")

val Repz_def = qdefine_fsym ("Repz",[‘z:1->Z’])
                            ‘iZ o z’
                            |> gen_all |> store_as "Repz_def";

val _ = new_fsym2IL1("Repz",rastt "iZ")

val Repz_rsi = Z_has_rep |> rewr_rule[GSYM Repz_def] 
                         |> store_as "Repz_rsi";

(*ZR class*)
val ZC_def = qdefine_fsym ("ZC",[‘ab:1->N * N’])
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
 first_x_assum (qsspecl_then [‘Pa(Pa(a1',a2'),Pa(a3',a4'))’,
               ‘Pa(Pa(a1,a2),Pa(a3,a4))’] assume_tac)  >>
 fs[addf0_def] >> first_x_assum irule >>
 arw[prrel_def,GSYM ZC_ZR])
(form_goal
 “∀z1 a1 a2.
  Repz(z1) = ZC(Pa(a1,a2)) ⇒
  ∀z2 a3 a4. 
  Repz(z2) = ZC(Pa(a3,a4)) ⇒
  Repz(Addz(z1,z2)) = ZC(Pa(Add(a1, a3), Add(a2, a4)))”));

val Repz_eq_eq = iZ_eq_eq |> rewr_rule[GSYM Repz_def] |> store_as "Repz_eq_eq";


val Repz_eq_ZR = rsi_eq_ER |> qsspecl [‘ZR’] |> C mp ZR_ER 
                           |> rewr_rule[GSYM ZC_def]
                           |> store_as "Repz_eq_ZR";


val eq_ZR = prove_store("eq_ZR",
e0
(rpt strip_tac >> assume_tac ZR_REFL >> fs[REFL_def])
(form_goal
 “!a b. a = b ==> Holds(ZR,a,b)”));

val Addz_comm = prove_store("Addz_comm",
e0
(rpt strip_tac >> irule Repz_eq_eq >> rpt strip_tac >>
 qsspecl_then [‘z1’] (x_choosel_then ["a","b"] assume_tac) Repz_ZC >>
 qsspecl_then [‘z2’] (x_choosel_then ["c","d"] assume_tac) Repz_ZC >>
 qby_tac ‘Repz(Addz(z1, z2)) = ZC(Pa(Add(a, c), Add(b, d)))’
 >-- (irule Addz_char >> arw[]) >>
 qby_tac ‘Repz(Addz(z2, z1)) = ZC(Pa(Add(c, a), Add(d, b)))’
 >-- (irule Addz_char >> arw[]) >>
 arw[] >> rw[ZC_ZR] >> 
 qsuff_tac ‘Add(a,c) = Add(c,a) & Add(b,d) = Add(d,b)’ 
 >-- (strip_tac >> arw[] >> irule eq_ZR >> arw[]) >> 
 qspecl_then [‘a’,‘c’] assume_tac Add_comm' >>
 qspecl_then [‘b’,‘d’] assume_tac Add_comm' >> arw[])
(form_goal “!z1 z2. Addz(z1,z2) = Addz(z2,z1)”));



val negf0_def = qdefine_fsym("negf0",[])
‘Swap(N,N)’ |> gen_all



val negf0_def1 = proved_th $
e0
(rw[Swap_Pa,negf0_def])
(form_goal “!m:1->N n. negf0 o Pa(m,n)= Pa(n,m)”)
|> store_as "negf0_def1";



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
Quo_fun |> qspecl [‘N * N’,‘N * N’,
                ‘negf0’,
                ‘ZR’,‘ZR’,
                ‘Z’,‘Z’,
                ‘iZ’,‘iZ’]
        |> rewr_rule[Inj_Quo_Z,ZR_ER,negf0_resp]
        |> qsimple_uex_spec "negz" []
        |> qspecl [‘z:1->Z’]
        |> rewr_rule[rext_def,GSYM Repz_def,GSYM ZC_def] 


val Negz_def = qdefine_fsym ("Negz",[‘z:1->Z’])
                            ‘negz o z’
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
 Repz(z) = ZC(Pa(a1,a2)) & Repz(negz o z) = ZC(Pa(a2,a1))”)
|> rewr_rule[GSYM Negz_def]

val Negz_char = prove_store("Neg_char",
e0
(rpt strip_tac >>
 strip_assume_tac main_negz1 >> arw[ZC_ZR] >>
 assume_tac negf0_resp >>
 fs[resp_def] >>
 first_x_assum (qsspecl_then [‘Pa(a,b)’,‘Pa(a1,a2)’] assume_tac) >>
 fs[negf0_def1,Pair_def'] >>
 assume_tac ZR_ER >> fs[ER_def,SYM_def] >> first_x_assum irule >>
 first_x_assum irule >>
 qpick_x_assum ‘ZC(Pa(a1, a2)) = ZC(Pa(a, b))’ (assume_tac o GSYM) >>
 fs[ZC_ZR])
(form_goal “!z a b. Repz(z) = ZC(Pa(a,b)) ==>
 Repz(Negz(z)) = ZC(Pa(b,a))”));


local 
val mulf0IL_def = define_fsym("mulf0IL",[])
(qform2IL [‘abcd:1->(N * N) * N * N’,‘mn:1->N * N’]
   ‘mn  = Pa(Add(Mul(Fst(Fst(abcd)),Fst(Snd(abcd))),
      Mul(Snd(Fst(abcd)),Snd(Snd(abcd)))),Add(Mul(Fst(Fst(abcd)),Snd(Snd(abcd))),
      Mul(Snd(Fst(abcd)),Fst(Snd(abcd)))))’)
val mulf0IL_l =  proved_th $
e0
(fconv_tac (basic_fconv no_conv forall_cross_fconv) >>
 rpt strip_tac >> rw[mulf0IL_def,Holds_def] >>
 rw[o_assoc,Eq_property_TRUE,Pa_distr,p12_of_Pa] >>
 rw[Pair_def'] >>
 rw[Mul_def,Add_def])
(form_goal
 “!abcd:1->(N * N) * N * N mn:1->N * N.
  Holds(mulf0IL,abcd,mn)<=>
  mn  = Pa(Add(Mul(Fst(Fst(abcd)),Fst(Snd(abcd))),
      Mul(Snd(Fst(abcd)),Snd(Snd(abcd)))),Add(Mul(Fst(Fst(abcd)),Snd(Snd(abcd))),
      Mul(Snd(Fst(abcd)),Fst(Snd(abcd)))))”);
val l =
 P2fun' |> qspecl [‘(N * N) * N * N’,‘N * N’]
        |> qspecl [‘mulf0IL’]
        |> conv_rule (depth_fconv no_conv forall_cross_fconv) 
        |> conv_rule (basic_fconv no_conv forall_cross_fconv) 
        |> rewr_rule[mulf0IL_l]
        |> rewr_rule[Pair_def']
in    
val mulf0_def = proved_th $
e0
(irule l >> rpt strip_tac >> uex_tac >>
 qexists_tac ‘Pa(Add(Mul(a', a), Mul(b, b'')), Add(Mul(a', b''), Mul(b, a)))’ >> rw[])
(form_goal “?!f:(N * N) * N * N -> N * N. 
 !a b c d. f o Pa(Pa(a,b),Pa(c,d)) = 
 Pa(Add(Mul(a,c),Mul(b,d)),Add(Mul(a,d),Mul(b,c)))”)
|> qsimple_uex_spec "mulf0" []
|> store_as "mulf0_def";
end


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
Quo_fun |> qspecl [‘(N * N) * (N * N)’,‘N * N’,
                ‘mulf0’,
                ‘prrel(ZR,ZR)’,‘ZR’,
                ‘Z * Z’,‘Z’,
                ‘ipow2(iZ,iZ)’,‘iZ’]
        |> rewr_rule[addz_conds,mulf0_resp]
        |> conv_rule (depth_fconv no_conv forall_cross_fconv)
        |> qsimple_uex_spec "mulz" []
        |> qspecl [‘z1:1->Z’,‘z2:1->Z’]
        |> rewr_rule[rext_def,GSYM IN_EXT,IN_rsi] 



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
 qsuff_tac ‘Pa(Pa(a1, a2), Pa(a3, a4))  = a & Pa(b1,b2) = b’ 
 >-- (qpick_x_assum ‘mulf0 o a = b’ mp_tac >>
      pop_assum_list (K all_tac) >> rpt strip_tac >> arw[]) >>
 arw[])
(form_goal
 “?a1 a2 a3 a4 b1 b2.
     (!x1 x2 x3 x4.
            IN(Pa(Pa(x1,x2),Pa(x3,x4)), 
               ipow2(iZ, iZ) o Pa(z1, z2)) <=>
            Holds(prrel(ZR, ZR), Pa(Pa(a1,a2),Pa(a3,a4)), Pa(Pa(x1,x2),Pa(x3,x4)))) &
        (!n1 n2.
            IN(Pa(n1,n2), iZ o mulz o Pa(z1, z2)) <=> 
            Holds(ZR, Pa(b1,b2), Pa(n1,n2))) &
        mulf0 o Pa(Pa(a1,a2),Pa(a3,a4)) = Pa(b1,b2)”)
|> rewr_rule[ipow2_def,prrel_def,GSYM IN_rsi]



val main_mulz2 = proved_th $
e0
(strip_assume_tac main_mulz1 >>
 qexistsl_tac [‘a1’,‘a2’,‘a3’,‘a4’,‘b1’,‘b2’] >>
 qby_tac ‘iZ o z1 = rsi(ZR,Pa(a1,a2)) & iZ o z2 = rsi(ZR,Pa(a3,a4))’ 
 >-- (irule Pow_conj_eq >> rw[iZ_nonempty] >> 
     depth_fconv_tac no_conv forall_cross_fconv >> arw[]) >>
 arw[] >> rw[GSYM IN_EXT] >> fconv_tac forall_cross_fconv >> arw[])
(form_goal
 “∃a1 a2 a3 a4 b1 b2.
  iZ o z1 = rsi(ZR,Pa(a1,a2)) & iZ o z2 = rsi(ZR,Pa(a3,a4)) &
  iZ o mulz o Pa(z1,z2) = rsi(ZR,Pa(b1,b2)) &
  mulf0 o Pa(Pa(a1, a2), Pa(a3, a4)) = Pa(b1, b2)”)
 



val main_mulz3 = main_mulz2 |> rewr_rule[mulf0_def] 
                            |> store_as "main_mulz3";



val Mulz_def = qdefine_fsym ("Mulz",[‘z1:1->Z’,‘z2:1->Z’])
                            ‘mulz o Pa(z1,z2)’
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
 first_x_assum (qsspecl_then [‘Pa(Pa(a1',a2'),Pa(a3',a4'))’,
               ‘Pa(Pa(a1,a2),Pa(a3,a4))’] assume_tac)  >>
 fs[mulf0_def] >> first_x_assum irule >>
 arw[prrel_def,GSYM ZC_ZR])
(form_goal
 “∀z1 a1 a2.
  Repz(z1) = ZC(Pa(a1,a2)) ⇒
  ∀z2 a3 a4. 
  Repz(z2) = ZC(Pa(a3,a4)) ⇒
  Repz(Mulz(z1,z2)) = 
  ZC(Pa(Add(Mul(a1, a3), Mul(a2, a4)),
          Add(Mul(a1, a4), Mul(a2, a3))))”));

val ZC_Repz = prove_store("ZC_Repz",
e0
(rpt strip_tac >> strip_assume_tac Z_def >>
 fs[GSYM Repz_def,GSYM ZC_def] >> 
 qby_tac ‘?n.  ZC(Pa(a, b)) = ZC(n)’ 
 >-- (qexists_tac ‘Pa(a,b)’ >> rw[]) >>
 first_x_assum (drule o iffLR) >>
 pop_assum strip_assume_tac >> uex_tac >>
 qexists_tac ‘b'’ >> arw[] >> rpt strip_tac >> irule Repz_eq_eq >>
 arw[])
(form_goal
 “!a b.?!z. Repz(z) = ZC(Pa(a,b))”));


val ZC_Repz' = prove_store("ZC_Repz'",
e0
(strip_tac >>
 qsspecl_then [‘ab’] strip_assume_tac Pair_has_comp >>
 arw[ZC_Repz])
(form_goal
 “!ab.?!z. Repz(z) = ZC(ab)”));

val _ = new_fsym2IL1("ZC",rastt "Rsi(ZR)")

val absz_def = 
    P2fun_uex |> qspecl [‘N * N’,‘Z’] 
          |> specl[qform2IL [‘ab:1->N * N’,‘y:1->Z’]
                     ‘Repz(y) = ZC(ab)’]
          |> rewr_rule[Holds_def,Pa_distr,p12_of_Pa,o_assoc,
                       Eq_property_TRUE,
                       GSYM Repz_def,GSYM ZC_def,GSYM rsi_def]
          |> conv_rule (top_depth_fconv no_conv forall_cross_fconv)
          |> C mp ZC_Repz
          |> qsimple_uex_spec "absz" []
          |> store_as "absz_def";

val Absz_def = qdefine_fsym ("Absz",[‘ab:1->N * N’])
                            ‘absz o ab’
                            |> gen_all |> store_as "Absz_def";


val Asz_def = qdefine_fsym ("Asz",[‘a:1->N’,‘b:1->N’])
                            ‘Absz(Pa(a,b))’
                            |> gen_all |> store_as "Asz_def";


val Zc_def = qdefine_fsym ("Zc",[‘a:1->N’,‘b:1->N’])
                            ‘ZC(Pa(a,b))’
                            |> gen_all |> store_as "Zc_def";


val Absz_Repz = absz_def |> qspecl [‘a:1->N’,‘b:1->N’,‘Absz(Pa(a,b))’]
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



(*
val casesz = prove_store("casesz",
e0
(dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qspecl_then [‘z’] strip_assume_tac cases_z >>
     arw[]) >>
 arw[])
(form_goal “(!a b. P(Asz(a,b))) <=> (!z:mem(Z). P(z))”));

maybe not a good choice since need to build IL, better choose Asz by hand, use cases_z instead
*)

(*not such easy to apply since there maybe many vars, need a conv for this*)

 (*[a,b]+0Z=[a,b]*)
val Addz_Oz = prove_store("Addz_Oz",
e0
(strip_tac >>
 qsspecl_then [‘z’] strip_assume_tac cases_z >>
arw[Oz_def,Addz_Asz,Add_O])
(form_goal “!z. Addz(z,Oz) = z”));

val Asz_eq_ZR = prove_store("Asz_eq_ZR",
e0
(rw[GSYM Repz_eq_ZR] >> rw[GSYM Zc_def] >> rpt strip_tac >> dimp_tac >>
 strip_tac
 >-- arw[GSYM Asz_Repz]  >>
 irule Repz_eq_eq >> arw[Asz_Repz])
(form_goal “!a b c d. Asz(a,b) = Asz(c,d) <=> Holds(ZR,Pa(a,b),Pa(c,d))”));

(*[a,b]+(−[a,b])=0Z*)

val Addz_Negz_Oz = prove_store("Addz_Negz_Oz",
e0
(strip_tac >>
 qspecl_then [‘z’] strip_assume_tac cases_z >> arw[] >> 
 rw[Negz_Asz,Addz_Asz,Oz_def] >> rpt strip_tac >>
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
 irule eq_ZR >> rw[Pa_eq_eq] >> strip_tac (* 2 *)
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
(strip_tac >>
 qspecl_then [‘z’] strip_assume_tac cases_z >> 
 arw[Ez_def,En_def,Mulz_Asz,Mul_RIGHT_1,Mul_LEFT_O,Mul_clauses,
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



(*[a,b]≤[c,d] ⇔ a+d≤b+c (⇔ ⟨a,b⟩≤⟨c,d⟩).*)

val le0_def = qdefine_psym ("le0",[‘ab:1->N * N’,‘cd:1->N * N’])
‘Le(Add(Fst(ab),Snd(cd)),Add(Snd(ab),Fst(cd)))’
|> gen_all |> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[Pair_def'] |> store_as "le0_def"; 


val Lez_def = qdefine_psym ("Lez",[‘z1:1->Z’,‘z2:1->Z’])
‘!a b c d.Repz(z1) = Zc(a,b) & Repz(z2) = Zc(c,d) ==>
 Le(Add(a,d),Add(b,c))’ |> gen_all |> store_as "Lez_def";

val LEz_def0 = define_fsym("LEz",[])
(qform2IL [‘z1:1->Z’,‘z2:1->Z’] 
  ‘!a b c d.Repz(z1) = ZC(Pa(a,b)) & Repz(z2) = ZC(Pa(c,d)) ==>
 Le(Add(a,d),Add(b,c))’)


val LEz_def = prove_store("LEz_def",
e0
(rpt strip_tac >> rw[Holds_def,Lez_def] >>
 rw[LEz_def0] >>
 rw[o_assoc,All_def,IMP_def,CONJ_def,Pa_distr] >>
 rw[Eq_property_TRUE] >>
 once_rw[p61_def,p62_def,p63_def,p64_def,p65_def,p66_def] >>
 rw[p12_of_Pa,o_assoc,Pa_distr] >>
 rw[GSYM rsi_def,GSYM Repz_def,Add_def,LE_Le,Zc_def,ZC_def])
(form_goal
 “!z1 z2.Holds(LEz,z1,z2) <=> Lez(z1,z2)”));


val LEz_REFL = prove_store("LEz_REFL",
e0
(rw[REFL_def,LEz_def,Lez_def] >>
 rpt strip_tac >> 
 qsuff_tac ‘Add(a', d) = Add(b, c)’
 >-- (strip_tac >> arw[Le_refl]) >>
 qsuff_tac ‘Holds(ZR,Pa(a',b),Pa(c,d))’
 >-- (rw[ZR_def] >> strip_tac >> arw[] >>
      qspecl_then [‘b’,‘c’] assume_tac Add_comm >> arw[]) >>
 irule $ iffLR ZC_ZR >> fs[Zc_def])
(form_goal “REFL(LEz)”));

val Repz_Zc = rewr_rule[GSYM Zc_def] Repz_ZC |> store_as "Repz_Zc";



val LEz_TRANS = prove_store("LEz_TRANS",
e0
(rw[TRANS_def,LEz_def,Lez_def] >>
 rpt strip_tac >> 
 qspecl_then [‘a2’] strip_assume_tac Repz_Zc >>
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
(form_goal “TRANS(LEz)”));



val LEz_ASYM= prove_store("LEz_ASYM",
e0
(rw[ASYM_def,LEz_def,Lez_def] >>
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
(form_goal “ASYM(LEz)”));


val Total_def = qdefine_psym("Total",[‘R:A*A->1+1’])
‘!a b. Holds(R,a,b) | Holds(R,b,a)’ |> gen_all |> store_as "Total_def";

val Lez_resp0 = prove_store("Lez_resp0",
e0
(qsuff_tac
 ‘!a b c d a' b' c' d'. Holds(ZR,Pa(a,b),Pa(a',b')) &
 Holds(ZR,Pa(c,d),Pa(c',d')) ==> 
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
(form_goal “!a b c d e f g h.Holds(ZR,Pa(a,b),Pa(c,d)) & 
 Holds(ZR,Pa(e,f),Pa(g,h)) ==>
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
(form_goal “!z1 z2 z3. Lez(z1,z2) ==> Lez(Addz(z1,z3),Addz(z2,z3))”));


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

