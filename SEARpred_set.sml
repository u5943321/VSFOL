
val tof_Tpm_inv = prove_store("tof_Tpm_inv",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT] >>
 rw[GSYM tof_def,Tpm_def])
(form_goal
 “!A B f:A->B. tof(Tpm(f))  = f”));


val Tpm_tof_inv = prove_store("Tpm_tof_inv",
e0
(flip_tac >> rpt strip_tac >> irule is_Tpm >>
 rw[tof_def])
(form_goal
 “!A B f:mem(Exp(A,B)). Tpm(tof(f))  = f”));


val Tpm_eq_eq = prove_store("Tpm_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >> 
 irule $ iffLR FUN_EXT >>
 once_rw[GSYM Tpm_def] >> arw[])
(form_goal “!A B f1:A->B f2. Tpm(f1) = Tpm(f2) <=> f1 = f2”));


val tof_eq_eq = prove_store("tof_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘Tpm(tof(f)) = Tpm(tof(g))’ >-- arw[]>> fs[Tpm_tof_inv] )
(form_goal
 “!A B f:mem(Exp(A,B)) g. tof(f)  = tof(g) <=> f = g”));



val IN_Sing = prove_store("IN_Sing",
e0
(rw[Sing_def,Sg_def])
(form_goal “!A a0 a:mem(A). IN(a,Sing(a0)) <=> a = a0”));

 
val EMPTY_def = qdefine_psym("EMPTY",[‘A’])
‘!x:mem(A).F’

val BU_ex = prove_store("BU_ex",
e0
(strip_tac >>
 qsuff_tac
 ‘?BU:Pow(Pow(A)) -> Pow(A). 
  !sss a:mem(A). IN(a,App(BU,sss)) <=>
  ?ss.IN(ss,sss) & IN(a,ss)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘BU’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >> strip_tac >>
     irule IN_EXT >> arw[]) >>
 irule 
 (P2fun' |> qspecl [‘Pow(Pow(A))’,‘Pow(A)’]
 |> fVar_sInst_th “P(sss:mem(Pow(Pow(A))),u:mem(Pow(A)))”
    “!a:mem(A). IN(a,u) <=>
           (?ss.IN(ss,sss) & IN(a,ss))”) >>
 strip_tac >>
 accept_tac (IN_def_P |> qspecl [‘A’] |> fVar_sInst_th “P(a:mem(A))”
 “ (?ss.IN(ss,x) & IN(a:mem(A),ss))”)
 )
(form_goal
 “!A. ?!BU:Pow(Pow(A)) -> Pow(A). 
  !sss a:mem(A). IN(a,App(BU,sss)) <=>
  ?ss.IN(ss,sss) & IN(a,ss)”));
 

val BU_def = BU_ex |> spec_all |> uex2ex_rule
                         |> qSKOLEM "BU" [‘A’]
                         |> gen_all
                         |> store_as "BU_def"; 


val BIGUNION_def = qdefine_fsym("BIGUNION",[‘sss:mem(Pow(Pow(A)))’])
‘App(BU(A),sss)’ |> gen_all |> store_as "BIGUNION_def";


val IN_BIGUNION = BU_def |> rewr_rule[GSYM BIGUNION_def] 
                         |> store_as "IN_BIGUNION";

 


val Inj_ex_uex = prove_store("Inj_ex_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- first_x_assum (accept_tac o uex2ex_rule) >>
 uex_tac >> qexists_tac ‘a’ >> arw[] >> rpt strip_tac >>
 fs[Inj_def] >> first_x_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !b. (?!a.App(f,a) = b) <=> (?a.App(f,a) = b)”));


val IMAGE_o = prove_store("IMAGE_o",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IMAGE_def] >> strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘App(f,a)’ >> arw[GSYM App_App_o] >>
     qexists_tac ‘a’ >> arw[]) >>
 qexists_tac ‘a'’ >> arw[App_App_o])
(form_goal “!A B f:A->B C g:B->C s:mem(Pow(A)). IMAGE(g o f,s) = IMAGE(g,IMAGE(f,s))”));



val ex_eq_IMAGE = prove_store("ex_eq_IMAGE",
e0
(rpt strip_tac >>
 strip_assume_tac
 (IN_def_P_ex |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a:mem(A))”
    “IN(App(f:A->B,a),s)”) >>
 qexists_tac ‘s'’ >>
 pop_assum (assume_tac o GSYM) >>
 rw[GSYM IN_EXT_iff] >> strip_tac >> 
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[IMAGE_def] >> arw[] >> 
     first_x_assum drule >>
     pop_assum strip_assume_tac >> 
     qexists_tac ‘a’ >> fs[]) >>
 fs[IMAGE_def] >> rfs[])
(form_goal “!A B f:A->B s:mem(Pow(B)).
 (!b. IN(b,s) ==> ?a. b = App(f,a)) ==>
 ?s0:mem(Pow(A)). s = IMAGE(f,s0) ”));

val App_IN_IMAGE = prove_store("App_IN_IMAGE",
e0
(rw[IMAGE_def] >> rpt strip_tac >>
 qexists_tac ‘a’ >> arw[])
(form_goal “!A B f:A->B s a. IN(a,s) ==> IN(App(f,a),IMAGE(f,s))”));


val IMAGE_BIGUNION = prove_store("IMAGE_BIGUNION",
e0
(cheat)
(form_goal
 “!A B f:A->B ss.IMAGE(f,BIGUNION(ss)) = BIGUNION(IMAGE(Image(f),ss))”));


val App_Prla = prove_store("App_Prla",
e0
(rpt strip_tac >> rw[Prla_def,App_Pa_Pair] >>
 rw[App_App_o,p12_of_Pair] )
(form_goal “!A B f:A->B X Y g:X->Y a x.App(Prla(f,g),Pair(a,x)) = 
Pair(App(f,a),App(g,x))”));

val p2_comm = prove_store("p2_comm",
e0
(rw[GSYM FUN_EXT] >>
 rpt strip_tac >>
 qsspecl_then [‘a’] strip_assume_tac Pair_has_comp >>
 arw[App_App_o,App_Prla,p12_of_Pair])
(form_goal “!A B C f:B->C. f o p2(A,B) = p2(A,C) o Prla(Id(A),f)”));


val p1_comm = prove_store("p1_comm",
e0
(cheat)
(form_goal “!A B C f:A->C. f o p1(A,B) = p1(C,B) o Prla(f,Id(B))”));



val p1_Prla = prove_store("p1_Prla",
e0
(cheat)
(form_goal “!A X f:A->X B Y g:B->Y. p1(X,Y) o Prla(f,g) = f o p1(A,B)”));

val IMAGE_Prla = prove_store("IMAGE_Prla",
e0
(rpt strip_tac >> rw[IMAGE_def] >> 
 fconv_tac (redepth_fconv no_conv exists_cross_fconv) >>
 rw[App_Prla,Pair_eq_eq])
(form_goal “!A X f:A->X B Y g:B->Y x y s.
 IN(Pair(x,y), IMAGE(Prla(f,g),s)) <=> 
 ?a b. IN(Pair(a,b),s) & x = App(f,a) & y = App(g,b)”));

val Image_IMAGE = prove_store("Image_IMAGE",
e0
(rw[GSYM IN_EXT_iff,IMAGE_def,Image_def])
(form_goal “!A B f:A->B s. App(Image(f),s) = IMAGE(f,s)”));

(*
val eq_m2s_Eqv = prove_store("eq_m2s_Eqv",
e0
(cheat)
(form_goal “!A s1 s2:mem(Pow(A)). s1 = s2 ==>
 Eqv(m2s(s1),m2s(s2))”));
*)


val IMAGE_Empty_Empty = prove_store("IMAGE_Empty_Empty",
e0
(cheat)
(form_goal “!A B f:A->B s. IMAGE(f,s) = Empty(B) <=> s = Empty(A)”));


val BIGUNION_Empty_Empty = prove_store("BIGUNION_Empty_Empty",
e0
(cheat)
(form_goal “!A ss. BIGUNION(ss) = Empty(A) <=> 
 (!s. IN(s,ss) ==> s = Empty(A))”));


val BIGUNION_Empty_Empty' = prove_store("BIGUNION_Empty_Empty'",
e0
(cheat)
(form_goal “!A ss. Empty(A) = BIGUNION(ss)  <=> 
 (!s. IN(s,ss) ==> s = Empty(A))”));


val IN_NONEMPTY = prove_store("IN_NONEMPTY",
e0
(rw[GSYM IN_EXT_iff,Empty_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[]) >>
 ccontra_tac >>
 qsuff_tac ‘!a. ~IN(a,s)’ >-- arw[] >>
 strip_tac >> ccontra_tac >>
 qsuff_tac ‘?a. IN(a,s)’ >--arw[] >>
 qexists_tac ‘a’ >> arw[])
(form_goal “!A s. (?a. IN(a,s)) <=> ~(s = Empty(A))”));



val INTER_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qspecl [‘Pow(A) * Pow(A)’,‘Pow(A)’] 
           |> fVar_sInst_th 
           “P(s12:mem(Pow(A) * Pow(A)),s:mem(Pow(A)))”
           “!a. IN(a,s) <=> IN(a:mem(A),Fst(s12)) & IN(a,Snd(s12))”
           |> conv_rule (depth_fconv no_conv forall_cross_fconv)
           |> rewr_rule[Pair_def']) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a':mem(A))”
    “IN(a':mem(A),a) & IN(a',b)”) >> arw[])
(form_goal “!A. ?!f:Pow(A) * Pow(A) -> Pow(A).
 !s1 s2 a. IN(a,App(f,Pair(s1,s2))) <=> IN(a,s1) & IN(a,s2)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "INTER" [‘A’]

val Inter_def = qdefine_fsym("Inter",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘App(INTER(A),Pair(s1,s2))’ 



val UNION_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qspecl [‘Pow(A) * Pow(A)’,‘Pow(A)’] 
           |> fVar_sInst_th 
           “P(s12:mem(Pow(A) * Pow(A)),s:mem(Pow(A)))”
           “!a. IN(a,s) <=> IN(a:mem(A),Fst(s12)) | IN(a,Snd(s12))”
           |> conv_rule (depth_fconv no_conv forall_cross_fconv)
           |> rewr_rule[Pair_def']) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a':mem(A))”
    “IN(a':mem(A),a) | IN(a',b)”) >> arw[])
(form_goal “!A. ?!f:Pow(A) * Pow(A) -> Pow(A).
 !s1 s2 a. IN(a,App(f,Pair(s1,s2))) <=> IN(a,s1) | IN(a,s2)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "UNION" [‘A’]

val IN_Inter = prove_store("IN_Inter",
e0
(rw[Inter_def,INTER_def])
(form_goal “!A s1 s2 a. IN(a:mem(A),Inter(s1,s2)) <=> IN(a,s1) & IN(a,s2)”));


val COMPL_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qspecl [‘Pow(A)’,‘Pow(A)’] 
           |> fVar_sInst_th 
           “P(s0:mem(Pow(A)),s:mem(Pow(A)))”
           “!a. IN(a,s) <=> ~IN(a:mem(A),s0)”) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a':mem(A))”
    “~IN(a':mem(A),x)”) >> arw[])
(form_goal “!A. ?!f:Pow(A) -> Pow(A).
 !s a. IN(a,App(f,s)) <=> ~IN(a,s)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "COMPL" [‘A’]

val Compl_def = qdefine_fsym("Compl",[‘s:mem(Pow(A))’])
‘App(COMPL(A),s)’

val IN_Compl = prove_store("IN_Compl",
e0
(rw[Compl_def,COMPL_def])
(form_goal “!A s a. IN(a:mem(A),Compl(s)) <=> ~IN(a,s)”));


val Union_def = qdefine_fsym("Union",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘App(UNION(A),Pair(s1,s2))’



val m2r_def = AX1 |> qspecl [‘A’,‘A’]
                  |> fVar_sInst_th “P(x:mem(A),y:mem(A))”
                  “IN(Pair(x,y),od:mem(Pow(A * A)))”
                  |> uex2ex_rule 
                  |> qSKOLEM "m2r" [‘od’] 
                  |> qspecl [‘a1:mem(A)’,‘a2:mem(A)’]
                  |> gen_all

val r2m_def = 
    IN_def_P |> qspecl [‘A * A’]
             |> fVar_sInst_th “P(a12:mem(A * A))”
             “Holds(R:A~>A,Fst(a12),Snd(a12))” 
             |> uex2ex_rule 
             |> qSKOLEM "r2m" [‘R’] 
             |> qspecl [‘Pair(a1:mem(A),a2:mem(A))’]
             |> rewr_rule [Pair_def']
             |> gen_all


val IN_Union = prove_store("IN_Union",
e0
(rw[Union_def,UNION_def])
(form_goal “!A s1 s2 a:mem(A). IN(a,Union(s1,s2)) <=> IN(a,s1) | IN(a,s2)”));
 
val Union_Empty_Empty = prove_store("Union_Empty_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Union,Empty_def])
(form_goal “!A. Union(Empty(A),Empty(A)) = Empty(A)”));


val SS_Refl = prove_store("SS_Refl",
e0
(rw[SS_def])
(form_goal “!A s:mem(Pow(A)). SS(s,s)”));


val NONE_def = qdefine_fsym("NONE",[‘X’])
‘App(i2(X,1),dot)’

val Null_def = proved_th $
e0
(strip_tac >> rw[GSYM NONE_def] >>
 qsuff_tac
 ‘?f:N->X+1.!n. App(f,n) = NONE(X)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rw[GSYM FUN_EXT] >> rpt strip_tac >> arw[]) >>
 assume_tac (P2fun' |> qspecl [‘N’,‘X + 1’] 
 |> fVar_sInst_th “P(n:mem(N),x1:mem(X+1))” “x1 = NONE(X)”) >>
 first_x_assum irule >> strip_tac >> uex_tac >> qexists_tac ‘NONE(X)’ >>
 rw[] >> rpt strip_tac >> arw[])
(form_goal “!X. ?!f:N->X+1.!n. App(f,n) = App(i2(X,1),dot)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Null" [‘X’]
|> gen_all


val SOME_def = qdefine_fsym("SOME",[‘a:mem(A)’])
‘App(i1(A,1),a)’ |> gen_all
