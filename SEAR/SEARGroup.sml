
val np_def = qdefine_fsym("np",[‘m:G * G ->G’,‘e:mem(G)’,‘x:mem(G)’])
‘Nrec(e,Ap1(m,x))’

val np_O = Nrec_O |> qsspecl [‘e:mem(G)’,‘Ap1(m:G * G->G,x)’]
                  |> rewr_rule[GSYM np_def]

val np_Suc = Nrec_Suc |> qsspecl [‘e:mem(G)’,‘Ap1(m:G * G->G,x)’,‘n:mem(N)’]
                      |> rewr_rule[GSYM np_def]



val Ltz_def = qdefine_psym("Ltz",[‘z1:mem(Z)’,‘z2:mem(Z)’])
‘Lez(z1,z2) & ~(z1 = z2)’ |> gen_all

(*extend lambda tool into !z. ?n. .... ==> 
absolute value of a int *)

(*
val Abv_ex = proved_th $
e0
(cheat)
(form_goal 
 “!z. (Lez(Oz,z) ==> ?!n. z = Asz(n,O))  &
      (Ltz(z,Oz) ==> ?!n. z = Asz(O,n)) ”)
*)

val Abv_def = proved_th $
e0
(cheat)
(form_goal 
 “!z. ?!n. (Lez(Oz,z) & z = Asz(n,O)) | 
           (Ltz(z,Oz) & z = Asz(O,n))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Abv" [‘z’] 
|> gen_all

val Abv_nonneg = prove_store("Abv_nonneg",
e0
cheat
(form_goal 
 “!z. Lez(Oz,z) ==> z = Asz(Abv(z),O) ”));



val zp_def = proved_th $
e0
cheat
(form_goal 
“!g:mem(Grp(G)). ?!f:G * Z -> G.
 !gz. 
 (Lez(Oz,Snd(gz)) ==> App(f,gz) = App(np(mof(g),eof(g),Fst(gz)),Abv(Snd(gz)))) &
 (Ltz(Snd(gz),Oz) ==> App(f,gz) = App(iof(g),App(np(mof(g),eof(g),Fst(gz)),Abv(Negz(Snd(gz))))) )”)
|> spec_all |> uex2ex_rule |> qSKOLEM "zp" [‘g’]

val gpw_def = qdefine_fsym("gpw",[‘g:mem(Grp(G))’,‘x:mem(G)’,‘z:mem(Z)’])
‘App(zp(g),Pair(x,z))’



val cyc_def = qdefine_psym("cyc",[‘g:mem(Grp(G))’])
‘?a. !x. ?z. x = gpw(g,a,z)’ |> gen_all

(*can define a set Ghom(g1,g2), and say f:mem(Ghom(g1,g2)) ==> ...
 but then run into the trouble with equalities.*)


(*
By the Division Theorem, it is possible to find integers 𝑞 and 𝑟 such that 𝑛=𝑚𝑞+𝑟 with 0≤𝑟<𝑚.
*)

val Subz_def = qdefine_fsym("Subz",[‘a:mem(Z)’,‘b:mem(Z)’])
‘Addz(a,Negz(b))’

val ghom_gpw = prove_store("ghom_gpw",
e0
(cheat)
(form_goal “!f:G1 -> G2 g1 g2. ghom(f,g1, g2) ==>
 !x z. App(f,gpw(g1,x,z)) = gpw(g2,App(f,x),z)”));

val gpow_Mulz = prove_store("gpow_Mulz",
e0
cheat
(form_goal
 “!G g:mem(Grp(G)) a. gpw(g, a, Mulz(z1, z2)) = gpw(g, gpw(g, a, z1), z2)”));

val Addz_eq_O = prove_store("Addz_eq_O",
e0
cheat
(form_goal “!a b. Addz(a,b) = a <=> b = Oz”));

val N2Z_def = fun_tm_compr ("n",mem_sort (rastt "N")) (rastt "Asz(n,O)")
|> qSKOLEM "N2Z" []

val n2z_def = qdefine_fsym("n2z",[‘n:mem(N)’]) ‘App(N2Z,n)’ |> gen_all

val division_theorem = prove_store("division_theorem",
e0
cheat
(form_goal 
 “!a b:mem(Z).~(b = Oz) ==> ?!q r. a = Addz(Mulz(q,b),r) & 
  Lez(Oz,r) & Ltz(r,n2z(Abv(b)))”));

val n2z_nonneg = prove_store("n2z_nonneg",
e0
cheat
(form_goal “!z. Lez(Oz,z) ==> n2z(Abv(z)) = z”));


val gmul_gpw = prove_store("gmul_gpw",
e0
cheat
(form_goal “!G g:mem(Grp(G)) a z1 z2. gmul(g,gpw(g,a,z1),gpw(g,a,z2)) = gpw(g,a,Addz(z1,z2))”));


val Mulz_Negz_2 = prove_store("Mulz_Negz_2",
e0
cheat
(form_goal “!a b. Mulz(a,Negz(b)) = Negz(Mulz(a,b))”));

val sub_cyc_cyc = prove_store("sub_cyc_cyc",
e0
((*rpt strip_tac >>
 qcases ‘!x:mem(H). x = eof(h)’
 >-- cheat >>
 fs[cyc_def] >>
 qby_tac ‘?m. ?x0. App(i,x0) = gpw(g,a,m) & Ltz(Oz,m) & 
   !m'. (?x0. App(i,x0) = gpw(g,a,m') & Ltz(Oz,m')) ==> Lez(m,m')  ’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘x0’ >> strip_tac >>
 qby_tac ‘?n. App(i,x) = gpw(g,a,n)’ 
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qby_tac ‘~(m = Oz)’
 >-- (fs[Ltz_def] >> ccontra_tac >> fs[]) >>
 qsspecl_then [‘n’,‘m’] assume_tac division_theorem >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 pop_assum (strip_assume_tac o uex2ex_rule) >> 
 qsuff_tac ‘r = Oz’ 
 >-- (strip_tac >> fs[Addz_Oz] >> qexists_tac ‘q’ >>
     drule Inj_eq_eq >> first_x_assum (irule o iffLR) >> arw[] >>
     drule ghom_gpw >> arw[] >> rw[GSYM gpow_Mulz] >>
     qsspecl_then [‘m’,‘q’] assume_tac Mulz_comm >> arw[]) >>
 qsuff_tac ‘?x0. App(i,x0) = gpw(g,a,r)’ 
 >-- (strip_tac >>
     qby_tac ‘n2z(Abv(m)) = m’
     >-- (irule n2z_nonneg >> fs[Ltz_def] >> fs[]) >>
     first_x_assum (qspecl_then [‘r’] assume_tac) >>  
     ccontra_tac >>
     qsuff_tac ‘Lez(m, r)’ (*Ltz(r, m) is already in assum*) 
     >-- cheat >>
     first_x_assum irule >> (*arw[Ltz_def] does not respond, tactic bug*)
     rw[Ltz_def] >> (*arw[] here does not eliminate Oz <= r, why?*)
     qexists_tac ‘x0'’ >> arw[] >> flip_tac >> arw[]) >>
 qexists_tac ‘gmul(h,x,gpw(h,x0,Negz(q)))’ >>
 drule $ iffLR ghom_def >> drule ghom_gpw >> arw[] >>
 rw[gmul_gpw,GSYM gpow_Mulz,Mulz_Negz_2] >>
 qsuff_tac 
 ‘Addz(Addz(Mulz(q, m), r), Negz(Mulz(m, q))) = r’ 
 >-- (strip_tac >> arw[]) >>
 cheat *) cheat)
(form_goal “!H h:mem(Grp(H)) G g:mem(Grp(G)) i:H -> G.
 ghom(i,h,g) & Inj(i) & cyc(g) ==> cyc(h)”));

(*analogue of that of functions, have a fun_tm_compr version of defining sets*)

(*exists a function Grp(G) -> Pow(Pow(G)), sending each group to the set of its subgroups. *)


val lcst_def = proved_th $
e0
cheat
(form_goal “!G g H a:mem(G). 
 ?!lc. !x. IN(x,lc) <=> ?h. IN(h,H) & x = gmul(g,a,h)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "lcst" [‘g’,‘a’,‘H’]

val rcst_def = proved_th $
e0
cheat
(form_goal “!G g H a:mem(G). 
 ?!lc. !x. IN(x,lc) <=> ?h. IN(h,H) & x = gmul(g,h,a)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "rcst" [‘g’,‘H’,‘a’]



val cstR_def = 
AX1 |> qspecl [‘G’,‘G’] |> uex2ex_rule
    |> fVar_sInst_th “P(g1:mem(G),g2:mem(G))”
    “lcst(g:mem(Grp(G)),g1,H) = lcst(g:mem(Grp(G)),g2,H)”
    |> qSKOLEM "cstR" [‘g’,‘H’] 
    |> store_as "cstR_def";


val cstR_Refl = prove_store("cst_Refl",
e0
(cheat)
(form_goal
 “Refl(cstR(g,H:mem(Pow(G))))”));


val cstR_Sym = prove_store("cst_Sym",
e0
(cheat)
(form_goal
 “Sym(cstR(g,H:mem(Pow(G))))”));

val ER_cstR = prove_store("ER_cstR",
e0
(cheat)
(form_goal “!G g H.ER(cstR(g,H:mem(Pow(G))))”));




(*the set Pow(G) is not naturally equipped with a group structure and therefore there makes no sense to construct quotient group as subgroup of sth, alternative solution is to do HOL approach, think it will be less pretty *)

(*Qc for quotient carrier*)

val Qc_def = Thm_2_4 |> qspecl [‘Pow(G)’]
                    |> fVar_sInst_th “P(s:mem(Pow(G)))”
                    “?a. s = rsi(cstR(g,H:mem(Pow(G))),a)”
                    |> qSKOLEM "Qc" [‘g’,‘H’]
                    |> qSKOLEM "iQc" [‘g’,‘H’]
                    |> store_as "Qc_def";

val iQc_Inj = Qc_def |> conjE1 |> gen_all

val Rcs_def = qdefine_fsym("Rcs",[‘cs:mem(Qc(g:mem(Grp(G)),H:mem(Pow(G))))’])
‘App(iQc(g,H),cs)’


(*
val Qc_mem_ex = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?a:Qc(g:mem(Grp(G)),H:mem(Pow(G))).  ’)
(form_goal “!g H:mem(Pow(G)) x. IN(x,H) ==>
 ?a:Qc(g:mem(Grp(G)),H:mem(Pow(G))).T”)

rastt "k:mem(Qc(g,H))"

rastt "Qc(g,H)"

mk_var ("a",(mem_sort (rastt "Qc(g,H)")))
*)

val mof_resp = prove_store("mof_resp",
e0
(rw[resp_def] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[prrel_def] >> rpt strip_tac >> fs[cstR_def,GSYM gmul_def,GSYM mul_def] >>
 fs[isnml_def] >>
 cheat)
(form_goal “isnml(h,g) ==> resp(mof(g:mem(Grp(G))),prrel(cstR(H),cstR(H)),cstR(H))”));

val qmul_conds = proved_th $
e0
(cheat)
(form_goal
“isnml(H,g) ==> ER(prrel(cstR(g,H) ,cstR(g,H))) &
      ER(cstR(g,H)) &
 resp(mof(g:mem(Grp(G))),prrel(cstR(g,H),cstR(g,H)),cstR(g,H)) &
      Inj(ipow2(iQc(g,H), iQc(g,H))) &
      Inj(iQc(g,H)) & Quo(prrel(cstR(g,H),cstR(g,H)), ipow2(iQc(g,H), iQc(g,H))) & Quo(cstR(g,H), iQc(g,H))”)

(*if H nonempty then have element*)

val quoeth = proved_th $
e0
cheat
(form_goal “!A. ?f:A * A->A. T”)


val Quo_fun_iff = prove_store("Quo_fun_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rfs[rext_def] >> 
     first_x_assum 
     (qspecl_then [‘q1’] (x_choosel_then ["a0","b0"] assume_tac)) >>
     fs[App_App_o] >> 
     irule $ iffRL rsi_eq_ER >> arw[] >>
     fs[resp_def] >> 
     first_x_assum (qspecl_then [‘a0’,‘a’] assume_tac) >>
     rfs[] >> first_x_assum irule >> 
     irule $ iffLR rsi_eq_ER >> arw[]) >>
 rw[rext_def,App_App_o] >>
 fs[Quo_def] >>
 qby_tac ‘?!q.  App(i1, q1) =  App(i1, q)’ >-- cheat
 (* cheat : injectivity*) >>
 rfs[] >> qexistsl_tac [‘a’,‘App(f,a)’] >> rw[] >>
 first_x_assum irule >> arw[])
(form_goal
“!A B f:A->B r1:A~>A r2:B~>B
 Q1 Q2 i1:Q1->Pow(A) i2:Q2->Pow(B). 
 ER(r1) & ER(r2) & resp(f,r1,r2) & Inj(i1) & Inj(i2) &
 Quo(r1,i1) & Quo(r2,i2) ==>
 (!qf:Q1->Q2.
 (!q1:mem(Q1). Holds(rext(f,r1,r2),App(i1,q1),App(i2 o qf,q1))) <=> 
 (!a q1. App(i1,q1) = rsi(r1,a) ==> App(i2,App(qf,q1)) = rsi(r2,App(f,a))))”))




val Quo_fun_alt = prove_store("Quo_fun_alt",
e0
(rpt gen_tac >> disch_tac >> drule Quo_fun >> 
 drule Quo_fun_iff >> fs[] >>
 qexists_tac ‘qf’ >> arw[])
(form_goal
“!A B f:A->B r1:A~>A r2:B~>B
 Q1 Q2 i1:Q1->Pow(A) i2:Q2->Pow(B). 
 ER(r1) & ER(r2) & resp(f,r1,r2) & Inj(i1) & Inj(i2) &
 Quo(r1,i1) & Quo(r2,i2) ==>
 ?qf.
 (!a q1. App(i1,q1) = rsi(r1,a) ==> App(i2,App(qf,q1)) = rsi(r2,App(f,a)))”))


(*
val rext_def' = proved_th $
e0
(cheat)
(form_goal
 “ Holds(rext(f:A->B, r1, r2), s1, s2) <=>
        ?ra rb.
          s1 = rsi(r1, ra) & s2 = rsi(r2, rb) & App(f, ra) = rb”)

*)




val qtop_def00 = 
Quo_fun_alt |> qspecl [‘G * G’,‘G’,
                ‘mof(g:mem(Grp(G)))’,
                ‘prrel(cstR(g,H),cstR(g,H:mem(Pow(G))))’,
                ‘cstR(g,H:mem(Pow(G)))’,
                ‘Qc(g,H:mem(Pow(G))) * Qc(g,H:mem(Pow(G)))’,‘Qc(g,H:mem(Pow(G)))’,
                ‘ipow2(iQc(g, H),iQc(g, H:mem(Pow(G))))’,
                ‘iQc(g, H:mem(Pow(G)))’]
|> C mp (undisch qmul_conds)
|> SKOLEM (quoeth |> qspecl [‘Qc(g,H:mem(Pow(G)))’])
           "qtop" [("g",mem_sort (rastt "Grp(G)")),("H",mem_sort (rastt "Pow(G)"))]
|> conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[GSYM IN_EXT_iff,IN_rsi,cstR_def]       
|>  conv_rule (depth_fconv no_conv forall_cross_fconv)
|> rewr_rule[ipow2_def]
|> rewr_rule[prrel_def]
|> rewr_rule[cstR_def]
|> rewr_rule[GSYM gmul_def,GSYM mul_def]
|> rewr_rule[IN_EXT_iff]
|> qspecl [‘a:mem(G)’,‘b:mem(G)’,‘cs1:mem(Qc(g, H))’,‘cs2:mem(Qc(g, H))’]
|> rewr_rule[GSYM Rcs_def]
|> gen_all
|> disch_all |> gen_all

(*representative function allows us to pick up representatives up to equivalence?*)


val cs_Rcs = prove_store("cs_Rcs",
e0
(cheat)
(form_goal
 “!a.?!cs:mem(Qc(g,H)). Rcs(cs) = rsi(cstR(g,H:mem(Pow(G))),a)”));

val csof_def = P2fun |> qspecl [‘G’,‘Qc(g:mem(Grp(G)),H:mem(Pow(G)))’]
                   |> fVar_sInst_th “P(a:mem(G),cs:mem(Qc(g:mem(Grp(G)),H:mem(Pow(G)))))”
                      “Rcs(cs:mem(Qc(g:mem(Grp(G)),H:mem(Pow(G))))) = rsi(cstR(g,H:mem(Pow(G))),a)”
                   |> C mp cs_Rcs
                   |> qSKOLEM "csof" [‘g’,‘H’]
                   |> store_as "csof_def";


val Csof_def = qdefine_fsym ("Csof",
                             [‘g:mem(Grp(G))’,‘H:mem(Pow(G))’,‘a:mem(G)’])
                            ‘App(csof(g,H),a)’
                            |> gen_all |> store_as "Csof_def";


val qmul_def = qdefine_fsym("qmul",[‘g:mem(Grp(G))’,‘H:mem(Pow(G))’,
                                    ‘cs1:mem(Qc(g:mem(Grp(G)),H:mem(Pow(G))))’,
                                    ‘cs2:mem(Qc(g:mem(Grp(G)),H:mem(Pow(G))))’])
                           ‘App(qtop(g,H),Pair(cs1,cs2))’



                           
val Rcs_Csof = 
csof_def |> qspecl [‘a:mem(G)’,‘App(csof(g, H), a:mem(G))’] 
|> rewr_rule[GSYM Csof_def]|>  gen_all


(*
val cs
rw[Rcs_Csof,IN_rsi] 
“!x x0:mem(G).Holds(cstR(g,H),x0,x) <=> IN(x, Rcs(Csof(g, H, x0)))”
*)

(*TODO: iffLR dest the deepest one... *)

val qtop_char = prove_store("qtop_char",
e0
(rpt strip_tac >> drule qtop_def00 >>
  pop_assum (qsspecl_then [‘a’,‘b’,‘Csof(g:mem(Grp(G)), H:mem(Pow(G)), a)’,
                          ‘Csof(g:mem(Grp(G)), H:mem(Pow(G)), b)’] 
                             assume_tac) >>
 qsuff_tac
 ‘!x.
    IN(x, Rcs(mul(qtop(g, H), Csof(g, H, a), Csof(g, H, b)))) <=>
    lcst(g, gmul(g, a, b), H) = lcst(g, x, H)’
 >-- (strip_tac >> rw[qmul_def,GSYM mul_def] >> 
     irule $ iffLR Inj_eq_eq >>
     qexistsl_tac [‘Pow(G)’,‘iQc(g,H)’] >>
     rw[GSYM Rcs_def,Qc_def] >>
     rw[GSYM IN_EXT_iff] >> arw[] >> 
     rw[GSYM cstR_def] >> rw[Rcs_Csof,IN_rsi]) >>
 first_x_assum irule >>
 cheat (*should be easy*))
(form_goal
 “!G g H:mem(Pow(G)). isnml(H,g) ==> !a b. 
 qmul(g,H,Csof(g,H,a),Csof(g,H,b)) = Csof(g,H,gmul(g,a,b))”));

(*just preimage*)
val ker_def = proved_th $
e0
cheat
(form_goal “!G1 G2 f:G1->G2 g1:mem(Grp(G1)) g2:mem(Grp(G2)). 
 ?!k:mem(Pow(G1)). !x. IN(x,k) <=> App(f,x) = eof(g2)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "ker" [‘f’,‘g1’,‘g2’]

(*
 Suppose that G1 and G2 are groups. Suppose that f is
a homomorphism from G1 to G2. Suppose f is onto from G1 to G2. Suppose K is the
kernel of f. Then, K is a normal subgroup of G1; there is a homomorphism g from G1/K
onto G2; and, g is injective.

*)



val iof_resp = prove_store("iof_resp",
e0
(cheat)
(form_goal “isnml(h,g) ==> resp(iof(g:mem(Grp(G))),cstR(g,H),cstR(g,H))”));

val qinv_conds = proved_th $
e0
(cheat)
(form_goal
“isnml(H,g:mem(Grp(G))) ==>
 ER(cstR(g, H)) &
      ER(cstR(g, H)) &
      resp(iof(g), cstR(g, H), cstR(g, H)) &
      Inj(iQc(g, H)) &
      Inj(iQc(g, H)) &
      Quo(cstR(g, H), iQc(g, H)) & Quo(cstR(g, H), iQc(g, H))”)


val has_endo = proved_th $
e0
cheat
(form_goal “!A. ?f:A ->A. T”)

val qinv_def00 = 
Quo_fun_alt |> qspecl [‘G’,‘G’,
                ‘iof(g:mem(Grp(G)))’,
                ‘cstR(g,H:mem(Pow(G)))’,
                ‘cstR(g,H:mem(Pow(G)))’,
                ‘Qc(g,H:mem(Pow(G)))’,‘Qc(g,H:mem(Pow(G)))’,
                ‘iQc(g, H:mem(Pow(G)))’,
                ‘iQc(g, H:mem(Pow(G)))’]
|> C mp (undisch qinv_conds)
|> SKOLEM (has_endo |> qspecl [‘Qc(g,H:mem(Pow(G)))’])
           "qinv" [("g",mem_sort (rastt "Grp(G)")),("H",mem_sort (rastt "Pow(G)"))]
|> rewr_rule[GSYM Rcs_Csof]
|> qspecl [‘a:mem(G)’,‘Csof(g,H,a:mem(G))’]
|> rewr_rule[GSYM Rcs_def,GSYM ginv_def]





val qg_isgrp = proved_th $
e0
cheat
(form_goal
“!G g H:mem(Pow(G)). isnml(H,g) ==> 
 isgrp(Pair(Tpm(qtop(g,H)),Pair(Tpm(qinv(g,H)), Csof(g,H,eof(g)))))”)

val isgrp_mem_Grp = prove_store("isgrp_mem_Grp",
e0
cheat
(form_goal
     “!G g0.isgrp(g0) ==> ?!g:mem(Grp(G)). g0 = RepG(g)”));


val Qc_mem_ex = prove_store("Qc_mem_ex",
e0
(rpt strip_tac >>
qsuff_tac
 ‘?a0 a. a0 = App(iQc(g,H),a) ’ 
>-- cheat >>
(*TODO: simplifier, if swap order of a0, a, does not work*)
rw[GSYM Qc_def] >>
qexistsl_tac [‘rsi(cstR(g, H), eof(g))’,‘eof(g)’] >> rw[])
(form_goal
“!G g H. ?a:mem(Qc(g:mem(Grp(G)),H:mem(Pow(G)))). T”));


val Grp_Qc_ex = prove_store("Grp_Qc_ex",
e0
cheat
(form_goal “!G g H. ?a:mem(Grp(Qc(g:mem(Grp(G)),H:mem(Pow(G))))). T”))

val Qg_def = isgrp_mem_Grp |> qspecl [‘Qc(g:mem(Grp(G)),H:mem(Pow(G)))’,‘Pair(Tpm(qtop(g:mem(Grp(G)),H)),Pair(Tpm(qinv(g,H)), Csof(g,H,eof(g))))’]
|> C mp (undisch $ spec_all (qg_isgrp))
|> uex2ex_rule 
|> SKOLEM (Grp_Qc_ex |> spec_all) "Qg" [("g",mem_sort (rastt "Grp(G)")),
                                         ("H",mem_sort (rastt "Pow(G)"))]
|> disch_all |> gen_all 

val resp1_def = qdefine_psym("resp1",[‘f:A->B’,‘R:A~>A’]) ‘resp(f,R,id(B))’

val resp1_property = prove_store("resp1_property",
e0
cheat
(form_goal “!A B f:A->B R. resp1(f,R) <=> 
 (!a1 a2. Holds(R,a1,a2) ==> App(f,a1) = App(f,a2))”));

val Inj_INV = prove_store("Inj_INV",
e0
cheat
(form_goal “!A B f:A->B. Inj(f) ==>
 !a0:mem(A). ?!ivf:B->A.!b.(!a.App(f,a) = b ==> App(ivf,b) = a) &
 ((!a. ~(App(f,a) = b)) ==> App(ivf,b) = a0)”));

val fun_mem_ex = proved_th $
e0
cheat
(form_goal “!A a0:mem(A) B. ?f:B->A.T”)


val LINV_def = Inj_INV |> spec_all |> undisch |> spec_all
                       |> uex2ex_rule 
                       |> SKOLEM (fun_mem_ex |> qspecl [‘A’,‘a0:mem(A)’,‘B’])
                       "LINV" [dest_var (rastt "f:A->B"),
                               dest_var (rastt "a0:mem(A)")]


(*

val Quot_def =  qdefine_psym ("Quot",[‘r:A~>A’,‘i:Q->Pow(A)’])
‘!s. (?!q. s = App(i:Q->Pow(A),q)) <=> (?a. s = rsi(r:A~>A,a))’
|> gen_all |> store_as "Quo_def";

val Quo_UMP  = prove_store("Quo_UMP",
e0
()
(form_goal 
 “!A B f:A->B R:A~>A. ER(R) & resp1(f,R) ==> 
!Q i:Q->Pow(A). Inj(i) & Quo(R,i) ==>
?!f: Q -> B. !q a. App(i,q) = rsi(R,a) ==> App(i,)”));
Quo_fun_alt

*)
     
val first_iso_thm = prove_store("first_iso_thm",
e0
cheat
(form_goal “!G1 G2 f:G1->G2 g1 g2. hom(f,g1,g2) & Surj(f) ==>
 ?phi:Qc(g1,ker(f,g1,g2)) -> G2. Inj(phi) & 
 hom(phi, Qg(g1,ker(f,g1,g2)), g2)”));

val FIN_def = qdefine_psym("FIN",[‘X’]) ‘Fin(Whole(X))’ |> gen_all


val Z_mem_ex = proved_th $
e0
cheat
(form_goal “?z:mem(Z).T”)

val Divz_def = division_theorem |> spec_all |> undisch 
                               |> uex2ex_rule
                               |> SKOLEM Z_mem_ex "Divz" 
                               [("a",mem_sort (rastt "Z")),
                                ("b",mem_sort (rastt "Z"))]


val Remz_def = Divz_def |> uex2ex_rule
                      |> SKOLEM Z_mem_ex "Remz" 
                      [("a",mem_sort (rastt "Z")),
                       ("b",mem_sort (rastt "Z"))]

val divides_def = qdefine_psym("divides",[‘b:mem(Z)’,‘a:mem(Z)’])
                              ‘Remz(a,b) = Oz’

val CD_def = qdefine_fsym("CD",[‘A’]) ‘Card(Whole(A))’ 

val Lagrange_lemma = prove_store("Lagrange_lemma",
e0
(cheat)
(form_goal
 “!G g:mem(Grp(G)) H. issgrp(H) ==> 
 !a b. Card(rcst(g,H,a)) = Card(rcst(g,H,b))”));



val Eqcs_def = proved_th $
e0
cheat
(form_goal “!A R: A~> A. ?!eqcs:mem(Pow(Pow(A))). 
 !eqc. IN(eqc,eqcs) <=> (?a. eqc = rsi(R,a))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "Eqcs" [‘R’] |> gen_all

val ER_partition = prove_store("ER_partition",
e0
cheat
(form_goal “!A R:A ~> A. ER(R) ==> !a. ?!eqc. IN(eqc, Eqcs(R)) & IN(a,eqc)”));

val Lagrange_theorem = prove_store("Lagrange_theorem",
e0
cheat
(form_goal
 “!G g:mem(Grp(G)) H. FIN(G) & issgrp(H,g) ==> 
   divides(n2z(Card(H)),n2z(Card(Whole(G))))”));



(*
(*center*)
val ctr_def = proved_th $
e0
cheat
(form_goal 
 “!G g:mem(Grp(G)). ?!ctr. (!z. IN(z,ctr) <=> !x. gmul(g,z,x) = gmul(g,x,z))”)
|> spec_all |> uex2ex_rule |> qSKOLEM "ctr" [‘g’]
  
val abel_def = qdefine_psym("abel",[‘g:mem(Grp(G))’])
‘!a b. gmul(g,a,b) = gmul(g,b,a)’

val Qg_ctr_cyc_abel = prove_store("Qg_ctr_cyc_abel",
e0
cheat
(form_goal
 “!G g:mem(Grp(G)). cyc(Qg(g,ctr(g))) ==> abel(g)”));





(*
If 𝑝 is a prime and 𝑃 is a group of prime power order 𝑝𝛼 for some 𝛼≥1, then 𝑃 has a nontrivial center: 𝑍(𝑃)≠1.
*)

val prime_def = qdefine_psym("prime",[‘p:mem(Z)’])
‘!q. divides(q,p) <=> (Abv(q) = Suc(O) | Abv(q) = Abv(p))’

(*sort info must be like this since negative power for z is undefined, need Q*)
val Powz_def = qdefine_fsym("Powz",[‘n:mem(N)’,‘z:mem(Z)’]) 
‘App(np(mulz,n2z(Suc(O)),z),n)’




(*need power for the arithematic*)
val prime_zp_order_nontrivial_ctr = 
prove_store("prime_zp_order_nontrivial_ctr",
e0
cheat
(form_goal “!p. CD(g) =  ==> ?z. IN(z,ctr(g)) & ~(z = eof(g))”));

*)

isgrp(g:bigproduct) ==> P(g)

!g:mem(Grp(G)).P(g)

g H 

want a term of sort Qg(g,H):mem(Grp(Qc(g,H)))

val snocrel_def = qdefine_fsym("snocrel",[‘r:mem(Pow(A * A))’,‘a:mem(A)’])
‘r’

(*should require a is not already in the rel*)






(*
Makkai

g = g' & H = H'
------------
(!f.P(f:Qc(g,H)->A)) <=>
(!f. P(f:Qc(g',H')->A) )

Qc(g,H)

*)
(*

Beth(wo:mem(Pow(A * A)),s:set) <=>
?B b:mem(Pow(B)). beth0(wo,b) & Eqv(s,Asset(b))

Beth(wo:mem(Pow(A * A)),b:mem(Pow(B)))

Eqv(Asset(s),N) ==> beth0({},s) &

require a is not in wo0
beth0(wo0,s0) & wo = snocrel(wo0,a) & 
Eqv(Asset(s),Pow(Asset(s0))) ==>
beth0(wo,s) &

(*wo is not a successor ordinal, but still well order*)
(!wo0 a. ~wo = snocrel(wo,a) & WO(wo)) &

(* f indexes a family of wo-beth number relation*)
!J f:J->Pow(A * A) * Pow(B). 
 (!j:mem(J). beth0(f(j)) & 
  (!wo0. wo0 ⊆ wo & wo0 <> wo <=> ?j. Fst(f(j)) = wo0)) &

(* s is the sup of the set of beth numbers indexed by J*)

(!s0 j.Snd(App(f,j)) = s0 ==> Card(s0) <= Card(s)) &
(!s'. (!s0 j.Snd(App(f,j)) = s0 ==> Card(s0) <= Card(s')) ==>
 Card(s) <= Card(s') ) ==>

beth(wo,s)


*)

local
val Lind_cl = 
 “(p = Pair(Empty(A * A),s:mem(Pow(B))) & Card(s) = CD(N) ==> IN(p,beth0)) &
  (!p0:mem(Pow(A * A) * Pow(B)) a:mem(A).
   IN(p0,beth0) & Card(s) = CD(Pow(asset(Snd(p0)))) &
        p = Pair(snocrel(Fst(p0),a),s)
    ==> IN(p,Lind)) &
  (!p0 ps. p0 = BIGUNION(ps) &  )”
in
val (Lind_incond,x1) = mk_incond Lind_cl;
val Lindf_ex = mk_fex Lind_incond x1;
val Lindf_def = mk_fdef "Lindf" Lindf_ex;
val Lindf_monotone = mk_monotone Lindf_def;
val Lind's_def = mk_prim Lindf_def;
val Linds_def = mk_LFP (rastt "Lind's(a0:mem(A),f0:X * A->A)");
val Linds_cond = mk_cond Linds_def Lind's_def;
val Linds_SS = mk_SS Linds_def Lind's_def;
val Lind_rules0 = mk_rules Lindf_monotone Linds_SS Linds_cond;
val Lind_cases0 = mk_cases Lindf_monotone Lind_rules0 Linds_cond;
val Lind_ind0 = mk_ind Linds_cond;
val Lind_ind1 = mk_ind1 Lindf_def Lind_ind0;
val Lind_ind2 = mk_ind2 Lind_ind1; 
val Lind_cases1 = mk_case1 Lindf_def Lind_cases0; 
val Lind_rules1 = mk_rules1 Lindf_def Lind_rules0; 
val Lind_rules2 = mk_rules2 Lind_rules1; 
val Lind_rules3 = mk_rules3 Lind_rules2;
end

val Lind_ind = Lind_ind2 |> store_as "Lind_ind";
val Lind_cases = Lind_cases1 |> store_as "Lind_cases";
val Lind_rules = Lind_rules3 |> store_as "Lind_rules";
