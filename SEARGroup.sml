
val mul_def = qdefine_fsym("mul",[‘m:G * G ->G’,‘g1:mem(G)’,‘g2:mem(G)’])
‘App(m,Pair(g1,g2))’


val asc_def = qdefine_psym("asc",[‘m:A * A -> A’])
‘!a1 a2 a3. mul(m,mul(m,a1,a2),a3) = mul(m,a1,mul(m,a2,a3))’

(*
App(m,Pair(App(m,Pair(a1,a2)),a3)) = 
App(m,Pair(a1,App(m,Pair(a2,a3))))’ |> gen_all
*)

val isunit_def = qdefine_psym("isunit",[‘m:A * A -> A’,‘e:mem(A)’])
‘!a. mul(m,e,a) = a & mul(m,a,e) = a’


val isinv_def = qdefine_psym("isinv",[‘m:A * A -> A’,‘i:A->A’,‘e:mem(A)’])
‘!a. mul(m,App(i,a),a) = e & mul(m,a,App(i,a)) = e’



(*c for component*)
val c31_def = qdefine_fsym("c31",[‘abc:mem(A * B * C)’]) ‘Fst(abc)’
val c32_def = qdefine_fsym("c32",[‘abc:mem(A * B * C)’]) ‘Fst(Snd(abc))’
val c33_def = qdefine_fsym("c33",[‘abc:mem(A * B * C)’]) ‘Snd(Snd(abc))’

val isgrp_def = qdefine_psym("isgrp",[‘g:mem(Exp(G * G,G) * Exp(G,G) * G)’])
‘asc(tof(c31(g))) & 
 isunit(tof(c31(g)),c33(g)) & 
 isinv(tof(c31(g)),tof(c32(g)),c33(g))’

val Grp_def = Thm_2_4 |> qspecl [‘Exp(G * G,G) * Exp(G,G) * G’]
                      |> fVar_sInst_th “P(g:mem(Exp(G * G,G) * Exp(G,G) * G))”
                         “isgrp(g:mem(Exp(G * G,G) * Exp(G,G) * G))”
                      |> qSKOLEM "Grp" [‘G’]
                      |> qSKOLEM "iG" [‘G’]

val RepG_def = qdefine_fsym("RepG",[‘g:mem(Grp(G))’]) ‘App(iG(G),g)’

val mof_def = qdefine_fsym("mof",[‘g:mem(Grp(G))’]) ‘tof(c31(RepG(g)))’
val iof_def = qdefine_fsym("iof",[‘g:mem(Grp(G))’]) ‘tof(c32(RepG(g)))’
val eof_def = qdefine_fsym("eof",[‘g:mem(Grp(G))’]) ‘c33(RepG(g))’

val gmul_def = qdefine_fsym("gmul",[‘g:mem(Grp(G))’,‘x:mem(G)’,‘y:mem(G)’])
‘mul(mof(g),x,y)’

val ginv_def = qdefine_fsym("ginv",[‘g:mem(Grp(G))’,‘x:mem(G)’])
‘App(iof(g),x)’

val np_def = qdefine_fsym("np",[‘m:G * G ->G’,‘e:mem(G)’,‘x:mem(G)’])
‘Nrec(e,Ap1(m,x))’

val np_O = Nrec_O |> qsspecl [‘e:mem(G)’,‘Ap1(m:G * G->G,x)’]
                  |> rewr_rule[GSYM np_def]

val np_Suc = Nrec_Suc |> qsspecl [‘e:mem(G)’,‘Ap1(m:G * G->G,x)’,‘n:mem(N)’]
                      |> rewr_rule[GSYM np_def]



(*extend lambda tool into !z. ?n. .... ==> *)
val Num_ex = proved_th $
e0
(cheat)
(form_goal “!z. Lez(Oz,z) ==> ?!n. z = Asz(n,O)”)

local 
val th0 = proved_th $
e0
cheat
(form_goal “?n:mem(N).T”)
in 
val Num_def = SKOLEM th0 "Num" [("z",mem_sort (rastt "Z"))] (Num_ex |> spec_all |> undisch |> uex2ex_rule) |> disch_all |> gen_all
end

val Ltz_def = qdefine_psym("Ltz",[‘z1:mem(Z)’,‘z2:mem(Z)’])
‘Lez(z1,z2) & ~(z1 = z2)’ |> gen_all

val zp_def = proved_th $
e0
cheat
(form_goal 
“!g:mem(Grp(G)). ?!f:G * Z -> G.
 !gz. 
 (Lez(Oz,Snd(gz)) ==> App(f,gz) = App(np(mof(g),eof(g),Fst(gz)),Num(Snd(gz)))) &
 (Ltz(Snd(gz),Oz) ==> App(f,gz) = App(iof(g),App(np(mof(g),eof(g),Fst(gz)),Num(Negz(Snd(gz))))) )”)
|> spec_all |> uex2ex_rule |> qSKOLEM "zp" [‘g’]

val gpw_def = qdefine_fsym("gpw",[‘g:mem(Grp(G))’,‘x:mem(G)’,‘z:mem(Z)’])
‘App(zp(g),Pair(x,z))’



val cyc_def = qdefine_psym("cyc",[‘g:mem(Grp(G))’])
‘?a. !x. ?z. x = gpw(g,a,z)’ |> gen_all

(*can define a set Ghom(g1,g2), and say f:mem(Ghom(g1,g2)) ==> ...
 but then run into the trouble with equalities.*)

val ghom_def = qdefine_psym("ghom",[‘f:G1->G2’,‘g1:mem(Grp(G1))’,
                                               ‘g2:mem(Grp(G2))’])
‘!a b. App(f,gmul(g1,a,b)) = gmul(g2,App(f,a),App(f,b))’

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

val division_theorem = prove_store("division_theorem",
e0
cheat
(form_goal 
 “!a b:mem(Z).~(b = Oz) ==> ?!q r. a = Addz(Mulz(q,b),r) & 
  Lez(Oz,r) & Lez(r,b)”));

val sub_cyc_cyc = prove_store("sub_cyc_cyc",
e0
(rpt strip_tac >>
 qcases ‘!x:mem(H). x = eof(h)’
 >-- cheat >>
 fs[cyc_def] >>
 qby_tac ‘?m. ?x0. App(i,x0) = gpw(g,a,m) & Ltz(Oz,m) & 
   !m'. ?x0. App(i,x0) = gpw(g,a,m') & Ltz(Oz,m') ==> Lez(m,m')  ’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘x0’ >> strip_tac >>
 qby_tac ‘?n. App(i,x) = gpw(g,a,n)’ 
 >-- cheat >> pop_assum strip_assume_tac >>
 qby_tac ‘~(m = )’
 qby_tac
 ‘?q r. n = Addz(Mulz(m,q),r)’ 
 >-- cheat >>
 pop_assum strip_assume_tac >> 
 qsuff_tac ‘r = Oz’ 
 >-- (strip_tac >> fs[Addz_Oz] >> qexists_tac ‘q’ >>
     drule Inj_eq_eq >> first_x_assum (irule o iffLR) >> arw[] >>
     drule ghom_gpw >> arw[] >> rw[gpow_Mulz]) >>
 qsuff_tac ‘?x0. App(i,x0) = gpw(g,a,r)’ 
 >-- strip_tac >>
     first_x_assum (qspecl_then [‘r’] assume_tac) >> 
     ccontra_tac >> 
     


 qsuff_tac ‘n = Mulz(m, q)’ 
 >-- (* fs[] why loop?*) (once_arw[] >> rw[Addz_eq_O]) >>
 
     )
(form_goal “!H h:mem(Grp(H)) G g:mem(Grp(G)) i:H -> G.
 ghom(i,h,g) & Inj(i) & cyc(g) ==> cyc(h)”)



[‘h:mem(Pow(G))’,‘g:mem(Grp(G))’])
‘is’




val Grp0_def = define_pred
“!G e:mem(G) m: G * G ~> G i:G ~>G. 
 Grp0(G,e,m,i) <=> Assoc(m) & 
 (!x. App(m,Pair(x,e)) = x & App(m,Pair(e,x)) = x) &
 ”







(*define topspace type to be 
 a set, and a function Pow(X) -> 2, or a mono to Pow(X). or an element of Pow(Pow(X)).

 a topospace is a mono to Pow(X).

there is a biginter function Pow(Pow(X)) -> Pow(X)

 a presheaf is a function that associate each mem of the domain of the mono a set, and hence associate the mono with a family of sets. 

so 

Psh(OX:Opens >--> Pow(X), B--> W)
*)
