val Fst_ex = prove_store("Fst_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(p1(A,B),x)’ >> rw[])
(form_goal
 “!A B x:mem(A * B).?fstx. Eval(p1(A,B),x) = fstx”));

 
val Snd_ex = prove_store("Snd_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(p2(A,B),x)’ >> rw[])
(form_goal
 “!A B x:mem(A * B).?sndx. Eval(p2(A,B),x) = sndx”));

val Fst_def = Fst_ex |> spec_all |> ex2fsym0 "Fst" ["x"]
val Snd_def = Snd_ex |> spec_all |> ex2fsym0 "Snd" ["x"]

val Pair_def' = Pair_def |> rewr_rule[Fst_def,Snd_def]

val ZR_def = 
fVar_Inst 
[("P",([("mn",mem_sort $Cross N N),("m'n'",mem_sort $Cross N N)],
 “Add(Fst(mn:mem(N * N)),Snd(m'n':mem(N * N))) = 
 Add(Fst(m'n'),Snd(mn))”))] 
(AX1 |> qspecl [‘N * N’,‘N * N’] |> uex_expand)
|> ex2fsym0 "ZR" [] |> conjE1
|> store_as "ZR_def";

val ZR_Refl = prove_store("ZR_Refl",
e0
(rw[Refl_def,ZR_def])
(form_goal
 “Refl(ZR)”));

val Pair_Fst_Snd = Pair_component |> rewr_rule[Fst_def,Snd_def] |> store_as "Pair_Fst_Snd";

(*AQ how to let it realize 
 !(a1 : mem(N * N))  (a2 : mem(N * N)).
               Add(Fst(a1#), Snd(a2#)) = Add(Fst(a2#), Snd(a1#)) ==>
               Add(Fst(a2#), Snd(a1#)) = Add(Fst(a1#), Snd(a2#))

analoge of cases on ‘a1’
*)


local 
val l =
fVar_Inst 
[("P",([("m",mem_sort N)],
 “!n0 p. Add(m,Add(n0,p)) = Add(Add(m,n0),p)”))] 
N_ind_P
in
val Add_assoc = prove_store("Add_assoc",
e0
(irule l >> rw[Add_O,Suc_def,Add_Suc,Add_Suc1,Add_O2] >>
 rpt strip_tac >>arw[])
(form_goal
 “!m n0 p. Add(m,Add(n0,p)) = Add(Add(m,n0),p)”));
end

val Add_eq_eq = prove_store("Add_eq_eq",
e0
(rpt strip_tac >> 
 qby_tac
 ‘Sub(Add(m,a),a) = Sub(Add(n,a),a)’
 >-- arw[] >>
 fs[Add_Sub])
(form_goal
 “!m n a. Add(m,a) = Add(n,a) ==> m = n”));

(*use add_sub*)
val ZR_Trans = prove_store("ZR_Trans",
e0
(rw[Trans_def,ZR_def] >>
 qsuff_tac
 ‘!a1 b1 a2 b2 a3 b3.
  Add(a1,b2) = Add(a2,b1) & Add(a2,b3) = Add(a3,b2) ==>
  Add(a1,b3) = Add(a3,b1)’
 >-- (rpt strip_tac >>
     first_x_assum (qspecl_then [‘Fst(a1)’,‘Snd(a1)’,‘Fst(a2)’,‘Snd(a2)’,‘Fst(a3)’,‘Snd(a3)’] assume_tac) >>
     first_x_assum irule >> arw[]) >>
 rpt strip_tac >>
 irule Add_eq_eq >> qexists_tac ‘b2’ >>
 once_rw[GSYM Add_assoc] >>
 qby_tac
 ‘Add(b3,b2) = Add(b2,b3) & Add(b1,b2) = Add(b2,b1)’ 
 >-- (strip_tac 
     >-- qspecl_then [‘b2’,‘b3’] accept_tac Add_sym
     >-- qspecl_then [‘b2’,‘b1’] accept_tac Add_sym) >>
 arw[] >>
 rw[Add_assoc] >> once_arw[] >> 
 qpick_x_assum ‘Add(a2, b3) = Add(a3, b2)’
 (assume_tac o GSYM) >> once_arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘b3’,‘b1’] assume_tac Add_sym >>
 once_arw[] >> rw[])
(form_goal
 “Trans(ZR)”));

val ZR_Sym = prove_store("ZR_Sym",
e0
(rw[ZR_def,Sym_def] >> rpt strip_tac >> flip_tac >>
 arw[])
(form_goal
 “Sym(ZR)”));

val ZR_ER = prove_store("ZR_ER",
e0
(rw[ER_def,ZR_Refl,ZR_Sym,ZR_Trans])
(form_goal “ER(ZR)”));

val toZ_def = 
Thm_2_14 |> qspecl [‘N * N’,‘ZR’]
         |> C mp ZR_ER
         |> ex2fsym0 "Z" []
         |> ex2fsym0 "toZ" []
         |> store_as "toZ_def";

val zj_ex = prove_store("zj_ex",
e0
(qexists_tac ‘Pair(O,O)’ >> rw[])
(form_goal
 “?zj.Pair(O,O) = zj”));

val zj_def = zj_ex |> ex2fsym0 "0j" []
                   |> store_as "zj_def";


val oj_ex = prove_store("oj_ex",
e0
(qexists_tac ‘Pair(Suc(O),O)’ >> rw[])
(form_goal
 “?oj.Pair(Suc(O),O) = oj”));

val oj_def = oj_ex |> ex2fsym0 "1j" []
                   |> store_as "oj_def";

val negj_def = 
fVar_Inst 
[("P",([("mn",mem_sort $Cross N N),("m'n'",mem_sort $Cross N N)],
 “Fst(mn:mem(N * N)) = Snd(m'n') & Snd(mn) = Fst(m'n')”))] 
(AX1 |> qspecl [‘N * N’,‘N * N’] |> uex_expand)
|> ex2fsym0 "negj" [] |> conjE1
|> store_as "negj_def";

val negj_Fun = prove_store("negj_Fun",
e0
(rw[Fun_expand,negj_def] >> rpt strip_tac 
 >-- (qexists_tac ‘Pair(Snd(a),Fst(a))’ >> 
     rw[Pair_def']) >>
 once_rw[Pair_component] >>
 rw[Pair_eq_eq] >> rw[Fst_def,Snd_def] >>
 pop_assum_list (map_every (assume_tac o GSYM)) >>
 arw[])
(form_goal
 “isFun(negj)”));

val Eval_negj = prove_store("Eval_negj",
e0
(rpt strip_tac >> assume_tac negj_Fun >>
 drule $GSYM Eval_def >> flip_tac >>  
 arw[] >> rw[negj_def] >>
 rw[Pair_def'])
(form_goal
 “!m n. Eval(negj,Pair(m,n)) = Pair(n,m)”));


val Negj_ex = prove_store("Negj_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(negj,mn)’ >> rw[])
(form_goal
 “!mn.?nm.Eval(negj,mn) = nm”));

val Negj_def = Negj_ex |> spec_all |> ex2fsym0 "Negj" ["mn"] |> store_as "Negj_def";

val Negj_property = Eval_negj |> rewr_rule[Negj_def]
                              |> store_as "Negj_property";





val addj_def = 
fVar_Inst 
[("P",([("abcd",mem_sort (Cross (Cross N N) $Cross N N)),("acbd",mem_sort $Cross N N)],
 “Fst(acbd) = Add(Fst(Fst(abcd:mem((N * N) * N * N))),Fst(Snd(abcd))) &
  Snd(acbd) = Add(Snd(Fst(abcd)),Snd(Snd(abcd)))”))] 
(AX1 |> qspecl [‘(N * N) * (N * N)’,‘N * N’] |> uex_expand)
|> ex2fsym0 "addj" [] |> conjE1
|> store_as "addj_def";

val Fst_Snd_eq = Pair_Eval_eq |> rewr_rule[Fst_def,Snd_def] |> store_as "Fst_Snd_eq";

val addj_Fun = prove_store("addj_Fun",
e0
(rw[Fun_expand,addj_def] >> rpt strip_tac 
 >-- (qexists_tac ‘Pair(Add(Fst(Fst(a)), Fst(Snd(a))),Add(Snd(Fst(a)), Snd(Snd(a))))’ >> 
     rw[Pair_def']) >>
 irule Fst_Snd_eq >>
 arw[])
(form_goal
 “isFun(addj)”));

val Eval_addj = prove_store("Eval_addj",
e0
(rpt strip_tac >> assume_tac addj_Fun >>
 drule $GSYM Eval_def >> flip_tac >>  
 arw[] >> rw[addj_def] >>
 rw[Pair_def'])
(form_goal
 “!a b c d. Eval(addj,Pair(Pair(a,b),Pair(c,d))) = Pair(Add(a,c),Add(b,d))”));


val Addj_ex = prove_store("Addj_ex",
e0
(rpt strip_tac >> qexists_tac ‘Eval(addj,Pair(ab,cd))’ >> rw[])
(form_goal
 “!ab cd.?acbd.Eval(addj,Pair(ab,cd)) = acbd”));

val Addj_def = Addj_ex |> spec_all |> ex2fsym0 "Addj" ["ab","cd"] |> store_as "Addj_def";

val Addj_property = Eval_addj |> rewr_rule[Addj_def]
                              |> store_as "Addj_property";


val J1_i = prove_store("J1_i",
e0
(rw[Addj_property,GSYM Add_assoc,ZR_def])
(form_goal
 “!a b c d e f.
 Holds(ZR,
 Addj(Addj(Pair(a,b),Pair(c,d)),Pair(e,f)),
 Addj(Pair(a,b),Addj(Pair(c,d),Pair(e,f))))”));

val J1_ii = prove_store("J1_ii",
e0
(rw[GSYM zj_def,Addj_property,ZR_def,Add_O])
(form_goal
 “!a b.Holds(ZR,Addj(Pair(a,b),0j),Pair(a,b))”));

val J1_iii = prove_store("J1_iii",
e0
(rw[Addj_property,GSYM zj_def,Negj_property,ZR_def,
    Pair_def',Add_O,Add_O2] >>
 rpt strip_tac >>
 qspecl_then [‘b’,‘a’] assume_tac Add_sym >>
 first_x_assum accept_tac)
(form_goal
 “!a b.Holds(ZR,Addj(Pair(a,b),Negj(Pair(a,b))),0j)”));

val J1_iv = prove_store("J1_iv",
e0
(rw[Addj_property,ZR_def,Pair_def'] >>
 rpt strip_tac >>
 qspecl_then [‘c’,‘a’] assume_tac Add_sym >>
 qspecl_then [‘b’,‘d’] assume_tac Add_sym >> 
 arw[])
(form_goal
 “!a b c d.Holds(ZR,Addj(Pair(a,b),Pair(c,d)),
                    Addj(Pair(c,d),Pair(a,b)))”));


val J2_i = prove_store("J2_i",
e0
(rw[Addj_property,ZR_def,Pair_def'] >>
 rpt strip_tac >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘d'’,‘b'’] assume_tac Add_sym >> arw[] >>
 qspecl_then [‘c’,‘d'’,‘b'’] assume_tac Add_assoc >>
 arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘Add(c',Add(d,b'))’,‘a’] 
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘a’,‘b'’] assume_tac Add_sym >>
 arw[] >>
 qsspecl_then [‘Add(c', Add(b, d))’,‘a'’]
 assume_tac Add_sym >> arw[] >>
 rw[GSYM Add_assoc] >> 
 qsuff_tac
 ‘Add(d, Add(a', b)) = Add(b, Add(d, a'))’
 >-- (strip_tac >> arw[]) >>
 qspecl_then [‘Add(a',b)’,‘d’] assume_tac Add_sym >>
 arw[] >> 
 qspecl_then [‘a'’,‘d’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc] >>
 qspecl_then [‘a'’,‘b’] assume_tac Add_sym >> arw[])
(form_goal
 “!a b a' b' c d c' d'. Holds(ZR,Pair(a,b),Pair(a',b')) & Holds(ZR,Pair(c,d),Pair(c',d')) ==>
 Holds(ZR,Addj(Pair(a,b),Pair(c,d)),Addj(Pair(a',b'),Pair(c',d')))”));

val J2_ii = prove_store("J2_ii",
e0
(rw[ZR_def,Negj_property,Pair_def'] >> rpt strip_tac >>
 qspecl_then [‘a'’,‘b’] assume_tac Add_sym >>
 arw[] >> last_x_assum (assume_tac o GSYM) >> arw[] >>
 qspecl_then [‘b'’,‘a’] accept_tac Add_sym)
(form_goal
 “!a b a' b'. Holds(ZR,Pair(a,b),Pair(a',b')) ==>
  Holds(ZR,Negj(Pair(a,b)),Negj(Pair(a',b')))”));

val rep_ex = prove_store("rep_ex",
e0
(strip_tac >> assume_tac toZ_def >>
 fs[Surj_def] >> 
 first_x_assum $ qspecl_then [‘z’] strip_assume_tac >>
 qexists_tac ‘x’ >> arw[] >>
 qexistsl_tac [‘Fst(x)’,‘Snd(x)’] >>
 qsspecl_then [‘x’] accept_tac Pair_Fst_Snd)
(form_goal
 “!z. ?rz. Eval(toZ,rz) = z & ?a b. rz = Pair(a,b)”));

val rep_def = rep_ex |> spec_all |> ex2fsym0 "rep" ["z"] |> gen_all |> store_as "rep_def";

val Eval_rep = rep_def |> spec_all |> conjE1
                       |> gen_all |> store_as "Eval_rep";

val rcp_def = rep_def |> spec_all |> conjE2
                      |> ex2fsym0 "rfst" ["z"]
                      |> ex2fsym0 "rsnd" ["z"]
                      |> gen_all
                      |> store_as "rcp_def";

val Eval_rcp = Eval_rep |> rewr_rule[rcp_def]
                        |> store_as "Eval_rcp";

val asz_ex = prove_store("asz_ex",
e0
(strip_tac >> qexists_tac ‘Eval(toZ,ab)’ >> rw[])
(form_goal
 “!ab.?z.Eval(toZ,ab) = z”));

val asz_def = asz_ex |> spec_all |> ex2fsym0 "asz" ["ab"] |> gen_all |> store_as "asz_def";

val rep_asz = Eval_rep |> rewr_rule[asz_def];

val Z = mk_fun "Z" []
(*
val ADDz_def = 
fVar_Inst 
[("P",([("z1z2",mem_sort $Cross Z Z),("z",mem_sort Z)],
 “Holds(ZR,Addj(
  Pair(rfst(Fst(z1z2)),rsnd(Fst(z1z2))),
  Pair(rfst(Snd(z1z2)),rsnd(Snd(z1z2)))),Pair(rfst(z),rsnd(z)))”))] 
(AX1 |> qspecl [‘Z * Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "ADDz" [] |> conjE1

*)

val ADDz_def = 
fVar_Inst 
[("P",([("z1z2",mem_sort $Cross Z Z),("z",mem_sort Z)],
 “Holds(ZR,Addj(rep(Fst(z1z2)),rep(Snd(z1z2))),rep(z))”))] 
(AX1 |> qspecl [‘Z * Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "ADDz" [] |> conjE1
|> store_as "ADDz_def";


val rep_asz_ZR = prove_store("rep_asz_ZR",
e0
(rw[GSYM asz_def] >>
 assume_tac Eval_rep >>
 rw[toZ_def] >> arw[])
(form_goal
 “!ab.Holds(ZR,ab,rep(asz(ab)))”));

val corres_z_uex = prove_store("corres_z_uex",
e0
(strip_tac >> uex_tac >>
 qexists_tac ‘asz(ab)’ >> rw[rep_asz_ZR] >>
 rpt strip_tac >> 
 fs[toZ_def,asz_def] >> rw[rep_asz])
(form_goal
 “!ab.?!z.Holds(ZR,ab,rep(z))”));

val ADDz_Fun = prove_store("ADDz_Fun",
e0
(rw[Fun_expand,ADDz_def] >> rpt strip_tac >--
 (qexists_tac ‘asz(Addj(rep(Fst(a)), rep(Snd(a))))’ >>
 rw[rep_asz_ZR]) >>
 qspecl_then [‘Addj(rep(Fst(a)), rep(Snd(a)))’]
 assume_tac corres_z_uex  >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘b1 = z & b2 = z’
 >-- (strip_tac >> arw[]) >> strip_tac >>
 first_x_assum irule >> first_x_assum accept_tac)
(form_goal
 “isFun(ADDz)”));

val Addz_ex = prove_store("Addz_ex",
e0
(rpt strip_tac >> 
 qexists_tac ‘Eval(ADDz,Pair(z1,z2))’ >> rw[])
(form_goal
 “!z1 z2.?z12. Eval(ADDz,Pair(z1,z2)) = z12”));

val Addz_def = Addz_ex |> spec_all 
                       |> ex2fsym0 "Addz" ["z1","z2"] 
                       |> gen_all
                       |> store_as "Addz_def";

val Addz_eqn = prove_store("Addz_eqn",
e0
(rpt strip_tac >>
 rw[GSYM Addz_def] >>
 assume_tac ADDz_Fun >>
 drule $ GSYM Eval_def >> 
 flip_tac >> arw[] >>
 rw[ADDz_def,Pair_def',rep_asz_ZR])
(form_goal
 “!z1 z2.
  Addz(z1,z2) = asz(Addj(rep(z1),rep(z2)))”));

(*rep_asz_ZR*)


val ZR_samez = prove_store("ZR_samez",
e0
(rw[toZ_def,GSYM asz_def])
(form_goal
 “!ab cd. Holds(ZR,ab,cd) <=> asz(ab) = asz(cd)”));

val Addz_sym = prove_store("Addz_sym",
e0
(rw[Addz_eqn] >> rw[GSYM ZR_samez] >> rpt strip_tac>>
 once_rw[rcp_def] >> rw[J1_iv])
(form_goal
 “!z1 z2. Addz(z1,z2) = Addz(z2,z1)”));

val rep_ZR_eq = prove_store("rep_ZR_eq",
e0
(rw[ZR_samez,rep_asz])
(form_goal
 “!z1 z2. 
  Holds(ZR,rep(z1),rep(z2)) <=> z1 = z2 ”));

val z_eq_cond = prove_store("z_eq_cond",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (qexistsl_tac [‘rep(z1)’,‘rep(z2)’] >>
      arw[rep_asz,rep_ZR_eq]) >>
 fs[ZR_samez])
(form_goal
 “!z1 z2. z1 = z2 <=>
  ?ab cd. asz(ab) = z1 & asz(cd) = z2 & Holds(ZR,ab,cd)”));

val ZR_refl = prove_store("ZR_refl",
e0
(assume_tac ZR_Refl >>fs[Refl_def])
(form_goal
 “!ab. Holds(ZR,ab,ab)”));

val ZR_sym = ZR_Sym |> rewr_rule[Sym_def]
                    |> store_as "ZR_sym"; 

val ZR_trans = ZR_Trans |> rewr_rule[Trans_def]
                        |> store_as "ZR_trans";

val ZR_cond = prove_store("ZR_cond",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (qexistsl_tac [‘ab’,‘cd’] >> 
      arw[ZR_refl]) >>
 qby_tac ‘Holds(ZR,ab,cd1)’
 >-- (irule ZR_trans >> qexists_tac ‘ab1’ >> arw[]) >>
 qby_tac ‘Holds(ZR,cd1,cd)’ 
 >-- (irule ZR_sym >> arw[]) >>
 irule ZR_trans >>
 qexists_tac ‘cd1’ >> arw[])
(form_goal
 “!ab cd. Holds(ZR,ab,cd) <=>
 ?ab1 cd1. Holds(ZR,ab,ab1) & Holds(ZR,cd,cd1) &
 Holds(ZR,ab1,cd1)”));


(*
have (a,b) ~ (a',b') 
     (c,d) ~ (c',d') 
==> addj((a,b),(c,d)) ~ addj((a',b'),(c',d'))

want (a + b) + c = a + b + c

that is ((a1,a2) + (b1,b2)) + (c1,c2)
       ~  (a1,a2) + (b1,b2) + (c1,c2)

*)

val ADDz_alt0 = prove_store("ADDz_alt0",
e0
(rpt strip_tac >>
 assume_tac ADDz_def >> 
 arw[] >> rw[Pair_def'])
(form_goal
 “!z1 z2 z12. 
  Holds(ADDz,Pair(z1,z2),z12) <=>
  Holds(ZR,Addj(rep(z1),rep(z2)),rep(z12))”));


val rep_rel_all = prove_store("rep_rel_all",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
      irule ZR_sym >> rw[rep_asz_ZR]) >>
 fs[ZR_samez,rep_asz])
(form_goal
 “!z rz.asz(rz) = z <=> Holds(ZR,rep(z),rz)”));

val ADDz_alt0' = prove_store("ADDz_alt0",
e0
(rpt strip_tac >> rw[ADDz_alt0] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexistsl_tac [‘rep(z1)’,‘rep(z2)’,‘rep(z12)’] >>
     arw[rep_asz]) >>
 irule $ iffRL ZR_cond >>
 qexistsl_tac [‘Addj(r1,r2)’,‘r12’] >>
 arw[] >> strip_tac >-- 
 (once_rw[rcp_def] >>
 qsspecl_then [‘r1’] assume_tac Pair_Fst_Snd >>
 once_arw[] >>
 qsspecl_then [‘r2’] assume_tac Pair_Fst_Snd >>
 once_arw[] >>
 irule J2_i >> rw[Pair_def'] >>
 rw[GSYM rcp_def] >> rw[GSYM Pair_Fst_Snd] >>
 strip_tac (* 2*) >>
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 fs[rep_rel_all]) >>
 fs[rep_rel_all])
(form_goal
 “!z1 z2 z12. 
  Holds(ADDz,Pair(z1,z2),z12) <=>
  ?r1 r2 r12. asz(r1) = z1 & asz(r2) = z2 & 
              asz(r12) = z12 &
  Holds(ZR,Addj(r1,r2),r12)”));


val J2_i_z = prove_store("J2_i_z",
e0
(rpt strip_tac >> assume_tac J2_i >>
 rw[GSYM Addz_def] >> assume_tac ADDz_Fun >>
 drule $ GSYM Eval_def >> flip_tac >> arw[] >>
 once_rw[ADDz_alt0'] >>
 qexistsl_tac [‘Pair(a,b)’,‘Pair(c,d)’,
                ‘Addj(Pair(a, b), Pair(c, d))’] >>
 rw[] >> rw[ZR_refl])
(form_goal
 “!z1 z2 a b c d. z1 = asz(Pair(a,b)) & z2 = asz(Pair(c,d)) ==>
 Addz(z1,z2) = asz(Addj(Pair(a,b),Pair(c,d)))”));


(*
val J1_1' = prove_store("J1_1'",
e0
()
(form_goal
 “!a b c d e f a' b' c' d' e' f'.
  Holds(ZR,Pair(a,b),Pair(a',b')) &
  Holds(ZR,Pair(c,d),Pair(c',d')) & 
  Holds(ZR,Pair(e,f),Pair(e',f')) ==>
  Holds”));

*)


val Addz_eqn' = prove_store("Addz_eqn'",
e0
(rpt strip_tac >>
 assume_tac J2_i_z >>
 first_x_assum irule >> rw[])
(form_goal
 “!a b c d.
  Addz(asz(Pair(a,b)),asz(Pair(c,d))) = 
  asz(Addj(Pair(a,b),Pair(c,d)))”));

val z_has_rep = prove_store("z_has_rep",
e0
(strip_tac >> qexistsl_tac [‘rfst(z)’,‘rsnd(z)’] >>
 rw[GSYM rcp_def,rep_asz])
(form_goal
 “!z. ?a b. z = asz(Pair(a,b))”));

val Addz_assoc = prove_store("Addz_assoc",
e0
(rpt strip_tac >> 
 qspecl_then [‘z1’] strip_assume_tac z_has_rep >>
 qspecl_then [‘z2’] strip_assume_tac z_has_rep >>
 qspecl_then [‘z3’] strip_assume_tac z_has_rep >>
 arw[] >> 
 rw[Addz_eqn'] >> rw[Addj_property] >>
 rw[Addz_eqn'] >> rw[GSYM Addj_property] >>
 assume_tac J1_i >> fs[ZR_samez])
(form_goal
 “!z1 z2 z3.Addz(Addz(z1,z2),z3) = Addz(z1,Addz(z2,z3))”));

val zz_ex = prove_store("zz_ex",
e0
(qexists_tac ‘asz(0j)’ >> rw[])
(form_goal
 “?z. asz(0j) = z”));

val zz_def = zz_ex |> ex2fsym0 "0z" []
                   |> store_as "zz_def";


val Addz_zz = prove_store("Addz_zz",
e0
(strip_tac >> once_rw[z_eq_cond] >>
 qspecl_then [‘z’] strip_assume_tac z_has_rep >> 
 arw[] >>
 assume_tac J1_ii >>
 fs[ZR_samez] >> 
 rw[GSYM zz_def] >> rw[GSYM zj_def,Addz_eqn'] >>
 rw[zj_def] >> arw[] >>
 qexistsl_tac [‘Pair(a,b)’,‘Pair(a,b)’] >> rw[])
(form_goal
 “!z. Addz(z,0z) = z”));



val NEGz_def = 
fVar_Inst 
[("P",([("z",mem_sort Z),("nz",mem_sort Z)],
 “asz(Negj(rep(z))) = nz”))] 
(AX1 |> qspecl [‘Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "NEGz" [] |> conjE1
|> store_as "NEGz_def";

val NEGz_Fun = prove_store("NEGz_Fun",
e0
(rw[Fun_expand,NEGz_def] >> rpt strip_tac >-- 
 (qexists_tac ‘asz(Negj(rep(a)))’ >> rw[]) >>
 pop_assum_list (map_every (assume_tac o GSYM)) >>
 arw[])
(form_goal
 “isFun(NEGz)”));

val Negz_ex = prove_store("Negz_ex",
e0
(strip_tac >> qexists_tac ‘Eval(NEGz,z)’ >> rw[])
(form_goal
 “!z. ?nz. Eval(NEGz,z) = nz”));

val Negz_def = Negz_ex |> spec_all 
                       |> ex2fsym0 "Negz" ["z"]
                       |> gen_all 
                       |> store_as "Negz_def";

val NEGz_alt0 = prove_store("NEGz_alt0",
e0
(rw[NEGz_def,ZR_samez,rep_asz])
(form_goal
 “!z nz. Holds(NEGz,z,nz) <=>
      Holds(ZR,Negj(rep(z)),rep(nz))”));


val NEGz_alt0' = prove_store("NEGz_alt0'",
e0
(rw[NEGz_alt0] >> rpt strip_tac >> 
 dimp_tac >> strip_tac 
 >-- (qexistsl_tac [‘rep(z)’,‘rep(nz)’] >> rw[rep_asz]
 >> arw[]) >>
 irule $ iffRL ZR_cond >>
 qexistsl_tac [‘Negj(rz)’,‘rnz’] >>
 arw[] >>
 arw[ZR_samez,rep_asz] >>
 once_rw[GSYM ZR_samez] >>
 qsspecl_then [‘rep(z)’] assume_tac Pair_Fst_Snd >>
 once_arw[] >>
 qsspecl_then [‘rz’] assume_tac Pair_Fst_Snd >>
 once_arw[] >> 
 irule J2_ii >> rw[Pair_def'] >>
 rw[GSYM Pair_Fst_Snd] >>
 arw[GSYM rep_rel_all])
(form_goal
 “!z nz. Holds(NEGz,z,nz) <=>
  (?rz rnz. asz(rz) = z & asz(rnz) = nz & 
  Holds(ZR,Negj(rz),rnz))”));

val J2_ii_z = prove_store("J2_ii_z",
e0
(rpt strip_tac >> assume_tac J2_ii >>
 rw[GSYM Negz_def] >> assume_tac NEGz_Fun >>
 drule $ GSYM Eval_def >> flip_tac >> arw[] >>
 irule $ iffRL NEGz_alt0' >>
(* once_rw[NEGz_alt0] behavior weird, use irule instead *)
 qexistsl_tac [‘Pair(a,b)’,‘Negj(Pair(a,b))’] >> rw[] >>
 rw[ZR_refl])
(form_goal
 “!z a b. z = asz(Pair(a,b)) ==>
  Negz(z) = asz(Negj(Pair(a,b)))”));

val Negz_eqn = prove_store("Negz_eqn",
e0
(rpt strip_tac >> irule J2_ii_z >> arw[])
(form_goal
 “!a b. Negz(asz(Pair(a,b))) = asz(Negj(Pair(a,b)))”));

val Z2_iii = prove_store("Z2_iii",
e0
(rpt strip_tac >>
 qspecl_then [‘z’] strip_assume_tac z_has_rep >> 
 arw[] >> rw[Negz_eqn,Addz_eqn',Negj_property,Addj_property] >> rw[GSYM zz_def]  >>
 rw[GSYM ZR_samez,ZR_def,Pair_def',GSYM zj_def,Add_O,Add_O2] >>
 qspecl_then [‘b’,‘a’] accept_tac Add_sym)
(form_goal
 “!z. Addz(z,Negz(z)) = 0z”));

local 
val l1 = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”))] 
 N_ind_P 
val l2 = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “!c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”))] 
 N_ind_P |> rewr_rule[Suc_def]
val l3 = 
 fVar_Inst 
[("P",([("c",mem_sort N)],
 “Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”))] 
 N_ind_P |> rewr_rule[Suc_def]
in
val Sub_Add = prove_store("SUB_Add",
e0
(strip_tac >> match_mp_tac l1 >> rw[Sub_of_O] >> strip_tac >>
 strip_tac >> rw[Suc_def] >> strip_tac >> match_mp_tac l2 >>
 rw[Add_O2,Sub_O] >> strip_tac >> strip_tac >>
 match_mp_tac l3 >> rw[Sub_O,Add_O] >> rpt strip_tac >>
 rw[Add_Suc1] >> rw[Sub_mono_eq] >> arw[])
(form_goal “!a b c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”));
end

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

local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “!b.  Le(b,a) ==> ?p. Add(p,b) = a”))] 
 N_ind_P 
in
val Le_Add = prove_store("Le_Add",
e0
(strip_tac >> match_mp_tac l >> rw[Suc_def,Le_O_iff] >>
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
end

val lej_def = 
fVar_Inst 
[("P",([("ab",mem_sort $ Cross N N),("cd",mem_sort $ Cross N N)],
 “Le(Add(Fst(ab),Snd(cd)),Add(Snd(ab),Fst(cd)))”))] 
(AX1 |> qspecl [‘(N * N)’, ‘N * N’] |> uex_expand)
|> ex2fsym0 "lej" [] |> conjE1
|> store_as "lej_def";

val LE_def = 
fVar_Inst 
[("P",([("m",mem_sort N),("n",mem_sort N)],
 “Sub(m,n) = O”))] 
(AX1 |> qspecl [‘N’, ‘N’] |> uex_expand)
|> ex2fsym0 "LE" [] |> conjE1
|> store_as "LE_def";


val LT_def = 
fVar_Inst 
[("P",([("m",mem_sort N),("n",mem_sort N)],
 “Holds(LE,m,n) & ~(m = n)”))] 
(AX1 |> qspecl [‘N’, ‘N’] |> uex_expand)
|> ex2fsym0 "LT" [] |> conjE1
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
 rw[Le_def] >> drule Le_Add >>
 pop_assum (strip_assume_tac o GSYM) >> arw[] >>
 qsspecl_then [‘a2’,‘p’] assume_tac Add_sym >> 
 once_arw[] >> rw[Sub_Add] >> fs[Le_def] >>
 rw[Sub_of_O])
(form_goal “Trans(LE)”));


local
val l = 
 fVar_Inst 
[("P",([("p",mem_sort N)],
 “Lt(a,b) <=> Lt(Add(a,p),Add(b,p))”))] 
 N_ind_P 
in
val LESS_MONO_ADD = prove_store("LESS_MONO_ADD",
e0
(strip_tac >> strip_tac >> match_mp_tac l >>
 rw[Suc_def] >> rw[Add_O,Add_Suc,LESS_MONO_EQ])
(form_goal “!m n p. Lt(m,n) <=> Lt(Add(m,p),Add(n,p))”));
end

local
val l = 
 fVar_Inst 
[("P",([("p",mem_sort N)],
 “(Add(a,p) = Add(b,p)) <=> a = b”))] 
 N_ind_P 
in
val EQ_MONO_ADD_EQ = prove_store("EQ_MONO_ADD_EQ",
e0
(strip_tac >> strip_tac >> match_mp_tac l >>
 rw[Add_O,Suc_def,Add_Suc] >> rpt strip_tac >>
 arw[Suc_eq_eq])
(form_goal “!m n p.(Add(m,p) = Add(n,p)) <=> m = n”));
end

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

val lej_property = prove_store("lej_property",
e0
(rw[lej_def,Pair_def'])
(form_goal
 “!a b c d.Holds(lej,Pair(a,b),Pair(c,d)) <=>
 Le(Add(a,d),Add(b,c))”));

val lej_Refl = prove_store("lej_Refl",
e0
(rw[Refl_def,lej_def] >> rpt strip_tac >>
 qspecl_then [‘Fst(a)’,‘Snd(a)’] assume_tac Add_sym >>
 arw[] >> rw[Le_refl])
(form_goal
 “Refl(lej)”));

val Pair_has_comp = prove_store("Pair_has_comp",
e0
(rpt strip_tac >> 
 qexistsl_tac [‘Fst(ab)’,‘Snd(ab)’]>>
 rw[GSYM Pair_Fst_Snd])
(form_goal
 “!A B ab:mem(A * B). ?a b. ab = Pair(a,b)”));


(*LESS_EQ_LESS_EQ_MONO

LESS_EQ_MONO_ADD_EQ

LESS_EQ_TRANS
*)

(*
val LESS_EQ_LESS_EQ_MONO = prove_store("LESS_EQ_LESS_EQ_MONO",
e0
(rpt strip_tac >>
 irule )
(form_goal “!m n p q. Le(m,p) & Le(n,q) ==> Le(Add(m,n),Add(p,q)) ”));
*)

val Le_Add = prove_store("Le_Add",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(a,d)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘b’,‘a’] assume_tac Add_sym >>
 arw[] >>
 qsspecl_then [‘d’,‘a’] assume_tac Add_sym >>
 arw[] >> arw[LESS_EQ_MONO_ADD_EQ]
(*need sub of add*))
(form_goal
 “!a b c d. Le(a,c) & Le(b,d) ==> 
   Le(Add(a,b),Add(c,d))”));


(*
Add(a, b''), Add(b, a'')

(a + b'' <= b + a''
sufficient to prove 
a + b' + a'+ b'' <= b + b' +a' + a''
a + b' + a' + b'' <= b + a' + a' + b''

)

*)

val lej_Trans = prove_store("lej_Trans",
e0
(rw[lej_def,Trans_def] >> rpt strip_tac >>
 qsspecl_then  [‘a1’] assume_tac Pair_has_comp >>
 qsspecl_then  [‘a2’] assume_tac Pair_has_comp >>
 qsspecl_then  [‘a3’] assume_tac Pair_has_comp >>
 fs[] >> fs[] >> fs[Pair_def'] >> 
 qsuff_tac ‘Le(Add(Add(a,b''),Add(a',b')),
               Add(Add(b,a''),Add(a',b')))’
 >-- rw[LESS_EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘Add(a,b')’,‘Add(a',b'')’,
               ‘Add(b,a')’,‘Add(b',a'')’]
 assume_tac Le_Add >> rfs[] >>
 qsuff_tac ‘Add(Add(a, b'), Add(a', b'')) = 
 Add(Add(a, b''), Add(a', b')) & 
 Add(Add(b, a'), Add(b', a'')) = 
 Add(Add(b, a''), Add(a', b'))’
 >-- (strip_tac >> fs[]) >> strip_tac >--
 (once_rw[Add_sym] >>
 qsspecl_then [‘b''’,‘a’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc] >> 
 qsspecl_then [‘b''’,‘Add(a',b')’] assume_tac Add_sym>>
 arw[] >> rw[GSYM Add_assoc] >>
 qsspecl_then [‘a’,‘b'’] assume_tac Add_sym >>
 once_arw[] >> rw[Add_assoc] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac Add_sym >>
 once_arw[] >> rw[]) >>
 qsspecl_then [‘Add(b',a'')’,‘Add(b,a')’]
 assume_tac Add_sym >> arw[] >>
 qsspecl_then [‘a''’,‘b'’] assume_tac Add_sym >> arw[]>>
 qsspecl_then [‘a''’,‘b’] assume_tac Add_sym >> arw[]>>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(b', Add(b, a')) = Add(b, Add(a', b'))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘b'’,‘a'’] assume_tac Add_sym >>
 arw[] >>
 rw[Add_assoc] >> 
 qsspecl_then [‘b'’,‘b’] assume_tac Add_sym >> arw[])
(form_goal
 “Trans(lej)”));


(*TODO: something like AP_TERM_TAC*)
val J1_x = prove_store("J1_x",
e0
(rw[lej_def,Pair_def',Addj_property] >>
 rpt strip_tac >> 
 qsuff_tac 
 ‘Le(Add(Add(a, d), Add(e, f)), Add(Add(b, c), Add(e,f))) &
  Add(Add(a, e), Add(d, f)) = Add(Add(a, d), Add(e, f)) & 
  Add(Add(b, f), Add(c, e)) = Add(Add(b, c), Add(e, f))’
 >-- (rpt strip_tac >> arw[]) >>
 rpt strip_tac (* 3 *)
 >-- arw[LESS_EQ_MONO_ADD_EQ]
 >-- (rw[GSYM Add_assoc] >>
      qsuff_tac ‘Add(e, Add(d, f)) = Add(d, Add(e, f))’ 
      >-- (strip_tac >> arw[]) >>
      rw[Add_assoc] >>
      qsspecl_then [‘d’,‘e’] assume_tac Add_sym >> arw[]) >>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(f, Add(c, e)) = Add(c, Add(e, f))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘Add(c,e)’,‘f’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc])
(form_goal
 “!a b c d e f. Holds(lej,Pair(a,b),Pair(c,d)) ==> 
 Holds(lej,Addj(Pair(a,b),Pair(e,f)),
           Addj(Pair(c,d),Pair(e,f)))”));

val J2_iv = prove_store("J2_iv",
e0
(once_rw[lej_def] >> once_rw[ZR_def] >> rw[Pair_def'] >>
 rpt strip_tac >> 
 qsuff_tac 
 ‘(Le(Add(a, d), Add(b, c)) <=> 
  Le(Add(Add(a,d),Add(b',d')), Add(Add(b,c),Add(b',d')))) &
  (Le(Add(Add(a,d),Add(b',d')), Add(Add(b,c),Add(b',d'))) <=> 
  Le(Add(Add(a',d'),Add(b,d)), Add(Add(b',c'),Add(b,d)))) & 
  (Le(Add(Add(a',d'),Add(b,d)), Add(Add(b',c'),Add(b,d))) <=> 
 Le(Add(a',d'), Add(b',c')))’
 >-- (rpt strip_tac >> arw[]) >> rpt strip_tac (* 2 *)
 >-- rw[LESS_EQ_MONO_ADD_EQ] 
 >-- (qsuff_tac ‘Add(Add(a, d), Add(b', d')) = 
                Add(Add(a', d'), Add(b, d)) & 
                Add(Add(b, c), Add(b', d')) = 
                Add(Add(b', c'), Add(b, d))’
     >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
     >-- (qsspecl_then [‘Add(b',d')’,‘Add(a,d)’] 
          assume_tac Add_sym >> arw[] >>
          qsspecl_then [‘d'’,‘b'’] assume_tac Add_sym >> arw[] >>
          rw[Add_assoc] >>
          qsuff_tac ‘Add(Add(d', b'), a) = 
                     Add(Add(a', d'), b)’
          >-- (strip_tac >> arw[]) >>
          qsspecl_then [‘d'’,‘a'’] assume_tac Add_sym >> arw[] >>
          rw[GSYM Add_assoc] >> 
          qsspecl_then [‘a’,‘b'’] assume_tac Add_sym >> arw[]) >>
     qsspecl_then [‘Add(b',d')’,‘Add(b,c)’] assume_tac Add_sym >>
     arw[] >> 
     qsspecl_then [‘c’,‘b’] assume_tac Add_sym >> arw[] >>
     qsspecl_then [‘d’,‘b’] assume_tac Add_sym >> arw[] >>
     rw[Add_assoc] >>
     qsuff_tac ‘Add(Add(b', d'), c) = Add(Add(b', c'), d)’ 
     >-- (strip_tac >> arw[]) >>
     rw[GSYM Add_assoc] >>
     qsspecl_then [‘c’,‘d'’] assume_tac Add_sym >> arw[]) >>
 rw[LESS_EQ_MONO_ADD_EQ]
 )
(form_goal “!a b c d a' b' c' d'. Holds(ZR,Pair(a,b),Pair(a',b')) &
 Holds(ZR,Pair(c,d),Pair(c',d')) ==> 
 (Holds(lej,Pair(a,b),Pair(c,d)) <=> Holds(lej,Pair(a',b'),Pair(c',d')))”));

val LEz_def = 
fVar_Inst 
[("P",([("z1",mem_sort Z),("z2",mem_sort Z)],
 “Holds(lej,rep(z1),rep(z2))”))] 
(AX1 |> qspecl [‘Z’,‘Z’] |> uex_expand)
|> ex2fsym0 "LEz" [] |> conjE1
|> store_as "LEz_def";

val LEz_Refl = prove_store("LEz_Refl",
e0
(rw[Refl_def,LEz_def] >> 
 assume_tac lej_Refl >> fs[Refl_def])
(form_goal “Refl(LEz)”));

val LEz_Trans = prove_store("LEz_Trans",
e0
(assume_tac lej_Trans >> fs[Trans_def] >> rw[LEz_def] >> 
 rpt strip_tac >> 
 qsspecl_then [‘rep(a1)’] assume_tac Pair_has_comp >> 
 qsspecl_then [‘rep(a2)’] assume_tac Pair_has_comp >>
 qsspecl_then [‘rep(a3)’] assume_tac Pair_has_comp >>
 pop_assum_list (map_every strip_assume_tac) >>
 arw[] >> first_x_assum irule >> rfs[] >>
 qexists_tac ‘Pair(a',b')’ >> arw[]
 )
(form_goal “Trans(LEz)”));


val _ = new_pred "Asym" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val Asym_def = store_ax("Asym_def",“!A R:A->A. Asym(R) <=> 
!a b. Holds(R,a,b) & Holds(R,b,a) ==> a = b”)


local
val l = 
 fVar_Inst 
[("P",([("a",mem_sort N)],
 “a = Suc(a)”))] 
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



local
val l = 
 fVar_Inst 
[("P",([("b",mem_sort N)],
 “Lt(a,Add(a,Suc(b)))”))] 
 N_ind_P 
in
val Add_Suc_Lt = prove_store("Add_Suc_NEQ",
e0
(strip_tac >> match_mp_tac l >> rw[Suc_def] >> strip_tac 
 >-- (rw[Lt_def,Le_def,Add_Suc,Add_O,Sub_Suc,Pre_O,O_xor_Suc,
        Suc_NEQ,Pre_O,Sub_EQ_O]) >>
 rpt strip_tac >> rw[Add_Suc] >> rw[Lt_Suc_Le] >>
 rw[GSYM Add_Suc] >> fs[Lt_def])
(form_goal “!a b. Lt(a,Add(a,Suc(b)))”));
end



val LT_Trans = prove_store("LT_Trans",
e0
(rw[Trans_def] >> rw[LT_Lt] >> rw[Lt_def] >>
 assume_tac Le_trans >> rpt strip_tac >--
 (first_x_assum irule >> qexists_tac ‘a2’ >> arw[]) >>
 qby_tac ‘(?p1. Add(a1,Suc(p1)) = a2) & 
          ?p2. Add(a2,Suc(p2)) = a3’ >-- cheat >>
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

val Le_asym = LE_Asym |> rewr_rule[LE_Le,Asym_def]
                      |> store_as "Le_Asym";

val LEz_Asym = prove_store("LEz_Asym",
e0
(rw[Asym_def,LEz_def] >> strip_tac >> strip_tac >> 
 qsspecl_then [‘rep(a)’] assume_tac Pair_has_comp >> 
 qsspecl_then [‘rep(b)’] assume_tac Pair_has_comp >>
 pop_assum_list (map_every strip_assume_tac) >> arw[] >>
 rw[lej_def,Pair_def'] >>
 strip_tac >> once_rw[z_eq_cond] >>
 qexistsl_tac [‘Pair(a'',b'')’,‘Pair(a',b')’] >>
 rw[ZR_def,Pair_def'] >> rpt strip_tac 
 >-- (pop_assum_list (map_every (assume_tac o GSYM)) >>
      arw[rep_asz]) 
 >-- (pop_assum_list (map_every (assume_tac o GSYM)) >>
      arw[rep_asz]) >>
 irule Le_asym >> 
 qsspecl_then [‘a''’,‘b'’] assume_tac Add_sym >>fs[] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac Add_sym >> fs[])
(form_goal “Asym(LEz)”));

val _ = new_pred "Total" [("R",rel_sort (mk_set "A") (mk_set "A"))]

val Total_def = store_ax("Total_def",“!A R:A->A.Total(R)<=> !a b. Holds(R,a,b) | Holds(R,b,a)”);


val LEz_Total = prove_store("LEz_Total",
e0
(rw[Total_def,LEz_def,lej_def] >> rpt strip_tac >>
 qsspecl_then [‘rep(a)’] assume_tac Pair_has_comp >> 
 qsspecl_then [‘rep(b)’] assume_tac Pair_has_comp >>
 pop_assum_list (map_every strip_assume_tac) >> arw[Pair_def'] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac Add_sym >> arw[] >>
 qsspecl_then [‘a''’,‘b'’] assume_tac Add_sym >> arw[] >>
 rw[LESS_EQ_cases] )
(form_goal “Total(LEz)”));
