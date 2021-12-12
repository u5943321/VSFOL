
val ZR_subset_ex = 
    pred_subset_ex' |> allE $ rastt "(N * N) * (N * N)"
                   |> allE $ rastt $ q2str
‘Eq(N) o Pa(ADD o 
     Pa(p1(N,N) o p1(N * N,N * N),
        p2(N,N) o p2(N * N,N * N)),
     ADD o 
     Pa(p2(N,N) o p1(N * N,N * N), 
        p1(N,N) o p2(N * N,N * N)))’

val ZR_subset_def = ex2fsym "ZR" [] (iffRL $ eqT_intro $ spec_all ZR_subset_ex)
                        |> C mp (trueI []) |> gen_all

val ZRI_def = 
ex2fsym "ZRI" [] (iffRL $ eqT_intro $ spec_all ZR_subset_def)
                        |> C mp (trueI []) |> gen_all

val ZRI_Mono = conjE1 ZRI_def
                      |> store_as "ZRI_Mono";

val Z_ex = 
    iscoEq_ex |> allE $ rastt "ZR" 
            |> allE $ rastt "N * N"
            |> allE $ rastt "p1(N * N, N * N) o ZRI"
            |> allE $ rastt "p2(N * N, N * N) o ZRI"

val Z_def = ex2fsym "Z" [] (iffRL $ eqT_intro $ spec_all Z_ex)
                        |> C mp (trueI []) |> gen_all

val toZ_def = ex2fsym "toZ" [] (iffRL $ eqT_intro $ spec_all Z_def)
                        |> C mp (trueI []) |> gen_all

(*val _ = new_fun "Pow" (ob_sort,[("A",ob_sort)])*)

val ADDj_ex = prove_store("ADDj_ex",
e0
(qexists_tac
 ‘Pa(ADD o Pa(p1(N,N) o p1(N * N,N * N),
             p1(N,N) o p2(N * N,N * N)) , 
    ADD o Pa(p2(N,N) o p1(N * N,N * N),
             p2(N,N) o p2(N * N,N * N)))’ >> rw[])
(form_goal
 “?addj. 
 Pa(ADD o Pa(p1(N,N) o p1(N * N,N * N),
             p1(N,N) o p2(N * N,N * N)) , 
    ADD o Pa(p2(N,N) o p1(N * N,N * N),
             p2(N,N) o p2(N * N,N * N)))= addj”));


val ADDj_def = ex2fsym0 "ADDj" [] ADDj_ex;


val toZ_Epi = prove_store("toZ_Epi",
e0
(assume_tac toZ_def >>
 drule coEqa_Epi >> first_x_assum accept_tac)
(form_goal
 “Epi(toZ)”));


val REP_ex = prove_store("REP_ex",
e0
(assume_tac toZ_Epi >> drule Epi_has_section >>
 first_x_assum accept_tac)
(form_goal 
 “?rep. toZ o rep = id(Z)”));

val REP_def = REP_ex|> ex2fsym0 "REP" []
                    |> store_as "REP_def";

val ADDz_ex = prove_store("ADDz_ex",
e0
(qexists_tac ‘toZ o ADDj o Pa(REP o p1(Z,Z),REP o p2(Z,Z))’ >>
 rw[])
(form_goal
 “?addz. toZ o ADDj o Pa(REP o p1(Z,Z),REP o p2(Z,Z)) = addz”));



val ADDz_def = ADDz_ex |> ex2fsym0 "ADDz" []
                       |> store_as "ADDz_def";




val ADDj_SYM = prove_store("ADDj_SYM",
e0
(rw[GSYM Swap_def] >>
 irule FUN_EXT >> rpt strip_tac >>
 qby_tac
 ‘?a0 b0 c0 d0.a = Pa(Pa(a0,b0),Pa(c0,d0))’
 >-- cheat >>
 pop_assum strip_assume_tac >> arw[] >>
 rw[GSYM ADDj_def] >> rw[Pa_distr,o_assoc,p12_of_Pa] >> 
 qspecl_then [‘c0’,‘a0’] assume_tac ADD_SYM >>
 qspecl_then [‘d0’,‘b0’] assume_tac ADD_SYM >> 
 arw[]
 )
(form_goal
 “ADDj o Swap(N * N,N * N) = ADDj”));


val ADDz_SYM = prove_store("ADDz_SYM",
e0
(rpt strip_tac >>
 rw[GSYM ADDz_def,o_assoc,Pa_distr,p12_of_Pa] >> 
 qsuff_tac
 ‘ADDj o Pa(REP o z1,REP o z2) = 
  ADDj o Pa(REP o z2,REP o z1)’ 
 >-- (strip_tac >> arw[]) >>
 qby_tac
 ‘ADDj o Pa(REP o z1, REP o z2) = 
  ADDj o Swap(N * N,N * N) o Pa(REP o z2, REP o z1)’
 >-- (rw[GSYM Swap_def,Pa_distr,p12_of_Pa,o_assoc]) >>
 arw[] >> rw[GSYM o_assoc,ADDj_SYM])
(form_goal
 “!z1:1->Z z2:1->Z. ADDz o Pa(z1,z2) = ADDz o Pa(z2,z1)”));




val ZR_Refl = prove_store("ZR_Refl",
e0
(rw[Refl_Diag] >>
 rw[GSYM to_P_component] >> 
 fconv_tac 
 (basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))>>
 rw[GSYM ZRI_def] >> 
 irule FUN_EXT >> strip_tac >>
 qsspecl_then [‘a’] assume_tac has_components >>
 pop_assum strip_assume_tac >>
 arw[] >>
 rw[o_assoc,Pa_distr,p12_of_Pa,GSYM Diag_def,idL,
    GSYM True_def] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 rw[Eq_property_TRUE] >> 
 qsspecl_then [‘a'’,‘b’] accept_tac ADD_SYM
 )
(form_goal “Refl(p1(N * N, N * N) o ZRI,p2(N * N, N * N) o ZRI)”));




val ZR_Sym = prove_store("ZR_Sym",
e0
(rw[Sym_alt,GSYM to_P_component,p21_Swap] >>
 irule prop_2_half2 >> 
 assume_tac ZRI_Mono >>
 drule Swap_Mono >> arw[] >>
 rpt strip_tac >>
 dflip_tac >>  rw[GSYM ZRI_def] >>
 qby_tac
 ‘Swap(N * N,N * N) o (Swap(N * N, N * N) o ZRI) o xb = 
  Swap(N * N, N * N) o x’
 >-- arw[] >>
 pop_assum mp_tac >> rw[GSYM o_assoc,Swap_Swap_id,idL]>>
 strip_tac >>
 qby_tac 
 ‘?xb. Swap(N * N,N * N) o x = ZRI o xb’ 
 >-- (qexists_tac ‘xb’ >> arw[]) >>
 pop_assum mp_tac >>
 rw[GSYM ZRI_def,True1TRUE] >>
 rw[Eq_property_TRUE,o_assoc,Pa_distr,p12_of_Pa] >>
 qsspecl_then [‘x’] strip_assume_tac has_components >>
 qsspecl_then [‘a’] strip_assume_tac has_components >>
 qsspecl_then [‘b’] strip_assume_tac has_components >>
 arw[p12_of_Pa] >>
 rw[GSYM Swap_def,o_assoc,Pa_distr,p12_of_Pa] >>
 strip_tac >>
 qsspecl_then [‘a''’,‘b'’] assume_tac ADD_SYM >> fs[] >>
 qsspecl_then [‘b''’,‘a'’] assume_tac ADD_SYM >> fs[] )
(form_goal “Sym(p1(N * N, N * N) o ZRI,p2(N * N, N * N) o ZRI)”));







(*
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

*)

val ADD_assoc = prove_store("ADD_assoc",
e0
(assume_tac equality_ind >>
 pop_assum (qspecl_then [‘N * N’,‘N’,‘ADD o Pa(p2(N * N,N),ADD o p1(N * N,N))’,‘N * N’,‘ADD o Pa(ADD o Pa(p2(N * N,N),p1(N,N) o p1(N * N,N)), p2(N,N) o p1(N * N,N))’] assume_tac) >> 
 qsuff_tac
 ‘!n0:1->N p m.ADD o Pa(m, ADD o Pa(n0,p)) = 
           ADD o Pa(ADD o Pa(m,n0),p)’
 >-- (strip_tac >>  arw[]) >>
 strip_tac >> strip_tac >>
 first_x_assum
 (qsspecl_then [‘Pa(n0,p)’,‘Pa(n0,p)’] assume_tac) >>
 fs[Pa_distr,o_assoc,p12_of_Pa] >>
 pop_assum (K all_tac) >>
 rw[ADD_O_n,ADD_el,ADD_SUC] >> rpt strip_tac >>
 arw[])
(form_goal
 “!m:1->N n0 p. ADD o Pa(m, ADD o Pa(n0,p)) = 
           ADD o Pa(ADD o Pa(m,n0),p)”));

val ZR_Trans =prove_store("ZR_Trans",
e0
(assume_tac ZRI_Mono >>
 irule $ iffRL Trans_alt' >> rw[GSYM to_P_component]>>
 arw[] >> dflip_tac >> rpt strip_tac >>
 qby_tac
 ‘?r01. Pa(h0, h1) = ZRI o r01’
 >-- (qexists_tac ‘r01’ >> arw[]) >>
 qby_tac
 ‘?r12. Pa(h1, h2) = ZRI o r12’
 >-- (qexists_tac ‘r12’ >> arw[]) >>
 pop_assum mp_tac >> pop_assum mp_tac >>
 rw[GSYM ZRI_def,True1TRUE,Pa_distr,
    Eq_property_TRUE,o_assoc,p12_of_Pa] >> 
 qsspecl_then [‘h0’] assume_tac has_components >> 
 pop_assum strip_assume_tac >>
 qsspecl_then [‘h1’] assume_tac has_components >> 
 pop_assum strip_assume_tac >> 
 qsspecl_then [‘h2’] assume_tac has_components >> 
 pop_assum strip_assume_tac >>
 arw[p12_of_Pa] >> rpt strip_tac >>
 qby_tac
 ‘ADD o Pa(ADD o Pa(a, b''),b') = 
  ADD o Pa(a,ADD o Pa(b',b''))’
 >-- (qspecl_then [‘b'’,‘b''’] assume_tac ADD_SYM >>
      arw[] >> rw[ADD_assoc]) >>
 fs[ADD_assoc] >> rfs[] >>
 fs[GSYM ADD_assoc] >> rfs[] >>
 qspecl_then [‘b'’,‘a''’] assume_tac ADD_SYM >> fs[] >>
 fs[ADD_assoc] >>
 assume_tac ADD_SUB >>
 first_assum (qspecl_then [‘ADD o Pa(a, b'')’,‘b'’]
 assume_tac) >>
 first_x_assum (qspecl_then [‘ADD o Pa(b, a'')’,‘b'’]
 assume_tac) >>
 pop_assum (assume_tac o GSYM) >>once_arw[] >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 pop_assum (K all_tac) >>
 arw[])
(form_goal
 “Trans(p1(N * N, N * N) o ZRI,p2(N * N, N * N) o ZRI)”));

val Thm6_ZR = prove_store("Thm6_ZR",
e0
(assume_tac Thm6_isEq >> 
 qby_tac ‘ZRI =  Pa(p1(N * N, N * N) o ZRI, p2(N * N, N * N) o ZRI)’
 >-- rw[GSYM to_P_component] >> once_arw[] >>
 first_x_assum irule >> rw[GSYM to_P_component] >> 
 rw[ZRI_Mono,ZR_Trans,ZR_Sym,ZR_Refl,toZ_def])
(form_goal
 “isEq(toZ o p1(N * N, N * N),toZ o p2(N * N,N * N),ZRI)”));


val Addz_ex = prove_store("Addz_ex",
e0
(rpt strip_tac >> qexists_tac ‘ADDz o Pa(z1,z2)’ >> rw[])
(form_goal
 “!X z1:X->Z z2. ?z12. ADDz o Pa(z1,z2) = z12”));

val Addz_def = Addz_ex |> spec_all |> ex2fsym0 "Addz" ["z1","z2"]
                       |> gen_all |> store_as "Addz_def";

val asz_ex = prove_store("asz_ex",
e0
(rpt strip_tac >> qexists_tac ‘toZ o pair’ >> rw[])
(form_goal “!X pair:X-> N * N. ?z. toZ o pair= z”));

val asz_def = asz_ex |> spec_all |> ex2fsym0 "asz" ["pair"]
                     |> gen_all |> store_as "asz_def";


val Addj_ex = prove_store("Addj_ex",
e0
(rpt strip_tac >> qexists_tac ‘ADDj o Pa(ab,cd)’ >> rw[])
(form_goal “!X ab:X->N * N cd. ?acbd.ADDj o Pa(ab,cd) = acbd”));

val Addj_def = Addj_ex |> spec_all |> ex2fsym0 "Addj" ["ab","cd"]
                       |> gen_all |> store_as "Addj_def";

val _ = new_pred "ZR" [("ab",ar_sort (mk_ob "X") (Po N N)),
                       ("cd",ar_sort (mk_ob "X") (Po N N))]

val ZR_def0 = store_ax("ZR_def0",
“!X ab:X->N * N cd. ZR(ab,cd) <=> ?x0:X-> ZR.Pa(ab,cd) = ZRI o x0”);


val Add_ex = prove_store("Add_ex",
e0
(rpt strip_tac >> qexists_tac ‘ADD o Pa(a,b)’ >> rw[])
(form_goal
 “!a:X->N b. ?ab. ADD o Pa(a,b) = ab”));

val Add_def = Add_ex |> spec_all |> ex2fsym0 "Add" ["a","b"]
                     |> gen_all
                     |> store_as "Add_def";

val Fst_ex = prove_store("Fst_ex",
e0
(rpt strip_tac >> qexists_tac ‘p1(A,B) o ab’ >> rw[])
(form_goal “!X A B ab:X->A * B. ?fst.p1(A,B) o ab = fst”));


val Snd_ex = prove_store("Snd_ex",
e0
(rpt strip_tac >> qexists_tac ‘p2(A,B) o ab’ >> rw[])
(form_goal “!X A B ab:X->A * B. ?snd.p2(A,B) o ab = snd”));

val Fst_def = Fst_ex |> spec_all |> ex2fsym0 "Fst" ["ab"]
                     |> gen_all
                     |> store_as "Fst_def";



val Snd_def = Snd_ex |> spec_all |> ex2fsym0 "Snd" ["ab"]
                     |> gen_all
                     |> store_as "Snd_def";

val Fst_Snd_Pa = p12_of_Pa |> rewr_rule[Fst_def,Snd_def]
                           |> store_as "Fst_Snd_Pa";

val Fst_Pa = p1_of_Pa |> rewr_rule[Fst_def] |> store_as "Fst_Pa";

val Snd_Pa = p2_of_Pa |> rewr_rule[Snd_def] |> store_as "Snd_Pa";

val ZR_def = prove_store("ZR_def",
e0
(rpt strip_tac >> 
 rw[ZR_def0,GSYM ZRI_def,GSYM Eq_property,p12_of_Pa,Pa_distr,o_assoc] >>
 qsspecl_then [‘ab’] strip_assume_tac has_components >>
 qsspecl_then [‘cd’] strip_assume_tac has_components >> arw[p12_of_Pa,Fst_Snd_Pa] >> dimp_tac >> strip_tac >> fs[GSYM Add_def])
(form_goal
 “!X ab:X->N * N cd. ZR(ab,cd) <=> 
  Add(Fst(ab),Snd(cd)) = Add(Snd(ab),Fst(cd))”));


val rep_ex = prove_store("rep_ex",
e0
(rpt strip_tac >> qexists_tac ‘REP o z’ >> rw[] )
(form_goal “!X z:X->Z.?r. REP o z = r”));

val rep_def= rep_ex |> spec_all |> ex2fsym0 "rep" ["z"] 
                    |> gen_all |> store_as "rep_def";

val rep_asz = prove_store("rep_asz",
e0
(rpt strip_tac >> rw[GSYM rep_def,GSYM asz_def,REP_def,GSYM o_assoc,idL])
(form_goal “!X z:X->Z. asz(rep(z)) = z”)); 

(*asz_def rep_def toZ_def REP_def*)

val lflip_tac =
fconv_tac 
 (land_fconv no_conv 
 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))

val rflip_tac =
fconv_tac 
 (rand_fconv no_conv 
 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))



val samez_cond = prove_store("samez_cond",
e0
(rw[ZR_def,GSYM asz_def] >> 
 assume_tac Thm6_ZR >> drule via_Eq_iff >> 
 rpt strip_tac >>
 (*qsspecl_then [‘ab’] strip_assume_tac has_components >>
 qsspecl_then [‘cd’] strip_assume_tac has_components >> fs[] >> *)
 first_x_assum (qsspecl_then [‘Pa(ab,cd)’] assume_tac) >> fs[o_assoc,p12_of_Pa] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> lflip_tac >> 
 rw[GSYM ZR_def] >> rw[ZR_def0])
(form_goal “!X ab:X-> N * N cd. asz(ab) = asz(cd) <=> ZR(ab,cd)”));

val ZR_samez = GSYM samez_cond;

val rep_asz_ZR = prove_store("rep_asz_ZR",
e0
(rw[GSYM samez_cond,rep_asz])
(form_goal “!X ab:X->N * N.ZR(ab,rep(asz(ab)))”));

val rep_ZR_eq = prove_store("rep_ZR_eq",
e0
(rw[ZR_samez,rep_asz])
(form_goal
 “!X z1:X->Z z2. ZR(rep(z1),rep(z2)) <=> z1 = z2”));

val z_eq_cond = prove_store("z_eq_cond",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexistsl_tac [‘rep(z1)’,‘rep(z2)’] >> arw[rep_asz,rep_ZR_eq]) >>
 fs[ZR_samez])
(form_goal “!X z1:X->Z z2. z1 = z2 <=> ?ab cd. asz(ab) = z1 & asz(cd) = z2 & ZR(ab,cd) ”));

val Add_sym = ADD_SYM |> rewr_rule[Add_def] |> store_as "Add_sym";

val ZR_refl = prove_store("ZR_refl",
e0
(rw[ZR_def] >> rpt strip_tac >>
 qsspecl_then [‘Fst(ab)’,‘Snd(ab)’] assume_tac Add_sym >> arw[])
(form_goal “!ab:1->N * N.ZR(ab,ab)”));


val ZR_sym = prove_store("ZR_sym",
e0
(rw[ZR_def] >> rpt strip_tac >> lflip_tac >>
 qsspecl_then [‘Fst(ab)’,‘Snd(cd)’] assume_tac Add_sym >> arw[] >> 
 qsspecl_then [‘Fst(cd)’,‘Snd(ab)’] assume_tac Add_sym >> arw[])
(form_goal “!ab:1->N * N cd.ZR(ab,cd) <=> ZR(cd,ab)”));


val ZR_trans = prove_store("ZR_sym",
e0
(assume_tac ZR_Trans >> 
 assume_tac ZRI_Mono >>
 pop_assum mp_tac >> once_rw[to_P_component] >> strip_tac >> 
 drule Trans_alt' >> fs[GSYM to_P_component] >> pop_assum (K all_tac) >>
 rw[ZR_def0] >> rpt strip_tac >> dflip_tac >> first_x_assum irule >>
 qexistsl_tac [‘cd’,‘x0’,‘x0'’] >> arw[])
(form_goal “!ab:1->N * N  cd ef.ZR(ab,cd) & ZR(cd,ef) ==> ZR(ab,ef)”));

val ZR_cond = prove_store("ZR_cond",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (qexistsl_tac [‘ab’,‘cd’] >> arw[ZR_refl]) >>
 qby_tac ‘ZR(ab,cd1)’ 
 >-- (irule ZR_trans >> qexists_tac ‘ab1’ >> arw[]) >>
 qby_tac ‘ZR(cd1,cd)’
 >-- (irule $ iffLR ZR_sym >> arw[]) >>
 irule ZR_trans >>
 qexists_tac ‘cd1’ >> arw[])
(form_goal “!ab:1->N * N cd.ZR(ab,cd) <=> ?ab1 cd1. ZR(ab,ab1) & ZR(cd,cd1) & ZR(ab1,cd1)”));


val rep_rel_all = prove_store("rep_rel_all",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
      irule $ iffLR ZR_sym >> rw[rep_asz_ZR]) >>
 fs[ZR_samez,rep_asz])
(form_goal
 “!z:1->Z rz.asz(rz) = z <=> ZR(rep(z),rz)”));

val Pa_Fst_Snd = to_P_component |> rewr_rule[Fst_def,Snd_def] |> GSYM
                                |> store_as "Pa_Fst_Snd";

val z_has_rep = prove_store("z_has_rep",
e0
(strip_tac >> rw[GSYM asz_def] >> rpt strip_tac >>
 qexistsl_tac [‘Fst(rep(z))’,‘Snd(rep(z))’] >>
 rw[Pa_Fst_Snd] >> rw[asz_def,rep_asz])
(form_goal
 “!X z:X->Z. ?a b. z = asz(Pa(a,b))”));


val Add_assoc = ADD_assoc |> rewr_rule[Add_def] |> store_as "Add_assoc";

val Addj_property =  prove_store("Addj_property",
e0
(rw[GSYM Addj_def,GSYM ADDj_def,p12_of_Pa,Pa_distr,o_assoc,GSYM Add_def])
(form_goal
 “!a:1->N b c d. Addj(Pa(a,b),Pa(c,d)) = Pa(Add(a,c),Add(b,d))”));


val J1_i = prove_store("J1_i",
e0
(rw[ZR_def,Addj_property] >> rpt strip_tac >> 
 rw[Fst_Snd_Pa] >>
 qsspecl_then [‘Add(Add(a, c), e)’,‘Add(b, Add(d, f))’] assume_tac Add_sym >>
 arw[] >> rw[GSYM Add_assoc])
(form_goal “!a b c d e f:1->N. 
 ZR(Addj(Addj(Pa(a,b),Pa(c,d)),Pa(e,f)),
    Addj(Pa(a,b),Addj(Pa(c,d),Pa(e,f))))”));


val ZR_def' = prove_store("ZR_def'",
e0
(rw[ZR_def] >> rpt strip_tac >> 
 qsspecl_then [‘Snd(ab)’,‘Fst(cd)’] assume_tac Add_sym >>
 arw[])
(form_goal
 “!ab:1 ->N * N cd.
        ZR(ab, cd) <=> Add(Fst(ab), Snd(cd)) = Add(Fst(cd), Snd(ab))”));

val Add_sym' = GSYM Add_sym

val J2_i = prove_store("J2_i",
e0
(rw[Addj_property,ZR_def',Fst_Snd_Pa] >>
 rpt strip_tac >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘d'’,‘b'’] assume_tac Add_sym' >> arw[] >>
 qspecl_then [‘c’,‘d'’,‘b'’] assume_tac Add_assoc >>
 arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘Add(c',Add(d,b'))’,‘a’] assume_tac Add_sym' >> 
 arw[] >>
 rw[GSYM Add_assoc] >>
 qspecl_then [‘a’,‘b'’] assume_tac Add_sym' >>
 arw[] >>
 qsspecl_then [‘Add(c', Add(b, d))’,‘a'’]
 assume_tac Add_sym' >> arw[] >>
 rw[GSYM Add_assoc] >> 
 qsuff_tac
 ‘Add(d, Add(a', b)) = Add(b, Add(d, a'))’
 >-- (strip_tac >> arw[]) >>
 qspecl_then [‘Add(a',b)’,‘d’] assume_tac Add_sym' >>
 arw[] >> 
 qspecl_then [‘a'’,‘d’] assume_tac Add_sym' >> arw[] >>
 rw[Add_assoc] >>
 qspecl_then [‘a'’,‘b’] assume_tac Add_sym' >> arw[])
(form_goal
 “!a:1->N b a' b' c d c' d'. ZR(Pa(a,b),Pa(a',b')) & ZR(Pa(c,d),Pa(c',d')) ==>
 ZR(Addj(Pa(a,b),Pa(c,d)),Addj(Pa(a',b'),Pa(c',d')))”));


val J2_i_z = prove_store("J2_i_z",
e0
(rpt strip_tac >> assume_tac J2_i >>
 rw[GSYM Addz_def,GSYM ADDz_def,o_assoc,Pa_distr] >> rw[asz_def,p12_of_Pa] >>
 rw[samez_cond] >> arw[] >>
 rw[rep_def,Addj_def]  >> 
 qsspecl_then [‘rep(asz(Pa(a,b)))’] strip_assume_tac has_components >>
 qsspecl_then [‘rep(asz(Pa(c,d)))’] strip_assume_tac has_components >>
 arw[] >> first_x_assum irule >> pop_assum_list (map_every (assume_tac o GSYM)) >>
 arw[] >> rw[GSYM rep_rel_all] >> arw[])
(form_goal
 “!z1:1->Z z2 a b c d. z1 = asz(Pa(a,b)) & z2 = asz(Pa(c,d)) ==>
 Addz(z1,z2) = asz(Addj(Pa(a,b),Pa(c,d)))”));


val Addz_eqn' = prove_store("Addz_eqn'",
e0
(rpt strip_tac >>
 assume_tac J2_i_z >>
 first_x_assum irule >> rw[])
(form_goal
 “!a:1->N b c d.
  Addz(asz(Pa(a,b)),asz(Pa(c,d))) = 
  asz(Addj(Pa(a,b),Pa(c,d)))”));

val ADDz_assoc = prove_store("ADDz_assoc",
e0
(rpt strip_tac >> 
 qsspecl_then [‘z1’] strip_assume_tac z_has_rep >>
 qsspecl_then [‘z2’] strip_assume_tac z_has_rep >>
 qsspecl_then [‘z3’] strip_assume_tac z_has_rep >>
 arw[] >> 
 rw[Addz_eqn'] >> rw[Addj_property] >>
 rw[Addz_eqn'] >> rw[GSYM Addj_property] >>
 assume_tac J1_i >> fs[ZR_samez])
(form_goal
 “!z1:1->Z z2 z3. Addz(Addz(z1,z2),z3) = Addz(z1,Addz(z2,z3))”));




val zj_ex = prove_store("zj_ex",
e0
(qexists_tac ‘Pa(O,O)’ >> rw[])
(form_goal
 “?zj.Pa(O,O) = zj”));

val zj_def = zj_ex |> ex2fsym0 "0j" []
                   |> store_as "zj_def";



val NEGj_ex = prove_store("NEGj_ex",
e0
(rpt strip_tac >> qexists_tac ‘Swap(N,N)’ >> rw[])
(form_goal “?NEGj.Swap(N,N) =NEGj ”));

val NEGj_def = NEGj_ex |> spec_all |> ex2fsym0 "NEGj" []
                       |> gen_all |> store_as "NEGj_def";



val NEGj_property = prove_store("NEGj_property",
e0
(rpt strip_tac >> rw[GSYM NEGj_def,Swap_Pa])
(form_goal “!X a:X->N b. NEGj o Pa(a,b) = Pa(b,a)”));


val Negj_ex = prove_store("Negj_ex",
e0
(rpt strip_tac >> qexists_tac ‘NEGj o ab’ >> rw[])
(form_goal “!X ab:X->N * N. ?nab. NEGj o ab = nab”));

val Negj_def = Negj_ex |> spec_all |> ex2fsym0 "Negj" ["ab"] 
                       |> gen_all |> store_as "Negj_def";

val Negj_property = NEGj_property |> rewr_rule[Negj_def]


val Add_El = ADD_el |> rewr_rule [Add_def] |> store_as "Add_El";

val Add_O_n = ADD_O_n |> rewr_rule[Add_def] |> store_as "Add_O_n";


val J1_ii = prove_store("J1_ii",
e0
(rw[GSYM zj_def,Addj_property,ZR_def,Fst_Snd_Pa,Add_O_n,Add_El] >> rpt strip_tac >>
 qsspecl_then [‘a’,‘b’] accept_tac Add_sym)
(form_goal
 “!a b.ZR(Addj(Pa(a,b),0j),Pa(a,b))”));


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
 qsspecl_then [‘z’] strip_assume_tac z_has_rep >> 
 arw[] >>
 assume_tac J1_ii >>
 fs[ZR_samez] >> 
 rw[GSYM zz_def] >> rw[GSYM zj_def,Addz_eqn'] >>
 rw[zj_def] >> arw[] >>
 qexistsl_tac [‘Pa(a,b)’,‘Pa(a,b)’] >> rw[])
(form_goal
 “!z. Addz(z,0z) = z”));

val Z2_ii = Addz_zz |> store_as "Z2_ii";

val Negz_ex =  prove_store("Negz_ex",
e0
(rpt strip_tac >> qexists_tac ‘asz(Negj(rep(z)))’ >> rw[])
(form_goal “!X z:X->Z.?nz. asz(Negj(rep(z))) = nz”));

val Negz_def = Negz_ex |> spec_all |> ex2fsym0 "Negz" ["z"]
                       |> gen_all |> store_as "Negz_def";


val J2_ii = prove_store("J2_ii",
e0
(rw[ZR_def,Negj_property,Fst_Snd_Pa] >>rpt strip_tac >> arw[])
(form_goal
 “!X a:X->N b a' b'. ZR(Pa(a,b),Pa(a',b')) ==> 
  ZR(Negj(Pa(a,b)),Negj(Pa(a',b')))”));


val J2_ii_z = prove_store("J2_ii_z",
e0
(rpt strip_tac >> assume_tac J2_ii >>
 rw[GSYM Negz_def] >> rw[samez_cond] >> 
 qsspecl_then [‘rep(z)’] strip_assume_tac has_components >> arw[] >>
 first_x_assum irule >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[GSYM rep_rel_all])
(form_goal
 “!a:1->N b z. z = asz(Pa(a,b)) ==>
  Negz(z) = asz(Negj(Pa(a,b)))”));


val Negz_eqn = prove_store("Negz_eqn",
e0
(rpt strip_tac >> irule J2_ii_z >> arw[])
(form_goal
 “!a:1->N b. Negz(asz(Pa(a,b))) = asz(Negj(Pa(a,b)))”));


val J1_iii = prove_store("J1_iii",
e0
(rw[Addj_property,GSYM zj_def,Negj_property,ZR_def,
    Fst_Snd_Pa,Add_El,Add_O_n] >>
 rpt strip_tac >>
 qspecl_then [‘a’,‘b’] assume_tac Add_sym >>
 first_x_assum accept_tac)
(form_goal
 “!a b. ZR(Addj(Pa(a,b),Negj(Pa(a,b))),0j)”));



val Z2_iii = prove_store("Z2_iii",
e0
(rpt strip_tac >>
 qsspecl_then [‘z’] strip_assume_tac z_has_rep >> 
 arw[] >> rw[Negz_eqn,Addz_eqn',Negj_property,Addj_property] >> rw[GSYM zz_def]  >>
 rw[GSYM ZR_samez,ZR_def,Fst_Snd_Pa,GSYM zj_def,Add_El,Add_O_n] >>
 qspecl_then [‘a’,‘b’] accept_tac Add_sym)
(form_goal
 “!z. Addz(z,Negz(z)) = 0z”));

val _ = new_pred "Le" [("m",ar_sort (mk_ob "X") N),
                       ("n",ar_sort (mk_ob "X") N)]

val Le_def0 = store_ax("Le_def0",
 “!X a:X->N b:X->N. Le(a,b) <=> Char(LE) o Pa(a,b) = True(X)”);


val Le_def1 = Le_def0 |> allE (rastt "1")
                      |> rewr_rule[True1TRUE]

val _ = new_pred "Lt" [("m",ar_sort (mk_ob "X") N),
                       ("n",ar_sort (mk_ob "X") N)]

val Lt_def0 = store_ax("Lt_def0",
 “!X a:X->N b:X->N. Lt(a,b) <=> Char(LT) o Pa(a,b) = True(X)”);


val Lt_def1 = Lt_def0 |> allE (rastt "1")
                     |> rewr_rule[True1TRUE]


val Le_def = LE_SUB |> rewr_rule[GSYM Le_def1,Sub_def]

val Lt_def = prove_store("Lt_def",
e0
(rw[Lt_def1,CLT_iff_LE_NE,Le_def1,LE_Char_LEo])
(form_goal 
 “!a:1->N b. Lt(a,b) <=> Le(a,b) & ~(a = b)”));

val Sub_of_O = SUB_0 |> rewr_rule[Sub_def]
                     |> store_as "Sub_of_O";

val Sub_O = SUB_0_cj2 |> rewr_rule[Sub_def]
                      |> store_as "Sub_O";

val Add_O = ADD_el |> spec_all |> conjE1
                   |> gen_all 
                   |> rewr_rule[Add_def]
                   |> store_as "Add_O";


val Add_Suc = ADD_el |> spec_all |> conjE2
                   |> gen_all 
                   |> rewr_rule[Add_def,Suc_def]
                   |> store_as "Add_O";

val Add_O2 = ADD_O_n |> rewr_rule[Add_def]
                      |> store_as "Add_O2";

val Add_Suc1 = ADD_SUC |> rewr_rule[Add_def,Suc_def]
                       |> store_as "Add_Suc1";

val Sub_mono_eq = SUB_MONO_EQ
                      |> rewr_rule[Sub_def,Suc_def]
                      |> store_as "Sub_mono_eq";

val Sub_Add = prove_store("Sub_Add",
e0
(qby_tac
 ‘?P0. !c b a:1->N. P0 o Pa3(c,b,a) = TRUE <=> 
  Sub(a,Add(b,c)) = Sub(Sub(a,b),c)’ >-- 
 (qexists_tac 
 ‘Eq(N) o Pa(SUB o Pa(p33(N,N,N),ADD o Pa(p32(N,N,N),p31(N,N,N))),SUB o Pa(SUB o Pa(p33(N,N,N),p32(N,N,N)),p31(N,N,N)))’ >>
  once_rw[GSYM Pa3_def] >> 
  once_rw[GSYM p31_def] >> once_rw[GSYM p32_def] >>
  once_rw[o_assoc] >> once_rw[Pa_distr] >>
  once_rw[Eq_property_TRUE] >> 
  once_rw[GSYM p33_def] >>
  rw[o_assoc,p12_of_Pa,Pa_distr] >>
  rw[Sub_def,Add_def]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac 
 ‘!a b c. P0 o Pa3(c,b,a) = TRUE’
 >-- (rpt strip_tac >> fs[]) >>
 rw[triple_IND',GSYM Pa3_def] >>
 fs[GSYM Pa3_def] >> rw[Suc_def] >>
 rw[Sub_of_O] >> strip_tac >> strip_tac >> 
 strip_tac (* 2 *)
 >-- rw[Sub_O,Add_O2] >>
 rpt strip_tac (* 2 *)
 >-- rw[Sub_O,Add_O] >>
 rw[Add_Suc1] >> rw[Sub_mono_eq] >> arw[])
(form_goal
 “!a:1->N b c. Sub(a,Add(b,c)) = Sub(Sub(a,b),c)”));

val Le_O_iff = prove_store("Le_O_iff",
e0
(strip_tac >> dimp_tac >> strip_tac 
 >-- (fs[Le_def1] >> drule LE_O_O >> arw[]) >>
 arw[] >> rw[Le_def] >> rw[Sub_O])
(form_goal
 “!a. Le(a,O) <=> a = O”));

val Le_cases = LE_cases 
                   |> rewr_rule[GSYM Le_def1,
                                GSYM Lt_def1]
                   |> store_as "Le_cases";

val Lt_Suc_Le = LESS_SUC_LEQ 
                    |> rewr_rule[GSYM Le_def1,
                                GSYM Lt_def1,
                                Suc_def]
                   |> store_as "Lt_Suc_Le";

val Le_Suc = prove_store("Le_Suc",
e0
(rpt strip_tac >> drule Le_cases >>
 pop_assum strip_assume_tac >--
 (drule $ iffLR Lt_Suc_Le >> arw[]) >> arw[])
(form_goal 
 “!a:1->N b. Le(a,Suc(b)) ==> (Le(a,b) | a = Suc(b))”));


val Le_Add_ex = prove_store("Le_Add",
e0
(qby_tac
 ‘?P. !n m. P o Pa(n,m) = TRUE <=> 
  (Le(n,m) ==> ?p. Add(p,n) = m)’
 >-- cheat >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘!m. ALL(P) o m = TRUE’ 
 >-- arw[ALL_property] >>
 rw[IP_el] >> arw[ALL_property,Suc_def,Le_O_iff] >>
 rpt strip_tac (* 2 *)
 >-- (arw[] >> qexists_tac ‘O’ >> rw[Add_O]) >>
 drule Le_Suc >> pop_assum strip_assume_tac (* 2 *)
 >-- (first_x_assum drule >>
     pop_assum strip_assume_tac >>
     qexists_tac ‘Suc(p)’ >> arw[Add_Suc1]) >>
 arw[] >> qexists_tac ‘O’ >> rw[Add_O2])
(form_goal
 “!m:1->N n. Le(n,m) ==> ?p. Add(p,n) = m”));


val lej_ex = prove_store("lej_ex",
e0
(qexists_tac
 ‘Char(LE) o Pa(
  ADD o Pa(p1(N,N) o p1(N * N,N * N),
           p2(N,N) o p2(N * N,N * N)),
  ADD o Pa(p2(N,N) o p1(N * N,N * N),
           p1(N,N) o p2(N * N,N * N))
)’ >-- rpt strip_tac >>
 qsspecl_then [‘ab’] assume_tac has_components >>
 qsspecl_then [‘cd’] assume_tac has_components >>
 fs[] >> 
 rw[Pa_distr,p12_of_Pa,o_assoc] >>
 rw[Le_def1])
(form_goal
 “?lej. !ab:1->N * N cd. 
  lej o Pa(ab,cd) = TRUE <=> 
  Le(ADD o Pa(p1(N,N) o ab,p2(N,N) o cd),
     ADD o Pa(p2(N,N) o ab,p1(N,N) o cd))”));

val lej_def = ex2fsym0 "lej" [] lej_ex
                       |> store_as "lej_def";

val Le_trans = prove_store("Le_trans",
e0
(rpt strip_tac >> rw[Le_def] >>
 drule Le_Add_ex >> pop_assum (strip_assume_tac o GSYM)>>
 arw[] >> 
 qsspecl_then [‘p’,‘b’] assume_tac Add_sym >>
 once_arw[] >> rw[Sub_Add] >> fs[Le_def] >>
 rw[Sub_of_O])
(form_goal
 “!a:1->N b c. Le(a,b) & Le(b,c) ==> Le(a,c)”));

val Lt_mono_eq = 
LESS_MONO_EQ 
    |> rewr_rule[GSYM Lt_def1,Suc_def]
    |> store_as "Lt_mono_eq";

val LESS_MONO_ADD = prove_store("LESS_MONO_ADD",
e0
(strip_tac >> strip_tac >>
qby_tac
 ‘?P. !p.  
 P o p = TRUE <=> 
 (Lt(m,n) <=> Lt(Add(m,p),Add(n,p))) ’
 >-- (
 qexists_tac ‘Iff(Char(LT) o Pa(m,n) o To1(N),
              Char(LT) o 
              Pa(ADD o Pa(m o To1(N),id(N)),
                 ADD o Pa(n o To1(N),id(N))))’
 >-- rw[GSYM Iff_def,Pa_distr,p12_of_Pa,o_assoc,
        IFF_def] >>
     once_rw[one_to_one_id] >> rw[idR,idL] >>
     rw[GSYM Lt_def1] >> rw[Add_def])>>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘!p. P o p = TRUE’
 >-- fs[ALL_property] >>
 rw[IP_el] >> strip_tac >-- 
 (*  why arw makes no change? after rw[IP_el], if use 
 arw, no change, and if arw with Suc_def, no change, it use rw, mmakes change*) 
 arw[Add_O] >> 
 rw[Suc_def] >> rpt strip_tac >> rfs[]
 (*the thing that should be done by arw is done by 
  rfs*)
 >>fs[Add_Suc,Lt_mono_eq])
(form_goal
 “!m:1->N n p. Lt(m,n) <=> Lt(Add(m,p),Add(n,p))”));

val Suc_eq_eq = 
INV_SUC_EQ |> rewr_rule[Suc_def]
           |> store_as "Suc_eq_eq";

val EQ_MONO_ADD_EQ = prove_store("EQ_MONO_ADD_EQ",
e0
(strip_tac >> strip_tac >>
qby_tac
 ‘?P. !p.  
 P o p = TRUE <=> 
 Add(m,p) = Add(n,p) <=> m = n’
 >-- (
 qexists_tac ‘Iff(Eq(N) o 
                  Pa(Add(m o To1(N),id(N)),
                     Add(n o To1(N),id(N))),
                  Eq(N) o Pa(m,n) o To1(N))’
 >-- rw[GSYM Iff_def,Pa_distr,p12_of_Pa,o_assoc,
        IFF_def,GSYM Add_def] >>
     once_rw[one_to_one_id] >> rw[idR,idL] >>
     rw[Eq_property_TRUE,Add_def])>>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘!p. P o p = TRUE’
 >-- fs[ALL_property] >>
 rw[IP_el] >> strip_tac
 >-- arw[Add_O] >>
 rpt strip_tac >> rfs[] >>
 fs[Add_Suc,Suc_def,Suc_eq_eq])
(form_goal
 “!m:1->N n p. Add(m,p) = Add(n,p) <=> m = n”));

val LESS_MONO_ADD_EQ = GSYM LESS_MONO_ADD
                            |> store_as
                            "LESS_MONO_ADD_EQ";

val Sub_EQ_O = 
 SUB_equal_0 |> rewr_rule[Sub_def]
             |> store_as "Sub_EQ_O";

val LESS_OR_EQ = prove_store("LESS_OR_EQ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (drule Le_cases >> arw[]) 
 >-- fs[Lt_def] >>
 arw[Le_def,Sub_EQ_O] )
(form_goal
 “!m n:1->N. Le(m,n) <=> (Lt(m,n) | m = n)”));

val LESS_EQ_MONO_ADD_EQ = prove_store
("LESS_EQ_MONO_ADD_EQ",
e0
(rw[LESS_OR_EQ,LESS_MONO_ADD_EQ,EQ_MONO_ADD_EQ])
(form_goal
 “!m:1->N n p.Le(Add(m,p),Add(n,p)) <=> Le(m,n)”));
 
val lej_property = prove_store("lej_property",
e0
(rw[lej_def,o_assoc,Pa_distr,p12_of_Pa,Add_def])
(form_goal
 “!a b c d. lej o Pa(Pa(a,b),Pa(c,d)) = TRUE <=> 
 Le(Add(a,d),Add(b,c))”));

val Le_refl = LE_refl |> rewr_rule[GSYM Le_def1]
                      |> store_as "Le_refl";

val lej_refl = prove_store("lej_refl",
e0
(strip_tac >> rw[lej_def] >>
 qsspecl_then [‘p1(N,N) o ab’,‘p2(N,N) o ab’]
 assume_tac Add_sym >> arw[Add_def] >>
 rw[Le_refl])
(form_goal
 “!ab. lej o Pa(ab,ab) = TRUE”));

val Le_Add = prove_store("Le_Add",
e0
(rpt strip_tac >> irule Le_trans >>
 qexists_tac ‘Add(a,d)’ >> arw[LESS_EQ_MONO_ADD_EQ] >>
 qsspecl_then [‘a’,‘b’] assume_tac Add_sym >>
 arw[] >>
 qsspecl_then [‘a’,‘d’] assume_tac Add_sym >>
 arw[] >> arw[LESS_EQ_MONO_ADD_EQ])
(form_goal
 “!a:1->N b c d. Le(a,c) & Le(b,d) ==> Le(Add(a,b),Add(c,d))”));



val lej_trans = prove_store("lej_trans",
e0
(rw[lej_def] >> rpt strip_tac >>
 qsspecl_then  [‘a1’] assume_tac has_components >>
 qsspecl_then  [‘a2’] assume_tac has_components >>
 qsspecl_then  [‘a3’] assume_tac has_components >>
 fs[] >> fs[] >> fs[p12_of_Pa,Add_def] >> 
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
 qsspecl_then [‘a’,‘b''’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc] >> 
 qsspecl_then [‘Add(a',b')’,‘b''’] assume_tac Add_sym>>
 arw[] >> rw[GSYM Add_assoc] >>
 qsspecl_then [‘b'’,‘a’] assume_tac Add_sym >>
 once_arw[] >> rw[Add_assoc] >>
 qsspecl_then [‘b''’,‘a'’] assume_tac Add_sym >>
 once_arw[] >> rw[]) >>
 qsspecl_then [‘Add(b,a')’,‘Add(b',a'')’]
 assume_tac Add_sym >> arw[] >>
 qsspecl_then [‘b'’,‘a''’] assume_tac Add_sym >> arw[]>>
 qsspecl_then [‘b’,‘a''’] assume_tac Add_sym >> arw[]>>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(b', Add(b, a')) = Add(b, Add(a', b'))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘a'’,‘b'’] assume_tac Add_sym >>
 arw[] >>
 rw[Add_assoc] >> 
 qsspecl_then [‘b’,‘b'’] assume_tac Add_sym >> arw[])
(form_goal
 “!a1:1->N * N a2 a3. lej o Pa(a1,a2) = TRUE & lej o Pa(a2,a3) = TRUE ==> lej o Pa(a1,a3) = TRUE” ));


val J1_x = prove_store("J1_x",
e0
(rw[lej_def,Addj_property,p12_of_Pa] >>
 rw[Add_def] >> rpt strip_tac >>
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
      qsspecl_then [‘e’,‘d’] assume_tac Add_sym >> arw[]) >>
 rw[GSYM Add_assoc] >>
 qsuff_tac ‘Add(f, Add(c, e)) = Add(c, Add(e, f))’
 >-- (strip_tac >> arw[]) >>
 qsspecl_then [‘f’,‘Add(c,e)’] assume_tac Add_sym >> arw[] >>
 rw[Add_assoc] )
(form_goal
 “!a b c d e f. 
  lej o Pa(Pa(a,b),Pa(c,d)) = TRUE ==>
  lej o Pa(Addj(Pa(a,b),Pa(e,f)),
           Addj(Pa(c,d),Pa(e,f))) = TRUE”));



val J2_iv = prove_store("J2_iv",
e0
(once_rw[lej_def] >> once_rw[ZR_def] >>
 rw[Fst_Snd_Pa] >>
 rw[p12_of_Pa] >> once_rw[Add_def] >>
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
     >-- (qsspecl_then [‘Add(b',d')’,‘Add(a,d)’] 
          assume_tac $ GSYM Add_sym >> arw[] >>
          qsspecl_then [‘d'’,‘b'’] assume_tac $ GSYM Add_sym >> arw[] >>
          rw[Add_assoc] >>
          qsuff_tac ‘Add(Add(d', b'), a) = 
                     Add(Add(a', d'), b)’
          >-- (strip_tac >> arw[]) >>
          qsspecl_then [‘d'’,‘a'’] assume_tac $GSYM Add_sym >> arw[] >>
          rw[GSYM Add_assoc] >> 
          qsspecl_then [‘a’,‘b'’] assume_tac $GSYM Add_sym >> arw[] >>
          qsspecl_then [‘a'’,‘b’] assume_tac  Add_sym >> arw[]) >>
     qsspecl_then [‘Add(b',d')’,‘Add(b,c)’] assume_tac$GSYM Add_sym >>
     arw[] >> 
     qsspecl_then [‘c’,‘b’] assume_tac $GSYM Add_sym >> arw[] >>
     qsspecl_then [‘d’,‘b’] assume_tac $GSYM Add_sym >> arw[] >>
     rw[Add_assoc] >>
     qsuff_tac ‘Add(Add(b', d'), c) = Add(Add(b', c'), d)’ 
     >-- (strip_tac >> arw[]) >>
     rw[GSYM Add_assoc] >>
     qsspecl_then [‘c’,‘d'’] assume_tac $GSYM Add_sym >> arw[] >>
  qsspecl_then [‘c'’,‘d’] assume_tac $GSYM Add_sym >> arw[]) >>
 rw[LESS_EQ_MONO_ADD_EQ] 
 )
(form_goal “!a b c d a' b' c' d'. 
 ZR(Pa(a,b),Pa(a',b')) &
 ZR(Pa(c,d),Pa(c',d')) ==> 
(lej o Pa(Pa(a,b),Pa(c,d)) = TRUE <=>
lej o Pa(Pa(a',b'),Pa(c',d')) = TRUE)”));

val LEz_ex = prove_store("LEz_ex",
e0
(qexists_tac ‘lej o Pa(REP o p1(Z,Z),REP o p2(Z,Z))’ >>
 rw[o_assoc,Pa_distr,p12_of_Pa,rep_def])
(form_goal
 “?lez. !z1 z2. lez o Pa(z1,z2) = TRUE <=> 
 lej o Pa(rep(z1),rep(z2)) = TRUE”));

val LEz_def = LEz_ex |> ex2fsym0 "LEz" []
                     |> store_as "LEz_def";

val LEz_refl = prove_store("LEz_refl",
e0
(rw[LEz_def,lej_refl])
(form_goal
 “!z. LEz o Pa(z,z) = TRUE”));

val LEz_trans = prove_store("LEz_trans",
e0
(assume_tac lej_trans >>
 rw[LEz_def] >> rpt strip_tac >>
 qsspecl_then [‘rep(a1)’] assume_tac has_components >> 
 qsspecl_then [‘rep(a2)’] assume_tac has_components >>
 qsspecl_then [‘rep(a3)’] assume_tac has_components >>
 pop_assum_list (map_every strip_assume_tac) >>
 arw[] >> first_x_assum irule >> rfs[] >>
 qexists_tac ‘Pa(a',b')’ >> arw[])
(form_goal
 “!a1:1->Z a2 a3. LEz o Pa(a1,a2) = TRUE & LEz o Pa(a2,a3) = TRUE ==> 
 LEz o Pa(a1,a3) = TRUE”));

val Suc_NONZERO = prove_store("Suc_NONZERO",
e0
(rw[O_xor_SUC] >> 
 strip_tac >> qexists_tac ‘n’ >> rw[Suc_def])
(form_goal
 “!n. ~(Suc(n) =O)”));

val WOP' = prove_store("WOP'",
e0
(assume_tac WOP >>
 rw[Le_def1] >> rpt strip_tac >> first_x_assum irule >>
 ccontra_tac >>
 fs[False2FALSE,TRUE_ne_FALSE])
(form_goal
 “!P:N -> 1+1 a.
        P o a = TRUE ==>
        ?(l : ar(1, N)).
          P o l = TRUE &
          !n. P o n = TRUE ==> Le(l,n)”));

val Suc_NEQ = prove_store("Suc_NEQ",
e0
(qby_tac
 ‘?P. !a. P o a = TRUE <=> (a = Suc(a))’
 >-- (qexists_tac ‘Eq(N) o Pa(id(N),SUC)’ >>
      rw[o_assoc,Pa_distr,Eq_property_TRUE,
       idL,Suc_def]) >>
 pop_assum (strip_assume_tac o GSYM) >>
 strip_tac >> ccontra_tac >>
 rfs[] >> drule WOP' >>
 pop_assum strip_assume_tac >>
 cases_on “l = O” >--
 (last_x_assum (assume_tac o GSYM) >> fs[GSYM Suc_NONZERO]) >>
 fs[O_xor_SUC] >>
 last_x_assum (assume_tac o GSYM) >> fs[Suc_eq_eq,Suc_def] >>
 first_x_assum drule >> 
 drule $ iffRL Lt_Suc_Le >> fs[Lt_def])
(form_goal “!a:1->N. ~(a = Suc(a))”));

val Sub_Suc = SUB_SUC |> rewr_rule[Sub_def,Suc_def,Pre_def]
                      |> store_as "Sub_Suc";

val Pre_O = PRE_def |> conjE1 |> conjE1 |> rewr_rule[Pre_def]
                    |> store_as "Pre_O";

val Lt_Suc = prove_store("Lt_Suc",
e0
(rw[Lt_def,Le_def,Sub_Suc,Suc_NEQ,Sub_EQ_O,Pre_O])
(form_goal “!a:1->N. Lt(a,Suc(a))”));

val O_xor_Suc = O_xor_SUC |> rewr_rule[Suc_def]
                          |> store_as "O_xor_Suc";

val Add_Suc_Lt = prove_store("Add_Suc_Lt",
e0
(strip_tac >>
 qby_tac ‘?P. !b. Lt(a,Add(a,Suc(b))) <=> P o b = TRUE’
 >-- (qexists_tac 
      ‘Char(LT) o Pa(a o To1(N), ADD o Pa(a o To1(N),SUC))’ >>
      rw[GSYM Lt_def1,o_assoc,Pa_distr,Suc_def] >>
      once_rw[one_to_one_id] >> rw[idR,Add_def]) >>
 pop_assum strip_assume_tac >> arw[] >>
 rw[IP_el] >> pop_assum (assume_tac o GSYM) >> arw[] >> strip_tac>--
(rw[Lt_def,Le_def,Add_Suc,Add_O,Sub_Suc,Pre_O,O_xor_Suc,
        Suc_NEQ,Pre_O,Sub_EQ_O]) >>
 rpt strip_tac >> rw[Add_Suc] >> rw[Lt_Suc_Le] >>
 rw[GSYM Add_Suc] >> fs[Lt_def,Suc_def]
 )
(form_goal
 “!a:1->N b. Lt(a,Add(a,Suc(b)))”));


val Lt_trans = prove_store("Lt_trans",
e0
(rw[Lt_def] >>
 assume_tac Le_trans >> rpt strip_tac >--
 (first_x_assum irule >> qexists_tac ‘a2’ >> arw[]) >>
 qby_tac ‘(?p1. Add(a1,Suc(p1)) = a2) & 
          ?p2. Add(a2,Suc(p2)) = a3’ >-- 
 (drule Le_Add_ex >> rev_drule Le_Add_ex >> fs[] >>
 qby_tac ‘~(p = O)’
 >-- (ccontra_tac >> fs[Add_O2]) >>
 qby_tac ‘~(p' = O)’
 >-- ccontra_tac >> fs[Add_O2] >>
 fs[O_xor_Suc] >> strip_tac 
 >-- (qexists_tac ‘n0'’ >> arw[] >> once_rw[Add_sym] >> fs[]) >>
 (qexists_tac ‘n0’ >> arw[] >> once_rw[Add_sym] >> fs[])) >>
 cheat >>
 pop_assum (strip_assume_tac o GSYM) >>
 fs[] >> rw[GSYM Add_assoc] >> once_rw[Add_Suc] >>
 assume_tac Add_Suc_Lt >> fs[Lt_def])
(form_goal “!a1:1->N a2 a3. Lt(a1,a2) & Lt(a2,a3) ==> Lt(a1,a3)”));


(*TODO: delete LE_cases_iff*)

val Le_asym = prove_store("Le_asym",
e0
(rpt strip_tac >> drule Le_cases >> pop_assum strip_assume_tac >>
 arw[] >> rev_drule Le_cases >> pop_assum strip_assume_tac >> arw[] >>
 qby_tac ‘Lt(a,a)’ 
 >-- (irule Lt_trans >> qexists_tac ‘b’ >> arw[]) >>
 fs[Lt_def])
(form_goal
 “!a:1->N b. Le(a,b) & Le(b,a) ==> a = b”));

val LEz_asym = prove_store("LEz_asym",
e0
(rw[LEz_def] >> strip_tac >> strip_tac >>
 qsspecl_then [‘rep(a)’] assume_tac has_components >> 
 qsspecl_then [‘rep(b)’] assume_tac has_components >>
 pop_assum_list (map_every strip_assume_tac) >> arw[] >>
 rw[lej_def] >> rw[p12_of_Pa,Add_def] >> strip_tac >>
 once_rw[z_eq_cond] >>
 qexistsl_tac [‘Pa(a'',b'')’,‘Pa(a',b')’] >>
 rw[ZR_def] >> rw[Fst_Snd_Pa] >> rpt strip_tac (* 3 *)
 >-- (pop_assum_list (map_every (assume_tac o GSYM)) >>
      arw[rep_asz])
 >-- (pop_assum_list (map_every (assume_tac o GSYM)) >>
      arw[rep_asz]) >>
 irule Le_asym  >> 
 qsspecl_then [‘a''’,‘b'’] assume_tac $GSYM Add_sym >>fs[] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac $GSYM Add_sym >> fs[])
(form_goal
 “!a b. LEz o Pa(a,b) = TRUE & LEz o Pa(b,a) = TRUE ==> a = b”));



val LEz_total = prove_store("LEz_total",
e0
(rw[LEz_def,lej_def] >> rpt strip_tac >>
 qsspecl_then [‘rep(a)’] assume_tac has_components >> 
 qsspecl_then [‘rep(b)’] assume_tac has_components >>
 pop_assum_list (map_every strip_assume_tac) >> 
 arw[p12_of_Pa] >>
 qsspecl_then [‘a'’,‘b''’] assume_tac $GSYM Add_sym >> arw[] >>
 qsspecl_then [‘a''’,‘b'’] assume_tac $GSYM Add_sym >> arw[] >>
 arw[Add_def] >> rw[Le_def1] >>
 rw[LESS_EQ_cases] )
(form_goal “!a:1->Z b. LEz o Pa(a,b) = TRUE | LEz o Pa(b,a) = TRUE”));


val Z = mk_fun "Z" []

val _ = new_pred "Lez" [("z1",ar_sort (mk_ob "X") Z),
                        ("z2",ar_sort (mk_ob "X") Z)]

val Lez_def0 = store_ax("Lez_def0",
“!X z1:X->Z z2.Lez(z1,z2) <=> LEz o Pa(z1,z2) = True(X)”);

val Lez_def = Lez_def0 |> allE (rastt "1")
                       |> rewr_rule[True1TRUE]
                       |> store_as "Lez_def";


val J2_iv' = prove_store("J2_iv'",
e0
(rpt strip_tac >> 
 qsspecl_then [‘ab’] assume_tac has_components >>
 qsspecl_then [‘ab'’] assume_tac has_components >>
 qsspecl_then [‘cd’] assume_tac has_components >>
 qsspecl_then [‘cd'’] assume_tac has_components >>
 pop_assum_list (map_every strip_assume_tac) >> rfs[] >>
 irule J2_iv >> arw[])  
(form_goal
 “!ab cd ab' cd'. ZR(ab,ab') & ZR(cd,cd') ==> 
 (lej o Pa(ab,cd) = TRUE <=> lej o Pa(ab',cd') = TRUE)”));





val Z2_x = prove_store("Z2_x",
e0
(rw[Lez_def,Addz_eqn',Addj_property,LEz_def] >>
 rpt strip_tac >>
 qsuff_tac 
 ‘lej o Pa(Pa(a, b),Pa(c, d)) = TRUE ==> 
  lej o Pa (Pa(Add(a, e), Add(b, f)),
            Pa(Add(c, e), Add(d, f))) = TRUE’ >--
 (rpt strip_tac >>
 qby_tac ‘lej o Pa(Pa(a, b), Pa(c, d)) = TRUE’
 >-- (irule $ iffLR J2_iv' >>
      qexistsl_tac 
      [‘rep(asz(Pa(a, b)))’,‘rep(asz(Pa(c, d)))’]>>
      arw[] >> rw[GSYM rep_rel_all]) >>
 first_x_assum drule >> 
 irule $ iffLR J2_iv' >>
 qexistsl_tac
 [‘Pa(Add(a, e), Add(b, f))’,‘Pa(Add(c, e), Add(d, f))’] >>
 arw[] >> once_rw[ZR_sym] >> rw[GSYM rep_rel_all]) >>
 pop_assum (K all_tac) >>
 rw[lej_property] >> rpt strip_tac >>
 qsspecl_then [‘Add(d,f)’,‘Add(a,e)’] assume_tac $ GSYM Add_sym >>
 arw[] >> rw[Add_assoc] >> rw[LESS_EQ_MONO_ADD_EQ] >>
 once_rw[Add_sym] >> rw[Add_assoc] >>
 rw[LESS_EQ_MONO_ADD_EQ] >> 
 qsspecl_then [‘c’,‘b’] assume_tac$ GSYM Add_sym >> fs[]
 )
(form_goal “!a:1->N b c d e f.Lez(asz(Pa(a,b)),asz(Pa(c,d))) ==>
            Lez(Addz(asz(Pa(a,b)),asz(Pa(e,f))),
                Addz(asz(Pa(c,d)),asz(Pa(e,f))))”));


(*
val lej_ex = prove_store("lej_ex",
e0
()
(form_goal
 “?lej. !a:1-> N b c d. 
  lej o Pa(Pa(a,b),Pa(c,d)) = TRUE <=> 
  Le(Add(a,d),Add(b,c))”));
*)


(*
rastt "Ev(X,2) o (f :1-> X * Pow(X))"



should be same 
rastt "Ev(X,2) o f: 1-> X * Exp(X,2)"

otherwise cannot unify 

so the subst from Pow(X) into Exp(X,2) must be done before unification

two dictionaries 

Exp(X,2) <> Pow(X)

("Pow",([("X",ob)],Exp(X,2) as a ast))


then use an inst_ast version of inst_term 

*)

(*

fun subst_ast a1 a2 ast = 
case ast of 
    aId(a) => if aId(a) = a1 then a2 else ast
   | aApp(str,astl) => 
     if ast = a1 then a2 else
     aApp(str,List.map (subst_ast a1 a2) astl)
   | aInfix(ast1,str,ast2) =>
    aInfix(subst_ast a1 a2 ast1,str,subst_ast a1 a2 ast2)
   | aBinder(str,ns,b) =>
     aBinder(str,subst_ast a1 a2 ns,subst_ast a1 a2 b)


val abbrevs0 = [("Exp",["X",ob_sort])]

*)


(*cannot be like fsyms psyms dict, should it be a dictionary at all?

thought about using something like ("Exp",([old arguments],[new_arguments]), and strings as key, but then the pp need another dictionary, seems weird.)
*)


(*fun subst_abbr ast = 

the obvious thing is to write a code that search if there is any occurrence of each abbreved term and replace them.

but then need to look through the dictionary and find out each occurence of any abbreved term.

Any better way to write this?


*)





