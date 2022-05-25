
(*member to relation*)
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


val isleast_def = qdefine_psym("isleast",[‘R:A~>A’,‘s:mem(Pow(A))’,‘l:mem(A)’])
‘IN(l,s) & !a. IN(a,s) ==> Holds(R,l,a)’

val Well_def = qdefine_psym("Well",[‘R:A~>A’])
‘Total(R) & 
 !s. ~(s = Empty(A)) ==> ?l. isleast(R,s,l)’ 
|> gen_all

val INr_def = qdefine_psym("INr",[‘a:mem(A)’,‘R:A~>A’])
‘?a1. Holds(R,a,a1) | Holds(R,a1,a)’

(*why choose to define snocrel like this instead of using 
A + 1, A + 1 + 1,... etc, 
then do not need to inject into A, easier to take bigunion,

and easier to say for every well order, for every base, instead of of certain form.


Initially it was:
“!A R:A~>A a.~INr(a,R) ==>
 ?!Ra. !a1 a2. Holds(Ra,a1,a2) <=> 
 Holds(R,a1,a2) | (INr(a1,R) & a2 = a)”

but thhen realise do not need the precond to define the rel
*)
val snocrel_def = 
AX1 |> qspecl [‘A’,‘A’] 
    |> fVar_sInst_th “P(a1:mem(A),a2:mem(A))”
    “ Holds(R:A~>A,a1,a2) | (INr(a1,R) & a2 = a)”
    |> uex2ex_rule |> qSKOLEM "snocrel" [‘R’,‘a’]
    |> qspecl [‘a1:mem(A)’,‘a2:mem(A)’]
    |> gen_all

(*member of power set to set,
to prove uniqueness !!!!!*)
val m2s_def = proved_th $
e0
(cheat)
(form_goal “!X xs:mem(Pow(X)). ?X0 i:X0->X. 
 Inj(i) & 
 !x. IN(x,xs) <=> ?x0:mem(X0). x = App(i,x0)”)
|> spec_all |> qSKOLEM "m2s" [‘xs’] 
|> qSKOLEM "m2i" [‘xs’] |> gen_all

(*inductive relaion need b is a member of some set B.
  can prove each finite beth exist,
 then the 
*)

val snocm_def = qdefine_fsym("snocm",[‘r:mem(Pow(A * A))’,‘a:mem(A)’]) ‘r2m(snocrel(m2r(r),a))’ 
 
val ischain_def = 
    qdefine_psym("ischain",
                 [‘r:A~>A’,‘s:mem(Pow(A))’])
    ‘!a1 a2. IN(a1,s) & IN(a2,s) ==> 
     Holds(r,a1,a2) | Holds(r,a2,a1)’
                           |> gen_all
 
val SSr_def =  
    AX1 |> qspecl [‘Pow(A)’,‘Pow(A)’]
        |> fVar_sInst_th “P(s1:mem(Pow(A)),s2:mem(Pow(A)))”
           “SS(s1:mem(Pow(A)),s2)”
        |> uex2ex_rule |> qSKOLEM "SSr" [‘A’] 

val SSchain_def = qdefine_psym("SSchain",
[‘s:mem(Pow(Pow(A)))’]) ‘ischain(SSr(A),s)’
|> gen_all

local
val iswo_cl = 
 “(od = Empty(A * A) ==> IN(od,wo)) &
  (!od0 a.
      IN(od0,wo) & ~INr(a,m2r(od0)) & od = snocm(od0,a) 
      ==> IN(od,wo)) &
  (!s. (!od0. IN(od0,s) ==> IN(od0,wo)) & 
       SSchain(s) &
       od = BIGUNION(s) ==>
   IN(od,wo)) ”
in
val (iswo_incond,x1) = mk_incond iswo_cl;
val iswof_ex = mk_fex iswo_incond x1;
val iswof_def = mk_fdef "iswof" iswof_ex;
val iswof_monotone = proved_th $
e0
(cheat)
(form_goal 
“!s1 s2.SS(s1,s2) ==> 
  SS(App(iswof(A), s1), App(iswof(A), s2))”)
val iswo's_def = mk_prim iswof_def;
val iswos_def = mk_LFP (rastt "iswo's(A)");
val iswos_cond = mk_cond iswos_def iswo's_def;
val iswos_SS = mk_SS iswos_def iswo's_def;
val iswo_rules0 = mk_rules iswof_monotone iswos_SS iswos_cond;
val iswo_cases0 = mk_cases iswof_monotone iswo_rules0 iswos_cond;
val iswo_ind0 = mk_ind iswos_cond;
val iswo_ind1 = mk_ind1 iswof_def iswo_ind0;
val iswo_ind2 = mk_ind2 iswo_ind1;
val iswo_cases1 = mk_case1 iswof_def iswo_cases0;
val iswo_rules1 = mk_rules1 iswof_def iswo_rules0;
val iswo_rules2 = mk_rules2 iswo_rules1;
val iswo_rules3 = mk_rules3 iswo_rules2;
end
 
val iswo_ind = iswo_ind2 |> store_as "iswo_ind";
val iswo_cases = iswo_cases1 |> store_as "iswo_cases";
val iswo_rules = iswo_rules3 |> store_as "iswo_rules";

val WO_def = Thm_2_4 |> qspecl [‘Pow(A * A)’] 
                    |> fVar_sInst_th 
                       “P(od:mem(Pow(A * A)))” 
                       “IN(od:mem(Pow(A * A)),iswos(A))”
                    |> qSKOLEM "WO" [‘A’] 
                    |> qSKOLEM "iWO" [‘A’]
                    |> gen_all


(*if as constructors, will have 
O | Suc ord | U (ord set)
!!!!!!!!! *)
val Rwo_def = qdefine_fsym("Rwo",[‘wo:mem(WO(A))’])
‘App(iWO(A),wo)’ |> gen_all


val Rwo_iswos = prove_store("Rwo_iswos",
e0
(rpt strip_tac >> 
 assume_tac
 (WO_def|> spec_all 
                      |> conjE2 
                      |> qspecl [‘Rwo(wo:mem(WO(A)))’]
                      |> rewr_rule[GSYM Rwo_def]) >>
 arw[] >> qexists_tac ‘wo’ >> rw[])
(form_goal “!A wo. IN(Rwo(wo), iswos(A))”));



val zord_def = proved_th $
e0
(rpt strip_tac >> rw[Rwo_def] >>
 irule $ iffRL Inj_ex_uex >>
 rw[WO_def] >> flip_tac >> rw[GSYM WO_def] >>
 rw[iswo_rules])
(form_goal “!A. ?!zo. Rwo(zo) = Empty(A * A)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "zord" [‘A’]
|> gen_all

val wo_ex = proved_th $
e0
(strip_tac >> qexists_tac ‘zord(A)’ >> rw[])
(form_goal “!A. ?wo:mem(WO(A)).T”)


val sord_def = proved_th $
e0
(rpt strip_tac >> rw[Rwo_def] >>
 irule $ iffRL Inj_ex_uex >> rw[WO_def,GSYM Rwo_def] >>
 flip_tac >> rw[from_WO] >>
 irule iswo_snocm >> arw[Rwo_iswos])
(form_goal 
 “!A wo a:mem(A). ~INr(a,m2r(Rwo(wo))) ==>
  ?!wo1.Rwo(wo1) = snocm(Rwo(wo),a)”)
|> spec_all |> undisch |> uex2ex_rule 
|> SKOLEM (spec_all wo_ex) "sord" 
[("wo",mem_sort (rastt "WO(A)")),
 ("a",mem_sort (rastt "A"))]
|> disch_all |> gen_all


(*add the condition of being an infinite chain?*)
val lord_def = proved_th $
e0
(rpt strip_tac >> rw[Rwo_def] >>
 irule $ iffRL Inj_ex_uex >> rw[WO_def,GSYM Rwo_def] >>
 flip_tac >> rw[from_WO] >>
 irule iswo_BIGUNION >> arw[] >> rpt strip_tac >>
 fs[IMAGE_def,GSYM Rwo_def,Rwo_iswos])
(form_goal 
 “!A s. SSchain(IMAGE(iWO(A),s)) ==>
  ?!lo.Rwo(lo) = BIGUNION(IMAGE(iWO(A),s))”)
|> spec_all |> undisch |> uex2ex_rule 
|> SKOLEM (spec_all wo_ex) "lord" 
[("s",mem_sort (rastt "Pow(WO(A))"))]
|> disch_all |> gen_all

val Leo_def = qdefine_psym("Leo",[‘wo1:mem(WO(A))’,‘wo2:mem(WO(A))’]) ‘SS(Rwo(wo1),Rwo(wo2))’ |> gen_all

val LEo_def = 
    AX1 |> qspecl [‘WO(A)’,‘WO(A)’] 
        |> fVar_sInst_th “P(a:mem(WO(A)),b:mem(WO(A)))”
           “Leo(a:mem(WO(A)),b)”
        |> uex2ex_rule |> qSKOLEM "LEo" [‘A’]
        |> store_as "LEo_def";

val all_P_WO = prove_store("all_P_WO",
e0
(dimp_tac >> rpt strip_tac >> arw[] >>
 first_x_assum (qspecl_then [‘Rwo(wo)’] assume_tac) >>
 fs[Rwo_iswos] >>
 first_x_assum irule >> rw[])
(form_goal
 “(!wo:mem(WO(A)).P(wo)) <=> 
  (!od:mem(Pow(A * A)). IN(od,iswos(A)) ==>
    IN(od,iswos(A)) & 
    (!wo.Rwo(wo) = od ==> P(wo)))”));


fun mk_induct ind = 
    let val (svar as (n,s),b) = dest_forall (concl ind) 
        val st = mk_var svar
        val pset = s |> dest_sort |> #2 |> hd
                     |> dest_fun |> #3 |> hd
        val specindefp = IN_def_P_ex |> allE pset
        val (exv,exb) = dest_exists (concl specindefp)
        val specind = ind |> allE (mk_var exv)
        val ind' = rewr_rule[GSYM(assume exb)] 
                            (add_assum exb specind) 
    in existsE exv specindefp ind'
    end

val iswo_induct = mk_induct iswo_ind

val Rwo_Empty_iff_zord = prove_store("Rwo_Empty_iff_zord",
e0
(rw[GSYM zord_def,Rwo_def] >>
 rpt strip_tac >> irule Inj_eq_eq >>
 rw[WO_def])
(form_goal “!A wo.Rwo(wo) = Empty(A * A) <=> 
 wo = zord(A)”));

val iswo_snocm = iswo_rules |> conjE2 
                            |> conjE1 


val iswo_BIGUNION = iswo_rules |> conjE2 
                               |> conjE2

val iswo_Rwo = WO_def |> spec_all |> conjE2
                      |> rewr_rule[GSYM Rwo_def]
                      |> store_as "iswo_Rwo";

val Rwo_eq_eq = prove_store("Rwo_eq_eq",
e0
(rpt strip_tac >> rw[Rwo_def] >> irule Inj_eq_eq >>
 rw[WO_def])
(form_goal “!A wo1 wo2:mem(WO(A)).Rwo(wo1) = Rwo(wo2) <=>
 wo1 = wo2”));

val Rwo_snocm_iff_sord = prove_store("Rwo_snocm_iff_sord",
e0
(rpt strip_tac >> flip_tac >>
 drule $ GSYM sord_def >> arw[Rwo_eq_eq])
(form_goal “!A wo0 wo a:mem(A).~INr(a, m2r(Rwo(wo0))) ==>
 (Rwo(wo) = snocm(Rwo(wo0),a) <=> 
 wo = sord(wo0,a))”));

(*
val all_wo_IMAGE = prove_store("all_wo_IMAGE",
e0
()
(form_goal “SSchain(s) & Rwo(wo) = BIGUNION(s) <=> 
 wo = lord(PREIM())”));
*)

val pres_refl_chain = prove_store("preserve_chain",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[ischain_def] >> rpt strip_tac >>
     first_x_assum (qspecl_then [‘App(f,a1)’,‘App(f,a2)’] 
                                assume_tac) >>
     drule App_IN_IMAGE >>
     rev_drule App_IN_IMAGE >>
     fs[]) >>
 fs[ischain_def] >> rpt strip_tac >> fs[IMAGE_def] >>
 first_x_assum (qspecl_then [‘a’,‘a'’] assume_tac) >>
 rfs[])
(form_goal “!A r1:A~>A B r2:B~>B f:A->B.
 (!a1 a2.Holds(r1,a1,a2) <=> Holds(r2,App(f,a1),App(f,a2)))
  ==>
 !ac. ischain(r2,IMAGE(f,ac)) <=> ischain(r1,ac) 
 ”));


val iWO_pres_refl_chain = prove_store("iWO_pres_refl_chain",
e0
(rw[LEo_def,Leo_def,SSr_def])
(form_goal 
“!od1 od2.Holds(LEo(A),od1,od2) <=> 
          Holds(SSr(A * A),Rwo(od1),Rwo(od2))”));

val SSchain_iWO_chain_LEo = prove_store("SSchain_iWO_chain_LEo",
e0
(rpt strip_tac >> rw[SSchain_def] >>
 irule pres_refl_chain >> 
 rw[GSYM Rwo_def,iWO_pres_refl_chain])
(form_goal
 “!A wos. SSchain(IMAGE(iWO(A),wos)) <=>
  ischain(LEo(A),wos)”));



val from_WO = WO_def |> spec_all |> conjE2 
                     |> GSYM 
                     |> rewr_rule[GSYM Rwo_def]
                     |> gen_all

val wo_induct = prove_store("wo_induct",
e0
(strip_tac >> disch_tac >>
 match_mp_tac $ iffRL all_P_WO >>
 ind_with iswo_induct >>
 rw[iswo_rules,Rwo_Empty_iff_zord] >> 
 strip_tac (* 2 *)
 >-- (strip_tac (* 2 *)
     >-- (rpt strip_tac >> arw[]) >>
     rpt gen_tac >> strip_tac >>
     qby_tac ‘IN(snocm(od0, a'), iswos(A))’ 
     >-- (irule iswo_snocm >> arw[]) >> arw[] >>
     rpt strip_tac >> fs[iswo_Rwo] >> 
     qby_tac ‘P(b)’ 
     >-- (first_x_assum irule >> arw[]) >>
     qsuff_tac ‘wo = sord(b,a')’
     >-- (strip_tac >> arw[] >>
         last_x_assum irule >> arw[]) >> rfs[] >>
     drule $ GSYM Rwo_snocm_iff_sord >> arw[]) >>
 strip_tac >> strip_tac >> 
 qby_tac
 ‘IN(BIGUNION(s'), iswos(A))’
 >-- (irule iswo_BIGUNION >> arw[] >>
     rpt strip_tac >> 
     first_x_assum drule >> arw[]) >> arw[] >>
 rpt strip_tac >>
 qsuff_tac 
 ‘?ods. wo = lord(ods) &
        ischain(LEo(A),ods) &
        IMAGE(iWO(A),ods) = s'’
 >-- (rpt strip_tac >> arw[] >>
     last_x_assum strip_assume_tac >>
     first_x_assum irule >> arw[] >>
     rpt strip_tac >>
     qsuff_tac ‘?od0. IN(od0,s') & Rwo(od) = od0’ 
     >-- (strip_tac >> 
          last_x_assum drule >> 
          pop_assum strip_assume_tac >>
          first_x_assum irule >>
          arw[]) >>
     qpick_x_assum ‘IMAGE(iWO(A), ods) = s'’ 
     mp_tac >> rw[GSYM IN_EXT_iff,IMAGE_def] >>
     strip_tac >> rw[IN_EXT_iff] >>
     fs[GSYM Rwo_def,IN_EXT_iff] >>
     qby_tac ‘?a. IN(a,ods) & Rwo(od) = Rwo(a)’ 
     >-- (qexists_tac ‘od’ >> arw[]) >>
     first_x_assum (drule o iffLR) >>
     qexists_tac ‘Rwo(od)’ >> arw[]) >> 
 qsuff_tac ‘?ods.IMAGE(iWO(A),ods) = s'’ 
 >-- (strip_tac >> qexists_tac ‘ods’ >> arw[] >>
     rw[GSYM SSchain_iWO_chain_LEo] >> arw[] >>
     irule $ iffLR Inj_eq_eq >>
     qexistsl_tac [‘Pow(A*A)’,‘iWO(A)’] >>
     rw[GSYM Rwo_def,WO_def] >>
     flip_tac >> arw[] >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     irule lord_def >> fs[]) >> 
 flip_tac >>
 irule ex_eq_IMAGE >> rw[GSYM Rwo_def] >>
 rpt strip_tac >>
 first_x_assum drule >>
 arw[from_WO])
(form_goal 
 “!A. P(zord(A)) &
      (!od a:mem(A). P(od) ==> P(sord(od,a))) &
      (!ods. ischain(LEo(A),ods) &
             (!od.IN(od,ods) ==> P(od))
             ==> P(lord(ods))) ==>
      !wo:mem(WO(A)).P(wo)”));

val msEqv_def = qdefine_psym("msEqv",[‘s:mem(Pow(A))’,‘S’])
‘Eqv(m2s(s),S)’ |> gen_all



local
val beth0_cl = 
 “(!s. msEqv(s,N) & p = Pair(zord(A),s) ==>
      IN(p,beths)) & 
  (!p0 wo0 b0 s a. 
            IN(p0,beths) & 
            p0 = Pair(wo0,b0) & 
            msEqv(s,Pow(m2s(b0))) &
          p = Pair(sord(wo0,a),s) ==>
          IN(p,beths)) &
  (!ps. (!p.IN(p,ps) ==> IN(p,beths)) &
        SSchain(IMAGE(iWO(A) o p1(WO(A),Pow(B)),ps)) &
        p = Pair(lord(IMAGE(p1(WO(A),Pow(B)),ps)),
                 BIGUNION(IMAGE(p2(WO(A),Pow(B)),ps))) ==>
   IN(p,beths))”
in
val (beth0_incond,x1) = mk_incond beth0_cl;
val beth0f_ex = mk_fex beth0_incond x1;
val beth0f_def = mk_fdef "beth0f" beth0f_ex;
val beth0f_monotone = proved_th $
e0
(cheat)
(form_goal 
“!s1 s2.SS(s1,s2) ==> 
  SS(App(beth0f(A,B), s1), App(beth0f(A,B), s2))”)
val beth0's_def = mk_prim beth0f_def;
val beth0s_def = mk_LFP (rastt "beth0's(A,B)");
val beth0s_cond = mk_cond beth0s_def beth0's_def;
val beth0s_SS = mk_SS beth0s_def beth0's_def;
val beth0_rules0 = mk_rules beth0f_monotone beth0s_SS beth0s_cond;
val beth0_cases0 = mk_cases beth0f_monotone beth0_rules0 beth0s_cond;
val beth0_ind0 = mk_ind beth0s_cond;
val beth0_ind1 = mk_ind1 beth0f_def beth0_ind0;
val beth0_ind2 = mk_ind2 beth0_ind1;
val beth0_cases1 = mk_case1 beth0f_def beth0_cases0;
val beth0_rules1 = mk_rules1 beth0f_def beth0_rules0;
val beth0_rules2 = mk_rules2 beth0_rules1;
val beth0_rules3 = mk_rules3 beth0_rules2;
end
 

val beth0_ind = beth0_ind2 |> store_as "beth0_ind";
val beth0_cases = beth0_cases1 |> store_as "beth0_cases";
val beth0_rules = beth0_rules3 |> store_as "beth0_rules";

val beth0_induct = mk_induct beth0_ind 

val isbeth_def = qdefine_psym("isbeth",[‘wo:mem(WO(A))’,‘beth:mem(Pow(B))’]) ‘IN(Pair(wo,beth),beth0s(A,B))’
|> gen_all


val isbeth_ind0 =  beth0_induct
                     |> conv_rule (redepth_fconv no_conv forall_cross_fconv) |> rewr_rule[GSYM isbeth_def,Pair_eq_eq]

val isbeth_induct = prove_store("isbeth_induct",
e0
(disch_tac >>
 match_mp_tac isbeth_ind0 >>
 arw[] >>
 pop_assum strip_assume_tac >>
 rpt strip_tac >> arw[] >>
 first_x_assum irule >> qexists_tac ‘b0’ >> arw[])
(form_goal
 “(!s:mem(Pow(B)).msEqv(s,N) ==> P(Pair(zord(A),s))) & 
  (!wo0 b0:mem(Pow(B)) s:mem(Pow(B)). 
   P(Pair(wo0, b0)) & msEqv(s, Pow(m2s(b0))) ==>
   !a:mem(A).P(Pair(sord(wo0,a),s))) & 
  (!ps : mem(Pow(WO(A) * Pow(B))).
    (!a b. IN(Pair(a, b), ps) ==> P(Pair(a, b))) &
    SSchain(IMAGE(iWO(A) o p1(WO(A), Pow(B)), ps)) ==>
    P(Pair(lord(IMAGE(p1(WO(A), Pow(B)), ps)),
           BIGUNION(IMAGE(p2(WO(A), Pow(B)), ps))))) ==>
      !wo:mem(WO(A)) beth:mem(Pow(B)).
        isbeth(wo, beth) ==> P(Pair(wo, beth))”));

(*
val beth0_cases = beth0_cases1 |> store_as "beth0_cases";
val beth0_rules = beth0_rules3 |> store_as "beth0_rules";

val beth0_induct = mk_induct beth0_ind
*)


val isBeth_def = qdefine_psym("isBeth",[‘wo:mem(WO(A))’,‘s’]) ‘?B beth:mem(Pow(B)). isbeth(wo,beth) & msEqv(beth,s)’
|> gen_all

val msEqv_Whole = prove_store("msEqv_Whole",
e0
(cheat)
(form_goal “!A. msEqv(Whole(A), A) ”));

 
val msEqv_m2s = prove_store("msEqv_m2s",
e0
(cheat)
(form_goal “!A s. msEqv(s:mem(Pow(A)), m2s(s)) ”));


val Eqv_m2s = prove_store("Eqv_m2s",
e0
cheat
(form_goal “!A.Eqv(m2s(Whole(A)), A)”));

val isbeth_zord = beth0_rules |> conjE1 
                              |> rewr_rule[GSYM isbeth_def]
                              |> gen_all

val isbeth_sord = 
beth0_rules |> conjE2 |> conjE1
             |> qspecl [‘Pair(sord(wo0, a0:mem(A)),
                              b1:mem(Pow(B)))’,
                        ‘wo0:mem(WO(A))’,‘b0:mem(Pow(B))’,
                        ‘b1:mem(Pow(B))’,‘a0:mem(A)’]
             |> rewr_rule[] 
             |> strip_all_and_imp
             |> gen_all 
             |> disch “msEqv(b1:mem(Pow(B)), Pow(m2s(b0:mem(Pow(B)))))”
             |> gen_all
             |> disch_all |> gen_all
             |> rewr_rule[GSYM isbeth_def]

val isbeth_lord = beth0_rules |> conjE2 |> conjE2 
|> conv_rule (redepth_fconv no_conv forall_cross_fconv)
                              |> rewr_rule[GSYM isbeth_def]
|> gen_all
  
(*

!(s : mem(Pow(B))).
               Eqv(m2s(s#), Pow(m2s(Snd(Pair(od, beth))))) ==>
               !(a' : mem(A)). IN(Pair(sord(od, a'#), s#), isbeths(A, B))

*)

(*if A can be injected into B , then Pow(A) can be injected into Pow(B)?*)

val Inj_IMAGE_msEqv = prove_store("Inj_IMAGE_msEqv",
e0
(cheat)
(form_goal
 “!A s:mem(Pow(A)) B.msEqv(s,B) ==>
  !C f:A->C. Inj(f) ==> msEqv(IMAGE(f,s),B) ”));

val Eqv_msEqv= prove_store("Eqv_msEqv",
e0
(cheat)
(form_goal “!S1 S2.
  Eqv(S1,S2) ==> 
  (!A s:mem(Pow(A)).msEqv(s,S1) <=> msEqv(s,S2))”));

val Eqv_SYM = prove_store("Eqv_SYM",
e0
cheat
(form_goal “!A B. Eqv(A,B) ==> Eqv(B,A)”))


val Eqv_REFL = prove_store("Eqv_REFL",
e0
cheat
(form_goal “!A. Eqv(A,A)”))


val Eqv_TRANS = prove_store("Eqv_TRANS",
e0
cheat
(form_goal “!A B. Eqv(A,B) ==>
 !C. Eqv(B,C) ==> Eqv(A,C)”))


val Inj_m2s_Eqv = prove_store("Inj_m2s_Eqv",
e0
(cheat)
(form_goal “!A B f:A->B. Inj(f) ==>
 !s. Eqv(m2s(s),m2s(IMAGE(f,s)))”));

val Eqv_Pow = prove_store("Eqv_Pow",
e0
(cheat)
(form_goal
 “!A B. Eqv(A,B) ==> Eqv(Pow(A),Pow(B))”));

local
val l = 
isbeth_induct |> fVar_sInst_th “P(pair:mem(WO(A) * Pow(B)))”
 “!C f:B->C. Inj(f) ==> isbeth(Fst(pair:mem(WO(A) * Pow(B))),IMAGE(f,Snd(pair)))”
             |> rewr_rule[Pair_def'] 
in
val Inj_IMAGE_beth = prove_store("Inj_IMAGE_beth",
e0
(strip_tac >> strip_tac >>
 match_mp_tac l >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> irule isbeth_zord >>
     irule Inj_IMAGE_msEqv >> arw[]) >>
 strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     irule isbeth_sord >>
     first_x_assum drule >>
     qexists_tac ‘IMAGE(f,b0)’ >> arw[] >>
     irule $ iffLR Eqv_msEqv >>
     fs[msEqv_def] >> 
     drule Inj_m2s_Eqv >>
     first_x_assum (qspecl_then [‘s’] assume_tac) >>
     qexists_tac ‘m2s(s)’ >> 
     drule Eqv_SYM >> arw[] >>
     qsuff_tac ‘Eqv(Pow(m2s(b0)),Pow(m2s(IMAGE(f, b0))))’ 
     >-- (strip_tac >> rev_drule Eqv_TRANS >>
         first_x_assum drule >> arw[]) >>
     irule Eqv_Pow >> irule Inj_m2s_Eqv >> arw[]) >>
 rpt strip_tac >>
 rw[IMAGE_BIGUNION,GSYM IMAGE_o,p2_comm] >>
 rw[IMAGE_o] >> 
 qby_tac
 ‘IMAGE(p1(WO(A), Pow(B)), ps) = 
  IMAGE(p1(WO(A), Pow(C)),
   IMAGE(Prla(Id(WO(A)), Image(f)), ps))’
 >-- cheat >> arw[] >>
 irule isbeth_lord >> 
 qby_tac
 ‘SSchain(IMAGE(iWO(A) o p1(WO(A), Pow(C)),
          IMAGE(Prla(Id(WO(A)), Image(f)), ps)))’ 
 >-- arw[GSYM IMAGE_o,o_assoc,p1_Prla,IdL] >>
 arw[] >> rpt gen_tac >> 
 rw[IMAGE_Prla,Id_def] >> rpt strip_tac >> 
 arw[Image_IMAGE] >> 
 first_x_assum irule >> arw[])
(form_goal 
 “!A B wo:mem(WO(A)) beth:mem(Pow(B)). 
  isbeth(wo,beth) ==>
 !C f:B->C. Inj(f) ==> isbeth(wo,IMAGE(f,beth))”));
end

val mEqv_def = qdefine_psym("mEqv",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(B))’]) ‘Eqv(m2s(s1),m2s(s2))’ |> gen_all

val msEqv_Pow = prove_store("msEqv_Pow",
e0
(cheat)
(form_goal “!A s0 s.msEqv(s0:mem(Pow(A)),s) ==>
 ?s1:mem(Pow(Pow(A))). msEqv(s1,Pow(s))”));


val AX5 = store_ax("AX5",
“!A.?B p:B->A Y M:B~>Y.  
 (!b.P(App(p,b),m2s(rsi(M,b)))) & 
 !a:mem(A) X. P(a,X) ==> ?b. App(p,b) = a”)


val AX5_conseq = prove_store("AX5_conseq",
e0
()
(form_goal
 “!A a:mem(A). ?S. P(a,S) ==>
  ?X. (!a. ?x. )”));



(*
isBeth(App(p, b'), m2s(rsi(M, b')))
.App(p, b') = wo
*)
val Beth_ex = prove("Beth_ex",
e0
(strip_tac >> ind_with (wo_induct |> spec_all) >>
 strip_tac (* 2 *)
 >-- (qexists_tac ‘N’ >> rw[isBeth_def] >>
     qexistsl_tac [‘N’,‘Whole(N)’] >> 
     rw[msEqv_Whole] >> irule isbeth_zord >>
     rw[msEqv_Whole]) >>
 strip_tac (* 2 *)
 >-- (rpt strip_tac >> fs[isBeth_def] >>
     qby_tac
     ‘?beth':mem(Pow(Pow(B))). isbeth(od,beth')’
     (*image of injection of beth into Pow*)
     >-- cheat >>
     pop_assum strip_assume_tac >>
     drule isbeth_sord >> 
     qsuff_tac
     ‘?s:mem(Pow(Pow(B))). msEqv(s, Pow(m2s(beth')))’
     >-- (strip_tac >>
     qexistsl_tac [‘m2s(s')’,‘Pow(B)’,‘s'’] >>
     rw[msEqv_m2s] >>
     fs[Pair_def'] >>
     first_x_assum irule >> arw[]) >>
     qby_tac ‘msEqv(beth', s)’ >-- cheat >> 
     rev_drule msEqv_Pow >>  
     pop_assum strip_assume_tac >>
     qexists_tac ‘s1’ >> cheat (* need some lemma *)) >>
 rpt strip_tac >>
 rw[isBeth_def] >>
 strip_assume_tac
 (AX5 |> qspecl [‘WO(A)’] 
 |> fVar_sInst_th “P(a:mem(WO(A)),X)”
     “isBeth(a:mem(WO(A)),X)”) >>
 (* {(wo,rsi(M,b)) | App(p,b) = wo} *)
 qsuff_tac
 ‘?ps:mem(Pow(WO(A) * Pow(Y))).
  !wo beth. 
   IN(Pair(wo,beth),ps) <=> 
   IN(wo,ods) & ?b.App(p,b) = wo & beth = rsi(M,b)’
 >-- (strip_tac >>
     qsspecl_then [‘ps’] assume_tac isbeth_lord >>
     qsuff_tac
     ‘isbeth(lord(IMAGE(p1(WO(A), Pow(Y)), ps)),
              BIGUNION(IMAGE(p2(WO(A), Pow(Y)), ps)))’
     >-- strip_tac >>
         qexistsl_tac [‘m2s(BIGUNION(IMAGE(p2(WO(A), Pow(Y)), ps)))’,‘Y’,‘BIGUNION(IMAGE(p2(WO(A), Pow(Y)), ps))’] >>
         rw[msEqv_m2s] >>
     qby_tac
      ‘IMAGE(p1(WO(A), Pow(Y)), ps) = ods’ 
     >-- cheat >> fs[] >>
     (*fs behaviour why??? *)
     first_x_assum irule >> 
     qby_tac
     ‘!wo b. IN(Pair(wo,b),ps) ==> isbeth(wo,b)’
     >-- (arw[] >> rpt strip_tac >> arw[] >>
         first_x_assum (qspecl_then [‘b'’] assume_tac) >>
         fs[isBeth_def] >> cheat (*need equiv lemma*)) >>
     arw[] >> fs[SSchain_iWO_chain_LEo,IMAGE_o] >>
     qby_tac 
     ‘IMAGE(p1(WO(A), Pow(Y)), ps) = ods’ 
     >-- cheat >>
     arw[]) >>
 strip_assume_tac
 (IN_def_P_ex |> qspecl [‘WO(A) * Pow(Y)’]
 |> fVar_sInst_th “P(pair:mem(WO(A) * Pow(Y)))”
    “?wo:mem(WO(A)) beth:mem(Pow(Y)). pair = Pair(wo,beth) &
     IN(wo,ods) &
     ?b. App(p,b) = wo & beth = rsi(M:B~>Y,b)”) >>
 qexists_tac ‘s’ >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rpt strip_tac >> rw[Pair_eq_eq] >>
 dimp_tac >> rpt strip_tac >> arw[] (* 2 *)
 >-- (qexists_tac ‘b’ >> arw[]) >>
 qexistsl_tac [‘wo’,‘rsi(M, b)’] >> arw[] >>
 qexists_tac ‘b’ >> arw[])
(form_goal 
“!A wo:mem(WO(A)). ?s. isBeth(wo,s)”));
