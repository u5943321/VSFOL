
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



(*if as constructors, will have 
O | Suc ord | U (ord set)
!!!!!!!!! *)
val Rwo_def = qdefine_fsym("Rwo",[‘wo:mem(WO(A))’])
‘App(iWO(A),wo)’ |> gen_all

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
(cheat)
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
(cheat)
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
    (!wo.Rwo(wo) = od ==> P(wo)))
  ”));

(*
val ind = iswo_ind
*)

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

val Rwo_snocm_iff_sord = prove_store("Rwo_snocm_iff_sord",
e0
(cheat)
(form_goal “!A wo0 wo a:mem(A).Rwo(wo) = snocm(Rwo(wo0),a) <=> 
 wo = sord(wo0,a)”));

val all_wo_IMAGE = prove_store("all_wo_IMAGE",
e0
()
(form_goal “SSchain(s) & Rwo(wo) = BIGUNION(s) <=> 
 wo = lord(PREIM())”));


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
         last_x_assum irule >> arw[]) >>
     rw[GSYM Rwo_snocm_iff_sord] >> rfs[]) >>
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
cheat)
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
val isbeth_cl = 
 “(!s. Eqv(m2s(s),N) & p = Pair(zord(A),s) ==>
      IN(p,beths)) & 
  (!p0 s a. IN(p0,beths) & 
            Eqv(m2s(s),Pow(m2s(Snd(p0)))) &
          p = Pair(sord(Fst(p0),a),s) ==>
          IN(p,beths)) &
  (!ps. (!p.IN(p,ps) ==> IN(p,beths)) &
        SSchain(IMAGE(iWO(A) o p1(WO(A),Pow(B)),ps)) &
        p = Pair(lord(IMAGE(p1(WO(A),Pow(B)),ps)),
                 BIGUNION(IMAGE(p2(WO(A),Pow(B)),ps))) ==>
   IN(p,beths))”
in
val (isbeth_incond,x1) = mk_incond isbeth_cl;
val isbethf_ex = mk_fex isbeth_incond x1;
val isbethf_def = mk_fdef "isbethf" isbethf_ex;
val isbethf_monotone = proved_th $
e0
(cheat)
(form_goal 
“!s1 s2.SS(s1,s2) ==> 
  SS(App(isbethf(A,B), s1), App(isbethf(A,B), s2))”)
val isbeth's_def = mk_prim isbethf_def;
val isbeths_def = mk_LFP (rastt "isbeth's(A,B)");
val isbeths_cond = mk_cond isbeths_def isbeth's_def;
val isbeths_SS = mk_SS isbeths_def isbeth's_def;
val isbeth_rules0 = mk_rules isbethf_monotone isbeths_SS isbeths_cond;
val isbeth_cases0 = mk_cases isbethf_monotone isbeth_rules0 isbeths_cond;
val isbeth_ind0 = mk_ind isbeths_cond;
val isbeth_ind1 = mk_ind1 isbethf_def isbeth_ind0;
val isbeth_ind2 = mk_ind2 isbeth_ind1;
val isbeth_cases1 = mk_case1 isbethf_def isbeth_cases0;
val isbeth_rules1 = mk_rules1 isbethf_def isbeth_rules0;
val isbeth_rules2 = mk_rules2 isbeth_rules1;
val isbeth_rules3 = mk_rules3 isbeth_rules2;
end
 
val isbeth_ind = isbeth_ind2 |> store_as "isbeth_ind";
val isbeth_cases = isbeth_cases1 |> store_as "isbeth_cases";
val isbeth_rules = isbeth_rules3 |> store_as "isbeth_rules";

val isBeth_def = qdefine_psym("isBeth",[‘wo:mem(WO(A))’,‘s’]) ‘?B beth:mem(Pow(B)). IN(Pair(wo,beth),isbeths(A,B)) & msEqv(beth,s)’
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

val isbeth_zord = isbeth_rules |> conjE1 
val isbeth_sord = 
isbeth_rules |> conjE2 |> conjE1
             |> strip_all_and_imp
             |> gen_all 
             |> disch “Eqv(m2s(s:mem(Pow(B))), Pow(m2s(Snd(p0: mem(WO(A) * Pow(B))))))”
             |> gen_all
             |> disch_all |> qgen ‘p0’
             |> qspecl 
             [‘Pair(wo:mem(WO(A)),b:mem(Pow(B)))’]
             |> rewr_rule[Pair_def']
             |> undisch |> spec_all |> rewr_rule[Pair_def'] 
  
(*

!(s : mem(Pow(B))).
               Eqv(m2s(s#), Pow(m2s(Snd(Pair(od, beth))))) ==>
               !(a' : mem(A)). IN(Pair(sord(od, a'#), s#), isbeths(A, B))

*)

(*if A can be injected into B , then Pow(A) can be injected into Pow(B)?*)
val Beth_ex = prove("Beth_ex",
e0
(strip_tac >> ind_with (wo_induct |> spec_all) >>
 strip_tac (* 2 *)
 >-- (qexists_tac ‘N’ >> rw[isBeth_def] >>
     qexistsl_tac [‘N’,‘Whole(N)’] >> 
     rw[msEqv_Whole] >> irule isbeth_zord >>
     rw[Eqv_m2s]) >>
 strip_tac (* 2 *)
 >-- rpt strip_tac >> fs[isBeth_def] >>
     qby_tac
     ‘?beth'. IN(Pair(od, beth'), isbeths(A, Pow(B))) ’
     (*image of injection of beth into Pow*)
     >-- cheat >>
     pop_assum strip_assume_tac >>
     drule isbeth_sord >> 
     qby_tac
      ‘!s:mem(Pow(Pow(B))). Eqv(m2s(s), Pow(m2s(Snd(Pair(od, beth'))))) <=> 
        Eqv(m2s(s), Pow(m2s(beth')))’ 
     >-- cheat >>
     fs[] >> pop_assum (K all_tac) >>
     qsuff_tac
     ‘?s:mem(Pow(Pow(B))). Eqv(m2s(s), Pow(m2s(beth')))’
     >-- (strip_tac >>
     qexistsl_tac [‘m2s(s')’,‘Pow(B)’,‘s'’] >>
     rw[msEqv_m2s] >>
     fs[Pair_def'] >>
     first_x_assum irule >> arw[]) >>
     

      )
(form_goal 
“!A wo:mem(WO(A)). ?s. isBeth(wo,s)”));
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
