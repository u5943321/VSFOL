(*ordinal with base set as a quotient of well orders*)

val Holdm_def = qdefine_psym("Holdm",[‘r:mem(Pow(A * B))’,‘a:mem(A)’,‘b:mem(B)’]) ‘IN(Pair(a,b),r)’
                            |> gen_all

val rdom_def = 
    IN_def_P |> spec_all 
             |> fVar_sInst_th “P(a:mem(A))”
                “?a1:mem(A). Holdm(r,a:mem(A),a1)”
             |> uex2ex_rule |> qSKOLEM "rdom" [‘r’] 
             |> gen_all

val rcod_def = 
    IN_def_P |> spec_all 
             |> fVar_sInst_th “P(a:mem(A))”
                “?a1:mem(A). Holdm(r,a1,a:mem(A))”
             |> uex2ex_rule |> qSKOLEM "rcod" [‘r’] 
             |> gen_all

val rset_def = qdefine_fsym("rset",[‘r:mem(Pow(A*A))’])
‘Union(rdom(r),rcod(r))’ |> gen_all

val strict_def =
    IN_def_P |> qspecl [‘A * A’] 
             |> fVar_sInst_th “P(a12:mem(A*A))”
             “Holdm(r:mem(Pow(A*A)),Fst(a12),Snd(a12)) & 
             ~(Fst(a12) = Snd(a12))”
        |> uex2ex_rule |> qSKOLEM "strict" [‘r’]
        |> qspecl [‘Pair(a1:mem(A),a2:mem(A))’]
        |> rewr_rule[Pair_def']
        |> gen_all

val wellfounded_def = qdefine_psym("wellfounded",
[‘r:mem(Pow(A*A))’])
‘!s. (?w. IN(w,s)) ==> ?min.IN(min,s) & 
     !w. Holdm(r,w,min) ==> ~IN(w,s)’
     |> gen_all

val reflexive_def = qdefine_psym("reflexive",
[‘r:mem(Pow(A * A))’,‘s:mem(Pow(A))’])
‘!x. IN(x,s) ==> Holdm(r,x,x)’ |> gen_all

val transitive_def = qdefine_psym("transitive",
[‘r:mem(Pow(A*A))’])
‘!x y z. Holdm(r,x,y) & Holdm(r,y,z) ==> Holdm(r,x,z)’
|> gen_all

val antisym_def = qdefine_psym("antisym",
[‘r:mem(Pow(A*A))’])
‘!x y.Holdm(r,x,y) & Holdm(r,y,x) ==> x = y’

val linear_order_def = qdefine_psym("linear_order",
[‘r:mem(Pow(A*A))’,‘s:mem(Pow(A))’])
‘SS(rdom(r),s) & SS(rcod(r),s) &
 transitive(r) & antisym(r) &
 (!x y. IN(x,s) & IN(y,s) ==> Holdm(r,x,y) | Holdm(r,y,x))’
|> gen_all

val wellorder_def = qdefine_psym("wellorder",[‘r:mem(Pow(A*A))’])
‘wellfounded(strict(r)) &
 linear_order(r,rset(r)) &
 reflexive(r,rset(r))’|> gen_all


val WO_def = Thm_2_4 |> qspecl [‘Pow(A*A)’] 
                     |> fVar_sInst_th “P(r:mem(Pow(A*A)))”
                     “wellorder(r:mem(Pow(A*A)))”
                     |> qSKOLEM "WO" [‘A’] 
                     |> qSKOLEM "iWO" [‘A’] 
                     |> gen_all 


val Rwo_def = qdefine_fsym("Rwo",[‘wo:mem(WO(A))’])
‘App(iWO(A),wo)’ |> gen_all

val WIN_def = qdefine_psym("WIN",[‘w:mem(WO(A))’,‘x:mem(A)’,
‘y:mem(A)’]) ‘Holdm(strict(Rwo(w)),x,y)’ |> gen_all

val iseg_def = IN_def_P |> spec_all 
                        |> fVar_sInst_th “P(y:mem(A))”
                           “WIN(w:mem(WO(A)),y,x)”
                        |> uex2ex_rule
                        |> qSKOLEM "iseg" [‘w’,‘x’]
                        |> gen_all

(*
val lt_def = qdefine_psym("lt",[‘r:mem(Pow(A*A))’,
                                  ‘a1:mem(A)’,‘a2:mem(A)’])
‘Holdm(r,a1,a2) & ~(a1 = a2)’ |> gen_all
*)

val elsOf_def = qdefine_fsym("elsOf",[‘w:mem(WO(A))’])
‘rset(Rwo(w))’ |> gen_all

val NOT_Holdm_Empty = prove_store("NOT_Holdm_Empty",
e0
(rw[Holdm_def,Empty_def])
(form_goal “!A x y.~Holdm(Empty(A*A),x,y)”));

val rdom_rcod_Empty = prove_store("rdom_rcod_Empty",
e0
(rw[rdom_def,rcod_def,GSYM IN_EXT_iff,
    Empty_def,NOT_Holdm_Empty] >>
 rpt strip_tac >> ccontra_tac >> fs[] )
(form_goal “!A.rdom(Empty(A*A)) = Empty(A) &
 rcod(Empty(A*A)) = Empty(A)”));

val rset_Empty = prove_store("rset_Empty",
e0
(rw[rset_def,IN_Union,rdom_rcod_Empty,Empty_def,
    Union_Empty_Empty])
(form_goal “!A.rset(Empty(A*A)) = Empty(A)”));

val strict_Empty_Empty= prove_store("strict_Empty_Empty",
e0
(rw[GSYM IN_EXT_iff] >>
 fconv_tac (redepth_fconv no_conv forall_cross_fconv) >>
 rw[strict_def,Empty_def,NOT_Holdm_Empty])
(form_goal “!A. strict(Empty(A*A)) = Empty(A*A)”));

val Empty_wellfounded = prove_store("Empty_wellfounded",
e0
(rw[wellfounded_def,Empty_def,NOT_Holdm_Empty])
(form_goal
 “!A. wellfounded(Empty(A*A))”));

val Empty_reflexive = prove_store("Empty_reflexive",
e0
(rw[reflexive_def,Empty_def])
(form_goal “!A. reflexive(Empty(A * A),Empty(A))”));


val Empty_transitive = prove_store("Empty_transitive",
e0
(rw[transitive_def,Empty_def,NOT_Holdm_Empty])
(form_goal “!A. transitive(Empty(A * A))”));


val Empty_antisym = prove_store("Empty_antisym",
e0
(rw[antisym_def,Empty_def,NOT_Holdm_Empty])
(form_goal “!A. antisym(Empty(A * A))”));

val Empty_linear_order = prove_store("Empty_linear_order",
e0
(rw[linear_order_def,rdom_rcod_Empty,SS_Refl,Empty_def,
    Empty_antisym,Empty_transitive])
(form_goal “!A.linear_order(Empty(A * A), Empty(A))”));


val Empty_wellorder = prove_store("Empty_wellorder",
e0
(strip_tac >> rw[wellorder_def,strict_Empty_Empty,
                 Empty_wellfounded,Empty_reflexive,
                 rset_Empty,Empty_linear_order])
(form_goal “!A.wellorder(Empty(A*A))”));

val WO_uex = prove_store("WO_uex",
e0
(rpt strip_tac >> rw[Rwo_def] >> 
 irule $ iffRL Inj_ex_uex >> flip_tac >>
 rw[GSYM WO_def] >> arw[])
(form_goal
 “!A r:mem(Pow(A*A)). wellorder(r) ==>
      ?!w. Rwo(w) = r”));

val zwo_def = WO_uex |> qsspecl [‘Empty(A*A)’]
                     |> rewr_rule[Empty_wellorder]
                     |> uex2ex_rule |> qSKOLEM "zwo" [‘A’]
                     |> gen_all

val Abswo_def = qdefine_fsym("Abswo",[‘A’])
‘LINV(iWO(A),zwo(A))’ |> gen_all 

val mkWO = qdefine_fsym("mkWO",[‘r:mem(Pow(A*A))’])
‘App(Abswo(A),r)’ |> gen_all

val orderiso_def = qdefine_psym("orderiso",[‘r1:mem(WO(A))’,
                                      ‘r2:mem(WO(B))’])
‘?f:A->B.
 (!x. IN(x,elsOf(r1)) ==> IN(App(f,x),elsOf(r2))) &
 (!x1 x2.IN(x1,elsOf(r1)) & IN(x2,elsOf(r1)) ==>
  (App(f,x1) = App(f,x2) <=> x1 = x2)) & 
 (!y. IN(y,elsOf(r2)) ==> ?x. IN(x,elsOf(r1)) & App(f,x) = y) &
 (!x y. WIN(r1,x,y) ==> WIN(r2,App(f,x),App(f,y)))’
|> gen_all

val oiso_def = 
AX1 |> qspecl [‘WO(A)’,‘WO(A)’] 
    |> fVar_sInst_th “P(r1:mem(WO(A)),r2:mem(WO(A)))”
       “orderiso(r1:mem(WO(A)),r2:mem(WO(A)))”
    |> uex2ex_rule |> qSKOLEM "oiso" [‘A’] 
    |> qspecl [‘r1:mem(WO(A))’,‘r2:mem(WO(A))’]
    |> gen_all



val rrestrict_def = 
    IN_def_P |> qspecl [‘A*A’] 
             |> fVar_sInst_th “P(a12:mem(A * A))”
                “Holdm(r,Fst(a12),Snd(a12)) &
                 IN(Fst(a12),s:mem(Pow(A))) &
                 IN(Snd(a12),s:mem(Pow(A)))”
             |> uex2ex_rule
             |> qSKOLEM "rrestrict" [‘r’,‘s’]
             |> qspecl [‘Pair(a1:mem(A),a2:mem(A))’] 
             |> gen_all

val wobound_def = qdefine_fsym("wobound",[‘x:mem(A)’,‘w:mem(WO(A))’]) ‘mkWO(rrestrict(Rwo(w),iseg(w,x)))’
|> gen_all

val WIN_wobound = prove_store("WIN_wobound",
e0
(cheat)
(form_goal “!A x:mem(A) y z w.WIN(wobound(z,w),x,y) <=> 
 WIN(w,x,z) & WIN(w,y,z) & WIN(w,x,y) ”));

val wobound2 = prove_store("wobound2",
e0
(cheat)
(form_goal “!A w a:mem(A) b.WIN(w,a,b) ==>
 wobound(a,wobound(b,w)) = wobound(a,w)”));

val orderlt_def = qdefine_psym("orderlt",
[‘w1:mem(WO(A))’,‘w2:mem(WO(B))’])
‘?x. IN(x,elsOf(w2)) & orderiso(w1,wobound(x,w2))’
|> gen_all

val orderlt_trichotomy = prove_store("orderlt_trichotomy",
e0
(cheat)
(form_goal “!A B w1:mem(WO(A)) w2:mem(WO(B)).orderlt(w1,w2) | orderiso(w1,w2) | orderlt(w2,w1)”));

val ordinal_def = 
    Thm_2_4 |> qspecl [‘Pow(WO(A))’] 
            |> fVar_sInst_th “P(a:mem(Pow(WO(A))))”
               “?w.a = rsi(oiso(A),w)”
            |> qSKOLEM "ordinal" [‘A’] 
            |> qSKOLEM "iord" [‘A’] 



val ordinal_uex = prove_store("ordinal_rsi_uex",
e0
(rpt strip_tac >> rw[Rwo_def] >> 
 irule $ iffRL Inj_ex_uex >> flip_tac >>
 rw[GSYM WO_def] >> arw[])
(form_goal
 “!A r:mem(Pow(A*A)). wellorder(r) ==>
      ?!w. Rwo(w) = r”));


val r2f_def = proved_th $
e0
cheat
(form_goal “!R:A~>B. ?!f:A * B -> 1+1.
 !a b. App(f,Pair(a,b)) = App(i2(1,1),dot)  <=> Holds(R,a,b)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "r2f" [‘R’] |> gen_all


val oiso_ER = prove_store("oiso_ER",
e0
(cheat)
(form_goal “!A. ER(oiso(A))”));

val prrel_oiso_ER = prove_store("prrel_oiso_ER",
e0
(cheat)
(form_goal “!A B. ER(prrel(oiso(A),oiso(B)))”));

val oiso_iord_Quot = prove_store("oiso_iord_Quot",
e0
(cheat)
(form_goal “Quot(oiso(A),iord(A))”));



val oiso_iord_Quot_cong = prove_store("oiso_iord_Quot_cong",
e0
(cheat)
(form_goal “!A.Quot(prrel(oiso(A),oiso(A)),
                 ipow2(iord(A),iord(A)))”));

val orderltr_def = 
AX1 |> qspecl [‘WO(A)’,‘WO(A)’] 
    |> fVar_sInst_th “P(w1:mem(WO(A)),w2:mem(WO(A)))”
       “orderlt(w1:mem(WO(A)),w2:mem(WO(A)))”
    |> uex2ex_rule |> qSKOLEM "orderltr" [‘A’] 
    |> gen_all

val resp1_r2f_orderltr = prove_store("resp1_r2f_orderltr",
e0
(cheat)
(form_goal 
 “!A.resp1(r2f(orderltr(A)), prrel(oiso(A), oiso(A))) ”));


val zord_def = 
  Quot_rsi_uex |> qsspecl [‘oiso(A)’,‘iord(A)’]
               |> rewr_rule[oiso_iord_Quot] 
               |> qspecl [‘zwo(A)’] 
               |> uex2ex_rule 
               |> qSKOLEM "zord" [‘A’]
               |> gen_all

val oiso_iord_abs_cong = 
abs_cong |> qsspecl [‘oiso(A)’,‘iord(A)’,‘oiso(A)’,‘iord(A)’]
         |> rewr_rule[oiso_ER,oiso_iord_Quot]

val Abso_def = qdefine_fsym("Abso",[‘A’])
‘Abs(oiso(A), iord(A), zord(A))’

val abso_def = qdefine_fsym("abso",[‘w:mem(WO(A))’])
‘abs(oiso(A), iord(A), zord(A), w)’ |> gen_all

val ordltf_def = 
Quot_UMP |> qsspecl [‘prrel(oiso(A),oiso(A))’]
         |> rewr_rule[prrel_oiso_ER]
         |> qsspecl [‘r2f(orderltr(A))’]
         |> rewr_rule[resp1_r2f_orderltr] 
         |> qsspecl [‘ipow2(iord(A),iord(A))’] 
         |> rewr_rule[oiso_iord_Quot_cong] 
         |> qspecl [‘Pair(zord(A),zord(A))’]
         |> uex2ex_rule
         |> qSKOLEM "ordltf" [‘A’] 
         |> qspecl [‘Pair(w1:mem(WO(A)),w2:mem(WO(A)))’] 
         |> rewr_rule[oiso_iord_abs_cong,
                      GSYM abso_def]

val ordlt_def = 
qdefine_psym("ordlt",[‘ord1:mem(ordinal(A))’,‘ord2:mem(ordinal(A))’]) ‘App(ordltf(A), Pair(ord1, ord2)) = true’
|> gen_all



val ordle_def = qdefine_psym("ordle",[‘ord1:mem(ordinal(A))’,‘ord2:mem(ordinal(A))’]) 
 ‘~(ordlt(ord2,ord1))’
|> gen_all



val ordlt_orderlt = prove_store("ordlt_orderlt",
e0
(rw[ordlt_def,ordltf_def,r2f_def',orderltr_def])
(form_goal
 “!A w1 w2:mem(WO(A)). 
   ordlt(abso(w1),abso(w2)) <=> orderlt(w1,w2) ”));

val ordltr_def = 
AX1 |> qspecl [‘ordinal(A)’,‘ordinal(A)’] 
    |> uex2ex_rule |> qSKOLEM "ordltr" [‘A’] 
    |> qspecl [‘ord1:mem(ordinal(A))’,‘ord2:mem(ordinal(A))’] 
    |> gen_all

val ordltm_def = qdefine_fsym("ordltm",[‘A’])
‘r2m(ordltr(A))’ |> gen_all

val ordltm_wellorder = prove_store("ordltm_wellorder",
e0
cheat
(form_goal “!A. wellorder(ordltm(A))”));


(*
Definition 4. Well-foundedness also allows the definition of a “least” operator for or-
dinals:
(oleast) (P : α ordinal → bool) =
ε(x : αordinal).P x ∧ ∀(y : αordinal).y <x ⇒ ¬P y
This is well-defined as long as the predicate (or set) P is not everywhere false (the empty set).
*)


val oleast_ex0 = proved_th $
e0
(rpt strip_tac >>
 cheat)
(form_goal 
 “!A s:mem(Pow(ordinal(A))). (?ord. IN(ord,s)) ==> 
        ?!x. IN(x,s) & !y. ordlt(y,x) ==> ~IN(y,s)”)

val oleastf_ex = proved_th $
e0
(cheat)
(form_goal 
 “?!oleast:Pow(ordinal(A)) -> ordinal(A) +1.
  (!s. (~(s = Empty(ordinal(A))) ==>
     ?ord.App(i1(ordinal(A),1),ord) = App(oleast,s) &
      IN(ord,s) &
      !y. ordlt(y,ord) ==> ~IN(y,s))) &
  App(oleast,Empty(ordinal(A))) = NONE(ordinal(A))  
      ”)
|> uex2ex_rule |> qSKOLEM "oleastf" [‘A’]

val oleast_def = qdefine_fsym("oleast",[‘s:mem(Pow(ordinal(A)))’]) ‘App(oleastf(A),s)’

val predsf_def = proved_th $
e0
cheat
(form_goal “!A. ?!predf.
 !alpha a:mem(ordinal(A)). IN(a,App(predf,alpha)) <=> ordlt(a,alpha) ”)
|> spec_all |> uex2ex_rule |> qSKOLEM "predsf" [‘A’]

val preds_def = 
qdefine_fsym("preds",[‘alpha:mem(ordinal(A))’]) 
‘App(predsf(A),alpha)’

val sup_def = qdefine_fsym("sup",[‘s:mem(Pow(ordinal(A)))’])
‘oleast(Compl(BIGUNION(IMAGE(predsf(A),s))))’
|> gen_all

val isomax_def = 
qdefine_psym
("isomax",[‘s:mem(Pow(ordinal(A)))’,‘ord:mem(ordinal(A))’])
‘(IN(ord,s) & !y. ordlt(ord,y) ==> ~IN(y,s))’
|> gen_all

val omaxf_ex = proved_th $
e0
(cheat)
(form_goal 
 “?!omaxf:Pow(ordinal(A)) -> ordinal(A) +1.
  (!s ord. isomax(s,ord) ==>
           App(omaxf,s) = SOME(ord)) &
  (!s. (!ord. ~isomax(s,ord)) ==> 
    App(omaxf,s) = NONE(ordinal(A)))”)
|> uex2ex_rule |> qSKOLEM "omaxf" [‘A’]

val omax_def = qdefine_fsym("omax",[‘s:mem(Pow(ordinal(A)))’]) ‘App(omaxf(A),s)’


val islimit_def = qdefine_psym("islimit",[‘alpha:mem(ordinal(A))’]) ‘omax(preds(alpha)) = NONE(ordinal(A))’ 

val ordSUC_def = proved_th $
e0
cheat
(form_goal “!A α:mem(ordinal(A)). ?!sα. ordlt(α,sα) &
 !β. ordlt(α,β) ==> ordlt(sα,β) | sα = β”)
|> spec_all |> uex2ex_rule |> qSKOLEM "ordSUC" [‘α’]


val orderlt_WF = prove_store("orderlt_WF",
e0
(cheat)
(form_goal “!A B.(?w:mem(WO(A)).IN(w,B)) ==> ?min. IN(min,B) & !b. orderlt(b,min) ==> ~IN(b,B)”));

val Rord_def = qdefine_fsym("Rord",[‘α:mem(ordinal(A))’])
‘App(iord(A),α)’ |> gen_all

val abso_Abso = prove_store("abso_Abso",
e0
(rw[abso_def,Abso_def,abs_def])
(form_goal “abso(a) = App(Abso(A),a)”));

val ord_rep_ex =  
Abs_Surj |> qsspecl [‘oiso(A)’,‘iord(A)’] 
         |> rewr_rule[oiso_iord_Quot] 
         |> qspecl [‘zord(A)’] 
         |> rewr_rule[GSYM Abso_def,Surj_def,
                      GSYM abso_Abso]
         |> gen_all




val Quot_IN_BIGUNION_abso = 
 Quot_IN_BIGUNION_abs |> qsspecl [‘oiso(A)’] 
                      |> rewr_rule[oiso_ER] 
                      |> qsspecl [‘iord(A)’] 
                      |> rewr_rule[oiso_iord_Quot] 
                      |> qspecl [‘zord(A)’] 
                      |> rewr_rule[GSYM abso_def] 
                      |> gen_all

val ordlt_WF0 = prove_store("ordlt_WF0",
e0
(rpt strip_tac >> 
 qsspecl_then [‘BIGUNION(IMAGE(iord(A),B))’] 
 assume_tac orderlt_WF >>
 qsspecl_then [‘w’] (x_choose_then "w0" assume_tac)
 ord_rep_ex >>
 qby_tac 
 ‘IN(w0, BIGUNION(IMAGE(iord(A), B)))’ 
 >--(irule  $ iffRL Quot_IN_BIGUNION_rep >>
    qexistsl_tac [‘zord(A)’,‘oiso(A)’] >>
    rw[oiso_ER,oiso_iord_Quot] >>
    qexists_tac ‘w’ >> fs[abso_def]) >>
 qby_tac ‘?w0. IN(w0, BIGUNION(IMAGE(iord(A), B)))’
 >-- (qexists_tac ‘w0’ >> arw[]) >>
 first_x_assum drule >>
 (*think about the pattern in this step*)
 pop_assum strip_assume_tac >>
 qexists_tac ‘abso(min)’ >> strip_tac 
 >-- arw[GSYM Quot_IN_BIGUNION_abso] >>
 rpt strip_tac >>
 qsspecl_then [‘b’] (strip_assume_tac o GSYM) ord_rep_ex >> 
 arw[] >> rw[ordlt_orderlt] >>
 arw[GSYM Quot_IN_BIGUNION_abso] >>
 first_x_assum irule >> fs[ordlt_orderlt])
(form_goal 
“!A B.(?w:mem(ordinal(A)).IN(w,B)) ==> ?min. IN(min,B) & !b. ordlt(b,min) ==> ~IN(b,B)”));


val ord_induction0 = prove_store("ord_induction0",
e0
(rpt strip_tac >> ccontra_tac >>
 qby_tac ‘?a1. IN(a1,Compl(s))’ 
 >-- (qexists_tac ‘a’ >> arw[IN_Compl]) >>
 drule ordlt_WF0 >>
 pop_assum strip_assume_tac >> fs[IN_Compl] >>
 first_x_assum drule >> fs[])
(form_goal 
 “!s.(!min:mem(ordinal(A)). (!b. ordlt(b,min) ==> IN(b,s)) ==> IN(min,s)) ==> !a:mem(ordinal(A)). IN(a,s)”));


val ord_induction = prove_store("ord_induction",
e0
(strip_assume_tac 
 (IN_def_P |> GSYM |> qspecl [‘ordinal(A)’] |> uex2ex_rule) >>
 arw[ord_induction0])
(form_goal 
 “(!min:mem(ordinal(A)). (!b. ordlt(b,min) ==> P(b)) ==> P(min)) ==> !a:mem(ordinal(A)). P(a)”));

val option_CASES = prove_store("option_CASES",
e0
(cheat)
(form_goal “!A ao:mem(A+1). ao = NONE(A) | ?a. ao = SOME(a)”));

val preds_omax_SOME_SUC = prove_store("preds_omax_SOME_SUC",
e0
cheat
(form_goal 
 “!A a b:mem(ordinal(A)).omax(preds(a)) = SOME(b) <=> a = ordSUC(b)”));


val ordlt_ZERO = prove_store("ordlt_ZERO",
e0
(cheat)
(form_goal “!A a:mem(ordinal(A)). ordlt(a,zord(A))”));

val ordle_lteq = prove_store("ordle_lteq",
e0
cheat
(form_goal “!A a b:mem(ordinal(A)).
 ordle(a,b) <=> ordlt(a,b) | a = b”));

val simple_ord_induction = prove_store("simple_ord_induction",
e0
(strip_tac >> match_mp_tac ord_induction >>
 qsuff_tac
 ‘!a:mem(ordinal(A)). (!b. ordlt(b,a) ==> P(b)) ==> P(a)’ 
 >-- rw[] >>
 strip_tac >>
 qcases ‘a = zord(A)’ 
 >-- arw[] >>
 qsspecl_then [‘omax(preds(a))’] 
 strip_assume_tac option_CASES (* 2 *)
 >-- (qby_tac ‘ordlt(zord(A),a)’ 
     >-- cheat >>
     rpt strip_tac >>
     last_x_assum irule >> arw[]) >>
 fs[preds_omax_SOME_SUC] >>
 rpt strip_tac >> last_x_assum irule >>
 first_x_assum irule >> rw[ordSUC_def])
(form_goal 
 “P(zord(A)) &
  (!α:mem(ordinal(A)). P(α) ==> P(ordSUC(α))) &
  (!α. omax(preds(α)) = NONE(ordinal(A)) &
       ordlt(zord(A),α) &
       (!β. ordlt(β,α) ==> P(β)) ==> P(α)) ==>
  !α:mem(ordinal(A)). P(α)”));


val ord_RECURSION = prove_store("ord_RECURSION",
e0
cheat
(form_goal
 “!A B z:mem(B) 
     sf:ordinal(A) * B-> B 
     lf:ordinal(A) * Pow(B) -> B.
  ?h:ordinal(A)->B.
   App(h,zord(A)) = z &
   (!α. App(h,ordSUC(α)) = App(sf,Pair(α,App(h,α)))) &
   !α. ordlt(zord(A),α) & islimit(α) ==>
   App(h,α) = App(lf,Pair(α,IMAGE(h,preds(α))))”));


val INJ_def = 
qdefine_psym("INJ",
[‘f:A->B’,‘s:mem(Pow(A))’,‘t:mem(Pow(B))’])
‘(!x. IN(x,s) ==> IN(App(f,x),t)) &
(!x y. IN(x,s) & IN(y,s) ==> App(f,x) = App(f,y) ==>
 x = y)’ |> gen_all


val SURJ_def = 
qdefine_psym("SURJ",
[‘f:A->B’,‘s:mem(Pow(A))’,‘t:mem(Pow(B))’])
‘(!x. IN(x,s) ==> IN(App(f,x),t)) &
(!x. IN(x,t) ==> ?y. IN(y,s) & App(f,y) = x)’ |> gen_all

 
val BIJ_def = 
qdefine_psym
("BIJ",[‘f:A->B’,‘s:mem(Pow(A))’,‘t:mem(Pow(B))’])
‘INJ(f,s,t) & SURJ(f,s,t)’ |> gen_all


val POW_def = IN_def_P |> qspecl [‘Pow(A)’] 
                       |> fVar_sInst_th “P(s:mem(Pow(A)))”
                          “SS(s,s0:mem(Pow(A)))”
                       |> uex2ex_rule 
                       |> qSKOLEM "POW" [‘s0’]
                       |> gen_all

val cardeq_def = 
qdefine_psym("cardeq",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(B))’])
‘?f.BIJ(f,s1,s2)’

val Snds_def = qdefine_fsym("Snds",
[‘abs:mem(Pow(A * B))’])
‘IMAGE(p2(A,B),abs)’ |> gen_all

val cardeqr_def = 
AX1 |> qspecl [‘Pow(A)’,‘Pow(B)’] 
    |> fVar_sInst_th “P(s1:mem(Pow(A)),s2:mem(Pow(B)))”
       “cardeq(s1:mem(Pow(A)),s2:mem(Pow(B)))” 
    |> uex2ex_rule 
    |> qSKOLEM "cardeqr" [‘A’,‘B’]
    |> gen_all 

val cardeqf_def = qdefine_fsym("cardeqf",
[‘A’,‘B’]) ‘r2f(cardeqr(A,B))’ |> gen_all

(*predicate to member of power set*)
val p2m_def =
IN_def_P 
|> qspecl [‘A’] 
|> fVar_sInst_th “P(a:mem(A))”
   “App(f:A->1+1,a) = true”
|> uex2ex_rule |> qSKOLEM "p2m" [‘f’] 
|> gen_all

val POWf_def = fun_tm_compr_uex 
("s",mem_sort (rastt "Pow(A)"))
(rastt "POW(s:mem(Pow(A)))")
|> uex2ex_rule |> qSKOLEM "POWf" [‘A’]

val sf0_ex = proved_th $
e0
cheat
(form_goal
 “?!sf0:Pow(Pow(B)) -> Pow(Pow(B)).
  !ss t. IN(t,App(sf0,ss)) <=> 
      ?s. IN(s,ss) & cardeq(POW(s),t)”)
|> uex2ex_rule 
|>qSKOLEM "sf0"[‘B’]


val bethf_def = 
ord_RECURSION  
|> qspecl [‘A’,‘Pow(Pow(B))’]  
|> qspecl [‘p2m(Ap1(cardeqf(B,N),Whole(N)))’]
|> qspecl [‘sf0(B) o p2(ordinal(A),Pow(Pow(B)))’]
|> qspecl [‘BU(Pow(B)) o p2(ordinal(A),Pow(Pow(Pow(B))))’]
|> qSKOLEM "bethf" [‘A’,‘B’]

val beth_def = 
 qdefine_psym("beth",[‘α:mem(ordinal(A))’,‘b:mem(Pow(B))’])
‘IN(b,App(bethf(A,B),α))’ |> gen_all


val beth_cardeq = prove_store("beth_cardeq",
e0
cheat
(form_goal
 “!α:mem(ordinal(A)).
  !B1 beth1:mem(Pow(B1)) B2 beth2:mem(Pow(B2)).
   beth(α,beth1) & beth(α,beth2) ==>
   cardeq(beth1,beth2)”));


val 


val beth_ex = prove_store("beth_ex",
e0
(strip_tac >>
 ind_with simple_ord_induction >>
 rpt strip_tac (* 3 *)
 >-- (qexistsl_tac [‘N’,‘Whole(N)’] >> cheat) 
 >-- (*inject b into Pow(Pow(B))*) cheat >>
 )
(form_goal  “!A α:mem(ordinal(A)). 
 ?B b:mem(Pow(B)).beth(α,b)”)



rastt "Ap1(cardeqf(B,B),Whole(N))"

val beth0_cl = 
 “(!s:mem(Pow(B)). cardeq(s,Whole(N)) & 
       p = Pair(zord(A),s) ==>
      IN(p,beths)) & 
  (!p0 b1.
       IN(p0,beths) & 
       cardeq(b1,Snd(p0)) &
       p = Pair(ordSUC(Fst(p0)),b1) ==>
       IN(p,beths)) & 
  (!p0s α b1.
       (!α0 b0. IN(Pair(α0,b0),p0s) ==> 
        IN(Pair(α0,b0),beths) & ordlt(α0,α)) &
       (!α0. 
         ) & 
       islimit(α) & ordlt(zord(A),α) & 
       cardeq(b1,BIGUNION(Snds(p0s))) &
       p = Pair(α,b1) ==>
       IN(p,beths))”
in
val (beth0_incond,x1) = mk_incond beth0_cl;
val beth0f_ex = mk_fex beth0_incond x1;
val beth0f_def = mk_fdef "beth0f" beth0f_ex;
val beth0f_monotone = proved_th $
e0
(rpt strip_tac >> fs[SS_def,beth0f_def] >>
 rpt strip_tac (* 3 *)
 >-- (disj1_tac >> qexists_tac ‘s’ >> arw[]) 
 >-- (disj2_tac >> disj1_tac >>
     qexistsl_tac [‘p0’,‘b1’] >>
     arw[] >> first_x_assum irule >> arw[]) >>
 disj2_tac >> disj2_tac >>
 qexistsl_tac [‘p0s’,‘α’,‘b1’] >> arw[] >>
 rpt strip_tac >> first_x_assum drule >> 
 first_x_assum irule >> arw[])
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







val PSS_def = 
qdefine_psym("PSS",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘SS(s1,s2) & ~(s1 = s2)’ |> gen_all

(*proper subsets*)
val Pss_def =
IN_def_P |> qspecl [‘Pow(A)’] 
         |> fVar_sInst_th “P(a:mem(Pow(A)))”
            “PSS(a,s0:mem(Pow(A)))”
         |> uex2ex_rule 
         |> qSKOLEM "Pss" [‘s0’]
         |> gen_all


val INmr_def = qdefine_psym("INmr",[‘a:mem(A)’,
                                    ‘r:mem(Pow(A*A))’])
‘?a1. IN(Pair(a,a1),r) | IN(Pair(a1,a),r)’ |> gen_all


val INr_def = qdefine_psym("INr",[‘a:mem(A)’,‘R:A~>A’])
‘?a1. Holds(R,a,a1) | Holds(R,a1,a)’

val snocrel_def = 
AX1 |> qspecl [‘A’,‘A’] 
    |> fVar_sInst_th “P(a1:mem(A),a2:mem(A))”
    “ Holds(R:A~>A,a1,a2) | (INr(a1,R) & a2 = a)”
    |> uex2ex_rule |> qSKOLEM "snocrel" [‘R’,‘a’]
    |> qspecl [‘a1:mem(A)’,‘a2:mem(A)’]
    |> gen_all


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

val snocm_def = qdefine_fsym("snocm",[‘r:mem(Pow(A * A))’,‘a:mem(A)’]) ‘r2m(snocrel(m2r(r),a))’ 
 

(*do not really need the precondition, but want to make sure the condition is checked.*)
val NOTINmr_snocm = prove_store("NOTINmr_snocm",
e0
(rpt strip_tac >> 
rw[snocm_def,r2m_def,snocrel_def,m2r_def,INr_def,INmr_def])
(form_goal
 “!A r:mem(Pow(A*A)) a. ~INmr(a,r) ==>
  !a1 a2. IN(Pair(a1,a2),snocm(r,a)) <=> 
          IN(Pair(a1,a2),r) | (INmr(a1,r) & a2 = a)”));

local
val Wo_cl = 
 “(od = Empty(A * A) ==> IN(od,wo)) &
  (!od0 a.
      IN(od0,wo) & ~INmr(a,od0) & od = snocm(od0,a) 
      ==> IN(od,wo)) &
  (!s. (!od0. IN(od0,s) ==> IN(od0,wo)) & 
       SSchain(s) &
       od = BIGUNION(s) ==>
   IN(od,wo)) ”
in
val (Wo_incond,x1) = mk_incond Wo_cl;
val Wof_ex = mk_fex Wo_incond x1;
val Wof_def = mk_fdef "Wof" Wof_ex;
val Wof_monotone = proved_th $
e0
(rpt strip_tac >>
 rw[SS_def,Wof_def] >> rpt strip_tac (* 3 *)
 >-- arw[] 
 >-- (disj2_tac >> disj1_tac >>
     qexistsl_tac [‘od0’,‘a'’] >> arw[] >>
     fs[SS_def] >> first_x_assum irule >> arw[]) >>
 disj2_tac >> disj2_tac >>
 qexists_tac ‘s’ >> arw[] >> 
 rpt strip_tac >> first_x_assum drule >>
 fs[SS_def] >> first_x_assum irule >> arw[])
(form_goal 
“!s1 s2.SS(s1,s2) ==> 
  SS(App(Wof(A), s1), App(Wof(A), s2))”)
val Wo's_def = mk_prim Wof_def;
val Wos_def = mk_LFP (rastt "Wo's(A)");
val Wos_cond = mk_cond Wos_def Wo's_def;
val Wos_SS = mk_SS Wos_def Wo's_def;
val Wo_rules0 = mk_rules Wof_monotone Wos_SS Wos_cond;
val Wo_cases0 = mk_cases Wof_monotone Wo_rules0 Wos_cond;
val Wo_ind0 = mk_ind Wos_cond;
val Wo_ind1 = mk_ind1 Wof_def Wo_ind0;
val Wo_ind2 = mk_ind2 Wo_ind1;
val Wo_cases1 = mk_case1 Wof_def Wo_cases0;
val Wo_rules1 = mk_rules1 Wof_def Wo_rules0;
val Wo_rules2 = mk_rules2 Wo_rules1;
val Wo_rules3 = mk_rules3 Wo_rules2;
end

val oiso_def = 
qdefine_psym("oiso",[‘f:A->B’,‘r1:mem(Pow(A*A))’,
                              ‘r2:mem(Pow(B*B))’]) 
‘!a1 a2. IN(Pair(a1,a2),r1) <=> IN()’
