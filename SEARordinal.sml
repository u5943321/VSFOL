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


val destWO_def = qdefine_fsym("destWO",[‘wo:mem(WO(A))’])
‘App(iWO(A),wo)’ |> gen_all

val WIN_def = qdefine_psym("WIN",[‘w:mem(WO(A))’,‘x:mem(A)’,
‘y:mem(A)’]) ‘Holdm(strict(destWO(w)),x,y)’ |> gen_all

val iseg_def = IN_def_P |> spec_all 
                        |> fVar_sInst_th “P(y:mem(A))”
                           “WIN(w:mem(WO(A)),y,x)”
                        |> uex2ex_rule
                        |> qSKOLEM "iseg" [‘w’,‘x’]
                        |> gen_all

val elsOf_def = qdefine_fsym("elsOf",[‘w:mem(WO(A))’])
‘rset(destWO(w))’ |> gen_all

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
(rpt strip_tac >> rw[destWO_def] >> 
 irule $ iffRL Inj_ex_uex >> flip_tac >>
 rw[GSYM WO_def] >> arw[])
(form_goal
 “!A r:mem(Pow(A*A)). wellorder(r) ==>
      ?!w. destWO(w) = r”));

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

val wobound_def = qdefine_fsym("wobound",[‘x:mem(A)’,‘w:mem(WO(A))’]) ‘mkWO(rrestrict(destWO(w),iseg(w,x)))’
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
(rpt strip_tac >> rw[destWO_def] >> 
 irule $ iffRL Inj_ex_uex >> flip_tac >>
 rw[GSYM WO_def] >> arw[])
(form_goal
 “!A r:mem(Pow(A*A)). wellorder(r) ==>
      ?!w. destWO(w) = r”));


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
 (*think about the pattern in this step about really auto quotient proof*)
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

(*
val lf0_ex = proved_th $
e0
cheat
(form_goal
 “?!lf0:Pow(Pow(Pow(B))) -> Pow(Pow(B)).
  !ss t. IN(t,App(lf0,ss)) <=> 
         (~(ss = Empty(Pow(Pow(B))))) &
         (!s.IN(s,ss) ==> ~(s = Empty(Pow(B)))) &
         cardeq(BIGUNION(BIGUNION(ss)),t)”)
|> uex2ex_rule 
|>qSKOLEM "lf0"[‘B’]

*)

(*preds beths*)
val pbeths_def =
IN_def_P |> qspecl [‘ordinal(A) * Pow(B)’] 
         |> fVar_sInst_th “P(pair:mem(ordinal(A) * Pow(B)))”
            “beth(Fst(pair:mem(ordinal(A) * Pow(B))),Snd(pair)) &
             ordlt(Fst(pair),α)” 
         |> uex2ex_rule |> qSKOLEM "pbeths" [‘α’,‘B’]



(*is selection, takes a *)
val isseletn_def = qdefine_psym
("isseletn",[‘ss:mem(Pow(Pow(A)))’,‘slc:mem(Pow(A))’])
‘?f:A-> Pow(A). BIJ(f,slc,ss)’

val cardleq_def = 
qdefine_psym("cardleq",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(B))’])
‘?f:A->B. INJ(f,s1,s2)’ |> gen_all

val ssup_def =
IN_def_P |> qspecl [‘Pow(B)’] 
         |> fVar_sInst_th “P(ssup:mem(Pow(B)))”
            “(!s:mem(Pow(A)).
              IN(s,ss) ==> cardleq(s,ssup:mem(Pow(B)))) &
             (!ssup':mem(Pow(B)).
               (!s.IN(s,ss) ==> cardleq(s,ssup)) ==>
               cardleq(ssup,ssup'))”
         |> uex2ex_rule
         |> qSKOLEM "ssup" [‘ss’,‘B’]


val issup_def = 
qdefine_psym
("issup",[‘sup:mem(Pow(B))’,‘ss:mem(Pow(Pow(A)))’])
‘IN(sup,ssup(ss,B))’

val lf0_ex = proved_th $
e0
cheat
(form_goal
 “?!lf0:Pow(Pow(Pow(B))) -> Pow(Pow(B)).
  !ss t. 
    IN(t,App(lf0,ss)) <=> 
    (~(ss = Empty(Pow(Pow(B))))) &
    (!s.IN(s,ss) ==> ~(s = Empty(Pow(B)))) &
    issup(t,BIGUNION(ss))”)
|> uex2ex_rule 
|> qSKOLEM "lf0"[‘B’]


val bethf_def = 
ord_RECURSION  
|> qspecl [‘A’,‘Pow(Pow(B))’]  
|> qspecl [‘p2m(Ap1(cardeqf(B,N),Whole(N)))’]
|> qspecl [‘sf0(B) o p2(ordinal(A),Pow(Pow(B)))’]
|> qspecl [‘lf0(B) o p2(ordinal(A),Pow(Pow(Pow(B))))’]
|> qSKOLEM "bethf" [‘A’,‘B’]

val beth_def = 
 qdefine_psym("beth",[‘α:mem(ordinal(A))’,‘b:mem(Pow(B))’])
‘IN(b,App(bethf(A,B),α))’ |> gen_all

(*
val beth_cardeq = prove_store("beth_cardeq",
e0
(ind_with simple_ord_induction >> 
 rpt strip_tac (* 3 *)
 >-- cheat 
 >-- (*card eq implies card pow eq*) cheat >>
 )
(form_goal
 “!α:mem(ordinal(A)).
  !B1 beth1:mem(Pow(B1)) B2 beth2:mem(Pow(B2)).
   beth(α,beth1) ==>
   (beth(α,beth2) <=>
   cardeq(beth1,beth2))”));

*)

val App_cardeqf = prove_store("App_cardeqf",
e0
(rw[cardeqf_def,r2f_def',cardeqr_def])
(form_goal “ App(cardeqf(A, B), Pair(s1:mem(Pow(A)), s2:mem(Pow(B)))) = true <=> 
 cardeq(s1,s2)”));


val beth_zord = prove_store("beth_zord",
e0
(rpt strip_tac >>
 rw[beth_def] >>
 rw[bethf_def,p2m_def,Ap1_def,App_cardeqf])
(form_goal
 “!B b:mem(Pow(B)). beth(zord(A),b) <=> 
 cardeq(b,Whole(N))”));

val cardeq_SYM = prove_store("cardeq_SYM",
e0
(cheat)
(form_goal
 “cardeq(s1:mem(Pow(A)),s2:mem(Pow(B))) ==> cardeq(s2,s1)”));

val beth_ordSUC = prove_store("beth_ordSUC",
e0
(rpt strip_tac >>
 rw[beth_def,bethf_def,App_App_o,App_p2_Pair,sf0_ex] >>
 dimp_tac >> rpt strip_tac 
 >-- (qexists_tac ‘s’ >> arw[] >>
     drule cardeq_SYM >> arw[]) >>
 qexists_tac ‘b0’ >> arw[] >>
 drule cardeq_SYM >> arw[])
(form_goal
 “!α:mem(ordinal(A)) B b:mem(Pow(B)). beth(ordSUC(α),b) <=>
 ?b0:mem(Pow(B)). beth(α,b0) & cardeq(b,POW(b0))”));

val IMAGE_bethf_preds_pbeths = 
prove_store("IMAGE_bethf_preds_pbeths",
e0
(rw[GSYM IN_EXT_iff,IN_BIGUNION,IMAGE_def,Snds_def,
    pbeths_def,preds_def] >>
 fconv_tac(redepth_fconv no_conv exists_cross_fconv) >>
 rw[Pair_def',App_p2_Pair] >>  
 rw[IN_EXT_iff]  >>
 rw[predsf_def,beth_def] >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexistsl_tac [‘a’,‘x’] >> rfs[]) >>
 qexists_tac ‘App(bethf(A, B), a')’ >>
 arw[] >> qexists_tac ‘a'’ >> arw[])
(form_goal “BIGUNION(IMAGE(bethf(A, B), preds(α))) = 
            Snds(pbeths(α,B))”));

(*
val IN_IMAGE_bethf = prove_store("IN_IMAGE_bethf",
e0
(rw[IMAGE_def,IN_BIGUNION] >> dimp_tac >> rpt strip_tac >> arw[](*2*)
 >-- (qexists_tac ‘a’ >> fs[beth_def] >> rfs[]) >>
 qexists_tac ‘BIGUNION(IMAGE(bethf(A, B), ords))’ >>
 fs[beth_def,IN_BIGUNION,IMAGE_def] >> strip_tac (* 2 *)
 >-- qexists_tac ‘ord’ >> arw[] >>
     )
(form_goal “IN(s, BIGUNION(IMAGE(bethf(A, B), ords))) <=> 
 ?ord. IN(ord,ords) & beth(ord,s) ”)); 
*)


val beth_limit = prove_store("beth_limit",
e0
(rpt strip_tac >> rw[GSYM IMAGE_bethf_preds_pbeths] >>
 assume_tac (bethf_def |> conjE2 |> conjE2) >>
 first_x_assum (qspecl_then [‘α’] assume_tac) >>
 rfs[] >>
 arw[beth_def,App_App_o,sf0_ex,App_p2_Pair] >>
 rw[lf0_ex] >> dimp_tac >> strip_tac >> arw[]
 >-- (rpt strip_tac >>
     fs[IMAGE_def,GSYM beth_def] >>
     first_x_assum  
     (qspecl_then [‘App(bethf(A,B),p)’] assume_tac) >>
     qby_tac ‘~(App(bethf(A, B), p) = Empty(Pow(B)))’ 
     >-- (first_x_assum irule >>
         qexists_tac ‘p’ >> arw[preds_def,predsf_def]) >>
     fs[GSYM IN_NONEMPTY] >>
     qexists_tac ‘a'’ >> arw[beth_def]) >>
rw[GSYM IN_NONEMPTY] >> rpt strip_tac (*2 *)
 >-- (first_x_assum drule >>
     qexists_tac ‘App(bethf(A,B),zord(A))’ >>
     rw[IMAGE_def] >>
     qexists_tac ‘zord(A)’>> arw[predsf_def,preds_def]) >>
 pop_assum mp_tac >>
 rw[IMAGE_def,preds_def,predsf_def]  >>
 rpt strip_tac>> 
 first_x_assum drule >> 
 arw[])
(form_goal
 “!α:mem(ordinal(A)).
 ordlt(zord(A),α) & islimit(α) ==>
 !B b:mem(Pow(B)).
 beth(α,b) <=> 
 (!p. ordlt(p,α) ==> 
  ?pbeth:mem(Pow(B)).beth(p,pbeth)) &
 issup(b,Snds(pbeths(α,B)))”));







(*if contain a set, then for any set not greater than it, contain a copy of such a set*)

val IMAGE_INJ_cardeq = 
prove_store("IMAGE_INJ_cardeq",
e0
cheat
(form_goal
 “!A s1 B s2 f:A->B.INJ(f,s1,s2) ==>
  !s01. SS(s01,s1) ==> cardeq(s01,IMAGE(f,s01))”));

val o_INJ_INJ = prove_store("o_INJ_INJ",
e0
cheat
(form_goal
 “!A s1 B s2 f:A->B. INJ(f,s1,s2) ==>
  !C s3 g:B->C.INJ(g,s2,s3) ==>
  INJ(g o f,s1,s3)”));

val Sg_INJ = prove_store("Sg_INJ",
e0
(cheat)
(form_goal “!B s.INJ(Sg(B), s, POW(s))”));


val INJ_SS = prove_store("INJ_SS",
e0
(cheat)
(form_goal “!A s1 B s2 f:A->B. INJ(f,s1,s2) ==> 
 !s2'. SS(s2,s2') ==> INJ(f,s1,s2') ”));


val ofcards_def = 
IN_def_P |> qspecl [‘Pow(A)’] 
         |> fVar_sInst_th “P(s:mem(Pow(A)))”
            “?c:mem(Pow(C)).IN(c,cs) &
             cardeq(c,s:mem(Pow(A)))” 
         |> uex2ex_rule 
         |> qSKOLEM "ofcards" [‘cs’,‘A’]


(*
val cardeq_card_bound = prove_store("cardeq_card_bound",
e0
cheat
(form_goal
 “!A B cs.
  (!c.IN(c,cs) ==>
   (?s1:mem(Pow(A)).cardeq(c,s1)) &
   (?s2:mem(Pow(B)).cardeq(c,s2))) ==>
 cardeq(BIGUNION(ofcards(cs,A)),BIGUNION(ofcards(cs,B)))”));
*)

 


val issup_cardleq = prove_store("issup_cardleq",
e0
()
(form_goal
 “!A ss:mem(Pow(Pow(A))) B sup1:mem(Pow(B)).
 issup(sup1,ss) ==>”));

val issup_cardeq = prove_store("issup_cardeq",
e0
(rpt strip_tac >> fs[issup_def,ssup_def] >>
 dimp_tac >> rpt strip_tac (* 3 *)
 >-- last_x_assum irule)
(form_goal
 “!A ss:mem(Pow(Pow(A))) B sup1:mem(Pow(B)).
 issup(sup1,ss) ==>
 !C sup2:mem(Pow(C)).
 issup(sup2,ss) <=> cardeq(sup1,sup2)”));

val issup_elements_same_card = 
prove_store("issup_elements_same_card",
e0
cheat
(form_goal
 “!A ss1:mem(Pow(Pow(A))) B ss2:mem(Pow(Pow(B))).
  (!s1. IN(s1,ss1) ==> ?s2.IN(s2,ss2) & cardeq(s1,s2)) &
  (!s2. IN(s2,ss2) ==> ?s1.IN(s1,ss1) & cardeq(s2,s1)) ==>
  !C sup:mem(Pow(C)). issup(sup,ss1) <=> issup(sup,ss2)”));

val IN_Snds_pbeths = prove_store("IN_Snds_pbeths",
e0
(rw[pbeths_def,Snds_def,IMAGE_def] >>
 rpt strip_tac >> 
 fconv_tac (redepth_fconv no_conv exists_cross_fconv) >>
 rw[Pair_def',App_p2_Pair] >> 
 dimp_tac >> rpt strip_tac >> arw[] (* 2 *)
 >-- (qexists_tac ‘a'’ >> arw[]) >>
 qexistsl_tac [‘p’,‘pbeth’] >> arw[] )
(form_goal
 “!A α:mem(ordinal(A)) B pbeth.IN(pbeth, Snds(pbeths(α, B))) <=> 
  ?p. ordlt(p,α) & beth(p,pbeth) ”));

val issup_INJ = prove_store("issup_INJ",
e0
(rw[issup_def,ssup_def] >> rpt strip_tac >>
 last_x_assum drule >>
 fs[cardleq_def] >> qexists_tac ‘f’ >> arw[])
(form_goal “!A ss B sup. issup(sup,ss) ==>
 !s. IN(s,ss) ==>?f:A->B. INJ(f,s,sup)”))

val beth_cardeq = prove_store("beth_cardeq",
e0
(ind_with simple_ord_induction >> 
 rpt strip_tac (* 3 *)
 >-- (fs[beth_zord] >>
     dimp_tac >> strip_tac (* 2 *)
     >-- (drule cardeq_SYM >>
         rev_drule cardeq_TRANS >>
         first_x_assum drule >> arw[]) >>
     drule cardeq_SYM >>
     drule cardeq_TRANS >>
     first_x_assum irule >> arw[]) 
(* >-- card eq implies card pow eq*)
  >--   (fs[beth_ordSUC] >>
     dimp_tac >> rpt strip_tac (* 2 *)
     >-- (first_x_assum rev_drule >>
         fs[] >> 
         qsspecl_then [‘b0’,‘b0'’] assume_tac cardeq_POW >>
         first_x_assum drule >>
         qsspecl_then [‘beth1’,‘POW(b0)’] assume_tac
         cardeq_TRANS >>
         rfs[] >>
         first_x_assum drule >>
         drule cardeq_TRANS >>
         first_x_assum irule >>
         irule cardeq_SYM >> arw[]) >>
     first_x_assum drule >> arw[] >>
     qsuff_tac
     ‘?b0':mem(Pow(B2)). cardeq(b0,b0')’ 
     >-- (strip_tac >> qexists_tac ‘b0'’ >> arw[] >>
         drule cardeq_POW >>
         rev_drule cardeq_TRANS >>
         first_x_assum drule >>
         irule cardeq_TRANS >>
         qexistsl_tac [‘B1’,‘beth1’] >> arw[] >>
         irule cardeq_SYM >> arw[]) >>
     qby_tac ‘cardeq(POW(b0),beth2)’ 
     >-- (irule cardeq_TRANS >>
         qexistsl_tac [‘B1’,‘beth1’] >> arw[] >>
         irule cardeq_SYM >> arw[]) >>
     qby_tac
      ‘?f:Pow(B1)->B2.INJ(f,POW(b0),beth2)’ 
     >-- (fs[cardeq_def,BIJ_def] >> 
         qexistsl_tac [‘f'''’] >> arw[]) >>
     pop_assum strip_assume_tac >> 
     qexists_tac ‘IMAGE(f o Sg(B1),b0)’ >>
     irule IMAGE_INJ_cardeq >>
     qexistsl_tac [‘b0’,‘Whole(B2)’] >>
     rw[SS_Refl] >> 
     irule o_INJ_INJ >>
     qexists_tac ‘POW(b0)’ >> 
     rw[Sg_INJ] >>
     drule INJ_SS >>
     first_x_assum irule >> rw[SS_def,Whole_def]) >>
 dimp_tac >> strip_tac >>
 qsspecl_then [‘α’] assume_tac beth_limit >>
 rfs[islimit_def] >> fs[] (* 2 *)
 >-- (drule issup_cardeq >>
     irule cardeq_SYM >>
     first_x_assum (irule o iffLR) >>
     qsspecl_then 
     [‘Snds(pbeths(α, B1))’,‘Snds(pbeths(α, B2))’]
     assume_tac issup_elements_same_card >>
     qsuff_tac
     ‘issup(beth1, Snds(pbeths(α, B1))) 
      <=> issup(beth1, Snds(pbeths(α, B2)))’ 
     >-- rfs[] >>
     first_x_assum irule >> strip_tac (* 2 *)
     >-- (rpt strip_tac >>
         qby_tac
         ‘?p. ordlt(p,α) & beth(p,s1)’ 
         >-- (fs[IN_Snds_pbeths] >> qexists_tac ‘p’ >>
             arw[]) >>
         pop_assum strip_assume_tac >>
         first_x_assum drule >>
         pop_assum strip_assume_tac >>
         qexists_tac ‘pbeth’ >> 
         rw[IN_Snds_pbeths] >> strip_tac (* 2 *)
         >-- (qexists_tac ‘p’ >> arw[]) >>
         last_x_assum drule >>
         first_x_assum rev_drule >>
         first_x_assum (irule o iffLR) >> arw[]) >>
     rpt strip_tac >>
     qby_tac
     ‘?p. ordlt(p,α) & beth(p,s2)’ 
     >-- (fs[IN_Snds_pbeths] >>
         qexists_tac ‘p’ >> arw[]) >>
     pop_assum strip_assume_tac >>
     qsuff_tac
     ‘?s1:mem(Pow(B1)). beth(p,s1)’ 
     >-- (strip_tac >>
         qexists_tac ‘s1’ >> rw[IN_Snds_pbeths] >>
         strip_tac (* 2 *)
         >-- (qexists_tac ‘p’ >> arw[]) >>
         last_x_assum drule >>
         first_x_assum drule >>
         irule cardeq_SYM >>
         first_x_assum (irule o iffLR) >> arw[]) >>
     first_x_assum irule >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- (first_x_assum drule >>
     pop_assum strip_assume_tac >>
     first_x_assum drule >>
     first_x_assum drule >> arw[] >>
     drule issup_INJ >>
     qby_tac
     ‘?f:B1->B1. INJ(f,pbeth,beth1)’ 
     >-- (first_x_assum irule >> 
          pop_assum (K all_tac) >>
          rw[IN_Snds_pbeths] >>
          qexists_tac ‘p’ >> arw[]) >>
     pop_assum strip_assume_tac >>
     qby_tac ‘?g:B1->B2.INJ(g,beth1,beth2)’ 
     >-- (fs[cardeq_def,BIJ_def] >>
         qexists_tac ‘f'’ >> arw[]) >>
     pop_assum strip_assume_tac >>
     qexists_tac ‘IMAGE(g o f,pbeth)’ >>
     irule IMAGE_INJ_cardeq >>
     qexistsl_tac [‘pbeth’,‘beth2’] >>
     rw[SS_Refl] >> irule o_INJ_INJ >> 
     qexistsl_tac [‘beth1’] >> arw[]) >>
 qsspecl_then [‘Snds(pbeths(α, B1))’,‘Snds(pbeths(α, B2))’]
 assume_tac issup_elements_same_card >>
 qsuff_tac
 ‘issup(beth2, Snds(pbeths(α, B1))) <=> 
  issup(beth2, Snds(pbeths(α, B2)))’
 >-- (strip_tac >>
     first_x_assum (irule o iffLR) >>
     drule issup_cardeq >>
     arw[]) >>
 first_x_assum irule >>
 rpt strip_tac (* 2 *)
 >-- (drule issup_INJ >>
     first_x_assum drule >>
     pop_assum strip_assume_tac >> 
     qby_tac ‘?g:B1->B2.INJ(g,beth1,beth2)’ 
     >-- (fs[cardeq_def,BIJ_def] >>
         qexists_tac ‘f'’ >> arw[]) >>
     pop_assum strip_assume_tac >> 
     drule $ iffLR IN_Snds_pbeths >>
     pop_assum strip_assume_tac >>
     qexists_tac ‘IMAGE(g o f,s1)’ >>
     rw[IN_Snds_pbeths] >>
     qby_tac ‘cardeq(s1, IMAGE(g o f, s1))’ 
     >-- (irule IMAGE_INJ_cardeq >>
         qexistsl_tac [‘s1’,‘beth2’] >>
         rw[SS_Refl] >>
         irule o_INJ_INJ >> qexists_tac ‘beth1’ >> 
         arw[]) >>
     arw[] >>
     qexists_tac ‘p’ >> arw[] >>
     last_x_assum drule >>
     first_x_assum drule >> arw[]) >>
 fs[IN_Snds_pbeths] >>
 first_x_assum drule >> 
 pop_assum strip_assume_tac >>
 qexists_tac ‘pbeth’ >> 
 qby_tac ‘cardeq(s2, pbeth)’ 
 >-- (last_x_assum drule >>
     first_x_assum rev_drule >>
     fs[]) >>
 arw[] >>
 qexists_tac ‘p’ >> arw[])
(form_goal
 “!α:mem(ordinal(A)).
  !B1 beth1:mem(Pow(B1)).
   beth(α,beth1) ==>
   !B2 beth2:mem(Pow(B2)).(beth(α,beth2) <=>
   cardeq(beth1,beth2))”));

val Beth_def = 
qdefine_psym("Beth",[‘α:mem(ordinal(A))’,‘BN’])
‘?B beth:mem(Pow(B)). beth(α,beth) & cardeq(beth,Whole(BN))’



val AX5 = store_ax("AX5",
“!A.?B p:B->A Y M:B~>Y.  
 (!b.P(App(p,b),m2s(rsi(M,b)))) & 
 !a:mem(A) X. P(a,X) ==> ?b. App(p,b) = a”)


val cardeq_Whole_m2s = prove_store("cardeq_Whole_m2s",
e0
cheat
(form_goal “!A s.cardeq(Whole(m2s(s)),s:mem(Pow(A)))”));

val cardeq_TRANS = prove_store("cardeq_TRANS",
e0
cheat
(form_goal “!A s1:mem(Pow(A)) B s2:mem(Pow(B)).
 cardeq(s1,s2) ==>
 !C s3:mem(Pow(C)).cardeq(s2,s3) ==>
 cardeq(s1,s3)”));


val cardeq_REFL = prove_store("cardeq_REFL",
e0
cheat
(form_goal “!A s:mem(Pow(A)). cardeq(s,s)”));




val IMAGE_Inj_cardeq = prove_store("IMAGE_Inj_cardeq",
e0
cheat
(form_goal “!A B f:A->B. Inj(f) ==>
 !s:mem(Pow(A)). cardeq(IMAGE(f,s),s)”));

val cardeq_POW = prove_store("cardeq_POW",
e0
cheat
(form_goal “!A s1:mem(Pow(A)) B s2:mem(Pow(B)).
 cardeq(s1,s2) ==> cardeq(POW(s1),POW(s2))”));

(*
val issup_ex = prove_store("issup_ex",
e0
()
(form_goal
 “”));
*)

val beth_ex = prove_store("beth_ex",
e0
(strip_tac >>
 ind_with simple_ord_induction >>
 rpt strip_tac (* 3 *)
 >-- (qexistsl_tac [‘N’] >>
     rw[Beth_def] >> qexistsl_tac [‘N’,‘Whole(N)’] >>
     rw[cardeq_REFL] >>
     rw[beth_zord,cardeq_REFL])
 >-- (*inject b into Pow(Pow(B))*)
     (fs[Beth_def,beth_ordSUC] >> 
     qexistsl_tac [‘m2s(POW(beth))’,‘Pow(B)’,‘POW(beth)’] >>
     strip_tac >--
     (qexistsl_tac [‘IMAGE(Sg(B),beth)’] >> 
     rw[cardeq_REFL] >>
     qspecl_then [‘B’] assume_tac Sg_Inj >>
     drule IMAGE_Inj_cardeq >> 
     drule beth_cardeq >> arw[] >>
     strip_tac (* 2 *)
     >-- (irule cardeq_SYM >> arw[]) >>
     irule cardeq_POW >> irule cardeq_SYM >> arw[]) >>
     irule cardeq_SYM >> rw[cardeq_Whole_m2s]) >>
 strip_assume_tac
 (AX5 |> qspecl [‘ordinal(A)’] 
 |> fVar_sInst_th “P(α:mem(ordinal(A)),X)”
     “Beth(α:mem(ordinal(A)),X)”) >> 
 rw[Beth_def] >>
 qsspecl_then [‘α’] assume_tac beth_limit >>
 rfs[islimit_def] >>
 qby_tac
 ‘!p. ordlt(p,α) ==>
      ?pbeth:mem(Pow(Y)). beth(p,pbeth)’
 >-- (rpt strip_tac >>
     first_x_assum drule >>
     pop_assum strip_assume_tac >>
     first_x_assum drule >> 
     pop_assum strip_assume_tac >>
     first_x_assum (qspecl_then [‘b’] assume_tac) >>
     qexists_tac ‘rsi(M,b)’ >> 
     fs[Beth_def] >>
     qsspecl_then [‘rsi(M,b)’] assume_tac cardeq_Whole_m2s>>
     drule beth_cardeq >>
     rfs[] >>
     irule cardeq_TRANS >>
     qexistsl_tac 
     [‘m2s(rsi(M, b))’,‘Whole(m2s(rsi(M, b)))’] >> arw[]) >>
 qsuff_tac
 ‘?sup.issup(sup:mem(Pow(Y)),Snds(pbeths(α, Y)))’
 >-- (strip_tac >>
     qexistsl_tac [‘m2s(sup)’,‘Y’,‘sup’] >>
     arw[] >>
     irule cardeq_SYM >> rw[cardeq_Whole_m2s]) >>
 


 qexistsl_tac
 [‘m2s(BIGUNION(Snds(pbeths(α, Y))))’,
  ‘Y’,‘BIGUNION(Snds(pbeths(α, Y)))’] >>
 arw[cardeq_REFL,cardeq_Whole_m2s] >> 
 irule cardeq_SYM >> rw[cardeq_Whole_m2s])
(form_goal  “!A α:mem(ordinal(A)). ?BN. Beth(α,BN)”));

(*
val beth_ex = prove_store("beth_ex",
e0
(strip_tac >>
 ind_with simple_ord_induction >>
 rpt strip_tac (* 3 *)
 >-- (qexistsl_tac [‘N’] >>
     rw[Beth_def] >> qexistsl_tac [‘N’,‘Whole(N)’] >>
     rw[cardeq_REFL] >>
     rw[beth_zord,cardeq_REFL])
 >-- (*inject b into Pow(Pow(B))*)
     (fs[Beth_def,beth_ordSUC] >> 
     qexistsl_tac [‘m2s(POW(beth))’,‘Pow(B)’,‘POW(beth)’] >>
     strip_tac >--
     (qexistsl_tac [‘IMAGE(Sg(B),beth)’] >> 
     rw[cardeq_REFL] >>
     qspecl_then [‘B’] assume_tac Sg_Inj >>
     drule IMAGE_Inj_cardeq >> 
     drule beth_cardeq >> arw[] >>
     strip_tac (* 2 *)
     >-- (irule cardeq_SYM >> arw[]) >>
     irule cardeq_POW >> irule cardeq_SYM >> arw[]) >>
     irule cardeq_SYM >> rw[cardeq_Whole_m2s]) >>
 strip_assume_tac
 (AX5 |> qspecl [‘ordinal(A)’] 
 |> fVar_sInst_th “P(α:mem(ordinal(A)),X)”
     “Beth(α:mem(ordinal(A)),X)”) >> 
 rw[Beth_def] >>
 qsspecl_then [‘α’] assume_tac beth_limit >>
 rfs[islimit_def] >>
 qby_tac
 ‘!p. ordlt(p,α) ==>
      ?pbeth:mem(Pow(Y)). beth(p,pbeth)’
 >-- (rpt strip_tac >>
     first_x_assum drule >>
     pop_assum strip_assume_tac >>
     first_x_assum drule >> 
     pop_assum strip_assume_tac >>
     first_x_assum (qspecl_then [‘b’] assume_tac) >>
     qexists_tac ‘rsi(M,b)’ >> 
     fs[Beth_def] >>
     qsspecl_then [‘rsi(M,b)’] assume_tac cardeq_Whole_m2s>>
     drule beth_cardeq >>
     rfs[] >>
     irule cardeq_TRANS >>
     qexistsl_tac 
     [‘m2s(rsi(M, b))’,‘Whole(m2s(rsi(M, b)))’] >> arw[]) >>
 qexistsl_tac
 [‘m2s(BIGUNION(Snds(pbeths(α, Y))))’,
  ‘Y’,‘BIGUNION(Snds(pbeths(α, Y)))’] >>
 arw[cardeq_REFL,cardeq_Whole_m2s] >> 
 irule cardeq_SYM >> rw[cardeq_Whole_m2s])
(form_goal  “!A α:mem(ordinal(A)). ?BN. Beth(α,BN)”));
*)

(*
a function B-> ordinal(A) is a 0-beth family if 
the preimage of 0 has cardinality N


*)


(*fibre is preimage of a *)
val FIB_def = qdefine_fsym("FIB",[‘f:A->B’,‘b:mem(B)’])
‘PREIM(f,Sing(b))’


(*fibre is preimage of a *)
val mFIB_def = qdefine_fsym("mFIB",[‘f:mem(Exp(A,B))’,‘b:mem(B)’])
‘PREIM(tof(f),Sing(b))’


val bdefz_ex = 
IN_def_P |> qspecl [‘Exp(B,ordinal(A))’]  
         |> fVar_sInst_th “P(f:mem(Exp(B,ordinal(A))))”
            “cardeq(mFIB(f:mem(Exp(B,ordinal(A))),
                          zord(A)),Whole(N))”
         |> uex2ex_rule 
         |> qSKOLEM "bdefz" [‘A’,‘B’]

val bdefs_ex = proved_th $
e0
cheat
(form_goal 
 “?sf:ordinal(A) * Pow(Exp(B, ordinal(A))) ->
      Pow(Exp(B, ordinal(A))).
 !α fams0 fam. 
  IN(fam,App(sf,Pair(α,fams0))) <=> 
  ?fam0. IN(fam0,fams0) &
         (!p. ordle(p,α) ==> 
              cardeq(mFIB(fam,p),mFIB(fam0,p))) &
         cardeq(mFIB(fam,ordSUC(α)),POW(mFIB(fam,α)))”)
|> qSKOLEM "bdefs" [‘A’,‘B’]


val bdefl_ex = proved_th $
e0
cheat
(form_goal 
 “?lf:ordinal(A) * Pow(Pow(Exp(B, ordinal(A))) ->
      Pow(Exp(B, ordinal(A))).
 !α famss0 fam. 
  IN(fam,App(sf,Pair(α,famss0))) <=> 
  ?fam0. IN(fam0,BIGUNION(famss0)) &
         (!p. ordlt(p,α) ==> 
              cardeq(mFIB(fam,p),mFIB(fam0,p))) &
         cardeq(mFIB(fam,ordSUC(α)),POW(mFIB(fam,α)))”)
|> qSKOLEM "bdefs" [‘A’,‘B’]


val bethf_def = 
ord_RECURSION  
|> qspecl [‘A’,‘Pow(Exp(B,ordinal(A)))’,‘bdefz(A,B)’]  
|> qspecl [‘bdefs(A,B)’]
|> qspecl [‘lf0(B) o p2(ordinal(A),Pow(Pow(Pow(B))))’]
|> qSKOLEM "bethf" [‘A’,‘B’]
