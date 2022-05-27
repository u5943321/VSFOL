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

val Abso_def = qdefine_fsym("Abso",[‘w:mem(WO(A))’])
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
                      GSYM Abso_def]

val ordlt_def = 
qdefine_psym("ordlt",[‘ord1:mem(ordinal(A))’,‘ord2:mem(ordinal(A))’]) ‘App(ordltf(A), Pair(ord1, ord2)) = true’
|> gen_all

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




(*
val wobound_def = Define`
  wobound x w = wellorder_ABS (rrestrict (wellorder_REP w) (iseg w x))
`;*)




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
