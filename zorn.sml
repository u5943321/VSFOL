(*
val partial_order_def = Define `
  partial_order r s <=>
       domain r SUBSET s /\ range r SUBSET s /\
       transitive r /\ reflexive r s /\ antisym r`;


val domain_def = Define `
  domain r = {x | ?y. (x, y) IN r}`;
val _ = ot "domain"

val range_def = Define `range r = {y | ?x. (x, y) IN r}`;
chain

 upper_bounds 

 maximal_elements 
*)

val domain_def = 
IN_def_P |> qspecl [‘A’]
         |> fVar_sInst_th “P(x:mem(A))”
            “?y. IN(Pair(x,y),r:mem(Pow(A * A)))”
         |> qsimple_uex_spec "domain" [‘r’]
         |> gen_all 


val range_def = 
IN_def_P |> qspecl [‘A’]
         |> fVar_sInst_th “P(y:mem(A))”
            “?x. IN(Pair(x,y),r:mem(Pow(A * A)))”
         |> qsimple_uex_spec "range" [‘r’]
         |> gen_all


val maximal_elements_def= 
IN_def_P 
|> qspecl [‘A’]
|> fVar_sInst_th “P(x:mem(A))”
   “IN(x,xs) & 
    (!x'. IN(x',xs) & IN(Pair(x,x'),r) ==>
    x = x':mem(A))”
|> qsimple_uex_spec "maximal_elements" [‘xs’,‘r’] 
|> gen_all


val minimal_elements_def= 
IN_def_P 
|> qspecl [‘A’]
|> fVar_sInst_th “P(x:mem(A))”
   “IN(x,xs) & 
    (!x'. IN(x',xs) & IN(Pair(x',x),r) ==>
    x = x':mem(A))”
|> qsimple_uex_spec "minimal_elements" [‘xs’,‘r’] 
|> gen_all


val upper_bounds_def = 
IN_def_P 
|> qspecl [‘A’]
|> fVar_sInst_th “P(x:mem(A))”
   “IN(x,range(r)) & 
    (!y. IN(y,s) ==>
       IN(Pair(y,x),r:mem(Pow(A * A))))”
|> qsimple_uex_spec "upper_bounds" [‘s’,‘r’] 
|> gen_all

val chain0_def = 
qdefine_psym("chain0",[‘s:mem(Pow(A))’,‘r:mem(Pow(A * A))’])
‘!x y. IN(x,s) & IN(y,s) ==> 
       IN(Pair(x,y),r) | IN(Pair(y,x),r)’
|> gen_all


val reflexive_def = qdefine_psym("reflexive",
[‘r:mem(Pow(A * A))’,‘s:mem(Pow(A))’])
‘!x. IN(x,s) ==> IN(Pair(x,x),r)’ |> gen_all

val transitive_def = qdefine_psym("transitive",
[‘r:mem(Pow(A*A))’])
‘!x y z. IN(Pair(x,y),r) & IN(Pair(y,z),r)
          ==> IN(Pair(x,z),r)’
|> gen_all

val antisym_def = qdefine_psym("antisym",
[‘r:mem(Pow(A*A))’])
‘!x y.IN(Pair(x,y),r) & IN(Pair(y,x),r) ==> x = y’
|> gen_all

val partial_order_def = 
qdefine_psym("partial_order",
[‘r:mem(Pow(A*A))’,‘s:mem(Pow(A))’])
‘SS(domain(r),s) & SS(range(r),s) &
 transitive(r) & reflexive(r,s) & antisym(r)’
|> gen_all

val ischoice_def = 
qdefine_psym("ischoice",[‘f:Pow(A)->A’,‘s:mem(Pow(Pow(A)))’])
‘~IN(Empty(A),s) &
(!s0. IN(s0,s) ==> IN(App(f,s0),s0))’

val AC = store_ax
("AC",
 “!A B R:A~>B. 
  (!a. ?b.Holds(R,a,b)) ==>
  ?f:A->B. 
  !a.Holds(R,a,App(f,a))”)


val ischoice_ex = prove_store("ischoice_ex",
e0
(rpt strip_tac >> 
 rw[ischoice_def] >> fs[NOT_EMPTY] >>
 strip_assume_tac
 (AX1_ex |> qspecl [‘Pow(A)’,‘A’] 
     |> fVar_sInst_th “P(s0:mem(Pow(A)),a0:mem(A))”
        “(IN(s0,s) & IN(a0,s0)) |
         ~IN(s0,s) & a0 = a:mem(A)”) >>
 qby_tac
 ‘!s0. IN(s0,s) ==> ~(s0 = Empty(A))’
 >-- (rpt strip_tac >> ccontra_tac >> fs[]) >>
 qby_tac
 ‘!s0. ?a0. Holds(R,s0,a0)’
 >-- (strip_tac >>
     arw[] >> qcases ‘IN(s0,s)’ >> arw[] (* 2 *)
     >-- (first_x_assum drule >>
         fs[GSYM IN_NONEMPTY] >>
         qexists_tac ‘a'’ >> arw[]) >>
     qexists_tac ‘a’ >> rw[]) >>
 drule AC >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘s0’] assume_tac) >>
 rfs[])
(form_goal
 “!A s. ~EMPTY(A) & ~IN(Empty(A), s) ==> ?f:Pow(A) -> A.ischoice(f,s)”));

(*
val fchains_def = 
IN_def_P
|> qspecl [‘Pow(A)’] 
|> fVar_sInst_th “P(k:mem(Pow(A)))”
   “chain0(k,r) & ~(k = Empty(A)) &
    !C. chain0(C,r) & SS(C,k) &
    ~(Inter(Diff(upper_bounds(C,r),C),k) = 
      Empty(A)) ==>
    !f. 
    (!s. ~(s = Empty(A)) ==> IN(App(f,s),s)) ==>
    IN(App(f,Diff(upper_bounds(C,r),C)),
       minimal_elements
       (Inter(Diff(upper_bounds(C,r),C),k),r)) ”
|> qsimple_uex_spec "fchains" [‘r’]

*)


val fchains_def = 
IN_def_P
|> qspecl [‘Pow(A)’] 
|> fVar_sInst_th “P(k:mem(Pow(A)))”
   “chain0(k,r) & ~(k = Empty(A)) &
    !C. chain0(C,r) & SS(C,k) &
    ~(Inter(Diff(upper_bounds(C,r),C),k) = 
      Empty(A)) ==>
    IN(App(f,Diff(upper_bounds(C,r),C)),
       minimal_elements
       (Inter(Diff(upper_bounds(C,r),C),k),r)) ”
|> qsimple_uex_spec "fchains" [‘r’,‘f’]

val hatclass_def = 
IN_def_P |> qspecl [‘Pow(A)’] 
         |> fVar_sInst_th “P(hc:mem(Pow(A)))”
            “?C:mem(Pow(A)). 
             hc = Diff(upper_bounds(C,r),C)”
         |> qsimple_uex_spec "hatclass" [‘r’]
         |> gen_all

val lemma1 = prove_store("lemma1",
e0
(rw[chain0_def,domain_def,range_def] >>
 rpt strip_tac >> 
 qexists_tac ‘x’ >>
 first_x_assum (qspecl_then [‘x’,‘x’] assume_tac) >>
 rfs[])
(form_goal
 “!x:mem(A) s r. 
 chain0(s,r) & IN(x,s) ==>
 IN(x,domain(r)) & IN(x,range(r))”));

val lemma2 = prove_store("lemma2",
e0
(rpt strip_tac >>
 qby_tac 
 ‘IN(x, range(r)) & IN(x', range(r))’ 
 >-- (strip_tac (* 2 *)
     >-- (qsuff_tac
         ‘IN(x,domain(r)) & IN(x,range(r))’
         >-- (strip_tac >> arw[]) >>
         irule lemma1 >> qexists_tac ‘k1’ >>
         fs[fchains_def]) >>
     qsuff_tac
     ‘IN(x',domain(r)) & IN(x',range(r))’
     >-- (strip_tac >> arw[]) >>
     irule lemma1 >> qexists_tac ‘k2’ >>
     fs[fchains_def]) >>
 x_choose_then "C" assume_tac
 (IN_def_P_ex 
 |> qspecl [‘A’]
 |> fVar_sInst_th “P(x:mem(A))”
    “IN(x:mem(A),k1) & IN(x,k2) &
     IN(Pair(x,x':mem(A)),r)”
 |> GSYM) >>
 qby_tac
 ‘IN(x',Diff(upper_bounds(C,r),C))’
 >-- (arw[upper_bounds_def,Diff_def] >>
     rpt strip_tac) >>
 qby_tac
 ‘chain0(C,r) & SS(C,k2) & SS(C,k1)’
 >-- (arw[chain0_def,SS_def] >> rpt strip_tac >>
     fs[fchains_def,chain0_def] >>
     first_x_assum irule >> arw[]) >>
 qby_tac
 ‘IN(App(f,Diff(upper_bounds(C,r),C)),
     minimal_elements
    (Inter(Diff(upper_bounds(C, r), C), k2),r))’
 >-- (fs[fchains_def] >> first_x_assum irule >>
     arw[] >> rw[GSYM IN_NONEMPTY,IN_Inter] >>
     qexists_tac ‘x'’ >> arw[]) >>
 qby_tac
 ‘IN(App(f,Diff(upper_bounds(C, r), C)),k2)’ 
 >-- fs[minimal_elements_def,IN_Inter] >>
 qby_tac
  ‘IN(Pair
     (App(f,Diff(upper_bounds(C, r), C)),x'),
     r)’
 >-- (fs[fchains_def] >>
     qby_tac
     ‘IN(x',Inter(Diff(upper_bounds(C, r), C),k2))’
     >-- arw[IN_Inter] >> 
     qsuff_tac
     ‘IN(x',Inter(Diff(upper_bounds(C, r), C),k2)) &
      chain0(k2, r) & 
      IN(App(f, Diff(upper_bounds(C, r), C)),
              minimal_elements(Inter(Diff(upper_bounds(C, r), C), k2), r)) & IN(x', k2) & 
      IN(App(f, Diff(upper_bounds(C, r), C)), k2) ==>
      IN(Pair(App(f, Diff(upper_bounds(C, r), C)), x'), r)’
     >-- (strip_tac >> first_x_assum irule >> arw[]) >>
     pop_assum_list (map_every (K all_tac)) >>
     rpt strip_tac >>
     fs[minimal_elements_def,chain0_def] >>
     first_assum (qspecl_then [‘x'’,‘App(f, Diff(upper_bounds(C, r), C))’] assume_tac) >>
     qby_tac
     ‘IN(Pair(x', App(f, Diff(upper_bounds(C, r), C))), r) | IN(Pair(App(f, Diff(upper_bounds(C, r), C)), x'), r)’ >-- (first_assum irule >> arw[]) >>
     pop_assum strip_assume_tac >>
     qby_tac
     ‘App(f, Diff(upper_bounds(C, r), C)) = x'’
     >-- (first_assum irule >> arw[]) >>
     fs[]) >>
 qby_tac
 ‘Inter(Diff(upper_bounds(C, r), C), k1) = Empty(A)’
 >-- (rw[GSYM IN_EXT_iff,Empty_def] >>
     strip_tac >> ccontra_tac >>
     qby_tac
     ‘IN(App(f,Diff(upper_bounds(C, r), C)),k1)’
     >-- (rev_drule $ iffLR fchains_def >>
         pop_assum strip_assume_tac >>
         qsuff_tac
         ‘IN(App(f, Diff(upper_bounds(C, r), C)),
                minimal_elements(Inter(Diff(upper_bounds(C, r), C), k1), r))’
         >-- (rw[minimal_elements_def,IN_Inter] >>
             rpt strip_tac) >>
         first_x_assum irule >> arw[] >>
         rw[GSYM IN_NONEMPTY] >>
         qexists_tac ‘x''’ >> arw[]) >>
     qby_tac
     ‘IN(App(f,Diff(upper_bounds(C, r), C)),C)’
     >-- arw[] >>
     drule $ iffLR ischoice_def >>
     fs[] >>
     qby_tac
     ‘IN(App(f, Diff(upper_bounds(C, r), C)), 
         Diff(upper_bounds(C, r), C))’
     >-- (first_x_assum irule >>
         rw[hatclass_def] >>
         qexists_tac ‘C’ >> arw[]) >>
     fs[Diff_def]) >>
 qby_tac
 ‘?x''. IN(x'',C) & IN(Pair(x,x''),r)’ 
 >-- (rev_drule $ iffLR fchains_def >>
     qsuff_tac
     ‘chain0(k1, r) & IN(x,k1) & IN(x, range(r)) & 
      SS(C,k1) & 
      Inter(Diff(upper_bounds(C, r), C), k1) = Empty(A) ==> ?x''. IN(x'',C) & IN(Pair(x,x''),r)’
     >-- (strip_tac >> first_x_assum irule >>
          arw[]) >>
     pop_assum_list (map_every (K all_tac)) >>
     rpt strip_tac >>
     fs[GSYM IN_EXT_iff,Empty_def,IN_Inter,
        Diff_def,upper_bounds_def] >>
     first_x_assum
     (qspecl_then [‘x’] strip_assume_tac) >>
     rfs[] >> 
     fs[SS_def,chain0_def] >>
     qcases ‘IN(x,C)’ >> fs[] (* 2 *)
     >-- (qexists_tac ‘x’ >> arw[] >>
         first_x_assum (qspecl_then [‘x’,‘x’] assume_tac) >> rfs[]) >>
      assume_tac
      (forall_exists_dual
     |> qspecl [‘A’] 
     |> fVar_sInst_th “P(y:mem(A))”
        “IN(y:mem(A),C) ==> 
         IN(Pair(y,x:mem(A)),r)”) >>
     fs[] >>
     fs[neg_imp_conj] >>
     qexists_tac ‘a’ >> arw[] >>
     first_x_assum drule >>
     first_x_assum
     (qspecl_then [‘x’,‘a’] assume_tac) >> rfs[]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘IN(Pair(x'',x'),r)’ 
 >-- rfs[] >>
 fs[transitive_def] >>
 first_x_assum irule  >>
 qexists_tac ‘x''’ >> arw[])
(form_goal
 “!f r:mem(Pow(A*A)) k1 k2 x x'.
  ischoice(f,hatclass(r)) & 
  transitive(r) & 
  IN(k1, fchains(r,f)) &
  IN(k2, fchains(r,f)) &
  IN(x, k1) &
  IN(x', k2) &
  ~IN(x', k1) 
  ==>
  IN(Pair(x,x'),r)”));

val lemma3 = prove_store("lemma3",
e0
(rpt strip_tac >>
 fs[antisym_def,SS_def] >> ccontra_tac >>
 fs[neg_or_distr] >>
 assume_tac
(forall_exists_dual
     |> qspecl [‘A’] 
     |> fVar_sInst_th “P(a:mem(A))”
        “IN(a:mem(A),k1) ==> 
         IN(a,k2)”) >>
 fs[] >> fs[neg_imp_conj] >>
 assume_tac
(forall_exists_dual
     |> qspecl [‘A’] 
     |> fVar_sInst_th “P(a:mem(A))”
        “IN(a:mem(A),k2) ==> 
         IN(a,k1)”) >>
 fs[] >> fs[neg_imp_conj] >>
 qby_tac
 ‘IN(Pair(a,a'),r)’
 >-- (irule lemma2 >> arw[] >>
     qexistsl_tac [‘f’,‘k1’,‘k2’] >> arw[]) >>
 qby_tac
 ‘IN(Pair(a',a),r)’
 >-- (irule lemma2 >> arw[] >>
     qexistsl_tac [‘f’,‘k2’,‘k1’] >> arw[]) >>
 qby_tac ‘a' = a’
 >-- (first_x_assum irule >> arw[]) >>
 fs[])
(form_goal
 “!f r:mem(Pow(A*A)) k1 k2.
  ischoice(f,hatclass(r)) & 
  transitive(r) & 
  antisym(r) & 
  IN(k1, fchains(r,f)) &
  IN(k2, fchains(r,f))
  ==>
  SS(k1,k2) | SS(k2,k1)”));

val lemma4 = prove_store("lemma4",
e0
((*rpt strip_tac (* 2 *)
 >-- rw[chain0_def] >> rpt strip_tac >>
    cheat >> *)
  )
(form_goal
 “!r:mem(Pow(A * A)) f. 
    antisym(r) & transitive(r) ==>
    chain0 (BIGUNION (fchains(r,f)), r) &
    (!x x' k.
      IN(Pair(x',x),r) &
      IN(x',BIGUNION (fchains(r,f))) &
      IN(x, BIGUNION (fchains (r,f))) &
      IN(k, fchains (r,f)) &
      IN(x, k)
      ==>
      IN(x', k))”));

val lemma9 = prove_store("lemma9",
e0
(cheat)
(form_goal
 “!r s. 
 SS(range(r),s) & ~(range(r) = Empty(A)) &
 antisym(r) & reflexive(r,s) & transitive(r) ==>
 SS(upper_bounds(BIGUNION(fchains(r)),r),
    maximal_elements(s,r))
  ”));


val zorns_lemma0 = prove_store("zorns_lemma0",
e0
(rpt strip_tac >>
 qsspecl_then [‘r’,‘s’] assume_tac lemma9 >>
 qsspecl_then [‘r’] assume_tac lemma4 >> 
 qby_tac
 ‘SS(upper_bounds(BIGUNION(fchains(r)), r),
              maximal_elements(s, r))’
 >-- (first_x_assum irule >>
     fs[partial_order_def,GSYM IN_NONEMPTY] >>
     qexists_tac ‘a’ >> 
     fs[reflexive_def,range_def] >>
     first_x_assum drule >> 
     qexists_tac ‘a’ >> arw[]) >> 
 qsuff_tac
 ‘?x.IN(x,upper_bounds(BIGUNION(fchains(r)), r))’
 >-- (strip_tac >>
     qexists_tac ‘x’ >> fs[SS_def] >>
     first_x_assum irule >> arw[]) >>
 rw[IN_NONEMPTY] >>
 first_x_assum irule >>
 rfs[partial_order_def])
(form_goal
 “!r s. ~(s = Empty(A)) & partial_order(r,s) &
  (!t. chain0(t,r) ==> 
    ~(upper_bounds(t,r) = Empty(A))) ==>
  ?x. IN(x,maximal_elements(s,r))”));

val Trans_transitive =
prove_store("Trans_transitive",
e0
(rw[Trans_def,transitive_def,r2m_def])
(form_goal “!A R. Trans(R:A~>A) <=> transitive(r2m(R))”));

val Refl_reflexive =
prove_store("Refl_reflexive",
e0
(rw[Refl_def,reflexive_def,r2m_def,Whole_def])
(form_goal “!A R. Refl(R:A~>A) <=>
 reflexive(r2m(R), Whole(A))”));


val Asym_antisym =
prove_store("Asym_antisym",
e0
(rw[Asym_def,antisym_def,r2m_def])
(form_goal “!A R. Asym(R:A~>A) <=>
 antisym(r2m(R))”));

val ptorder_partial_order = prove_store
("ptorder_partial_order",
e0
(rw[ptorder_def,partial_order_def,SS_Whole,
    Trans_transitive,Refl_reflexive,
    Asym_antisym] )
(form_goal
 “ptorder(R:A~>A) <=> partial_order(r2m(R), Whole(A))”));

val zorns_lemma = prove_store("zorns_lemma",
e0
(rpt strip_tac >>
 qsspecl_then [‘r2m(R)’,‘Whole(A)’] assume_tac
 zorns_lemma0 >>
 qsuff_tac
 ‘?x. IN(x,maximal_elements(Whole(A),r2m(R)))’
 >-- (rw[ismax_def,maximal_elements_def,Whole_def,
        r2m_def] >> rpt strip_tac >>
     qexists_tac ‘x’ >> rpt strip_tac >>
     flip_tac >> first_x_assum irule >> arw[]) >>
 first_x_assum irule >>
 fs[ptorder_partial_order,EMPTY_Empty_Whole] >> 
 last_x_assum (assume_tac o GSYM) >> arw[] >>
 rpt strip_tac >>
 rw[GSYM IN_NONEMPTY] >>
 qcases ‘t = Empty(A)’
 >-- (arw[] >> 
     fs[GSYM IN_NONEMPTY] >>
     qexists_tac ‘a’ >> 
     rw[upper_bounds_def,r2m_def,Empty_def,
        range_def] >>
     qexists_tac ‘a’ >>
     fs[partial_order_def,reflexive_def,
        Whole_def,r2m_def]) >>
 qsuff_tac
 ‘?ub:mem(A). ubound(t,R,ub)’
 >-- (rw[ubound_def,upper_bounds_def,range_def,
        r2m_def] >>
     rpt strip_tac >>
     qexists_tac ‘ub’ >> arw[] >> 
     fs[partial_order_def,reflexive_def,
       Whole_def,r2m_def] >>
     qexists_tac ‘ub’ >> arw[]) >>
 first_x_assum irule >> arw[] >>
 fs[chain0_def,chain_def,r2m_def])
(form_goal
“!A R:A~>A. ~EMPTY(A) & ptorder(R) ==> 
  (!c. chain(c,R) & ~(c = Empty(A)) ==> ?ub. ubound(c,R,ub)) ==>
  ?m. ismax(R,m)”));



“!r k1 k2 x x'.
  transitive r /\
  k1 IN fchains r /\
  k2 IN fchains r /\
  x IN k1 /\
  x' IN k2 /\
  x' NOTIN k1
  ==>
  (x,x') IN r”
qpat_x_assum
‘∀x y. x ∈ C ∧ y ∈ C ⇒ (x,y) ∈ r ∨ (y,x) ∈ r’ (K all_tac) >>
qpat_x_assum
‘∀x y. x ∈ k1 ∧ y ∈ k1 ⇒ (x,y) ∈ r ∨ (y,x) ∈ r’ (K all_tac) >>
qpat_x_assum
‘∀C'.
          (∀x y. x ∈ C' ∧ y ∈ C' ⇒ (x,y) ∈ r ∨ (y,x) ∈ r) ∧ C' ⊆ k2 ∧
          (upper_bounds C' r DIFF C') ∩ k2 ≠ ∅ ⇒
          ((CHOICE (upper_bounds C' r DIFF C') ∈ upper_bounds C' r ∧
            CHOICE (upper_bounds C' r DIFF C') ∉ C') ∧
           CHOICE (upper_bounds C' r DIFF C') ∈ k2) ∧
          ∀x'³'.
            ((x'³' ∈ upper_bounds C' r ∧ x'³' ∉ C') ∧ x'³' ∈ k2) ∧
            (x'³',CHOICE (upper_bounds C' r DIFF C')) ∈ r ⇒
            CHOICE (upper_bounds C' r DIFF C') = x'³'’ (K all_tac) >>
qpat_x_assum
‘∀C'.
          (∀x y. x ∈ C' ∧ y ∈ C' ⇒ (x,y) ∈ r ∨ (y,x) ∈ r) ∧ C' ⊆ k1 ∧
          (upper_bounds C' r DIFF C') ∩ k1 ≠ ∅ ⇒
          ((CHOICE (upper_bounds C' r DIFF C') ∈ upper_bounds C' r ∧
            CHOICE (upper_bounds C' r DIFF C') ∉ C') ∧
           CHOICE (upper_bounds C' r DIFF C') ∈ k1) ∧
          ∀x'³'.
            ((x'³' ∈ upper_bounds C' r ∧ x'³' ∉ C') ∧ x'³' ∈ k1) ∧
            (x'³',CHOICE (upper_bounds C' r DIFF C')) ∈ r ⇒
            CHOICE (upper_bounds C' r DIFF C') = x'³'’ (K all_tac) >>
qpat_x_assum
 ‘CHOICE (upper_bounds C r DIFF C) ∈ upper_bounds C r’
(K all_tac) >>
 qpat_x_assum
 ‘CHOICE (upper_bounds C r DIFF C) ∉ C’
(K all_tac) >>
first_x_assum (qspecl_then [‘x'’] strip_assume_tac) >> rfs[] >>
qpat_x_assum
 ‘x' ∉ C’
(K all_tac) >>
qpat_x_assum
 ‘x' ∉ k1’ (K all_tac) >>
qpat_x_assum
 ‘x ∈ k1’ (K all_tac) >>
qpat_x_assum
 ‘x' ∈ range r’ (K all_tac) >>
qpat_x_assum
 ‘C ⊆ k2’ (K all_tac) >>
qpat_x_assum
 ‘C ⊆ k1’ (K all_tac) >>
qpat_x_assum
 ‘k1 ≠ ∅’ (K all_tac) >>
qpat_x_assum
 ‘k2 ≠ ∅’ (K all_tac) >>
qpat_x_assum
 ‘transitive(r)’ (K all_tac) >>
qpat_x_assum
‘ x ∈ range r’ (K all_tac) >>
qpat_x_assum
‘x' ∈ upper_bounds C r’ (K all_tac) >>
qpat_x_assum
‘Abbrev (C = {x | x ∈ k1 ∧ x ∈ k2 ∧ (x,x') ∈ r})’
(K all_tac) >>
qabbrev_tac
‘t = CHOICE (upper_bounds C r DIFF C)’ >>
qpat_x_assum
‘ Abbrev (t = CHOICE (upper_bounds C r DIFF C))’
(K all_tac)
            
need
‘(x',CHOICE (upper_bounds C r DIFF C)) ∈ r ⇒
        CHOICE (upper_bounds C r DIFF C) = x'’

(*need x' in k2*)
Cases_on ‘(x',t) ∈ r ’
>-- first_x_assum drule >> strip_tac >> rw[]

 metis_tac[]


qpat_x_assum
 ‘x' ∈ upper_bounds C r’
 (K all_tac)

 metis_tac[]
imp_res_tac

pop_assum
‘∀x y. x ∈ k2 ∧ y ∈ k2 ⇒ (x,y) ∈ r ∨ (y,x) ∈ r’ by simp[] 


“!r k1 k2 x x'.
  transitive r /\
  k1 IN fchains r /\
  k2 IN fchains r /\
  x IN k1 /\
  x' IN k2 /\
  x' NOTIN k1
  ==>
  (x,x') IN r”

qpat_x_assum
‘ ∀C'.
          (∀x y. x ∈ C' ∧ y ∈ C' ⇒ (x,y) ∈ r ∨ (y,x) ∈ r) ∧
          (∀x. x ∈ C' ⇒ x ∈ k2) ∧
          (∃x''.
             ((x'' ∈ range r ∧ ∀y. y ∉ C' ∨ (y,x'') ∈ r) ∧ x'' ∉ C') ∧
             x'' ∈ k2) ⇒
          CHOICE ({x | x ∈ range r ∧ ∀y. y ∈ C' ⇒ (y,x) ∈ r} DIFF C') ∈
          minimal_elements
            (({x | x ∈ range r ∧ ∀y. y ∈ C' ⇒ (y,x) ∈ r} DIFF C') ∩ k2) r’
(K all_tac) >>
qpat_x_assum
 ‘ ∀C'.
          (∀x y. x ∈ C' ∧ y ∈ C' ⇒ (x,y) ∈ r ∨ (y,x) ∈ r) ∧
          (∀x. x ∈ C' ⇒ x ∈ k1) ∧
          (∃x''.
             ((x'' ∈ range r ∧ ∀y. y ∉ C' ∨ (y,x'') ∈ r) ∧ x'' ∉ C') ∧
             x'' ∈ k1) ⇒
          CHOICE ({x | x ∈ range r ∧ ∀y. y ∈ C' ⇒ (y,x) ∈ r} DIFF C') ∈
          minimal_elements
            (({x | x ∈ range r ∧ ∀y. y ∈ C' ⇒ (y,x) ∈ r} DIFF C') ∩ k1) r’
(K all_tac) >>
qpat_x_assum
‘(CHOICE ({x | x ∈ range r ∧ ∀y. y ∈ C ⇒ (y,x) ∈ r} DIFF C),x') ∈ r’ (K all_tac) >>
qpat_x_assum
‘CHOICE ({x | x ∈ range r ∧ ∀y. y ∈ C ⇒ (y,x) ∈ r} DIFF C) ∈
        minimal_elements
          (({x | x ∈ range r ∧ ∀y. y ∈ C ⇒ (y,x) ∈ r} DIFF C) ∩ k2) r’
(K all_tac) >>
qpat_x_assum
‘CHOICE ({x | x ∈ range r ∧ ∀y. y ∈ C ⇒ (y,x) ∈ r} DIFF C) ∈ k2’ (K all_tac) >>
qpat_x_assum
‘∀x y. x ∈ k2 ∧ y ∈ k2 ⇒ (x,y) ∈ r ∨ (y,x) ∈ r’
(K all_tac) >>
qpat_x_assum
‘ x'³' ∈ k2’ (K all_tac) >>
qpat_x_assum
‘∀x y. x ∈ C ∧ y ∈ C ⇒ (x,y) ∈ r ∨ (y,x) ∈ r’
(K all_tac) >> 
qpat_x_assum
‘Abbrev (C = {x | x ∈ k1 ∧ x ∈ k2 ∧ (x,x') ∈ r})’
(K all_tac) >> 
qpat_x_assum
‘x' ∉ C’ (K all_tac) >> 
qpat_x_assum
‘∀y. y ∈ C ⇒ (y,x') ∈ r’ (K all_tac) >> 
qpat_x_assum
‘∀x. x ∈ C ⇒ x ∈ k2’ (K all_tac) >> 
qpat_x_assum
‘x'' ∈ k1’ (K all_tac) >> 
qpat_x_assum
‘ x' ∉ k1’ (K all_tac) >> 
qpat_x_assum
‘x' ∈ range r’ (K all_tac) >> 
qpat_x_assum
‘x' ∈ k2’ (K all_tac) >>
qpat_x_assum
‘transitive r’ (K all_tac) >>


metis_tac[]


qpat_x_assum
‘∀x y. x ∈ k1 ∧ y ∈ k1 ⇒ (x,y) ∈ r ∨ (y,x) ∈ r’
(K all_tac) need this
‘∀x. x ∈ C ⇒ x ∈ k1’ 
