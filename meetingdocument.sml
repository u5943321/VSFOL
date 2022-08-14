val indisc_2_FSCC = cg $
e0
(rpt strip_tac >>
 rw[FSCC_def] >> rpt strip_tac >>
 qby_tac
 ‘(!fc:2->Cl. dom(fc) = o1 & cod(fc) = o2 ==> fc = a1)’ 
 >-- cheat >>
 qby_tac
 ‘(!fc:2->Cl. dom(fc) = o2 & cod(fc) = o1 ==> fc = a2)’ >--
 cheat >>
 qby_tac ‘~(a1 = id(o1))’ 
 >-- (cheat) >> 
 qby_tac
 ‘(!fc:2->Cl. dom(fc) = o1 & cod(fc) = o1 ==> fc = id(o1))’
 >--
 (cheat) >> 
 qby_tac
 ‘(!fc:2->Cl. dom(fc) = o2 & cod(fc) = o2 ==> fc = id(o2))’
 >-- (cheat) >> 
 qby_tac
 ‘!c. isPb(c, o1, i, To1(S)) ==>
  !f:2->A. 
  (!s1 s2. dom(f) = i o s1 & cod(f) = i o s2 ==>
   c o f = id(o1)) & 
  (!s1. dom(f) = i o s1 ==>
        (!s2. ~(cod(f) = i o s2)) ==>
   c o f = a1) & 
  (!s2. cod(f) = i o s2 ==>
        (!s1. ~(dom(f) = i o s1)) ==>
   c o f = a2) &
  (
  (!s1. ~(dom(f) = i o s1)) &
  (!s2. ~(cod(f) = i o s2)) ==> c o f = id(o2))’ 
 >-- cheat >>
 qsuff_tac ‘?c.isPb(c, o1, i, To1(S))’
 >-- (strip_tac >> uex_tac >>
     qexists_tac ‘c’ >> arw[] >>
     rpt strip_tac >>
     irule $ iffLR fun_ext >>
     strip_tac >> 
     qby_tac
     ‘(!s1:1->S. ~(dom(a) = i o s1)) <=> 
      ~(?s1:1->S. dom(a) = i o s1)’
     >-- cheat >>
     qby_tac
     ‘(!s2:1->S. ~(cod(a) = i o s2)) <=> 
     ~(?s2:1->S. cod(a) = i o s2)’
     >-- cheat >> 
     qcases ‘?s1.dom(a) = i o s1’ >>
     qcases ‘?s2.cod(a) = i o s2’ (* 4 *)
     >-- cheat
     >-- (pop_assum mp_tac >> pop_assum strip_assume_tac >>
          rpt strip_tac >>
          first_assum drule >> 
          first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
          first_x_assum drule >>
          first_x_assum rev_drule >> 
          first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >> 
          first_x_assum drule >>
          qsuff_tac ‘c' o a = a1 & c o a = a1’
          >-- (strip_tac >> arw[]) >>
          strip_tac (* 2 *)
          >-- (first_x_assum irule >> arw[]) >>
          first_x_assum irule >> arw[])
     >-- cheat >>
     cheat) >> cheat)
(form_goal
 “!Cl o1:1->Cl o2:1->Cl a1:2->Cl a2:2->Cl. 
 dom(a1) = o1 ∧ cod(a1) = o2 ∧ 
 dom(a2) = o2 ∧ cod(a2) = o1 ∧ 
 a1 @ a2 = id(o2) ∧ a2 @ a1 = id(o1) ∧
 ~(o1 = o2) &
 (!oc:1->Cl. oc = o1 | oc = o2) & 
 (∀a:2-> Cl. a = id(o1) | a = id(o2) | a = a1 | a = a2) ==>
 FSCC(o1)”));


val indisc_2_FSCC = cg $
e0
(rpt strip_tac )
(form_goal
 “!Cl o1:1->Cl o2:1->Cl a1:2->Cl a2:2->Cl. 
 dom(a1) = o1 ∧ cod(a1) = o2 ∧ 
 dom(a2) = o2 ∧ cod(a2) = o1 ∧ 
 a1 @ a2 = id(o2) ∧ a2 @ a1 = id(o1) ∧
 ~(o1 = o2) &
 (!oc:1->Cl. oc = o1 | oc = o2) & 
 (∀a:2-> Cl. a = id(o1) | a = id(o2) | a = a1 | a = a2) ==>
 FSCC(o1)”)

