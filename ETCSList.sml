(*
collect the set of all sets of of sets of (n,a) pairs such that 
{} in the set 
if l is in in the set, then for every a\in A, l ∪ (CARD l,a) is in the set

*)

 
val Lists_cond_ex = prove_store("Lists_cond_ex",
e0
(rpt strip_tac >> 
 qby_tac
 ‘?P0. !ls. P0 o ls = TRUE <=> IN(Empty(N * A),ls)’ >--
 (qexists_tac ‘Mem(Exp(N * A, 1 + 1)) o 
             Pa(Empty(N * A) o To1(Exp(Exp(N * A, 1 + 1), 1 + 1)),id(Exp(Exp(N * A, 1 + 1), 1 + 1)))’
 >> rw[o_assoc,Pa_distr,IN_def] >>
 once_rw[one_to_one_id] >> rw[idL,idR,True1TRUE]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?P1. !a:1->A l ls.
    P1 o Pa(a,Pa(l,ls)) = TRUE<=>
    !n. hasCard(ls,n) ==> 
 !a. IN(Ins(Pa(n,a),l), ls)’ >-- 
(qexists_tac
 ‘Mem(Exp(N * A, 1 + 1)) o 
  Pa(Ins(
     Pa
     (CARD
      (p32(A,Exp(N * A, 1 + 1),Exp(Exp(N * A, 1 + 1),1+1))), 
      p31(A,Exp(N * A, 1 + 1),Exp(Exp(N * A, 1 + 1),1+1))),
     p32(A,Exp(N * A, 1 + 1),Exp(Exp(N * A, 1 + 1),1+1))),
)
(form_goal “!A.?P. !ls.P o ls = TRUE <=>
IN(Empty(N * A),ls) &
 !l. IN(l,ls) ==>
 !n. hasCard(ls,n) ==> 
 !a. IN(Ins(Pa(n,a),l), ls)”)
