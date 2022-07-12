
val _ = new_pred "isop" [("A",cat_sort),("A'",cat_sort)]

val _ = new_pred "isopf" 
            [("f",fun_sort (mk_cat "A") (mk_cat "B")),
             ("f'",fun_sort (mk_cat "A'") (mk_cat "B'"))]

val op_ex = store_ax("op_ex",
“∀A. ∃Aop. isop(A,Aop)”);


val op_op_refl = store_ax("op_op_refl",
“∀A Aop. isop(A,Aop) ⇒ isop(Aop,A)”);


val opf_uex = store_ax("opf_uex",
“∀A B f:A->B Aop Bop. isop(A,Aop) ∧ isop(B,Bop) ⇒ 
  ∃!f':Aop -> Bop. isopf(f,f')”);

val opf_unique = prove_store("opf_unique",
e0
(rpt strip_tac >>
 qby_tac ‘∃!f':Aop -> Bop. isopf(f,f')’ 
 >-- (irule opf_uex >> arw[]) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qsuff_tac ‘f1 = f' & f2 = f'’ 
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[] )
(form_goal
 “∀A B f:A->B Aop Bop f1:Aop->Bop f2. 
  isop(A,Aop) ∧ isop(B,Bop) &
  isopf(f,f1) & isopf(f,f2) ⇒ f1 = f2”));

val opf_opf_refl = store_ax("opf_opf_refl",
“∀A B f:A->B Aop Bop f':Aop -> Bop. isopf(f,f') ⇒ isopf(f',f)”); 


val opf_unique' = prove_store("opf_unique'",
e0
(rpt strip_tac >>
 irule opf_unique >>
 qexistsl_tac [‘A’,‘B’,‘f’] >> arw[] >>
 rpt strip_tac >> irule opf_opf_refl >> arw[])
(form_goal
 “∀A B f:A->B Aop Bop f1:Aop->Bop f2. 
  isop(A,Aop) ∧ isop(B,Bop) &
  isopf(f1,f) & isopf(f2,f) ⇒ f1 = f2”));



val op_2 = store_ax("op_2",“isop(2,2)”);

val op_1 = store_ax("op_1",“isop(1,1)”);

val op_3 = store_ax("op_3",“isop(3,3)”);

val opf_0f = store_ax("opf_0f",“isopf(0f,1f)”);


(*Although cannot have opf since preconditions are required, can have app function symbols on such functors.*)


(*should prove that op cats are equivalent*)


(*

A^op^op = A ∧ F^op^op

f: A-> B g:A->B

opf(f,A',B') = opf(g,A',B')

axiom


isopf(f:A->B,f':A'->B') ⇒ isop(A,A') ∧ isop(B,B')


 isop(A,A') ∧ isop(B,B') ⇒ ∃!

*)

(* use CC2_1*)
val ob_of_2 = prove_store("ob_of_2",
e0
(cheat)
(form_goal “∀f:1->2. f = 1f | f = 0f”));

val opf_1f = prove_store("opf_1f",
e0
(assume_tac opf_0f >> drule opf_opf_refl >> arw[])
(form_goal “isopf(1f,0f)”));

val op_ob_uex = prove_store("op_ob_uex",
e0
(rpt strip_tac >> irule opf_uex >> arw[op_1])
(form_goal “∀A A'. isop(A,A') ⇒ ∀a:1->A. ∃!a':1->A'. isopf(a,a')”));

(*part of CC7*)
val opf_o_opf = store_ax("opf_o_opf",
“∀A B f:A->B A' B' f':A'->B'. isopf(f,f') ⇒ 
 ∀C g:B->C C' g':B'->C'. isopf(g,g') ⇒
 isopf(g o f, g' o f')”);

val opar_dom_cod = prove_store("opar_dom_cod",
e0
(rpt strip_tac 
>-- (rw[dom_def,cod_def] >> 
    irule opf_o_opf >> arw[opf_0f]) 
>-- (rw[dom_def,cod_def] >>
    irule opf_o_opf >> arw[opf_1f]))
(form_goal
“∀A A'. isop(A,A') ⇒ 
∀a:2->A a':2 ->A'. isopf(a,a') ⇒
 isopf(dom(a),cod(a')) ∧ 
 isopf(cod(a),dom(a'))”));


val op_ar_uex = prove_store("op_ar_uex",
e0
(rpt strip_tac >> uex_tac >>
 qspecl_then [‘2’,‘A’,‘a’,‘2’,‘A'’] 
 assume_tac opf_uex >> fs[op_2] >> rfs[] >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum (x_choose_then "a'" strip_assume_tac) >> 
 qexists_tac ‘a'’ >> arw[] >>
 drule opar_dom_cod >> first_x_assum drule >>
 arw[] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal “∀A A'. isop(A,A') ⇒
 ∀a:2->A. ∃!a':2->A'. isopf(a,a') ∧ isopf(dom(a),cod(a')) ∧ 
 isopf(cod(a),dom(a'))”));

(*
val op_cat_ex = prove_store("op_cat_ex",
e0
(strip_tac >>  
 qsspecl_then [‘Id(A)’] strip_assume_tac op_ex >>
 qexists_tac ‘Aop’ >> arw[])
(form_goal “∀A. ∃A'. isop(A,A')”));
*)

val opf_id_id = store_ax("opf_id_id",
“∀A A'. isop(A,A') ⇒ isopf(Id(A),Id(A'))”);

(*pop assum list reverse the order...*)

val opf_unique = prove_store("opf_unique",
e0
(cheat)
(form_goal “∀A A'. isop(A,A') ⇒ ∀B B'.isop(B,B') ⇒
 ∀f:A->B f1:A'->B' f2:A' ->B'.  isopf(f,f1) ∧ isopf(f,f2) ⇒ f1 = f2”));

val op_prod = prove_store("op_prod",
e0
((*rpt strip_tac >> rw[isPr_def] >>
 rpt strip_tac >> uex_tac >>
 qby_tac ‘∃X0. isop(X,X0)’ >-- rw[op_cat_ex] >>
 pop_assum strip_assume_tac >>
 drule op_op_refl >>
 qby_tac ‘∃f':X0 ->A. isopf(f,f')’ 
 >-- (irule opf_ex >> arw[] >> irule op_op_refl >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘∃g':X0 ->B. isopf(g,g')’ 
 >-- (irule opf_ex >> arw[] >> irule op_op_refl >> arw[]) >>
 pop_assum strip_assume_tac >> 
 fs[isPr_def] >>
 first_x_assum (qsspecl_then [‘f'’,‘g'’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qby_tac ‘∃fg':X->AB'. isopf(fg,fg')’
 >-- (irule opf_ex >> arw[]) >>
 pop_assum strip_assume_tac >> 
 qexists_tac ‘fg'’ >>
 qby_tac ‘p1' o fg' = f & p2' o fg' = g’ 
 >-- (strip_tac  
      >-- (qsuff_tac ‘p1' o fg' = opf(p1 o fg,X,A') ∧ 
                     f = opf(p1 o fg,X,A')’ 
          >-- (rpt strip_tac >> arw[]) >>
          strip_tac
          >-- (irule is_opf >> arw[] >> 
              qpick_x_assum ‘p1 o fg = f'’ 
              (assume_tac o GSYM) >> arw[] >>
              irule opf_o_opf >> arw[]) 
          >-- (irule is_opf >> arw[] >> 
               irule opf_opf_refl >> arw[])) >>
      cheat (*same *) ) >>
 arw[] >> rpt strip_tac >>
 qsuff_tac ‘isopf(fg, fg'')’ 
 >-- (strip_tac >> irule opf_unique >>
     qexistsl_tac [‘X0’,‘AB’,‘fg’] >> arw[]) >>
 qby_tac
 ‘p1 o opf(fg'', X0,AB) = f' ∧ 
  p2 o opf(fg'', X0,AB) = g'’
 >-- cheat >>
 qby_tac ‘opf(fg'', X0,AB) = fg’
 >-- (first_x_assum irule >> arw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 irule opf_opf_refl >> irule opf_property >> arw[] >>
 irule op_op_refl >> arw[]*)cheat)
(form_goal
 “∀A B AB p1:AB ->A p2:AB ->B.isPr(p1,p2) ⇒
 ∀A' B' AB'. isop(A,A') ∧ isop(B,B') ∧ isop(AB,AB') ⇒ 
 ∀p1':AB' -> A' p2':AB' -> B'. isopf(p1,p1') ∧ isopf(p2,p2') ⇒ isPr(p1',p2')”));

val op_3 = store_ax("op_3",“isop(3,3)”);

val ab_dom_cod = prove_store("ab_dom_cod",
e0
(rw[dom_def,cod_def] >> assume_tac CC4_2 >>
 fs[isPo_def])
(form_goal “dom(β) = cod(α)”));

val oa_gamma_ba = prove_store("oa_gamma_ba",
e0
(cheat)
(form_goal “∀f:2->3 g:2->3. ~isid(f) ∧ ~isid(g) ∧ dom(g) = cod(f) ⇒ g = β ∧ f = α”));

val isid_opf = prove_store("isid_opf",
e0
(cheat)
(form_goal “∀A A'. isop(A,A') ⇒ 
 (∀f:2->A. isid(f) ⇔ isid(opf(f,2,A')))”));

val ab_not_id = prove_store("ab_not_id",
e0
(cheat)
(form_goal “~isid(α) ∧ ~isid(β)”));

(*
val dom_opf_cod = prove_store("dom_opf_cod",
e0
(rpt strip_tac >> drule opar_dom_cod >>
 irule is_opf >> arw[op_1] >> 
 qsuff_tac ‘isopf(f,opf(f,2,A'))’ 
 >-- (strip_tac >> first_x_assum drule >> arw[]) >>
 irule opf_property >> arw[op_2]
 )
(form_goal “∀A A'. isop(A,A') ⇒ 
 ∀f:2->A. dom(opf(f,2,A')) = opf(cod(f),1,A') ”));
*)

(*
val dom_opf_cod = prove_store("dom_opf_cod",
e0
(rpt strip_tac >> drule opar_dom_cod >>
 irule is_opf >> arw[op_1] >> 
 qsuff_tac ‘isopf(f,opf(f,2,A'))’ 
 >-- (strip_tac >> first_x_assum drule >> arw[]) >>
 irule opf_property >> arw[op_2] cheat
 )
(form_goal “∀A A'. isop(A,A') ⇒ 
 ∀f:2->A f':2->A'.isopf(f,f') ⇒
 isopf(cod(f),dom(f')) ”));
is precisely opar_dom_cod 
*)


val cod_opf_dom = prove_store("cod_opf_dom",
e0
(rpt strip_tac >> drule opar_dom_cod >>
 irule is_opf >> arw[op_1] >> 
 qsuff_tac ‘isopf(f,opf(f,2,A'))’ 
 >-- (strip_tac >> first_x_assum drule >> arw[]) >>
 irule opf_property >> arw[op_2]
 )
(form_goal “∀A A'. isop(A,A') ⇒ 
 ∀f:2->A. cod(opf(f,2,A')) = opf(dom(f),1,A') ”));

(*

val opf_ab = prove_store("opf_ab",
e0
(irule oa_gamma_ba >>
 assume_tac op_3 >> drule $ GSYM isid_opf >> arw[] >>
 rw[ab_not_id] >> 
 drule dom_opf_cod >> arw[] >>
 drule cod_opf_dom >> arw[] >>
 assume_tac ab_dom_cod >> 
 cheat
 (*cannot use category as input, trouble here! 
 alternatively, have a machinary that regard op(_,2,3), not 
 op(_,_,_), as a function symbol.*)
 )
(form_goal “opf(α,2,3) = β ∧ opf(β,2,3) = α”));

*)


val opf_ab = prove_store("opf_ab",
e0
(cheat)
(form_goal “isopf(α,β) & isopf(β,α)”));







(*if add the assumption that opf ⇒ is op cat, then agree with the actual situation, and can avoid the precondition in opf_opf_o*)



(*
val opf_opf_o = prove_store("opf_opf_o",
e0
(rpt strip_tac >> irule is_opf >> arw[] >>
 irule opf_o_opf >> strip_tac >> irule opf_property >> arw[])
(form_goal “∀A A'.isop(A,A') ⇒ ∀B B'. isop(B,B') ⇒
  ∀C C'. isop(C,C') ⇒ 
  ∀f:A->B g:B->C f':A'->B' g':B'->C'. 
  
 opf(g,B',C') o opf(f,A',B') = 
  opf(g o f,A',C')”));
*)


val opf_opf_o = prove_store("opf_opf_o",
e0
(rpt strip_tac >> irule is_opf >> arw[] >>
 irule opf_o_opf >> strip_tac >> irule opf_property >> arw[])
(form_goal “∀A A'.isop(A,A') ⇒ ∀B B'. isop(B,B') ⇒
  ∀C C'. isop(C,C') ⇒ 
  ∀f:A->B g:B->C. opf(g,B',C') o opf(f,A',B') = 
  opf(g o f,A',C')”));

val opf_oa = prove_store("opf_oa",
e0
(rpt strip_tac >-- (fs[cpsb_def] >>
 drule dom_opf_cod >> arw[] >>
 drule cod_opf_dom >> arw[] >> cheat
 (*same problem as above*)) >>
 qby_tac ‘cpsb(opf(f,2,A'),opf(g,2,A'))’
 >-- cheat >>
 rw[] >> drule oa_def' >> arw[] >>
 qby_tac
 ‘Poa(1f, 0f, α, β, opf(g, 2, A'), opf(f, 2, A')) = 
 opf(Poa(1f,0f,α,β,f,g),3,A')’ 
 >-- flip_tac >> irule is_Poa_ab >> fs[cpsb_def] >>
     qsuff_tac 
     ‘opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(α,2,3) =
      opf(f, 2, A') ∧ 
      opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(β,2,3) =
      opf(g, 2, A')’
     >-- rw[opf_ab] >>
     (*Poa_ab_eqn*)

cheat >>
 arw[] >> 
 qby_tac ‘γ = opf(γ,2,3)’ >-- cheat >>
 once_arw[] >> 
 qby_tac
 ‘opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(γ, 2, 3) = 
  opf(Poa(1f, 0f, α, β, f, g) o γ, 2,A')’
 >-- (irule opf_opf_o >> arw[op_2,op_3]) >>
 qpick_x_assum ‘γ = opf(γ, 2, 3)’ (K all_tac) >> 
 arw[] >>
 rev_drule oa_def' >> cheat (*same problem*))
(form_goal “∀A f:2->A g:2->A. cpsb(g,f) ⇒
 ∀A'. isop(A,A') ⇒ 
 cpsb(opf(f,2,A'),opf(g,2,A')) ∧
 opf(f,2,A') @ opf(g,2,A') = opf(g @ f,2,A')”));


val opf_op_ex = prove_store

(*for all f:A->B exists f':A'->B' such that f' is op to f and A' is op to A and B' is op to B*)

val opf1_eq = store_ax("opf1_eq",
“∀A B f:A->B g:A->B. f = g ⇒
 ∀A' B'. isop(A,A') ∧ isop(B,B') ⇒ 
 opf(f,A',B') = opf(g,A',B')”);


val opf_opf_eqn = prove_store("opf_opf_eqn",
e0
(rpt strip_tac >> 
 flip_tac >> irule is_opf >> drule op_op_refl >>
 rev_drule op_op_refl >> arw[] >>
 irule opf_opf_refl >> irule opf_property >> arw[])
(form_goal “∀A B A' B'. isop(A,A') ∧ isop(B,B') ⇒ 
 ∀f:A->B. opf(opf(f, A', B'), A, B) = f”));

rpt strip_tac >> irule Thm3_2 >> rpt strip_tac
>-- cheat >>
rw[isgen_def] >> rpt strip_tac >>
qspecl_then [‘A’] strip_assume_tac op_cat_ex >> 
qspecl_then [‘B’] (x_choose_then "B'" strip_assume_tac) 
op_cat_ex >>
qby_tac ‘~(opf(f1,A',B') = opf(f2,A',B'))’ >-- 
(ccontra_tac >>
 qsuff_tac ‘opf(opf(f1,A',B'),A,B) = f1 ∧
            opf(opf(f2,A',B'),A,B) = f2’
 >-- (drule opf1_eq >>
      first_x_assum (qspecl_then [‘A’,‘B’] assume_tac) >>
      drule op_op_refl >> 
      qby_tac ‘isop(A', A)’ >-- 
      (irule op_op_refl >> arw[]) >>
      strip_tac >> fs[]) >>
 strip_tac >> irule opf_opf_eqn >> arw[]) >>
drule CC2_2 >> pop_assum strip_assume_tac >>
qexists_tac ‘opf(a,op2,A)’ >>
qby_tac ‘opf(opf(a, op2, A),2,A') = a’
>-- irule opf_opf_eqn >> arw[] >> irule op_op_refl >> arw[]>>
    qby_tac ‘~(opf(f1, A', B') o opf(opf(a, op2, A), 2, A') =
              opf(f2, A', B') o opf(opf(a, op2, A), 2, A'))’      >-- arw[] >>
    qby_tac ‘opf(f1, A', B') o opf(opf(a, op2, A), 2, A') = 
             opf(f1 o opf(a, op2, A),2,B')’
    >-- (irule opf_opf_o >> arw[] >> 
        irule op_op_refl >> arw[]) >>
    qby_tac ‘opf(f2, A', B') o opf(opf(a, op2, A), 2, A') = 
             opf(f2 o opf(a, op2, A),2,B')’
    >-- (irule opf_opf_o >> arw[] >> 
        irule op_op_refl >> arw[]) >>
    fs[] >> 
    ccontra_tac >> drule opf1_eq >>
    first_x_assum (qspecl_then [‘2’,‘B'’] assume_tac) >>
    rfs[] >> rev_drule op_op_refl >> fs[]
        


qexists_tac ‘opf(a,op2,A')’
“∀op2. isop(2,op2) ⇒ areIso(op2,2)”

val opf_To1 = prove_store("opf_To1",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘1’,‘To1(A)’,‘A’,‘1’]
 assume_tac opf_uex >>
 rfs[op_1] >> fs[To1_def] >>
 pop_assum (strip_assume_tac o uex_expand))
(form_goal
 “∀A.isop(A,A) ⇒ isopf(To1(A), To1(A))”));


val opf_opf_id = prove_store("opf_opf_id",
e0
(rpt strip_tac >>
 rw[id_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qsuff_tac
     ‘isopf((a o To1(2)) o 0f, (a' o To1(2)) o 1f)’
     >-- (rw[o_assoc,one_to_one_Id] >> rw[IdR]) >>
     irule opf_o_opf >> arw[opf_0f]) >>
 irule opf_o_opf >> arw[] >>
 assume_tac op_2 >> drule opf_To1 >> arw[])
(form_goal
 “∀A Aop. isop(A,Aop) ⇒
  ∀a a'.
  (isopf(id(a:1->A),id(a':1->Aop)) ⇔ isopf(a,a'))”));

val opar_uex = prove_store("opar_uex",
e0
(rpt strip_tac >>
 qspecl_then [‘2’,‘A’,‘f’,‘2’,‘Aop’] 
 assume_tac opf_uex >>
 rfs[op_2])
(form_goal
 “∀A Aop. isop(A,Aop) ⇒
  ∀f:2->A. ?!f':2->Aop. isopf(f,f')”));


val opar_ex = prove_store("opar_ex",
e0
(rpt strip_tac >>
 drule opar_uex >>
 first_x_assum
 (qsspecl_then [‘f’] 
  (strip_assume_tac o uex2ex_rule)) >>
 qexists_tac ‘f'’ >> arw[])
(form_goal
 “∀A Aop. isop(A,Aop) ⇒
  ∀f:2->A. ?f':2->Aop. isopf(f,f')”));


val opar_unique = prove_store("opar_unique",
e0
(rpt strip_tac >>
 drule opar_uex >>
 first_x_assum
 (qsspecl_then [‘f’] assume_tac) >>
 assume_tac
 (uex_unique |> qspecl [‘2’,‘Aop’] 
 |> fVar_sInst_th “P(f':2->Aop)”
    “isopf(f:2->A, f':2->Aop)”) >>
 first_x_assum drule >> first_x_assum irule >>
 arw[])
(form_goal
 “∀A Aop. isop(A,Aop) ⇒
  ∀f:2->A f1 f2:2->Aop. 
  isopf(f,f1) & isopf(f,f2) ⇒ f1 = f2”));


val opf_gamma = prove_store("opf_gamma",
e0
(cheat (* use is_gamma *))
(form_goal
 “isopf(γ,γ)”));

val opf_cpsb = prove_store("opf_cpsb",
e0
(rpt strip_tac >> fs[cpsb_def] >>
 drule opar_dom_cod >>
 first_x_assum rev_drule >>
 irule opf_unique >>
 qexistsl_tac [‘1’,‘A’,‘cod(f)’] >>
 arw[op_1] >>
 last_x_assum (assume_tac o GSYM) >> arw[] >>
 drule opar_dom_cod >>
 first_x_assum drule >> arw[])
(form_goal 
 “∀A f:2->A g:2->A. cpsb(g,f) ⇒
  ∀A'. isop(A,A') ⇒ 
  ∀f' g':2->A'.isopf(f,f') & isopf(g,g') ⇒
 cpsb(f',g')”));


val opf_o_eq = prove_store("opf_o_eq",
e0
(rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (irule opf_unique >>
     qexistsl_tac [‘A’,‘C’,‘a’] >> arw[] >>
     pop_assum (assume_tac o GSYM) >>
     arw[] >>
     irule opf_o_opf >>
     arw[]) >>
 irule opf_unique >>
 qexistsl_tac [‘A'’,‘C'’,‘a'’] >> arw[] >>
 rpt strip_tac (* 4 *)
 >-- (irule opf_opf_refl >> arw[]) 
 >-- (irule op_op_refl >> arw[]) 
 >-- (irule op_op_refl >> arw[]) >>
 pop_assum (assume_tac o GSYM) >>
 arw[] >>
 irule opf_o_opf >> strip_tac >>
 irule opf_opf_refl >> arw[])
(form_goal
 “∀A B f:A->B A' B' f':A'->B' 
   C g:B->C C' g':B'->C'.
  isop(A, A') & isop(B,B') & isop(C, C') & 
  isopf(f,f') & isopf(g,g') ⇒
  ∀a a'. isopf(a,a') ⇒
   (g o f = a ⇔ g' o f' = a') 
  ”));

val opf_tri = prove_store("opf_tri",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘∀t. 
   isopf(tri(f,g),t) ⇒ t = tri(g',f')’
 >-- (strip_tac >>
     qby_tac
     ‘∃!t:3->A'. isopf(tri(f,g),t)’
     >-- (irule opf_uex >> arw[op_3]) >>
     pop_assum (strip_assume_tac o uex2ex_rule) >>
     first_x_assum drule >> fs[]) >>
 rpt strip_tac >>
 irule is_tri >>
 drule opf_cpsb >> 
 rw[GSYM cpsb_def] >> first_x_assum drule >>
 qby_tac ‘cpsb(f',g')’ 
 >-- (first_x_assum irule >> arw[]) >>
 arw[] >>
 qsuff_tac
 ‘tri(f, g) o β = g & tri(f,g) o α = f’ 
 >-- (rpt strip_tac >--
     (irule $ iffLR opf_o_eq >>
     qexistsl_tac [‘2’,‘3’,‘β’,‘A’,‘g’,‘tri(f,g)’]>>
     arw[] >> rw[op_2,op_3] >>
     rw[opf_ab]) >>
     irule $ iffLR opf_o_eq >>
     qexistsl_tac [‘2’,‘3’,‘α’,‘A’,‘f’,‘tri(f,g)’]>>
     arw[] >> rw[op_2,op_3] >>
     rw[opf_ab]) >> 
 qsspecl_then [‘f’,‘g’] assume_tac tri_eqns >>
 rfs[cpsb_def])
(form_goal 
 “∀A f:2->A g:2->A. cpsb(g,f) ⇒
  ∀A'. isop(A,A') ⇒ 
  ∀f' g':2->A'.isopf(f,f') & isopf(g,g') ⇒
 isopf(tri(f,g),tri(g',f'))”));

val opf_oa = prove_store("opf_oa",
e0
(rpt strip_tac >>
 qby_tac ‘cpsb(f',g')’ 
 >-- (irule opf_cpsb >>
     qexistsl_tac [‘A’,‘f’,‘g’] >> arw[]) >>
 rw[oa_def] >>
 qby_tac
 ‘isopf(tri(f,g),tri(g',f'))’ 
 >-- (rev_drule opf_tri >>
     first_x_assum irule >> arw[]) >>
 irule opf_o_opf >> arw[opf_gamma])
(form_goal
 “∀A f:2->A g:2->A. cpsb(g,f) ⇒
  ∀A'. isop(A,A') ⇒ 
  ∀f' g':2->A'.isopf(f,f') & isopf(g,g') ⇒
isopf(g @ f,f' @ g')”));

val isopf_oa = prove_store("opf_oa",
e0
(rpt strip_tac >-- cheat >>
 qby_tac ‘cpsb(opf(f,2,A'),opf(g,2,A'))’
 >-- cheat >>
 rw[] >> drule oa_def' >> arw[] >>
 qby_tac
 ‘Poa(1f, 0f, α, β, opf(g, 2, A'), opf(f, 2, A')) = 
 opf(Poa(1f,0f,α,β,f,g),3,A')’ 
 >-- flip_tac >> irule is_Poa_ab >> fs[cpsb_def] >>
     qsuff_tac 
     ‘opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(α,2,3) =
      opf(f, 2, A') ∧ 
      opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(β,2,3) =
      opf(g, 2, A')’
     >-- rw[opf_ab] >>
     (*Poa_ab_eqn*)

cheat >>
 arw[] >> 
 qby_tac ‘γ = opf(γ,2,3)’ >-- cheat >>
 once_arw[] >> 
 qby_tac
 ‘opf(Poa(1f, 0f, α, β, f, g), 3, A') o opf(γ, 2, 3) = 
  opf(Poa(1f, 0f, α, β, f, g) o γ, 2,A')’
 >-- (irule opf_opf_o >> arw[op_2,op_3]) >>
 qpick_x_assum ‘γ = opf(γ, 2, 3)’ (K all_tac) >> 
 arw[] >>
 rev_drule oa_def' >> cheat same problem*)cheat)
(form_goal 
 “∀A f:2->A g:2->A. cpsb(g,f) ⇒
  ∀A'. isop(A,A') ⇒ 
  ∀f' g':2->A'.isopf(f,f') & isopf(g,g') ⇒
 cpsb(f',g') ∧
isopf(g @ f,f' @ g')”));

val opf_oa = prove_store("opf_oa",
e0
(cheat)
(form_goal
 “∀A f:2->A g:2->A. cpsb(g,f) ⇒
  ∀A'. isop(A,A') ⇒ 
  ∀f' g':2->A'.isopf(f,f') & isopf(g,g') ⇒
isopf(g @ f,f' @ g')”));



val Thm18 = prove_store("Thm18",
e0
(rpt strip_tac >>
 assume_tac
 (CC5 |> qspecl [‘Aop’,‘B’] 
 |> fVar_sInst_th “R(f:2->Aop,g:2->B)”
    “∃f0:2->A. isopf(f0,f:2->Aop) & R(f0,g:2->B)”) >>
 qsuff_tac
 ‘?(cf : fun(Aop, B)).
 !(a : fun(2, Aop))  (b : fun(2, B)).
    (?(f0 : fun(2, A)). isopf(f0, a) & R(f0, b)) <=>
                 cf o a = b’
 >-- (strip_tac >>
     qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
     >-- (qexists_tac ‘a’ >> arw[]) >> 
     qsuff_tac ‘a = f0’ 
     >-- (strip_tac >> arw[]) >>
     flip_tac >>
     irule opf_unique' >> 
     qexistsl_tac [‘2’,‘Aop’,‘a'’] >>
     arw[op_2] >> irule op_op_refl >> arw[]) >>
 first_x_assum irule >> strip_tac (* 2 *)
 >-- (rpt strip_tac (* 2 *)
     >-- (drule opar_dom_cod >>
         first_x_assum drule >> 
         qexists_tac ‘id(cod(f0))’ >>
         last_x_assum drule >> arw[] >>
         drule opf_opf_id  >>
         arw[]) >>
     drule opar_dom_cod >>
     first_x_assum drule >> 
     qexists_tac ‘id(dom(f0))’ >>
     last_x_assum drule >> arw[] >>
     drule opf_opf_id  >>
     arw[]) >> strip_tac (* 2 *) >--
 (rpt strip_tac >> drule op_op_refl >>
 drule opar_uex >>
 first_x_assum (qsspecl_then [‘f’] assume_tac) >>  
 qsuff_tac
 ‘?(g : fun(2, B)). 
  ?(f0 : fun(2, A)). isopf(f0, f) & R(f0, g)’
 >-- (strip_tac >> uex_tac >>
     qexists_tac ‘g’ >> rpt strip_tac (* 2 *)
     >-- (qexists_tac ‘f0’ >> arw[]) >>
     qby_tac ‘f0 = f0'’ 
     >-- (irule opf_unique' >>
         qexistsl_tac [‘2’,‘Aop’,‘f’] >> arw[] >>
         rw[op_2]) >> fs[] >>
     first_x_assum 
     (qsspecl_then [‘f0'’] assume_tac) >>
     assume_tac
     (uex_unique |> qspecl [‘2’,‘B’] 
     |> fVar_sInst_th “P(g:2->B)”
        “R(f0':2->A, g:2->B)”) >>
     first_x_assum drule >> first_x_assum irule >>
     arw[]) >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 first_x_assum (qsspecl_then [‘f'’] assume_tac) >>
 pop_assum (strip_assume_tac o uex2ex_rule)>>
 qexistsl_tac [‘g’,‘f'’] >> arw[] >>
 drule opf_opf_refl >> arw[]) >>
 rpt strip_tac >>
 qby_tac ‘cpsb(f0',f0'')’ 
 >-- (drule isopf_oa >>
     drule op_op_refl >>
     first_x_assum drule >>
     first_x_assum
     (qsspecl_then [‘f0'’,‘f0''’] assume_tac) >>
     qsuff_tac
     ‘isopf(f, f0') & isopf(g, f0'')’
     >-- (disch_tac >>
         first_x_assum drule >> arw[]) >> 
     strip_tac >> irule opf_opf_refl >> arw[]) >>
 first_assum drule >>
 first_x_assum irule >> arw[] >>
 qsuff_tac
 ‘f0 = f0' @ f0''’
 >-- (strip_tac >> fs[]) >>
 qsuff_tac ‘isopf(f0' @ f0'', g @ f)’ 
 >-- (strip_tac >> irule opf_unique' >>
     qexistsl_tac [‘2’,‘Aop’,‘g @ f’] >> 
     arw[op_2] >> irule op_op_refl >> arw[]) >>
 irule opf_opf_refl >> 
 qsuff_tac ‘cpsb(f0',f0'') & 
 isopf(g @ f,f0' @ f0'')’
 >-- (strip_tac >> arw[]) >>
 irule isopf_oa >> arw[] >> rpt strip_tac (* 3 *)
 >-- (irule opf_opf_refl >> arw[]) 
 >-- (irule op_op_refl >> arw[]) >>
 irule opf_opf_refl >> arw[])
(form_goal
 “∀A B. 
 (∀f:2->A. ∃!g:2->B. R(f,g)) ∧
 (∀f:2->A g:2->B. R(f,g) ⇒ 
  R(id(dom(f)),id(cod(g))) ∧
  R(id(cod(f)),id(dom(g)))) ∧
 (∀f:2->A g:2->A h: 2->B. cpsb(g,f) ⇒
  R(g @ f, h) ⇒
  ∀f1 g1. R(f,f1) ∧ R(g,g1) ⇒ h = f1 @ g1) ⇒
 ∀Aop. isop(A,Aop) ⇒ 
 ∃cf:Aop->B. 
 ∀a:2->A a':2->Aop.
  isopf(a,a') ⇒
 ∀b:2->B.
  R(a,b) ⇔ cf o a' = b”));

val isDiso_def = 
qdefine_psym("isDiso",[‘A’,‘i:A1->A2’])
‘isop(A,A1) & isop(A,A2) & 
 Iso(i) &
 (∀f:2->A f1:2->A1.
   isopf(f,f1) ⇒ 
   ∀f2:2->A2.isopf(f,f2) ⇔ 
   i o f1 = f2)’



val isopf_of_o = prove_store("isopf_of_o",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’,‘f’,‘A'’,‘B'’]
 assume_tac opf_uex >>
 rfs[] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qspecl_then [‘B’,‘C’,‘g’,‘B'’,‘C'’]
 assume_tac opf_uex >> rfs[] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexistsl_tac [‘f'’,‘f''’] >> arw[] >>
 irule opf_unique >>
 qexistsl_tac [‘A’,‘C’,‘g o f’] >>
 arw[] >> irule opf_o_opf >> arw[])
(form_goal
 “∀A C A' C'. isop(A,A') & isop(C,C') ⇒
 ∀B f:A->B g:B->C gf':A'->C'. 
 isopf(g o f,gf') ⇒
 ∀B'. isop(B,B') ⇒
∃f':A' -> B' g':B'->C'.
 isopf(f,f') & isopf(g,g') &
 gf' = g' o f'”));

val Thm19_natural = prove_store("Thm19_natural",
e0
(rpt strip_tac >> fs[isDiso_def] >>
 irule $ iffLR fun_ext >>
 rw[o_assoc] >> strip_tac >>
 flip_tac >>
 first_assum $ irule o iffLR >>
 qby_tac
 ‘?!f1a0:2->B. isopf(f1 o a,f1a0)’ 
 >-- (irule opar_uex >> irule op_op_refl >> arw[]) >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘f1a0’ >> drule opf_opf_refl >>
 arw[] >>
 qby_tac
 ‘∃a0:2->A f0:A->B. 
  isopf(a,a0) & isopf(f1,f0) &
  f1a0 = f0 o a0’
 >-- (irule isopf_of_o >>
     rw[op_2] >>
     rpt strip_tac (* 3 *)
     >-- (irule opf_opf_refl >> arw[]) 
     >-- (irule op_op_refl >> arw[]) >>
     irule op_op_refl >> arw[]) >>
 pop_assum strip_assume_tac >>
 arw[]>>
 qby_tac ‘f0= f’ 
 >-- (irule opf_unique >>
     qexistsl_tac [‘A1’,‘B1’,‘f1’] >> arw[] >>
     rpt strip_tac (* 3 *)
     >-- (irule opf_opf_refl >> arw[]) 
     >-- (irule op_op_refl >> arw[]) >>
     irule op_op_refl >> arw[]) >> fs[] >>
 irule opf_o_opf >>
 arw[] >> 
 first_assum $ irule o iffRL >>
 qexists_tac ‘a’ >> rw[]>>
 irule opf_opf_refl >> arw[])
(form_goal
 “∀A A1 A2 iA:A1->A2
   B B1 B2 iB:B1->B2. 
   isDiso(A,iA) & isDiso(B,iB) ⇒
   ∀f:A->B f1:A1->B1 f2:A2->B2.
    isopf(f,f1) & isopf(f,f2) ⇒
    f2 o iA = iB o f1
   ”));


val Thm19_uex = prove_store("Thm19_uex",
e0
(qsuff_tac
 ‘∀A A1 A2. isop(A,A1) & isop(A,A2) ⇒
  ?i:A1 -> A2. isDiso(A,i)’
 >-- (rpt strip_tac >> 
     first_x_assum 
     (qspecl_then [‘A’,‘A1’,‘A2’] assume_tac) >>
     rfs[] >> 
     uex_tac >> 
     qexists_tac ‘i’ >> arw[] >>
     rpt strip_tac >>
     qspecl_then [‘A’,‘A1’,‘A2’,‘i’,
                  ‘A’,‘A1’,‘A2’,‘i'’] assume_tac
     Thm19_natural >>
     rfs[] >>
     first_x_assum 
     (qsspecl_then [‘Id(A)’,‘Id(A1)’,‘Id(A2)’]
      assume_tac) >>
     rev_drule opf_id_id >> 
     drule opf_id_id >> fs[] >>
     fs[IdL,IdR]) >>
 qsuff_tac
 ‘∀A A1 A2. isop(A,A1) & isop(A,A2) ⇒
  ?i:A1 -> A2. 
  (∀f:2->A f1:2->A1.
   isopf(f,f1) ⇒ 
   ∀f2:2->A2.isopf(f,f2) ⇔ 
   i o f1 = f2)’ >--
 (rpt strip_tac >>
 first_assum 
 (qspecl_then [‘A’,‘A1’,‘A2’] assume_tac) >>
 first_x_assum
 (qspecl_then [‘A’,‘A2’,‘A1’] assume_tac) >>
 rfs[] >> 
 qexists_tac ‘i’ >>
 rw[isDiso_def] >> arw[] >>
 rw[Iso_def] >>
 qexists_tac ‘i'’ >> strip_tac (* 2 *)
 >-- (irule $ iffLR fun_ext >>
     rw[o_assoc,IdL] >>
     strip_tac >>
     first_x_assum $ irule o iffLR >>
     rev_drule op_op_refl >>
     qspecl_then [‘2’,‘A1’,‘a’,‘2’,‘A’]
     assume_tac opf_uex >>
     rfs[op_2] >>
     pop_assum (assume_tac o uex2ex_rule) >>
     pop_assum (x_choose_then "a0" assume_tac) >>
     qexists_tac ‘a0’ >>
     drule opf_opf_refl >> arw[] >>
     first_x_assum (irule o iffRL) >>
     qexists_tac ‘a’ >> arw[]) >>
 irule $ iffLR fun_ext >> 
 rw[o_assoc,IdL] >>
 strip_tac >>
 first_x_assum $ irule o iffLR >>
 drule op_op_refl >>
 qspecl_then [‘2’,‘A2’,‘a’,‘2’,‘A’]
 assume_tac opf_uex >>
 rfs[op_2] >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "a0" assume_tac) >>
 qexists_tac ‘a0’ >>
 drule opf_opf_refl >> arw[] >>
 first_x_assum (irule o iffRL) >>
 qexists_tac ‘a’ >> arw[]) >>
 rpt strip_tac >> 
 assume_tac
 (Thm18 |> qspecl [‘A’,‘A2’] 
 |> fVar_sInst_th “R(f:2->A,g:2->A2)”
    “isopf(f:2->A,g:2->A2)”) >>
 qsuff_tac
 ‘!(Aop : cat).
               isop(A, Aop) ==>
               ?(cf : fun(Aop, A2)).
                 !(a : fun(2, A))  (a' : fun(2, Aop)).
                   isopf(a, a') ==>
                   !(b : fun(2, A2)). isopf(a, b) <=> cf o a' = b’
 >-- (strip_tac >>
     first_x_assum (qspecl_then [‘A1’] assume_tac) >>
     rfs[] >>
     qexists_tac ‘cf’ >>
     rpt strip_tac >>
     first_x_assum irule >> arw[]) >>
 first_x_assum match_mp_tac >>
 strip_tac (* 2 *)
 >-- (strip_tac >> 
     irule opf_uex >> arw[op_2]) >>
 strip_tac (* 2 *) 
 >-- (drule opar_dom_cod >>
     rpt gen_tac >> strip_tac >>
     first_x_assum drule >>
     drule opf_opf_id >> arw[]) >>
 rpt strip_tac >>
 irule opf_unique >>
 qexistsl_tac [‘2’,‘A’,‘g @ f’] >>
 arw[op_2] >>
 irule opf_oa >> arw[])
(form_goal
 “∀A A1 A2. isop(A,A1) & isop(A,A2) ⇒
  ?!i:A1 -> A2. isDiso(A,i)”));
