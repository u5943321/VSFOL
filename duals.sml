
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
(strip_tac >>
 qsspecl_then [‘f’] strip_assume_tac one_to_two >> fs[])
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
(rpt strip_tac >>
 assume_tac opf_uex >>
 first_x_assum 
 (qspecl_then [‘A’,‘B’,‘f:A->B’,‘A'’,‘B'’] assume_tac) >>
 rfs[] >>
 pop_assum (strip_assume_tac o uex_expand) >>
 first_assum rev_drule >> arw[] >> flip_tac >>
 first_x_assum irule >> arw[])
(form_goal “∀A A'. isop(A,A') ⇒ ∀B B'.isop(B,B') ⇒
 ∀f:A->B f1:A'->B' f2:A' ->B'.  isopf(f,f1) ∧ isopf(f,f2) ⇒ f1 = f2”));


(*
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

*)

val op_3 = store_ax("op_3",“isop(3,3)”);

(*
val ab_dom_cod = prove_store("ab_dom_cod",
e0
(rw[dom_def,cod_def] >> assume_tac CC4_2 >>
 fs[isPo_def])
(form_goal “dom(β) = cod(α)”));
*)
val oa_gamma_ba = prove_store("oa_gamma_ba",
e0
(rpt gen_tac >> strip_tac >> 
 qsspecl_then [‘f’] strip_assume_tac to_3_cases >>
  qsspecl_then [‘g’] strip_assume_tac to_3_cases >>
 fs[id_isid] >> 
 fs[three_dom_cod] >> fs[three_ob_ne])
(form_goal “∀f:2->3 g:2->3. ~isid(f) ∧ ~isid(g) ∧ dom(g) = cod(f) ⇒ g = β ∧ f = α”));


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


(*
val id_opf = prove_store("id_opf",
e0
()
(form_goal 
 “∀A A'. isop(A,A') ⇒ ”));
*)

val isid_opf = prove_store("isid_opf",
e0
(qsuff_tac
 ‘∀A A'. isop(A,A') ⇒ 
 (∀f:2->A f':2->A'. isopf(f,f') ⇒
  (isid(f) ==> isid(f')))’
 >-- (rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
     >-- (first_x_assum drule >> first_x_assum drule >>
         first_x_assum drule >> arw[]) >>
     first_x_assum irule >> qexistsl_tac [‘A'’,‘f'’] >>
     arw[] >> drule op_op_refl >> arw[] >>
     irule opf_opf_refl >> arw[]) >>
rpt strip_tac >>
fs[isid_def] >> fs[GSYM id_def] >>
qexists_tac ‘dom(f')’ >> 
qby_tac ‘isopf(id(f0),id(dom(f')))’ 
>-- (irule $ iffRL opf_opf_id >> arw[] >>
     drule opar_dom_cod >>
     first_x_assum drule >> fs[id_cod]) >>
irule opar_unique >> 
qexistsl_tac [‘A’,‘id(f0)’] >> arw[])
(form_goal “∀A A'. isop(A,A') ⇒ 
 (∀f:2->A f':2->A'. isopf(f,f') ⇒
  (isid(f) ⇔ isid(f')))”));

val isid_dom_cod_eq = prove_store("isid_dom_cod_eq",
e0
(rpt strip_tac >> fs[isid_def,dom_def,cod_def,o_assoc,one_to_one_Id,IdR] )
(form_goal “!A f:2->A. isid(f) ==> dom(f) = cod(f)”));


val ab_not_id = prove_store("ab_not_id",
e0
(strip_tac >> ccontra_tac 
 >> (drule isid_dom_cod_eq >>
     fs[three_ob_ne,three_dom_cod]))
(form_goal “~isid(α) ∧ ~isid(β)”));

val opf_ab = prove_store("opf_ab",
e0
(qsuff_tac
 ‘∀f:2->3 g. 
  isopf(α,f) & isopf(β,g) ⇒ f = β & g = α’ 
 >-- (rpt gen_tac >> strip_tac >>
     qby_tac
     ‘∃f:2->3 g:2->3.isopf(α,f) & isopf(β,g)’
     >-- (assume_tac op_3 >> 
         drule opar_ex >>
         first_assum (qspecl_then [‘α’] assume_tac) >>
         first_x_assum (qspecl_then [‘β’] assume_tac) >> 
         fs[] >> qexistsl_tac [‘f'’,‘f''’] >> arw[]) >>
     pop_assum 
     (x_choosel_then ["f","g"] assume_tac) >>
     first_x_assum drule >> fs[]) >>
 rpt gen_tac >> strip_tac >>
 irule oa_gamma_ba >> assume_tac op_3 >>
 drule isid_opf >> first_assum drule >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 first_x_assum rev_drule >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[ab_not_id] >>
 irule $ opf_unique >> 
 qexistsl_tac [‘1’,‘3’,‘cod(α)’] >>  
 rw[op_1,op_3] >>
 rw[GSYM ab_dom_cod] >>
 drule opar_dom_cod >>
 first_assum drule >> arw[] >>
 rw[ab_dom_cod] >> 
 first_x_assum rev_drule >> arw[])
(form_goal “isopf(α,β) & isopf(β,α)”));


val op_alpha1_beta2 = prove_store("op_alpha1_beta2",
e0
(assume_tac op_1 >> assume_tac op_3 >>
 assume_tac opf_ab >> pop_assum strip_assume_tac >>
 drule opar_dom_cod >> first_x_assum drule >>
 fs[three_dom_cod] >> drule opf_opf_refl >> arw[])
(form_goal “isopf(α₁, β₂)”));


val opf_gamma = prove_store("opf_gamma",
e0
(assume_tac op_3 >>
 drule opar_ex >>
 first_x_assum (qspecl_then [‘γ’] assume_tac) >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘f' = γ’ >-- (strip_tac >> fs[]) >>
 irule is_gamma >>
 drule opar_dom_cod >>
 first_x_assum drule >> fs[three_dom_cod] >>
 assume_tac op_alpha1_beta2 >>
 strip_tac (* 2 *)
 >-- (irule opf_unique >> qexistsl_tac [‘1’,‘3’,‘β₂’] >>
     arw[op_1,op_3] >> irule opf_opf_refl >> arw[]) >>
 irule opf_unique >> qexistsl_tac [‘1’,‘3’,‘α₁’] >>
 arw[op_1,op_3] >> irule opf_opf_refl >> arw[]
(* use is_gamma *))
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
(rpt strip_tac (* 2 *)
 >-- (irule opf_cpsb >> 
     qexistsl_tac [‘A’,‘f’,‘g’] >> arw[]) >>
 irule opf_oa >> arw[])
(form_goal 
 “∀A f:2->A g:2->A. cpsb(g,f) ⇒
  ∀A'. isop(A,A') ⇒ 
  ∀f' g':2->A'.isopf(f,f') & isopf(g,g') ⇒
 cpsb(f',g') ∧
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
