val Disc_def = qdefine_psym("Disc",[‘A’]) ‘!f:2->A. isid(f)’ |> gen_all;

val Epi_onto_obj = prove_store("Epi_onto_obj",
e0
(rw[Thm15])
(form_goal
 “!A B f:A->B. Epi(f) ==>
  !b:1->B. ?a:1->A. b = f o a”));

val fun_ext_alt = prove_store("fun_ext_alt",
e0
(rpt strip_tac >>
 irule $ iffLR fun_ext >>
 arw[])
(form_goal “∀A B f:A->B g. (∀a:2->A b. f o a = b ⇔ g o a = b) ⇒
 f = g”));

val CC5_uex = prove_store("CC5_uex",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?cf:A->B. ∀a:2->A b:2->B. R(a,b) ⇔ cf o a = b’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘cf’ >>
     rpt strip_tac >> arw[] >>
     irule fun_ext_alt >> 
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 irule CC5 >> arw[])
(form_goal
 “∀A B. 
 (∀f:2->A. ∃!g:2->B. R(f,g)) ∧
 (∀f:2->A g:2->B. R(f,g) ⇒ 
  R(id(dom(f)),id(dom(g))) ∧ R(id(cod(f)),id(cod(g)))) ∧
 (∀f:2->A g:2->A h: 2->B. cpsb(g,f) ⇒
  R(g @ f, h) ⇒ ∀f1 g1. R(f,f1) ∧ R(g,g1) ⇒ h = g1 @ f1) ⇒
 ?!cf:A->B. ∀a:2->A b:2->B. R(a,b) ⇔ cf o a = b”));

val fun_ext_Disc = prove_store("fun_ext_Disc",
e0
(rpt strip_tac >> fs[Disc_def] >>
 fs[isid_def] >>
 irule $ iffLR fun_ext >> strip_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >> fs[] >>
 arw[GSYM o_assoc])
(form_goal “∀A. Disc(A) ⇒ ∀B f:A->B g. 
 (∀a:1->A. f o a = g o a) ⇒ f = g”));


val to_Disc_determined_by_dom = prove_store("to_Disc_determined_by_dom",
e0
(rpt strip_tac >> fs[Disc_def,isid_def] >> 
 first_x_assum (qsspecl_then [‘f o a’] assume_tac) >>
 fs[] >> arw[dom_def,GSYM o_assoc] >> rw[id_def,o_assoc] >>
 qsuff_tac
 ‘f0 o To1(2) = f0 o (To1(2) o 0f) o To1(2)’ >-- rw[o_assoc] >>
 rw[one_to_one_Id,IdL])
(form_goal 
 “∀B. Disc(B) ⇒ 
  ∀A f:A->B a:2->A. f o a = id(f o dom(a))”));

val fun_ext_Disc' = prove_store("fun_ext_Disc'",
e0
(rpt strip_tac >>
 irule $ iffLR fun_ext >> strip_tac >>
 drule to_Disc_determined_by_dom >> arw[])
(form_goal “∀B. Disc(B) ⇒ ∀A f:A->B g. 
 (∀a:1->A. f o a = g o a) ⇒ f = g”));

val id_eq_eq = prove_store("id_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 fs[id_def] >>
 qby_tac
 ‘a1 o To1(2) o 0f = a2 o To1(2) o 0f’
 >-- arw[GSYM o_assoc] >>
 fs[one_to_one_Id,IdR])
(form_goal “∀A a1:1->A a2. id(a1) = id(a2) ⇔ a1 = a2”));

val id_dom = prove_store("id_dom",
e0
(rw[dom_def,id_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. dom(id(a)) = a”));


val id_cod = prove_store("id_cod",
e0
(rw[cod_def,id_def,o_assoc,one_to_one_Id,IdR])
(form_goal “∀A a:1->A. cod(id(a)) = a”));




val CC5_Disc_uex_lemma0 = proved_th $
e0
(rpt strip_tac >>
 uex_tac >> qexists_tac ‘g’ >> rpt strip_tac (* 2 *)
         >-- (qexistsl_tac [‘a1’,‘b1’]  >> arw[]) >>
         fs[id_eq_eq] >> rfs[] >>
         first_x_assum (qspecl_then [‘a1’] assume_tac) >>
         pop_assum (strip_assume_tac o uex_expand) >>
         qsuff_tac ‘b1' = b & b1 = b’ 
         >-- (rpt strip_tac >> arw[]) >>
         strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “Disc(A) & 
 (!(a : fun(1, A)). ?!(b : fun(1, B)). R(a, b)) & 
 (∃g:2->B.
        ∃a1 b1. f = id(a1) & g = id(b1) & R(a1,b1)) ==>
 ?!(g : fun(2, B)).
               ?(a1 : fun(1, A))  (b1 : fun(1, B)).
                 f = id(a1) & g = id(b1) & R(a1, b1)”)

val CC5_Disc_uex_lemma = proved_th $
e0
(rpt strip_tac >> 
 irule CC5_Disc_uex_lemma0 >> arw[] >> 
 first_x_assum 
     (qspecl_then [‘dom(f)’] (strip_assume_tac o uex2ex_rule)) >>
 qexistsl_tac [‘id(b)’,‘dom(f)’,‘b’] >> arw[] >>
 flip_tac >> fs[Disc_def,isid_alt])
(form_goal
 “Disc(A) & 
 (!(a : fun(1, A)). ?!(b : fun(1, B)). R(a, b))  ==>
 ?!(g : fun(2, B)).
               ?(a1 : fun(1, A))  (b1 : fun(1, B)).
                 f = id(a1) & g = id(b1) & R(a1, b1)”)



val CC5_Disc_uex = prove_store("CC5_Disc_uex",
e0
(rpt strip_tac >> 
 qsuff_tac
 ‘?cf:A->B. ∀a:1->A b:1->B. R(a,b) ⇔ cf o a = b’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘cf’ >> arw[] >>
      rpt strip_tac >> irule fun_ext_Disc >> arw[] >>
      pop_assum (assume_tac o GSYM) >> arw[]) >>
 assume_tac
 (CC5_uex |> qspecl [‘A’,‘B’] 
 |> fVar_sInst_th “R(f:2->A,g:2->B)”
    “∃a1:1->A b1:1->B. f = id(a1) & g = id(b1) & R(a1,b1)”) >>
 qsuff_tac
 ‘?!cf:A->B. 
   ∀a:2->A b:2->B.
    (∃a1:1->A b1:1->B. a = id(a1) & b = id(b1) & R(a1,b1)) ⇔ 
   cf o a = b’ 
 >-- (strip_tac >> 
     pop_assum (strip_assume_tac o uex2ex_rule) >>
     qexists_tac ‘cf’ >> 
     rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
     >-- (first_x_assum (qspecl_then [‘id(a)’,‘id(b)’] assume_tac) >>
         qsuff_tac ‘cf o id(a) = id(b)’ 
         >-- (rw[id_def] >>
             strip_tac >>
             qby_tac ‘(cf o a o To1(2)) o 0f = (b o To1(2)) o 0f’ 
             >-- arw[] >> fs[o_assoc,one_to_one_Id,IdR]) >>
         first_x_assum (irule o iffLR) >> 
         qexistsl_tac [‘a’,‘b’] >> arw[]) >>
     first_x_assum (qspecl_then [‘id(a)’,‘id(b)’] assume_tac) >>
   (*  fs[id_def] loop ,do not know why*)
     qsuff_tac ‘cf o id(a) = id(b)’ 
     >-- (strip_tac >> first_x_assum (drule o iffRL) >>
         pop_assum strip_assume_tac >> fs[id_eq_eq] (*slow*)) >>
     rw[id_def] >> arw[GSYM o_assoc]) >>
 first_x_assum irule >> rpt strip_tac (* 4 *)
 >-- (qexistsl_tac [‘a1’,‘b1’] >> arw[] >> rw[id_dom]) 
 >-- (qexistsl_tac [‘a1’,‘b1’] >> arw[] >> rw[id_cod]) 
 >-- (irule CC5_Disc_uex_lemma >> arw[]) 
(*qsuff_tac
     ‘∃g:2->B.
        ∃a1 b1. f = id(a1) & g = id(b1) & R(a1,b1)’
     >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> rpt strip_tac (* 2 *)
         >-- (qexistsl_tac [‘a1’,‘b1’]  >> arw[]) >>
         fs[id_eq_eq] >> rfs[] >>
         first_x_assum (qspecl_then [‘a1’] assume_tac) >>
         pop_assum (strip_assume_tac o uex_expand) >>
         qsuff_tac ‘b1' = b & b1 = b’ 
         >-- (rpt strip_tac >> arw[]) >>
         strip_tac >> first_x_assum irule >> arw[]) >>
     first_x_assum 
     (qspecl_then [‘dom(f)’] (strip_assume_tac o uex2ex_rule)) >>
     qexistsl_tac [‘id(b)’,‘dom(f)’,‘b’] >> arw[] >>
     flip_tac >> fs[Disc_def,isid_alt]*) >>
 fs[] >> 
 qby_tac ‘a1'' = a1’ 
 >-- (drule cpsb_idR >> fs[id_eq_eq])  >>
 qby_tac ‘a1' = a1’
 >-- (drule cpsb_idL >> fs[id_eq_eq]) >>
 fs[] >>
 qby_tac ‘b1' = b1’
 >-- (first_x_assum (qspecl_then [‘a1’] (strip_assume_tac o uex_expand)) >>
     qsuff_tac ‘b1 = b & b1' = b’
     >-- (strip_tac >> arw[]) >> strip_tac >> 
     first_x_assum irule >> arw[]) >>
 qby_tac ‘b1'' = b1’
 >-- (first_x_assum (qspecl_then [‘a1’] (strip_assume_tac o uex_expand)) >>
     qsuff_tac ‘b1 = b & b1'' = b’
     >-- (strip_tac >> arw[]) >> strip_tac >> 
     first_x_assum irule >> arw[]) >>
 arw[] >>
 flip_tac >> irule cpsb_idL >> rw[cpsb_def] >>
 rw[id_dom,id_cod] (*line by line okay, seems loop if as a whole cheat*) )
(form_goal
 “∀A. Disc(A) ==> !B. 
 (∀a:1->A. ∃!b:1->B. R(a,b)) ⇒
 ?!cf:A->B. ∀a:1->A b:1->B. R(a,b) ⇔ cf o a = b”));

(*
val CC5_Disc_uex = prove_store("CC5_Disc_uex",
e0
(rpt strip_tac >> 
  assume_tac
 (CC5_uex |> qspecl [‘A’,‘B’] 
 |> fVar_sInst_th “R(f:2->A,g:2->B)”
    “∃a1:1->A b1:1->B. f = id(a1) & g = id(b1) & R(a1,b1)”) >>
 qsuff_tac
 ‘?!cf:A->B. 
   ∀a:2->A b:2->B.
    (∃a1:1->A b1:1->B. a = id(a1) & b = id(b1) & R(a1,b1)) ⇔ 
   cf o a = b’ 
 >-- cheat >>
 first_x_assum irule >> rpt strip_tac (* 4 *)
 >-- cheat
 >-- cheat
 >-- (qsuff_tac
     ‘∃g:2->B.
        ∃a1 b1. f = id(a1) & g = id(b1) & R(a1,b1)’
     >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> rpt strip_tac (* 2 *)
         >-- cheat (*qexistsl_tac [‘a1’,‘b1’]  >> arw[]*) >>
         fs[id_eq_eq] >> rfs[] >>
         first_x_assum (qspecl_then [‘a1’] assume_tac) >>
         pop_assum (strip_assume_tac o uex_expand) >>
         qsuff_tac ‘b1' = b & b1 = b’ 
         >-- cheat (*rpt strip_tac >> arw[]*) >>
         strip_tac >> first_x_assum irule >> arw[]) >> cheat
     ) >> cheat  )
(form_goal
 “∀A. Disc(A) ==> !B. 
 (∀a:1->A. ∃!b:1->B. R(a,b)) ⇒
 ?!cf:A->B. ∀a:1->A b:1->B. R(a,b) ⇔ cf o a = b”));
*)




(*up to here, can have output, but very slow.*)




(*
proved_th $
e0
(rpt strip_tac >> 
  assume_tac
 (CC5_uex |> qspecl [‘A’,‘B’] 
 |> fVar_sInst_th “R(f:2->A,g:2->B)”
    “∃a1:1->A b1:1->B. f = id(a1) & g = id(b1) & R(a1,b1)”) >>
 first_x_assum irule >> rpt strip_tac (* 4 *)
 >-- cheat
 >-- cheat
 >-- (qsuff_tac
     ‘∃g:2->B.
        ∃a1 b1. f = id(a1) & g = id(b1) & R(a1,b1)’
     >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> rpt strip_tac (* 2 *)
         >-- (qexistsl_tac [‘a1’,‘b1’]  >> arw[]) >>
         fs[id_eq_eq] >> rfs[] >>
         first_x_assum (qspecl_then [‘a1’] assume_tac) >>
         pop_assum (strip_assume_tac o uex_expand) >>
         qsuff_tac ‘b1' = b & b1 = b’ 
         >-- (rpt strip_tac >> arw[]) >>
         strip_tac >> first_x_assum irule >> arw[]) >> cheat
     ) >> cheat)
(form_goal
“∀A. Disc(A) ==> !B. 
 (∀a:1->A. ∃!b:1->B. R(a,b)) ⇒
 ?!cf:A->B. 
   ∀a:2->A b:2->B.
    (∃a1:1->A b1:1->B. a = id(a1) & b = id(b1) & R(a1,b1)) ⇔ 
   cf o a = b”)


val CC5_Disc_uex = prove_store("CC5_Disc_uex",
e0
(rpt strip_tac >> 
 qsuff_tac
 ‘?cf:A->B. ∀a:1->A b:1->B. R(a,b) ⇔ cf o a = b’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘cf’ >> arw[] >>
      rpt strip_tac >> irule fun_ext_Disc >> arw[] >>
      pop_assum (assume_tac o GSYM) >> arw[]) >>
 assume_tac
 (CC5_uex |> qspecl [‘A’,‘B’] 
 |> fVar_sInst_th “R(f:2->A,g:2->B)”
    “∃a1:1->A b1:1->B. f = id(a1) & g = id(b1) & R(a1,b1)”) >>
 qsuff_tac
 ‘?!cf:A->B. 
   ∀a:2->A b:2->B.
    (∃a1:1->A b1:1->B. a = id(a1) & b = id(b1) & R(a1,b1)) ⇔ 
   cf o a = b’ 
 >-- (strip_tac >> 
     pop_assum (strip_assume_tac o uex2ex_rule) >>
     qexists_tac ‘cf’ >> 
     rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
     >-- (first_x_assum (qspecl_then [‘id(a)’,‘id(b)’] assume_tac) >>
         qsuff_tac ‘cf o id(a) = id(b)’ 
         >-- (rw[id_def] >>
             strip_tac >>
             qby_tac ‘(cf o a o To1(2)) o 0f = (b o To1(2)) o 0f’ 
             >-- arw[] >> fs[o_assoc,one_to_one_Id,IdR]) >>
         first_x_assum (irule o iffLR) >> 
         qexistsl_tac [‘a’,‘b’] >> arw[]) >>
     first_x_assum (qspecl_then [‘id(a)’,‘id(b)’] assume_tac) >>
   (*  fs[id_def] loop ,do not know why*)
     qsuff_tac ‘cf o id(a) = id(b)’ 
     >-- (strip_tac >> first_x_assum (drule o iffRL) >>
         pop_assum strip_assume_tac >> fs[id_eq_eq] (*slow*)) >>
     rw[id_def] >> arw[GSYM o_assoc]) >>
 first_x_assum irule >> rpt strip_tac (* 4 *)
 >-- (qexistsl_tac [‘a1’,‘b1’] >> arw[] >> rw[id_dom]) 
 >-- (qexistsl_tac [‘a1’,‘b1’] >> arw[] >> rw[id_cod]) 
 >-- qsuff_tac
     ‘∃g:2->B.
        ∃a1 b1. f = id(a1) & g = id(b1) & R(a1,b1)’
     >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> rpt strip_tac (* 2 *)
         >-- (qexistsl_tac [‘a1’,‘b1’]  >> arw[]) >>
         fs[id_eq_eq] >> rfs[] >>
         first_x_assum (qspecl_then [‘a1’] assume_tac) >>
         pop_assum (strip_assume_tac o uex_expand) >>
         qsuff_tac ‘b1' = b & b1 = b’ 
         >-- (rpt strip_tac >> arw[]) >>
         strip_tac >> first_x_assum irule >> arw[]) 
 >-- (qsuff_tac
     ‘∃g:2->B.
        ∃a1 b1. f = id(a1) & g = id(b1) & R(a1,b1)’
     >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> rpt strip_tac (* 2 *)
         >-- (qexistsl_tac [‘a1’,‘b1’]  >> arw[]) >>
         fs[id_eq_eq] >> rfs[] >>
         first_x_assum (qspecl_then [‘a1’] assume_tac) >>
         pop_assum (strip_assume_tac o uex_expand) >>
         qsuff_tac ‘b1' = b & b1 = b’ 
         >-- (rpt strip_tac >> arw[]) >>
         strip_tac >> first_x_assum irule >> arw[]) >>
     first_x_assum 
     (qspecl_then [‘dom(f)’] (strip_assume_tac o uex2ex_rule)) >>
     qexistsl_tac [‘id(b)’,‘dom(f)’,‘b’] >> arw[] >>
     flip_tac >> fs[Disc_def,isid_alt]) >>
 fs[] >> 
 qby_tac ‘a1'' = a1’ 
 >-- (drule cpsb_idR >> fs[id_eq_eq])  >>
 qby_tac ‘a1' = a1’
 >-- (drule cpsb_idL >> fs[id_eq_eq]) >>
 fs[] >>
 qby_tac ‘b1' = b1’
 >-- (first_x_assum (qspecl_then [‘a1’] (strip_assume_tac o uex_expand)) >>
     qsuff_tac ‘b1 = b & b1' = b’
     >-- (strip_tac >> arw[]) >> strip_tac >> 
     first_x_assum irule >> arw[]) >>
 qby_tac ‘b1'' = b1’
 >-- (first_x_assum (qspecl_then [‘a1’] (strip_assume_tac o uex_expand)) >>
     qsuff_tac ‘b1 = b & b1'' = b’
     >-- (strip_tac >> arw[]) >> strip_tac >> 
     first_x_assum irule >> arw[]) >>
 arw[] >>
 flip_tac >> irule cpsb_idL >> rw[cpsb_def] >>
 rw[id_dom,id_cod]  )
(form_goal
 “∀A. Disc(A) ==> !B. 
 (∀a:1->A. ∃!b:1->B. R(a,b)) ⇒
 ?!cf:A->B. ∀a:1->A b:1->B. R(a,b) ⇔ cf o a = b”));
*)

(*zf_ne_of,CC2_1*)
val zf_xor_of = prove_store("zf_xor_of",
e0
(strip_tac >> qcases ‘f = 0f’ >> arw[zf_ne_of] >>
 ccontra_tac >>
 qsspecl_then [‘id(f)’] strip_assume_tac CC2_1 (* 3 *) >> fs[id_def]
 >-- (qby_tac
     ‘f o To1(2) o 0f = 𝟘 o 0f’ 
     >-- arw[GSYM o_assoc] >>
     fs[zero_def,o_assoc,one_to_one_Id,IdR]) 
 >-- (qby_tac
     ‘f o To1(2) o 0f = 𝟙 o 0f’ 
     >-- arw[GSYM o_assoc] >>
     fs[one_def,o_assoc,one_to_one_Id,IdR]) >>
 qby_tac
 ‘f o To1(2) o 0f = 𝟚 o 0f’ 
 >-- arw[GSYM o_assoc] >>
 fs[two_def,o_assoc,one_to_one_Id,IdR,IdL])
(form_goal
 “!f:1->2. ~(f = 0f) <=> f = 1f”));


(*

val CC5_Disc_uex_one = prove_store("CC5_Disc_uex_one",
e0
(cheat)
(form_goal
 “∀A. Disc(A) ==> 
    !a0:1->A.
      ?!cf:A->2. ∀a:1->A. cf o a = 0f <=> a = a0”));
*)

val no_arrow_1f_to_0f = prove_store("no_arrow_1f_to_0f",
e0
(strip_tac >>
 qsspecl_then [‘f’] strip_assume_tac CC2_1 >> 
 arw[dom_cod_zot,zf_ne_of,GSYM zf_ne_of])
(form_goal
 “!f:2->2. ~(dom(f) = 1f & cod(f) = 0f)”));

(*So no arrow of Q goes from any other object*)
val no_arrow_from_other = prove_store("no_arrow_from_other",
e0
(rpt strip_tac >> ccontra_tac >>
 qsuff_tac
 ‘dom(f o g) = 1f & cod(f o g) = 0f’
 >-- rw[no_arrow_1f_to_0f] >>
 fs[dom_def,cod_def,o_assoc] >>
 first_x_assum irule >> arw[])
(form_goal
 “!A a0:1->A f:A-> 2.
  (f o a0 = 0f &
  (!a:1->A.  ~(a = a0) ==> f o a = 1f)) ==>
  !g:2->A. cod(g) = a0 ==> dom(g) = a0”));



val CC5_ap2_Thm20 = prove_store("CC5_ap2_Thm20",
e0
(rpt strip_tac >>
 assume_tac
 (CC5 |> qspecl [‘A’,‘A’] 
 |> fVar_sInst_th “R(f:2->A,g:2->A)”
    “g = id(dom(f:2->A))”) >>
 qsuff_tac ‘∃cf:A->A. ∀a b:2->A. b = id(dom(a)) ⇔ cf o a = b’ 
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum irule >> rpt strip_tac (* 4 *)
 >-- arw[]
 >-- (arw[] >> 
     first_x_assum (qspecl_then [‘cod(f)’,‘f’] assume_tac) >>
     fs[id_dom,id_cod])
 >-- (uex_tac >> qexists_tac ‘id(dom(f))’ >> rw[]) >>
 arw[] >> drule oa_dom_cod >> arw[] >>
 drule $ iffLR cpsb_def >> arw[] >> flip_tac >> 
 qsuff_tac
 ‘cod(f) = cod(id(dom(f)))’ 
 >-- (strip_tac >> once_arw[] >> rw[idL]) >>
 rw[id_cod] >>
 flip_tac >> first_x_assum irule >> rw[])
(form_goal
 “!A. 
    (!a:1->A f:2->A. cod(f) = a ==> dom(f) = a) ==>
    ∃F:A->A. ∀f:2->A. F o f = id(dom(f))”));

(*
val CC5_ap2_Thm20 = prove_store("CC5_ap2_Thm20",
e0
(rpt strip_tac >>
 )
(form_goal
 “!A. 
    (!a:1->A f:2->A. cod(f) = a ==> dom(f) = a) ==>
    !f:2->A. Id(A) o f = id(dom(f))”));
*)


val Disc_fac_eq = prove_store("Disc_fac_eq",
e0
(rpt strip_tac >>
 irule $ iffLR fun_ext >> strip_tac >>
 fs[Disc_def,isid_alt] >> rw[o_assoc] >>
 first_x_assum (qspecl_then [‘h o a’] assume_tac) >> fs[] >>
 first_x_assum (qspecl_then [‘f o a’] assume_tac) >> fs[] >> 
 qsuff_tac ‘g o id(dom(f o a))  = k o id(dom(h o a))’
 >-- arw[] >>
 rw[id_def,dom_def] >>
 qsuff_tac
 ‘g o ((f o a) o 0f) = k o ((h o a) o 0f)’ 
 >-- (strip_tac >> arw[GSYM o_assoc]) >>
 arw[o_assoc])
(form_goal
 “!A B f:A->B D g:B -> D
     C h:A->C   k:C -> D.
   Disc(B) & Disc(C) ==>
   (!a:1->A. g o f o a = k o h o a) ==> g o f = k o h”));

val CC5_Disc_uex' = CC5_Disc_uex |> strip_all_and_imp  
                                 |> disch_all 
                                 |> gen_all

val Thm20 = prove_store("Thm20",
e0
(rpt strip_tac >> fs[Disc_def] >>
 strip_tac >>
 qsuff_tac
 ‘∃F:Q->Q. ∀f:2->Q. F o f = id(dom(f))’ 
 >-- (strip_tac >> qsuff_tac ‘F' = Id(Q)’
     >-- (strip_tac >> fs[] >>
         qpick_x_assum
         ‘∀f:2->Q. Id(Q) o f = id(dom(f))’ mp_tac >>
         once_rw[IdL] >> strip_tac >>
         rw[isid_def] >> qexists_tac ‘dom(f)’ >>
         pop_assum (assume_tac o GSYM) >> fs[id_def]) >>
     drule $ iffLR iscoEq_def >>
     pop_assum strip_assume_tac >>
     first_x_assum drule >>
     pop_assum (strip_assume_tac o uex_expand) >>
     qsuff_tac
     ‘Id(Q) = x0 & F' = x0’
     >-- (strip_tac >> arw[]) >>
     strip_tac >> first_x_assum irule (* 2 *)
     >-- rw[IdL]>>
     irule $ iffLR fun_ext >> rpt strip_tac >> 
     first_assum (qspecl_then [‘a’] assume_tac) >>
     qpick_x_assum ‘q = x0 o q’ (assume_tac o GSYM) >> 
     drule $ iffLR isid_def >> 
     fs[] >> arw[o_assoc] >>
     rw[id_def,dom_def] >> 
     qby_tac
     ‘((q o f0 o To1(2)) o 0f) o To1(2) = 
      q o f0 o (To1(2) o 0f) o To1(2)’
     >-- rw[o_assoc] >> arw[one_to_one_Id,IdL]) >>
 irule CC5_ap2_Thm20 >>
 strip_tac >> match_mp_tac no_arrow_from_other >>
 qby_tac ‘?t:1->T. q o t = a’ 
 >-- (flip_tac >> irule Epi_onto_obj >>
     irule iscoEq_Epi >>
     qexistsl_tac [‘A’,‘F’,‘G’] >> arw[]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac
 ‘?g:T->2. 
  (!t'. q o t' = q o t ==> g o t' = 0f) &
  (!t'. ~(q o t' = q o t) ==> g o t' = 1f)’
 >-- (strip_tac >>
     drule $ iffLR iscoEq_def >> 
     pop_assum strip_assume_tac >> 
     qsuff_tac
     ‘g o F = g o G’
     >-- (strip_tac >>
         first_x_assum drule >> 
         pop_assum (assume_tac o uex2ex_rule) >>
         pop_assum (x_choose_then "g0" assume_tac) >>
         qexists_tac ‘g0’ >> rpt strip_tac (* 2 *)
         >-- (qpick_x_assum ‘q o t = a’ (assume_tac o GSYM) >> arw[] >>
             qpick_x_assum ‘g = g0 o q’ (assume_tac o GSYM) >> 
             arw[GSYM o_assoc] >> first_x_assum irule >> rw[]) >>
         qby_tac ‘?t1:1->T. q o t1 = a'’ 
         >-- (flip_tac >> irule Epi_onto_obj >>
              irule iscoEq_Epi >>
              qexistsl_tac [‘A’,‘F’,‘G’] >> arw[]) >>
         pop_assum strip_assume_tac >>
         pop_assum (assume_tac o GSYM) >> arw[] >>
         qpick_x_assum ‘g = g0 o q’ (assume_tac o GSYM) >> 
         arw[GSYM o_assoc] >>
         first_x_assum irule >> ccontra_tac >>
         fs[]) >>
     irule Disc_fac_eq >> arw[Disc_def] >>
     qby_tac
     ‘!a':1->A. q o F o a' = q o G o a'’
     >-- arw[GSYM o_assoc] >>
     strip_tac >> 
     qcases ‘q o F o a' = a’ (* 2 *)
     >-- (qby_tac ‘q o G o a' = a’ >-- rfs[] >>
         last_assum (qspecl_then [‘F o a'’] assume_tac) >>
         last_assum (qspecl_then [‘G o a'’] assume_tac) >>
         rfs[]) >>
     qby_tac ‘~(q o G o a' = a)’ >-- rfs[] >>
     first_assum (qspecl_then [‘F o a'’] assume_tac) >>
     first_assum (qspecl_then [‘G o a'’] assume_tac) >> 
     rfs[]) >>
 assume_tac
 (CC5_Disc_uex' |> qspecl [‘T’,‘2’]  
 |> fVar_sInst_th “R(t':1->T,b:1->2)”
    “(q:T->Q o t':1->T = q o t & b = 0f) |
     (~(q o t' = q o t) & b = 1f)”) >>
 rfs[Disc_def] >>
 qby_tac
 ‘!t':1-> T. 
  ?!b. (q:T->Q o t':1->T = q o t & b = 0f) |
     (~(q o t' = q o t) & b = 1f)’
 >-- (strip_tac >>
     qcases ‘q o t' = q o t’ >> arw[] (* 2 *)
     >-- (uex_tac >> qexists_tac ‘0f’ >> rw[]) >> 
     uex_tac >> qexists_tac ‘1f’ >> rw[]) >>rfs[] >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘cf’ >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rpt strip_tac (* 2 *)
 >> arw[])
(form_goal
 “!T. 
    Disc(T) ==>
    !A F:A->T G:A->T Q q:T->Q. 
      iscoEq(F,G,q) ==> Disc(Q)”));


(*val DISTI_EL = store_ax("DISTI_EL",“?X x1:1->X x2. ~(x1 = x2)”);*)
val i1_ne_i2 = prove_store("i1_ne_i2",
e0
(ccontra_tac >>
 assume_tac zf_ne_of >>
 qsuff_tac ‘0f = 1f’ >-- arw[] >>
 qby_tac ‘coPa(0f,1f) o i1(1,1) = 0f &
          coPa(0f,1f) o i2(1,1) = 1f’ >--
 rw[i12_of_coPa] >>
 pop_assum (assume_tac o GSYM) >> 
 qpick_x_assum ‘~(0f = 1f)’ (K all_tac) >> 
 once_arw[] >> pop_assum (K all_tac) >> arw[])
(form_goal
 “~(i1(1,1) = i2(1,1))”));

val i1_xor_i2_1 = prove_store("i1_xor_i2_1",
e0
(strip_tac >>
 qsspecl_then [‘id(x)’] assume_tac Thm16 >>
 fs[one_to_one_Id,To1_def,GSYM id_def,id_eq_eq] 
 >-- rw[i1_ne_i2] >> rw[GSYM i1_ne_i2])
(form_goal 
 “!x:1->1+1. x = i1(1,1) <=> ~(x = i2(1,1))”));


val i1_xor_i2' = prove_store("i1_xor_i2",
e0
(rw[i1_xor_i2_1])
(form_goal
 “∀x:1->1+1. ~(x = i1(1,1)) ⇔ x = i2(1,1)”));

val ar_of_11 = prove_store("ar_of_11",
e0
(strip_tac >>
 qsspecl_then [‘f’] assume_tac Thm16 >>
 fs[To1_def,GSYM id_def])
(form_goal “!f. f = id(i1(1,1)) | f = id(i2(1,1))”));


val i1_xor_i2_1_ar = prove_store("i1_xor_i2_1_ar",
e0
(strip_tac >>
 qsspecl_then [‘x’] assume_tac ar_of_11 >> fs[] 
 >-- fs[id_eq_eq,i1_ne_i2] >>
 fs[id_eq_eq,GSYM i1_ne_i2])
(form_goal 
 “!x:2->1+1. x = id(i1(1,1)) <=> ~(x = id(i2(1,1)))”));


val i1_xor_i2_ar' = prove_store("i1_xor_i2_ar'",
e0
(rw[i1_xor_i2_1_ar])
(form_goal
 “∀x:2->1+1. ~(x = id(i1(1,1))) ⇔ x = id(i2(1,1))”));

val to_2_eq = prove_store("to_2_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 irule $ iffLR fun_ext >> strip_tac >>  
 qcases ‘f1 o a = id(i1(1,1))’ 
 >-- (arw[] >> flip_tac >> ccontra_tac >> 
     drule $ iffLR i1_xor_i2_ar' >> 
     first_x_assum (qsspecl_then [‘dom(a)’] assume_tac) >>
     rfs[dom_def,GSYM o_assoc] >> fs[id_def,o_assoc,one_to_one_Id,IdR]) >>
 drule $ iffLR i1_xor_i2_ar' >> arw[] >> flip_tac >> ccontra_tac >>
 drule $ iffRL i1_xor_i2_1_ar >> 
 first_x_assum (qsspecl_then [‘dom(a)’] assume_tac) >>
 fs[GSYM o_assoc,dom_def] >> rfs[] >>
 fs[id_def,one_to_one_Id,IdR,o_assoc])
(form_goal
 “∀X f1:X->1+1 f2. f1 = f2 ⇔ 
     (∀x. f1 o x = i2(1,1) ⇔ f2 o x = i2(1,1))”));

val Thm21_isPb_char = prove_store("Thm21_isPb_char",
e0
(rpt strip_tac >>
 fs[isPb_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >> arw[GSYM o_assoc] >>
     rw[o_assoc,one_to_one_Id,IdR]) >>
 first_x_assum (qsspecl_then [‘d’,‘Id(1)’] assume_tac) >>
 rfs[IdR] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!D c:D->1+1 S i:S->D. isPb(c, i2(1, 1), i, To1(S)) ==>
  !d:1->D. (?s:1->S. i o s = d) <=> c o d = i2(1,1)”));

(*not really used
val FSC_Disc_Disc = prove_store("FSC_Disc_Disc",
e0
cheat
(form_goal “!D. Disc(D) ==>
            !S i:S->D. FSC(i) ==> Disc(S)”));
*)

val Disc_1 = prove_store("Disc_1",
e0
(rw[Disc_def,isid_def] >> 
 strip_tac >> qexists_tac ‘Id(1)’ >> rw[IdL,To1_def])
(form_goal “Disc(1)”));

(*
val i2_Mono = prove_store("i2_Mono",
e0
cheat
(form_goal “Mono(i2(1,1))”));
not really used
*)


val FSC_def = qdefine_psym("FSC",[‘i:S->A’])
‘Mono(i) & 
 !f:2->A d:1->S c:1->S. dom(f) = i o d & cod(f) = i o c ==> 
 ?f0:2->S. f = i o f0’ 
|> qgenl [‘S’,‘A’,‘i’]

val Thm21_char_isPb = prove_store("Thm21_char_isPb",
e0
(rpt strip_tac >>
 rw[isPb_def] >>
 qby_tac
 ‘c o i = i2(1, 1) o To1(S)’ 
 >-- (irule  Disc_fac_eq >> arw[Disc_1] >>
     strip_tac >> rw[one_to_one_Id,IdR] >>
     first_x_assum (irule o iffLR) >> qexists_tac ‘a’ >> rw[]) >>
 arw[] >>
 rpt strip_tac >> fs[one_to_one_Id,To1_def] >> 
 qsuff_tac
 ‘?a.i o a = u’
 >-- (fs[FSC_def,Mono_def] >> 
     rpt strip_tac >> uex_tac >> qexists_tac ‘a’ >> arw[] >>
     rpt strip_tac >> first_x_assum irule >> arw[]) >>
 assume_tac
 (CC5 |> qspecl [‘A’,‘S’] 
 |> fVar_sInst_th “R(f:2->A,g:2->S)”
    “i o g:2->S = u:A->D o f:2->A”) >> 
 qsuff_tac
 ‘?cf:A->S. !a:2->A b:2->S. i o b = u o a <=> cf o a = b’
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     irule $ iffLR fun_ext >> arw[o_assoc]) >>
 first_x_assum irule >> rpt strip_tac (* 4 *)
 >-- fs[id_def,dom_def,GSYM o_assoc]
 >-- fs[id_def,cod_def,GSYM o_assoc]
 >-- (*sufficient to prove existence by i is mono*)
    (qsuff_tac ‘?g:2->S. i o g = u o f’ 
    >-- (strip_tac >> uex_tac >> qexists_tac ‘g’ >> arw[] >>
        rpt strip_tac >> fs[FSC_def,Mono_def] >> 
        first_x_assum irule >> arw[]) >>
    first_x_assum (qspecl_then [‘dom(u o f)’] assume_tac) >>
    fs[dom_def] >> 
    qby_tac
    ‘c o (u o f) o 0f = i2(1, 1)’
    >-- (fs[GSYM o_assoc] >> rw[o_assoc,one_to_one_Id,IdR]) >>
    fs[] >>
    qexists_tac ‘id(s)’ >> fs[Disc_def] >>
    arw[id_def,GSYM o_assoc] >>
    rw[o_assoc] >>
    first_x_assum (qspecl_then [‘u o f’] assume_tac) >>
    fs[isid_def] >> fs[GSYM o_assoc] >> 
    qby_tac
    ‘((f0 o To1(2)) o 0f) o To1(2) = 
     f0 o (To1(2) o 0f) o To1(2)’
    >-- rw[o_assoc] >> 
    arw[one_to_one_Id,IdL]) >>
 qby_tac ‘cpsb(g1,f1)’ 
 >-- (rw[cpsb_def] >> drule $ iffLR FSC_def >> fs[] >>
     fs[Mono_def] >> first_x_assum irule >>
     rw[dom_def,cod_def] >> arw[GSYM o_assoc] >> 
     rw[o_assoc] >> rw[GSYM dom_def,GSYM cod_def] >>
     fs[cpsb_def]) >>
 drule fun_pres_oa >>
 first_x_assum (qsspecl_then [‘i’] assume_tac) >> rfs[] >>
 rev_drule fun_pres_oa >> 
 first_x_assum (qsspecl_then [‘u’] (assume_tac o GSYM)) >> fs[] >>
 fs[FSC_def,Mono_def] >> first_x_assum irule >> arw[])
(form_goal
 “!D. Disc(D) ==>
      !S i:S->D. FSC(i) ==>
  !c:D->1+1.
    (!d:1->D. (?s:1->S. i o s = d) <=> c o d = i2(1,1)) ==>
    isPb(c, i2(1, 1), i, To1(S))”));


val Thm21 = prove_store("Thm21",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?c:D -> 1+1. isPb(c,i2(1,1),i,To1(S))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘c’ >> arw[] >>
     rpt strip_tac >> 
     irule $ iffRL to_2_eq >>
     drule (GSYM Thm21_isPb_char) >>
     rev_drule (GSYM Thm21_isPb_char) >> arw[]) >>
 drule Thm21_char_isPb >>
 first_x_assum drule >>
 qsuff_tac
 ‘?c:D->1+1.
  !d:1->D.
  (?s:1->S. i o s = d) <=> c o d = i2(1,1)’
 >-- (strip_tac >>
     first_x_assum drule >> qexists_tac ‘c’ >> arw[]) >>
 assume_tac
 (CC5_Disc_uex' |> qspecl [‘D’,‘1+1’] 
 |> fVar_sInst_th “R(d:1->D,b:1->1+1)”
    “((?s:1->S. i o s = d:1->D) & b = i2(1,1))| 
     (~(?s:1->S. i o s = d) & b = i1(1,1))”) >>
 rfs[] >>
 qby_tac
 ‘!d:1->D.
  ?!b:1-> 1+1.
  ((?s:1->S. i o s = d:1->D) & b = i2(1,1))| 
     (~(?s:1->S. i o s = d) & b = i1(1,1))’
 >-- (strip_tac >> qcases ‘?s:1->S. i o s = d:1->D’ >> arw[] (* 2 *)
     >-- (uex_tac >> qexists_tac ‘i2(1,1)’ >> rw[]) >> 
     uex_tac >> qexists_tac ‘i1(1,1)’ >> rw[]) >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘cf’ >>  
 pop_assum (assume_tac o GSYM) >> arw[] >> strip_tac >>
 qcases ‘?s:1->S. i o s = d:1->D’ >> arw[] >>
 rw[GSYM i1_ne_i2])
(form_goal
 “!S D i:S->D. Disc(D) & FSC(i) ==>
  ?!c:D -> 1+1. isPb(c,i2(1,1),i,To1(S))”));


val SO_def = qdefine_psym("SO",[‘s:S->A’])
‘Mono(s) & Disc(S) &
 (!D d:D->A. Disc(D) ==> ?d0:D->S. d = s o d0)’
|> gen_all

val Thm22 = prove_store("Thm22",
e0
(rpt strip_tac >>
 qsspecl_then [‘q o s’,‘q o s’] assume_tac isPb_ex >>
 pop_assum (x_choosel_then ["K","s1","s2"] assume_tac) >>
 qsspecl_then [‘s1’,‘s2’] assume_tac iscoEq_ex >>
 pop_assum (x_choosel_then ["Qs","q0"] assume_tac) >>
 qby_tac ‘?qs0:Qs->Q. qs0 o q0 = q o s’ 
 >-- (fs[iscoEq_def] >>
     flip_tac >>
     qsuff_tac ‘?!qs0:Qs->Q. q o s = qs0 o q0’
     >-- (strip_tac >> pop_assum (strip_assume_tac o uex2ex_rule) >>
         qexists_tac ‘qs0’ >> arw[]) >>
     first_x_assum irule >> fs[isPb_def]) >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘Qs’,‘qs0’] >> rw[SO_def] >>
 qby_tac ‘Disc(Qs)’ 
 >-- (irule Thm20 >>
     qexistsl_tac [‘K’,‘S’,‘s1’,‘s2’,‘q0’] >> arw[] >> fs[SO_def]) >>
 arw[] >>
 qby_tac ‘Mono(qs0)’ >--
 (rw[Mono_def] >> rpt strip_tac >>
 irule fun_ext_Disc' >> arw[] >> strip_tac >>
 qabbrev_tac ‘g o a = t1’ >>
 qabbrev_tac ‘h o a = t2’ >> arw[] >>
 qby_tac ‘?t01:1->S. q0 o t01 = t1’ 
 >-- (flip_tac >> irule Thm15 >> drule iscoEq_Epi >> arw[]) >>
 pop_assum strip_assume_tac >> 
 qby_tac ‘?t02:1->S. q0 o t02 = t2’ 
 >-- (flip_tac >> irule Thm15 >> drule iscoEq_Epi >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘?k:1->K. s1 o k = t01 & s2 o k = t02’ 
 >-- (fs[isPb_def] >>
     qsuff_tac ‘?!k:1->K. s1 o k = t01 & s2 o k = t02’
     >-- (strip_tac >> pop_assum (strip_assume_tac o uex2ex_rule) >>
         qexists_tac ‘k’ >> arw[]) >>
     first_x_assum irule >> 
     qpick_x_assum ‘qs0 o q0 = q o s’ (assume_tac o GSYM) >> arw[] >>
     arw[o_assoc] >> 
     qpick_x_assum ‘g o a = t1’ (assume_tac o GSYM) >> 
     qpick_x_assum ‘h o a = t2’ (assume_tac o GSYM) >> 
     arw[] >> arw[GSYM o_assoc]) >>
 pop_assum strip_assume_tac >>
 qpick_x_assum ‘q0 o t01 = t1’ (assume_tac o GSYM) >>
 qpick_x_assum ‘q0 o t02 = t2’ (assume_tac o GSYM) >> 
 arw[] >>
 qpick_x_assum ‘s1 o k = t01’ (assume_tac o GSYM) >>
 qpick_x_assum ‘s2 o k = t02’ (assume_tac o GSYM) >> 
 arw[] >> fs[iscoEq_def] >> fs[GSYM o_assoc]) >>
 arw[] >> rpt strip_tac >>
 qsuff_tac ‘?d0:D->Qs. !od:1->D oqs:1->Qs. d o od = qs0 o oqs <=> d0 o od = oqs’
 >-- (strip_tac >> qexists_tac ‘d0’ >> 
     irule fun_ext_Disc >> arw[] >> strip_tac >> arw[o_assoc]) >>
 qsuff_tac
 ‘?!d0:D->Qs. !od:1->D oqs:1->Qs. d o od = qs0 o oqs <=> d0 o od = oqs’
 >-- (strip_tac >> pop_assum (strip_assume_tac o uex2ex_rule) >>
     qexists_tac ‘d0’ >> arw[]) >> 
 irule
 (CC5_Disc_uex' |> qspecl [‘D’,‘Qs’] 
 |> fVar_sInst_th “R(od:1->D,oqs:1->Qs)”
    “d:D->Q o od:1->D = qs0:Qs->Q o oqs”) >>
 arw[] >> strip_tac >>
 qsuff_tac ‘?(b : fun(1, Qs)). d o a = qs0 o b’ 
 >-- (strip_tac >> fs[Mono_def] >>
     uex_tac >> qexists_tac ‘b’ >> arw[] >>
     rpt strip_tac >> first_x_assum irule >> arw[]) >>
 qby_tac ‘?a0:1->A. d o a = q o a0’ 
 >-- (irule Thm15 >> rev_drule iscoEq_Epi >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘?a00:1->S. a0 = s o a00’
 >-- (fs[SO_def] >> first_x_assum irule >> rw[Disc_1]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘q0 o a00’ >> arw[] >>
 fs[GSYM o_assoc])
(form_goal
 “!A S s:S->A.SO(s) ==>
  !B f1 f2:B->A Q q:A->Q.  iscoEq(f1,f2,q) ==> ?S' s':S'->Q. SO(s')”));

val eq_opf_eq = prove_store("eq_opf_eq",
e0
(rpt strip_tac >> irule $ iffLR fun_ext >> strip_tac >>
rev_drule op_op_refl >>
drule opar_uex >> 
first_x_assum (qspecl_then [‘a’] assume_tac) >>
pop_assum (assume_tac o uex2ex_rule) >>
pop_assum (x_choose_then "a0" assume_tac) >> 
qsuff_tac ‘isopf(f o a0,fop o a) & isopf(g o a0,gop o a)’  
>-- (strip_tac >> rfs[] >>
    irule opar_unique >> qexistsl_tac [‘B’,‘g o a0’] >> arw[]) >>
strip_tac (* 2 *)
>-- (irule opf_o_opf >> arw[] >> irule opf_opf_refl >> arw[]) >>
(irule opf_o_opf >> arw[] >> irule opf_opf_refl >> arw[]))
(form_goal “isop(A,Aop) & isop(B,Bop) ==> 
 !f g:A->B. f = g ==>
 !fop gop:Aop->Bop. isopf(f,fop) & isopf(g,gop) ==> fop = gop”));


val opf_Mono_Mono = prove_store("opf_Mono_Mono",
e0
(rpt strip_tac >> fs[Mono_def] >> rpt strip_tac >>
 qspecl_then [‘X’] assume_tac op_ex >>
 pop_assum (x_choose_then "Xop" assume_tac) >>
 qspecl_then [‘X’,‘A'’,‘g’,‘Xop’,‘A’] assume_tac opf_uex >> rfs[] >>
 rev_drule op_op_refl >> first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "g0" assume_tac) >> 
 qspecl_then [‘X’,‘A'’,‘h’,‘Xop’,‘A’] assume_tac opf_uex >> rfs[] >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "h0" assume_tac) >> 
 qby_tac ‘f o g0 = f o h0’ 
 >-- (irule eq_opf_eq >>
     qexistsl_tac [‘X’,‘B'’,‘f' o g’,‘f' o h’] >> arw[] >>
     qspecl_then [‘B’,‘B'’] assume_tac op_op_refl >> 
     first_x_assum drule >> arw[] >> strip_tac (* 2 *)
     >-- (irule opf_o_opf >> arw[] >> irule opf_opf_refl >> arw[]) >>
     qpick_x_assum ‘f' o g = f' o h’ (assume_tac o GSYM) >> arw[] >>
     irule opf_o_opf >> arw[] >> irule opf_opf_refl >> arw[]) >>
 first_x_assum drule >> fs[] >>
 irule opf_unique >> qexistsl_tac [‘Xop’,‘A’,‘h0’] >>
 arw[] >> rpt strip_tac (* 3 *)
 >-- (irule opf_opf_refl >> arw[]) 
 >-- (irule op_op_refl >> arw[]) 
 >-- (irule opf_opf_refl >> arw[]))
(form_goal
 “!A B f:A->B. Mono(f) ==> 
  !A' B' f':A'->B'. isop(A,A') & isop(B,B') & isopf(f,f') ==>
  Mono(f')”));

val op_Disc_Disc = prove_store("op_Disc_Disc",
e0
(rpt strip_tac >> fs[Disc_def] >>
 strip_tac >> drule op_op_refl >>
 drule opar_uex >> 
 first_x_assum (qspecl_then [‘f’] assume_tac) >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "f0" assume_tac) >>
 drule isid_opf >> first_x_assum drule >> fs[])
(form_goal
 “!D. Disc(D) ==> !D'. isop(D,D') ==> Disc(D')”));

val Thm23_without_CC5 = prove_store("Thm23_without_CC5",
e0
(rpt strip_tac >> rw[SO_def] >>
 qby_tac ‘Mono(sop)’ 
 >-- (irule opf_Mono_Mono >> 
     qexistsl_tac [‘S’,‘A’,‘s’] >> fs[SO_def]) >> arw[] >>
 qby_tac ‘Disc(Sop)’ 
 >-- (irule op_Disc_Disc >> qexists_tac ‘S’ >> fs[SO_def]) >> arw[] >>
 rpt strip_tac >> 
 qspecl_then [‘D’] assume_tac op_ex >>
 pop_assum (x_choose_then "D0" assume_tac) >>
 drule op_Disc_Disc >>
 first_x_assum drule >>
 drule $ iffLR SO_def >> fs[] >>
 qspecl_then [‘D’,‘Aop’,‘d’,‘D0’,‘A’] assume_tac opf_uex >>
 rev_drule op_op_refl >> rfs[] >> first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "dop" assume_tac) >>
 first_x_assum (qsspecl_then [‘dop’] assume_tac) >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qspecl_then [‘D0’,‘S’,‘d0’,‘D’,‘Sop’] assume_tac opf_uex >>
 rfs[] >>
 qspecl_then [‘D’,‘D0’] assume_tac op_op_refl >>
 first_x_assum drule >>
 first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "d0op" assume_tac) >>
 qexists_tac ‘d0op’ >> 
 irule eq_opf_eq >>
 qexistsl_tac [‘D0’,‘A’,‘dop’,‘s o d0’] >>
 arw[] >> strip_tac (* 2 *)
 >-- (irule opf_o_opf >> arw[]) >>
 qpick_x_assum ‘dop = s o d0’ (assume_tac o GSYM) >> arw[] >>
 irule opf_opf_refl >>
 arw[])
(form_goal
 “!A S s:S->A. SO(s) ==> 
  !Aop Sop. isop(A,Aop) & isop(S,Sop) ==>
  !sop:Sop->Aop. isopf(s,sop) ==> SO(sop)”));

val Thm23_Iso_ex = prove_store("Thm23_Iso_ex",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘(?!i:D->Dop. !od:1->D odop:1->Dop. isopf(od,odop) <=> i o od = odop)’
 >-- (strip_tac >> pop_assum (strip_assume_tac o uex2ex_rule) >>
     qexists_tac ‘i’ >> arw[]) >>
 irule
 (CC5_Disc_uex' |> qspecl [‘D’,‘Dop’] 
 |> fVar_sInst_th “R(od:1->D,odop:1->Dop)”
    “isopf(od:1->D,odop:1->Dop)”) >> arw[] >>
 strip_tac >> irule opf_uex >> arw[op_1])
(form_goal
 “!D. Disc(D) ==> !Dop. isop(D,Dop) ==> 
  (?i:D->Dop. !od:1->D odop:1->Dop. isopf(od,odop) <=> i o od = odop)”));

val Thm23_with_CC5_1 = prove_store("Thm23_with_CC5_1",
e0
(rpt strip_tac >>
 drule Thm23_Iso_ex >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 drule op_Disc_Disc >>
 first_x_assum drule >>
 drule Thm23_Iso_ex >>
 drule op_op_refl >> first_x_assum drule >>
 pop_assum (x_choose_then "j" assume_tac) >>
 qexistsl_tac [‘i’,‘j’] >>
 arw[] >>
 qby_tac ‘(!od:1->D. isopf(od,i o od)) &
  (!odop:1->Dop. isopf(odop,j o odop))’ >-- arw[] >>
 arw[] >>
 strip_tac (* 2 *)
 >-- (irule fun_ext_Disc >> arw[IdL,o_assoc] >>
     strip_tac >>
     qpick_x_assum ‘!(od : fun(1, Dop))  (odop : fun(1, D)).
               isopf(od, odop) <=> j o od = odop’ (assume_tac o GSYM) >>
     arw[] >> irule opf_opf_refl >> arw[]) >>
 irule fun_ext_Disc >> arw[IdL,o_assoc] >>
 strip_tac >>
 qpick_x_assum ‘!(od : fun(1, D))  (odop : fun(1, Dop)).
               isopf(od, odop) <=> i o od = odop’ (assume_tac o GSYM) >> 
 arw[] >>
 irule opf_opf_refl >> arw[])
(form_goal 
 “!D. Disc(D) ==> !Dop. isop(D,Dop) ==> 
  ?i:D->Dop j:Dop->D. 
  (!od:1->D. isopf(od,i o od)) &
  (!odop:1->Dop. isopf(odop,j o odop)) &
  j o i = Id(D) & i o j = Id(Dop)”));

(*should I add an axiom saying A \cong B  ==> (isop(A,C) <=> isop(B,C))? *)


val Mono_o_Iso_Mono = prove_store("Mono_o_Iso_Mono",
e0
(rpt strip_tac >> fs[Mono_def] >> rpt strip_tac >>
 fs[o_assoc] >> first_x_assum drule >>
 fs[Iso_def] >>
 qby_tac ‘f' o i o g = f' o i o h’ >-- arw[] >>
 fs[GSYM o_assoc] >> rfs[IdL])
(form_goal “!A B f:A->B. Mono(f) ==> 
   !A' i:A'->A. Iso(i) ==> Mono(f o i)”));

val Thm23_with_CC5_2 = prove_store("Thm23_with_CC5_2",
e0
(rpt strip_tac >> 
 drule $ iffLR SO_def >> pop_assum strip_assume_tac >>
 drule Thm23_with_CC5_1 >>
 qspecl_then [‘S’] assume_tac op_ex >>
 pop_assum (x_choose_then "Sop" assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qspecl_then [‘S’,‘A’,‘s’,‘Sop’,‘Aop’] assume_tac opf_uex >>
 rfs[] >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "sop" assume_tac) >>
 qexists_tac ‘sop o i’ >> rw[SO_def] >> 
 qby_tac ‘Mono(sop o i)’ >--
 (qby_tac ‘Mono(sop)’ 
 >-- (irule opf_Mono_Mono >> qexistsl_tac [‘S’,‘A’,‘s’] >> arw[]) >>
 irule Mono_o_Iso_Mono >> arw[] >>
 rw[Iso_def] >> qexists_tac ‘j’ >> arw[]) >> arw[] >>
 rpt strip_tac >>
 rw[o_assoc] >> 
 qspecl_then [‘D’] assume_tac op_ex >>
 pop_assum (x_choose_then "Dop" assume_tac) >>
 drule op_Disc_Disc >>
 first_x_assum drule >>
 qspecl_then [‘D’,‘Aop’,‘d’,‘Dop’,‘A’] assume_tac opf_uex >>
 rfs[] >>
 rev_drule op_op_refl >>
 first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "dop" assume_tac) >>
 first_x_assum (qsspecl_then [‘dop’] assume_tac) >> 
 first_x_assum drule >>
 pop_assum (x_choose_then "d0op" assume_tac) >>
 qspecl_then [‘Dop’,‘S’,‘d0op’,‘D’,‘Sop’] assume_tac opf_uex >>
 rfs[] >>
 qspecl_then [‘D’,‘Dop’] assume_tac op_op_refl >>
 first_x_assum drule >> first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "d0" assume_tac) >>
 qexists_tac ‘j o d0’ >> 
 qsuff_tac ‘d = sop o (i o j) o d0’ >-- rw[o_assoc] >>
 arw[IdL] >>
 irule eq_opf_eq >>
 qexistsl_tac [‘Dop’,‘A’,‘dop’,‘s o d0op’] >> arw[] >>
 strip_tac (* 2 *)
 >-- (irule opf_o_opf >> arw[]) >>
 qpick_x_assum ‘dop = s o d0op’ (assume_tac o GSYM) >> arw[] >>
 irule opf_opf_refl >> arw[])
(form_goal 
 “!A S s:S->A. SO(s) ==>
  !Aop. isop(A,Aop) ==> ?s':S->Aop.SO(s')”));




