val Pb12_eq_eq = proved_th $
e0
(rpt strip_tac >> fs[isPb_def] >>
 first_x_assum
 (qsspecl_then [‘p o t2’,‘q o t2’] assume_tac) >>
 rfs[GSYM o_assoc] >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘t1 = a & t2 = a’ >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “!X Z f:X->Z Y g:Y->Z
   P p:P->X q:P ->Y.
  isPb(f,g,p,q) ==>
  !T t1:T->P t2. p o t1 = p o t2 & q o t1 = q o t2 ==>
  t1 = t2”)


val isPb_unique = proved_th $
e0
(rpt strip_tac >>
 drule $ iffLR isPb_def >>
 pop_assum strip_assume_tac >>
 rev_drule $ iffLR isPb_def >>  
 pop_assum strip_assume_tac >>
 first_x_assum rev_drule >>
 first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choosel_then ["i"] assume_tac) >>
 first_x_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choosel_then ["j"] assume_tac) >>
 qexistsl_tac [‘i’,‘j’] >>
 arw[] >> strip_tac (*2 *)
 >-- (drule Pb12_eq_eq >> first_x_assum irule >>
     arw[GSYM o_assoc] >> rw[IdR]) >>
 rev_drule Pb12_eq_eq >> first_x_assum irule >>
 arw[GSYM o_assoc] >> rw[IdR])
(form_goal
 “!X Z f:X->Z Y g:Y->Z
  P p:P->X q:P->Y P' p':P'->X q':P' ->Y.
  isPb(f,g,p,q) &
  isPb(f,g,p',q') ==>
  ?i: P-> P' j:P'->P.
  i o j = Id(P') & j o i = Id(P) &
  p' o i = p & q' o i = q &
  p o j = p' & q o j = q'
  ”);


val isPb_unique' = proved_th $
e0
(rpt strip_tac >>
 qsspecl_then [‘f’,‘g’,‘p’,‘q’,‘p'’,‘q'’] assume_tac
 isPb_unique >> rfs[] >> qexistsl_tac [‘i’,‘j’] >> arw[])
(form_goal
 “!X Z f:X->Z Y g:Y->Z
  P p:P->X q:P->Y.
  isPb(f,g,p,q) ==>
  !P' p':P'->X q':P' ->Y.
  isPb(f,g,p',q') ==>
  ?i: P-> P' j:P'->P.
  i o j = Id(P') & j o i = Id(P) &
  p' o i = p & q' o i = q &
  p o j = p' & q o j = q'
  ”);


val isPb_uex = proved_th $
e0
(rpt strip_tac >>
 qsspecl_then [‘f’,‘g’] strip_assume_tac isPb_ex  >>
 qexistsl_tac [‘P’,‘p’,‘q’]  >> arw[] >>
 rpt strip_tac >>
 rev_drule isPb_unique' >>
 first_x_assum drule >> arw[])
(form_goal
 “!X Z f:X->Z Y g:Y->Z.
  ?P p:P->X q:P->Y.
  isPb(f,g,p,q) &
  !P' p':P'->X q':P' ->Y.
  isPb(f,g,p',q') ==>
  ?i: P-> P' j:P'->P.
  i o j = Id(P') & j o i = Id(P) &
  p' o i = p & q' o i = q &
  p o j = p' & q o j = q'
  ”)



val isPb_REFL = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘Id(P)’,‘Id(P)’] >>
 rw[IdR])
(form_goal “!P p:P->X q:P->Y.
 (?i: P-> P j:P->P.
  i o j = Id(P) & j o i = Id(P) &
  p o i = p & q o i = q &
  p o j = p & q o j = q)”)


val isPb_SYM = proved_th $
e0
(rpt strip_tac >>
 qexistsl_tac [‘j’,‘i’] >> arw[])
(form_goal “!P p:P->X q:P->Y P' p':P'->X q':P'-> Y.
 (?i: P-> P' j:P'->P.
  i o j = Id(P') & j o i = Id(P) &
  p' o i = p & q' o i = q &
  p o j = p' & q o j = q') ==>
 (?i: P'-> P j:P->P'.
  i o j = Id(P) & j o i = Id(P') &
  p o i = p' & q o i = q' &
  p' o j = p & q' o j = q)
 ”)


val isPb_TRANS = proved_th $
e0
(rpt strip_tac >>
 qexistsl_tac [‘i' o i’,‘j o j'’] >>
 arw[GSYM o_assoc] >>
 qsuff_tac
 ‘i' o (i o j) o j' = Id(P'') &
  j o (j' o i') o i = Id(P)’ >-- rw[o_assoc] >>
 arw[] >> rw[IdL] >> arw[])
(form_goal
“!P p:P->X q:P->Y
  P' p':P' ->X q':P'-> Y
  P'' p'':P'' ->X q'':P''-> Y.
 (?i: P-> P' j:P'->P.
  i o j = Id(P') & j o i = Id(P) &
  p' o i = p & q' o i = q &
  p o j = p' & q o j = q') &
 (?i: P'-> P'' j:P''->P'.
  i o j = Id(P'') & j o i = Id(P') &
  p'' o i = p' & q'' o i = q' &
  p' o j = p'' & q' o j = q'') ==>
 (?i: P-> P'' j:P''->P.
  i o j = Id(P'') & j o i = Id(P) &
  p'' o i = p & q'' o i = q &
  p o j = p'' & q o j = q'')
 ”)


val isPb_Reqv = conjI isPb_REFL (conjI isPb_SYM isPb_TRANS)




local
val uexth = isPb_uex |> spec_all
val eth = proved_th $
e0
(rpt strip_tac >>
 qsspecl_then [‘f’,‘g’] strip_assume_tac isPb_ex >>
 qexistsl_tac [‘P’,‘p’,‘q’] >> rw[])
(form_goal “∀X Z f:X->Z Y g:Y->Z. ∃P p:P->X q:P->Y.T”)
val eqvth = isPb_Reqv
val fnames = ["Pbo","Pba1","Pba2"]
val arg1 = List.map (dest_var o rastt)
                    ["P","p:P->X","q:P->Y"]
val arg2 = List.map (dest_var o rastt)
                     ["P'","p':P'->X","q':P'->Y"]
val eqr =
“(?i: P-> P' j:P'->P.
  i o j = Id(P') & j o i = Id(P) &
  p':P'->X o i = p:P->X & q':P'->Y o i = q:P->Y &
  p o j = p' & q o j = q')”
val arg = arg1
val Q = “isPb(f:X->Z,g:Y->Z,p:P->X,q:P->Y)”
val argQ = (arg,Q)
val vl = List.map dest_var [rastt "f:X->Z",rastt "g:Y->Z"]
val arg12eqr = (arg1,arg2,eqr)
val uexth = (isPb_uex |> spec_all)
in
(*val reflth = isPb_REFL
val symth = isPb_SYM
val transth = isPb_TRANS
val argseqr = (arg1,arg2,eqr) *)
val Pb_def =
new_spec argQ arg12eqr fnames vl (eth|> spec_all) eqvth uexth
|> gen_all
end


val Pb_iso_iso0_ex0 = proved_th $
e0
(rpt strip_tac >> match_mp_tac isPb_unique >>
 qexistsl_tac [‘Z’,‘f’,‘g’] >> arw[Pb_def])
(form_goal
 “!X Z f:X->Z Y g:Y->Z
   P p:P->X q:P ->Y.
  isPb(f,g,p,q) ==>
  ?iso: P-> Pbo(f,g) iso0:Pbo(f,g) ->P.
  iso o iso0 = Id(Pbo(f,g)) & iso0 o iso = Id(P) &
  Pba1(f,g) o iso = p & Pba2(f,g) o iso = q &
  p o iso0 = Pba1(f,g) & q o iso0 = Pba2(f,g)”)


val Pb_iso_iso0_ex = proved_th $
e0
(rw[Pb_iso_iso0_ex0])
(form_goal
 “!X Z f:X->Z Y g:Y->Z
   P p:P->X q:P ->Y.
  isPb(f,g,p,q) ==>
  ?iso: P-> Pbo(f,g) iso0:Pbo(f,g) ->P.
  iso o iso0 = Id(Pbo(f,g)) & iso0 o iso = Id(P) &
  Pba1(f,g) o iso = p & Pba2(f,g) o iso = q &
  p o iso0 = Pba1(f,g) & q o iso0 = Pba2(f,g)”)


val Pba12_eq_eq =
Pb12_eq_eq |> qspecl [‘X’,‘Z’,‘f:X->Z’,‘Y’,‘g:Y->Z’,
                      ‘Pbo(f:X->Z,g:Y->Z)’,‘Pba1(f:X->Z,g:Y->Z)’,
                      ‘Pba2(f:X->Z,g:Y->Z)’]
|> rewr_rule[Pb_def]
|> gen_all


val through_Pb = prove_store("through_Pb",
e0
(rpt strip_tac >>
 fs[isPb_def] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum drule >>
     pop_assum (assume_tac o uex2ex_rule) >> arw[]) >>
 qpick_x_assum ‘p o a0 = a1’ (assume_tac o GSYM) >>
 arw[GSYM o_assoc] >> arw[o_assoc])
(form_goal “!X Z f:X->Z Y g:Y->Z P p:P->X q:P->Y.
 isPb(f,g,p,q) ==>
 !A a1:A->X a2:A->Y.
  f o a1 = g o a2 <=>
  ?a0:A->P. p o a0 = a1 & q o a0 = a2”));


val Pb_eqn = prove_store("Pb_eqn",
e0
(rpt strip_tac >>
 qsspecl_then [‘f’,‘g’] assume_tac Pb_def >>
 fs[isPb_def])
(form_goal “!X Z f:X->Z Y g:Y->Z.
  f o Pba1(f,g) = g o Pba2(f,g)”));
