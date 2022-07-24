
val isPb_unique = proved_th $
e0
(cheat)
(form_goal
 “!X Z f:X->Z Y g:Y->Z
  P p:P->X q:P->Y P' p':P'->X q':P' ->Y. 
  isPb(f,g,p,q) & 
  isPb(f,g,p',q') ==>
  ?i: P-> P' j:P'->P. 
  i o j = Id(P') & j o i = Id(P) &
  p' o i = p & q' o i = q & 
  p o j = p' & q o j = q'
  ”)





val isPb_uex = proved_th $
e0
(cheat)
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
cheat
(form_goal “!P p:P->X q:P->Y.
 (?i: P-> P j:P->P. 
  i o j = Id(P) & j o i = Id(P) &
  p o i = p & q o i = q & 
  p o j = p & q o j = q)”)


val isPb_SYM = proved_th $
e0
cheat
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
cheat
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
(cheat)
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


val iidL_def = 
qdefine_psym("iidL",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘p1:Pb->C1’,‘p2:Pb->C1’,
 ‘r:Pb -> C1’])
‘isPb(d1,d0,p1,p2) &
?C01 pc0:C01->C0 pc1:C01->C1.
 isPb(Id(C0),d0,pc0,pc1) &
 !ci1. 
 p1 o ci1 = i o pc0 & 
 p2 o ci1 = pc1 ==>
 r o ci1 = pc1’


val iidR_def = 
qdefine_psym("iidR",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘p1:Pb->C1’,‘p2:Pb->C1’,
 ‘r:Pb -> C1’])
‘isPb(d1,d0,p1,p2) &
?C10 pc1:C10->C1 pc0:C10 ->C0.
 isPb(d1,Id(C0),pc1,pc0) &
 !c1i. 
 p1 o c1i = pc1 & 
 p2 o c1i = i o pc0 ==>
 r o c1i = pc1’


val iassoc_def = 
qdefine_psym("iassoc",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘p1:Pb->C1’,‘p2:Pb->C1’,
 ‘r:Pb -> C1’])
‘isPb(d1,d0,p1,p2) & 
 ?LPb pr12:LPb->Pb pr3:LPb->C1
  RPb pr1:RPb->C1 pr23:RPb->Pb.
  isPb(d1 o r,d0,pr12,pr3) & 
  isPb(d1, d0 o r, pr1,pr23) &
  !xr1:LPb->Pb x1r:RPb->Pb L2R:LPb->RPb.
  p1 o xr1 = r o pr12 &
  p2 o xr1 = pr3 & 
  p1 o x1r = pr1 & 
  p2 o x1r = r o pr23 & 
  pr1 o L2R = p1 o pr12 & 
  p1 o pr23 o L2R = p2 o pr12 & 
  p2 o pr23 o L2R = pr3==>
  r o xr1 = r o x1r o L2R’



val icat_def = 
qdefine_psym
("icat",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘p1:Pb->C1’,‘p2:Pb->C1’,
 ‘r:Pb -> C1’])
‘isPb(d1,d0,p1,p2) & 
 d0 o i = Id(C0) &
 d1 o i = Id(C0) &
 iidL(d0,d1,i,p1,p2,r) &
 iidR(d0,d1,i,p1,p2,r) &
 d0 o r = d0 o p2 &
 d1 o r = d1 o p1 & 
 iassoc(d0,d1,i,p1,p2,r)’




val icat_Icat_d0_0 = prove_store("icat_Icat_d0_0",
e0
(rpt strip_tac >> 
 qpick_x_assum
 ‘r o iso0 = r0’ (assume_tac o GSYM) >> arw[] >>
 arw[GSYM o_assoc] >> arw[o_assoc])
(form_goal 
 “!C1 C0 d0:C1->C0 d1:C1->C0 
   Pb p1:Pb-> C1 p2:Pb -> C1 r:Pb->C1 iso0 r0.
 isPb(d1, d0, p1, p2) & 
  d0 o r = d0 o p2 &
  r o iso0 = r0 & 
  p1 o iso0 = Pba1(d1,d0) & 
  p2 o iso0 = Pba2(d1,d0) ==> 
  d0 o r0 = d0 o Pba2(d1, d0) ”));




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


val Pba12_eq_eq = 
Pb12_eq_eq |> qspecl [‘X’,‘Z’,‘f:X->Z’,‘Y’,‘g:Y->Z’,
                      ‘Pbo(f:X->Z,g:Y->Z)’,‘Pba1(f:X->Z,g:Y->Z)’,
                      ‘Pba2(f:X->Z,g:Y->Z)’]
|> rewr_rule[Pb_def] 
|> gen_all



val icat_Icat_d0 = prove_store("icat_Icat_d0",
e0
(rpt strip_tac >>
 irule icat_Icat_d0_0 >>
 drule Pb_iso_iso0_ex >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘Pb’,‘iso0’,‘p1’,‘p2’,‘r’] >>
 arw[] >>
 qpick_x_assum ‘r0 o iso = r’ (assume_tac o GSYM) >>
 arw[o_assoc] >>
 qby_tac ‘iso' = iso’
 >-- (irule Pba12_eq_eq >> arw[]) >> fs[IdR]
 )
(form_goal 
 “!C1 C0 d0:C1->C0 d1:C1->C0 
   Pb p1:Pb-> C1 p2:Pb -> C1 r:Pb->C1 iso r0.
 isPb(d1, d0, p1, p2) & 
  d0 o r = d0 o p2 &
  r0 o iso = r & 
  Pba1(d1, d0) o iso = p1 & 
  Pba2(d1, d0) o iso = p2 ==> 
  d0 o r0 = d0 o Pba2(d1, d0) ”));



val icat_Icat = prove_store("icat_Icat",
e0
(rpt strip_tac >> rw[Icat_def] >> fs[icat_def] >>
 
 )
(form_goal
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1 
   Pb p1:Pb-> C1 p2:Pb -> C1 r:Pb->C1.
  icat(d0, d1, i, p1, p2, r) ==>
  !iso:Pb->Pbo(d1,d0) r0:Pbo(d1,d0) -> C1.
  Pba1(d1,d0) o iso = p1 & 
  Pba2(d1,d0) o iso = p2 & 
  r0 o iso = r ==>
  Icat(d0, d1, i,r0)”));


