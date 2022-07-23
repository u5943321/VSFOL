
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


val IidL_def = 
qdefine_psym("IidL",
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


val IidR_def = 
qdefine_psym("IidR",
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


val Iassoc_def = 
qdefine_psym("Iassoc",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘p1:Pb->C1’,‘p2:Pb->C1’,
 ‘r:Pb -> C1’])
‘?Lpb p12:LPb->Pb p3:Lpb->C1.
  isPb()


!cr1:Pbo(d1 o gamma,d0) -> Pbo(d1,d0) 
  aiso
  c1r:Pbo(d1,d0 o gamma) -> Pbo(d1,d0). 
  Pba1(d1,d0) o cr1 = gamma o Pba1(d1 o gamma,d0) &
  Pba2(d1,d0) o cr1 = Pba2(d1 o gamma,d0) &
  Pba1(d1,d0) o c1r = Pba1(d1,d0 o gamma) &
  Pba2(d1,d0) o c1r = gamma o Pba2(d1,d0 o gamma) &
  Pba1(d1,d0 o gamma) o aiso = 
  Pba1(d1,d0) o Pba1(d1 o gamma,d0) & 
  Pba1(d1,d0) o Pba2(d1,d0 o gamma) o aiso = 
  Pba1(d1,d0) o Pba1(d1 o gamma,d0)
  & 
  Pba2(d1,d0) o Pba2(d1,d0 o gamma) o aiso = 
  Pba2(d1 o gamma,d0)
   ==>
  gamma o cr1 = gamma o c1r o aiso’
