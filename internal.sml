
(*proposed soluion as alternative to choose a pullback object to reduce the parameters, and build the whole diagram,

but may need to prove this approach does give such a diagram to show it works...*)


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
 ‘gamma:Pbo(d1:C1->C0,d0:C1->C0) -> C1’])
‘!ci1:Pbo(Id(C0),d0) -> Pbo(d1,d0). 
 Pba1(d1,d0) o ci1 = i o Pba1(Id(C0),d0) & 
 Pba2(d1,d0) o ci1 = Pba2(Id(C0),d0) ==>
 gamma o ci1 = Pba2(Id(C0),d0)’


val IidR_def = 
qdefine_psym("IidR",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘gamma:Pbo(d1:C1->C0,d0:C1->C0) -> C1’])
‘!c1i:Pbo(d1,Id(C0)) -> Pbo(d1,d0). 
 Pba1(d1,d0) o c1i = Pba1(d1,Id(C0)) & 
 Pba2(d1,d0) o c1i = i o Pba2(d1,Id(C0)) ==>
 gamma o c1i = Pba1(d1,Id(C0))’


val Iassoc_def = 
qdefine_psym("Iassoc",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘gamma:Pbo(d1:C1->C0,d0:C1->C0) -> C1’])
‘!cr1:Pbo(d1 o gamma,d0) -> Pbo(d1,d0) 
  aiso
  c1r:Pbo(d1,d0 o gamma) -> Pbo(d1,d0). 
  Pba1(d1,d0) o cr1 = gamma o Pba1(d1 o gamma,d0) &
  Pba2(d1,d0) o cr1 = Pba2(d1 o gamma,d0) ==>
  gamma o cr1 = gamma o c1r o aiso’

val Icat_def = 
qdefine_psym
("Icat",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘gamma:Pbo(d1:C1->C0,d0:C1->C0) -> C1’])
‘d0 o i = Id(C0) &
 d1 o i = Id(C0) &
 IidL(d0,d1,i,gamma) & IidR(d0,d1,i,gamma) &
 d0 o gamma = d0 o Pba2(d1,d0) &
 d1 o gamma = d1 o Pba1(d1,d0) & 
 ’


rastt "Pba2(Id(C0),d0:C1->C0)" fun(Pbo(Id(C0), d0), C1)
rastt " gamma o ci1"

rastt "Pba1(d1,d0) o ci1:Pbo(Id(C0),d1) -> Pbo(d1:C1->C0,d0:C1->C0)"  fun(Pbo(Id(C0), d1), C1)

val is_o_def = 


store_ax("is_o_def", (*should be define_pred*)
“∀Ar Ob d:Ar -> Ob c:Ar -> Ob
  P π1:P (*Ar *_Ob Ar -> Ar*) -> Ar π2:P -> Ar cps:P -> Ar X a1:X->Ar a2:X-> Ar a:X->Ar.
  is_o(a1,a2,a,cps) ⇔ 
  isPb(d,c,π1,π2) ∧ 
  d o a2 = c o a1 ∧ 
  a = cps o Pba(d,c,π1,π2,a1,a2)”);

(*use big product instead*)
val is_intcat_def = store_ax("is_intcat_def",
“∀Ar Ob d:Ar -> Ob c:Ar -> Ob
  P π1:P -> Ar π2:P -> Ar cps:P -> Ar id:Ob -> Ar.
 is_intcat(d,c,id,π1,π2,cps) ⇔ 
 ∀X a1:X->Ar a2:X->Ar a3:X-> Ar a12 a23 a123.
 is_o(a1,a2,a12,cps) ∧ is_o(a2,a3,a23,cps) ⇒
 is_o(a1,a23,a123,cps) ∧ is_o(a12,a3,a123,cps)”);



