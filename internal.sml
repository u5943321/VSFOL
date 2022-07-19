
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


val isicat_def = 
define_pred
("isicat",
[‘d:Ar->Ob’,‘c:Ar->Ob’,‘iid:Ob->Ar’,‘io:Pbo(c,d) -> Ar’])
‘isPb(c,d,p1,p2) & 
 !’
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



