
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
 Iassoc(d0,d1,i,gamma)’
 

val Ipreso_def = qdefine_psym("Ipreso",
[‘cd0:C1->C0’,‘cd1:C1->C0’,‘ci:C0->C1’,
 ‘cr:Pbo(cd1:C1->C0,cd0:C1->C0) -> C1’,
 ‘dd0:D1->D0’,‘dd1:D1->D0’,‘di:D0->D1’,
 ‘dr:Pbo(dd1:D1->D0,dd0:D1->D0) -> D1’,
 ‘f0:C0->D0’,‘f1:C1->D1’])
‘!ff1:Pbo(cd1,cd0) -> Pbo(dd1,dd0).
 Pba1(dd1,dd0) o ff1 = f1 o Pba1(cd1,cd0) &
 Pba2(dd1,dd0) o ff1 = f1 o Pba2(cd1,cd0)
 ==>
 dr o ff1 = f1 o cr’


val IFun_def = qdefine_psym("IFun",
[‘cd0:C1->C0’,‘cd1:C1->C0’,‘ci:C0->C1’,
 ‘cr:Pbo(cd1:C1->C0,cd0:C1->C0) -> C1’,
 ‘dd0:D1->D0’,‘dd1:D1->D0’,‘di:D0->D1’,
 ‘dr:Pbo(dd1:D1->D0,dd0:D1->D0) -> D1’,
 ‘f0:C0->D0’,‘f1:C1->D1’])
‘Icat(cd0,cd1,ci,cr) & Icat(dd0,dd1,di,dr) &
 dd0 o f1 = f0 o cd0 & 
 dd1 o f1 = f0 o cd1 &
 di o f0 = f1 o ci & 
 Ipreso(cd0, cd1, ci, cr, dd0, dd1, di, dr, f0, f1)’


val ISC_def = 
qdefine_psym
("ISC",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘gamma:Pbo(d1:C1->C0,d0:C1->C0) -> C1’])
‘Icat(d0,d1,i,gamma) & Disc(C0) & Disc(C1)’
 
val Id0_def = qdefine_fsym("Id0",[‘A’])
‘Er1(A) o Ed(0f,A)’

val Id1_def = qdefine_fsym("Id1",[‘A’])
‘Er1(A) o Ed(1f,A)’



val pb2tri_tri2pb_ex = proved_th $
e0
(cheat)
(form_goal
 “?pb2tri: Pbo(Id1(A),Id0(A)) -> Exp(3,A)
   tri2pb:Exp(3,A)-> Pbo(Id1(A),Id0(A)). 
  pb2tri o tri2pb = Id(Exp(3,A)) & 
  tri2pb o pb2tri = Id(Pbo(Id1(A),Id0(A))) &
  Ed(α,A) o pb2tri = Pba1(Id1(A),Id0(A)) & 
  Ed(β,A) o pb2tri = Pba2(Id1(A),Id0(A)) & 
  Pba1(Id1(A),Id0(A)) o tri2pb = Ed(α,A) &
  Pba2(Id1(A),Id0(A)) o tri2pb = Ed(β,A)
  ”)



val pb2tri_uex = proved_th $
e0
(cheat)
(form_goal
 “?!pb2tri: Pbo(Id1(A),Id0(A)) -> Exp(3,A).
   ?tri2pb:Exp(3,A)-> Pbo(Id1(A),Id0(A)). 
  pb2tri o tri2pb = Id(Exp(3,A)) & 
  tri2pb o pb2tri = Id(Pbo(Id1(A),Id0(A))) &
  Ed(α,A) o pb2tri = Pba1(Id1(A),Id0(A)) & 
  Ed(β,A) o pb2tri = Pba2(Id1(A),Id0(A)) & 
  Pba1(Id1(A),Id0(A)) o tri2pb = Ed(α,A) &
  Pba2(Id1(A),Id0(A)) o tri2pb = Ed(β,A)
  ”)
|> qsimple_uex_spec "pb2tri" [‘A’]


val tri2pb_def = proved_th $
e0
(cheat)
(form_goal
 “?!tri2pb:Exp(3,A)-> Pbo(Id1(A),Id0(A)). 
  pb2tri(A) o tri2pb = Id(Exp(3,A)) & 
  tri2pb o pb2tri(A) = Id(Pbo(Id1(A),Id0(A))) &
  Ed(α,A) o pb2tri(A) = Pba1(Id1(A),Id0(A)) & 
  Ed(β,A) o pb2tri(A) = Pba2(Id1(A),Id0(A)) & 
  Pba1(Id1(A),Id0(A)) o tri2pb = Ed(α,A) &
  Pba2(Id1(A),Id0(A)) o tri2pb = Ed(β,A)
  ”)
|> qsimple_uex_spec "tri2pb" [‘A’]



val Ir_def = qdefine_fsym("Ir",[‘A’])
‘Ed(γ,A) o pb2tri(A)’


val Ii_def = qdefine_fsym("Ii",[‘A’])
‘Tp(p2(2,A))’

val C2Icat_cl12 = proved_th $
e0
(rw[Ii_def,Id1_def,Id0_def,Er1_def,Ed_def,o_assoc,
    Pa_distr,p12_of_Pa,To1_def,IdL,Ev_of_Tp_el,Ev_of_Tp_el'])
(form_goal “Id0(A) o Ii(A) = Id(A) & 
           Id1(A) o Ii(A) = Id(A)”)




val C2Icat_cl3 = proved_th $
e0
(rw[IidL_def] >> rpt strip_tac >> 
 )
(form_goal “IidL(Id0(A), Id1(A), Ii(A), Ir(A))”)


val C2Icat = prove_store("C2Icat",
e0
(strip_tac >> rw[Icat_def] >>
 )
(form_goal “!A.Icat(Id0(A),Id1(A),Ii(A),Ir(A))”));

(*
rastt "Id0(A)"; sort_of it;
rastt "Id1(A)"; sort_of it;
rastt "Ir(A)"; sort_of it;
*)

val Sq_def = qdefine_fsym("Sq",[‘F:A->B’])
‘Tp(F o Ev(2,A))’

(*rastt "Sq(F:A->B)" sort_of it*)

val Thm24 = prove_store("Thm24",
e0
(rpt strip_tac >>
 qby_tac ‘!aob:1->Exp(2,A). G o aob = Sq(F) o aob’ 
 >-- cheat >>
 fs[IFun_def] >>
 irule $ iffLR fun_ext >> strip_tac >>
 irule $ iffLR Pt_eq_eq >>
 irule cs_ext >> 
 
 )
(form_goal
 “!A B F:A->B G. 
  IFun(Id0(A),Id1(A),Ii(A),Ir(A),
       Id0(B),Id1(B),Ii(B),Ir(B),F,G) ==>
   G = Sq(F)”));

val Thm25 = prove_store("Thm25",
e0
()
(form_goal
 “!A T t:T->Exp(2,A). SO(t) ==>
  !S s:S->A.SO(s) ==>
  ?td0:T->S td1:T->S ti:S->T tr:Pbo(td1,td0) -> T. 
  ISC(td0,td1,ti,tr) & 
  IFun(td0,td1,ti,tr,Id0(A),Id1(A),Ii(A),Ir(A),s,t)”));

val Thm26 = prove_store("Thm26",
e0
()
(form_goal 
 “!A Ta ta:Ta->Exp(2,A) Sa sa:Sa->A
   B Tb tb:Tb->Exp(2,B) Sb sb:Sb->B. 
  SO(ta) & SO(sa) & SO(tb) & SO(sb) &
  !S s:S->A.SO(s) ==>
  !td0:T->S td1:T->S ti:S->T tr:Pbo(td1,td0) -> T. 
  ISC(td0,td1,ti,tr) & 
  IFun(td0,td1,ti,tr,Id0(A),Id1(A),Ii(A),Ir(A),s,t)”));

(*
rastt "Pba2(Id(C0),d0:C1->C0)" fun(Pbo(Id(C0), d0), C1)
rastt " gamma o ci1"

rastt "Pba1(d1,d0) o ci1:Pbo(Id(C0),d1) -> Pbo(d1:C1->C0,d0:C1->C0)"  fun(Pbo(Id(C0), d1), C1)

*)

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



