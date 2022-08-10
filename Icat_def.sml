val IidL_def =
qdefine_psym("IidL",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘gamma:Pbo(d1:C1->C0,d0:C1->C0) -> C1’])
‘!ci1:Pbo(Id(C0),d0) -> Pbo(d1,d0).
 Pba1(d1,d0) o ci1 = i o Pba1(Id(C0),d0) &
 Pba2(d1,d0) o ci1 = Pba2(Id(C0),d0) ==>
 gamma o ci1 = Pba2(Id(C0),d0)’;


val IidR_def =
qdefine_psym("IidR",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘gamma:Pbo(d1:C1->C0,d0:C1->C0) -> C1’])
‘!c1i:Pbo(d1,Id(C0)) -> Pbo(d1,d0).
 Pba1(d1,d0) o c1i = Pba1(d1,Id(C0)) &
 Pba2(d1,d0) o c1i = i o Pba2(d1,Id(C0)) ==>
 gamma o c1i = Pba1(d1,Id(C0))’;


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
  Pba2(d1,d0) o Pba1(d1 o gamma,d0)
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
 d0 o gamma = d0 o Pba1(d1,d0) &
 d1 o gamma = d1 o Pba2(d1,d0) &
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

