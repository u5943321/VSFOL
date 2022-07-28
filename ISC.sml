
val ISC_def = 
qdefine_psym
("ISC",
[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,
 ‘gamma:Pbo(d1:C1->C0,d0:C1->C0) -> C1’])
‘Icat(d0,d1,i,gamma) & Disc(C0) & Disc(C1)’
 


val C2Icat_IidL_alt = 
IidL_alt |> qsspecl [‘Id0(A)’,‘Id1(A)’,‘Ii(A)’,‘Ir(A)’]
         |> rewr_rule[C2ICat_cod,C2ICat_dom,C2Icat_cl12]


val C2Icat_IidR_alt = 
IidR_alt |> qsspecl [‘Id0(A)’,‘Id1(A)’,‘Ii(A)’,‘Ir(A)’]
         |> rewr_rule[C2ICat_cod,C2ICat_dom,C2Icat_cl12]


val C2Icat_Iassoc_alt = 
Iassoc_alt |> qsspecl [‘Id0(A)’,‘Id1(A)’,‘Ii(A)’,‘Ir(A)’]
         |> rewr_rule[C2ICat_cod,C2ICat_dom,C2Icat_cl12]


val tt_ex = prove_store("tt_ex",
e0
(rpt strip_tac >>
 qby_tac ‘Id1(A) o t o Pba1(td1, td0) = Id0(A) o t o Pba2(td1, td0)’ 
 >-- (qpick_x_assum ‘s o td0 = Id0(A) o t’ (assume_tac o GSYM) >>
     qpick_x_assum ‘s o td1 = Id1(A) o t’ (assume_tac o GSYM) >>
     arw[GSYM o_assoc] >> rw[Pb_eqn,o_assoc]) >>
 qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
 drule through_Pb >>
 first_x_assum (qsspecl_then [‘t o Pba1(td1, td0)’,‘t o Pba2(td1, td0)’]
 assume_tac) >> rfs[] >> qexists_tac ‘a0’ >> arw[])
(form_goal
 “!A T t:T->Exp(2,A). SO(t) ==>
  !S s:S->A.SO(s) ==>
  !td0:T->S td1:T->S ti:S->T tr:Pbo(td1,td0) -> T. 
  s o td0 = Id0(A) o t & 
  s o td1 = Id1(A) o t &
  t o ti = Ii(A) o s ==>
  ?tt.Pba1(Id1(A), Id0(A)) o tt = t o Pba1(td1, td0) &
      Pba2(Id1(A), Id0(A)) o tt = t o Pba2(td1, td0)”));


val Thm25_ISC = prove_store("Thm25_ISC",
e0
(rpt strip_tac >>
 rw[ISC_def] >> 
 qby_tac ‘Disc(S)’ >-- fs[SO_def] >>
 qby_tac ‘Disc(T)’ >-- fs[SO_def] >> arw[] >>
 rw[Icat_def] >>
 qby_tac ‘td0 o ti = Id(S)’ 
 >-- (drule $ iffLR SO_def >>
     pop_assum strip_assume_tac>>
     drule $ iffLR Mono_def >> first_x_assum irule>>
     arw[GSYM o_assoc] >> arw[o_assoc] >> rw[IdR] >>
     rw[C2Icat_cl12,GSYM o_assoc,IdL]) >> arw[] >>
 qby_tac ‘td1 o ti = Id(S)’ 
 >-- (drule $ iffLR SO_def >>
     pop_assum strip_assume_tac>>
     drule $ iffLR Mono_def >> first_x_assum irule>>
     arw[GSYM o_assoc] >> arw[o_assoc] >> rw[IdR] >>
     rw[C2Icat_cl12,GSYM o_assoc,IdL]) >> arw[] >>
 qby_tac
 ‘?tt.Pba1(Id1(A), Id0(A)) o tt = t o Pba1(td1, td0) &
      Pba2(Id1(A), Id0(A)) o tt = t o Pba2(td1, td0)’
 >-- 

cheat >>
 pop_assum strip_assume_tac >> 
 qby_tac ‘td0 o tr = td0 o Pba1(td1, td0)’ 
 >-- (drule $ iffLR SO_def >>
     pop_assum strip_assume_tac>>
     drule $ iffLR Mono_def >> first_x_assum irule>>
     arw[GSYM o_assoc] >> rw[o_assoc] >>
     first_x_assum (qsspecl_then [‘tt’] assume_tac) >> rfs[] >>
     rw[GSYM o_assoc,C2ICat_dom] >> arw[o_assoc]) >> arw[] >> 
 qby_tac ‘td1 o tr = td1 o Pba2(td1, td0)’ 
 >-- (drule $ iffLR SO_def >>
     pop_assum strip_assume_tac>>
     drule $ iffLR Mono_def >> first_x_assum irule>>
     arw[GSYM o_assoc] >> rw[o_assoc] >>
     first_x_assum (qsspecl_then [‘tt’] assume_tac) >> rfs[] >>
     rw[GSYM o_assoc,C2ICat_cod] >> arw[o_assoc]) >> arw[] >>     
 qby_tac ‘IidL(td0, td1, ti, tr)’ 
 >-- (irule $ iffRL IidL_alt >> arw[] >>
     rpt strip_tac >> rw[isio_def] >> rw[Pb_def] >> arw[] >>
     pop_assum (assume_tac o GSYM) >> arw[] >> arw[GSYM o_assoc] >>
     rw[IdL] >> pop_assum (assume_tac o GSYM) >>
     arw[o_assoc] >>
     qsspecl_then [‘td1’,‘td0’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘ti o c’,‘a’] assume_tac) >>
     rfs[GSYM o_assoc,IdL] >>
     qexists_tac ‘a0’ >> arw[] >>
     first_x_assum (qsspecl_then [‘tt’] assume_tac) >> rfs[] >>
     rev_drule $ iffLR SO_def >>
     pop_assum strip_assume_tac >>
     drule $ iffLR Mono_def >>
     first_x_assum irule >> arw[GSYM o_assoc] >>
     assume_tac C2Icat_IidL >> drule $ iffLR IidL_def >>
     rw[o_assoc] >> 
     qby_tac
     ‘?ci1.Pba1(Id1(A), Id0(A)) o ci1 = Ii(A) o Pba1(Id(A), Id0(A)) &
           Pba2(Id1(A), Id0(A)) o ci1 = Pba2(Id(A), Id0(A))’ 
     >-- (irule ci1_ex >> rw[C2Icat_cl12]) >>
     pop_assum strip_assume_tac >>
     qsspecl_then [‘Id(A)’,‘Id0(A)’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘s o c’,‘t o a’] assume_tac) >>
     qby_tac ‘Id(A) o s o c = Id0(A) o t o a’ 
     >-- (rw[IdL] >>
         qpick_x_assum ‘s o td0 = Id0(A) o t’ (assume_tac o GSYM) >> 
         arw[GSYM o_assoc] >> arw[o_assoc]) >>
     first_x_assum (drule o iffLR) >>
     pop_assum strip_assume_tac >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     first_x_assum (qsspecl_then [‘ci1’] assume_tac) >> rfs[] >>
     pop_assum (assume_tac o GSYM) >> arw[] >> rw[o_assoc] >>
     qsuff_tac ‘tt o a0 = ci1 o a0'’ 
     >-- (strip_tac >> arw[]) >>
     irule Pba12_eq_eq >> pop_assum (assume_tac o GSYM) >>
     arw[GSYM o_assoc] >> arw[o_assoc] >>
     arw[GSYM o_assoc]) >> arw[] >> 
 qby_tac ‘IidR(td0, td1, ti, tr)’ 
 >-- (irule $ iffRL IidR_alt >> arw[] >>
     rpt strip_tac >> rw[isio_def] >> rw[Pb_def] >> arw[] >>
     pop_assum (assume_tac o GSYM) >> arw[] >> arw[GSYM o_assoc] >>
     rw[IdL] >> pop_assum (assume_tac o GSYM) >>
     arw[o_assoc] >>
     qsspecl_then [‘td1’,‘td0’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘a’,‘ti o c’] assume_tac) >>
     rfs[GSYM o_assoc,IdL] >>
     qexists_tac ‘a0’ >> arw[] >>
     first_x_assum (qsspecl_then [‘tt’] assume_tac) >> rfs[] >>
     rev_drule $ iffLR SO_def >>
     pop_assum strip_assume_tac >>
     drule $ iffLR Mono_def >>
     first_x_assum irule >> arw[GSYM o_assoc] >>
     assume_tac C2Icat_IidR >> drule $ iffLR IidR_def >>
     rw[o_assoc] >> 
     qby_tac
     ‘?c1i.Pba1(Id1(A), Id0(A)) o c1i = Pba1(Id1(A), Id(A)) &
           Pba2(Id1(A), Id0(A)) o c1i = Ii(A) o Pba2(Id1(A), Id(A))’ 
     >-- (irule c1i_ex >> rw[C2Icat_cl12]) >>
     pop_assum strip_assume_tac >>
     qsspecl_then [‘Id1(A)’,‘Id(A)’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘t o a’,‘s o c’] assume_tac) >>
     qby_tac ‘Id1(A) o t o a = Id(A) o s o c’ 
     >-- (rw[IdL] >>
         qpick_x_assum ‘s o td1 = Id1(A) o t’ (assume_tac o GSYM) >> 
         arw[GSYM o_assoc] >> arw[o_assoc]) >>
     first_x_assum (drule o iffLR) >>
     pop_assum strip_assume_tac >>
     qpick_x_assum ‘Pba1(Id1(A), Id(A)) o a0' = t o a’
      (assume_tac o GSYM) >> arw[] >>
     first_x_assum (qsspecl_then [‘c1i’] assume_tac) >> rfs[] >>
     pop_assum (assume_tac o GSYM) >> arw[] >> rw[o_assoc] >>
     qsuff_tac ‘tt o a0 = c1i o a0'’ 
     >-- (strip_tac >> arw[]) >>
     irule Pba12_eq_eq >> pop_assum (assume_tac o GSYM) >>
     arw[GSYM o_assoc] >> arw[o_assoc] >>
     arw[GSYM o_assoc]) >> arw[] >> 
 irule $ iffRL Iassoc_alt >> arw[] >>
 rpt strip_tac >>
 qby_tac ‘!X f:X->T g:X->T. td0 o g = td1 o f ==>
 ?gf. isio(td0, td1, Pba1(td1, td0), Pba2(td1, td0), tr, g, f, gf) & 
      isio(Id0(A), Id1(A), Pba1(Id1(A), Id0(A)), Pba2(Id1(A), Id0(A)),
           Ir(A), t o g, t o f, t o gf)’ 
 >-- (rpt strip_tac >>
     qsspecl_then [‘td1’,‘td0’] assume_tac Pb_def >>
     drule isio_ex >>
     first_x_assum (qsspecl_then [‘tr’] assume_tac) >> rfs[] >>
     first_x_assum drule >> pop_assum strip_assume_tac >>
     qexists_tac ‘gf’ >> arw[] >>
     first_x_assum (qsspecl_then [‘tt’] assume_tac) >> rfs[] >> 
     drule $ iffLR isio_def >>
     pop_assum strip_assume_tac >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     arw[GSYM o_assoc] >> rw[o_assoc] >>
     qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
     drule isio_o_r1 >>
     first_x_assum (qsspecl_then [‘Ir(A)’] assume_tac) >>
     fs[C2ICat_cod,C2ICat_dom] >>
     first_x_assum irule >> arw[GSYM o_assoc] >> 
     arw[o_assoc] >>
     qpick_x_assum ‘s o td0 = Id0(A) o t’ (assume_tac o GSYM)>> 
     arw[GSYM o_assoc] >>
     qpick_x_assum ‘s o td1 = Id1(A) o t’ (assume_tac o GSYM) >>
     arw[GSYM o_assoc] >> arw[o_assoc]) >>
 first_assum drule >>
 pop_assum (x_choose_then "t32" strip_assume_tac) >>
 first_assum rev_drule >>
 pop_assum (x_choose_then "t21" strip_assume_tac) >>
 qby_tac ‘td0 o t3 = td1 o t21’ >-- cheat >>
 first_assum drule >>
 pop_assum (x_choose_then "t321r" strip_assume_tac)  >>
 qby_tac ‘td0 o t32 = td1 o t1’ >-- cheat >>
 first_x_assum drule >>
 pop_assum (x_choose_then "t321l" strip_assume_tac) >>
 qexistsl_tac [‘t321l’,‘t32’,‘t21’] >> arw[] >>
 qsuff_tac ‘t321l = t321r’ >-- (strip_tac >> arw[]) >>
 qsuff_tac ‘t o t321l = t o t321r’ 
 >-- (strip_tac >> rev_drule $ iffLR SO_def >>
     pop_assum strip_assume_tac >>
     drule $ iffLR Mono_def >>
     first_x_assum irule >> arw[]) >>
 assume_tac C2Icat_Iassoc >>
 drule $ iffLR C2Icat_Iassoc_alt >>
 first_x_assum (qsspecl_then [‘t o t3’,‘t o t2’,‘t o t1’] assume_tac) >>
 rfs[GSYM o_assoc] >>
 qby_tac ‘(Id0(A) o t) o t2 = (Id1(A) o t) o t1 &
          (Id0(A) o t) o t3 = (Id1(A) o t) o t2’
 >-- (qpick_x_assum ‘s o td0 = Id0(A) o t’ (assume_tac o GSYM) >>
     qpick_x_assum ‘s o td1 = Id1(A) o t’ (assume_tac o GSYM) >> arw[] >>
     arw[o_assoc]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qby_tac ‘t21' = t o t21’
 >-- (qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
     drule isio_unique1 >>
     first_x_assum (qspecl_then [‘Ir(A)’] assume_tac) >>
     first_x_assum irule >>
     qexistsl_tac [‘t o t1’,‘t o t2’] >> arw[]) >> fs[] >>
 qby_tac ‘t32' = t o t32’ 
 >-- (qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
     drule isio_unique1 >>
     first_x_assum (qspecl_then [‘Ir(A)’] assume_tac) >>
     first_x_assum irule >>
     qexistsl_tac [‘t o t2’,‘t o t3’] >> arw[]) >> fs[] >>
 qsuff_tac ‘t o t321l = t321 & t o t321r = t321’ 
 >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
     drule isio_unique1 >>
     first_x_assum (qspecl_then [‘Ir(A)’] assume_tac) >>
     first_x_assum irule >>
     qexistsl_tac [‘t o t1’,‘t o t32’] >> arw[]) >>
 qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
 drule isio_unique1 >>
 first_x_assum (qspecl_then [‘Ir(A)’] assume_tac) >>
 first_x_assum irule >>
 qexistsl_tac [‘t o t21’,‘t o t3’] >> arw[])
(form_goal
 “!A T t:T->Exp(2,A). SO(t) ==>
  !S s:S->A.SO(s) ==>
  !td0:T->S td1:T->S ti:S->T tr:Pbo(td1,td0) -> T. 
  s o td0 = Id0(A) o t & 
  s o td1 = Id1(A) o t &
  t o ti = Ii(A) o s & 
  (!tt: Pbo(td1,td0) -> Pbo(Id1(A),Id0(A)).
   Pba1(Id1(A),Id0(A)) o tt = t o Pba1(td1,td0) & 
   Pba2(Id1(A),Id0(A)) o tt = t o Pba2(td1,td0) ==>
   t o tr = Ir(A) o tt) ==>
  ISC(td0,td1,ti,tr)”));


val Thm25_0 = prove_store("Thm25_0",
e0
(rpt gen_tac >> )
(form_goal
 “!A T t:T->Exp(2,A). SO(t) ==>
  !S s:S->A.SO(s) ==>
  !td0:T->S td1:T->S ti:S->T tr:Pbo(td1,td0) -> T. 
  s o td0 = Id0(A) o t & 
  s o td1 = Id1(A) o t &
  t o ti = Ii(A) o s & 
  (!tt: Pbo(td1,td0) -> Pbo(Id1(A),Id0(A)).
   Pba1(Id1(A),Id0(A)) o tt = t o Pba1(td1,td0) & 
   Pba2(Id1(A),Id0(A)) o tt = t o Pba2(td1,td0) ==>
   t o tr = Ir(A) o tt) ==>
  ISC(td0,td1,ti,tr) & 
  IFun(td0,td1,ti,tr,Id0(A),Id1(A),Ii(A),Ir(A),s,t)”));


val Thm25 = prove_store("Thm25",
e0
()
(form_goal
 “!A T t:T->Exp(2,A). SO(t) ==>
  !S s:S->A.SO(s) ==>
  ?td0:T->S td1:T->S ti:S->T tr:Pbo(td1,td0) -> T. 
  ISC(td0,td1,ti,tr) & 
  IFun(td0,td1,ti,tr,Id0(A),Id1(A),Ii(A),Ir(A),s,t)”));

