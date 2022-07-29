
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
 “!A T t:T->Exp(2,A)
  S s:S->A td0:T->S td1:T->S. 
  s o td0 = Id0(A) o t & 
  s o td1 = Id1(A) o t  ==>
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
 >-- (irule tt_ex >> qexists_tac ‘s’ >> arw[]) >>
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
 qby_tac ‘td0 o t3 = td1 o t21’ 
 >-- (flip_tac >> 
     qsspecl_then [‘td1’,‘td0’] assume_tac Pb_def >>
     drule isio_dom_cod >> first_assum drule >> arw[]) >>
 first_assum drule >>
 pop_assum (x_choose_then "t321r" strip_assume_tac)  >>
 qby_tac ‘td0 o t32 = td1 o t1’ 
 >-- (qsspecl_then [‘td1’,‘td0’] assume_tac Pb_def >>
     drule isio_dom_cod >> first_assum rev_drule >> arw[]) >>
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





val Thm25_ISC = prove_store("Thm25_ISC",
e0
(rpt gen_tac >> strip_tac >> 
rpt gen_tac >> strip_tac >> 
rpt gen_tac >> strip_tac >>  
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
 >-- (irule tt_ex >> qexists_tac ‘s’ >> arw[]) >>
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
     arw[GSYM o_assoc] >> arw[o_assoc]) >> arw[] >>
 irule $ iffRL Iassoc_alt >> arw[] >>
 rpt strip_tac >>
 first_assum drule >>
 pop_assum (x_choose_then "t32" strip_assume_tac) >>
 first_assum rev_drule >>
 pop_assum (x_choose_then "t21" strip_assume_tac) >>
 qby_tac ‘td0 o t3 = td1 o t21’ 
 >-- (flip_tac >> 
     qsspecl_then [‘td1’,‘td0’] assume_tac Pb_def >>
     drule isio_dom_cod >> first_assum drule >> arw[]) >>
 first_assum drule >>
 pop_assum (x_choose_then "t321r" strip_assume_tac)  >>
 qby_tac ‘td0 o t32 = td1 o t1’ 
 >-- (qsspecl_then [‘td1’,‘td0’] assume_tac Pb_def >>
     drule isio_dom_cod >> first_assum rev_drule >> arw[]) >>
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
  (ISC(td0,td1,ti,tr) &
 (!X f:X->T g:X->T. td0 o g = td1 o f ==>
 ?gf. isio(td0, td1, Pba1(td1, td0), Pba2(td1, td0), tr, g, f, gf) & 
      isio(Id0(A), Id1(A), Pba1(Id1(A), Id0(A)), Pba2(Id1(A), Id0(A)),
           Ir(A), t o g, t o f, t o gf)))”));

val Thm25_0 = prove_store("Thm25_0",
e0
(rpt (rpt gen_tac >> disch_tac) >>
 rev_drule Thm25_ISC >>
 first_x_assum drule>>
 first_x_assum (qsspecl_then [‘td0’,‘td1’,‘ti’,‘tr’] assume_tac) >>
 rfs[] >>
 rw[IFun_def] >>
 qby_tac ‘Ipreso(td0, td1, ti, tr, Id0(A), Id1(A), Ii(A), Ir(A), s, t)’ 
 >-- (irule $ iffRL Ipreso_alt >> arw[] >>
     rw[C2ICat] >> drule $ iffLR ISC_def >> arw[]) >>
 arw[] >> rw[C2ICat] >> drule $ iffLR ISC_def >> arw[])
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

val Disc_dom_eq = prove_store("Disc_dom_eq",
e0
(rpt strip_tac >> fs[Disc_def] >>
 fs[isid_alt] >>
 qby_tac ‘id(dom(a1)) = id(dom(a2))’ 
 >-- (last_x_assum (K all_tac)>> arw[]) >>
 rfs[])
(form_goal “!D. Disc(D) ==>
  !a1:2->D a2.dom(a1) = dom(a2) ==> a1 = a2
 ”));


val Pb_Disc_Disc = prove_store("Pb_Disc_Disc",
e0
(rpt strip_tac >> rw[Disc_def] >> strip_tac >>
 rw[isid_def] >>
 drule through_Pb >>
 first_x_assum (qsspecl_then [‘dom(p o f')’,‘dom(q o f')’] assume_tac) >>
 drule $ iffLR isPb_def >>
 pop_assum strip_assume_tac >>
 fs[GSYM o_assoc,dom_def] >>
 qexists_tac ‘a0’ >> 
 drule Pb12_eq_eq >> first_x_assum irule >> strip_tac (* 2 *)
 >-- (rev_drule Disc_dom_eq >>
     first_x_assum irule >> fs[dom_def,GSYM o_assoc] >>
     rw[o_assoc] >> rw[one_to_one_Id] >> rw[IdR]) >>
 drule Disc_dom_eq >>
 first_x_assum irule >>
 fs[dom_def,GSYM o_assoc] >>
 rw[o_assoc] >> rw[one_to_one_Id] >> rw[IdR])
(form_goal
 “!D1 D2. Disc(D1) & Disc(D2) ==>
  !A f:D1->A g:D2->A P p:P->D1 q:P->D2.
  isPb(f,g,p,q) ==> Disc(P)”));

val Thm25 = prove_store("Thm25",
e0
(rpt strip_tac >>
 qsuff_tac ‘?td0:T->S td1:T->S ti:S->T tr:Pbo(td1,td0) -> T.
  s o td0 = Id0(A) o t & 
  s o td1 = Id1(A) o t &
  t o ti = Ii(A) o s & 
  (!tt: Pbo(td1,td0) -> Pbo(Id1(A),Id0(A)).
   Pba1(Id1(A),Id0(A)) o tt = t o Pba1(td1,td0) & 
   Pba2(Id1(A),Id0(A)) o tt = t o Pba2(td1,td0) ==>
   t o tr = Ir(A) o tt)’
 >-- (strip_tac >> qexistsl_tac [‘td0’,‘td1’,‘ti’,‘tr’] >>
     rev_drule Thm25_0 >> first_x_assum drule >>
     first_x_assum irule >> arw[]) >>
 drule $ iffLR SO_def >> pop_assum strip_assume_tac >>
 rev_drule $ iffLR SO_def >> pop_assum strip_assume_tac >>
 first_x_assum (qsspecl_then [‘Ii(A) o s’] assume_tac) >>
 first_x_assum drule >> pop_assum (x_choose_then "ti" assume_tac) >>
 pop_assum (assume_tac o GSYM) >>
 first_assum (qsspecl_then [‘Id0(A) o t’] assume_tac) >>
 first_x_assum drule >>
 pop_assum (x_choose_then "td0" (assume_tac o GSYM)) >>
 first_x_assum (qsspecl_then [‘Id1(A) o t’] assume_tac) >>
 first_x_assum drule >>
 pop_assum (x_choose_then "td1" (assume_tac o GSYM)) >> 
 qexistsl_tac [‘td0’,‘td1’,‘ti’] >> arw[] >>
 qby_tac
 ‘?tt.Pba1(Id1(A), Id0(A)) o tt = t o Pba1(td1, td0) &
      Pba2(Id1(A), Id0(A)) o tt = t o Pba2(td1, td0)’
 >-- (irule tt_ex >> qexists_tac ‘s’ >> arw[]) >>
 pop_assum strip_assume_tac >>
 rev_drule $ iffLR SO_def >>
 pop_assum strip_assume_tac >>
 first_x_assum (qsspecl_then [‘Ir(A) o tt’] assume_tac) >>
 qsuff_tac ‘Disc(Pbo(td1, td0))’ 
 >-- (strip_tac >> first_x_assum drule >>
     pop_assum (x_choose_then "tr" assume_tac) >>
     qexists_tac ‘tr’ >> rpt strip_tac >>
     qsuff_tac ‘tt' = tt’ 
     >-- (strip_tac >> arw[]) >>
     irule Pba12_eq_eq>> arw[]) >>
 qspecl_then [‘T’,‘T’] assume_tac Pb_Disc_Disc >> rfs[] >>
 qsspecl_then [‘td1’,‘td0’] assume_tac Pb_def >>
 first_x_assum drule >> arw[])
(form_goal
 “!A T t:T->Exp(2,A). SO(t) ==>
  !S s:S->A.SO(s) ==>
  ?td0:T->S td1:T->S ti:S->T tr:Pbo(td1,td0) -> T. 
  ISC(td0,td1,ti,tr) & 
  IFun(td0,td1,ti,tr,Id0(A),Id1(A),Ii(A),Ir(A),s,t)”));

val ISOof_def = 
qdefine_psym("ISOof",
[‘td0:T->S’,‘td1:T->S’,‘ti:S->T’,‘tr:Pbo(td1:T->S,td0:T->S)->T’,
 ‘s:S->A’,‘t:T->Exp(2,A)’]) 
‘SO(t) & SO(s) & 
 s o td0 = Id0(A) o t & 
 s o td1 = Id1(A) o t &
 t o ti = Ii(A) o s & 
 (!tt: Pbo(td1,td0) -> Pbo(Id1(A),Id0(A)).
  Pba1(Id1(A),Id0(A)) o tt = t o Pba1(td1,td0) & 
  Pba2(Id1(A),Id0(A)) o tt = t o Pba2(td1,td0) ==>
 t o tr = Ir(A) o tt) & 
 ISC(td0,td1,ti,tr) & 
 IFun(td0,td1,ti,tr,Id0(A),Id1(A),Ii(A),Ir(A),s,t)’


val Sq_Ii = prove_store("Sq_Ii",
e0
(rpt strip_tac >> rw[Ii_ID] >> rw[Ii_def,Sq_def] >>
 rw[ID_def] >> 
 irule Ev_eq_eq >> rw[Ev_of_Tp_el] >>
 rw[o_assoc,Ev_of_Tp_el] >> rw[p12_of_Pa] >>
 rw[Pt_def] >> rw[id_def,o_assoc,GSYM Tp1_def,Ev_of_Tp_el,Swap_Pa] >>
 rw[Pa_distr,p12_of_Pa,o_assoc] >> rw[Ev_of_Tp_el] >>
 rw[o_assoc,p12_of_Pa])
(form_goal “!A B F:A->B.Ii(B) o F = Sq(F) o Ii(A)”));

val Sq_Rw = prove_store("Sq_Rw",
e0
(rpt strip_tac >> rw[Rw_def] >> rw[Ec_def] >> rw[Sq_def])
(form_goal
“∀A B F:A->B T η.Sq(F:A->B) o η:T->Exp(2,A) = Rw(F,η)”));


val Rw_vo = prove_store("Rw_vo",
e0
(rpt strip_tac >>
 irule $ Nt_ext_cpnt >>
 qabbrev_tac ‘Dom(f) = F1’ >>
 qabbrev_tac ‘Cod(f) = F2’ >>
 qabbrev_tac ‘Cod(g) = F3’ >>
 qby_tac ‘Nt(f,F1,F2)’ 
 >-- (qsspecl_then [‘f’] assume_tac Nt_Dom_Cod >> rfs[]) >>
 qby_tac ‘Nt(g,F2,F3)’ 
 >-- (qsspecl_then [‘g’] assume_tac Nt_Dom_Cod >> rfs[]) >>
 qby_tac ‘Nt(vo(g,f),F1,F3)’ 
 >-- (irule vo_Nt_Nt >> qexists_tac ‘F2’ >> arw[]) >>
 drule Nt_Rw_Nt >>
 first_x_assum (qsspecl_then [‘F’] assume_tac) >>
 rev_drule Nt_Rw_Nt >>
 first_x_assum (qsspecl_then [‘F’] assume_tac) >>
 qsspecl_then [‘F2’,‘F3’,‘g’] assume_tac Nt_Rw_Nt >>
 first_x_assum drule >>
 first_x_assum (qsspecl_then [‘F’] assume_tac) >>
 qby_tac ‘Nt(vo(Rw(F, g), Rw(F, f)), F o F1, F o F3)’
 >-- (irule vo_Nt_Nt >> qexists_tac ‘F o F2’ >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- (qexistsl_tac [‘F o F1’,‘F o F3’] >> arw[]) >>
 rw[Rw_cpnt] >>
 qby_tac ‘cpnt(vo(g, f), a) = cpnt(g, a) @ cpnt(f,a)’ 
 >-- (irule Nt_vo_cpnt >> qexistsl_tac [‘F1’,‘F2’,‘F3’] >> arw[]) >> arw[] >>
 qby_tac ‘cpsb(cpnt(g, a),cpnt(f, a))’ 
 >-- (irule Dom_Cod_vo_cpsb >> arw[]) >>
 drule fun_pres_oa >> 
 first_x_assum (qsspecl_then [‘F’] assume_tac) >> arw[] >>
 qby_tac
 ‘cpnt(vo(Rw(F, g), Rw(F, f)), a) = 
  cpnt(Rw(F, g), a) @ cpnt(Rw(F, f), a)’ 
 >-- (irule Nt_vo_cpnt >> qexistsl_tac [‘F o F1’,‘F o F2’,‘F o F3’] >>
     arw[]) >> arw[] >>
 rw[Rw_cpnt])
(form_goal 
 “∀A B F:A->B g f:T->Exp(2,A). 
  Dom(g) = Cod(f) ⇒
  Rw(F, vo(g, f)) = vo(Rw(F, g), Rw(F, f))”));

val Sq_IFun = prove_store("Sq_IFun",
e0
(rpt strip_tac >> rw[IFun_def] >>
 qby_tac ‘Icat(Id0(A), Id1(A), Ii(A), Ir(A))’
 >-- rw[C2ICat] >>
 qby_tac ‘Icat(Id0(B), Id1(B), Ii(B), Ir(B))’
 >-- rw[C2ICat] >> arw[] >>
 qby_tac ‘Id0(B) o Sq(F) = F o Id0(A)’
 >-- rw[Id0_Sq] >>
 qby_tac ‘Id1(B) o Sq(F) = F o Id1(A)’
 >-- rw[Id1_Sq] >> arw[]>>
 qby_tac ‘Ii(B) o F = Sq(F) o Ii(A)’
 >-- rw[Sq_Ii] >> arw[] >>
 irule $ iffRL Ipreso_alt >> arw[] >>
 rpt strip_tac >>
 qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
 drule isio_ex >>
 first_x_assum (qsspecl_then [‘Ir(A)’] assume_tac) >>
 qby_tac ‘Id0(A) o Ir(A) = Id0(A) o Pba1(Id1(A), Id0(A)) &
          Id1(A) o Ir(A) = Id1(A) o Pba2(Id1(A), Id0(A)) ’
 >-- fs[Icat_def] >>
 first_x_assum drule >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘gf’ >> arw[] >>
 irule $ iffRL isio_iff_vo' >>
 qby_tac ‘Dom(Sq(F) o g) = Cod(Sq(F) o f)’
 >-- (fs[GSYM Id0_Dom,GSYM Id1_Cod] >> arw[GSYM o_assoc] >> 
     arw[o_assoc]) >> arw[] >>
 rw[Sq_Rw]  >>
 qby_tac ‘gf = vo(g,f)’ 
 >-- (irule $ iffLR isio_iff_vo' >> arw[GSYM Id0_Dom,GSYM Id1_Cod]) >>
 arw[] >>
 irule Rw_vo >> arw[GSYM Id0_Dom,GSYM Id1_Cod])
(form_goal 
 “!A B F:A->B G. 
  IFun(Id0(A),Id1(A),Ii(A),Ir(A),
       Id0(B),Id1(B),Ii(B),Ir(B),F,Sq(F))”));


val ISOof_Icat = prove_store("ISOof_Icat",
e0
(rpt strip_tac >> fs[ISOof_def,ISC_def])
(form_goal
 “!A A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  Icat(Ad0,Ad1,Ai,Ar)”));


val ISOof_Mono = prove_store("ISOof_Mono",
e0
(rpt strip_tac >> fs[ISOof_def,SO_def])
(form_goal
 “!A A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  Mono(As) & Mono(At)”));


val isio_ISOof = prove_store("isio_ISOof",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (rw[isio_def] >> 
     qby_tac ‘isPb(Id1(A), Id0(A), Pba1(Id1(A), Id0(A)), Pba2(Id1(A), Id0(A))) &
             Id0(A) o Ir(A) = Id0(A) o Pba1(Id1(A), Id0(A)) &
             Id1(A) o Ir(A) = Id1(A) o Pba2(Id1(A), Id0(A)) &
             Id0(A) o At o g = Id1(A) o At o f’
     >-- (rw[Pb_def] >>
         drule $ iffLR ISOof_def >>
         pop_assum strip_assume_tac >>
         drule $ iffLR ISC_def >>
         pop_assum strip_assume_tac >> rw[C2ICat_cod,C2ICat_dom] >>
         drule $ iffLR IFun_def >>
         once_arw[GSYM o_assoc] >> once_arw[] >> rw[o_assoc] >>
         once_arw[] >> rw[]) >> arw[] >>
     qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘At o f’,‘At o g’] assume_tac) >>
     rfs[] >>
     qexists_tac ‘a0’ >> arw[] >>
     qsspecl_then [‘Ad1’,‘Ad0’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >> rfs[] >>
     qsspecl_then [‘At’,‘As’,‘Ad0’,‘Ad1’] assume_tac tt_ex >>
     qby_tac ‘As o Ad0 = Id0(A) o At & As o Ad1 = Id1(A) o At’ 
     >-- (drule $ iffLR ISOof_def >> once_arw[] >> once_arw[] >> rw[]) >>
     first_x_assum drule >>
     pop_assum strip_assume_tac >>
     qby_tac ‘a0 = tt o a0'’ 
     >-- (irule Pba12_eq_eq >> once_arw[] >> arw[GSYM o_assoc] >>
         arw[o_assoc]) >> arw[] >>
     qby_tac ‘Ir(A) o tt = At o Ar’ 
     >-- (drule $ iffLR ISOof_def >>
         pop_assum strip_assume_tac >>   
         flip_tac >> first_x_assum irule >> arw[]) >>
     rw[GSYM o_assoc] >> once_arw[] >> rw[o_assoc] >>
     qby_tac ‘Ar o a0' = gf’ 
     >-- (drule isio_unique1 >>
         first_x_assum (qspecl_then [‘Ar’] assume_tac) >>
         first_x_assum irule >>
         qexistsl_tac [‘f’,‘g’] >> arw[] >>
         drule isio_o_r1 >>
         first_x_assum (qsspecl_then [‘Ar’] assume_tac) >>
         qby_tac ‘Ad0 o Ar = Ad0 o Pba1(Ad1, Ad0) & 
                  Ad1 o Ar = Ad1 o Pba2(Ad1, Ad0)’
         >-- (drule $ iffLR ISOof_def >>
             pop_assum strip_assume_tac >>
             drule $ iffLR ISC_def >>
             pop_assum strip_assume_tac >>
             drule $ iffLR Icat_def >> once_arw[] >> once_arw[] >> rw[]) >>
         first_x_assum drule >> 
         first_x_assum irule >> arw[]) >>
     arw[]) >>
 rw[isio_def] >> rw[Pb_def] >>
 drule ISOof_Icat >>
 qby_tac ‘Ad0 o Ar = Ad0 o Pba1(Ad1, Ad0) &
          Ad1 o Ar = Ad1 o Pba2(Ad1, Ad0) &
          Ad0 o g = Ad1 o f’
 >-- (drule $ iffLR Icat_def >> arw[]) >>
 arw[] >>
 qsspecl_then [‘Ad1’,‘Ad0’] assume_tac Pb_def >>
 drule through_Pb >>
 first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >> rfs[] >>
 qexists_tac ‘a0’ >> arw[] >> 
 qsuff_tac ‘At o Ar o a0 = At o gf’
 >-- (drule ISOof_Mono >> fs[Mono_def]) >>
 qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
 drule isio_unique1 >>
 first_x_assum (qspecl_then [‘Ir(A)’] assume_tac) >>
 first_x_assum irule >> qexistsl_tac [‘At o f’,‘At o g’] >> arw[] >>
 qsspecl_then [‘At’,‘As’,‘Ad0’,‘Ad1’] assume_tac tt_ex >>
 qby_tac ‘As o Ad0 = Id0(A) o At & As o Ad1 = Id1(A) o At’ 
 >-- (drule $ iffLR ISOof_def >> once_arw[] >> once_arw[] >> rw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>  
 qby_tac ‘Ir(A) o tt = At o Ar’ 
 >-- (drule $ iffLR ISOof_def >>
      pop_assum strip_assume_tac >>   
     flip_tac >> first_x_assum irule >> arw[]) >>
 pop_assum (assume_tac o GSYM) >>
 arw[GSYM o_assoc] >> rw[o_assoc] >>
 drule isio_o_r1 >>
 first_x_assum (qsspecl_then [‘Ir(A)’] assume_tac) >>
 qby_tac ‘Id0(A) o Ir(A) = Id0(A) o Pba1(Id1(A), Id0(A)) &
          Id1(A) o Ir(A) = Id1(A) o Pba2(Id1(A), Id0(A))’
 >-- rw[C2ICat_dom,C2ICat_cod] >>
 first_x_assum drule >>
 first_x_assum irule >> arw[GSYM o_assoc] >> arw[o_assoc] >>
 qby_tac ‘Id0(A) o At = As o Ad0 & Id1(A) o At = As o Ad1’ 
 >-- (drule $ iffLR ISOof_def >> arw[]) >>
 once_arw[GSYM o_assoc] >> once_arw[] >>
 rw[o_assoc] >> once_arw[] >> rw[])
(form_goal
 “!A A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀T f:T->A1 g:T->A1 gf. 
   Ad0 o g = Ad1 o f ⇒
   (isio(Ad0, Ad1, Pba1(Ad1, Ad0), Pba2(Ad1, Ad0), Ar, g, f, gf) ⇔ 
   isio(Id0(A),Id1(A),Pba1(Id1(A),Id0(A)),Pba2(Id1(A),Id0(A)),Ir(A),At o g,At o f,At o gf))”));




val isio_ISOof_vo = prove_store("isio_ISOof_vo",
e0
(rpt strip_tac >>
 drule isio_ISOof >>
 first_x_assum drule >> arw[] >>
 pop_assum (K all_tac) >>
 irule isio_iff_vo' >>
 rw[GSYM Id1_Cod,GSYM Id0_Dom] >>
 qby_tac ‘Id0(A) o At = As o Ad0 & Id1(A) o At = As o Ad1’
 >-- (drule $ iffLR ISOof_def >> arw[]) >>
 arw[GSYM o_assoc] >> arw[o_assoc])
(form_goal
 “!A A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀T f:T->A1 g:T->A1 gf. 
   Ad0 o g = Ad1 o f ⇒
   (isio(Ad0, Ad1, Pba1(Ad1, Ad0), Pba2(Ad1, Ad0), Ar, g, f, gf) ⇔ 
   At o gf = vo(At o g,At o f))”));


val Thm26_L2R = prove_store("Thm26_L2R",
e0
(rpt strip_tac >>
 qby_tac ‘?f0. Bs o f0 = F o As’ 
 >-- (drule $ iffLR ISOof_def >>
     pop_assum strip_assume_tac >>
     drule $ iffLR SO_def >> pop_assum strip_assume_tac >>
     first_x_assum (qsspecl_then [‘F o As’] assume_tac) >>
     flip_tac >> first_x_assum irule >> 
     rev_drule $ iffLR ISOof_def >> pop_assum strip_assume_tac >>
     drule $ iffLR SO_def >> arw[]) >>
 pop_assum strip_assume_tac >> qexists_tac ‘f0’ >> arw[] >>
 qby_tac ‘?f1. Bt o f1 = Sq(F) o At’ 
 >-- (drule $ iffLR ISOof_def >>
     pop_assum strip_assume_tac >>
     rev_drule $ iffLR SO_def >>
     pop_assum strip_assume_tac >>
     first_x_assum (qsspecl_then [‘Sq(F) o At’] assume_tac) >>
     flip_tac >> first_x_assum irule >>
     rev_drule $ iffLR ISOof_def >>
     pop_assum strip_assume_tac >> 
     fs[SO_def]) >> pop_assum strip_assume_tac >>
 qexists_tac ‘f1’ >> arw[] >>
 rw[IFun_def] >>
 qby_tac ‘Icat(Ad0, Ad1, Ai, Ar)’ 
 >-- (rev_drule $ iffLR ISOof_def >>  
     pop_assum strip_assume_tac >>
     fs[ISC_def]) >> arw[] >>
 qby_tac ‘Icat(Bd0, Bd1, Bi, Br)’ 
 >-- (drule $ iffLR ISOof_def >>  
     pop_assum strip_assume_tac >>
     fs[ISC_def]) >> arw[] >>
 qby_tac ‘Mono(Bs) & Mono(Bt) & Mono(As) & Mono(At)’ 
 >-- fs[ISOof_def,SO_def] >>
 pop_assum strip_assume_tac >>
 qby_tac ‘Bd0 o f1 = f0 o Ad0’
 >-- (qsuff_tac ‘Bs o Bd0 o f1 = Bs o f0 o Ad0’ 
     >-- fs[Mono_def] >>
     arw[GSYM o_assoc] >> rw[o_assoc] >>
     qby_tac ‘Bs o Bd0 = Id0(B) o Bt’ >-- fs[ISOof_def] >>
     arw[GSYM o_assoc] >> arw[o_assoc] >>
     qby_tac ‘Id0(B) o Sq(F) = F o Id0(A)’ 
     >-- rw[Id0_Sq] >> arw[GSYM o_assoc] >>
     rw[o_assoc] >>  
     qby_tac ‘Id0(A) o At = As o Ad0’ 
     >-- fs[ISOof_def] >> arw[]) >> arw[] >>
 qby_tac ‘Bd1 o f1 = f0 o Ad1’
 >-- (qsuff_tac ‘Bs o Bd1 o f1 = Bs o f0 o Ad1’ 
     >-- fs[Mono_def] >>
     arw[GSYM o_assoc] >> rw[o_assoc] >>
     qby_tac ‘Bs o Bd1 = Id1(B) o Bt’ >-- fs[ISOof_def] >>
     arw[GSYM o_assoc] >> arw[o_assoc] >>
     qby_tac ‘Id1(B) o Sq(F) = F o Id1(A)’ 
     >-- rw[Id1_Sq] >> arw[GSYM o_assoc] >>
     rw[o_assoc] >>  
     qby_tac ‘Id1(A) o At = As o Ad1’ 
     >-- fs[ISOof_def] >> arw[]) >> arw[] >>
 qby_tac ‘Bi o f0 = f1 o Ai’ 
 >-- (qsuff_tac ‘Bt o Bi o f0 = Bt o f1 o Ai’ 
     >-- fs[Mono_def] >>
     arw[GSYM o_assoc] >> rw[o_assoc] >>
     qby_tac ‘Bt o Bi = Ii(B) o Bs’ >-- fs[ISOof_def] >>
     arw[GSYM o_assoc] >> arw[o_assoc] >>
     rw[GSYM o_assoc] >> rw[Sq_Ii] >> rw[o_assoc] >>
     qby_tac ‘Ii(A) o As = At o Ai’ >-- fs[ISOof_def] >>
     arw[]) >> arw[] >>
 irule $ iffRL Ipreso_alt >> arw[] >>
 rpt strip_tac >>
 qsspecl_then [‘Ad1’,‘Ad0’] assume_tac Pb_def >>
 drule isio_ex >>
 first_x_assum (qsspecl_then [‘Ar’] assume_tac) >>
 qby_tac ‘Ad0 o Ar = Ad0 o Pba1(Ad1, Ad0) & Ad1 o Ar = Ad1 o Pba2(Ad1, Ad0)’
 >-- fs[Icat_def] >>
 first_x_assum drule >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘gf’ >> arw[] >>
 drule isio_ISOof_vo >> 
 first_x_assum (irule o iffRL) >>
 arw[GSYM o_assoc] >> arw[o_assoc] >>
 rev_drule isio_ISOof_vo >>
 first_x_assum drule >>
 first_x_assum (drule o iffLR) >> arw[] >>
 rw[Sq_Rw] >> irule Rw_vo >>
 rw[GSYM Id1_Cod,GSYM Id0_Dom] >>
 qby_tac ‘Id0(A) o At = As o Ad0 & Id1(A) o At = As o Ad1’ 
 >-- fs[ISOof_def] >>
 arw[GSYM o_assoc] >> arw[o_assoc])
(form_goal 
 “!A B F:A->B
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A)
   B0 B1
   Bd0:B1->B0 Bd1:B1->A0 Bi:B0->B1 Br
   Bs:B0->B Bt:B1->Exp(2,B).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) & 
  ISOof(Bd0:B1->B0, Bd1:B1->B0, Bi:B0->B1, Br,
        Bs:B0->B, Bt:B1->Exp(2,B)) ==>
  ?f0:A0->B0 f1:A1->B1. 
   Bs o f0 = F o As & Bt o f1 = Sq(F) o At & 
   IFun(Ad0,Ad1,Ai,Ar,Bd0,Bd1,Bi,Br,f0,f1) 
  ”));




val ISOof_SO = prove_store("ISOof_SO",
e0
(rpt strip_tac >> fs[ISOof_def])
(form_goal
 “!A A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  SO(As) & SO(At)”));

val ISOof_ar_lift_ex = prove_store("ISOof_ar_lift_ex",
e0
(rpt strip_tac >> once_rw[GSYM Tp1_eq_eq] >>
 rev_drule ISOof_SO >>
 pop_assum strip_assume_tac >>
 fs[SO_def] >> rw[Tp1_Tp0_inv] >>
 first_x_assum irule >> rw[Disc_1])
(form_goal
 “!A
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀a:2->A. ∃a1:1->A1. a = Tp0(At o a1)”));


val ISOof_Ii_iff = prove_store("ISOof_Ii_iff",
e0
(rpt strip_tac >>
 qby_tac
 ‘∀a:2->A. ∃a1:1->A1. a = Tp0(At o a1)’ (*in fact unique*)
 >-- (strip_tac >> once_rw[GSYM Tp1_eq_eq] >>
     rev_drule ISOof_SO >>
     pop_assum strip_assume_tac >>
     fs[SO_def] >> rw[Tp1_Tp0_inv] >>
     first_x_assum irule >> rw[Disc_1]) >>
 qby_tac
 ‘∀a0:1->A.∃a00:1->A0. a0 = As o a00’ 
 >-- (rev_drule ISOof_SO >>
     pop_assum strip_assume_tac >>
     fs[SO_def] >>
     strip_tac >> first_x_assum irule >> rw[Disc_1]) >>
 rpt strip_tac >>
     dimp_tac >> rpt strip_tac (* 2 *)
     >-- (first_x_assum (qsspecl_then [‘a0’] assume_tac) >>
         pop_assum strip_assume_tac >> qexists_tac ‘a00’ >> arw[] >>
         qsuff_tac ‘At o a1 = At o Ai o a00’
         >-- (rev_drule ISOof_Mono >> fs[Mono_def]) >>
         qby_tac ‘At o a1 = Tp1(id(a0))’ 
         >-- (irule $ iffLR Tp0_eq_eq >>
             qpick_x_assum ‘a = Tp0(At o a1)’ (assume_tac o GSYM) >>
             arw[] >> rw[Tp0_Tp1_inv]) >>
         arw[] >> 
         first_assum (qsspecl_then [‘id(As o a00)’] assume_tac) >>
         pop_assum strip_assume_tac >>
         arw[] >> rw[Tp1_Tp0_inv] >> 
         once_rw[GSYM Tp0_eq_eq] >> 
         pop_assum (assume_tac o GSYM) >> arw[] >>
         once_rw[GSYM Tp1_eq_eq] >> rw[Tp1_Tp0_inv] >>
         rw[GSYM Ii_ap] >> 
         qsuff_tac ‘Ii(A) o As = At o Ai’ 
         >-- (strip_tac >> arw[GSYM o_assoc]) >>
         rev_drule $ iffLR ISOof_def >> arw[]) >>
     first_assum (qsspecl_then [‘a’] assume_tac) >>
     pop_assum strip_assume_tac >> 
     first_x_assum drule >>
     pop_assum strip_assume_tac >> 
     arw[] >> pop_assum (assume_tac o GSYM) >> arw[] >>
     qby_tac ‘At o Ai = Ii(A) o As’ 
     >-- (rev_drule $ iffLR ISOof_def >> arw[]) >>
     arw[GSYM o_assoc] >> rw[o_assoc] >>
     rw[Ii_ap] >> rw[Tp0_Tp1_inv])
(form_goal
 “!A
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀a:2->A a0:1->A. a = id(a0) ⇔
  (∀a1:1->A1. a = Tp0(At o a1) ⇒
  ∃a00:1->A0. a1 = Ai o a00 & As o a00 = a0)”));



val Tp1_Dom = prove_store("Tp1_Dom",
e0
(rpt strip_tac >> rw[Dom_def,GSYM Tp1_def,dom_def] >>
 rw[Er1_def,Ed_def] >> rw[o_assoc,Pa_distr,p12_of_Pa] >>
 rw[To1_def] >> rw[IdL] >>
 rw[Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa,Pa_distr] >>
 rw[Ev_of_Tp_el'] >> rw[o_assoc,p12_of_Pa] >>
 rw[To1_def] >> rw[one_to_one_Id,IdR]
 )
(form_goal “∀A f:2->A. Dom(Tp1(f)) = dom(f)”));


val Tp1_Cod = prove_store("Tp1_Cod",
e0
(rpt strip_tac >> rw[Cod_def,GSYM Tp1_def,cod_def] >>
 rw[Er1_def,Ed_def] >> rw[o_assoc,Pa_distr,p12_of_Pa] >>
 rw[To1_def] >> rw[IdL] >>
 rw[Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa,Pa_distr] >>
 rw[Ev_of_Tp_el'] >> rw[o_assoc,p12_of_Pa] >>
 rw[To1_def] >> rw[one_to_one_Id,IdR])
(form_goal “∀A f:2->A. Cod(Tp1(f)) = cod(f)”));




val cpnt_Tp1 = prove_store("cpnt_Tp1",
e0
(rpt strip_tac >> rw[cpnt_def] >>
 rw[Pt_def] >> rw[o_assoc,Pa_distr,p12_of_Pa] >>
 rw[GSYM Tp1_def] >>
 rw[Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa] >>
 rw[IdR])
(form_goal “∀A f:2->A dot. cpnt(Tp1(f), dot) = f”));

val vo_1 = prove_store("vo_1",
e0
(rpt strip_tac >> flip_tac >> rw[Tp0_iff_Tp1] >>
 irule $ Nt_ext_cpnt >>
 qsspecl_then [‘f’] assume_tac Tp1_Dom >>
 qsspecl_then [‘f’] assume_tac Tp1_Cod >>
 qsspecl_then [‘g’] assume_tac Tp1_Dom >>
 qsspecl_then [‘g’] assume_tac Tp1_Cod >>
 drule oa_dom_cod >>
 qsspecl_then [‘g @ f’] assume_tac Tp1_Dom >>
 qsspecl_then [‘g @ f’] assume_tac Tp1_Cod >>
 qsspecl_then [‘Tp1(g @ f)’] assume_tac Nt_Dom_Cod >> rfs[] >>
 qsspecl_then [‘dom(f)’,‘cod(f)’,‘cod(g)’,‘Tp1(f)’,‘Tp1(g)’]
 assume_tac vo_Nt_Nt >>
 qsspecl_then [‘Tp1(f)’] assume_tac Nt_Dom_Cod >> rfs[] >>
 qsspecl_then [‘Tp1(g)’] assume_tac Nt_Dom_Cod >> rfs[] >> fs[] >>
 fs[cpsb_def] >> rfs[] >> first_x_assum drule >>
 rpt strip_tac (* 2 *)
 >-- (qexistsl_tac [‘dom(f)’,‘cod(g)’] >> arw[]) >>
 rw[cpnt_Tp1] >>
 qsspecl_then [‘dom(f)’,‘cod(f)’,‘cod(g)’,‘Tp1(f)’,‘Tp1(g)’]
 assume_tac Nt_vo_cpnt >>
 rfs[] >> rw[cpnt_Tp1])
(form_goal “∀A f:2->A g:2->A.
cpsb(g,f) ⇒
g @ f = Tp0(vo(Tp1(g), Tp1(f))) ”));


val ISOof_Ad0_dom_Tp0 = prove_store("ISOof_Ad0_dom_Tp0",
e0
(rpt strip_tac >>arw[] >>
 qby_tac ‘As o Ad0  = Id0(A) o At’ 
 >-- fs[ISOof_def] >>
 arw[GSYM o_assoc] >>rw[o_assoc] >> rw[Id0_Dom] >> 
 rw[GSYM Tp1_Dom] >> rw[Tp1_Tp0_inv])
(form_goal
 “!A
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀f:2->A f1. f = Tp0(At o f1) ⇒ dom(f) = As o Ad0 o f1”));



val ISOof_Ad1_cod_Tp0 = prove_store("ISOof_Ad1_cod_Tp0",
e0
(rpt strip_tac >>arw[] >>
 qby_tac ‘As o Ad1  = Id1(A) o At’ 
 >-- fs[ISOof_def] >>
 arw[GSYM o_assoc] >>rw[o_assoc] >> rw[Id1_Cod] >> 
 rw[GSYM Tp1_Cod] >> rw[Tp1_Tp0_inv])
(form_goal
 “!A
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀f:2->A f1. f = Tp0(At o f1) ⇒ cod(f) = As o Ad1 o f1”));


val ISOof_cpsb = prove_store("ISOof_cpsb",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qsuff_tac ‘As o Ad0 o g1 = As o Ad1 o f1’ 
     >-- (drule ISOof_Mono >> fs[Mono_def]) >>
     rfs[cpsb_def] >>
     drule ISOof_Ad1_cod_Tp0 >>
     first_x_assum rev_drule >> pop_assum (assume_tac o GSYM) >> arw[] >>
     drule ISOof_Ad0_dom_Tp0 >>
     first_x_assum drule >> pop_assum (assume_tac o GSYM) >> arw[]) >>
 drule ISOof_ar_lift_ex >>
 first_assum (qsspecl_then [‘f’] assume_tac) >>
 pop_assum (x_choose_then "f1" assume_tac) >>
 first_x_assum (qsspecl_then [‘g’] assume_tac) >>
 pop_assum (x_choose_then "g1" assume_tac) >>
 rw[cpsb_def] >>
 drule ISOof_Ad0_dom_Tp0 >>
 first_x_assum drule >> 
 drule ISOof_Ad1_cod_Tp0 >>
 first_x_assum rev_drule >>
 arw[] >> 
 qsuff_tac ‘Ad0 o g1 = Ad1 o f1’ >-- (strip_tac >> arw[]) >>
 first_x_assum irule >> arw[])
(form_goal 
  “!A
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀f g:2->A.cpsb(g,f) ⇔ 
  (∀f1 g1. f = Tp0(At o f1) & g = Tp0(At o g1) ⇒
  Ad0 o g1 = Ad1 o f1)
  ”));

val ISOof_Ir_iff = prove_store("ISOof_Ir_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (drule ISOof_ar_lift_ex >>
     first_assum (qsspecl_then [‘f’] assume_tac) >>
     pop_assum (x_choose_then "f1" assume_tac) >>
     first_assum (qsspecl_then [‘g’] assume_tac) >>
     pop_assum (x_choose_then "g1" assume_tac) >>
     qexistsl_tac [‘f1’,‘g1’,‘gf1’] >> rw[GSYM Tp0_iff_Tp1] >>
     arw[] >>
     drule isio_ISOof_vo >>
     first_x_assum (irule o iffRL) >>
     qby_tac ‘Ad0 o g1 = Ad1 o f1’
     >-- (drule ISOof_cpsb >>
         first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
         first_x_assum (irule o iffLR) >> arw[] >>
         arw[cpsb_def] >> fs[]) >> arw[] >>
     once_rw[GSYM Tp0_eq_eq] >>
     qpick_x_assum ‘gf = Tp0(At o gf1)’ (assume_tac o GSYM) >> arw[] >>
     qpick_x_assum ‘f = Tp0(At o f1)’ (assume_tac o GSYM) >>
     arw[] >>
     qpick_x_assum ‘g = Tp0(At o g1)’ (assume_tac o GSYM) >> arw[] >>
     fs[Tp0_iff_Tp1] >> irule vo_1 >> arw[cpsb_def]) >>
 drule ISOof_ar_lift_ex >>
 first_assum (qsspecl_then [‘gf’] assume_tac) >>
 pop_assum (x_choose_then "gf1" assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 arw[] >> fs[GSYM Tp0_iff_Tp1] >>
 qpick_x_assum ‘Tp0(At o f1) = f’ (assume_tac o GSYM) >>
 qpick_x_assum ‘Tp0(At o g1) = g’ (assume_tac o GSYM) >>
 arw[] >> 
 qby_tac ‘gf1' = gf1’
 >-- (drule ISOof_Mono >>
     fs[Mono_def] >> first_x_assum irule >>
     irule $ iffLR Tp0_eq_eq >> arw[]) >> fs[] >>
 qpick_x_assum ‘Tp0(At o gf1) = gf’ (assume_tac o GSYM) >> arw[] >>
 drule isio_ISOof >>
 first_x_assum (qsspecl_then [‘f1’,‘g1’,‘gf1’] assume_tac) >>
 qby_tac ‘Ad0 o g1 = Ad1 o f1’ 
 >-- (drule ISOof_cpsb >>
         first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
         first_x_assum (irule o iffLR) >> arw[] >>
         arw[cpsb_def] >> fs[])  >>
 first_x_assum drule >>
 first_x_assum (drule o iffLR) >>
 once_rw[GSYM Tp1_eq_eq] >> rw[Tp1_Tp0_inv] >>
 qsspecl_then [‘Id1(A)’,‘Id0(A)’] assume_tac Pb_def >>
 drule isio_unique1 >>
 first_x_assum (qspecl_then [‘Ir(A)’] assume_tac) >>
 first_x_assum irule >>
 qexistsl_tac [‘At o f1’,‘At o g1’] >> arw[] >>
 irule $ iffRL isio_iff_vo' >>
 qby_tac ‘Dom(At o g1) = Cod(At o f1)’ 
 >-- (qsuff_tac ‘Dom(Tp1(Tp0(At o g1))) = Cod(Tp1(Tp0(At o f1)))’
     >-- rw[Tp1_Tp0_inv] >>
     rw[Tp1_Dom,Tp1_Cod] >> arw[]) >> arw[] >>
 irule $ iffLR Tp0_eq_eq >>
 rw[Tp0_Tp1_inv] >>
 qsuff_tac ‘Tp0((At o g1)) @ Tp0(At o f1) = Tp0(vo(Tp1(Tp0(At o g1)), Tp1(Tp0(At o f1))))’
 >-- rw[Tp1_Tp0_inv] >>
 irule vo_1 >> arw[cpsb_def])
(form_goal
 “!A
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀f:2->A g:2->A.
  dom(g) = cod(f) ⇒
  ∀gf:2->A. gf = g @ f ⇔
  (∀gf1:1->A1. gf = Tp0(At o gf1) ⇒
  ∃f1:1->A1 g1:1->A1 gf1. 
  isio(Ad0,Ad1,Pba1(Ad1,Ad0),Pba2(Ad1,Ad0),Ar,g1,f1,gf1) & 
  At o f1 = Tp1(f) & At o g1 = Tp1(g) & 
  At o gf1 = Tp1(gf))”));

val Thm26_cl_unique = prove_store("Thm26_cl_unique",
e0
(rpt strip_tac >>
 rev_drule ISOof_ar_lift_ex >>
 first_x_assum (qsspecl_then [‘a’] assume_tac) >>
 pop_assum (x_choose_then "a1" assume_tac) >>
 uex_tac >> qexists_tac ‘Tp0(Bt o f1 o a1)’ >>
 rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘a1’ >> arw[]) >>
 arw[] >> 
 qsuff_tac ‘a1' = a1’
 >-- (strip_tac >> arw[]) >>
 rev_drule ISOof_Mono >>
 qsuff_tac ‘At o a1' = At o a1’ >-- fs[Mono_def] >>
 once_rw[GSYM Tp0_eq_eq] >>
 qpick_x_assum ‘a = Tp0(At o a1)’ (assume_tac o GSYM)>> arw[])
(form_goal 
 “!A B 
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A)
   B0 B1
   Bd0:B1->B0 Bd1:B1->B0 Bi:B0->B1 Br
   Bs:B0->B Bt:B1->Exp(2,B) f0:A0->B0 f1:A1->B1.
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ISOof(Bd0:B1->B0, Bd1:B1->B0, Bi:B0->B1, Br,
        Bs:B0->B, Bt:B1->Exp(2,B)) ⇒
  IFun(Ad0,Ad1,Ai,Ar,Bd0,Bd1,Bi,Br,f0,f1) ⇒
  (!(a : fun(2, A)).
                 ?!(b : fun(2, B)).
                   ?(a1 : fun(1, A1)).
                     a = Tp0(At o a1) & b = Tp0(Bt o f1 o a1))”));



val ISOof_ar_lift_unique = prove_store("ISOof_ar_lift_unique",
e0
(rpt strip_tac >>
 drule ISOof_Mono >>
 fs[Tp0_eq_eq] >> fs[Mono_def] >>
 first_x_assum irule >> arw[])
(form_goal
 “!A
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A).
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ∀a1:1->A1 a1'. Tp0(At o a1) = Tp0(At o a1') ⇒ a1 = a1'”));


val IFun_f1_Ai = prove_store("IFun_f1_Ai",
e0
(rpt strip_tac >>
 qby_tac ‘f1 o Ai = Bi o f0’ 
 >-- fs[IFun_def] >>
 arw[GSYM o_assoc] >> rw[o_assoc] >>
 qby_tac ‘f0 o Ad0 = Bd0 o f1’ 
 >-- fs[IFun_def] >> arw[])
(form_goal
 “!A0 A1 
   Ad0:A1->A0 Ad1 Ai Ar
   B0 B1
   Bd0:B1->B0 Bd1 Bi:B0->B1 Br
   f0:A0->B0 f1:A1->B1. 
   IFun(Ad0,Ad1,Ai,Ar,Bd0,Bd1,Bi,Br,f0,f1) ⇒
   f1 o Ai o Ad0 = Bi o Bd0 o f1”));


val IFun_f1_Ai_Ad1 = prove_store("IFun_f1_Ai_Ad1",
e0
(rpt strip_tac >>
 qby_tac ‘f1 o Ai = Bi o f0’ 
 >-- fs[IFun_def] >>
 arw[GSYM o_assoc] >> rw[o_assoc] >>
 qby_tac ‘f0 o Ad1 = Bd1 o f1’ 
 >-- fs[IFun_def] >> arw[])
(form_goal
 “!A0 A1 
   Ad0:A1->A0 Ad1 Ai Ar
   B0 B1
   Bd0:B1->B0 Bd1 Bi:B0->B1 Br
   f0:A0->B0 f1:A1->B1. 
   IFun(Ad0,Ad1,Ai,Ar,Bd0,Bd1,Bi,Br,f0,f1) ⇒
   f1 o Ai o Ad1 = Bi o Bd1 o f1”));






(*Thm26_cl_id slow *)
val Thm26_cl_id = prove_store("Thm26_cl_id",
e0
(rpt gen_tac >> rpt disch_tac >>
 rpt gen_tac >> strip_tac >>
 once_arw[] >> rev_drule ISOof_Ad1_cod_Tp0 >>
 first_x_assum drule >> rfs[] >> 
 drule ISOof_Ad1_cod_Tp0 >>
 first_x_assum drule >> rfs[] >>
 rev_drule ISOof_Ad0_dom_Tp0 >>
 first_x_assum drule >> rfs[] >>
 drule ISOof_Ad0_dom_Tp0 >> first_x_assum drule >> rfs[] >>
 strip_tac (* 2 *)
 >-- (qexists_tac ‘Ai o Ad0 o a1’ >> strip_tac (* 2 *) >--
     (rev_drule ISOof_Ii >> flip_tac >>
     arw[] >> rpt strip_tac >>
     qby_tac ‘Ai o Ad0 o a1 = a1'’ 
     >-- (rev_drule ISOof_ar_lift_unique >>
         first_x_assum drule >> arw[]) >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qexists_tac ‘Ad0 o a1’ >> rw[]) >>
     drule ISOof_Ii >> flip_tac >> arw[] >>
     rpt strip_tac >>
     qby_tac ‘f1 o Ai o Ad0 o a1 = a1'’
     >-- (drule ISOof_ar_lift_unique >>
         first_x_assum drule >> arw[]) >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qexists_tac ‘Bd0 o f1 o a1’ >> rw[] >> 
     qby_tac ‘f1 o Ai o Ad0 = Bi o Bd0 o f1’ 
     >-- (drule IFun_f1_Ai  >> arw[]) >>
     qsuff_tac ‘(f1 o Ai o Ad0) o a1 = (Bi o Bd0 o f1) o a1’ 
     >-- rw[o_assoc] >> arw[]) >>
 qexists_tac ‘Ai o Ad1 o a1’ >> strip_tac (* 2 *) >--
     (rev_drule ISOof_Ii >> flip_tac >>
     arw[] >> rpt strip_tac >>
     qby_tac ‘Ai o Ad1 o a1 = a1'’ 
     >-- (rev_drule ISOof_ar_lift_unique >>
         first_x_assum drule >> arw[]) >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qexists_tac ‘Ad1 o a1’ >> rw[]) >>
     drule ISOof_Ii >> flip_tac >> arw[] >>
     rpt strip_tac >>
     qby_tac ‘f1 o Ai o Ad1 o a1 = a1'’
     >-- (drule ISOof_ar_lift_unique >>
         first_x_assum drule >> arw[]) >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qexists_tac ‘Bd1 o f1 o a1’ >> rw[] >> 
     qby_tac ‘f1 o Ai o Ad1 = Bi o Bd1 o f1’ 
     >-- (drule IFun_f1_Ai_Ad1  >> arw[]) >>
     qsuff_tac ‘(f1 o Ai o Ad1) o a1 = (Bi o Bd1 o f1) o a1’ 
     >-- rw[o_assoc] >> arw[])
(form_goal 
 “!A B 
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A)
   B0 B1
   Bd0:B1->B0 Bd1:B1->B0 Bi:B0->B1 Br
   Bs:B0->B Bt:B1->Exp(2,B) f0:A0->B0 f1:A1->B1.
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ISOof(Bd0:B1->B0, Bd1:B1->B0, Bi:B0->B1, Br,
        Bs:B0->B, Bt:B1->Exp(2,B)) ⇒
  IFun(Ad0,Ad1,Ai,Ar,Bd0,Bd1,Bi,Br,f0,f1) ⇒
  (!(a : fun(2, A))  (b : fun(2, B)).
                 (?(a1 : fun(1, A1)).
                     a = Tp0(At o a1) & b = Tp0(Bt o f1 o a1)) ==>
                 (?(a1 : fun(1, A1)).
                     id(dom(a)) = Tp0(At o a1) &
                     id(dom(b)) = Tp0(Bt o f1 o a1)) &
                 ?(a1 : fun(1, A1)).
                   id(cod(a)) = Tp0(At o a1) &
                   id(cod(b)) = Tp0(Bt o f1 o a1))”));



val Thm26_cl_oa = prove_store("Thm26_cl_oa",
e0
(rpt gen_tac >> rpt disch_tac >>
 rpt gen_tac >> strip_tac >>
 disch_tac >>
 pop_assum (x_choose_then "agf0" assume_tac) >>
 rpt gen_tac >>
 disch_tac >> pop_assum strip_assume_tac >> 
 arw[] >> drule ISOof_Ir_iff >>
 qby_tac ‘dom(Tp0(Bt o f1 o a1')) = cod(Tp0(Bt o f1 o a1))’ 
 >-- cheat >>
 first_x_assum drule >>
 arw[] >> pop_assum (K all_tac) >>
 rpt strip_tac >>
 rw[Tp1_Tp0_inv] >>
 qexistsl_tac [‘f1 o a1’,‘f1 o a1'’,‘f1 o agf0’] >>
 rw[] >>
 drule isio_ISOof >>
 first_x_assum (irule o iffRL) >>
 qby_tac ‘Bd0 o f1 o a1' = Bd1 o f1 o a1’ >-- cheat >> arw[] >>
 irule $ iffRL isio_iff_vo' >>
 qby_tac ‘Dom(Bt o f1 o a1') = Cod(Bt o f1 o a1)’
 >-- cheat >> arw[] >>
 qsuff_tac
 ‘Bt o f1 o agf0 = vo(Tp1(Tp0(Bt o f1 o a1')), Tp1(Tp0(Bt o f1 o a1)))’ 
 >-- rw[Tp1_Tp0_inv] >>
 drule vo_1 >> 
 qby_tac ‘cpsb(Tp0(Bt o f1 o a1'),Tp0(Bt o f1 o a1))’
 >-- arw[cpsb_def] >>
 drule $ GSYM vo_1 >>
 once_rw[GSYM Tp0_eq_eq] >> arw[] >> 
 Ipreso_alt
 
 
 qby_tac ‘’


 qby_tac ‘ Bd0 o g# = Bd1 o f#’
 )
(form_goal 
 “!A B 
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A)
   B0 B1
   Bd0:B1->B0 Bd1:B1->B0 Bi:B0->B1 Br
   Bs:B0->B Bt:B1->Exp(2,B) f0:A0->B0 f1:A1->B1.
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) ⇒
  ISOof(Bd0:B1->B0, Bd1:B1->B0, Bi:B0->B1, Br,
        Bs:B0->B, Bt:B1->Exp(2,B)) ⇒
  IFun(Ad0,Ad1,Ai,Ar,Bd0,Bd1,Bi,Br,f0,f1) ⇒
  !(af : fun(2, A))  (ag : fun(2, A))  (h : fun(2, B)).
               cpsb(ag, af) ==>
               (?(a1 : fun(1, A1)).
                   ag @ af = Tp0(At o a1) & h = Tp0(Bt o f1 o a1)) ==>
               !(af1 : fun(2, B))  (ag1 : fun(2, B)).
                 (?(a1 : fun(1, A1)).
                     af = Tp0(At o a1) & af1 = Tp0(Bt o f1 o a1)) &
                 (?(a1 : fun(1, A1)).
                     ag = Tp0(At o a1) & ag1 = Tp0(Bt o f1 o a1)) ==>
                 h = ag1 @ af1”));





val Thm26_R2L = prove_store("Thm26_R2L",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘∃F:A->B. 
   ∀a:2->A b:2->B. 
   (∃a1:1->A1. a = Tp0(At o a1) & b = Tp0(Bt o f1 o a1)) ⇔
   F o a = b’
 >-- (strip_tac >> qexists_tac ‘F’ >> arw[]) >>
 match_mp_tac
 (CC5 |> qspecl [‘A’,‘B’] 
 |> fVar_sInst_th “R(a:2->A,b:2->B)”
    “∃a1:1->A1. 
     a:2->A = Tp0(At o a1) & b:2->B = Tp0(Bt:B1->Exp(2,B) o f1 o a1)”) >>
 qby_tac
 ‘(!(a : fun(2, A)).
                 ?!(b : fun(2, B)).
                   ?(a1 : fun(1, A1)).
                     a = Tp0(At o a1) & b = Tp0(Bt o f1 o a1))’
 >-- (irule Thm26_cl_unique >>
     qexistsl_tac 
     [‘A0’,‘Ad0’,‘Ad1’,‘Ai’,‘Ar’,‘As’,‘B0’,‘Bd0’,‘Bd1’,‘Bi’,‘Br’,‘Bs’,‘f0’] >>
     arw[]) >> arw[] >>
 qby_tac
 ‘(!(a : fun(2, A))  (b : fun(2, B)).
                 (?(a1 : fun(1, A1)).
                     a = Tp0(At o a1) & b = Tp0(Bt o f1 o a1)) ==>
                 (?(a1 : fun(1, A1)).
                     id(dom(a)) = Tp0(At o a1) &
                     id(dom(b)) = Tp0(Bt o f1 o a1)) &
                 ?(a1 : fun(1, A1)).
                   id(cod(a)) = Tp0(At o a1) &
                   id(cod(b)) = Tp0(Bt o f1 o a1))’
 
 >-- (rpt gen_tac  >> strip_tac >> irule Thm26_cl_id >>
     strip_tac (* 2 *)
     >-- (qexistsl_tac 
     [‘A0’,‘Ad0’,‘Ad1’,‘Ai’,‘Ar’,‘As’,‘B0’,‘Bd0’,‘Bd1’,‘Bi’,‘Br’,‘Bs’,‘f0’] >>
     arw[]) >> qexists_tac ‘a1’ >> arw[]) >>
 arw[] >>
 


 qby_tac
 ‘∀a0:1->A.∃a00:1->A0. a0 = As o a00’ 
 >-- (rev_drule ISOof_SO >>
     pop_assum strip_assume_tac >>
     fs[SO_def] >>
     strip_tac >> first_x_assum irule >> rw[Disc_1]) >>


 qby_tac
 ‘∀a:2->A. ∃a1:1->A1. a = Tp0(At o a1)’ (*in fact unique*)
 >-- (strip_tac >> once_rw[GSYM Tp1_eq_eq] >>
     rev_drule ISOof_SO >>
     pop_assum strip_assume_tac >>
     fs[SO_def] >> rw[Tp1_Tp0_inv] >>
     first_x_assum irule >> rw[Disc_1]) >>
 
 
                               
)
(form_goal
 “!A B 
   A0 A1 
   Ad0:A1->A0 Ad1:A1->A0 Ai:A0->A1 Ar
   As:A0->A At:A1->Exp(2,A)
   B0 B1
   Bd0:B1->B0 Bd1:B1->B0 Bi:B0->B1 Br
   Bs:B0->B Bt:B1->Exp(2,B) f0:A0->B0 f1:A1->B1.
  ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A)) & 
  ISOof(Bd0:B1->B0, Bd1:B1->B0, Bi:B0->B1, Br,
        Bs:B0->B, Bt:B1->Exp(2,B)) & 
  IFun(Ad0,Ad1,Ai,Ar,Bd0,Bd1,Bi,Br,f0,f1) ⇒
  ∃F:A->B. 
   ∀a:2->A b:2->B. F o a = b ⇔
   ∃a1:1->A1. a = Tp0(At o a1) & b = Tp0(Bt o f1 o a1) ”));

