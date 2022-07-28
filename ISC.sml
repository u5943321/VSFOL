
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
 qby_tac ‘Bd0 o f1 = f0 o Ad0’
 >-- qsuff_tac ‘Bs o Bd0 o f1 = Bs o f0 o Ad0’ 
     >-- cheat >>
     arw[GSYM o_assoc] >> rw[o_assoc] >>
     qby_tac ‘Bs o Bd0 = Id0(B) o Bt’ >-- cheat >>
     arw[GSYM o_assoc] >> arw[o_assoc] >>
     qby_tac ‘ Id0(B) o Sq(F) = F o Id0(A)’ 
     >-- cheat >> arw[GSYM o_assoc] >>
     rw[o_assoc] >> 
 )
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

“ISOof(Ad0:A1->A0, Ad1:A1->A0, Ai:A0->A1, Ar,
        As:A0->A, At:A1->Exp(2,A))”

val Thm26_R2L = prove_store("Thm26_R2L",
e0
()
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
  !f0:S->A f1:T->A. 
  IFun()”));
