
(*is composition only meaninngful if the map r outputs an arrow with correct dom and cod*)
val isio_def = 
 qdefine_psym("isio",
 [‘d0:C1->C0’,‘d1:C1->C0’,
  ‘p1:C1C1->C1’,‘p2:C1C1->C1’,‘r:C1C1->C1’,
  ‘g:A->C1’,‘f:A->C1’,‘gf:A->C1’])
‘isPb(d1,d0,p1,p2) &
 d0 o r = d0 o p1 & d1 o r = d1 o p2 & 
 d0 o g = d1 o f & 
 ?fg0:A->C1C1. p1 o fg0 = f & p2 o fg0 = g & 
 r o fg0 = gf’




val isio_unique1 = prove_store("isio_unique1",
e0
(rpt strip_tac >>
 drule $ iffLR isio_def >>
 pop_assum strip_assume_tac >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 rev_drule $ iffLR isio_def >>
 pop_assum strip_assume_tac >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 qsuff_tac ‘fg0' = fg0’ 
 >-- (strip_tac >> once_arw[] >> rw[]) >>
 drule Pb12_eq_eq >>
 first_x_assum irule>> once_arw[] >> rw[])
(form_goal
 “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1. 
   isPb(d1,d0,p1,p2) ==>
   !r A g f:A->C1 gf1 gf2:A->C1.
   isio(d0,d1,p1,p2,r,g,f,gf1) &
   isio(d0,d1,p1,p2,r,g,f,gf2) ==>
   gf1 = gf2
   ”));


val isio_compatible = prove_store("isio_compatible",
e0
()
(form_goal
 “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1. 
   isPb(d1,d0,p1,p2) ==>
   !Pb p1':Pb->C1 p2':Pb->C1.
   isPb(d1,d0,p1',p2') ==>
   ”));


val isio_ex = prove_store("isio_ex",
e0
(rpt strip_tac>>
 once_rw[isio_def] >>
 once_arw[] >> rw[] >>
 drule through_Pb >>
 qpick_x_assum ‘d0 o g = d1 o f’ (assume_tac o GSYM) >>
 first_x_assum (drule o iffLR) >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘r o a0’,‘a0’] >> once_arw[] >> rw[])
(form_goal
 “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1. 
   isPb(d1,d0,p1,p2) ==>
   !r. 
   d0 o r = d0 o p1 & d1 o r = d1 o p2 ==>
   !A g f:A->C1.
   d0 o g = d1 o f ==>
   ?gf:A->C1.isio(d0,d1,p1,p2,r,g,f,gf)
   ”));


val isio_dc1 = prove_store("isio_dc1",
e0
(rpt gen_tac >> strip_tac >>
 drule $ iffLR isio_def >>
 pop_assum strip_assume_tac >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 once_arw[GSYM o_assoc] >>
 once_arw[] >> rw[o_assoc] >> once_arw[] >> rw[])
(form_goal “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1 r
   A g f:A->C1 gf:A->C1.
   isio(d0,d1,p1,p2,r,g,f,gf) ==>
   d0 o gf = d0 o f & d1 o gf = d1 o g”));



val isio_cpsb1 = prove_store("isio_cpsb1",
e0
(rpt strip_tac >>
 drule $ iffLR isio_def >> once_arw[] >> rw[])
(form_goal “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1 r
   A g f:A->C1 gf:A->C1.isio(d0,d1,p1,p2,r,g,f,gf) ==>
   d0 o g = d1 o f”));


val isio_cpsb = prove_store("isio_cpsb",
e0
(rpt gen_tac >> strip_tac >>
 rw[isio_cpsb1])
(form_goal “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1.
   isPb(d1,d0,p1,p2) ==>
   !r A g f:A->C1 gf:A->C1.isio(d0,d1,p1,p2,r,g,f,gf) ==>
   d0 o g = d1 o f”));


val isio_dom_cod1 = prove_store("isio_dom_cod1",
e0
(rpt gen_tac >> strip_tac >>
 drule $ iffLR isio_def >> 
 pop_assum strip_assume_tac >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 arw[GSYM o_assoc] >> arw[o_assoc])
(form_goal “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1 r
   A g f:A->C1 gf:A->C1.isio(d0,d1,p1,p2,r,g,f,gf) ==>
   d0 o gf = d0 o f & d1 o gf = d1 o g”));


val isio_dom_cod = prove_store("isio_dom_cod",
e0
(rpt gen_tac >> strip_tac >>
 rw[isio_dom_cod1])
(form_goal “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1.
   isPb(d1,d0,p1,p2) ==>
   !r
   A g f:A->C1 gf:A->C1.isio(d0,d1,p1,p2,r,g,f,gf) ==>
   d0 o gf = d0 o f & d1 o gf = d1 o g”));


val isio_dom = prove_store("isio_dom",
e0
(rpt strip_tac >> drule isio_dom_cod >>
 first_x_assum drule >> arw[])
(form_goal “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1.
   isPb(d1,d0,p1,p2) ==>
   !r
   A g f:A->C1 gf:A->C1.isio(d0,d1,p1,p2,r,g,f,gf) ==>
   d0 o gf = d0 o f”));


val isio_cod = prove_store("isio_cod",
e0
(rpt strip_tac >> drule isio_dom_cod >>
 first_x_assum drule >> arw[])
(form_goal “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1.
   isPb(d1,d0,p1,p2) ==>
   !r
   A g f:A->C1 gf:A->C1.isio(d0,d1,p1,p2,r,g,f,gf) ==>
    d1 o gf = d1 o g”));





val isio_o_r1 = prove_store("isio_o_r1",
e0
(rpt strip_tac >> 
 rw[isio_def] >> arw[] >>
 qexistsl_tac [‘gf0’] >> arw[])
(form_goal
 “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1.
   isPb(d1, d0, p1, p2) ==>
   !r.d0 o r = d0 o p1 &
   d1 o r = d1 o p2 ==>
   !A g f:A->C1 gf0:A->C1C1.
   d0 o g = d1 o f  & 
   p1 o gf0 = f & p2 o gf0 = g ==>
   isio(d0,d1,p1,p2,r,g,f,r o gf0)
”));





val tuple_ex = prove_store("tuple_ex",
e0
(rpt strip_tac >>
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule through_Pb >>
 first_x_assum (qsspecl_then [‘t1’,‘t2’] assume_tac) >>
 rfs[] >>
 qsspecl_then [‘d1 o r’,‘d0’] assume_tac Pb_def >>
 drule through_Pb >>
 first_x_assum (qsspecl_then [‘a0’,‘t3’] assume_tac)>>
 rfs[] >> fs[o_assoc] >> rfs[] >>
 qexists_tac ‘a0'’ >> arw[])
(form_goal
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1 r.
  d0 o r = d0 o Pba1(d1, d0) & 
  d1 o r = d1 o Pba2(d1, d0) ==>
  !T t3 t2 t1:T->C1. 
   d0 o t2 = d1 o t1 & 
   d0 o t3 = d1 o t2 ==> 
 ?tuple:T->Pbo(d1 o r,d0).
   Pba1(d1,d0) o Pba1(d1 o r,d0) o tuple = t1 & 
   Pba2(d1,d0) o Pba1(d1 o r,d0) o tuple = t2 & 
   Pba2(d1 o r,d0) o tuple = t3”));

val cr1_aiso_cr1_ex = prove_store("cr1_aiso_cr1_ex",
e0
(rpt strip_tac >>
 qby_tac
 ‘?cr1.
  Pba1(d1, d0) o cr1 = r o Pba1(d1 o r, d0) &
  Pba2(d1, d0) o cr1 = Pba2(d1 o r, d0)’
 >-- (qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule through_Pb >> 
     first_x_assum $ irule o iffLR >>
     rw[GSYM o_assoc,Pb_eqn]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘cr1’ >> once_arw[] >> rw[] >> 
 qby_tac
 ‘?c1r. 
  Pba1(d1, d0) o c1r = Pba1(d1, d0 o r) &
  Pba2(d1, d0) o c1r = r o Pba2(d1, d0 o r)’ 
 >-- (qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum $ irule o iffLR >>
     rw[GSYM o_assoc,Pb_eqn]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘?c1r aiso.
               Pba1(d1, d0) o c1r = Pba1(d1, d0 o r) &
               Pba2(d1, d0) o c1r = r o Pba2(d1, d0 o r) &
               Pba1(d1, (d0 o r)) o aiso = Pba1(d1, d0) o Pba1(d1 o r, d0) &
               Pba1(d1, d0) o Pba2(d1, (d0 o r)) o aiso = Pba2(d1, d0) o
                 Pba1(d1 o r, d0) &
               Pba2(d1, d0) o Pba2(d1, (d0 o r)) o aiso = Pba2(d1 o r, d0)’  
 >-- (strip_tac >> qexistsl_tac [‘aiso’,‘c1r’] >>
     arw[]) >>
 qexists_tac ‘c1r’ >> once_arw[] >> rw[] >>
 qby_tac 
 ‘d1 o Pba2(d1, d0) o Pba1(d1 o r, d0) = 
  d0 o Pba2(d1 o r, d0)’
 >-- (qpick_x_assum ‘d1 o r = d1 o Pba2(d1, d0)’
     (assume_tac o GSYM) >> arw[GSYM o_assoc]  >>
     rw[Pb_eqn]) >> 
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule through_Pb >>
 first_x_assum
 (qsspecl_then [‘Pba2(d1,d0) o Pba1(d1 o r,d0)’,‘Pba2(d1 o r,d0)’] assume_tac) >>
 first_x_assum (drule o iffLR) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘d1 o Pba1(d1, d0) o Pba1(d1 o r, d0) = (d0 o r) o a0’
 >-- (arw[] >> rw[o_assoc] >> arw[] >> 
     rw[GSYM o_assoc,Pb_eqn]) >>
 qsspecl_then [‘d1’,‘d0 o r’] assume_tac Pb_def >>
 drule $ through_Pb >>
 first_x_assum 
 (qsspecl_then 
  [‘Pba1(d1,d0) o Pba1(d1 o r,d0)’,‘a0’]
  assume_tac)  >>
 first_x_assum (drule o iffLR) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘a0'’ >> arw[])
(form_goal
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1 r.
  d0 o r = d0 o Pba1(d1, d0) & 
  d1 o r = d1 o Pba2(d1, d0) ==>
  ?cr1 aiso c1r.Pba1(d1, d0) o cr1 = r o Pba1(d1 o r, d0) &
               Pba2(d1, d0) o cr1 = Pba2(d1 o r, d0) &
               Pba1(d1, d0) o c1r = Pba1(d1, d0 o r) &
               Pba2(d1, d0) o c1r = r o Pba2(d1, d0 o r) &
               Pba1(d1, (d0 o r)) o aiso = Pba1(d1, d0) o Pba1(d1 o r, d0) &
               Pba1(d1, d0) o Pba2(d1, (d0 o r)) o aiso = Pba2(d1, d0) o
                 Pba1(d1 o r, d0) &
               Pba2(d1, d0) o Pba2(d1, (d0 o r)) o aiso = Pba2(d1 o r, d0)”));

val Iassoc_alt = prove_store("Iassoc_alt",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >--
 (rpt strip_tac >>
 drule $ iffLR Iassoc_def >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?t21.
  isio(d0, d1, Pba1(d1, d0), Pba2(d1, d0), r, t2, t1, t21)’
 >-- (irule isio_ex >> arw[Pb_def]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?t32.
  isio(d0, d1, Pba1(d1, d0), Pba2(d1, d0), r, t3, t2, t32)’
 >-- (irule isio_ex >> arw[Pb_def]) >>
 pop_assum strip_assume_tac >> 
 qby_tac
 ‘?cr1 aiso c1r.Pba1(d1, d0) o cr1 = r o Pba1(d1 o r, d0) &
               Pba2(d1, d0) o cr1 = Pba2(d1 o r, d0) &
               Pba1(d1, d0) o c1r = Pba1(d1, d0 o r) &
               Pba2(d1, d0) o c1r = r o Pba2(d1, d0 o r) &
               Pba1(d1, (d0 o r)) o aiso = Pba1(d1, d0) o Pba1(d1 o r, d0) &
               Pba1(d1, d0) o Pba2(d1, (d0 o r)) o aiso = Pba2(d1, d0) o
                 Pba1(d1 o r, d0) &
               Pba2(d1, d0) o Pba2(d1, (d0 o r)) o aiso = Pba2(d1 o r, d0)’ 
 >-- (qsspecl_then [‘d0’,‘d1’,‘i’,‘r’] assume_tac
     cr1_aiso_cr1_ex >> 
     first_x_assum irule >> arw[]) >>
 pop_assum strip_assume_tac >>
 first_x_assum 
 (qsspecl_then [‘cr1’,‘aiso’,‘c1r’] assume_tac) >> rfs[] >> 
 qby_tac
 ‘?t321l. isio(d0, d1, Pba1(d1, d0), Pba2(d1, d0), r, t3, t21, t321l)’ 
 >-- (qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule isio_ex >> 
     first_x_assum irule >> arw[] >>
     drule isio_cod >> flip_tac >>
     first_x_assum irule >> 
     qexistsl_tac [‘t1’,‘r’] >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?t321r. isio(d0, d1, Pba1(d1, d0), Pba2(d1, d0), r, t32, t1, t321r)’ 
 >-- (qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule isio_ex >> 
     first_x_assum irule >> arw[] >>
     qpick_x_assum ‘d0 o t2 = d1 o t1’ (assume_tac o GSYM) >>
     arw[] >> 
     drule isio_dom >>
     first_x_assum irule >> 
     qexistsl_tac [‘t3’,‘r’] >> arw[]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘t321r = t321l’ 
 >-- (strip_tac >>
     qexistsl_tac [‘t321l’,‘t32’,‘t21’] >> arw[] >> fs[]) >>
 qsuff_tac 
 ‘?tuple:T->Pbo(d1 o r, d0). 
  t321l = r o cr1 o tuple & t321r = r o c1r o aiso o tuple’
 >-- (strip_tac >>
     arw[] >> 
     qsuff_tac ‘(r o cr1) o tuple = 
                            (r o c1r o aiso) o tuple’ 
     >-- rw[o_assoc] >> arw[] >> strip_tac >>
    arw[]) >>
 qsuff_tac
 ‘?tuple:T->Pbo(d1 o r,d0).
   Pba1(d1,d0) o Pba1(d1 o r,d0) o tuple = t1 & 
   Pba2(d1,d0) o Pba1(d1 o r,d0) o tuple = t2 & 
   Pba2(d1 o r,d0) o tuple = t3’ >-- (strip_tac >>
 qexists_tac ‘tuple’ >>
 strip_tac (* 2 *)
 >-- (qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule isio_unique1 >>
     first_x_assum  
     (qsspecl_then [‘r’,‘t3’,‘t21’,‘t321l’,‘r o cr1 o tuple’] assume_tac) >> rfs[] >>
     first_x_assum irule >>
     drule isio_o_r1 >>
     first_x_assum (qsspecl_then [‘r’] assume_tac) >>
     rfs[] >>
     first_x_assum irule >> 
     arw[GSYM o_assoc] >>
     qby_tac ‘d1 o t2 = d1 o t21’ 
     >-- (flip_tac >> drule isio_cod >> 
         first_x_assum irule >> 
         qexistsl_tac [‘t1’,‘r’] >> arw[]) >> arw[] >>
     rw[o_assoc] >> 
     drule isio_unique1 >>
     first_x_assum (qsspecl_then [‘r’,‘t2’,‘t1’,‘r o Pba1((d1 o r), d0) o tuple’,‘t21’] assume_tac) >> rfs[] >>
     first_x_assum irule >> 
     drule isio_o_r1 >>
     first_x_assum (qsspecl_then [‘r’] assume_tac) >> rfs[]>>
     first_x_assum irule >> arw[]) >>
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule isio_unique1 >> 
 first_x_assum  
     (qsspecl_then [‘r’,‘t32’,‘t1’,‘t321r’,‘r o c1r o aiso o tuple’] assume_tac) >> rfs[] >> 
 first_x_assum irule >>
 drule isio_o_r1 >>
 first_x_assum (qsspecl_then [‘r’] assume_tac) >> rfs[] >>
 first_x_assum irule >> arw[GSYM o_assoc] >>
 arw[o_assoc] >>
 qby_tac ‘d0 o t32 = d1 o t1’ 
 >-- (qpick_x_assum ‘d0 o t2 = d1 o t1’ 
      (assume_tac o GSYM) >>
     arw[] >> drule isio_dom >>
     first_x_assum irule >> 
     qexistsl_tac [‘t3’,‘r’] >> arw[]) >> 
 arw[] >>
 drule isio_unique1 >>
 first_x_assum (qsspecl_then [‘r’,‘t3’,‘t2’,‘r o Pba2(d1, (d0 o r)) o aiso o tuple’,‘t32’] assume_tac) >>
 rfs[] >> first_x_assum irule >>
 drule isio_o_r1 >>
 first_x_assum (qsspecl_then [‘r’] assume_tac) >> rfs[] >>
 first_x_assum irule >> arw[] >>
 qsuff_tac
 ‘(Pba1(d1, d0) o Pba2(d1, (d0 o r)) o aiso) o tuple = t2 &
  (Pba2(d1, d0) o Pba2(d1, (d0 o r)) o aiso) o tuple = t3’
 >-- rw[o_assoc] >>
 arw[] >> arw[o_assoc]) >>
 qsspecl_then [‘d0’,‘d1’,‘i’,‘r’] assume_tac tuple_ex >>
 first_x_assum irule >>
 arw[]) >> 
 rw[Iassoc_def] >> 
 rpt strip_tac >>
 irule $ iffLR fun_ext >> strip_tac >>
 rw[o_assoc] >> 
 qabbrev_tac ‘Pba2(d1 o r,d0) o a = t3’ >>
 qabbrev_tac ‘Pba2(d1,d0) o Pba1(d1 o r,d0) o a = t2’ >>
 qabbrev_tac ‘Pba1(d1,d0) o Pba1(d1 o r,d0) o a = t1’ >> 
 qby_tac ‘d0 o t2 = d1 o t1’ 
 >-- (qpick_x_assum ‘Pba1(d1, d0) o Pba1((d1 o r), d0) o a = t1’ (assume_tac o GSYM) >> arw[] >>
     qpick_x_assum ‘Pba2(d1, d0) o Pba1((d1 o r), d0) o a = t2’ (assume_tac o GSYM) >>
     arw[] >> rw[Pb_eqn,GSYM o_assoc]) >>
 qby_tac ‘d0 o t3 = d1 o t2’ 
 >-- (qpick_x_assum ‘Pba2((d1 o r), d0) o a = t3’
     (assume_tac o GSYM) >> arw[] >>
     qpick_x_assum ‘Pba2(d1, d0) o Pba1((d1 o r), d0) o a = t2’ (assume_tac o GSYM) >> arw[] >>
     rw[GSYM o_assoc,GSYM Pb_eqn] >> rw[o_assoc] >>
     arw[GSYM o_assoc]) >>
 first_x_assum
 (qsspecl_then [‘t3’,‘t2’,‘t1’] assume_tac) >>
 rfs[] >>
 qsuff_tac ‘r o cr1 o a = t321 & r o c1r o aiso o a = t321’ 
 >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (irule isio_unique1 >>
     qexistsl_tac 
     [‘C0’,‘d0’,‘d1’,‘Pbo(d1,d0)’,
      ‘Pba1(d1,d0)’,‘Pba2(d1,d0)’,‘r’,‘t21’,‘t3’] >>
     arw[] >> 
     qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >> 
     arw[] >> drule isio_o_r1 >>
     first_x_assum (qsspecl_then [‘r’] assume_tac) >>
     rfs[] >>
     first_x_assum irule >> strip_tac (* 2 *)
     >-- (arw[GSYM o_assoc] >> 
         rw[o_assoc] >>
         drule isio_unique1 >>
         first_x_assum (qsspecl_then [‘r’,‘t2’,‘t1’,‘r o Pba1((d1 o r), d0) o a’,‘t21’] assume_tac) >> rfs[] >> 
         first_x_assum irule >>
         drule isio_o_r1 >> 
         first_x_assum (qsspecl_then [‘r’] assume_tac) >>
         rfs[] >> first_x_assum irule >> arw[]) >>
     arw[GSYM o_assoc] >>
     drule isio_dom_cod >> flip_tac >>
     qsuff_tac
     ‘d0 o t21 = d0 o t1 & d1 o t21 = d1 o t2’ 
     >-- (strip_tac >> arw[]) >>
     first_x_assum irule >> qexists_tac ‘r’ >> arw[]) >>
(*second subgoal,.  r o c1r o aiso o a = t321*)
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule isio_unique1 >>
 first_x_assum 
(qsspecl_then [‘r’,‘t32’,‘t1’,‘r o c1r o aiso o a’,‘t321’] assume_tac)>>
first_x_assum irule>> arw[] >> 
drule isio_o_r1 >>
first_x_assum (qsspecl_then [‘r’] assume_tac) >>
rfs[] >>
qby_tac ‘d0 o t32 = d1 o t1’
>-- (drule isio_cpsb >> first_x_assum irule >>
    qexistsl_tac [‘t321’,‘r’] >> arw[]) >>
first_x_assum (qsspecl_then [‘t32’,‘t1’,‘c1r o aiso o a’] assume_tac) >>
rfs[] >>
first_x_assum irule >> arw[GSYM o_assoc] >>
arw[o_assoc] >>
drule isio_unique1 >>
first_x_assum (qsspecl_then [‘r’,‘t3’,‘t2’,‘r o Pba2(d1, (d0 o r)) o aiso o a’,‘t32’] assume_tac) >> rfs[] >>
first_x_assum irule >> 
drule isio_o_r1 >>
first_x_assum (qsspecl_then [‘r’] assume_tac) >>
rfs[] >>
first_x_assum irule >> arw[] >> 
qsuff_tac
 ‘Pba1(d1, d0) o (Pba2(d1, (d0 o r)) o aiso) o a = t2 &
  Pba2(d1, d0) o (Pba2(d1, (d0 o r)) o aiso) o a = t3’ 
 >-- rw[o_assoc] >>
 arw[] >> arw[GSYM o_assoc] >> arw[o_assoc])
(form_goal 
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1 r.
  d0 o r = d0 o Pba1(d1, d0) & 
  d1 o r = d1 o Pba2(d1, d0) ==>
  (Iassoc(d0,d1,i,r) <=> 
  !T t3 t2 t1:T->C1. 
   d0 o t2 = d1 o t1 & 
   d0 o t3 = d1 o t2 ==>
   ?t321:T->C1 t32 t21.
   isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,t2,t1,t21) & 
   isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,t3,t2,t32) &
   isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,t32,t1,t321) &
   isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,t3,t21,t321))
   ”));


val Iassoc_alt_2 = prove_store("Iassoc_alt_2",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
 drule $ iffLR Iassoc_def >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?t21.
  isio(d0, d1, Pba1(d1, d0), Pba2(d1, d0), r, t2, t1, t21)’
 >-- (irule isio_ex >> arw[Pb_def]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?t32.
  isio(d0, d1, Pba1(d1, d0), Pba2(d1, d0), r, t3, t2, t32)’
 >-- (irule isio_ex >> arw[Pb_def]) >>
 pop_assum strip_assume_tac >> 
 qby_tac
 ‘?cr1 aiso c1r.Pba1(d1, d0) o cr1 = r o Pba1(d1 o r, d0) &
               Pba2(d1, d0) o cr1 = Pba2(d1 o r, d0) &
               Pba1(d1, d0) o c1r = Pba1(d1, d0 o r) &
               Pba2(d1, d0) o c1r = r o Pba2(d1, d0 o r) &
               Pba1(d1, (d0 o r)) o aiso = Pba1(d1, d0) o Pba1(d1 o r, d0) &
               Pba1(d1, d0) o Pba2(d1, (d0 o r)) o aiso = Pba2(d1, d0) o
                 Pba1(d1 o r, d0) &
               Pba2(d1, d0) o Pba2(d1, (d0 o r)) o aiso = Pba2(d1 o r, d0)’ 
 >-- (qsspecl_then [‘d0’,‘d1’,‘i’,‘r’] assume_tac
     cr1_aiso_cr1_ex >> 
     first_x_assum irule >> arw[]) >>
 pop_assum strip_assume_tac >>
 first_x_assum 
 (qsspecl_then [‘cr1’,‘aiso’,‘c1r’] assume_tac) >> rfs[] >> 
 qby_tac
 ‘?t321l. isio(d0, d1, Pba1(d1, d0), Pba2(d1, d0), r, t3, t21, t321l)’ 
 >-- (qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule isio_ex >> 
     first_x_assum irule >> arw[] >>
     drule isio_cod >> flip_tac >>
     first_x_assum irule >> 
     qexistsl_tac [‘t1’,‘r’] >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?t321r. isio(d0, d1, Pba1(d1, d0), Pba2(d1, d0), r, t32, t1, t321r)’ 
 >-- (qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule isio_ex >> 
     first_x_assum irule >> arw[] >>
     qpick_x_assum ‘d0 o t2 = d1 o t1’ (assume_tac o GSYM) >>
     arw[] >> 
     drule isio_dom >>
     first_x_assum irule >> 
     qexistsl_tac [‘t3’,‘r’] >> arw[]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘t321r = t321l’ 
 >-- (strip_tac >>
     qexistsl_tac [‘t321l’,‘t32’,‘t21’] >> arw[] >> fs[]) >>
 qsuff_tac 
 ‘?tuple:2->Pbo(d1 o r, d0). 
  t321l = r o cr1 o tuple & t321r = r o c1r o aiso o tuple’
 >-- (strip_tac >>
     arw[] >> 
     qsuff_tac ‘(r o cr1) o tuple = 
                            (r o c1r o aiso) o tuple’ 
     >-- rw[o_assoc] >> arw[] >> strip_tac >>
    arw[]) >>
 qsuff_tac
 ‘?tuple:2->Pbo(d1 o r,d0).
   Pba1(d1,d0) o Pba1(d1 o r,d0) o tuple = t1 & 
   Pba2(d1,d0) o Pba1(d1 o r,d0) o tuple = t2 & 
   Pba2(d1 o r,d0) o tuple = t3’ >-- (strip_tac >>
 qexists_tac ‘tuple’ >>
 strip_tac (* 2 *)
 >-- (qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule isio_unique1 >>
     first_x_assum  
     (qsspecl_then [‘r’,‘t3’,‘t21’,‘t321l’,‘r o cr1 o tuple’] assume_tac) >> rfs[] >>
     first_x_assum irule >>
     drule isio_o_r1 >>
     first_x_assum (qsspecl_then [‘r’] assume_tac) >>
     rfs[] >>
     first_x_assum irule >> 
     arw[GSYM o_assoc] >>
     qby_tac ‘d1 o t2 = d1 o t21’ 
     >-- (flip_tac >> drule isio_cod >> 
         first_x_assum irule >> 
         qexistsl_tac [‘t1’,‘r’] >> arw[]) >> arw[] >>
     rw[o_assoc] >> 
     drule isio_unique1 >>
     first_x_assum (qsspecl_then [‘r’,‘t2’,‘t1’,‘r o Pba1((d1 o r), d0) o tuple’,‘t21’] assume_tac) >> rfs[] >>
     first_x_assum irule >> 
     drule isio_o_r1 >>
     first_x_assum (qsspecl_then [‘r’] assume_tac) >> rfs[]>>
     first_x_assum irule >> arw[]) >>
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule isio_unique1 >> 
 first_x_assum  
     (qsspecl_then [‘r’,‘t32’,‘t1’,‘t321r’,‘r o c1r o aiso o tuple’] assume_tac) >> rfs[] >> 
 first_x_assum irule >>
 drule isio_o_r1 >>
 first_x_assum (qsspecl_then [‘r’] assume_tac) >> rfs[] >>
 first_x_assum irule >> arw[GSYM o_assoc] >>
 arw[o_assoc] >>
 qby_tac ‘d0 o t32 = d1 o t1’ 
 >-- (qpick_x_assum ‘d0 o t2 = d1 o t1’ 
      (assume_tac o GSYM) >>
     arw[] >> drule isio_dom >>
     first_x_assum irule >> 
     qexistsl_tac [‘t3’,‘r’] >> arw[]) >> 
 arw[] >>
 drule isio_unique1 >>
 first_x_assum (qsspecl_then [‘r’,‘t3’,‘t2’,‘r o Pba2(d1, (d0 o r)) o aiso o tuple’,‘t32’] assume_tac) >>
 rfs[] >> first_x_assum irule >>
 drule isio_o_r1 >>
 first_x_assum (qsspecl_then [‘r’] assume_tac) >> rfs[] >>
 first_x_assum irule >> arw[] >>
 qsuff_tac
 ‘(Pba1(d1, d0) o Pba2(d1, (d0 o r)) o aiso) o tuple = t2 &
  (Pba2(d1, d0) o Pba2(d1, (d0 o r)) o aiso) o tuple = t3’
 >-- rw[o_assoc] >>
 arw[] >> arw[o_assoc]) >>
 qsspecl_then [‘d0’,‘d1’,‘i’,‘r’] assume_tac tuple_ex >>
 first_x_assum irule >>
 arw[]) >>
 rw[Iassoc_def] >> 
 rpt strip_tac >>
 irule $ iffLR fun_ext >> strip_tac >>
 rw[o_assoc] >> 
 qabbrev_tac ‘Pba2(d1 o r,d0) o a = t3’ >>
 qabbrev_tac ‘Pba2(d1,d0) o Pba1(d1 o r,d0) o a = t2’ >>
 qabbrev_tac ‘Pba1(d1,d0) o Pba1(d1 o r,d0) o a = t1’ >> 
 qby_tac ‘d0 o t2 = d1 o t1’ 
 >-- (qpick_x_assum ‘Pba1(d1, d0) o Pba1((d1 o r), d0) o a = t1’ (assume_tac o GSYM) >> arw[] >>
     qpick_x_assum ‘Pba2(d1, d0) o Pba1((d1 o r), d0) o a = t2’ (assume_tac o GSYM) >>
     arw[] >> rw[Pb_eqn,GSYM o_assoc]) >>
 qby_tac ‘d0 o t3 = d1 o t2’ 
 >-- (qpick_x_assum ‘Pba2((d1 o r), d0) o a = t3’
     (assume_tac o GSYM) >> arw[] >>
     qpick_x_assum ‘Pba2(d1, d0) o Pba1((d1 o r), d0) o a = t2’ (assume_tac o GSYM) >> arw[] >>
     rw[GSYM o_assoc,GSYM Pb_eqn] >> rw[o_assoc] >>
     arw[GSYM o_assoc]) >>
 first_x_assum
 (qsspecl_then [‘t3’,‘t2’,‘t1’] assume_tac) >>
 rfs[] >>
 qsuff_tac ‘r o cr1 o a = t321 & r o c1r o aiso o a = t321’ 
 >-- (strip_tac >> arw[]) >> strip_tac (* 2 *)
 >-- (irule isio_unique1 >>
     qexistsl_tac 
     [‘C0’,‘d0’,‘d1’,‘Pbo(d1,d0)’,
      ‘Pba1(d1,d0)’,‘Pba2(d1,d0)’,‘r’,‘t21’,‘t3’] >>
     arw[] >> 
     qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >> 
     arw[] >> drule isio_o_r1 >>
     first_x_assum (qsspecl_then [‘r’] assume_tac) >>
     rfs[] >>
     first_x_assum irule >> strip_tac (* 2 *)
     >-- (arw[GSYM o_assoc] >> 
         rw[o_assoc] >>
         drule isio_unique1 >>
         first_x_assum (qsspecl_then [‘r’,‘t2’,‘t1’,‘r o Pba1((d1 o r), d0) o a’,‘t21’] assume_tac) >> rfs[] >> 
         first_x_assum irule >>
         drule isio_o_r1 >> 
         first_x_assum (qsspecl_then [‘r’] assume_tac) >>
         rfs[] >> first_x_assum irule >> arw[]) >>
     arw[GSYM o_assoc] >>
     drule isio_dom_cod >> flip_tac >>
     qsuff_tac
     ‘d0 o t21 = d0 o t1 & d1 o t21 = d1 o t2’ 
     >-- (strip_tac >> arw[]) >>
     first_x_assum irule >> qexists_tac ‘r’ >> arw[]) >>
(*second subgoal,.  r o c1r o aiso o a = t321*)
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule isio_unique1 >>
 first_x_assum 
(qsspecl_then [‘r’,‘t32’,‘t1’,‘r o c1r o aiso o a’,‘t321’] assume_tac)>>
first_x_assum irule>> arw[] >> 
drule isio_o_r1 >>
first_x_assum (qsspecl_then [‘r’] assume_tac) >>
rfs[] >>
qby_tac ‘d0 o t32 = d1 o t1’
>-- (drule isio_cpsb >> first_x_assum irule >>
    qexistsl_tac [‘t321’,‘r’] >> arw[]) >>
first_x_assum (qsspecl_then [‘t32’,‘t1’,‘c1r o aiso o a’] assume_tac) >>
rfs[] >>
first_x_assum irule >> arw[GSYM o_assoc] >>
arw[o_assoc] >>
drule isio_unique1 >>
first_x_assum (qsspecl_then [‘r’,‘t3’,‘t2’,‘r o Pba2(d1, (d0 o r)) o aiso o a’,‘t32’] assume_tac) >> rfs[] >>
first_x_assum irule >> 
drule isio_o_r1 >>
first_x_assum (qsspecl_then [‘r’] assume_tac) >>
rfs[] >>
first_x_assum irule >> arw[] >> 
qsuff_tac
 ‘Pba1(d1, d0) o (Pba2(d1, (d0 o r)) o aiso) o a = t2 &
  Pba2(d1, d0) o (Pba2(d1, (d0 o r)) o aiso) o a = t3’ 
 >-- rw[o_assoc] >>
 arw[] >> arw[GSYM o_assoc] >> arw[o_assoc])
(form_goal 
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1 r.
  d0 o r = d0 o Pba1(d1, d0) & 
  d1 o r = d1 o Pba2(d1, d0) ==>
  (Iassoc(d0,d1,i,r) <=> 
  !t3 t2 t1:2->C1. 
   d0 o t2 = d1 o t1 & 
   d0 o t3 = d1 o t2 ==>
   ?t321:2->C1 t32 t21.
   isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,t2,t1,t21) & 
   isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,t3,t2,t32) &
   isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,t32,t1,t321) &
   isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,t3,t21,t321))
   ”));

