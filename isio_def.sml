
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
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[isio_def] >> arw[GSYM o_assoc] >>
     arw[o_assoc] >>
     rev_drule through_Pb >>
     first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
     rfs[] >> 
     qexists_tac ‘a0’>> arw[] >> 
     qpick_x_assum ‘r o fg0 = gf’ (assume_tac o GSYM) >>
     arw[] >>
     qsuff_tac ‘i o a0 = fg0’ >-- (strip_tac >> arw[]) >>
     drule Pb12_eq_eq >> first_x_assum irule >>
     arw[GSYM o_assoc]) >>
 fs[isio_def] >> 
 qsspecl_then [‘d1’,‘d0’,‘p1’,‘p2’,‘p1'’,‘p2'’]
 assume_tac isPb_unique >>
 rfs[] >> 
 qby_tac ‘j = i’ 
 >-- (rev_drule Pb12_eq_eq >> first_x_assum irule >> arw[])>>
 fs[] >>
 qby_tac
 ‘d0 o r = d0 o p1’ 
 >-- (qby_tac ‘d0 o r o i o i' = d0 o p1' o i'’ 
     >-- fs[GSYM o_assoc] >>
     rfs[IdR]) >> arw[] >>
 qby_tac ‘d1 o r = d1 o p2’ 
 >-- (qby_tac ‘d1 o r o i o i' = d1 o p2' o i'’ 
     >-- fs[GSYM o_assoc] >>
     rfs[IdR]) >> arw[] >>
 rev_drule through_Pb >>
 first_x_assum (qsspecl_then [‘f’,‘g’] assume_tac) >>
 rfs[] >>
 qexists_tac ‘a0’ >> arw[] >>
 qpick_x_assum ‘(r o i) o fg0 = gf’ (assume_tac o GSYM) >>
 arw[] >>
 rw[o_assoc] >>
 qsuff_tac ‘a0 = i o fg0’ 
 >-- (strip_tac >> arw[]) >>
 rev_drule Pb12_eq_eq >>
 first_x_assum irule >> arw[GSYM o_assoc])
(form_goal
 “!C0 C1 d0:C1->C0 d1:C1->C0 
   C1C1 p1:C1C1->C1 p2:C1C1->C1. 
   isPb(d1,d0,p1,p2) ==>
   !Pb p1':Pb->C1 p2':Pb->C1.
   isPb(d1,d0,p1',p2') ==>
   !i:Pb->C1C1.
   p1 o i = p1' & p2 o i = p2' ==>
   !r A g f:A->C1 gf.
    isio(d0,d1,p1,p2,r,g,f,gf) <=> 
    isio(d0,d1,p1',p2',r o i,g,f,gf)
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

val Pbfac_def = 
qdefine_psym("Pbfac",
[‘f:X->Z’,‘g:Y->Z’,‘p:P->X’,‘q:P->Y’,
 ‘t1:T->X’,‘t2:T->Y’,‘tb:T->P’])
‘isPb(f,g,p,q) & 
 f o t1 = g o t2 & 
 p o tb = t1 & q o tb = t2’


(*
val Icat_dom_alt = prove_store("Icat_dom_alt",
e0
()
(form_goal
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1 r.
  d0 o r = d0 o Pba1(d1, d0) <=> 
  !f:T->C1 g:T->C1.
  d0 o g = d1 o f ==>
  !fg:T->Pbo(d1,d0).
   Pba1(d1,d0) o fg = f &
   Pba2(d1,d0) o fg = g ==>
   
  !”));
*)


val C2ICat_dom = prove_store("C2ICat_dom",
e0
(rw[Id0_def,Ir_def] >>
 qsuff_tac
 ‘(Er1(A) o Ed(0f, A)) o Ed(γ, A) =
  (Er1(A) o Ed(0f, A)) o Pba1(Id1(A), Id0(A)) o tri2pb(A)’ 
 >-- (strip_tac >>
     qby_tac
     ‘((Er1(A) o Ed(0f, A)) o Ed(γ, A)) o pb2tri(A) = 
      ((Er1(A) o Ed(0f, A)) o
      Pba1(Id1(A), Id0(A)) o tri2pb(A)) o pb2tri(A)’ 
     >-- (arw[] >>  fs[o_assoc,tri2pb_eqns]) >>
     fs[o_assoc,tri2pb_eqns,IdR]) >>
 rw[tri2pb_eqns] >> rw[o_assoc] >>
 rw[GSYM Ed_o] >> rw[Er1_eq_eq] >>
 irule Ed_eq >> rw[CC4_1])
(form_goal 
 “Id0(A) o Ir(A) = Id0(A) o Pba1(Id1(A), Id0(A))”));



val C2ICat_cod = prove_store("C2ICat_cod",
e0
(rw[Id1_def,Ir_def] >>
 qsuff_tac
 ‘(Er1(A) o Ed(1f, A)) o Ed(γ, A) =
  (Er1(A) o Ed(1f, A)) o Pba2(Id1(A), Id0(A)) o tri2pb(A)’ 
 >-- (strip_tac >>
     qby_tac
     ‘((Er1(A) o Ed(1f, A)) o Ed(γ, A)) o pb2tri(A) = 
      ((Er1(A) o Ed(1f, A)) o
      Pba2(Id1(A), Id0(A)) o tri2pb(A)) o pb2tri(A)’ 
     >-- (arw[] >>  fs[o_assoc,tri2pb_eqns]) >>
     fs[o_assoc,tri2pb_eqns,IdR]) >>
 rw[tri2pb_eqns] >> rw[o_assoc] >>
 rw[GSYM Ed_o] >> rw[Er1_eq_eq] >>
 irule Ed_eq >> rw[CC4_1])
(form_goal 
 “Id1(A) o Ir(A) = Id1(A) o Pba2(Id1(A), Id0(A))”));

val Nt_ext_Dom_Cod = prove_store("Nt_ext_Dom_Cod",
e0
(rpt strip_tac >> irule Nt_ext_cpnt >> arw[] >>
 qexistsl_tac [‘Dom(η2)’,‘Cod(η2)’] >>
 arw[Nt_Dom_Cod] >>
 qpick_x_assum ‘Dom(η1) = Dom(η2)’ (assume_tac o GSYM) >>
 arw[] >>
 qpick_x_assum ‘Cod(η1) = Cod(η2)’ (assume_tac o GSYM) >>
 arw[Nt_Dom_Cod])
(form_goal 
 “∀A B η1:A -> Exp(2,B) η2. 
  (Dom(η1) = Dom(η2) & Cod(η1) = Cod(η2) & 
 ∀a:1->A.cpnt(η1,a) = cpnt(η2,a)) ⇒
 η1 = η2”));



val Nt_iff_Dom_Cod = prove_store("Nt_iff_Dom_Cod",
e0
(rpt strip_tac >> 
 rw[Nt_def,csL_Pt,csR_Pt,Dom_def,Cod_def] >> 
 dimp_tac >> rpt strip_tac >> fs[GSYM o_assoc] >>
 irule $ iffLR fun_ext >> fs[o_assoc])
(form_goal “∀A B η:A->Exp(2,B) F1 F2.Nt(η,F1,F2) ⇔ 
 F1 = Dom(η) & F2 = Cod(η)”));



val vo_Dom_Cod = prove_store("vo_Dom_Cod",
e0
(rpt gen_tac >> strip_tac >> flip_tac >>
 rw[GSYM Nt_iff_Dom_Cod] >>
 irule vo_Nt_Nt >> qexists_tac ‘Dom(η2)’ >>
 rw[Nt_Dom_Cod] >> arw[Nt_Dom_Cod])
(form_goal 
 “∀A B η1:A->Exp(2,B) η2. Dom(η2) = Cod(η1) ⇒
 Dom(vo(η2,η1)) = Dom(η1) &
 Cod(vo(η2,η1)) = Cod(η2)”));


val vo_Dom = prove_store("vo_Dom",
e0
(rpt strip_tac>> drule vo_Dom_Cod >> arw[])
(form_goal 
 “∀A B η1:A->Exp(2,B) η2. Dom(η2) = Cod(η1) ⇒
 Dom(vo(η2,η1)) = Dom(η1)”));


val vo_Cod = prove_store("vo_Cod",
e0
(rpt strip_tac>> drule vo_Dom_Cod >> arw[])
(form_goal 
 “∀A B η1:A->Exp(2,B) η2. Dom(η2) = Cod(η1) ⇒
 Cod(vo(η2,η1)) = Cod(η2)”));



val Dom_Cod_vo_cpnt = prove_store("Dom_Cod_vo_cpnt",
e0
(rpt strip_tac >> irule Nt_vo_cpnt >>
 qexistsl_tac[‘Dom(η1)’,‘Dom(η2)’,‘Cod(η2)’] >>
 rw[Nt_Dom_Cod] >> arw[Nt_Dom_Cod])
(form_goal
 “∀A B η1 η2:A->Exp(2,B).
 Dom(η2) = Cod(η1) ⇒ 
 ∀a:1->A.
 cpnt(vo(η2, η1), a) = cpnt(η2, a) @ cpnt(η1, a)”));




val Dom_Cod_vo_cpsb = prove_store("Dom_Cod_vo_cpsb",
e0
(rpt strip_tac >> irule vo_cpsb >>
 fs[Dom_def,Cod_def] >> fs[Er1_eq_eq])
(form_goal
 “∀A B η1 η2:A->Exp(2,B).
 Dom(η2) = Cod(η1) ⇒ 
 ∀a:1->A.
  cpsb(cpnt(η2, a),cpnt(η1, a))”));

val vo_assoc = prove_store("vo_assoc",
e0
(rpt strip_tac >> irule Nt_ext_Dom_Cod >>
 drule vo_Dom_Cod >>
 rfs[] >>
 drule vo_Dom_Cod >> arw[] >>
 rev_drule vo_Dom_Cod >>
 qby_tac
 ‘Dom(η3) = Cod(vo(η2, η1))’ >-- arw[] >>
 drule vo_Dom_Cod >> arw[] >>
 strip_tac >> 
 qby_tac
 ‘cpnt(vo(vo(η3, η2), η1), a) = 
  cpnt(vo(η3,η2), a) @ cpnt(η1,a)’ 
 >-- (irule Dom_Cod_vo_cpnt >> arw[]) >> arw[] >>
 qby_tac
 ‘cpnt(vo(η3, vo(η2, η1)), a) = 
  cpnt(η3, a) @ cpnt(vo(η2,η1),a)’
 >-- (irule Dom_Cod_vo_cpnt >> arw[]) >> arw[] >>
 qby_tac 
 ‘cpnt(vo(η3, η2), a) = cpnt(η3, a) @ cpnt(η2,a)’
 >-- (irule Dom_Cod_vo_cpnt >> arw[]) >> arw[] >>
 qby_tac 
 ‘cpnt(vo(η2, η1), a) = cpnt(η2, a) @ cpnt(η1,a)’
 >-- (irule Dom_Cod_vo_cpnt >> arw[]) >> arw[] >>
 irule Thm8 >>
 strip_tac (* 2 *)
 >-- (irule Dom_Cod_vo_cpsb>> arw[]) >>
(irule Dom_Cod_vo_cpsb>> arw[]))
(form_goal 
 “!A B η1 η2 η3:A->Exp(2,B).
 Dom(η2) = Cod(η1) & 
 Dom(η3) = Cod(η2) ⇒
 vo(vo(η3,η2),η1) = vo(η3,vo(η2,η1))”));

val Id0_Ed_ra = prove_store("Id0_Ed_ra",
e0
(strip_tac >> rw[Id0_def,GSYM Ed_o,o_assoc,Er1_eq_eq] >>
 irule Ed_eq >> rw[CC4_1])
(form_goal “∀A. Id0(A) o Ed(γ, A) = Id0(A) o Ed(α, A)”));


val Id1_Ed_rb = prove_store("Id0_Ed_rb",
e0
(strip_tac >> rw[Id1_def,GSYM Ed_o,o_assoc,Er1_eq_eq] >>
 irule Ed_eq >> rw[CC4_1])
(form_goal “∀A.Id1(A) o Ed(γ, A) = Id1(A) o Ed(β, A)”));

val isio_vo = prove_store("isio_vo",
e0
(rpt strip_tac >> rw[isio_def] >>
 rw[icat_Pb] >> fs[GSYM Id0_Dom,GSYM Id1_Cod] >>
 rw[Id0_Ed_ra,Id1_Ed_rb] >>
 assume_tac icat_Pb >>
 drule through_Pb >>
 last_x_assum (assume_tac o GSYM) >>
 first_x_assum (drule o iffLR) >>
 pop_assum strip_assume_tac >> qexists_tac ‘a0’ >>
 arw[vo_def] >>
 qsuff_tac ‘a0 = irt(t1,t2)’ 
 >-- (strip_tac >> arw[]) >>
 irule is_irt >> arw[] >> 
 fs[Id1_def,Id0_def,o_assoc,Er1_eq_eq])
(form_goal 
 “!A X t1:X->Exp(2,A) t2.
  Dom(t2) = Cod(t1) ⇒
  isio(Id0(A),Id1(A),Ed(α,A),Ed(β,A),Ed(γ,A),t2,t1,vo(t2,t1))”));

val isio_iff_vo = prove_store("isio_vo",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) 
 >-- (assume_tac icat_Pb >> drule isio_unique1 >>
     first_x_assum (qsspecl_then [‘Ed(γ,A)’,‘t2’,‘t1’,‘t21’,‘vo(t2,t1)’] assume_tac) >>
     first_x_assum irule >>
     drule isio_vo >> arw[]) >>
 drule isio_vo >> arw[])
(form_goal 
 “!A X t1:X->Exp(2,A) t2 t21.
  Dom(t2) = Cod(t1) ⇒
  (isio(Id0(A),Id1(A),Ed(α,A),Ed(β,A),Ed(γ,A),t2,t1,t21) <=> 
  t21 = vo(t2,t1))”));


val isio_iff_vo' = prove_store("isio_vo",
e0
(rpt strip_tac >>
 qsspecl_then [‘Id0(A)’,‘Id1(A)’,‘Ed(α,A)’,‘Ed(β,A)’]
 assume_tac isio_compatible >>
 fs[icat_Pb] >>
 first_x_assum (qsspecl_then [‘Pba1(Id1(A), Id0(A))’,‘Pba2(Id1(A), Id0(A))’] assume_tac) >> fs[Pb_def] >>
 rw[Ir_def] >> 
 first_x_assum (qsspecl_then [‘pb2tri(A)’] assume_tac) >>
 fs[tri2pb_eqns] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 drule isio_iff_vo >> arw[])
(form_goal 
 “!A X t1:X->Exp(2,A) t2 t21.
  Dom(t2) = Cod(t1) ⇒
  (isio(Id0(A),Id1(A),Pba1(Id1(A), Id0(A)),Pba2(Id1(A), Id0(A)),Ir(A),t2,t1,t21) <=> 
  t21 = vo(t2,t1))”));

val C2Icat_Iassoc = prove_store("Icat_Iassoc",
e0
(rpt strip_tac >>
 qsspecl_then [‘Id0(A)’,‘Id1(A)’,‘Ii(A)’,‘Ir(A)’]
 assume_tac Iassoc_alt_2 >>
 fs[C2ICat_cod,C2ICat_dom] >>
 rpt strip_tac >> 
 last_x_assum (K all_tac) >> 
 fs[Id0_Dom,Id1_Cod] >>
 qexistsl_tac [‘vo(vo(t3,t2),t1)’,‘vo(t3,t2)’,‘vo(t2,t1)’] >>
 rpt strip_tac (*4 *)
 >-- (irule $ iffRL isio_iff_vo' >> arw[]) 
 >-- (irule $ iffRL isio_iff_vo' >> arw[]) 
 >-- (irule $ iffRL isio_iff_vo' >> rw[] >>
     last_x_assum (assume_tac o GSYM) >> arw[] >>
     irule vo_Dom >> arw[]) >>
 qby_tac ‘vo(vo(t3, t2), t1) = vo(t3, vo(t2, t1))’ 
 >-- (irule vo_assoc >> arw[]) >>
 arw[] >> 
 irule $ iffRL isio_iff_vo' >>  
 arw[] >> flip_tac >> irule vo_Cod >> arw[])
(form_goal
 “Iassoc(Id0(A),Id1(A),Ii(A),Ir(A))”));


val C2Icat_cl12 = prove_store("C2Icat_cl12",
e0
(rw[Ii_def,Id1_def,Id0_def,Er1_def,Ed_def,o_assoc,
    Pa_distr,p12_of_Pa,To1_def,IdL,Ev_of_Tp_el,Ev_of_Tp_el'])
(form_goal “Id0(A) o Ii(A) = Id(A) & 
           Id1(A) o Ii(A) = Id(A)”));

val ci1_ex = prove_store("ci1_ex",
e0
(rpt strip_tac >>
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule through_Pb >>
 first_x_assum
 (qsspecl_then [‘i o Pba1(Id(C0), d0)’,‘Pba2(Id(C0), d0)’]
  assume_tac) >> rfs[GSYM o_assoc,IdL] >> 
 fs[GSYM Pb_eqn,IdL] >>
 qexists_tac ‘a0’ >> arw[])
(form_goal
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1.
  d1 o i = Id(C0) ⇒
  ∃ci1.Pba1(d1, d0) o ci1 = i o Pba1(Id(C0), d0) &
       Pba2(d1, d0) o ci1 = Pba2(Id(C0), d0)”));

val IidL_alt = prove_store("IidL_alt",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[isio_def] >> arw[Pb_def] >>
     arw[GSYM o_assoc,IdL] >>
     drule $ iffLR IidL_def >>
     qby_tac
     ‘∃ci1.Pba1(d1, d0) o ci1 = i o Pba1(Id(C0), d0) &
               Pba2(d1, d0) o ci1 = Pba2(Id(C0), d0)’ 
     >-- (drule ci1_ex >> arw[]) >>
     pop_assum strip_assume_tac >> 
     qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘i o c’,‘a’] assume_tac)>>
     rfs[GSYM o_assoc,IdL] >>
     qexists_tac ‘a0’ >> arw[] >> 
     first_x_assum (qsspecl_then [‘ci1’] assume_tac) >> 
     rfs[] >> 
     qsspecl_then [‘Id(C0)’,‘d0’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘c’,‘a’] assume_tac) >>
     rfs[IdL] >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qpick_x_assum ‘r o ci1 = Pba2(Id(C0), d0)’
     (assume_tac o GSYM) >> arw[] >> rw[o_assoc] >>
     qsuff_tac ‘a0 = ci1 o a0'’ 
     >-- (strip_tac >> arw[]) >>
     irule Pba12_eq_eq >> arw[GSYM o_assoc] >>
     arw[o_assoc])>>
 rw[IidL_def] >> rpt strip_tac >> 
 irule $ iffLR fun_ext >> rw[o_assoc] >>
 strip_tac >> 
 qabbrev_tac ‘Pba1(Id(C0), d0) o a = c’ >>
 qabbrev_tac ‘Pba2(Id(C0), d0) o a = f’ >> arw[] >>
 qby_tac ‘d0 o f = c’ 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[GSYM Pb_eqn,GSYM o_assoc] >> arw[IdL]) >>
 first_x_assum drule >>
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule isio_unique1 >>
 first_x_assum (qspecl_then [‘r’] assume_tac) >>
 first_x_assum irule >>
 qexistsl_tac [‘i o c’,‘f’] >> arw[] >>
 drule isio_o_r1 >>
 first_x_assum (qsspecl_then [‘r’] assume_tac) >> rfs[] >>
 first_x_assum irule >> arw[GSYM o_assoc] >>
 arw[o_assoc] >> rw[IdL]
 )
(form_goal
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1 r.
  d1 o i = Id(C0) & 
  d0 o r = d0 o Pba1(d1, d0) & 
  d1 o r = d1 o Pba2(d1, d0) ⇒
  (IidL(d0,d1,i,r) ⇔ 
  ∀T c:T->C0 a:T->C1.
  d0 o a = c ⇒
  isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,a,i o c,a))
  ”));





val C2Icat_d0r = C2ICat_dom;
val C2Icat_d1r = C2ICat_cod;


val ID_alt = prove_store("ID_alt",
e0
(rw[ID_def] >> irule Ev_eq_eq >> rw[o_assoc,Ev_of_Tp_el] >>
rw[p12_of_Pa] >> rw[Swap_Pa] >> rw[Pt_def] >>
rw[id_def,GSYM Tp1_def,o_assoc] >>
rw[To1_def] >> rw[GSYM o_assoc,Ev_of_Tp_el] >>
rw[o_assoc,p12_of_Pa,Pa_distr])
(form_goal
“ID(F:A->B) = Tp(p2(2, B)) o F”));

val Ii_ID = prove_store("Ii_ID",
e0
(rw[Ii_def] >> rw[ID_alt])
(form_goal “∀T A c:T->A. Ii(A) o c = ID(c)”));

val Er1_Ed0_Tp_p2_Id = prove_store("Er1_Ed0_Tp_p2_Id",
e0
(rw[Er1_def,Ed_def] >> 
rw[o_assoc,Pa_distr,p12_of_Pa,IdL,To1_def] >>
rw[Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa,To1_def,Pa_distr] >>
rw[Ev_of_Tp_el'] >> rw[p12_of_Pa])
(form_goal
“ Er1(B) o Ed(0f, B) o Tp(p2(2, B)) = Id(B)”));


val Er1_Ed1_Tp_p2_Id = prove_store("Er1_Ed1_Tp_p2_Id",
e0
(rw[Er1_def,Ed_def] >> 
rw[o_assoc,Pa_distr,p12_of_Pa,IdL,To1_def] >>
rw[Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa,To1_def,Pa_distr] >>
rw[Ev_of_Tp_el'] >> rw[p12_of_Pa])
(form_goal
“ Er1(B) o Ed(1f, B) o Tp(p2(2, B)) = Id(B)”));

val ID_Dom = prove_store("ID_Dom",
e0
(rw[Dom_def,ID_alt] >> rpt strip_tac >>
 assume_tac Er1_Ed0_Tp_p2_Id >>  fs[GSYM o_assoc,IdL])
(form_goal “∀A B F:A->B. Dom(ID(F)) = F”));


val ID_Cod = prove_store("ID_Cod",
e0
(rw[Cod_def,ID_alt] >> rpt strip_tac >>
 assume_tac Er1_Ed1_Tp_p2_Id >>  fs[GSYM o_assoc,IdL])
(form_goal “∀A B F:A->B. Cod(ID(F)) = F”));

val ID_Dom_Cod = prove_store("ID_Dom_Cod",
e0
(rw[ID_Dom,ID_Cod])
(form_goal “∀A B F:A->B. Dom(ID(F)) = F & Cod(ID(F)) = F”));




val Cod_cod_cpnt = prove_store("Cod_cod_cpnt",
e0
(rpt strip_tac >> flip_tac >> 
qsspecl_then [‘η’] assume_tac Nt_Dom_Cod >>
drule Nt_dom_cod_cpnt >> arw[])
(form_goal
“∀A B η:A->Exp(2,B) a. Cod(η) o a = cod(cpnt(η, a))”));



val Dom_dom_cpnt = prove_store("Dom_dom_cpnt",
e0
(rpt strip_tac >> flip_tac >> 
qsspecl_then [‘η’] assume_tac Nt_Dom_Cod >>
drule Nt_dom_cod_cpnt >> arw[])
(form_goal
“∀A B η:A->Exp(2,B) a. Dom(η) o a = dom(cpnt(η, a))”));


val IDL = prove_store("IDL",
e0
(rpt strip_tac >> 
 irule Nt_ext_cpnt >>  strip_tac (* 2 *)
 >-- (qexistsl_tac [‘Dom(η)’,‘Cod(η)’] >>
     rw[Nt_iff_Dom_Cod] >> flip_tac >>
     qby_tac ‘Dom(ID(Cod(η))) = Cod(η)’ 
     >-- rw[ID_Dom_Cod] >>
     drule vo_Dom_Cod >> arw[] >> rw[ID_Dom_Cod]) >>
 qby_tac ‘Dom(ID(Cod(η))) = Cod(η)’ 
 >-- rw[ID_Dom_Cod] >>
 drule Dom_Cod_vo_cpnt >> arw[] >> 
 rw[cpnt_ID] >> strip_tac >> 
 irule cpsb_idL >> rw[cpsb_def,id_dom] >> 
 rw[Cod_cod_cpnt])
(form_goal “∀A B η:A->Exp(2,B).vo(ID(Cod(η)),η) = η”));



val IDR = prove_store("IDR",
e0
(rpt strip_tac >> 
 irule Nt_ext_cpnt >>  strip_tac (* 2 *)
 >-- (qexistsl_tac [‘Dom(η)’,‘Cod(η)’] >>
     rw[Nt_iff_Dom_Cod] >> flip_tac >>
     qby_tac ‘Dom(η) = Cod(ID(Dom(η)))’ 
     >-- rw[ID_Dom_Cod] >>
     drule vo_Dom_Cod >> last_x_assum (K all_tac) >> 
     arw[] >> rw[ID_Dom_Cod]) >>
 qby_tac ‘Dom(η) = Cod(ID(Dom(η)))’ 
 >-- rw[ID_Dom_Cod] >>
 drule Dom_Cod_vo_cpnt >> last_x_assum (K all_tac) >>
 arw[] >> rw[cpnt_ID] >> strip_tac >> 
 irule cpsb_idR >> rw[cpsb_def,id_cod] >> 
 rw[Dom_dom_cpnt])
(form_goal “∀A B η:A->Exp(2,B).vo(η,ID(Dom(η))) = η”));


val C2Icat_IidL = prove_store("C2Icat_IidL",
e0
(irule $ iffRL IidL_alt >>
 rw[C2ICat_cod,C2ICat_dom,C2Icat_cl12] >> rw[Ii_ID] >>
 rpt strip_tac >>
 irule $ iffRL isio_iff_vo' >> fs[Id0_Dom] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[ID_Dom_Cod] >>
 rw[IDR])
(form_goal
 “IidL(Id0(A),Id1(A),Ii(A),Ir(A))”));



val c1i_ex = prove_store("c1i_ex",
e0
(rpt strip_tac >>
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule through_Pb >>
 first_x_assum
 (qsspecl_then [‘Pba1(d1, Id(C0))’,‘i o Pba2(d1, Id(C0))’]
  assume_tac) >> rfs[GSYM o_assoc,IdL] >>  
 fs[Pb_eqn,IdL] >>
 qexists_tac ‘a0’ >> arw[])
(form_goal
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1.
  d0 o i = Id(C0) ⇒
  ∃c1i.Pba1(d1, d0) o c1i = Pba1(d1, Id(C0)) &
       Pba2(d1, d0) o c1i = i o Pba2(d1, Id(C0))”));



val IidR_alt = prove_store("IidR_alt",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[isio_def] >> arw[Pb_def] >>
     arw[GSYM o_assoc,IdL] >>
     drule $ iffLR IidR_def >>
     qby_tac
     ‘∃c1i.Pba1(d1, d0) o c1i = Pba1(d1, Id(C0)) &
           Pba2(d1, d0) o c1i = i o Pba2(d1, Id(C0))’ 
     >-- (drule c1i_ex >> arw[]) >>
     pop_assum strip_assume_tac >> 
     qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘a’,‘i o c’] assume_tac)>>
     rfs[GSYM o_assoc,IdL] >>
     qexists_tac ‘a0’ >> arw[] >> 
     first_x_assum (qsspecl_then [‘c1i’] assume_tac) >> 
     rfs[] >> 
     qsspecl_then [‘d1’,‘Id(C0)’] assume_tac Pb_def >>
     drule through_Pb >>
     first_x_assum (qsspecl_then [‘a’,‘c’] assume_tac) >>
     rfs[IdL] >>
     qpick_x_assum ‘Pba1(d1, Id(C0)) o a0' = a’
     (assume_tac o GSYM) >> arw[] >>
     qpick_x_assum ‘r o c1i = Pba1(d1, Id(C0))’
     (assume_tac o GSYM) >> arw[] >>
     rw[o_assoc] >>
     qsuff_tac ‘a0 = c1i o a0'’ 
     >-- (strip_tac >> arw[]) >>
     irule Pba12_eq_eq >> arw[GSYM o_assoc] >>
     arw[o_assoc])>>
 rw[IidR_def] >> rpt strip_tac >> 
 irule $ iffLR fun_ext >> rw[o_assoc] >>
 strip_tac >> 
 qabbrev_tac ‘Pba1(d1,Id(C0)) o a = f’ >>
 qabbrev_tac ‘Pba2(d1,Id(C0)) o a = c’ >> arw[] >>
 qby_tac ‘d1 o f = c’ 
 >-- (qpick_x_assum ‘Pba1(d1, Id(C0)) o a = f’
      (assume_tac o GSYM) >> arw[] >>
      rw[Pb_eqn,GSYM o_assoc]  >> arw[IdL]) >>
 first_x_assum drule >>
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule isio_unique1 >>
 first_x_assum (qspecl_then [‘r’] assume_tac) >>
 first_x_assum irule >>
 qexistsl_tac [‘f’,‘i o c’] >> arw[] >>
 drule isio_o_r1 >>
 first_x_assum (qsspecl_then [‘r’] assume_tac) >> rfs[] >>
 first_x_assum irule >> arw[GSYM o_assoc] >>
 arw[o_assoc] >> rw[IdL])
(form_goal
 “!C1 C0 d0:C1->C0 d1:C1->C0 i:C0->C1 r.
  d0 o i = Id(C0) & 
  d0 o r = d0 o Pba1(d1, d0) & 
  d1 o r = d1 o Pba2(d1, d0) ⇒
  (IidR(d0,d1,i,r) ⇔ 
  ∀T a:T->C1 c:T->C0 .
  d1 o a = c ⇒
  isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,i o c,a,a))
  ”));
