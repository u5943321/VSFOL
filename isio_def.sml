
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


val Iassoc_alt = prove_store("Iassoc_alt",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- cheat >>
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
 >-- cheat >>
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
