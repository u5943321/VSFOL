val E0_def = qdefine_fsym("E0",[]) ‘dom(ε2)’

val E1_def = qdefine_fsym("E1",[]) ‘cod(ε2)’

val ar_of_E = 
store_ax("ar_of_E",“!f:2->E.f = id(E0) | f = id(E1) | f = ε1 | f = ε2 ”)


val isid_Po = prove_store("isid_Po",
e0
(rpt strip_tac >> rw[isid_alt] >> 
 qsspecl_then [‘f’] strip_assume_tac Pa_has_components >>
 rw[p12_of_Pa] >> arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- fs[id_def,dom_def,Pa_distr,o_assoc] >>
  fs[id_def,dom_def,Pa_distr,o_assoc,p12_of_Pa])
(form_goal “!A B f:2->A* B. isid(f) <=> isid(p1(A,B) o f) & isid(p2(A,B) o f)”));

val Po_Disc_Disc = prove_store("Po_Disc_Disc",
e0
(rpt strip_tac >> rw[Disc_def] >>
 rw[isid_Po] >> fs[Disc_def])
(form_goal “!D1 D2.Disc(D1) & Disc(D2) ==> Disc(D1 * D2)”));

val Fcond0_def = 
qdefine_psym
("Fcond0",
 [‘d0:Ar->Ob’,‘d1:Ar->Ob’,‘i:Ob->Ar’,‘r:Pbo(d1:Ar->Ob,d0:Ar->Ob) -> Ar’,‘f:1->Ar’,‘g:1->Ar’])
‘ISC(d0,d1,i,r) & 
 (!a:1->Ar.~(d0 o a = d1 o g & d1 o a = d1 o f))’


val Fcond1_def = 
qdefine_psym
("Fcond1",
 [‘d0:Ar->Ob’,‘d1:Ar->Ob’,‘i:Ob->Ar’,‘r:Pbo(d1:Ar->Ob,d0:Ar->Ob) -> Ar’,‘f:1->Ar’,‘g:1->Ar’])
‘ISC(d0,d1,i,r) &
 (?a:1->Ar. d0 o a = d1 o g & d1 o a = d0 o f)’


val Fconde1_def = 
qdefine_psym
("Fconde1",
 [‘d0:Ar->Ob’,‘d1:Ar->Ob’,‘i:Ob->Ar’,‘r:Pbo(d1:Ar->Ob,d0:Ar->Ob) -> Ar’,‘f:1->Ar’,‘g:1->Ar’])
‘ISC(d0,d1,i,r) & 
 ~Fcond0(d0, d1, i, r, f, g) &
 ~Fcond1(d0, d1, i, r, f, g) & 
 ((?a:1->Ar. isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,g,a,f)) |
 (?a:1->Ar. isio(d0,d1,Pba1(d1,d0),Pba2(d1,d0),r,a,g,f)))’


val Fconde2_def = 
qdefine_psym
("Fconde2",
 [‘d0:Ar->Ob’,‘d1:Ar->Ob’,‘i:Ob->Ar’,‘r:Pbo(d1:Ar->Ob,d0:Ar->Ob) -> Ar’,‘f:1->Ar’,‘g:1->Ar’])
‘ISC(d0,d1,i,r) & 
 ~Fcond0(d0, d1, i, r, f, g) & 
 ~Fcond1(d0, d1, i, r, f, g) &
 ~Fconde1(d0, d1, i, r, f, g)’


val Fcond1_not_Fcond0 = prove_store("Fcond1_not_Fcond0",
e0
(rpt strip_tac >>
 fs[Fcond1_def,Fcond0_def] >>
 ccontra_tac >>
 qsspecl_then [‘d1’,‘d0’] assume_tac Pb_def >>
 drule isio_ex >>
 first_x_assum (qsspecl_then [‘r’] assume_tac) >>
 qby_tac ‘d0 o r = d0 o Pba1(d1, d0) & d1 o r = d1 o Pba2(d1, d0)’ 
 >-- (drule $ iffLR ISC_def >> fs[Icat_def]) >>
 first_x_assum drule >>
 first_x_assum (qsspecl_then [‘f’,‘a’] assume_tac) >>
 rfs[] >>
 drule isio_dom_cod1 >>
 rfs[])
(form_goal 
 “!Ar Ob d0:Ar->Ob d1 i r f g.
 Fcond1(d0,d1,i,r,f,g) ==> ~Fcond0(d0,d1,i,r,f,g)”));



val Fcond0_not_Fcond1 = prove_store("Fcond0_not_Fcond1",
e0
(rpt strip_tac >>
 ccontra_tac >> drule Fcond1_not_Fcond0 >> rfs[])
(form_goal 
 “!Ar Ob d0:Ar->Ob d1 i r f g.
 Fcond0(d0,d1,i,r,f,g) ==> ~Fcond1(d0,d1,i,r,f,g)”));



val Fcond0_not_others = prove_store("Fcond0_not_others",
e0
(rpt strip_tac (* 3 *)
 >-- (drule Fcond0_not_Fcond1 >> arw[]) 
 >-- (rw[Fconde1_def] >> arw[]) >>
 rw[Fconde2_def] >> arw[])
(form_goal 
 “!Ar Ob d0:Ar->Ob d1 i r f g.
 Fcond0(d0,d1,i,r,f,g) ==> 
 ~Fcond1(d0,d1,i,r,f,g) & ~Fconde1(d0,d1,i,r,f,g) & ~Fconde2(d0,d1,i,r,f,g)”));

val Fcond1_not_others = prove_store("Fcond1_not_others",
e0
(rpt strip_tac (* 3 *)
 >-- (drule Fcond1_not_Fcond0 >> arw[]) 
 >-- (rw[Fconde1_def] >> arw[]) >>
 rw[Fconde2_def] >> arw[])
(form_goal 
 “!Ar Ob d0:Ar->Ob d1 i r f g.
 Fcond1(d0,d1,i,r,f,g) ==> 
 ~Fcond0(d0,d1,i,r,f,g) & ~Fconde1(d0,d1,i,r,f,g) & ~Fconde2(d0,d1,i,r,f,g)”));



val Fconde1_not_others = prove_store("Fconde1_not_others",
e0
(rpt strip_tac (* 3 *)
 >-- fs[Fconde1_def] 
 >-- fs[Fconde1_def] >>
 fs[Fconde2_def])
(form_goal 
 “!Ar Ob d0:Ar->Ob d1 i r f g.
 Fconde1(d0,d1,i,r,f,g) ==> 
 ~Fcond0(d0,d1,i,r,f,g) & ~Fcond1(d0,d1,i,r,f,g) & ~Fconde2(d0,d1,i,r,f,g)”));


val Fconde2_not_others = prove_store("Fconde2_not_others",
e0
(rpt strip_tac (* 3 *)
 >-- fs[Fconde2_def] 
 >-- fs[Fconde2_def] >>
 fs[Fconde2_def])
(form_goal 
 “!Ar Ob d0:Ar->Ob d1 i r f g.
 Fconde2(d0,d1,i,r,f,g) ==> 
 ~Fcond0(d0,d1,i,r,f,g) & ~Fcond1(d0,d1,i,r,f,g) & ~Fconde1(d0,d1,i,r,f,g)”));


val CC5_Disc = prove_store("CC5_Disc",
e0
(rpt strip_tac >>
 drule CC5_Disc_uex >>
 first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >> arw[])
(form_goal “∀A. Disc(A) ==> !B. 
 (∀a:1->A. ∃!b:1->B. R(a,b)) ⇒
 ?cf:A->B. ∀a:1->A b:1->B. R(a,b) ⇔ cf o a = b”));


 
val CC5_Disc' = prove_store("CC5_Disc'",
e0
(rpt strip_tac >>
 drule CC5_Disc >>
 first_x_assum drule >> arw[])
(form_goal “∀A B. (∀a:1->A. ∃!b:1->B. R(a,b)) ==>
 Disc(A) ==>
 ?cf:A->B. ∀a:1->A b:1->B. R(a,b) ⇔ cf o a = b”));

val Fst_def = qdefine_fsym("Fst",[‘f:X->A * B’])
‘p1(A,B) o f’


val Snd_def = qdefine_fsym("Snd",[‘f:X->A * B’])
‘p2(A,B) o f’

val Fst_Snd_Pa = prove_store("Fst_Snd_Pa",
e0
(rw[Fst_def,Snd_def,p12_of_Pa])
(form_goal “!X A B f:X->A g:X->B. Fst(Pa(f,g)) = f & Snd(Pa(f,g)) = g”));



val P1251_1252_functor_ex = prove_store("P1251_1252_functor_ex",
e0
(rpt strip_tac >> 
 qby_tac ‘Disc(Ar)’ >-- fs[ISC_def] >>
 qspecl_then [‘Ar’,‘Ar’] assume_tac Po_Disc_Disc >>
 rfs[] >> 
 qsuff_tac
 ‘?cf:Ar * Ar->Exp(2,E).
 !fg:1->Ar * Ar ae:1->Exp(2,E). 
  (Fcond0(d0,d1,i,r,Fst(fg),Snd(fg)) & ae = Tp1(id(E0))) |
  (Fcond1(d0,d1,i,r,Fst(fg),Snd(fg)) & ae = Tp1(id(E1))) |
  (Fconde1(d0,d1,i,r,Fst(fg),Snd(fg)) & ae = Tp1(ε1)) | 
  (Fconde2(d0,d1,i,r,Fst(fg),Snd(fg)) & ae = Tp1(ε2)) <=> cf o fg = ae’
 >-- (strip_tac >>
     qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> rpt gen_tac >> once_arw[] >>
     once_rw[Tp1_eq_eq] >> once_rw[Fst_Snd_Pa] >>
     rw[] >>
     rpt strip_tac >> arw[]) >>
 assume_tac
 (CC5_Disc' 
  |> qspecl [‘Ar * Ar’,‘Exp(2,E)’] 
  |> fVar_sInst_th “R(fg:1->Ar * Ar,ae:1->Exp(2,E))”
     “(Fcond0(d0,d1,i,r,Fst(fg),Snd(fg)) & ae = Tp1(id(E0))) |
  (Fcond1(d0,d1,i,r,Fst(fg),Snd(fg)) & ae = Tp1(id(E1))) |
  (Fconde1(d0,d1,i,r,Fst(fg),Snd(fg)) & ae = Tp1(ε1)) | 
  (Fconde2(d0:Ar->Ob,d1,i,r,Fst(fg:1->Ar * Ar),Snd(fg)) & ae:1->Exp(2,E) = Tp1(ε2))”) >>
 rfs[] >>
 first_x_assum irule >>
 strip_tac >>
 qcases ‘Fcond0(d0, d1, i, r, Fst(a), Snd(a))’
 >-- (drule Fcond0_not_others >> arw[] >>
     uex_tac >> qexists_tac ‘Tp1(id(E0))’ >> arw[]) >>
 qcases ‘Fcond1(d0, d1, i, r, Fst(a), Snd(a))’
 >-- (drule Fcond1_not_others >> arw[] >>
     uex_tac >> qexists_tac ‘Tp1(id(E1))’ >> arw[]) >>
 qcases ‘Fconde1(d0, d1, i, r, Fst(a), Snd(a))’ 
 >-- (drule Fconde1_not_others >> arw[] >>
     uex_tac >> qexists_tac ‘Tp1(ε1)’ >> rw[]) >>
 qby_tac ‘Fconde2(d0, d1, i, r, Fst(a), Snd(a))’ 
 >-- arw[Fconde2_def] >>
 drule Fconde2_not_others >> arw[] >>
 uex_tac >> qexists_tac ‘Tp1(ε2)’ >> rw[])
(form_goal
 “!Ar Ob d0:Ar->Ob d1 i r.
  ISC(d0,d1,i,r) ==>
  ?F:Ar * Ar -> Exp(2,E). 
  !f:1->Ar g:1->Ar. 
  (Fcond0(d0,d1,i,r,f,g) ==> 
   F o Pa(f,g) = Tp1(id(E0))) &
  (Fcond1(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(id(E1))) & 
  (Fconde1(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(ε1))  & 
  (Fconde2(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(ε2))
  ”));

(*antiparallel conndition*)
val iapcond_def = qdefine_psym("iapcond",[‘d0:Ar->Ob’,‘d1:Ar->Ob’,‘i:Ob->Ar’,‘r:Pbo(d1:Ar->Ob,d0:Ar->Ob) -> Ar’])
‘!f:1->Ar g:1->Ar.
 d0 o f = d1 o g & d0 o g = d1 o f ==> f = g’

val iapcond_endo_iid = prove_store("iapcond_endo_iid",
e0
(rpt strip_tac >>
 fs[iapcond_def] >> first_x_assum irule >> arw[] >>
 qby_tac ‘d0 o i = Id(Ob) & d1 o i = Id(Ob)’ 
 >-- fs[ISC_def,Icat_def] >>
 arw[GSYM o_assoc] >> rw[IdL])
(form_goal
 “!Ar Ob d0:Ar->Ob d1 i r.
  ISC(d0,d1,i,r) ==>
  iapcond(d0,d1,i,r) ==>
  !f:1->Ar. d0 o f = d1 o f ==> f = i o d1 o f”));

val Icat_i_Mono = prove_store("Icat_i_Mono",
e0
(rpt strip_tac >> fs[Icat_def] >>
 rw[Mono_def] >> rpt strip_tac >>
 qby_tac ‘d1 o i o g = d1 o i o h’ >-- arw[] >>
 rfs[GSYM o_assoc] >> fs[IdL])
(form_goal “!Ar Ob d0:Ar->Ob d1 i r.
  Icat(d0,d1,i,r) ==> Mono(i)”));


val iapcond_iob_eq = prove_store("iapcond_ex_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f1 = f2’ >-- (strip_tac >> fs[]) >>
 fs[iapcond_def] >> first_x_assum irule >> arw[])
(form_goal “!Ar Ob d0:Ar->Ob d1 i r.
  ISC(d0,d1,i,r) ==>
  iapcond(d0,d1,i,r) ==> 
  !iob1 iob2:1->Ob f1 f2:1->Ar. 
  d0 o f1 = iob1 & d1 o f1 = iob2 &
  d0 o f2 = iob2 & d1 o f2 = iob1 ==> iob1 = iob2”));

val iapcond_ex_eq = prove_store("iapcond_ex_eq",
e0
(rpt strip_tac >>
 drule $ iffLR iapcond_def >> 
 first_x_assum irule >> strip_tac (* 2 *)
 >-- (drule iapcond_iob_eq >> first_x_assum drule >>
     first_x_assum 
     (qsspecl_then [‘d0 o f’,‘d1 o f'’,‘a2b'’,‘b'2a’] assume_tac) >>
     first_x_assum irule >> arw[]) >>
 drule iapcond_iob_eq >> first_x_assum drule >>
 first_x_assum (qsspecl_then [‘d0 o f'’,‘d1 o f’,‘a'2b’,‘b2a'’] assume_tac) >>
 first_x_assum irule >> arw[])
(form_goal “!Ar Ob d0:Ar->Ob d1 i r.
  ISC(d0,d1,i,r) ==>
  iapcond(d0,d1,i,r) ==> 
  !f f':1->Ar a2b' b'2a b2a' a'2b:1->Ar. 
  d0 o a2b' = d0 o f & d1 o a2b' = d1 o f' & 
  d0 o b'2a = d1 o f' & d1 o b'2a = d0 o f & 
  d0 o b2a' = d1 o f & d1 o b2a' = d0 o f' & 
  d0 o a'2b = d0 o f' & d1 o a'2b = d1 o f ==>
  f = f'”));




val P1252_first_thm = prove_store("P1252_first_thm",
e0
(rpt strip_tac >>
 qsuff_tac ‘d0 o f = d1 o f'’)
(form_goal
 “!Ar Ob d0:Ar->Ob d1 i r.
  ISC(d0,d1,i,r) ==>
  iapcond(d0,d1,i,r) ==>
  !F:Ar * Ar -> Exp(2,E). 
  (!f:1->Ar g:1->Ar. 
  (Fcond0(d0,d1,i,r,f,g) ==> 
   F o Pa(f,g) = Tp1(id(E0))) &
  (Fcond1(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(id(E1))) & 
  (Fconde1(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(ε1))  & 
  (Fconde2(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(ε2))) ==>
  !f:1->Ar f':1->Ar.
  (!g:1->Ar. F o Pa(f,g) = F o Pa(f',g)) ==>
  f = f'
  ”));


val P1252_first_thm = prove_store("P1252_first_thm",
e0
(rpt strip_tac >>
 qsuff_tac ‘d0 o f = d1 o f'’)
(form_goal
 “!Ar Ob d0:Ar->Ob d1 i r.
  ISC(d0,d1,i,r) ==>
  iapcond(d0,d1,i,r) ==>
  !F:Ar * Ar -> Exp(2,E). 
  (!f:1->Ar g:1->Ar. 
  (Fcond0(d0,d1,i,r,f,g) ==> 
   F o Pa(f,g) = Tp1(id(E0))) &
  (Fcond1(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(id(E1))) & 
  (Fconde1(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(ε1))  & 
  (Fconde2(d0,d1,i,r,f,g) ==>
   F o Pa(f,g) = Tp1(ε2))) ==>
  !f:1->Ar f':1->Ar.
  (!g:1->Ar. F o Pa(f,g) = F o Pa(f',g)) ==>
  f = f'
  ”));
