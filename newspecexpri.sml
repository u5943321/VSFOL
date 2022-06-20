


val isPair_def = qdefine_psym("isPair",[‘p1:AxB->A’,‘p2:AxB->B’])
‘!x:mem(A) y:mem(B). 
   ?!r:mem(AxB).App(p1,r) = x & App(p2,r) = y’

val isPair_uex = prove_store("isPair_uex",
e0
(rpt gen_tac >> strip_tac (* 2 *)
 >-- fs[isPair_def] >>
     qby_tac
     ‘∀ab:mem(AB).
      ?!ab'. App(p1,ab) = App(p1',ab') & 
             App(p2,ab) = App(p2',ab')’ 
     >-- (strip_tac >> flip_tac >> arw[]) >>
     drule
     (P2fun |> qspecl [‘AB’,‘AB'’] 
     |> fVar_sInst_th “P(ab:mem(AB),ab':mem(AB'))”
        “App(p1:AB->A,ab) = App(p1':AB'->A,ab') & 
         App(p2:AB->B,ab) = App(p2':AB'->B,ab')”) >>
     pop_assum (x_choose_then "i" assume_tac) >>
     qby_tac
     ‘∀ab':mem(AB').
      ?!ab. App(p1,ab) = App(p1',ab') & 
             App(p2,ab) = App(p2',ab')’ 
     >-- arw[] >>
     drule
     (P2fun |> qspecl [‘AB'’,‘AB’] 
     |> fVar_sInst_th “P(ab':mem(AB'),ab:mem(AB))”
        “App(p1:AB->A,ab) = App(p1':AB'->A,ab') & 
         App(p2:AB->B,ab) = App(p2':AB'->B,ab')”) >> 
     pop_assum (x_choose_then "j" assume_tac) >>
     qexistsl_tac [‘i’,‘j’] >>
     qby_tac
     ‘i o j = Id(AB')’ 
     >-- (arw[GSYM FUN_EXT,Id_def,App_App_o] >>
         pop_assum (assume_tac o GSYM) >> arw[]) >>
     qby_tac
     ‘j o i = Id(AB)’ 
     >-- (arw[GSYM FUN_EXT,Id_def,App_App_o] >>
          strip_tac >>
          last_x_assum (qsspecl_then [‘a’,‘App(i,a)’] (assume_tac o GSYM)) >>
          arw[]) >>
     arw[] >>
     qby_tac
     ‘p1' o i = p1 & p2' o i = p2’
     >-- (arw[GSYM FUN_EXT,App_App_o] >> 
         qpick_x_assum
         ‘∀a b.
          App(i, a) = b <=>
          App(p1, a) = App(p1', b) & App(p2, a) = App(p2', b)’
         (assume_tac o GSYM) >> flip_tac >> 
         qsuff_tac
         ‘∀a. App(p1,a) = App(p1',App(i,a)) &
              App(p2,a) = App(p2',App(i,a))’ 
         >-- (rpt strip_tac >> arw[]) >> arw[]) >> arw[] >>
     arw[GSYM FUN_EXT,App_App_o] >> 
     qpick_x_assum
     ‘∀a b.
      App(j, a) = b <=>
      App(p1, b) = App(p1', a) & App(p2, b) = App(p2', a)’
         (assume_tac o GSYM) >> 
     qsuff_tac
     ‘∀a. App(p1,App(j,a)) = App(p1',a) &
          App(p2,App(j,a)) = App(p2',a)’ 
     >-- (rpt strip_tac >> arw[]) >>
     arw[])
(form_goal “!A B AB p1:AB->A p2:AB ->B AB' p1':AB'->A p2'. 
 isPair(p1,p2) & isPair(p1',p2') ⇒ 
 ?i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
  p1' o i = p1 & p2' o i = p2 &
  p1 o j = p1' & p2 o j = p2'”));


val Pr_uex = prove_store("Pr_uex",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] assume_tac Cross_ex >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘AxB’,‘p1’,‘p2’] >>
 qby_tac
 ‘isPair(p1,p2)’ 
 >-- (rw[isPair_def] >>
     rpt strip_tac >>
     uex_tac >> first_x_assum (qspecl_then [‘x’,‘y’] strip_assume_tac) >>
     qexists_tac ‘r’ >> arw[] >>
     rpt strip_tac >> first_x_assum irule >> arw[]) >>
 arw[] >> rpt strip_tac >>
 qsspecl_then [‘p1’,‘p2’,‘p1'’,‘p2'’] assume_tac  isPair_uex >>
 first_x_assum irule >> arw[])
(form_goal “!A B. ?AB p1:AB->A p2:AB ->B. 
 isPair(p1,p2) &
 (!AB' p1':AB'->A p2'. isPair(p1',p2') ==>
  ?i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
  p1' o i = p1 & p2' o i = p2 &
  p1 o j = p1' & p2 o j = p2')”));

val Pr_ts_ex = proved_th $
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] strip_assume_tac Cross_ex >>
 qexistsl_tac [‘AxB’,‘p1’,‘p2’] >> rw[])
(form_goal “!A B. ?AB p1:AB->A p2:AB ->B. T”)

val Reqv = proved_th $
e0
(rpt strip_tac (* 3 *)
 >-- (qexistsl_tac [‘Id(AB)’,‘Id(AB)’] >> rw[IdL,IdR]) 
 >-- (qexistsl_tac [‘j’,‘i’] >> arw[]) >>
 qexistsl_tac [‘i' o i’,‘j o j'’] >>
 arw[GSYM o_assoc] >>
 qsuff_tac
 ‘i' o (i o j) o j' = Id(AB'') & j o (j' o i') o i = Id(AB)’ 
 >-- rw[o_assoc] >>
 arw[IdL,IdR])
(form_goal 
“(!AB p1:AB->A p2:AB->B.
 ?i:AB->AB j. i o j = Id(AB) & j o i = Id(AB) &
  p1 o i = p1 & p2 o i = p2 &
  p1 o j = p1 & p2 o j = p2) &
 (!AB p1:AB->A p2:AB->B AB' p1':AB'->A p2':AB'->B. 
  (?i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   p1' o i = p1 & p2' o i = p2 &
   p1 o j = p1' & p2 o j = p2')==>
  (?i:AB'->AB j. i o j = Id(AB) & j o i = Id(AB') &
   p1 o i = p1' & p2 o i = p2' &
   p1' o j = p1 & p2' o j = p2)) & 
 (!AB p1:AB->A p2:AB->B AB' p1':AB'->A p2':AB'->B
      AB'' p1'':AB''->A p2'':AB''->B. 
  (?i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   p1' o i = p1 & p2' o i = p2 &
   p1 o j = p1' & p2 o j = p2') &
  (?i:AB'->AB'' j. i o j = Id(AB'') & j o i = Id(AB') &
   p1'' o i = p1' & p2'' o i = p2' &
   p1' o j = p1'' & p2' o j = p2'') ==>
  (?i:AB->AB'' j. i o j = Id(AB'') & j o i = Id(AB) &
   p1'' o i = p1 & p2'' o i = p2 &
   p1 o j = p1'' & p2 o j = p2''))
 ”)

val uexth = Pr_uex |> spec_all

val eth = Pr_ts_ex |> spec_all

val eqvth = Reqv

val fnames = ["*","p1","p2"]

(*val iseqr = “P()”*)


val arg1 = List.map (dest_var o rastt) 
                    ["AB","p1:AB->A","p2:AB->B"]

val arg2 = List.map (dest_var o rastt) 
                     ["AB'","p1':AB'->A","p2':AB'->B"]

val eqr = 
“?i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   (p1':AB'->A) o i = p1 & (p2':AB'->B) o i = p2 &
   p1 o j = p1' & p2 o j = p2'”


val arg = arg1
val Q = “isPair(p1:AB->A,p2:AB->B)”

val argQ = (arg,Q)

val vl = List.map dest_var [rastt "A",rastt "B"]


val arg12eqr = (arg1,arg2,eqr)


new_spec argQ arg12eqr ["*","p1","p2"] vl eth eqvth uexth




val Id_uex = prove_store("Id_uex",
e0
(cheat)
(form_goal “?i:A ->A. (!a.App(i,a) = a) & 
 !i'. (!a.App(i',a) = a) ==> i = i'”));

val uexth = Id_uex

val eth = proved_th $
e0
cheat
(form_goal “?i:A->A.T”)

val vl = [("A",set_sort)]

(*spec of new fsym if the input is a uex theorem with assumptions*)

val fname = "Id"

val argQ = ([dest_var (rastt "i:A->A")],“!a. App(i:A->A,a) = a”)

val arg12eqr = ([dest_var (rastt "i:A->A")],[dest_var (rastt "i':A->A")],
                “i = i':A->A”)

val eqvth = proved_th $
e0
cheat
(form_goal “(!i:A->A. i = i) &
 (!i:A->A i':A->A. i = i' ==> i' = i) &
 (!i:A->A i':A->A i'':A->A. 
   i = i' & i' = i'' ==> i = i'')”)

new_spec argQ arg12eqr [fname] vl eth eqvth uexth


val Id_uex0 = prove_store("Id_uex0",
e0
(cheat)
(form_goal “?!i:A ->A. (!a.App(i,a) = a)”));

val uexth0 = Id_uex0

simple_uex_spec "Id" [("A",set_sort)] Id_uex0



set_spec (rastt "N0") sname iname fvs uexth




val Exp_ev_unique = prove_store("Exp_ev_unique",
e0
(rpt strip_tac >> 
 qby_tac
 ‘∀a2b.?!a2b'.∀a. App(Ap1(ev,a2b),a) = App(ev',Pair(a,a2b'))’
 >-- (strip_tac >>
     first_x_assum (qsspecl_then [‘Ap1(ev,a2b)’] assume_tac) >>
     flip_tac >> arw[]) >>
 drule 
 (P2fun |> qspecl [‘A2B’,‘A2B'’] 
        |> fVar_sInst_th “P(a2b:mem(A2B),a2b':mem(A2B'))”
           “∀a. App(Ap1(ev:A * A2B -> B,a2b),a) = 
                App(ev':A * A2B' -> B,Pair(a,a2b'))”) >>
 pop_assum (x_choose_then "i" assume_tac) >>
 qby_tac
 ‘∀a2b'.?!a2b.∀a. App(Ap1(ev',a2b'),a) = App(ev,Pair(a,a2b))’
 >-- (strip_tac >>
     first_x_assum (qsspecl_then [‘Ap1(ev',a2b')’] assume_tac) >>
     flip_tac >> arw[]) >>
 drule 
 (P2fun |> qspecl [‘A2B'’,‘A2B’] 
        |> fVar_sInst_th “P(a2b':mem(A2B'),a2b:mem(A2B))”
           “∀a. App(Ap1(ev':A * A2B' -> B,a2b'),a) = 
                App(ev:A * A2B -> B,Pair(a,a2b))”) >>
 pop_assum (x_choose_then "j" assume_tac) >>
 qexistsl_tac [‘i’,‘j’] >> 
 qby_tac
 ‘i o j = Id(A2B')’ 
 >-- (rw[GSYM FUN_EXT,Id_def,App_App_o] >> arw[] >>
     strip_tac >>
     last_x_assum (qsspecl_then [‘a’,‘App(j,a)’] assume_tac) >>
     fs[] >> 
     pop_assum (assume_tac o GSYM) >> arw[Ap1_def]) >>
 qby_tac
 ‘j o i = Id(A2B)’ 
 >-- (rw[GSYM FUN_EXT,Id_def,App_App_o] >> arw[] >>
     strip_tac >>
     first_x_assum (qsspecl_then [‘a’,‘App(i,a)’] assume_tac) >>
     fs[] >> 
     pop_assum (assume_tac o GSYM) >> arw[Ap1_def]) >>
 arw[] >>
 qby_tac
 ‘ev' o Prla(Id(A), i) = ev’ 
 >-- (rw[GSYM FUN_EXT] >> forall_cross_tac >> 
     rw[App_App_o,App_Prla,Id_def] >>
     fs[Ap1_def] >>
     flip_tac >> rpt strip_tac >>
     first_x_assum (irule o iffLR) >> rw[]) >>
 qby_tac
 ‘ev o Prla(Id(A), j) = ev'’ 
 >-- (rw[GSYM FUN_EXT] >> forall_cross_tac >> 
     rw[App_App_o,App_Prla,Id_def] >>
     fs[Ap1_def] >>
     flip_tac >> rpt strip_tac >>
     first_x_assum (irule o iffLR) >> rw[]) >>
 arw[])
(form_goal 
 “∀A B A2B ev:A * A2B ->B A2B' ev': A * A2B' -> B.
  (!f:A->B.?!sf:mem(A2B).!a:mem(A).App(ev,Pair(a,sf)) = App(f,a)) &
  (!f:A->B.?!sf:mem(A2B').!a:mem(A).App(ev',Pair(a,sf)) = App(f,a)) ⇒
  ∃i: A2B -> A2B' j:A2B' -> A2B. 
   i o j = Id(A2B') & j o i = Id(A2B) &
   ev' o Prla(Id(A),i)  = ev & ev o Prla(Id(A),j) = ev'”));


val Exp_ex_uex = prove_store("Exp_ex_uex",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] strip_assume_tac Exp_ex >>
 qexistsl_tac [‘A2B’,‘ev’] >> arw[] >> 
 rpt strip_tac >> irule Exp_ev_unique >> arw[])
(form_goal
“!A B.
 ?A2B ev:A * A2B ->B. 
 (!f:A->B.?!sf:mem(A2B).!a:mem(A).App(ev,Pair(a,sf)) = App(f,a)) &
 ∀A2B' ev':A * A2B' -> B.
 (∀f:A->B.?!sf:mem(A2B').!a:mem(A).App(ev',Pair(a,sf)) = App(f,a)) ⇒
 ∃i: A2B -> A2B' j:A2B' -> A2B. 
   i o j = Id(A2B') & j o i = Id(A2B) &
   ev' o Prla(Id(A),i)  = ev & ev o Prla(Id(A),j) = ev'”));

val Exp_uex_refl = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘Id(A2B)’,‘Id(A2B)’] >> 
 rw[IdL,IdR,Prla_Id])
(form_goal 
 “∀A2B ev:A * A2B -> B.
  ∃i: A2B -> A2B j:A2B -> A2B. 
   i o j = Id(A2B) & j o i = Id(A2B) &
   ev o Prla(Id(A),i)  = ev & ev o Prla(Id(A),j) = ev”)


val Exp_uex_sym = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘j’,‘i’] >> arw[])
(form_goal 
 “∀A2B ev:A * A2B -> B A2B' ev':A * A2B' -> B.
  (∃i: A2B -> A2B' j:A2B' -> A2B. 
   i o j = Id(A2B') & j o i = Id(A2B) &
   ev' o Prla(Id(A),i)  = ev & ev o Prla(Id(A),j) = ev') ⇒ 
  (∃i: A2B' -> A2B j:A2B -> A2B'.
   i o j = Id(A2B) & j o i = Id(A2B') &
   ev o Prla(Id(A),i) = ev' & ev' o Prla(Id(A),j) = ev)”)


val Exp_uex_trans = proved_th $
e0
(rpt strip_tac >>
 qexistsl_tac [‘i' o i’,‘j o j'’] >> 
 rw[Prla_rsplit2] >> arw[GSYM o_assoc] >>
 qsuff_tac
 ‘i' o (i o j) o j' = Id(A2B'') & j o (j' o i') o i = Id(A2B)’
 >-- rw[o_assoc] >>
 arw[IdL,IdR])
(form_goal 
 “∀A2B ev:A * A2B -> B A2B' ev':A * A2B' -> B A2B'' ev'':A * A2B'' -> B.
  (∃i: A2B -> A2B' j:A2B' -> A2B. 
   i o j = Id(A2B') & j o i = Id(A2B) &
   ev' o Prla(Id(A),i)  = ev & ev o Prla(Id(A),j) = ev') & 
  (∃i: A2B' -> A2B'' j:A2B'' -> A2B'.
   i o j = Id(A2B'') & j o i = Id(A2B') &
   ev'' o Prla(Id(A),i) = ev' & ev' o Prla(Id(A),j) = ev'') ⇒ 
  (∃i: A2B -> A2B'' j:A2B'' -> A2B.
   i o j = Id(A2B'') & j o i = Id(A2B) &
   ev'' o Prla(Id(A),i) = ev & ev o Prla(Id(A),j) = ev'')”)


val Exp_ev_eqv = conjI Exp_uex_refl (conjI Exp_uex_sym Exp_uex_trans)

val arg = [("A2B",set_sort),("ev",fun_sort (rastt "A * A2B") (rastt "B"))]

val Q = “!f:A->B.?!sf:mem(A2B).!a:mem(A).App(ev,Pair(a,sf)) = App(f,a)”
val argQ = (arg,Q) 

val arg1 = arg 
val arg2 = [("A2B'",set_sort),("ev'",fun_sort (rastt "A * A2B'") (rastt "B"))] 

val eqr = “(∃i: A2B -> A2B' j:A2B' -> A2B. 
   i o j = Id(A2B') & j o i = Id(A2B) &
   ev' o Prla(Id(A),i)  = ev:A * A2B ->B & ev o Prla(Id(A),j) = ev')”

val arg12eqr = (arg1,arg2,eqr) 
val fnames = ["Exp","ev"]

val vl = [("A",set_sort),("B",set_sort)] 


val eth = proved_th $
e0
cheat
(form_goal
“?A2B ev:A * A2B ->B. T”)

val eqvth = Exp_ev_eqv
val uexth = Exp_ex_uex

new_spec argQ arg12eqr fnames vl eth eqvth (spec_all uexth)

check_ER arg12eqr eqvth uexth 

val argseqr = arg12eqr

val reflth = Exp_uex_refl



val symth = Exp_uex_sym

val transth = Exp_uex_trans


fun check_ER argseqr eqvth uexth = 
    let val eqvcls = mk_ER_condf argseqr
        val _ = eq_form (eqvcls,concl eqvth) orelse
                raise simple_fail "newspec.eqvth concl"
        val _ = HOLset.isSubset(cont eqvth,cont uexth) orelse
                raise simple_fail "newspec.eqvth cont"
        val _ = List.all 
                    (fn asm => 
                        List.exists
                            (fn a => eq_form(a,asm)) (ant uexth))
                    (ant eqvth) orelse
                raise simple_fail "newspec.eqvth ant"

val Pow_unique = prove_store("Pow_unique",
e0
(cheat)
(form_goal
 “∀PA e:A ~>PA PA' e':A~> PA'.
  (∀S1:1~>A. 
   ?!s:mem(PA).
     !x. Holds(S1,dot,x) ⇔ Holds(e,x,s)) &
  (∀S1:1~>A. 
   ?!s:mem(PA').
     !x. Holds(S1,dot,x) ⇔ Holds(e',x,s)) ⇒
  ∃i:PA -> PA' j:PA' -> PA. 
     i o j = Id(PA') & j o i = Id(PA) &
     asR(i) @ e = e' & asR(j) @ e' = e ”));

val Pow_R_REFL = prove_store("Pow_R_REFL",
e0
(rpt strip_tac >> qexistsl_tac [‘Id(PA)’,‘Id(PA)’] >>
 rw[IdL,IdR,asR_Id,idL,idR])
(form_goal
 “∀PA e:A ~>PA.
    ∃i:PA -> PA j:PA -> PA. 
     i o j = Id(PA) & j o i = Id(PA) &
     asR(i) @ e = e & asR(j) @ e = e ”));


val Pow_R_SYM = prove_store("Pow_R_SYM",
e0
(rpt strip_tac >>
 qexistsl_tac [‘j’,‘i’] >> arw[])
(form_goal
 “∀PA e:A~>PA PA' e':A~> PA'.
(∃i:PA -> PA' j:PA' -> PA. 
   i o j = Id(PA') & j o i = Id(PA) &
   asR(i) @ e = e' & asR(j) @ e' = e) ⇒
 (∃i:PA' -> PA j:PA -> PA'. 
   i o j = Id(PA) & j o i = Id(PA') &
   asR(i) @ e' = e & asR(j) @ e = e')”));


val Pow_R_TRANS = prove_store("Pow_R_TRANS",
e0
(rpt strip_tac >>
 qexistsl_tac [‘i' o i’,‘j o j'’] >> 
 arw[ao_assoc,asR_o]>>
 qsuff_tac
 ‘i' o (i o j) o j' = Id(PA'') & j o (j' o i') o i = Id(PA)’ 
 >-- rw[o_assoc] >>
 arw[IdR,IdL])
(form_goal
 “∀PA e:A~>PA PA' e':A~> PA' PA'' e'':A~>PA''.
(∃i:PA -> PA' j:PA' -> PA. 
   i o j = Id(PA') & j o i = Id(PA) &
   asR(i) @ e = e' & asR(j) @ e' = e) &
 (∃i:PA' -> PA'' j:PA'' -> PA'. 
   i o j = Id(PA'') & j o i = Id(PA') &
   asR(i) @ e' = e'' & asR(j) @ e'' = e') ⇒
 (∃i:PA -> PA'' j:PA'' -> PA. 
   i o j = Id(PA'') & j o i = Id(PA) &
   asR(i) @ e = e'' & asR(j) @ e'' = e)”));


val o_uex = prove_store("o_uex",
e0
(rpt strip_tac >> uex_tac >>
 qsspecl_then [‘phi’,‘psi’] strip_assume_tac o_ex >>
 qexists_tac ‘f’ >> arw[] >>
 rpt strip_tac >> rw[GSYM FUN_EXT] >>
 arw[] >> strip_tac >>  
 last_x_assum (irule o iffLR) >> rw[])
(form_goal
 “!A B phi:A->B C psi:B->C. ?!f:A->C. 
 !a c. App(f,a) = c <=> Holds(asR(psi) @ asR(phi),a,c)”));
