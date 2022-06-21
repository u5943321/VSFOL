val _ = new_fun "App" (mem_sort (mk_set "B"),
                       [("f",fun_sort (mk_set "A") (mk_set "B")),
                       ("a",mem_sort (mk_set "A"))]);

val rel2fun = store_ax("rel2fun",
“!A B R:A~>B. isFun(R) ==> ?!f:A->B. !a b. App(f,a) = b <=> Holds(R,a,b)”);


val rel2fun_ex = prove_store("rel2fun_ex",
e0
(rpt strip_tac >> drule rel2fun >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f’ >> arw[])
(form_goal
 “!A B R:A~>B. isFun(R) ==> 
  ?f:A ->B. !a b. App(f,a) = b <=> Holds(R,a,b)”));

val rel2fun_ex' = rel2fun_ex |> rewr_rule[Fun_def]



val P2fun = prove_store("P2fun",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] (strip_assume_tac) 
 (AX1_ex) >>
 qby_tac ‘!x. ?!y. Holds(R,x,y)’
 >-- (arw[]) >>
 drule rel2fun_ex' >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >> rfs[])
(form_goal “!A B. (!x:mem(A). ?!y:mem(B). P(x,y)) ==>
 ?f:A->B. !a:mem(A) b:mem(B). App(f,a) = b <=> P(a,b)”));



val P2fun' = prove_store("P2fun'",
e0
(rpt strip_tac >> drule P2fun >>
 pop_assum strip_assume_tac >>  
 qexists_tac ‘f’ >> 
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal “!A B. (!x:mem(A). ?!y:mem(B). P(x,y)) ==>
 ?f:A->B. !a:mem(A). P(a, App(f,a))”));




val asR_uex =
    AX1 |> qspecl [‘A’, ‘B’]
        |> fVar_sInst_th
           “P(a:mem(A),b:mem(B))”
           “App(f:A->B,a) = b”

val asR_def = 
    asR_uex |> qsimple_uex_spec "asR" [‘f’] 

val asR_Fun = prove_store("asR_Fun",
e0
(rpt strip_tac >> rw[Fun_expand] >>
 rw[asR_def] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘App(f,a)’ >> rw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B. isFun(asR(f))”));



val FUN_EXT = prove_store("FUN_EXT",
e0
(rpt strip_tac >> 
 assume_tac rel2fun >>
 first_x_assum (qsspecl_then [‘asR(f2)’] assume_tac) >>
 qsspecl_then [‘f2’] assume_tac asR_Fun >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 dimp_tac >> rpt strip_tac >> arw[] >>
 qsuff_tac ‘f1 = f & f2 = f’ 
 >-- (strip_tac >> arw[]) >> strip_tac >> first_x_assum irule (* 2 *) >>
 arw[asR_def])
(form_goal “!A B f1:A->B f2. 
 (!a.App(f1,a) = App(f2,a)) <=> f1 = f2”));

val P2fun_uex = prove_store("P2fun_uex",
e0
(rpt strip_tac >> drule P2fun' >> pop_assum strip_assume_tac >>
uex_tac >> qexists_tac ‘f’ >> arw[] >> rpt strip_tac >>
rw[GSYM FUN_EXT] >> strip_tac >>
last_x_assum (qspecl_then [‘a’] assume_tac) >>
pop_assum (assume_tac o uex_expand) >>
pop_assum strip_assume_tac >> 
qsuff_tac ‘App(f',a) = y & App(f,a) = y’ 
>-- (strip_tac >> arw[]) >>
strip_tac >> first_x_assum irule >> arw[])
(form_goal “!A B. (!x:mem(A). ?!y:mem(B). P(x,y)) ==>
 ?!f:A->B. !a:mem(A). P(a, App(f,a))”));
(*apply only first arg*)


val unique_lemma = proved_th$
e0
(rpt strip_tac >> uex_tac >> qexists_tac ‘a’ >> rw[] >> rpt strip_tac >>
 arw[])
(form_goal “!A a:mem(A). ?!a'. a' = a”)

fun fun_tm_compr (ivar as (n,s)) otm = 
    let val isort = s
        val osort = sort_of otm
        val avoids = HOLset.union(fvt otm,fvt (mk_var ivar))
        val ovt = pvariantt avoids (mk_var ("y",osort))
        val dom = isort |> dest_sort |> snd |> hd
        val cod = osort |> dest_sort |> snd |> hd 
        val th0 = P2fun' |> specl [dom,cod] 
        val p = mk_fvar "P" [mk_var ivar,ovt]
        val p1 = mk_eq ovt otm
        val th1 = fVar_sInst_th p p1 th0
        val lemma = unique_lemma |> allE cod |> allE otm
                                 |> add_cont (fvt (mk_var ivar))
                                 |> allI ivar
        val th2 = mp th1 lemma
    in th2
    end


fun fun_tm_compr_uex (ivar as (n,s)) otm = 
    let val isort = s
        val osort = sort_of otm
        val avoids = HOLset.union(fvt otm,fvt (mk_var ivar))
        val ovt = pvariantt avoids (mk_var ("y",osort))
        val dom = isort |> dest_sort |> snd |> hd
        val cod = osort |> dest_sort |> snd |> hd 
        val th0 = P2fun_uex |> specl [dom,cod] 
        val p = mk_fvar "P" [mk_var ivar,ovt]
        val p1 = mk_eq ovt otm
        val th1 = fVar_sInst_th p p1 th0
        val lemma = unique_lemma |> allE cod |> allE otm
                                 |> add_cont (fvt (mk_var ivar))
                                 |> allI ivar
        val th2 = mp th1 lemma
    in th2
    end

fun qfun_compr qv qt = 
    let val vt = qparse_term_with_cont essps qv
        val v = dest_var vt
        val t = qparse_term_with_cont (fvt vt) qt
    in fun_tm_compr_uex v t
    end;

val Id_uex = rel2fun |> qsspecl [‘id(A)’] |> rewr_rule[id_Fun] 
                    
val Id_def = Id_uex |> qsimple_uex_spec "Id" [‘A’] 
                    |> rewr_rule[id_def]
                    |> qspecl [‘a:mem(A)’,‘a:mem(A)’]
                    |> rewr_rule[]
                    |> gen_all

val App_Id = Id_def |> store_as "App_Id";


val o_ex = prove_store("o_ex",
e0
(rpt strip_tac >> 
 qsspecl_then [‘phi’] assume_tac asR_Fun >>
 qsspecl_then [‘psi’] assume_tac asR_Fun >>
 qby_tac ‘isFun(asR(psi) @ asR(phi))’ 
 >-- (irule ao_Fun >> arw[]) >>
 drule rel2fun >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f’ >> arw[])
(form_goal
 “!A B phi:A->B C psi:B->C. ?f:A->C. 
 !a c. App(f,a) = c <=> Holds(asR(psi) @ asR(phi),a,c)”));
 
val o_uex = prove_store("o_uex",
e0
(rpt strip_tac >>
 qsspecl_then [‘phi’,‘psi’] strip_assume_tac o_ex >>
 uex_tac >> qexists_tac ‘f’ >> arw[]>>
 rpt strip_tac >>
 rw[GSYM FUN_EXT] >> arw[] >>
 last_x_assum (assume_tac o GSYM) >> arw[])
(form_goal  
 “!A B phi:A->B C psi:B->C. ?!f:A->C. 
 !a c. App(f,a) = c <=> Holds(asR(psi) @ asR(phi),a,c)”));

val o_def = o_uex |> spec_all |> qsimple_uex_spec "o" [‘psi’,‘phi’]
                  |> gen_all



val Inj_def = 
    qdefine_psym ("Inj",[‘f:A->B’]) 
                 ‘!x1 x2. App(f,x1) = App(f,x2) ==> x1 = x2’
    |> gen_all |> store_as "Inj_def";

val Surj_def = 
    qdefine_psym ("Surj",[‘f:A->B’]) 
                 ‘!b. ?a. App(f,a) = b’
    |> gen_all |> store_as "Surj_def";
 
val Bij_def =
    qdefine_psym ("Bij",[‘f:A->B’]) 
                 ‘Inj(f) & Surj(f)’
    |> gen_all |> store_as "Bij_def";


val Bij_op = prove_store("Bij_op",
e0
(rpt strip_tac >>
 qsuff_tac ‘isFun(op(asR(f)))’ 
 >-- (strip_tac >> drule rel2fun >>
     pop_assum (strip_assume_tac o uex_expand) >>
     qexists_tac ‘f'’ >>
     arw[GSYM R_EXT,asR_def,op_def]) >> 
 rw[Fun_expand] >>
 fs[Bij_def,Inj_def,Surj_def] >> rpt strip_tac (* 2 *)
 >-- (first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
      qexists_tac ‘a'’ >> arw[op_def,asR_def]) >>
 fs[op_def,asR_def] >> first_x_assum irule >> arw[])
(form_goal “!A B f:A->B. Bij(f) ==> 
 ?f':B->A. asR(f') = op(asR(f))”));


val App_App_o = prove_store("App_App_o",
e0
(rw[o_def,GSYM ao_def,asR_def] >> rpt strip_tac >>
 qexists_tac ‘App(f,a)’ >> arw[])
(form_goal “!A B f:A->B C g:B->C a. 
  App(g o f,a) = App(g,App(f,a))”));

val App_o_l = App_App_o

val asR_o = prove_store("asR_o",
e0
(rw[GSYM R_EXT,asR_def,GSYM ao_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘App(f,a)’ >> arw[GSYM App_App_o]) >>
 arw[App_App_o])
(form_goal “!A B f:A->B C g:B ->C. 
 asR(g o f) = asR(g) @ asR(f)”));

val asR_Id = prove_store("asR_Id",
e0
(rw[asR_def,Id_def,id_def,GSYM R_EXT])
(form_goal
 “!A. asR(Id(A)) = id(A)”));


val asR_eq_eq = prove_store("asR_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 irule $ iffLR FUN_EXT >> 
 drule $ iffRL R_EXT >> fs[asR_def])
(form_goal “!A B f1:A->B f2. asR(f1) = asR(f2) <=> f1 = f2”));



val Thm_2_7_bij = prove_store("Thm_2_7_bij",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (drule Bij_op >> pop_assum strip_assume_tac >>
     qexists_tac ‘f'’ >> pop_assum mp_tac >>
     rw[GSYM asR_eq_eq,asR_o,asR_Id,GSYM R_EXT] >>
     rw[GSYM ao_def,asR_def,id_def,op_def] >>
     strip_tac >> arw[] >> rpt strip_tac >--
     (fs[Bij_def,Inj_def] >> dimp_tac >> strip_tac
      >-- (first_x_assum irule >> arw[]) >>
      qexists_tac ‘App(phi,a)’ >> arw[]) >>
     fs[Bij_def,Inj_def,Surj_def] >> 
     dimp_tac >> strip_tac (* 2 *)
     >-- (qpick_x_assum ‘App(phi, b') = a’ 
          (assume_tac o GSYM) >> arw[]) >>
     arw[] >> 
     last_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
     qexists_tac ‘a'’ >> arw[]) >>
 rw[Bij_def,Inj_def,Surj_def] >> rpt strip_tac (* 2 *)
 >-- (qby_tac ‘App(psi,App(phi, x1)) = App(psi,App(phi, x2))’ 
      >-- arw[] >>
      rfs[GSYM App_App_o,Id_def]) >>
 qexists_tac ‘App(psi,b)’ >> arw[GSYM App_App_o,Id_def])
(form_goal
 “!A B phi:A->B.Bij(phi) <=> ?psi:B->A. psi o phi = Id(A) & phi o psi = Id(B)”));


val Inj_lcancel = prove_store("Inj_lcancel",
e0
(rpt strip_tac >> fs[Inj_def] >>
 rw[GSYM FUN_EXT] >> strip_tac >> 
 qsuff_tac ‘App(m,App(f,a)) = App(m,App(g,a))’ >--
 (strip_tac >> first_x_assum irule >> arw[]) >>
 arw[GSYM App_App_o])
(form_goal
 “!A B m:A->B.Inj(m) ==>
  !X f:X->A g:X->A. m o f = m o g ==> f = g”));
 

val IdL = prove_store("IdL",
e0
(rw[Id_def,GSYM FUN_EXT,App_App_o])
(form_goal “!A B f:A->B. Id(B) o f = f”));


val IdR = prove_store("IdR",
e0
(rw[Id_def,GSYM FUN_EXT,App_App_o,App_Id] )
(form_goal “!A B f:A->B. f o Id(A) = f”));



local 
val l = 
    P2fun' |> qspecl [‘A’,‘A’]
           |> fVar_sInst_th “P(x:mem(A),y:mem(A))”
              “ Holds(R:A0~>A0,App(i:A->A0,x),App(i,y))”
in
val Inj_lift_R_lemma = prove_store("Inj_lift_R_lemma",
e0
(rpt strip_tac >> rw[App_App_o] >> irule l >> arw[]
 )
(form_goal “!A A0 i:A->A0. Inj(i) ==>
 !R:A0~>A0. (!a1:mem(A). ?!a2:mem(A). Holds(R,App(i,a1),App(i,a2))) ==>
 ?f:A->A. (!a. Holds(R,App(i,a),App(i o f,a)))”));
end

val asR_def = asR_def |> gen_all

val Inj_lift_fun_lemma = prove_store("Inj_lift_fun_lemma",
e0
(rpt strip_tac >>
 drule Inj_lift_R_lemma >>
 first_x_assum (qspecl_then [‘asR(f0)’] assume_tac) >>
 qsuff_tac ‘?f:A->A.!a. Holds(asR(f0), App(i, a), App(i o f, a))’ 
 >-- (strip_tac >> qexists_tac ‘f’ >> 
     qspecl_then [‘A0’,‘A0’,‘f0’] assume_tac asR_def >>
     fs[App_App_o]) >>
 first_x_assum irule >> strip_tac >> uex_tac >>
 first_x_assum (qspecl_then [‘a1’] strip_assume_tac) >> 
 qexists_tac ‘a2’ >> 
 qspecl_then [‘A0’,‘A0’,‘f0’] assume_tac asR_def >> arw[] >>
 fs[App_App_o] >> rpt strip_tac >> fs[Inj_def] >>
 first_x_assum drule >> arw[])
(form_goal “!A A0 i:A->A0. Inj(i) ==>
 !f0:A0->A0. (!a1:mem(A). ?a2:mem(A). App(f0 o i,a1) = App(i,a2)) ==>
 ?f:A->A. (!a. App(i o f,a) = App(f0 o i,a))”));


val Inj_lift_fun_lemma' = prove_store("Inj_lift_fun_lemma'",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?f:A->A. (!a. App(i o f,a) = App(f0 o i,a))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >> drule Inj_lcancel >> first_x_assum irule >>
     irule $ iffLR FUN_EXT >> arw[]) >> 
 drule Inj_lift_R_lemma >>
 first_x_assum (qspecl_then [‘asR(f0)’] assume_tac) >>
 qsuff_tac ‘?f:A->A.!a. Holds(asR(f0), App(i, a), App(i o f, a))’ 
 >-- (strip_tac >> qexists_tac ‘f’ >> 
     qspecl_then [‘A0’,‘A0’,‘f0’] assume_tac asR_def >>
     fs[App_App_o]) >>
 first_x_assum irule >> strip_tac >> uex_tac >>
 first_x_assum (qspecl_then [‘a1’] strip_assume_tac) >> 
 qexists_tac ‘a2’ >> 
 qspecl_then [‘A0’,‘A0’,‘f0’] assume_tac asR_def >> arw[] >>
 fs[App_App_o] >> rpt strip_tac >> fs[Inj_def] >>
 first_x_assum drule >> arw[])
(form_goal “!A A0 i:A->A0. Inj(i) ==>
 !f0:A0->A0. (!a1:mem(A). ?a2:mem(A). App(f0 o i,a1) = App(i,a2)) ==>
 ?!f:A->A. (!a. App(i o f,a) = App(f0 o i,a))”));


val Inj_eq_eq = prove_store("Inj_eq_eq",
e0
(rpt strip_tac >> fs[Inj_def] >> dimp_tac >>
 rpt strip_tac >> arw[] >>
 first_x_assum irule >> arw[])
(form_goal “!X Y i:X->Y. Inj(i) ==>
 (!x1 x2. App(i,x1) = App(i,x2) <=> x1 =  x2)”));


val Inj_lift_fun = prove_store("Inj_lift_fun",
e0
(rpt strip_tac >>
 irule (P2fun' |> qspecl [‘X’,‘A’] 
        |> fVar_sInst_th “P(x:mem(X),a:mem(A))”
           “App(i:A->A0,a) = App(f0:X->A0,x)”
        |> rewr_rule[GSYM App_App_o]) >>
 flip_tac >> strip_tac >> uex_tac >>
 first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 qexists_tac ‘a’ >> arw[] >> fs[Inj_def] >> rpt strip_tac >>
 first_x_assum irule >> arw[]
 )
(form_goal
 “!A A0 i:A-> A0.
  Inj(i) ==>
  !X f0:X->A0.
  (!x. ?a.App(f0,x) = App(i,a))==>
  ?f:X->A. 
  !x. App(i o f,x) = App(f0,x)”));



val Inj_lift_fun_uex = prove_store("Inj_lift_fun_uex",
e0
(rpt strip_tac >>
 irule (P2fun_uex |> qspecl [‘X’,‘A’] 
        |> fVar_sInst_th “P(x:mem(X),a:mem(A))”
           “App(i:A->A0,a) = App(f0:X->A0,x)”
        |> rewr_rule[GSYM App_App_o]) >>
 flip_tac >> strip_tac >> uex_tac >>
 first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 qexists_tac ‘a’ >> arw[] >> fs[Inj_def] >> rpt strip_tac >>
 first_x_assum irule >> arw[]
 )
(form_goal
 “!A A0 i:A-> A0.
  Inj(i) ==>
  !X f0:X->A0.
  (!x. ?a.App(f0,x) = App(i,a))==>
  ?!f:X->A. 
  !x. App(i o f,x) = App(f0,x)”));


val o_assoc = prove_store("o_assoc",
e0
(rw[GSYM FUN_EXT,App_App_o])
(form_goal
 “!A B f:A->B C g:B->C D h:C->D.
  (h o g) o f = h o g o f”));


val P2fun_uex' = prove_store("P2fun_uex'",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?f:A->B. !a:mem(A). P(a, App(f,a))’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >>
     rpt strip_tac >>
     first_x_assum (qspecl_then [‘a’] assume_tac)>>
     first_x_assum (qspecl_then [‘a’] assume_tac) >>
     first_x_assum (qspecl_then [‘a’] (strip_assume_tac o uex_expand)) >>
     qsuff_tac ‘App(f',a) = y & App(f,a) = y’ 
     >-- (rpt strip_tac >> arw[]) >>
     rpt strip_tac >> first_x_assum irule >> arw[]) >>
 drule P2fun' >> arw[])
(form_goal “!A B. (!x:mem(A). ?!y:mem(B). P(x,y)) ==>
 ?!f:A->B. !a:mem(A). P(a, App(f,a))”));


val P2fun_uex0 = prove_store("P2fun_uex0",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?f:A->B. !a:mem(A) b:mem(B). App(f,a) = b <=> P(a,b)’ 
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >>
     rpt strip_tac >> arw[] >> last_x_assum (irule o iffLR) >> rw[]) >>
 drule P2fun >> arw[])
(form_goal “!A B. (!x:mem(A). ?!y:mem(B). P(x,y)) ==>
 ?!f:A->B. !a:mem(A) b:mem(B). App(f,a) = b <=> P(a,b)”));

