val _ = new_sort "set" [];
val _ = new_sort "mem" [("A",mk_sort "set" [])];
val _ = new_sort "rel" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "rel" "~>"

val set_sort = mk_sort "set" []
fun mem_sort A = mk_sort "mem" [A]
fun rel_sort A B = mk_sort "rel" [A,B]
fun mk_set A = mk_var(A,set_sort)
fun mk_rel R A B = mk_var(R,rel_sort A B)
fun mk_mem a A = mk_var(a,mem_sort A)

val _ = EqSorts := "rel" :: (!EqSorts)
val _ = EqSorts := "mem" :: (!EqSorts)

val _ = new_pred "Holds" [("R",rel_sort (mk_set "A") (mk_set "B")),
                         ("a",mem_sort (mk_set "A")),
                         ("b",mem_sort (mk_set "B"))]


val AX0 = store_ax("AX0",“?A a:mem(A).T”);

val AX1 = store_ax("AX1",
“!A B:set.?!R:A~>B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)”);

val Fun_def = 
    qdefine_psym ("isFun",[‘R:A~>B’]) 
                 ‘!x:mem(A). ?!y:mem(B). Holds(R,x,y)’
    |> gen_all |> store_as "Fun_def";


val Fun_expand = proved_th $
e0
(rpt strip_tac >> rw[Fun_def] >>
 rw[uex_def “?!y:mem(B).Holds(R,x,y)”] >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac (* 2 *)
     >-- (first_x_assum (qspecl_then [‘a’] assume_tac) >> 
          pop_assum strip_assume_tac >> qexists_tac ‘y’ >> arw[]) 
     >-- (first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
          first_assum rev_drule >>
          first_assum (qspecl_then [‘b2’] assume_tac) >>
          first_assum drule >> arw[])) >>
 rpt strip_tac >> last_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
 qexists_tac ‘b’ >> arw[] >> rpt strip_tac >> first_x_assum irule >>
 qexists_tac ‘x’ >> arw[])
(form_goal
“!A B R:A~>B. isFun(R) <=>
 (!a.?b.Holds(R,a,b)) & 
 (!a b1 b2. Holds(R,a,b1) & Holds(R,a,b2) ==> b1 = b2)”)


val _ = new_sort "fun" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "fun" "->"

fun fun_sort A B = mk_sort "fun" [A,B]
fun mk_func f A B = mk_var(f,fun_sort A B)
val _ = EqSorts := "fun" :: (!EqSorts)

val _ = new_fun "App" (mem_sort (mk_set "B"),
                       [("f",fun_sort (mk_set "A") (mk_set "B")),
                       ("a",mem_sort (mk_set "A"))]);

val rel2fun = store_ax("rel2fun",
“!A B R:A~>B. isFun(R) ==> ?!f:A->B. !a b. App(f,a) = b <=> Holds(R,a,b)”);


local
val l = fVar_sInst_th
“P(a:mem(A),b:mem(B))”
“App(f:A->B,a) = b”
(AX1 |> qspecl [‘A’, ‘B’] |> uex_expand)
in
val asR_ex = prove_store("asR_ex",
e0
(rpt strip_tac >> strip_assume_tac l >>
 qexists_tac ‘R’ >> arw[])
(form_goal
 “!A B f:A->B.?R.!a b. Holds(R,a,b) <=> App(f,a) = b”));
end
 
val exth = proved_th $
e0
(strip_tac >> 
 qsspecl_then [‘f’] strip_assume_tac asR_ex >>
 qexists_tac ‘R’ >> rw[])
(form_goal “!f:A->B.?R:A~>B.T”)

val asR_def = asR_ex |> spec_all |> SKOLEM (spec_all exth) "asR"
                     [dest_var (rastt "f:A -> B")]

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



val _ = new_pred "isTab" [("R",rel_sort (mk_set "A") (mk_set "B")),
                          ("p",rel_sort (mk_set "TR") (mk_set "A")),
                          ("q",rel_sort (mk_set "TR") (mk_set "B"))]


val Tab_def = qdefine_psym ("isTab",[‘R:A~>B’,‘p:TR -> A’,‘q:TR->B’])
‘(!x y. Holds(R,x,y) <=> ?r. App(p,r) = x & App(q,r) = y) & 
 !r s. App(p,r) = App(p,s) & App(q,r) = App(q,s) ==> r = s’
|> qgenl [‘A’,‘B’,‘R’,‘TR’,‘p’,‘q’]
|> store_as "Tab_def";


val AX2 = new_ax “!A B R:A~>B.?TR p:TR->A q:TR->B. 
(!x y. Holds(R,x,y) <=> ?r. App(p,r) = x & App(q,r) = y) & 
 !r s. App(p,r) = App(p,s) & App(q,r) = App(q,s) ==> r = s”;



local
val lemma = 
    AX1 |> qspecl [‘A’,‘A’]
        |> fVar_sInst_th “P(a:mem(A),b:mem(B))”
           “~(a:mem(A) = a)”
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma) 
in
val Thm_2_2 = prove_store("Thm_2_2",
e0
(strip_assume_tac AX0 >> strip_assume_tac lemma' >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 >>
 qexists_tac ‘TR’ >> strip_tac >> 
 by_tac “!a b. ~Holds(R:A~>A,a:mem(A),b:mem(A))” 
 >-- (rpt strip_tac >> pop_assum (K all_tac) >> pop_assum (K all_tac) >>
      once_arw[] >> ccontra_tac >> fs[]) >>
 qsuff_tac ‘Holds(R,App(p,a'),App(q,a'))’
 >-- arw[] >>
 pop_assum (K all_tac) >> arw[] >> qexists_tac ‘a'’ >> rw[])
(form_goal
“?Empty. !a:mem(Empty).F”));
end
 
local 
val lemma = 
    AX1 |> qspecl [‘A’,‘A’]
        |> fVar_sInst_th “P(y:mem(A),z:mem(A))”
           “y = a0:mem(A) & z = a0” 
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma)
in
val Thm_2_3 = prove_store("Thm_2_3",
e0
(x_choosel_then ["A","a0"] assume_tac AX0 >> 
 strip_assume_tac lemma' >>
 qspecl_then [‘A’,‘A’,‘R’] strip_assume_tac AX2 >>
 qby_tac ‘Holds(R,a0,a0)’ >--
 (pop_assum (K all_tac) >> pop_assum (K all_tac) >> arw[]) >>
 pop_assum mp_tac >> once_arw[] >> strip_tac  >>
 qexistsl_tac [‘TR’,‘r’] >> 
 strip_tac >> first_x_assum irule >> arw[] >>
 fs[] >> first_x_assum $ (irule o iffLR) >>
 qexists_tac ‘x'’ >> rw[])
(form_goal
“?ONE x:mem(ONE). !x':mem(ONE). x' = x”));
end

local
val exth = proved_th $
e0
(strip_assume_tac Thm_2_3 >> qexists_tac ‘ONE’ >> rw[])
(form_goal “?a:set.T”)
in
val ONE_def = SKOLEM exth "1" [] Thm_2_3
end

local
val exth' = proved_th $
e0
(strip_assume_tac ONE_def >> qexists_tac ‘x’ >> rw[])
(form_goal “?a:mem(1).T”)
in
val dot_def = SKOLEM exth' "dot" [] ONE_def
end

val ONE = mk_fun "1" []
val dot = mk_fun "dot" []


local
val l = AX1 |> qspecl [‘A’,‘B’] |> uex_expand
            |> fVar_sInst_th “P(a:mem(A),b:mem(B))”
            “Holds(R1:A~>B,a,b)” 
in
val R_EXT = prove_store("R_EXT",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 strip_assume_tac l >>
 qsuff_tac ‘R1 = R & R2= R’ >-- (strip_tac >> arw[]) >> 
 strip_tac >> first_x_assum irule >> arw[]
 )
(form_goal
“!A B R1:A~>B R2. (!a b.Holds(R1,a,b) <=> Holds(R2,a,b)) <=> R1= R2”));
end


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


local 
val lemma = 
    AX1 |> qspecl [‘A’,‘1’]
        |> fVar_sInst_th “P(a:mem(A),b:mem(1))”
           “a = a:mem(A)” 
        |> uex_expand
in
val Thm_2_3_5 = prove_store("Thm_2_3_5",
e0
(strip_tac >> rw[uex_def “?!f:A~>1.isFun(f)”] >> 
 strip_assume_tac lemma >> qexists_tac ‘R’ >> rw[Fun_def] >> strip_tac (* 2 *)
 >-- (strip_tac >> rw[uex_def “?!y:mem(1).Holds(R,x,y)”] >>
      qexists_tac ‘dot’ >> once_rw[dot_def] >>
      arw[] >> strip_tac >> rw[]) >>
 strip_tac >> strip_tac >> rw[R_EXT] >> first_x_assum irule >>
 strip_tac >> first_x_assum (qspecl_then [‘a’] assume_tac) >>
 pop_assum (strip_assume_tac o uex_expand) >>
 pop_assum (K all_tac) >> pop_assum mp_tac >> once_rw[dot_def] >>
 rpt strip_tac >> arw[])
(form_goal
“!A.?!f:A~>1. isFun(f)”));
end

val asR_eq_eq = prove_store("asR_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >>
 irule $ iffLR FUN_EXT >> 
 drule $ iffRL R_EXT >> fs[asR_def])
(form_goal “!A B f1:A->B f2. asR(f1) = asR(f2) <=> f1 = f2”));

val To1_ex = prove_store("To1_ex",
e0
(strip_tac >> uex_tac >> 
 qspecl_then [‘A’] (strip_assume_tac o uex_expand) Thm_2_3_5 >>
 first_x_assum drule >>
 drule rel2fun >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f'’ >> rw[] >> strip_tac >>
 x_choose_then "f1" strip_assume_tac 
 (Thm_2_3_5 |> qspecl [‘A’] |> uex_expand) >>
 qsuff_tac ‘asR(f'') = asR(f')’ 
 >-- rw[asR_eq_eq] >>
 qsuff_tac ‘asR(f'') = f1 & asR(f') = f1’ 
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> rw[asR_Fun])
(form_goal “!A. ?!f:A ->1. T”));


 
val To1_def = SKOLEM (To1_ex |> spec_all |> uex2ex_rule) 
                     "To1" [dest_var $ rastt "A"] 
                     (To1_ex |> spec_all |> uex_expand)
                     |> rewr_rule []


val Thm_2_4_R_ver = prove_store("Thm_2_4_R_ver",
e0
(rpt strip_tac >> qspecl_then [‘1’,‘A’,‘R’] strip_assume_tac AX2 >>
 qexistsl_tac [‘TR’,‘q’] >>
 once_arw[] >> strip_tac (* 2 *)
 >-- (rw[Inj_def] >> arw[] >> rpt strip_tac >> first_x_assum irule >>
      arw[] >> once_rw[dot_def] >> rw[]) >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘r’ >> arw[]) >>
 qexists_tac ‘b’ >> arw[] >> once_rw[dot_def] >> rw[])
(form_goal
“!A R:1 ~> A.?B i:B->A. Inj(i) & !a:mem(A).Holds(R,dot,a) <=> ?b. a = App(i,b)”));


local
val l0 = 
    AX1 |> qspecl [‘1’,‘A’]
        |> fVar_sInst_th “P(a:mem(1),b:mem(A))”
           “a = a:mem(1) & P(b:mem(A))” 
        |> gen_all
val uth = uex_def “?!R:1~>A. !a. Holds(R, dot, a) <=> P(a)”
in
val Rel_Pred1 = proved_th $
e0
(assume_tac l0 >> strip_tac >>
 first_x_assum (qspecl_then [‘A’] assume_tac) >>
 first_assum (fn th => assume_tac (uex_def $ concl th)) >> fs[] >>
 rw[uth] >> qexists_tac ‘R’ >> once_arw[] >> rw[] >> 
 rpt strip_tac >> first_x_assum irule >> once_rw[dot_def] >> arw[] >>
 rpt strip_tac >> rw[])
(form_goal
“!A. ?!R:1~>A.!a:mem(A). Holds(R,dot,a) <=> P(a)”)
end

local
val lemma = mp (uex_ex (concl $ spec_all Rel_Pred1)) (spec_all Rel_Pred1) 
in
val Thm_2_4 = proved_th $
e0
(assume_tac Thm_2_4_R_ver >> strip_tac >>
 strip_assume_tac lemma >>
 first_x_assum (qspecl_then [‘A’,‘R’] strip_assume_tac) >>
 qexistsl_tac [‘B’,‘i’] >> once_arw[] >> fs[])
(form_goal
“!A.?B i:B->A. Inj(i) & !a:mem(A).P(a) <=> ?b. a = App(i,b)”)
end

val Tab_App_Rel = prove_store("Tab_App_Rel",
e0
(rpt strip_tac >> fs[Tab_def] >>
 qexists_tac ‘r’ >> arw[])
(form_goal
“!A B R:A~>B TR p:TR->A q:TR->B.isTab(R,p,q) ==>
 (!r x y. App(p,r) = x & App(q,r) = y ==> Holds(R,x,y))”)); 

val Tab_mem_R = prove_store("Tab_mem_R",
e0
(rpt strip_tac >> fs[Tab_def] >>
 qexists_tac ‘r’ >> rw[])
(form_goal
 “!A B R:A~>B TR p q. isTab(R,p:TR->A,q) ==> 
 !r:mem(TR). Holds(R,App(p,r),App(q,r))”)); 

val Tab_prop1 = prove_store("Tab_prop1",
e0
(rpt strip_tac >> fs[Tab_def])
(form_goal 
“!A B R:A~>B TR p:TR->A q:TR->B.
 isTab(R,p,q) ==> 
 (!x y. Holds(R,x,y) <=> ?r:mem(TR).App(p,r) = x & App(q,r) = y)”)); 


val Tab_prop2 = proved_th $
e0
(rpt strip_tac >> fs[Tab_def] >> first_x_assum irule >> arw[])
(form_goal 
“!A B R:A~>B TR p:TR->A q:TR->B.
 isTab(R,p,q) ==> 
 (!r s. App(p,r) = App(p,s) & App(q,r) = App(q,s) ==> r = s)”)

local
val lemma =
    AX1 |> qspecl [‘T1’,‘T2’] 
        |> fVar_sInst_th “P(a:mem(T1),b:mem(T2))”
           “App(p1:T1->A,a) = App(p2:T2->A,b) & 
            App(q1:T1->B,a) = App(q2:T2->B,b)” 
val lemma' = dimp_mp_l2r lemma (uex_def $ concl lemma) 
in
val Thm_2_5 = proved_th $
e0
(rpt strip_tac >> x_choose_then "B0" strip_assume_tac lemma' >> 
 qby_tac ‘isFun(B0)’ >--
 (rw[Fun_def] >> strip_tac >>
  rw[uex_def “?!y:mem(T2).Holds(B0:T1~>T2,x,y)”] >>
  arw[] >> rev_drule Tab_mem_R >> 
  first_x_assum (qspecl_then [‘x’] assume_tac) >>
  drule Tab_prop1 >> fs[] >>
  qexists_tac ‘r’ >> arw[] >> drule Tab_prop2 >>
  rpt strip_tac >> first_x_assum irule >> arw[]) >>
 drule rel2fun >>
 pop_assum (strip_assume_tac o uex_expand) >> 
 qexists_tac ‘f’ >> rw[Bij_def] >> 
 rw[Inj_def,Surj_def] >> arw[] >> strip_tac (* 2 *)
 >-- (rev_drule Tab_prop2 >> rpt strip_tac >> first_x_assum irule >>
      first_assum (qspecl_then [‘x1’,‘App(f,x1)’] assume_tac) >>
      first_x_assum (qspecl_then [‘x2’,‘App(f,x2)’] assume_tac) >>
      first_assum (qspecl_then [‘x1’,‘App(f,x1)’] assume_tac) >> 
      first_assum (qspecl_then [‘x2’,‘App(f,x2)’] assume_tac) >> 
      fs[]) >>
 (*Surj*)
 strip_tac >> 
 fconv_tac (once_depth_fconv no_conv (rewr_fconv (eq_sym "mem"))) >>
 drule Tab_mem_R >> first_x_assum (qspecl_then [‘b’] assume_tac) >>
 rev_drule Tab_prop1 >> fs[] >>
 qexists_tac ‘r’ >> arw[])
(form_goal
“!A B R:A~>B T1 p1:T1->A q1:T1->B T2 p2:T2->A q2:T2->B.
 isTab(R,p1,q1) & isTab(R,p2,q2) ==> ?b:T1->T2. Bij(b)”)
end

val _ = new_fun "@" (rel_sort (mk_set "A") (mk_set "C"),
                     [("phi",rel_sort (mk_set "B") (mk_set "C")),
                      ("psi",rel_sort (mk_set "A") (mk_set "B"))])

val ao_def = store_ax("ao_def",
“!A B phi:A~>B C psi:B~>C a:mem(A) c:mem(C). 
(?b. Holds(phi,a,b) & Holds(psi,b,c)) <=> Holds(psi @ phi,a,c)”);

val _ = new_fun "id" (rel_sort (mk_set "A") (mk_set "A"),
                     [("A",set_sort)])

val id_def = store_ax("id_def",“!A a:mem(A) b. Holds(id(A),a,b) <=> a = b”);

val id_Fun = prove_store("id_Fun",
e0
(strip_tac >> rw[Fun_expand,id_def] >> flip_tac >> rpt strip_tac
 >-- (qexists_tac ‘a’ >> rw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A. isFun(id(A))”));


val idL = prove_store("idL",
e0
(rpt strip_tac >> irule $ iffLR R_EXT >> 
 rw[GSYM ao_def,id_def] >> rpt strip_tac >> dimp_tac >> strip_tac
 >-- fs[] >> qexists_tac ‘b’ >> arw[])
(form_goal
 “!A B f:A~>B. id(B) @ f = f”));


val idR = prove_store("idR",
e0
(rpt strip_tac >> irule $ iffLR R_EXT >> 
 rw[GSYM ao_def,id_def] >> rpt strip_tac >> dimp_tac >> strip_tac
 >-- fs[] >> qexists_tac ‘a’ >> arw[])
(form_goal
 “!A B f:A~>B. f @ id(A) = f”));
 

val Id_ex = prove_store("Id_ex",
e0
(strip_tac >>
 qspecl_then [‘A’] assume_tac id_Fun >>
 drule rel2fun >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f’  >> arw[id_def])
(form_goal “!A. ?i:A ->A. (!a.App(i,a) = a)”));

val Id_def = qSKOLEM "Id" [‘A’] (Id_ex|> spec_all) 
                     |> gen_all |> store_as "Id_def";

val App_Id = Id_def |> store_as "App_Id";

val Thm_2_7_assoc = proved_th $
e0
(rpt strip_tac >> once_rw[GSYM R_EXT] >> rw[GSYM ao_def] >> rpt strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘b''’ >> arw[] >> qexists_tac ‘b'’ >> arw[]) >>
 qexists_tac ‘b''’ >> arw[] >> qexists_tac ‘b'’ >> arw[])
(form_goal
“!A B phi:A~>B C psi:B~>C D chi:C~>D. (chi @ psi) @ phi = chi @ psi @ phi”)

val Thm_2_7_id = proved_th $
e0
(rpt strip_tac >> rw[GSYM R_EXT] >> rpt strip_tac  (* 2 *)
 >-- (rw[GSYM ao_def,id_def] >> dimp_tac >> rpt strip_tac
      >-- arw[] >> qexists_tac ‘a’ >> arw[]) >>
 rw[GSYM ao_def,id_def] >> dimp_tac >> rpt strip_tac 
 >-- fs[] >> qexists_tac ‘b’ >> arw[])
(form_goal
“!A B phi:A~>B. phi @ id(A) = phi & id(B) @ phi = phi”)

val _ = new_fun "op" (rel_sort (mk_set "B") (mk_set "A"),[("R",rel_sort (mk_set "A") (mk_set "B"))])

val op_def = store_ax("op_def",“!A B R:A~>B a b.Holds(op(R),a,b) <=> Holds(R,b,a)”);


val Thm_2_7_ao_Fun = prove_store("Thm_2_7_ao_Fun",
e0
(rpt strip_tac >> fs[Fun_expand,GSYM ao_def] >> rpt strip_tac (* 2 *)
 >-- (last_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
      last_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
      qexistsl_tac [‘b'’,‘b’] >> arw[]) >>
 first_x_assum irule >> 
 qby_tac ‘b' = b’ >--
 (first_x_assum irule >> qexistsl_tac [‘a’] >> arw[]) >>
 fs[] >> qexists_tac ‘b’ >> arw[])
(form_goal
 “!A B f:A~>B C g:B~>C. isFun(f) & isFun(g) ==> isFun(g @ f)”));

val ao_Fun = Thm_2_7_ao_Fun |> store_as "ao_Fun";  


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

val o_def = qSKOLEM "o" [‘psi:B->C’,‘phi:A->B’] 
                        (o_ex |> spec_all)
                        |> gen_all |> store_as "o_def";


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
 ?f':B->A. asR(f') = op(asR(f))”))


val App_App_o = prove_store("App_App_o",
e0
(rw[o_def,GSYM ao_def,asR_def] >> rpt strip_tac >>
 qexists_tac ‘App(f,a)’ >> arw[])
(form_goal “!A B f:A->B C g:B->C a. 
  App(g o f,a) = App(g,App(f,a))”));

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

(*val _ = new_fun "*" (set_sort,[("A",set_sort),("B",set_sort)]) *)
(*
For sets A and B, let ⊤:A↬B denote the relation such that ⊤(x,y) holds always. A tabulation of ⊤ is denoted A×B; it is a set equipped with functions p:A×B→A and q:A×B→B such that for any x∈A and y∈B, there exists a unique z∈A×B with p(z)=x and q(z)=y. It is called the cartesian product of A and B.
Theorem 2.8. For any sets A and B, A×B is a product of A and B in the category Set, and a coproduct in the category Rel.
*)

local 
val lemma = 
    AX1 |> qspecl [‘A’,‘B’]
        |> fVar_sInst_th “P(a:mem(A),b:mem(B))”
           “T”
in
val T_uex = dimp_mp_l2r lemma (uex_def $ concl lemma)
                        |> rewr_rule []
                        |> gen_all
end

val T_ex = prove_store("T_ex",
e0
(assume_tac T_uex >> 
 rpt strip_tac >> 
 first_x_assum (qspecl_then [‘A’,‘B’] strip_assume_tac) >>
 qexists_tac ‘R’ >> arw[] >> rpt strip_tac >> rw[])
(form_goal
“!A B. ?T0:A~>B. !a b. Holds(T0,a,b)”));

val Cross_ex = prove_store("Cross_ex",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘B’] strip_assume_tac T_ex >>
 qspecl_then [‘A’,‘B’,‘T0’] strip_assume_tac AX2 >> 
 qexistsl_tac [‘TR’,‘p’,‘q’] >> fs[] >> rpt strip_tac >> rw[])
(form_goal
 “!A B. ?AxB p1:AxB ->A p2:AxB ->B.
  (!x:mem(A) y:mem(B). 
   ?r:mem(AxB).App(p1,r) = x & App(p2,r) = y) &
   !r s. App(p1,r) = App(p1,s) & App(p2,r) = App(p2,s) ==> r = s”)); 


val Cross_def = Cross_ex |> spec_all 
                         |> qSKOLEM "*" [‘A’,‘B’]
                         |> gen_all 
                         |> store_as "Cross_def"; 

val p1_def = Cross_def |> spec_all 
                       |> qSKOLEM "p1" [‘A’,‘B’]
                       |> gen_all 
                       |> store_as "p1_def";

val p2_def = p1_def |> spec_all 
                    |> qSKOLEM "p2" [‘A’,‘B’]
                    |> gen_all 
                    |> store_as "p2_def";

val _ = new_pred "SetPr" [("p1",rel_sort (mk_set "AxB") (mk_set "A")),
                            ("p2",rel_sort (mk_set "AxB") (mk_set "B"))]

                 
val SetPr_def = 
    qdefine_psym ("SetPr",[‘p1:AB->A’,‘p2:AB->B’])
                 ‘!X f:X->A g:X->B.?!fg: X->AB. p1 o fg = f & p2 o fg = g’ 
                                                                  |> gen_all
    |> store_as "SetPr_def";

fun Cross A B = mk_fun "*" [A,B]


val Thm_2_8_SetPr = proved_th $
e0
(rpt strip_tac >> rw[SetPr_def] >> rpt strip_tac >>
 rw[uex_def “?!fg:X-> A * B.p1(A,B) o fg = f & p2(A,B) o fg = g”] >>
 strip_assume_tac $
 uex_expand $ 
 fVar_Inst_th 
 ("P",([("x",mem_sort (mk_set "X")),
        ("ab",mem_sort (Cross (mk_set"A") (mk_set "B")))],
  “App(p1(A,B),ab) = App(f:X->A,x) & 
   App(p2(A,B),ab) = App(g:X->B,x)”))
 (AX1 |> qspecl [‘X’,‘A * B’]) >>
 qspecl_then [‘A’,‘B’] strip_assume_tac p2_def >>
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> 
  rpt strip_tac (* 2 *) >-- 
  (first_x_assum (qspecl_then [‘App(f,a)’,‘App(g,a)’] assume_tac) >>
   arw[]) >>
  first_x_assum irule >> arw[]) >> arw[] >>
 drule rel2fun >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum $ x_choose_then "R1" strip_assume_tac >> 
 qexists_tac ‘R1’ >>
 qby_tac ‘p1(A, B) o R1 = f & p2(A, B) o R1 = g’ >--
 (arw[GSYM FUN_EXT,o_def] >> rpt strip_tac (* 2 *) 
  >-- (rw[GSYM ao_def,asR_def] >>
      arw[] >> 
      last_x_assum 
      (qspecl_then [‘App(f,a)’,‘App(g,a)’] strip_assume_tac)>>
      qexists_tac ‘r’ >> arw[]) >>
  rw[GSYM ao_def,asR_def] >>
  arw[] >> 
  last_x_assum 
  (qspecl_then [‘App(f,a)’,‘App(g,a)’] strip_assume_tac)>>
  qexists_tac ‘r’ >> arw[]) >> arw[] 
 (*last subgoal*)
 >>
 rpt strip_tac >> first_x_assum irule >> 
 rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (arw[] >> pop_assum (assume_tac o GSYM) >>
     once_arw[] >> arw[GSYM App_App_o]) >>
 first_x_assum irule >> arw[] >> rfs[] >>
 arw[GSYM App_App_o])
(form_goal
“!A B. SetPr(p1(A,B),p2(A,B))”)


val Pa_def =
    Thm_2_8_SetPr |> rewr_rule[SetPr_def]
                  |> spec_all |> uex_expand
                  |> qSKOLEM "Pa" [‘f’,‘g’]
                  |> gen_all
                  |> store_as "Pa_def";

val p12_of_Pa = Pa_def |> spec_all |> conjE1 
                       |> qgen ‘g’ |> qgen ‘B’ |> gen_all
                       |> store_as "p12_of_Pa";

val p1_of_Pa = p12_of_Pa |> spec_all |> conjE1
                         |> gen_all 
                         |> store_as "p1_of_Pa";

val p2_of_Pa = p12_of_Pa |> spec_all |> conjE2
                         |> gen_all
                         |> store_as "p2_of_Pa";

val is_Pa = Pa_def |> spec_all |> conjE2 
                   |> qgen ‘g’ |> qgen ‘B’ |> gen_all
                   |> store_as "p12_of_Pa";
 


val _ = new_pred "SetEz" [("f",rel_sort (mk_set "A") (mk_set "B")),
                           ("g",rel_sort (mk_set "A") (mk_set "B")),
                           ("e",rel_sort (mk_set "E") (mk_set "A"))]

(*thesetting is considering two categories at the same time, any thing to do for that?, below is ugly, have not tested if some of e or x0 is a function can be proved rather than stated*)

val SetEz_def = 
    qdefine_psym ("SetEz",[‘f:A->B’,‘g:A->B’,‘e:E->A’])
    ‘!X x:X->A.f o x = g o x ==> ?!x0:X->E. x = e o x0’



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
 
local
val lemma =
    Thm_2_4|> qspecl [‘A’]
           |> fVar_sInst_th “P(a:mem(A))”
              “App(f:A->X,a) = App(g,a)” 
           |> gen_all 
val lemma1 = 
    AX1 |> qspecl [‘X’,‘E’]
        |> fVar_sInst_th “P(a0:mem(X),a0':mem(E))”
           “App(e:E->A,a0') = App(x:X->A,a0)” 
        |> uex_expand
in
val Thm_2_9_Eqlz = proved_th $
e0
(rpt strip_tac >> rw[SetEz_def] >>
 qspecl_then [‘A’,‘B’,‘f’,‘g’]
  (x_choosel_then ["E","e"] strip_assume_tac) lemma >>
 qexistsl_tac [‘E’,‘e’] >> arw[] >> 
 rpt strip_tac >> uex_tac >> 
 strip_assume_tac lemma1 >>
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> rpt strip_tac >--
  (flip_tac >>
  last_x_assum $ assume_tac o iffLR >>
  first_x_assum irule >> arw[GSYM App_App_o]) >>
  fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 drule rel2fun >> pop_assum (assume_tac o uex_expand) >>
 pop_assum (x_choose_then "R1" strip_assume_tac) >>
 qby_tac ‘x = e o R1’ >--
 (rw[GSYM FUN_EXT] >> strip_tac >>
  first_x_assum (qspecl_then [‘a’,‘App(R1,a)’] assume_tac) >>
  rfs[GSYM App_App_o]) >> 
 qexists_tac ‘R1’ >> arw[] >> rpt strip_tac >>
 drule Inj_lcancel >> first_x_assum irule >> arw[])
(form_goal
“!A B f:A->B g:A->B.?E e:E->A.SetEz(f,g,e)”)
end


local
val lemma =
    Thm_2_4 |> qspecl [‘B’]
            |> fVar_sInst_th “P(b:mem(B))”
               “?a:mem(A).App(f:A->B,a) = b” 
val lemma1 = 
    AX1 |> qspecl [‘A’,‘s’] 
        |> fVar_sInst_th “P(x:mem(A),y:mem(s))”
           “App(f:A->B,x) = App(m:s->B,y)”
        |> uex_expand
in
val Thm_2_10 = proved_th $
e0
(rpt strip_tac >> 
 x_choosel_then ["s","m"] strip_assume_tac lemma >>
 x_choose_then "e" strip_assume_tac lemma1 >>
 qby_tac ‘isFun(e)’ >--
 (rw[Fun_expand] >> arw[] >> rpt strip_tac (* 2 *)
  >-- (last_x_assum $ irule o iffLR >> qexists_tac ‘a’ >> rw[]) >>
  fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 drule rel2fun >> 
 pop_assum (assume_tac o uex_expand) >>
 pop_assum (x_choose_then "e1" strip_assume_tac) >>
 qexistsl_tac [‘s’,‘e1’,‘m’] >> 
 arw[] >>
 qby_tac ‘Surj(e1)’ 
 >-- (arw[Surj_def] >> strip_tac >> qexists_tac ‘b’ >> rw[])>>
 arw[] >>
 rw[GSYM FUN_EXT] >> strip_tac >>
 last_x_assum (qspecl_then [‘a’,‘App(e1,a)’] assume_tac) >>
 fs[GSYM App_App_o] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 qpick_x_assum ‘!a b.App(e1,a) = b <=> Holds(e,a,b)’
 (assume_tac o GSYM) >>
 arw[])
(form_goal
“!A B f:A->B.?M e:A->M m:M->B. f = m o e & Surj(e) & Inj(m)”)
end

val AX3 = store_ax("AX3",
“!A. ?PA e:A~>PA. !S0:1~>A.?!s:mem(PA). !x:mem(A). Holds(S0,dot,x) <=> 
 Holds(e,x,s)”)



(*
Theorem 2.12. For any relation R:B↬A, there exists a unique function fR:B→PA such that R(y,x) if and only if ϵ(x,fR(y)). It follows that Set is a topos (and Rel is a power allegory).
*)

val Pow_def = AX3 |> spec_all
                  |> qSKOLEM "Pow" [‘A’] 
                  |> gen_all |> store_as "Pow_def"; 

fun Pow A = mk_fun "Pow" [A]

val In_def = 
    Pow_def |> spec_all
            |> qSKOLEM "In" [‘A’] 
            |> gen_all |> store_as "In_def"; 

(*base change*)
val BC0_def = 
    AX1 |> qspecl [‘Pow(Y)’,‘Pow(Z)’]
        |> fVar_sInst_th
           “P(ys:mem(Pow(Y)),zs:mem(Pow(Z)))”
           “!z:mem(Z). Holds(In(Z),z,zs) <=> Holds(In(Y),App(f,z),ys)”
        |> uex_expand
        |> qSKOLEM "BC0" [‘f’] |> gen_all
        |> store_as "BC0_def";


local 
val lemma = 
fVar_Inst_th 
("P",([("star",mem_sort ONE),("a",mem_sort (mk_set "A"))],
“(?a0. a = App(s0:A0->A,a0))”))
(AX1|> qspecl [‘1’,‘A’]) 
|> uex_expand 
in
val In_def_Inj = prove_store("In_def_Inj",
e0
(rpt strip_tac >> assume_tac In_def >>
 strip_assume_tac lemma >>
 first_x_assum (qspecl_then [‘A’,‘R’] $ strip_assume_tac o uex_expand) >>
 uex_tac >>
 qexists_tac ‘s’ >> 
 qpick_x_assum ‘!a b. Holds(R,a,b) <=> ?a0.b = App(s0,a0)’
 (mp_tac o GSYM) >> once_rw[dot_def] >> strip_tac >>
 first_x_assum (qspecl_then [‘dot’] assume_tac) >> arw[] >>
 rfs[]
 )
(form_goal
“!A A0 s0:A0->A.
 ?!s:mem(Pow(A)).!x:mem(A). (?a0.x = App(s0,a0)) <=> Holds(In(A),x,s)”));
end
 
local
val lemma = 
fVar_Inst_th 
("P",([("a",mem_sort (mk_set "A"))],
“(?a0. a = App(s0:A0->A,a0))”))
(Thm_2_4 |> qspecl [‘A’]) 
in
val In_def_P = prove_store("In_def_P",
e0
(strip_tac >> uex_tac >> 
 strip_assume_tac $ spec_all Thm_2_4 >>
 (strip_assume_tac o uex_expand) 
 (In_def_Inj |> qsspecl [‘i:B->A’]) >>
 qexists_tac ‘s’ >> strip_tac (* 2 *) >--
 (strip_tac >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 arw[]) >>
 rpt strip_tac >> first_x_assum irule >>
 strip_tac >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
 last_x_assum (qspecl_then [‘x’] assume_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A.?!s:mem(Pow(A)).!a.P(a) <=> Holds(In(A),a,s)”));
end



local
val lemma = 
fVar_Inst_th
("P",([("a",mem_sort (mk_set "A"))],
“Holds(In(A),a,s1)”))
(In_def_P|> qspecl [‘A’]) |> uex_expand
in
val In_EXT = prove_store("In_EXT",
e0
(rpt strip_tac >> strip_assume_tac lemma >>
 qsuff_tac ‘s1 = s & s2 = s’ >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> rpt strip_tac (*2  *)
 >-- rw[] >> pop_assum (K all_tac) >> arw[])
(form_goal
 “!A s1:mem(Pow(A)) s2. (!x.Holds(In(A),x,s1) <=> Holds(In(A),x,s2)) ==>
 s1 = s2”));
end

local
val lemma = 
fVar_Inst_th 
("P",([("z",mem_sort (mk_set "Z"))],
“Holds(In(Y), App(f:Z->Y, z), a)”))
(In_def_P |> qspecl [‘Z’]) 
|> uex_expand
in
val BC0_isFun = prove_store("BC0_isFun",
e0
(rpt strip_tac >> 
 qspecl_then [‘Y’,‘Z’,‘f’] strip_assume_tac BC0_def >>
 rw[Fun_expand] >> arw[] >> strip_tac (* 2 *) >--
 (strip_tac >> strip_assume_tac lemma >> qexists_tac ‘s’ >>
 strip_tac >> first_x_assum (qspecl_then [‘z’] assume_tac) >> arw[]) >>
 rpt strip_tac >> irule In_EXT >> arw[] >> strip_tac >> rw[])
(form_goal “!Z Y f:Z->Y.isFun(BC0(f))”));
end

(*TODO: show BC is a functor Pow(B) ~>Pow (A)*)


val Ex0_def = 
fVar_Inst_th 
("P",([("zs",mem_sort (Pow (mk_set "Z"))),("ys",mem_sort (Pow (mk_set "Y")))],
“!y:mem(Y). Holds(In(Y),y,ys) <=> ?z:mem(Z).Holds(In(Z),z,zs) & App(f,z) = y”))
(AX1|> qspecl [‘Pow(Z)’,‘Pow(Y)’]) 
|> uex_expand |> qSKOLEM "Ex0" [‘f’] |> gen_all



val All0_def = 
fVar_Inst_th 
("P",([("zs",mem_sort (Pow (mk_set "Z"))),("ys",mem_sort (Pow (mk_set "Y")))],
“!y:mem(Y). Holds(In(Y),y,ys) <=> !z:mem(Z). App(f,z) = y ==> Holds(In(Z),z,zs) ”))
(AX1|> qspecl [‘Pow(Z)’,‘Pow(Y)’]) 
|> uex_expand |> qSKOLEM "All0" [‘f’] |> gen_all


local
val lemma = 
fVar_Inst_th 
("P",([("y",mem_sort (mk_set "Y"))],
“?z:mem(Z).Holds(In(Z),z,a) & App(f:Z->Y,z) = y”))
(In_def_P |> qspecl [‘Y’]) 
|> uex_expand
in
val Ex0_isFun = proved_th $
e0
(rpt strip_tac >> rw[Fun_expand] >> strip_tac (* 2 *) >-- 
 (strip_tac >> 
  qspecl_then [‘Y’,‘Z’,‘f’] strip_assume_tac Ex0_def >>
  arw[] >> x_choose_then "b" strip_assume_tac lemma >> 
  qexists_tac ‘b’ >> strip_tac >> arw[]) >>
 rpt strip_tac >> irule In_EXT >> strip_tac >>
  qspecl_then [‘Y’,‘Z’,‘f’] strip_assume_tac Ex0_def >> fs[])
(form_goal 
“!Z Y f:Z->Y.isFun(Ex0(f))”)
end


local
val lemma = 
fVar_Inst_th
("P",([("y",mem_sort (mk_set "Y"))],
“!z:mem(Z). App(f:Z->Y,z) = y ==> Holds(In(Z),z,a)”))
(In_def_P |> qspecl [‘Y’]) 
|> uex_expand
in
val All0_isFun = prove_store("All0_isFun",
e0
(rpt strip_tac >> rw[Fun_expand] >> strip_tac (* 2 *) >-- 
 (strip_tac >> 
  qspecl_then [‘Y’,‘Z’,‘f’] strip_assume_tac All0_def >>
  arw[] >> 
  x_choose_then "b" strip_assume_tac lemma >> 
  qexists_tac ‘b’ >> strip_tac >> arw[]) >>
 rpt strip_tac >> irule In_EXT >> strip_tac >>
  qspecl_then [‘Y’,‘Z’,‘f’] strip_assume_tac All0_def >> fs[])
(form_goal 
“!Z Y f:Z->Y.isFun(All0(f))”));
end


(*poset order of P(A)*)
val _ = new_pred "PO" [("S1",mem_sort (Pow (mk_set "A"))),
                       ("S2",mem_sort (Pow (mk_set "A")))]

val PO_def = qdefine_psym ("PO",[‘S1:mem(Pow(A))’,
                                 ‘S2:mem(Pow(A))’])
‘!a. Holds(In(A),a,S1) ==> Holds(In(A),a,S2)’ 
|> gen_all |> store_as "PO_def";
 

val BC_def = rel2fun |> qsspecl [‘BC0(f:Z->Y)’]
                     |> C mp (BC0_isFun|>qsspecl [‘f:Z->Y’])
                     |> uex2ex_rule 
                     |> qSKOLEM "BC" [‘f’] 
                     |> gen_all
                     |> store_as "BC_def";

val In_App_BC = prove_store("In_App_BC",
e0
(rpt strip_tac >> 
 qspecl_then [‘Y’,‘Z’,‘f’] assume_tac BC_def >>
 qspecl_then [‘Y’,‘Z’,‘f’] (assume_tac o conjE1) BC0_def >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum $ irule o iffLR o iffLR >>
     qexists_tac ‘App(BC(f),ys)’ >> arw[] >>
     first_x_assum $ irule o iffLR >> rw[]) >>
 first_x_assum $ irule o iffRL o iffLR >>
 qexists_tac ‘ys’ >> arw[] >>
 first_x_assum $ irule o iffLR >> rw[])
(form_goal
 “!Z Y f:Z->Y z ys.Holds(In(Z),z,App(BC(f),ys)) <=> 
 Holds(In(Y),App(f,z),ys) ”)); 


val Ex_def = rel2fun |> qsspecl [‘Ex0(f:Z->Y)’]
                     |> C mp (Ex0_isFun|>qsspecl [‘f:Z->Y’])
                     |> uex2ex_rule 
                     |> qSKOLEM "Ex" [‘f’] 
                     |> gen_all
                     |> store_as "Ex_def";


val In_App_Ex = prove_store("In_App_Ex",
e0
(rpt strip_tac >> 
 qspecl_then [‘Y’,‘Z’,‘f’] (assume_tac o conjE1) Ex0_def >> 
 qspecl_then [‘Y’,‘Z’,‘f’] assume_tac Ex_def >>
 dimp_tac >> strip_tac (* 2 *) >--
 (first_x_assum $ irule o iffLR o iffLR >> 
  qexists_tac ‘App(Ex(f),zs)’ >> arw[] >>
  first_x_assum $ irule o iffLR >> rw[]) >>
 first_x_assum $ irule o iffRL o iffLR >> qexists_tac ‘zs’ >> strip_tac (* 2 *)
 >-- (qexists_tac ‘z’ >> arw[]) >> 
 first_x_assum $ irule o iffLR >> rw[])
(form_goal
 “!Z Y f:Z->Y y zs. Holds(In(Y),y,App(Ex(f),zs)) <=> 
   ?z:mem(Z).Holds(In(Z),z,zs) & App(f,z) = y”)); 




val All_def = rel2fun |> qsspecl [‘All0(f:Z->Y)’]
                     |> C mp (All0_isFun|>qsspecl [‘f:Z->Y’])
                     |> uex2ex_rule 
                     |> qSKOLEM "All" [‘f’] 
                     |> gen_all
                     |> store_as "All_def";
 
val In_App_All = prove_store("In_App_All",
e0
(rpt strip_tac >> 
 qspecl_then [‘Y’,‘Z’,‘f’] (assume_tac o conjE1) All0_def >> 
 qspecl_then [‘Y’,‘Z’,‘f’] assume_tac All_def >> 
 dimp_tac >> strip_tac (* 2 *) >--
 (rpt strip_tac >> 
 first_x_assum $ irule o iffLR o iffLR >> 
 qexistsl_tac [‘App(All(f),zs)’,‘y’] >> arw[] >> 
 last_x_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum $ irule o iffRL o iffLR >> 
 qexists_tac ‘zs’ >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> first_x_assum drule >> arw[]) >> 
 last_x_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!Z Y f:Z->Y y zs. Holds(In(Y),y,App(All(f),zs)) <=> 
   !z:mem(Z).App(f,z) = y ==> Holds(In(Z),z,zs)”));




 
val Thm_2_11_SEx_ex = prove_store("Thm_2_11_SEx_ex",
e0
(rpt strip_tac >> rw[PO_def] >> 
 qby_tac ‘!z.Holds(In(Z),z,App(BC(f),ys)) <=> 
             Holds(In(Y),App(f,z),ys)’
 >-- (rw[In_App_BC] >> strip_tac >> rw[]) >> arw[] >> 
 qby_tac ‘!y. Holds(In(Y),y,App(Ex(f),zs)) <=> 
   ?z:mem(Z).Holds(In(Z),z,zs) & App(f,z) = y’ 
 >-- (rw[In_App_Ex] >> strip_tac >> rw[]) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> first_x_assum irule >> qexists_tac ‘a’ >> arw[]) >>
 rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
 first_x_assum irule>> arw[])
(form_goal
 “!Z Y f:Z->Y. 
  !zs:mem(Pow(Z)) ys:mem(Pow(Y)).
  (PO(App(Ex(f),zs),ys) <=> PO(zs,App(BC(f),ys)))”)); 

val Thm_2_11_SAll_ex = prove_store("Thm_2_11_SAll_ex",
e0
(rpt strip_tac >> rw[PO_def,In_App_BC,In_App_All] >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> first_x_assum irule >> 
      qsuff_tac ‘App(f,z) = a’ >-- (strip_tac >> fs[]) >> 
      arw[]) >>
 rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
 first_x_assum irule >> qexists_tac ‘App(f,a)’ >> arw[])
(form_goal
 “!Z Y f:Z->Y.
  !ys:mem(Pow(Y)) zs:mem(Pow(Z)). PO(App(BC(f),ys),zs) <=> PO(ys,App(All(f),zs))”)); 




val op_DISTR = prove_store("op_DISTR",
e0
(rpt strip_tac >> 
 rw[GSYM R_EXT,op_def,GSYM ao_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac (*2 *) >--
 (qexists_tac ‘b'’ >> arw[]) >>
 qexists_tac ‘b'’ >> arw[])
(form_goal
“!A B phi:A~>B C psi:B~>C. op(psi @ phi) = op(phi) @ op(psi)”));

(*
If x and y are elements of a poset, then their meet is an element x∧y of the poset such that:

x∧y≤x and x∧y≤y;
if a≤x and a≤y, then a≤x∧y.
*)


val Sub_def = qdefine_psym ("Sub",[‘R1:A~>B’,‘R2:A~>B’])
              ‘!a b. Holds(R1,a,b) ==> Holds(R2,a,b)’
              |> gen_all |> store_as "Sub_def";

local 
val lemma = 
fVar_Inst_th
("P",([("a",mem_sort (mk_set "A")),
        ("b",mem_sort (mk_set "B"))],
“Holds(R1:A~>B,a,b) & Holds(R2:A~>B,a,b)”))
(AX1 |> qspecl [‘A’,‘B’]) |> uex_expand
in
val Meet_ex = prove_store("Meet_ex",
e0
(rpt strip_tac >> strip_assume_tac lemma >> 
 qexists_tac ‘R’ >> arw[] >> rpt strip_tac >> rw[])
(form_goal 
 “!A B R1:A~>B R2:A~>B. ?M:A~>B. !a b. Holds(M,a,b) <=> Holds(R1,a,b) & Holds(R2,a,b)”));
end


val Meet_def = Meet_ex |> spec_all
                       |> qSKOLEM "Meet" [‘R1’,‘R2’] 
                       |> gen_all 
                       |> store_as "Meet_def"; 

val Sub_Meet = prove_store("Sub_Meet",
e0
(rpt strip_tac >> fs[Meet_def,Sub_def] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal
“!A B R1:A~>B R2:A~>B. Sub(Meet(R1,R2),R1) & Sub(Meet(R1,R2),R2) &
 !R0. Sub(R0,R1) & Sub(R0,R2) ==> Sub(R0,Meet(R1,R2))”)); 

local 
val lemma = 
fVar_Inst_th
("P",([("a",mem_sort (mk_set "A")),
        ("b",mem_sort (mk_set "B"))],
“Holds(R1:A~>B,a,b) | Holds(R2:A~>B,a,b)”))
(AX1 |> qspecl [‘A’,‘B’]) |> uex_expand
in
val Join_ex = prove_store("Join_ex",
e0
(rpt strip_tac >> strip_assume_tac lemma >> 
 qexists_tac ‘R’ >> arw[] >> rpt strip_tac >> rw[])
(form_goal 
 “!A B R1:A~>B R2:A~>B. ?J:A~>B. !a b. Holds(J,a,b) <=> Holds(R1,a,b) | Holds(R2,a,b)”));
end
   

val Join_def = Join_ex |> spec_all 
                       |> qSKOLEM "Join" [‘R1’,‘R2’] 
                       |> gen_all |> store_as "Join_def";

(*
If x and y are elements of a poset P, then their join (or supremum, abbreviate sup, or least upper bound, abbreviated lub), is an element x∨y of the poset such that:

x≤x∨y and y≤x∨y;
if x≤a and y≤a, then x∨y≤a.

*) 

val Sub_Join = prove_store("Sub_Join",
e0
(rpt strip_tac >> fs[Join_def,Sub_def] >> rpt strip_tac (* 4 *)
 >-- (disj1_tac >> arw[]) >-- (disj2_tac >> arw[]) >--
 (last_x_assum irule >> arw[]) >>
  first_x_assum irule >> arw[])
(form_goal
“!A B R1:A~>B R2:A~>B. Sub(R1,Join(R1,R2)) & Sub(R2,Join(R1,R2)) &
 !R0. (Sub(R1,R0) & Sub(R2,R0)) ==> Sub(Join(R1,R2),R0)”)); 
 
(*the modular law holds: for ϕ:x→y, ψ:y→z, and χ:x→z, we have ψϕ∩χ≤ψ(ϕ∩ψoχ).*)
 
val MODULAR_LAW = prove_store("MODULAR_LAW",
e0
(rpt strip_tac >> rw[Sub_def,Meet_def,op_def,GSYM ao_def] >>
 rpt strip_tac >> qexists_tac ‘b'’ >> arw[] >>
 qexists_tac ‘b’ >> arw[])
(form_goal
 “!x y phi:x~>y z psi:y~>z chi:x~>z. 
  Sub(Meet(psi @ phi,chi),psi @ Meet(phi,op(psi) @ chi))”));

(*
A union allegory Is an allegory whose hom-posets have finite joins that are preserved by composition. Thus a union allegory is locally a lattice. If additionally it is locally a distributive lattice, it is called a distributive allegory.
*)
 
val left_o_pres_Join = prove_store("left_o_pres_Join",
e0
(rpt strip_tac >> rw[GSYM ao_def,Join_def,GSYM R_EXT] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 4 *)
 >-- (disj1_tac >> qexists_tac ‘b'’ >> arw[])
 >-- (disj2_tac >> qexists_tac ‘b'’ >> arw[])
 >-- (qexists_tac ‘b'’ >> rpt strip_tac (* 2 *)
      >-- (disj1_tac >> arw[]) >> arw[]) >>
 qexists_tac ‘b'’ >> rpt strip_tac (* 2 *)
  >-- (disj2_tac >> arw[]) >> arw[])
(form_goal
 “!A B R1:A~>B R2:A~>B C R:B~>C. R @ Join(R1,R2) = Join(R @ R1, R @ R2)”)); 

 
val right_o_pres_Join = prove_store("right_o_pres_Join",
e0
(rpt strip_tac >> rw[GSYM R_EXT,GSYM ao_def,Join_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 4 *)
 >-- (disj1_tac >> qexists_tac ‘b'’ >> arw[])
 >-- (disj2_tac >> qexists_tac ‘b'’ >> arw[])
 >-- (qexists_tac ‘b'’ >> arw[]) >>
 qexists_tac ‘b'’ >> arw[])
(form_goal
 “!A B R1:A~>B R2:A~>B R:C~>A. Join(R1,R2) @ R = Join(R1 @ R, R2 @ R)”)); 


(*
A division allegory is a distributive allegory in which composition on one (and therefore the other) side has a right adjoint (left or right division). That is: given r:A→B and s:A→C, there exists s/r:B→C such that

t≤s/r∈hom(B,C)⇔t∘r≤s∈hom(A,C)
*)
 
local 
val lemma = fVar_Inst_th
("P",([("b",mem_sort (mk_set "B")),
        ("c",mem_sort (mk_set "C"))],
“!a:mem(A). Holds(r:A~>B,a,b) ==> Holds(s:A~>C,a,c)”))
(AX1 |> qspecl [‘B’,‘C’]) |> uex_expand
in
val Div_ex = prove_store("Div_ex",
e0
(rpt strip_tac >> rw[Sub_def,GSYM ao_def] >>
 strip_assume_tac lemma >> qexists_tac ‘R’ >> 
 strip_tac >> dimp_tac (* 2 *) >--
 (rpt strip_tac >> first_x_assum $ irule o iffLR >>
  qexists_tac ‘b'’ >> arw[] >> first_x_assum irule >> arw[]) >>
 rpt strip_tac >> arw[] >> rpt strip_tac >> first_x_assum irule >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!A B r:A~>B C s:A~>C. ?sdr:B~>C. 
  !t.Sub(t,sdr) <=> Sub(t @ r,s)”));
end

(*
Theorem 2.12. For any relation R:B↬A, there exists a unique function fR:B→PA such that R(y,x) if and only if ϵ(x,fR(y)). It follows that Set is a topos (and Rel is a power allegory).
Proof. We simply define fR elementwise; for each y we define fR(y) to be the unique element of PA such that ϵ(x,fR(y)) holds iff R(y,x) holds. Extensionality of functions implies that it is unique.  ▮
*)


local
val lemma = 
fVar_Inst_th
("P",([("y",mem_sort (mk_set "B")),("s",mem_sort (Pow (mk_set "A")))],
“!x.Holds(In(A),x,s) <=> Holds(R:B~>A,y,x)”))
(AX1|> qspecl [‘B’,‘Pow(A)’]) |> uex_expand
val lemma1 = 
fVar_Inst_th 
("P",([("x",mem_sort (mk_set "A"))],
“Holds(R:B~>A,a,x)”))
(In_def_P|> qspecl [‘A’]) |> uex_expand
in
val Thm_2_12 = prove_store("Thm_2_12",
e0
(rpt strip_tac >>
 x_choose_then "fR" strip_assume_tac lemma >>
 uex_tac >> 
 qby_tac ‘isFun(fR)’ >-- 
 (arw[Fun_expand] >> rpt strip_tac (* 2 *) >--
  (strip_assume_tac lemma1 >> qexists_tac ‘s’ >> arw[] >>
   strip_tac >> rw[]) >>
  strip_assume_tac lemma1 >> 
  qsuff_tac ‘b1 = s & b2 = s’ >-- (strip_tac >> arw[]) >>
  strip_tac >> first_x_assum irule >> arw[] >> strip_tac >> rw[]) >>
 drule rel2fun >> pop_assum (assume_tac o uex_expand) >>
 pop_assum $ x_choose_then "fR1" strip_assume_tac >>
 qexists_tac ‘fR1’ >>
 qby_tac
 ‘!y x.Holds(In(A),x,App(fR1,y)) <=> Holds(R,y,x)’ 
 >-- (strip_tac >> first_x_assum (irule o iffLR) >>
     first_x_assum (irule o iffLR) >> rw[]) >>
 arw[] >> rpt strip_tac >> first_x_assum irule >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 irule In_EXT >> rfs[])
(form_goal
“!B A R:B~>A.?!fR:B->Pow(A).!y x.(Holds(R,y,x) <=> Holds(In(A),x,App(fR,y)))”));
end

 
local
val lemma =
(fVar_Inst_th ("P",([("star",mem_sort ONE),("x",mem_sort (mk_set "A"))],“x = a:mem(A)”)) (AX1 |> qspecl [‘1’,‘A’])) |> uex_expand
in
val Thm_2_3_5_el = prove_store("Thm_2_3_5_el",
e0
(rpt strip_tac >> uex_tac >>
 strip_assume_tac lemma >> 
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> once_rw[dot_def] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘a’ >> rw[]) >-- arw[]) >>
 drule rel2fun >> pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f’ >> 
 qby_tac ‘App(f,dot) = a’ >-- arw[] >>
 arw[] >>
 rpt strip_tac >> first_x_assum irule >>
 rpt strip_tac >> once_rw[dot_def] >> fs[] >>
 rflip_tac >> rw[])
(form_goal
 “!A a:mem(A). ?!R:1->A. App(R,dot) = a”));
end

(*mem as fun*)
val MF_def = Thm_2_3_5_el |> spec_all 
                          |> uex2ex_rule
                          |> qSKOLEM "MF" [‘a’] 
                          |> gen_all
                          |> store_as "MF_def";
 

(*
Theorem 2.13. For any two sets A and B, there exists a set BA and a function ev:BA×A→B such that for any function f:A→B there exists a unique element sf∈BA such that ev(sf,a)=f(a) for all a∈A. It follows that Set is a cartesian closed category.

Proof. We take BA to be a tabulation of the subset of P(A×B) containing only the functions. More precisely, define F⊆P(A×B) such that s∈F iff for every x∈A, there exists a unique y∈B such that ϵ((x,y),s), and let BA=|F|.  ▮
*)

val Pair_def = p2_def |> spec_all |> conjE1 |> spec_all 
                     |> qSKOLEM "Pair" [‘x’,‘y’] 
                     |> gen_all |> store_as "Pair_def";

val Pair_App_eq = p2_def |> spec_all |> conjE2 |> gen_all |> store_as "Pair_App_eq";

val Pair_component = prove_store("Pair_component",
e0
(rpt strip_tac >> irule Pair_App_eq >>
 rw[Pair_def])
(form_goal
 “!A B r:mem(A * B).Pair(App(p1(A,B),r),App(p2(A,B),r)) = r”));

val Pair_eq_eq = prove_store("Pair_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘App(p1(A,B),Pair(a1, b1)) = App(p1(A,B),Pair(a2, b2))’
 >-- arw[] >>
 fs[Pair_def] >>
 qby_tac ‘App(p2(A,B),Pair(a1, b1)) = App(p2(A,B),Pair(a2, b2))’
 >-- arw[] >>
 fs[Pair_def])
(form_goal
 “!A a1:mem(A) a2 B b1:mem(B) b2.Pair(a1,b1) = Pair(a2,b2) <=> (a1 = a2 & b1 = b2)”));

val Pair_p12 = prove_store("Pair_p12",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] strip_assume_tac p2_def >>
 first_x_assum irule >> rw[Pair_def])
(form_goal
 “!A B ab:mem(A * B). Pair(App(p1(A,B),ab),App(p2(A,B),ab)) = ab”)); 

local 
val lemma = 
fVar_Inst_th
("P",([("s",mem_sort (Pow (Cross (mk_set "A") (mk_set "B"))))],
“!x:mem(A).?!y:mem(B).Holds(In(A * B),Pair(x,y),s)”))
(Thm_2_4 |> qspecl [‘Pow(A * B)’])
val lemma1 = 
fVar_Inst_th 
("P",([("fa",mem_sort (Cross (mk_set "A2B") (mk_set "A"))),
        ("b",mem_sort (mk_set "B"))],
“Holds(In(A * B),Pair(App(p2(A2B,A),fa),b),App(i,App(p1(A2B,A),fa)))”))
(AX1 |> qspecl [‘A2B * A’,‘B’]) |> uex_expand
val lemma2 = 
fVar_Inst_th
("P",([("ab",mem_sort (Cross (mk_set "A") (mk_set "B")))],
“App(f:A->B,App(p1(A,B),ab)) = App(p2(A,B),ab)”))
(In_def_P |> qspecl [‘A * B’]) |> uex_expand
in
val Thm_2_13 = proved_th $
e0
(rpt strip_tac >> 
 x_choosel_then ["A2B","i"] strip_assume_tac lemma >>
 x_choose_then "ev" strip_assume_tac lemma1 >> 
 qby_tac ‘isFun(ev)’ >--
 (rw[Fun_expand] >> arw[] >> rpt strip_tac (* 2 *) >--
  (first_x_assum 
    (qspecl_then [‘App(i, App(p1(A2B, A), a))’] assume_tac) >>
   qby_tac ‘?b:mem(A2B).App(i,App(p1(A2B,A),a)) = App(i,b)’ >--
    (qexists_tac ‘App(p1(A2B, A), a)’ >> rw[]) >>
   fs[] >> pop_assum (assume_tac o GSYM) >> arw[] >>
   pop_assum (K all_tac) >> 
   first_x_assum 
    (qspecl_then [‘App(p2(A2B, A), a)’]  
     (strip_assume_tac o uex_expand)) >>
   qexists_tac ‘y’ >> arw[]) >>
  first_x_assum 
    (qspecl_then [‘App(i, App(p1(A2B, A), a))’] assume_tac) >>
   qby_tac ‘?b:mem(A2B).App(i,App(p1(A2B,A),a)) = App(i,b)’ >--
    (qexists_tac ‘App(p1(A2B, A), a)’ >> rw[]) >>
   fs[] >> pop_assum (assume_tac o GSYM) >> arw[] >>
   pop_assum (K all_tac) >> 
   first_x_assum 
    (qspecl_then [‘App(p2(A2B, A), a)’]  
     (strip_assume_tac o uex_expand)) >>
  qsuff_tac ‘b1 = y & b2 = y’ >-- (strip_tac >> arw[]) >>
  strip_tac (* 2 *) >> first_x_assum irule >> arw[]) >> 
 drule rel2fun >> pop_assum (assume_tac o uex_expand) >>
 pop_assum $ x_choose_then "ev1" strip_assume_tac >>
 qexistsl_tac [‘A2B’,‘ev1’] >>
 (*the 2 conds of fun above has repeated proof*)
 rpt strip_tac >> uex_tac >> 
 x_choose_then "grf" strip_assume_tac $ GSYM lemma2 >>
 last_assum (qspecl_then [‘grf’] assume_tac) >>
 qby_tac ‘!x.?!y.Holds(In(A * B),Pair(x,y),grf)’ >--
 (strip_tac >> uex_tac >> arw[] >> rw[Pair_def] >>
  qexists_tac ‘App(f,x)’ >> rw[] >> rpt strip_tac >> arw[]) >>
 qby_tac ‘?b : mem(A2B). grf = App(i, b)’ >--
 (pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >> 
   once_arw[] >> first_x_assum (accept_tac o iffLR)) >>
  pop_assum (x_choose_then "fbar" assume_tac) >>
  qexists_tac ‘fbar’ >> 
  fs[Pair_def] >> rpt strip_tac (* 2 *) >--
  (qpick_x_assum ‘App(i, fbar) = App(i, b)’ (assume_tac o GSYM) >>
  arw[Pair_def]) >>
  fs[Inj_def] >> first_x_assum irule >> 
  qpick_x_assum ‘App(i, fbar) = App(i, b)’ (assume_tac o GSYM) >>
  fs[] >> flip_tac >> first_x_assum irule >>
  strip_tac >> 
  first_x_assum (qspecl_then [‘App(i,sf')’] assume_tac) >>
  (*?(b : mem(A2B)). App(i, sf') = App(i, b#) should automatically become true , happens twice in this proof, todo, stupid*)
  qby_tac ‘?b.App(i,sf') = App(i,b)’ >--
  (qexists_tac ‘sf'’ >> rw[]) >> fs[] >>
  pop_assum (assume_tac o GSYM) >> arw[] >>
  pop_assum (K all_tac) >>
  dimp_tac >> strip_tac (* 2 *) >--
  (qpick_x_assum ‘!x:mem(A).?!y:mem(B).Holds(In(A * B),Pair(x,y),App(i,sf'))’ assume_tac >> 
   first_x_assum (qspecl_then [‘App(p1(A,B),a)’] $
     strip_assume_tac o uex_expand) >>
   qsuff_tac ‘App(p2(A, B), a) = y & 
              App(f, App(p1(A, B), a)) = y’ >--
   (strip_tac >> arw[]) >>
   strip_tac >> first_x_assum irule  (* 2 *)
   >-- arw[Pair_p12] >>
   pick_x_assum  “!a.Holds(In(A* B),Pair(a,App(f,a)),App(i:A2B->Pow(A * B),sf':mem(A2B)))” assume_tac >>
   first_x_assum (qspecl_then [‘App(p1(A,B),a)’] assume_tac) >>
   arw[]) >> 
  once_rw[GSYM Pair_p12] >> once_arw[] >>
  pick_x_assum  “!a.Holds(In(A* B),Pair(a,App(f,a)),App(i:A2B->Pow(A * B),sf':mem(A2B)))” assume_tac >>
   first_x_assum (qspecl_then [‘App(p1(A,B),a)’] assume_tac) >>
   arw[] >> rfs[])
(form_goal
“!A B.?A2B ev:A2B * A ->B. 
 !f:A->B. 
 ?!sf:mem(A2B).!a:mem(A).App(ev,Pair(sf,a)) = App(f,a)”)
end

local
val l = 
    fVar_Inst_th ("P",([("af",mem_sort $ Cross (mk_set "A") (mk_set "A2B")),("b",mem_sort (mk_set "B"))],
“App(ev:A2B * A ->B,Pair(App(p2(A,A2B),af),App(p1(A,A2B),af))) = b”))
(AX1|> qspecl [‘A * A2B’,‘B’])
|> uex_expand 
in
val Exp_ex = prove_store("Exp_ex",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] strip_assume_tac Thm_2_13 >> 
 qexists_tac ‘A2B’ >>
 strip_assume_tac l >>
 qby_tac ‘isFun(R)’ >--
 (arw[Fun_expand] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘App(ev, Pair(App(p2(A, A2B), a), App(p1(A, A2B), a)))’ >>
      rw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[]) >>
 drule rel2fun >> 
 pop_assum (assume_tac o uex_expand) >>
 pop_assum $ x_choose_then  "R1" strip_assume_tac >>
 qexists_tac ‘R1’ >> 
 strip_tac >> uex_tac >> 
 last_x_assum (qspecl_then [‘f’] (strip_assume_tac o uex_expand)) >>
 qexists_tac ‘sf’ >> rpt strip_tac (* 2 *)
 >-- arw[Pair_def] >>
 first_x_assum irule >> rfs[Pair_def])
(form_goal
“!A B.?A2B ev:A * A2B ->B. 
 !f:A->B.?!sf:mem(A2B).!a:mem(A).App(ev,Pair(a,sf)) = App(f,a)”));
end

val Exp_def = Exp_ex |> spec_all |> qSKOLEM "Exp" [‘A’,‘B’]
                     |> gen_all |> store_as "Exp_def"; 

val Ev_def = Exp_def |> spec_all |> qSKOLEM "Ev" [‘A’,‘B’]
                     |> gen_all |> store_as "Ev_def";

val Tpm_def = Ev_def |> spec_all |> uex_expand
                     |> qSKOLEM  "Tpm" [‘f’]
                     |> disch_all |> gen_all
                     |> store_as "Tpm_def";  


val rel2fun_ex = prove_store("rel2fun_ex",
e0
(rpt strip_tac >> drule rel2fun >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f’ >> arw[])
(form_goal
 “!A B R:A~>B. isFun(R) ==> 
  ?f:A ->B. !a b. App(f,a) = b <=> Holds(R,a,b)”));

val rel2fun_ex' = rel2fun_ex |> rewr_rule[Fun_def]


val AX1_ex = prove_store("AX1_ex",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] (strip_assume_tac o uex_expand) AX1 >>
 qexists_tac ‘R’ >> arw[])
(form_goal
 “!A B. ?R:A~>B. !a b. Holds(R,a,b) <=> P(a,b)”));
 
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
                                 |> allI ivar
        val th2 = mp th1 lemma
    in th2
    end
(*under test
example:
val ivar = dest_var $ rastt "a:mem(A)"
val otm = rastt "App(f:A * X -> B,Pair(a,x))"

*)

local
val l = P2fun' |> qspecl [‘A’,‘B’] 
               |> fVar_sInst_th “P(a:mem(A),b:mem(B))”
                  “App(f:A * X->B,Pair(a,x)) = b”
in
val Ap1_ex = prove_store("curry_lemma",
e0
(rpt strip_tac >> flip_tac >> irule l >> strip_tac >>
 uex_tac >> qexists_tac ‘App(f, Pair(x', x))’ >> rw[] >>
 rpt strip_tac >> arw[]) 
(form_goal
 “!A X B f:A * X->B. 
  !x. ?fx:A->B. 
  !a. App(fx,a) = App(f,Pair(a,x))”));
end

val Ap1_def = Ap1_ex |> spec_all |> qSKOLEM "Ap1" [‘f’,‘x’] 
                     |> qgen ‘f’ |> qgen ‘B’
                     |> gen_all
                     |> store_as "Ap1_def";

val Cross_eq = 
    p2_def |> spec_all |> conjE2 |> gen_all|> store_as "Cross_eq";


val ao_assoc = Thm_2_7_assoc

val ao_Fun = Thm_2_7_ao_Fun



val App_o_l = App_App_o


val App_Pa = prove_store("App_Pa",
e0
(rpt strip_tac >>  assume_tac Pa_def >> irule Cross_eq >> rw[Pair_def] >> 
 arw[GSYM App_App_o])
(form_goal
 “!A C f:A->C B D g:B->D. 
  !ab:mem(A * B).App(Pa(f o p1(A,B),g o p2(A,B)),ab) = Pair(App(f o p1(A,B),ab),App(g o p2(A,B),ab))”));


val App_o_p2 = prove_store("App_o_p2",
e0
(rw[App_App_o,Pair_def])
(form_goal
 “!B C f:B->C.  !A a b.App(f o p2(A,B),Pair(a,b)) = App(f,b)”));


val App_o_p1 = prove_store("App_o_p1",
e0
(rw[App_App_o,Pair_def])
(form_goal
 “!A C f:A->C. !B a b.App(f o p1(A,B),Pair(a,b)) = App(f,a)”));



val is_Tpm = Tpm_def |> spec_all |> conjE2 
                     |> gen_all 
                     |> store_as "is_Tpm";



val Fst_ex = prove_store("Fst_ex",
e0
(rpt strip_tac >> qexists_tac ‘App(p1(A,B),x)’ >> rw[])
(form_goal
 “!A B x:mem(A * B).?fstx. App(p1(A,B),x) = fstx”));

 
val Snd_ex = prove_store("Snd_ex",
e0
(rpt strip_tac >> qexists_tac ‘App(p2(A,B),x)’ >> rw[])
(form_goal
 “!A B x:mem(A * B).?sndx. App(p2(A,B),x) = sndx”));

val Fst_def = Fst_ex |> spec_all |> qSKOLEM "Fst" [‘x’]
val Snd_def = Snd_ex |> spec_all |> qSKOLEM "Snd" [‘x’]

val Pair_def' = Pair_def |> rewr_rule[Fst_def,Snd_def]|> gen_all
                         |> store_as "Pair_def'";

val Pair_Fst_Snd = Pair_component |> rewr_rule[Fst_def,Snd_def] |> store_as "Pair_Fst_Snd";



val Pair_has_comp = prove_store("Pair_has_comp",
e0
(rpt strip_tac >> 
 qexistsl_tac [‘Fst(ab)’,‘Snd(ab)’]>>
 rw[Pair_Fst_Snd])
(form_goal
 “!A B ab:mem(A * B). ?a b. ab = Pair(a,b)”));


val IdL = prove_store("IdL",
e0
(rw[Id_def,GSYM FUN_EXT,App_App_o])
(form_goal “!A B f:A->B. Id(B) o f = f”));


val IdR = prove_store("IdR",
e0
(rw[Id_def,GSYM FUN_EXT,App_App_o])
(form_goal “!A B f:A->B. f o Id(A) = f”));


val p12_of_Pair = Pair_def |> store_as "p12_of_Pair"; 

local 
val l = P2fun' |> qspecl [‘X’,‘Exp(A,B)’]
              |> fVar_sInst_th “P(x:mem(X),fx:mem(Exp(A,B)))”
                 “Tpm(Ap1(f:A * X->B,x)) = fx”
in
val Tp_ex = prove_store("Tp_ex",
e0
(rpt strip_tac >> 
 qby_tac ‘!h:X->Exp(A,B). Ev(A,B) o Pa(p1(A,X),h o p2(A,X)) = f ==>
  (!a. Tpm(Ap1(f, a)) = App(h, a))’
 >-- (rpt strip_tac >> flip_tac >> irule is_Tpm >> 
     strip_tac >> rw[Ap1_def] >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[App_App_o] >> 
     qsuff_tac
     ‘App(Ev(A, B), Pair(a', App(h, a))) =
      App(Ev(A, B), App(Pa(Id(A) o p1(A, X), h o p2(A, X)), Pair(a', a)))’
     >-- rw[IdL] >>
     rw[App_Pa,App_App_o,p12_of_Pair,Id_def]) >>
 assume_tac l >>
 qsuff_tac ‘?f':X->Exp(A,B).!a. Tpm(Ap1(f, a)) = App(f', a)’ 
 >-- (strip_tac >> uex_tac >>
     qexists_tac ‘f'’ >> strip_tac >--(* 2 *) 
     (rw[GSYM FUN_EXT] >> strip_tac >>
     qsspecl_then [‘a’] (x_choosel_then ["a0","x0"] assume_tac) Pair_has_comp>>
     arw[] >>  
     qsuff_tac
     ‘App(Ev(A, B), App(Pa(Id(A) o p1(A, X), f' o p2(A, X)), Pair(a0, x0))) =
               App(f, Pair(a0, x0))’
     >-- rw[IdL] >>
     rw[App_App_o,App_Pa] >> 
     rw[p12_of_Pair,Id_def] >>
     first_x_assum (qspecl_then [‘x0’] assume_tac) >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[Tpm_def,Ap1_def]) >>
     rpt strip_tac >> first_x_assum drule >> 
     rw[GSYM FUN_EXT] >> pop_assum (assume_tac o GSYM) >> arw[]) >>
 first_x_assum irule >> strip_tac >>
 uex_tac >> qexists_tac ‘Tpm(Ap1(f, x))’ >> rw[] >> rpt strip_tac >> arw[])
(form_goal
 “!A X B f:A * X ->B. ?!h: X -> Exp(A,B).
  Ev(A,B) o Pa(p1(A,X),h o p2(A,X)) = f”));
end


val Tp_def = Tp_ex |> spec_all |> uex_expand
                   |> qSKOLEM "Tp" [‘f’]
                   |> store_as "Tp_def";



val is_Tp = Tp_def |> spec_all
                   |> conjE2 |> gen_all
                   |> store_as "is_Tp";

val Refl_def = qdefine_psym ("Refl",[‘R:A~>A’])
               ‘!a. Holds(R,a,a)’ |> gen_all |> store_as "Refl_def";

val Sym_def =  qdefine_psym ("Sym",[‘R:A~>A’])
               ‘!a1 a2. Holds(R,a1,a2) ==> Holds(R,a2,a1)’
               |> gen_all |> store_as "Sym_def";


val Trans_def = qdefine_psym ("Trans",[‘R:A~>A’])
               ‘!a1 a2 a3. Holds(R,a1,a2) & Holds(R,a2,a3) ==> Holds(R,a1,a3)’
               |> gen_all |> store_as "Trans_def";

val ER_def = qdefine_psym ("ER",[‘R:A~>A’])
             ‘Refl(R) & Sym(R) & Trans(R)’
             |> gen_all |> store_as "ER_def";

val Sym_Trans_Rright = prove_store("Sym_Trans_Rright",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >--
 (qby_tac ‘Holds(R,y,x)’ >-- 
  (fs[Sym_def] >> first_x_assum rev_drule >> arw[]) >>
  fs[Trans_def] >> first_x_assum irule >>
  qexists_tac ‘x’ >> arw[]) >>
 fs[Trans_def] >> first_x_assum irule >>
 qexists_tac ‘y’ >> arw[])
(form_goal
 “!A R:A~>A.Sym(R) & Trans(R)==> !x y. Holds(R,x,y) ==>
  (!z.Holds(R,x,z) <=> Holds(R,y,z))”));


(*

Theorem 2.14. If R is an equivalence relation on A, then there is a surjective function q:A↠B such that R(x,y) holds iff q(x)=q(y).

Proof. R induces a function fR:A→PA as above; let B be im(fR) and q the surjective part of the image factorization. If R(x,y) holds, then by symmetry and transitivity, R(x,z)⇔R(y,z) for all z; hence fR(x)=fR(y) and so q(x)=q(y). Conversely, if q(x)=q(y), then fR(x)=fR(y); but y∈fR(y) by reflexivity, hence y∈fR(x) and thus R(x,y) holds.  ▮

*)
 
val Thm_2_14 = prove_store("Thm_2_14",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘A’,‘R’] (strip_assume_tac o uex_expand) Thm_2_12 >>
 qsspecl_then [‘fR’] assume_tac Thm_2_10 >> pop_assum strip_assume_tac >>
 qexistsl_tac [‘M’,‘e’] >> strip_tac >-- arw[] >>
 rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >--
 (qsuff_tac ‘App(fR,x) = App(fR,y)’ >--
  (arw[] >> fs[Inj_def] >> strip_tac >> first_x_assum irule >>
   qby_tac ‘App(m, App(e, x)) = App(m o e, x) &
            App(m, App(e, y)) = App(m o e, y)’ >--
   rw[App_App_o] >>
   fs[]) >>
  irule In_EXT >> strip_tac >> 
  first_assum (qspecl_then [‘y’,‘x'’] (assume_tac o GSYM)) >>
  first_x_assum (qspecl_then [‘x’,‘x'’] (assume_tac o GSYM)) >>
  arw[] >> 
  qby_tac ‘Sym(R) & Trans(R)’ >-- fs[ER_def] >>
  drule Sym_Trans_Rright >> first_x_assum drule >> arw[]) >>
  arw[] >>  
  qsuff_tac ‘Holds(In(A),y,App(fR,y)) & App(fR,y) = App(fR,x)’ >--
  (strip_tac >> rev_full_simp_tac[] >> fs[]) >>
  strip_tac (* 2 *) >--
   (first_x_assum (irule o iffLR) >> fs[ER_def,Refl_def]) >> 
  arw[App_App_o])
(form_goal
“!A R:A~>A. ER(R) ==> ?B q:A->B. Surj(q) & !x y.Holds(R,x,y) <=> App(q,x) = App(q,y)”)); 

(*
Axiom 4 (Infinity): There exists a set N, containing an element o, and a function s:N→N such that s(n)≠o for any n∈N and s(n)=s(m) only if n=m for any n,m∈N.
*)


val IN_def = qdefine_psym ("IN",[‘a:mem(A)’,‘ss:mem(Pow(A))’])
             ‘Holds(In(A),a,ss)’ 
             |> gen_all |> store_as "IN_def";


val IN_def_P_expand = In_def_P |> spec_all
                        |> uex_expand 
                        |>rewr_rule[spec_all $ GSYM IN_def]
                        |> gen_all
                        |> store_as "IN_def_P_expand";

val IN_EXT = In_EXT |> rewr_rule[GSYM IN_def]
                    |> store_as "IN_EXT";



val SS_def = qdefine_psym ("SS",[‘P1:mem(Pow(A))’,‘P2:mem(Pow(A))’])
                          ‘(∀a. IN(a,P1) ⇒ IN(a,P2))’
                          |> gen_all 
                          |> store_as "SS_def";



val SS_Trans = prove_store("SS_Trans",
e0
(rw[SS_def] >> rpt strip_tac >> first_x_assum irule >>
 first_x_assum irule >> arw[])
(form_goal 
 “∀A P1:mem(Pow(A)) P2. SS(P1,P2) ⇒ ∀P3. SS(P2,P3) ⇒ SS(P1,P3)”));

val SS_SS_eq = prove_store("SS_SS_eq",
e0
(rpt strip_tac >> irule IN_EXT >> fs[SS_def] >> 
 strip_tac >> dimp_tac >> strip_tac >> 
 first_x_assum irule >> arw[])
(form_goal “∀A p1:mem(Pow(A)) p2. SS(p1,p2) ∧ SS(p2,p1) ⇒
 p1 = p2”));



val IN_def_P_ex = prove_store("IN_def_P_ex",
e0
(strip_tac >>
 qspecl_then [‘A’] strip_assume_tac IN_def_P_expand >>
 qexists_tac ‘s’ >> first_x_assum accept_tac)
(form_goal “!A. ?s:mem(Pow(A)). (!a. P(a) <=> IN(a,s))”));



val IN_def_P = In_def_P |>rewr_rule[GSYM IN_def]
                        |> GSYM
                        |> store_as "IN_def_P";

val AX4 = new_ax
“?N0 O0:mem(N0) S0:N0->N0.  (!n:mem(N0). ~(App(S0,n) = O0)) & 
 !n m. App(S0,n) = App(S0,m) <=> n = m”

val N0_def = AX4 |> qSKOLEM "N0" [] |> store_as "N0_def";

val O0_def = N0_def |> qSKOLEM "O0" [] |> store_as "O0_def";

val S0_def = O0_def |> qSKOLEM "S0" [] |> store_as "S0_def";

val N0 = mk_fun "N0" []



local
val lemma =
fVar_Inst_th ("P",([("sss",mem_sort $ Pow $ Pow (mk_set "A")),
                  ("ss",mem_sort $ Pow (mk_set "A"))],
“!a:mem(A).IN(a,ss) <=> !ss0. IN(ss0,sss) ==> IN(a,ss0)”))
(AX1|> qspecl [‘Pow(Pow(A))’,‘Pow(A)’])
|> uex_expand
val lemma' = 
fVar_Inst_th ("P",([("a",mem_sort (mk_set "A"))],
“!ss0. IN(ss0,sss) ==> IN(a:mem(A),ss0)”))
(IN_def_P_expand|> qspecl [‘A’]) |> GSYM
in
val BIGINTER_ex = prove_store("BIGINTER_ex",
e0
(strip_tac >> 
 x_choosel_then ["BI"] strip_assume_tac lemma >>
 qby_tac ‘!sss. ?ss. Holds(BI,sss,ss)’ >--
 (strip_tac >> once_arw[] >> 
  x_choose_then "ss" strip_assume_tac lemma' >>
  qexists_tac ‘ss’ >> once_arw[] >> rw[]) >>
 qby_tac ‘isFun(BI)’
 >-- (rw[Fun_expand] >> arw[] >> rpt strip_tac >>
     irule IN_EXT >> arw[]) >>
 drule rel2fun_ex >> pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >> rpt strip_tac >> 
 first_x_assum $ irule o iffLR >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A. ?BI:Pow(Pow(A)) -> Pow(A). 
  !sss:mem(Pow(Pow(A))) a:mem(A). IN(a,App(BI,sss)) <=>
  !ss.IN(ss,sss) ==> IN(a,ss)”));
end

val BI_def = BIGINTER_ex |> spec_all |> qSKOLEM "BI" [‘A’]
                         |> gen_all
                         |> store_as "BI_def"; 





val BIGINTER_ex = prove_store("BIGINTER_ex",
e0
(rpt strip_tac >> qexists_tac ‘App(BI(A),sss)’ >> rw[])
(form_goal
 “!A sss:mem(Pow(Pow(A))). ?isss.App(BI(A),sss) = isss”))


val BIGINTER_def = BIGINTER_ex |> spec_all |> qSKOLEM "BIGINTER" [‘sss’]
                               |> store_as "BIGINTER_def";

val IN_BIGINTER = BI_def |> rewr_rule[BIGINTER_def] 
                         |> store_as "IN_BIGINTER";


val IN_EXT_iff = prove_store("IN_EXT_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac 
 >-- (irule IN_EXT >> arw[]) >> arw[])
(form_goal “∀A s1 s2. (∀x:mem(A). IN(x,s1) ⇔ IN(x,s2)) ⇔ s1 = s2”));

use "SEARreln.sml";

local
val inN_cl = 
 “(n = O0 ==> IN(n,inN)) &
  (!n0. IN(n0,inN) & n = App(S0,n0) ==> IN(n,inN))”
in
val (inN_incond,x1) = mk_incond inN_cl;
val inNf_ex = mk_fex inN_incond x1;
val inNf_def = mk_fdef "inNf" inNf_ex;
val inNf_monotone = mk_monotone inNf_def;
val inN's_def = mk_prim inNf_def;
val inNs_def = mk_LFP (rastt "inN's");
val inNs_cond = mk_cond inNs_def inN's_def;
val inNs_SS = mk_SS inNs_def inN's_def;
val inN_rules0 = mk_rules inNf_monotone inNs_SS inNs_cond;
val inN_cases0 = mk_cases inNf_monotone inN_rules0 inNs_cond;
val inN_ind0 = mk_ind inNs_cond;
val inN_ind1 = mk_ind1 inNf_def inN_ind0;
val inN_ind2 = mk_ind2 inN_ind1;
val inN_cases1 = mk_case1 inNf_def inN_cases0;
val inN_rules1 = mk_rules1 inNf_def inN_rules0;
val inN_rules2 = mk_rules2 inN_rules1;
val inN_rules3 = mk_rules3 inN_rules2;
end

val inN_ind = inN_ind2 |> store_as "inN_ind";
val inN_cases = inN_cases1 |> store_as "inN_cases";
val inN_rules = inN_rules3 |> store_as "inN_rules";


(*Thm_2_4 is TYPE_DEFINITION, not easy to express it as a thm because the first input is a lambda abs, is this the reason of claiming Thm_2_4 is the best form of TYPE_DEFINITION? *)



(*lift lemmas not require R to be a full relation, hopefully can also be used for definition of Z or Q, where the relation are between power sets*)

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

val N_def = Thm_2_4 |> qspecl [‘N0’] 
                    |> fVar_sInst_th 
                       “P(a:mem(N0))” “IN(a,inNs)”
                    |> qSKOLEM "N" [] |> qSKOLEM "iN" []

val iN_Inj = N_def |> conjE1 |> store_as "iN_Inj"; 

(*iN_inNs should be automated*)
val iN_inNs = prove_store("iN_inNs",
e0
(strip_assume_tac N_def >> strip_tac >> first_x_assum $ irule o iffRL >>
 qexists_tac ‘n’ >> rw[])
(form_goal “!n.IN(App(iN,n),inNs)”));

val SUC_ex_lemma = prove_store("SUC_ex_lemma",
e0
(strip_tac >> 
 strip_assume_tac N_def >> 
 first_x_assum $ irule o iffLR >> 
 rw[App_App_o] >> irule (inN_rules |> conjE2) >>
 rw[iN_inNs])
(form_goal “!n1:mem(N).?n2:mem(N).App(S0 o iN, n1) = App(iN,n2)”));

val SUC_def =
 Inj_lift_fun_lemma |> qsspecl [‘iN’] 
                    |> C mp iN_Inj
                    |> qspecl [‘S0’]
                    |> C mp SUC_ex_lemma 
                    |> qSKOLEM "SUC" [] 
                    |> store_as "SUC_def";

val O_def = inN_rules |> conjE1 |> rewr_rule[N_def] 
                      |> qSKOLEM "O" []
                      |> store_as "O_def";

(*iN_eq_eq auto*)
val iN_eq_eq = iN_Inj |> rewr_rule[Inj_def]
                      |> store_as "iN_eq_eq";

val S0_eq_eq = S0_def |> conjE2 |> iffLR |> store_as "S0_eq_eq";

(*property of lifted function lemmas like Inj(f) ==> Inj(Lift(f)) ?*)
val SUC_Inj = prove_store("SUC_Inj",
e0
(rw[Inj_def] >> rpt strip_tac >> irule iN_eq_eq >>
 irule S0_eq_eq >> rw[GSYM SUC_def,GSYM App_App_o] >>
 arw[App_App_o])
(form_goal “Inj(SUC)”));

val iN_O = prove_store("iN_O",
e0
(strip_tac >> dimp_tac >> strip_tac >> arw[O_def] >>
 irule iN_eq_eq >> arw[GSYM O_def])
(form_goal “!n. App(iN,n) = O0 <=> n = O”));

val SUC_NONZERO = prove_store("SUC_NONZERO",
e0
(strip_tac >> rw[GSYM iN_O,GSYM App_App_o,SUC_def] >> 
 rw[App_App_o,S0_def])
(form_goal “!n.~(App(SUC,n) = O)”));


val Image_ex = prove_store("Image_ex",
e0
(rpt strip_tac >> irule 
 (P2fun' |> qspecl [‘Pow(A)’,‘Pow(B)’]
        |> fVar_sInst_th “P(x:mem(Pow(A)),y:mem(Pow(B)))”
        “!b. IN(b,y) <=> ?a. IN(a,x) & b = App(f:A->B,a)”) >>
 strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘B’] 
           |> fVar_sInst_th “P(b:mem(B))”
           “?a:mem(A). IN(a,x) & b = App(f:A->B,a)”))
(form_goal “!A B f:A->B. ?im:Pow(A) -> Pow(B). 
 !sa b. IN(b,App(im,sa)) <=> ?a. IN(a,sa) & b = App(f,a)”));


val Image_def = Image_ex |> spec_all
                         |> qSKOLEM "Image" [‘f’] 
                         |> gen_all
                         |> store_as "Image_def"; 


(*a machinary to convert things like O_xor_SUC into N0 form? maybe this:*)

val IMAGE_def = 
    IN_def_P_ex |> qspecl [‘B’] |> fVar_sInst_th “P(b:mem(B))”
                “?a. IN(a,s0) & b = App(f:A->B,a)” 
                |> GSYM 
                |> qSKOLEM "IMAGE" [‘f’,‘s0’] 
                |> gen_all
                |> store_as "IMAGE_def"; 

val Whole_def = 
    IN_def_P_ex |> qspecl [‘A’] |> fVar_sInst_th “P(a:mem(A))”
                “T” 
                |> rewr_rule [] 
                |> qSKOLEM "Whole" [‘A’] 
                |> gen_all
                |> store_as "Whole_def"; 


val IN_IMAGE_Inj = prove_store("IN_IMAGE_Inj",
e0
(rw[Inj_def,IMAGE_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘a’ >> arw[]) >>
 first_x_assum drule >> fs[])
(form_goal “!A A0 i:A->A0. Inj(i) ==>
 !s:mem(Pow(A)) a. IN(a,s) <=> IN(App(i,a),IMAGE(i,s))”));




val N_ind_P = prove_store("N_ind_P",
e0
(x_choose_then "s" (assume_tac o conjE1) (IN_def_P_expand |> qspecl [‘N’]) >>
 arw[] >> 
 strip_tac >> assume_tac iN_Inj >> drule IN_IMAGE_Inj >>
 arw[] >> 
 qspecl_then [‘IMAGE(iN,s)’] assume_tac inN_ind >>
 fs[N_def] >> 
 pop_assum 
 (assume_tac o (conv_rule $ (basic_fconv no_conv pull_exists_fconv1))) >>
 (*think more general on this step*)
 strip_tac >> first_x_assum irule >> arw[O_def,iN_inNs] >>
 rpt strip_tac (* 2 *)
 >-- (pop_assum mp_tac >> pop_assum (K all_tac) >>
     strip_tac >> fs[IMAGE_def] >>
     fs[GSYM App_App_o,GSYM SUC_def] >> first_x_assum irule >>
     qexists_tac ‘a'’ >> arw[]) >>
 qexists_tac ‘n’>> rw[])
(form_goal “P(O) & 
  (!n.P(n) ==> P(App(SUC,n)))==> !n:mem(N).P(n)”));

(*~(?(pn : mem(N)). F)  conv for this*)
val O_xor_SUC = prove_store("O_xor_SUC",
e0
(ind_with N_ind_P >> rw[GSYM SUC_NONZERO] >>  
 strip_tac >-- (ccontra_tac >>
 pop_assum strip_assume_tac) >>
 rpt strip_tac >>  rw[SUC_NONZERO] >> qexists_tac ‘n’ >> rw[])
(form_goal “!n. ~(n = O) <=> ?pn.n = App(SUC,pn)”));



val SUC_eq_eq = prove_store("SUC_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 assume_tac SUC_Inj >> fs[Inj_def] >> first_x_assum irule >> arw[])
(form_goal
 “!n1 n2. App(SUC,n1) = App(SUC,n2) <=> n1 = n2”));

val Suc_def = qdefine_fsym ("Suc",[‘n:mem(N)’]) ‘App(SUC,n)’ |> gen_all
                           |> store_as "Suc_def";

val O_xor_Suc = O_xor_SUC |> rewr_rule[GSYM Suc_def] |> store_as "O_xor_Suc";

val Suc_eq_eq = SUC_eq_eq |> rewr_rule[GSYM Suc_def] 
                          |> store_as "Suc_eq_eq";

val Suc_NONZERO = SUC_NONZERO |> rewr_rule[GSYM Suc_def]
                              |> store_as "Suc_NONZERO";

val N_induct = N_ind_P |> rewr_rule[GSYM Suc_def] 
                       |> store_as "N_induct";


val Eqv_def = qdefine_psym ("Eqv",[‘A’,‘B’]) ‘?f:A->B.Bij(f)’
              |> gen_all |> store_as "Eqv_def";

(*member of pow as set*)

val Asset_def = qdefine_psym ("Asset",[‘bs:mem(Pow(B))’,‘B0’])
‘!B1 i:B1->B. 
 Inj(i) & 
 (!b. (?b0:mem(B1). App(i,b0) = b) <=> IN(b,bs)) ==> 
 Eqv(B0,B1)’
 |> gen_all |> store_as "Asset_def";


val nPow_def = qdefine_psym ("nPow",[‘B’,‘n:mem(N)’,‘Pn’])
‘?C f:N->Pow(C). 
    (!C0. Asset(App(f,O),C0) ==> Eqv(C0,B)) &
    (!k Ck Csk. 
      Lt(k,n) &
      Asset(App(f,O),Ck) & Asset(App(f,O),Csk) ==>
      Eqv(Csk,Pow(Ck))) & 
    (!Cn. Asset(App(f,n),Cn) ==> Eqv(Cn,Pn))’
    |> store_as "nPow_def";

val AX5 = store_ax("AX5",
“!A.?B p:B->A Y M:B~>Y.  
 (!b Mb.
     (?i:Mb->Y. Inj(i) & 
                !y. (?y0. App(i,y0) = y) <=> Holds(M,b,y))
     ==> P(App(p,b),Mb)) & 
 !a:mem(A) X. P(a,X) ==> ?b. App(p,b) = a”)



val Sg_def = P2fun'|> qspecl [‘A’,‘Pow(A)’] 
                   |> fVar_sInst_th “P(a:mem(A),s:mem(Pow(A)))”
                      “!a0. IN(a0,s) <=> a0 = a:mem(A)”
                   |> C mp 
                      (IN_def_P |> spec_all
                                |> fVar_sInst_th “P(a0:mem(A))”
                                   “a0 = a:mem(A)”
                                |> qgen ‘a’)
                   |> qSKOLEM "Sg" [‘A’] |> gen_all
                   |> store_as "Sg_def";

val Sing_def = qdefine_fsym ("Sing",[‘a:mem(A)’])
                            ‘App(Sg(A),a:mem(A))’
                            |> gen_all |> store_as "Sing_def";


val Empty_def = IN_def_P |> qspecl [‘X’]
                         |> fVar_sInst_th “P(x:mem(X))” “F”
                         |> uex2ex_rule
                         |> qSKOLEM "Empty" [‘X’]
                         |> rewr_rule[]
                         |> gen_all |> store_as "Empty_def";

val Inj_eq_eq = prove_store("Inj_eq_eq",
e0
(rpt strip_tac >> fs[Inj_def] >> dimp_tac >>
 rpt strip_tac >> arw[] >>
 first_x_assum irule >> arw[])
(form_goal “!X Y i:X->Y. Inj(i) ==>
 (!x1 x2. App(i,x1) = App(i,x2) <=> x1 =  x2)”));


val Sing_eq_eq = prove_store("Sing_eq_eq",
e0
(rw[GSYM IN_EXT_iff,Sing_def,Sg_def] >> 
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >> 
 first_x_assum (qspecl_then [‘a1’] assume_tac) >> fs[])
(form_goal “!A a1:mem(A) a2. Sing(a1) = Sing(a2) <=> a1 = a2”));


val Sing_NONEMPTY = prove_store("Sing_NONEMPTY",
e0
(rw[GSYM IN_EXT_iff,Empty_def,Sing_def,Sg_def] >>rpt strip_tac >>
 ccontra_tac >> first_x_assum (qspecl_then [‘a’] assume_tac) >> fs[] )
(form_goal “!A a:mem(A). ~(Sing(a) = Empty(A))”));




val iscoPr_def = qdefine_psym("iscoPr",[‘i1:A->AB’,‘i2:B->AB’])
‘!X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g’
|> qgenl [‘A’,‘B’,‘AB’,‘i1’,‘i2’]
|> store_as "iscoPr_def";




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



fun dest_cross t = 
    case view_term t of 
        vFun("*",_,[A,B])=> (A,B)
      | _ => raise simple_fail "dest_cross.not a cross";
               

fun mk_Pair a b = mk_fun "Pair" [a,b]

fun forall_cross_fconv f = 
    let val (pv as (n,s),b) = dest_forall f 
        val pset = s |> dest_sort |> #2  |> hd
        val (A,B) = dest_cross pset 
        val pt = mk_var pv
        val eth = Pair_has_comp |> specl [A,B,pt]
        val (ocv1 as (ocn1,ocs1),ob1) = dest_exists (concl eth) 
        val (ocv2 as (ocn2,ocs2),ob2) = dest_exists ob1
        val avoids = fvf b
        val ct1 = pvariantt avoids (mk_var ocv1)
        val ct2 = pvariantt avoids (mk_var ocv2)
        val (cv1 as (cn1,cs1)) = dest_var ct1
        val (cv2 as (cn2,cs2)) = dest_var ct2
        val b1 = substf (ocv1,ct1) ob1
        val b2 = substf (ocv2,ct2) (substf (ocv1,ct1) ob2)
        val pair = mk_Pair ct1 ct2 
        val b' = substf (pv,pair) b
        val new = mk_forall cn1 cs1 (mk_forall cn2 cs2 b')
        val l2r = f |> assume |> allE pair 
                    |> simple_genl [cv1,cv2]
                    |> disch f
        val eth1 = b1 |> assume 
        val r2l = new |> assume |> specl [ct1,ct2]
                      |> rewr_rule[GSYM $ assume b2]
                      |> existsE cv2 eth1 
                      |> existsE cv1 eth
                      |> allI pv
                      |> disch new
    in dimpI l2r r2l 
    end

(* subset of Pow(A) * Pow(B)*)
val iscoPr_ex = prove_store("iscoPr_ex",
e0
(rpt strip_tac >>
 x_choosel_then ["AB","i"] assume_tac
 (Thm_2_4 |> qspecl [‘Pow(A) * Pow(B)’] 
 |> fVar_sInst_th “P(sab:mem(Pow(A) * Pow(B)))”
    “(Snd(sab) = Empty(B) & ?a. Fst(sab) = Sing(a)) | 
     (Fst(sab) = Empty(A) & ?b. Snd(sab) = Sing(b))”
 |> conv_rule (depth_fconv no_conv forall_cross_fconv)
 |> rewr_rule[Pair_def']) >> 
 qexists_tac ‘AB’ >> fs[] >>
 qby_tac
 ‘?i10:A->Pow(A) * Pow(B).
  !a.App(i10,a) = Pair(Sing(a),Empty(B))’
 >-- (irule (P2fun' |> qspecl [‘A’,‘Pow(A) * Pow(B)’]
     |> fVar_sInst_th “P(a:mem(A),sab:mem(Pow(A) * Pow(B)))”
     “sab:mem(Pow(A) * Pow(B)) = Pair(Sing(a),Empty(B))”) >>
     strip_tac >> uex_tac >> 
     qexists_tac ‘Pair(Sing(x), Empty(B))’ >> rw[]) >>
 pop_assum strip_assume_tac >>
 drule Inj_lift_fun >>
 first_x_assum (qsspecl_then [‘i10’] assume_tac) >>
 qby_tac
 ‘!x.?a:mem(AB).App(i10,x) = App(i,a)’
 >-- (strip_tac >> 
     arw[] >> first_x_assum (irule o iffLR) >>
     rw[] >> disj1_tac >> qexists_tac ‘x’ >> 
     rw[]) >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["i1"] assume_tac) >>
 qby_tac
 ‘?i20:B->Pow(A) * Pow(B).
  !b.App(i20,b) = Pair(Empty(A),Sing(b))’
 >-- (irule (P2fun' |> qspecl [‘B’,‘Pow(A) * Pow(B)’]
     |> fVar_sInst_th “P(b:mem(B),sab:mem(Pow(A) * Pow(B)))”
     “sab:mem(Pow(A) * Pow(B)) = Pair(Empty(A),Sing(b))”) >>
     strip_tac >> uex_tac >> 
     qexists_tac ‘Pair(Empty(A),Sing(x))’ >> rw[]) >>
 pop_assum strip_assume_tac >>
 drule Inj_lift_fun >>
 first_x_assum (qsspecl_then [‘i20’] assume_tac) >>
 qby_tac
 ‘!x.?b:mem(AB).App(i20,x) = App(i,b)’
 >-- (strip_tac >> 
     arw[] >> first_x_assum (irule o iffLR) >>
     rw[] >> disj2_tac >> qexists_tac ‘x’ >> 
     rw[]) >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["i2"] assume_tac) >>
 qexistsl_tac [‘i1’,‘i2’] >> 
 qby_tac ‘!ab. 
 (?a.App(i,ab) = Pair(Sing(a),Empty(B))) |
 (?b.App(i,ab) = Pair(Empty(A),Sing(b)))’
 >-- (strip_tac >>
     first_x_assum 
     (qspecl_then [‘Fst(App(i,ab))’,
                   ‘Snd(App(i,ab))’] assume_tac) >>
     fs[Pair_Fst_Snd] >>
     qby_tac ‘?b. App(i,ab) = App(i,b)’
     >-- (qexists_tac ‘ab’ >> rw[]) >>
     first_x_assum (drule o iffRL) >> 
     pop_assum (strip_assume_tac o GSYM) (* 2 *)
     >-- (disj1_tac >> qexists_tac ‘a''’ >> arw[Pair_Fst_Snd]) >> disj2_tac >> qexists_tac ‘b'’ >> arw[Pair_Fst_Snd]) >>
 qby_tac ‘Inj(i10)’
 >-- (rw[Inj_def] >> arw[Pair_eq_eq,Sing_eq_eq])>>
 qby_tac ‘Inj(i20)’
 >-- (rw[Inj_def] >> arw[Pair_eq_eq,Sing_eq_eq])>>
 qby_tac ‘Inj(i1)’ 
 >-- (rw[Inj_def] >> rpt strip_tac >>
     irule $ iffLR Inj_eq_eq >>
     qexistsl_tac [‘Pow(A) * Pow(B)’,‘i10’] >>
     qby_tac
     ‘App(i o i1, x1) = App(i o i1, x2)’ 
     >-- (rw[App_App_o] >> arw[]) >> rfs[]) >> arw[] >>
 qby_tac ‘Inj(i2)’ 
 >-- (rw[Inj_def] >> rpt strip_tac >>
     irule $ iffLR Inj_eq_eq >>
     qexistsl_tac [‘Pow(A) * Pow(B)’,‘i20’] >>
     qby_tac
     ‘App(i o i2, x1) = App(i o i2, x2)’ 
     >-- (rw[App_App_o] >> arw[]) >> rfs[]) >> arw[] >>
qby_tac ‘(!a b. ~(App(i1,a) = App(i2,b)))’
 >--(rpt strip_tac >>
 ccontra_tac >>
 qby_tac
 ‘App(i o i1, a) = App(i o i2, b)’
 >-- rw[App_App_o] >> arw[] >>
 rfs[Pair_eq_eq,Sing_NONEMPTY]) >> arw[] >>
 qby_tac ‘!ab. ((?a. ab = App(i1,a)) | (?b. ab = App(i2,b)))’
 >-- (strip_tac >> 
 first_x_assum (qspecl_then [‘ab’] strip_assume_tac) (* 2 *)
 >-- (disj1_tac >> qexists_tac ‘a’ >> 
     irule $ iffLR Inj_eq_eq >> 
     qexistsl_tac [‘Pow(A) * Pow(B)’,‘i’] >>
     arw[] >> arw[GSYM App_App_o]) >>
 disj2_tac >> qexists_tac ‘b’ >> 
 irule $ iffLR Inj_eq_eq >> 
 qexistsl_tac [‘Pow(A) * Pow(B)’,‘i’] >>
 arw[] >> arw[GSYM App_App_o]) >>
 qby_tac ‘iscoPr(i1,i2)’ >--
 (rw[iscoPr_def] >> rpt strip_tac >>
  uex_tac >> 
  qby_tac
  ‘?fg: AB ->X.
   !ab. 
   (!a. App(i,ab) = Pair(Sing(a),Empty(B)) ==>
        App(fg,ab) = App(f,a)) &
   (!b. App(i,ab) = Pair(Empty(A),Sing(b)) ==>
        App(fg,ab) = App(g,b)) ’
  >-- (assume_tac (P2fun' |> qspecl [‘AB’,‘X’]
     |> fVar_sInst_th “P(ab:mem(AB),x:mem(X))”
        “(?a. ab = App(i1:A->AB,a) & x = App(f:A->X,a)) | 
         (?b. ab = App(i2:B->AB,b) & x = App(g:B->X,b))”) >>
     qby_tac ‘!ab. 
     ?!x. (?a. ab = App(i1:A->AB,a) & x = App(f:A->X,a)) | 
         (?b. ab = App(i2:B->AB,b) & x = App(g:B->X,b))’
     >-- (strip_tac >>
         qsuff_tac
         ‘?x. (?a. ab = App(i1:A->AB,a) & x = App(f:A->X,a)) | 
         (?b. ab = App(i2:B->AB,b) & x = App(g:B->X,b))’
         >-- (strip_tac (* 2 *)
             >-- (uex_tac >> qexists_tac ‘x’ >> 
                 rpt strip_tac (* 3 *)
                 >-- (disj1_tac >> qexists_tac ‘a’ >> 
                     arw[]) 
                 >-- (arw[] >>
                     qsuff_tac ‘a= a'’ 
                     >-- (strip_tac >> arw[]) >>
                     irule $ iffLR Inj_eq_eq >>
                     qexistsl_tac [‘AB’,‘i1’] >> arw[] >>
                     qpick_x_assum ‘ab = App(i1, a)’
                     (assume_tac o GSYM) >> arw[]) >>
                 rfs[]) >>
             uex_tac >> qexists_tac ‘x’ >> 
             rpt strip_tac (* 3 *)
             >-- (disj2_tac >> qexists_tac ‘b’ >> arw[]) 
             >-- (fs[] >> rfs[])
             >-- (arw[] >>
                     qsuff_tac ‘b= b'’ 
                     >-- (strip_tac >> arw[]) >>
                     irule $ iffLR Inj_eq_eq >>
                     qexistsl_tac [‘AB’,‘i2’] >> arw[] >>
                     qpick_x_assum ‘ab = App(i2, b)’
                     (assume_tac o GSYM) >> arw[])) >>
         qcases ‘?a. ab = App(i1,a)’ (* 2 *)
         >-- (fs[] >> qexists_tac ‘App(f,a)’ >> disj1_tac >>
             qexists_tac ‘a’ >> rw[]) >>
         qpick_x_assum ‘!ab. (?a. ab = App(i1,a)) |
                             (?b. ab = App(i2,b))’
         (qspecl_then [‘ab’] assume_tac) >> rfs[] >>
         qexists_tac ‘App(g,b)’ >> disj2_tac >> 
         qexists_tac ‘b’ >>  rw[]) >>
     first_x_assum drule >>
     pop_assum (x_choosel_then ["fg"] assume_tac) >>
     qexists_tac ‘fg’ >> rpt strip_tac (* 2 *)
     >-- (first_x_assum
         (qspecl_then [‘ab’] strip_assume_tac) (* 2 *)
         >-- (fs[GSYM App_App_o] >> 
             rfs[Sing_eq_eq,Pair_eq_eq]) >>
         fs[GSYM App_App_o] >> 
         rfs[Pair_eq_eq,Sing_NONEMPTY]) >>
     first_x_assum
     (qspecl_then [‘ab’] strip_assume_tac) (* 2 *)
     >-- (fs[GSYM App_App_o] >> 
         rfs[Pair_eq_eq,Sing_NONEMPTY]) >>
     fs[GSYM App_App_o] >> 
     rfs[Sing_eq_eq,Pair_eq_eq]) >>
  pop_assum strip_assume_tac >>
  qexists_tac ‘fg’ >>
  qby_tac ‘fg o i1 = f & fg o i2 = g’ 
  >-- (rw[GSYM FUN_EXT,App_App_o] >> 
      rpt strip_tac (* 2 *)
      >-- (first_x_assum 
      (qspecl_then [‘App(i1, a)’] strip_assume_tac) >>
      first_x_assum irule >> arw[GSYM App_App_o]) >>
      first_x_assum 
      (qspecl_then [‘App(i2, a)’] strip_assume_tac) >>
      first_x_assum irule >> arw[GSYM App_App_o]) >>
  arw[] >> rpt strip_tac >>
  rw[GSYM FUN_EXT] >> strip_tac >>
  last_x_assum (qspecl_then [‘a’] strip_assume_tac) (* 2 *)
  >-- (first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
      first_x_assum drule >> arw[]>>
      qby_tac ‘a = App(i1,a')’ 
      >-- (rev_drule Inj_eq_eq >>
          first_x_assum (irule o iffLR) >>
          arw[GSYM App_App_o]) >>
      arw[] >> rw[GSYM App_App_o] >> arw[]) >> 
  first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
  first_x_assum drule >> arw[]>>
  qby_tac ‘a = App(i2,b)’ 
  >-- (rev_drule Inj_eq_eq >>
       first_x_assum (irule o iffLR) >>
       arw[GSYM App_App_o]) >>
  arw[] >> rw[GSYM App_App_o] >> arw[]) >>
 arw[])
(form_goal “!A B.?AB i1:A->AB i2:B->AB.iscoPr(i1,i2)
 & Inj(i1) & Inj(i2) & 
 (!a b. ~(App(i1,a) = App(i2,b))) & 
 !ab. ((?a. ab = App(i1,a)) | (?b. ab = App(i2,b)))
 ”));


val coPo_def = iscoPr_ex |> spec_all 
                         |> qSKOLEM "+" [‘A’,‘B’] |> gen_all
                         |> store_as "coPo_def";

val i1_def = coPo_def |> spec_all 
                      |> qSKOLEM "i1" [‘A’,‘B’] |> gen_all
                      |> store_as "i1_def";

val i2_def = i1_def |> spec_all |> qSKOLEM "i2" [‘A’,‘B’] |> gen_all
                    |> store_as "i2_def";

val coPa_def = i2_def |> rewr_rule[iscoPr_def] 
                      |> spec_all
                      |> conjE1 |> spec_all
                      |> uex_expand 
                      |> qSKOLEM "coPa" [‘f’,‘g’]
                      |> gen_all
                      |> store_as "coPa_def";

val i1_Inj = i2_def |> spec_all |> conjE2
                    |> conjE1 |> gen_all


val i1_ne_i2 = i2_def |> spec_all |> conjE2
                    |> conjE2 |> conjE2
                    |> conjE1 |> gen_all

val i1_or_i2 = i2_def |> spec_all |> conjE2
                    |> conjE2 |> conjE2
                    |> conjE2|> gen_all

val i1_xor_i2 = prove_store("i1_xor_i2",
e0
(rpt strip_tac >>
 qsspecl_then [‘ab’] strip_assume_tac i1_or_i2 (* 2 *) >--
 (arw[i1_ne_i2] >> dimp_tac >> strip_tac >> arw[] >>
 qsuff_tac ‘?a'.  App(i1(A, B), a) = App(i1(A,B),a')’
 >-- arw[] >>
 qexists_tac ‘a’ >> rw[]) >>
 arw[GSYM i1_ne_i2] >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘b’ >> rw[]) >>
 ccontra_tac >> fs[])
(form_goal “!A B ab.~(?a. ab = App(i1(A,B),a)) <=> ?b. ab = App(i2(A,B),b)”));


val i2_xor_i1 = prove_store("i2_xor_i1",
e0
(rpt strip_tac >>
 rw[GSYM i1_xor_i2])
(form_goal “!A B ab.~(?b. ab = App(i2(A,B),b)) <=> ?a. ab = App(i1(A,B),a)”));


val tof_def = proved_th $
e0
(rpt strip_tac >> flip_tac >>
 qsuff_tac ‘?f:A->B. 
 !a. App(f,a)= App(Ev(A,B),Pair(a,f0))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >> arw[GSYM FUN_EXT]) >>
 irule (P2fun' |> qspecl [‘A’,‘B’] 
 |> fVar_sInst_th “P(x:mem(A),y:mem(B))”
    “y = App(Ev(A,B),Pair(x,f0:mem(Exp(A,B))))”) >>
 strip_tac >> uex_tac >> qexists_tac ‘App(Ev(A, B), Pair(x, f0))’ >> rw[])
(form_goal “!A B f0:mem(Exp(A,B)).
 ?!f:A->B. 
 !a. App(Ev(A,B),Pair(a,f0)) = App(f,a)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "tof" [‘f0’]
