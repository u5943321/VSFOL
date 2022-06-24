val _ = new_pred "Holds" [("R",rel_sort (mk_set "A") (mk_set "B")),
                         ("a",mem_sort (mk_set "A")),
                         ("b",mem_sort (mk_set "B"))]

val AX1 = store_ax("AX1",
“!A B:set.?!R:A~>B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(a,b)”);


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


val Fun_def = 
    qdefine_psym ("isFun",[‘R:A~>B’]) 
                 ‘!x:mem(A). ?!y:mem(B). Holds(R,x,y)’
    |> gen_all |> store_as "Fun_def";


val AX1_ex = prove_store("AX1_ex",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] (strip_assume_tac o uex_expand) AX1 >>
 qexists_tac ‘R’ >> arw[])
(form_goal
 “!A B. ?R:A~>B. !a b. Holds(R,a,b) <=> P(a,b)”));

val ao_uex = 
AX1 |> qspecl [‘A’,‘C’] 
    |> fVar_sInst_th “P(a:mem(A),c:mem(C))”
       “(?b. Holds(phi:A~>B,a,b) & Holds(psi:B~>C,b,c))” 

val ao_def0 = 
    ao_uex |> qsimple_uex_spec "@" [‘psi’,‘phi’]
           |> GSYM |> gen_all

val ao_def = prove_store("ao_def",
e0
(rw[ao_def0])
(form_goal “!A B phi:A~>B C psi:B~>C a:mem(A) c:mem(C). 
(?b. Holds(phi,a,b) & Holds(psi,b,c)) <=> Holds(psi @ phi,a,c)”));

val id_uex = AX1 |> qspecl [‘A’,‘A’] 
                 |> fVar_sInst_th “P(a1:mem(A),a2:mem(A))”
                    “a1 = a2:mem(A)” 
val id_def = id_uex |> qsimple_uex_spec "id" [‘A’] |> gen_all 


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


val op_uex = 
    AX1 |> qspecl [‘B’,‘A’]
        |> fVar_sInst_th “P(b:mem(B),a:mem(A))”
           “Holds(R:A~>B,a,b)” 

val op_def = op_uex |> qsimple_uex_spec "op" [‘R’] 
                    |> gen_all



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

val ao_assoc = Thm_2_7_assoc

val ao_Fun = Thm_2_7_ao_Fun |> store_as "ao_Fun";  



val op_DISTR = prove_store("op_DISTR",
e0
(rpt strip_tac >> 
 rw[GSYM R_EXT,op_def,GSYM ao_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac (*2 *) >--
 (qexists_tac ‘b'’ >> arw[]) >>
 qexists_tac ‘b'’ >> arw[])
(form_goal
“!A B phi:A~>B C psi:B~>C. op(psi @ phi) = op(phi) @ op(psi)”));


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

val op_op = prove_store("op_op",
e0
(rpt strip_tac >> irule $ iffLR R_EXT >> rw[op_def])
(form_goal
 “∀A B R:A~>B. op(op(R)) = R”));
