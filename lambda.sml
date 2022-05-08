

val conj1 = #1 o dest_conj
val conj2 = #2 o dest_conj


val iant = #1 o dest_imp
val iconc = #2 o dest_imp

val strip_conj =
   let
      fun aux acc f =
         aux (aux acc (conj2 f)) (conj1 f)
         handle _ => f :: acc
   in
      aux []
   end

val disj1 = #1 o dest_disj
val disj2 = #2 o dest_disj



val strip_disj =
   let
      fun aux acc f =
         aux (aux acc (disj2 f)) (disj1 f)
         handle _ => f :: acc
   in
      aux []
   end

fun conjIs thl = List.foldl (uncurry (C conjI)) (List.hd thl) (List.tl thl)


fun djE (f1,th1) (f2,th2) = (mk_disj f1 f2,disjE (assume (mk_disj f1 f2)) th1 th2)


fun djEs fthl = List.foldl (uncurry (C djE)) (List.hd fthl) (List.tl fthl)



val disj_neg_absorb = proved_th $
e0
(dimp_tac >> strip_tac >> qcases ‘A’ >> qcases ‘B’ >> arw[] (* 4 *)
 >> first_x_assum opposite_tac)
(form_goal “(A | (~A & B)) <=> A | B”)

(*tactic bug, if fs on disj_neg_absorb, then will complain disj not in list*)

val disj_of_negconj = proved_th $
e0
(dimp_tac >> strip_tac >> arw[] >> strip_tac >>
 qcases ‘A’ >> qcases ‘B’ >> arw[] 
 >-- (qsuff_tac ‘A | B’ >-- arw[] >> disj1_tac >> arw[]) 
 >-- (qsuff_tac ‘A | B’ >-- arw[] >> disj1_tac >> arw[]) 
 >-- (qsuff_tac ‘A | B’ >-- arw[] >> disj1_tac >> arw[]) >>
 (qsuff_tac ‘A | B’ >-- arw[] >> disj2_tac >> arw[]))
(form_goal “(~A & ~B) <=> ~(A | B)”)

fun drop_last_cj f = 
    let val cjs = strip_conj f
        val (last,cjs') = (hd (rev cjs),rev (tl (rev cjs)))
    in (mk_conjl cjs',last)
    end

(*drop_last_cj “~P1 & ~P2 & P3”*)

val TAUT = proved_th $
e0
(qcases ‘A’ >> arw[])
(form_goal “A | ~A”)


val cond_unique_lemma = proved_th $
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘b’ >> arw[] >> rpt strip_tac >> arw[])
(form_goal “!A a:mem(A). P(a) ==> !B b:mem(B).?!b'. P(a) & b = b'”)



fun define_fun f = 
    let val (inputvar as (n,s),clauses) = dest_forall f
        val inputt = mk_var(n,s)
        val setvar = s |> dest_sort |> #2 |> hd
        val cll = strip_conj clauses
        val conds = List.map iant cll
        val outputs = List.map (#2 o dest_eq o iconc) cll
        val outputset = outputs |> hd |> sort_of |> dest_sort |> #2 |> hd
        val culemma = cond_unique_lemma |> specl [setvar,inputt]
        val fvar0 = mk_fvar "P" [inputt]
        val cases = List.map 
                        (fn (cond,output) =>
                            culemma 
                                |> fVar_sInst_th fvar0 cond
                                |> undisch |> sspecl [output])
                             (zip conds outputs)
        val vconseqs = List.map (dest_uex o concl) cases
        val conseqs = List.map #2 vconseqs
        val djconseq = mk_disjl conseqs 
        val iffs = List.map (fn f => mk_dimp f djconseq) conseqs
        val eqvTs = List.map 
                        (fn (cond,iff) => 
                                         (REWR_FCONV [assume cond])
                                        iff |> rewr_rule[]) 
                        (zip conds iffs)
        val casesunified = List.map 
                               (fn (cl,eqth) =>
                               conv_rule (once_depth_fconv no_fconv (rewr_fconv eqth)) cl) (zip cases eqvTs)
        val todjEs = zip conds casesunified
        val (djf,djEedth0) = djEs todjEs 
        val djEedth = djEedth0 |> disch djf |> rewr_rule[disj_assoc] 
        val provedjf = REWR_FCONV [GSYM CONJ_ASSOC,disj_of_negconj,
                                      disj_neg_absorb,TAUT] djf
        val djEedth' = djEedth |> rewr_rule[provedjf,GSYM disj_assoc] 
        val (outputv,rel) = dest_uex (concl djEedth')
        val outputt = mk_var outputv
        val fvar1 = mk_fvar "P" [inputt,outputt]
        val specp2fun = P2fun_uex |> specl [setvar,outputset]
                                  |> fVar_sInst_th fvar1 rel
                                  |> C mp (allI inputvar djEedth')
                                  |> GSYM



        fun thsfc thl = basic_fconv no_fconv 
                                   (first_fconv (List.map rewr_fconv thl))
        val fc0 = thsfc [GSYM CONJ_ASSOC,disj_of_negconj,
                                      disj_neg_absorb,TAUT]
        val provecond = fc
        fun fc0 f0 = 
            let val fth = REWR_FCONV [GSYM CONJ_ASSOC,disj_of_negconj,
                                      disj_neg_absorb',TAUT] f0 
