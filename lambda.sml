

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




val imp_dimp_distr = proved_th $
e0
(dimp_tac >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum (irule o iffLR) >> arw[] >> 
      first_x_assum irule >> arw[]) 
 >-- (first_x_assum (irule o iffRL) >> arw[] >> 
      first_x_assum irule >> arw[]) 
 >-- (first_x_assum (irule o iffLR) >> arw[]) >>
 first_x_assum (irule o iffRL) >> arw[] )
(form_goal “(A ==> (B <=> C)) <=> ((A ==> B) <=> (A ==> C))”)

fun cond_rw_fconv impf = 
    let val (ante,conc) = dest_imp impf
        val anteth = assume ante
        val ciffc' = REWR_FCONV [anteth] conc
        val disched = disch ante ciffc'
        val specdistrth = conv_rule 
                              (rewr_fconv imp_dimp_distr) (disched)
    in specdistrth
    end


fun define_lambda_fun f = 
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
        val (funcv,fundef0) = dest_uex (concl specp2fun) 
        val (inputa, def0) = dest_forall fundef0
        val addT = T_imp1 def0 |> GSYM
        val T2djs = conv_rule (once_depth_fconv no_conv
                                                (rewr_fconv (GSYM provedjf)))
                                                addT
        (*T2djs can be hand instead*)
        val distrdjs = conv_rule (basic_fconv no_conv
                                               disj_imp_distr_fconv)
                                 T2djs
        val (old,newcls) = dest_dimp (concl distrdjs)
        val cjs = strip_conj newcls
        val impeqths = List.map cond_rw_fconv cjs
        val ncl2ncls' = REWR_FCONV impeqths newcls
        val wholeiff = iff_trans distrdjs ncl2ncls'
                       |> forall_iff inputa
                       |> uex_iff funcv
        val newdef = dimp_mp_l2r specp2fun wholeiff
    in newdef
    end

(*inst_thm (mk_inst [] [("P",“P(a:mem(A))”)]) (assume “P”) 
 
*)
