

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


val cond_unique_lemma' = proved_th $
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘b’ >> arw[] >> rpt strip_tac >> arw[])
(form_goal “!A a:mem(A). P(a) ==> !B b:mem(B).?!b'. P(a) & b' = b”)




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


val disj_assoc = prove_store("disj_assoc",
e0
(dimp_tac >> qcases ‘A’ >> fs[])
(form_goal “(A | B) | C <=> A | B | C”));


fun cond_rw_fconv impf = 
    let val (ante,conc) = dest_imp impf
        val anteth = assume ante
        val ciffc' = REWR_FCONV [anteth] conc
        val disched = disch ante ciffc'
        val specdistrth = conv_rule 
                              (rewr_fconv imp_dimp_distr) (disched)
    in specdistrth
    end



val f0 = “!a. (a = num1 ==> App(f,a) = num1) &
             (a = num2 ==> App(f,a) = num2) &
             (a = num3 ==> App(f,a) = num3) & 
             (ELSE ==> App(f,a) = O)”

val f = “ !a .
     (a = num1 ==> App(f, a) = num1) &
     (~(a = num1) & a = num2 ==> App(f, a) = num2) &
     (~(a = num1) & ~(a = num2) & a = num3 ==> App(f, a) = num3) &
     (~(a = num1) & ~(a = num2) & ~(a = num3) ==> App(f, a) = O)”

val f = “ !a .
     (a = num1 ==> App(f, a) = num1) &
     (~(a = num1) & a = num2 ==> App(f, a) = num2) &
     (~(a = num1) & ~(a = num2) ==> App(f, a) = num3)”



val f = “ !a .
     (a = num1 ==> App(f, a) = num1) &
     (~(a = num1)  ==> App(f, a) = num2)”


val f = “!a. (Odd(a) ==>  App(f, a) = num1) &
             (~Odd(a) ==> App(f,a) = O)”


REWR_FCONV [assume “~(a = num1)”] “a = num1”


val f1 = normalise_lambda_input f0
 define_lambda_fun f1 


val f = “!a. (P1(a) ==> App(f,a) = (Suc(a))) &
             (~P1(a) & P2(a) ==> App(f,a) = Suc(Suc(a))) &
             (~P1(a) & ~P2(a) & P3(a) ==> App(f,a) = a) &
             (~P1(a) & ~P2(a) & ~P3(a) ==> App(f,a) = O)”


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



fun define_lambda_fun' f = 
    let val (inputvar as (n,s),clauses) = dest_forall f
        val inputt = mk_var(n,s)
        val setvar = s |> dest_sort |> #2 |> hd
        val cll = strip_conj clauses
        val conds = List.map iant cll
        val outputs = List.map (#2 o dest_eq o iconc) cll
        val outputset = outputs |> hd |> sort_of |> dest_sort |> #2 |> hd
        val culemma = cond_unique_lemma' |> specl [setvar,inputt]
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
                        (*          |> GSYM*)
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
 

fun conj_assoc_fm f = 
    let val th = basic_fconv no_conv conj_assoc_fconv f 
    in th |> concl |> dest_dimp |> #2
    end

fun nlist n = 
    if n = 0 then [] else (nlist (n-1)) @ [n]

val fm0 = “!a.(P1(a) ==> App(f,a) = Suc(a)) &
             (P2(a) ==> App(f,a) = Suc(Suc(a))) &
             (ELSE ==> App(f,a) = a)”



fun normalise_lambda_input fm0 = 
    let val (ns,fm) = dest_forall fm0
        val cls = strip_conj fm 
        val (antes0,concs) = unzip (List.map dest_imp cls) 
        val antes1 = List.take (antes0,length(antes0) - 1) 
        val nums = nlist (length(antes1))
        fun mk_nth_ante (n,ante) = 
            let val toneg = List.take (antes1,n-1)
                val negs = List.map mk_neg toneg 
                val conj0 = mk_conj (mk_conjl negs) ante
                            handle _ => ante
            in conj_assoc_fm conj0
            end
        val antes2 = List.map mk_nth_ante 
                              (zip nums antes1)
        val ELSE = mk_conjl (List.map mk_neg antes1) 
        val antes = antes2 @ [ELSE] 
        val cls1 = List.map (uncurry mk_imp) 
                            (zip antes concs)
        val cjcls1 = mk_conjl cls1
    in uncurry mk_forall ns cjcls1 
    end


(fn (n,ante) => conj_assoc_fm 
            (mk_conj (mk_conjl (List.take ())) ante))
                         (fn ante => )

 List.take ([1,2,3],1)


(*inst_thm (mk_inst [] [("P",“P(a:mem(A))”)]) (assume “P”) 
 
*)
