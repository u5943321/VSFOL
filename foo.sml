
fun fVar_sInst_th f f' th = 
    let val (P,args) = dest_fvar f
        val vl = List.map dest_var args
    in fVar_Inst_th (P,(vl,f')) th
    end


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

val rel2fun_ex = prove_store("rel2fun_ex",
e0
(rpt strip_tac >> assume_tac rel2fun >>
 first_x_assum drule >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qexists_tac ‘f’ >> arw[] )
(form_goal “!A B R:A~>B. isFun(R) ==> ?f:A->B. !a b. App(f,a) = b <=> Holds(R,a,b)”));



val S1_def = rel2fun_ex |> qspecl [‘N0’,‘N0’,‘S0’]
                        |> C mp S0_Fun
                        |> ex2fsym0 "S1" []
                        |> store_as "S1_def";

val inNf_ex = prove_store("inNf_ex",
e0
(cheat)
(form_goal “∃f. ∀p:mem(Pow(N0)). (∀x. IN(x,App(f,p)) ⇔ 
 (x = O0 | 
           ∃n0:mem(N0). IN(n0,p) ∧ x = App(S1,n0)) )”));

val inNf_def = inNf_ex |> ex2fsym0 "inNf" []


val SS_def = define_pred “∀A P1:mem(Pow(A)) P2. SS(P1,P2) ⇔ 
 (∀a. IN(a,P1) ⇒ IN(a,P2))”

val SS_Trans = prove_store("SS_Trans",
e0
(rw[SS_def] >> rpt strip_tac >> first_x_assum irule >>
 first_x_assum irule >> arw[])
(form_goal 
 “∀A P1:mem(Pow(A)) P2. SS(P1,P2) ⇒ ∀P3. SS(P2,P3) ⇒ SS(P1,P3)”));


val IN_def_P_ex = prove_store("IN_def_P_ex",
e0
(strip_tac >>
 qspecl_then [‘A’] strip_assume_tac IN_def_P_expand >>
 qexists_tac ‘s’ >> first_x_assum accept_tac)
(form_goal “!A. ?s:mem(Pow(A)). (!a. P(a) <=> IN(a,s))”));



val inN's_def = 
    IN_def_P_ex |> allE (rastt "Pow(N0)") |> GSYM
                |> fVar_sInst_th “P(a:mem(Pow(N0)))” 
                “SS(App(inNf,a:mem(Pow(N0))), a)”
                |> ex2fsym0 "inN's" []
                |> store_as "inN's_def";

val inNs_ex = prove_store("inNs_ex",
e0
(qexists_tac ‘BIGINTER(inN's)’ >> rw[])
(form_goal “∃inNs. inNs = BIGINTER(inN's)”));

val inNs_def = inNs_ex |> ex2fsym0 "inNs" []



val inNf_monotone = prove_store("inNf_monotone",
e0
(rw[inNf_def,SS_def] >> rpt strip_tac (* 2 *)
 >-- arw[] >> disj2_tac >> qexists_tac ‘n0’ >> arw[] >>
 first_x_assum irule >> arw[])
(form_goal “∀s1 s2. SS(s1,s2) ⇒ SS(App(inNf,s1), App(inNf,s2))”));

val inNf_monotone = prove_store("inNf_monotone",
e0
(rw[SS_def] >> rpt gen_tac >> disch_tac >>
 rw[inNf_def] >> 
rpt strip_tac (* 2 *)
 >-- arw[] >> disj2_tac >> qexists_tac ‘n0’ >> arw[] >>
 first_x_assum irule >> arw[])
(form_goal “∀s1 s2. SS(s1,s2) ⇒ SS(App(inNf,s1), App(inNf,s2))”));


“SS(App(inNf,s1), App(inNf,s2))”
|> basic_fconv (no_conv) (first_fconv [rewr_fconv(spec_all SS_def),rewr_fconv (spec_all inNf_def)])

(*

val disj_imp_distr = prove_store("disj_imp_distr",
e0
cheat
(form_goal “(A | B ⇒ C) ⇔ ((A ⇒ C) ∧ (B ⇒ C))”));

(assume “P | Q | S ⇒ R”) |> rewr_rule [disj_imp_distr]
*)

(*disj_imp_distr_th,COND_EXISTS_FCONV , pe_cl1 *)

val inN_rules0 = prove_store("inN_rules0",
e0
(rw[SS_def] >> rpt strip_tac >>
 rw[inNs_def] >> rw[IN_BIGINTER] >>
 rpt strip_tac >> 
 qby_tac ‘SS(inNs,ss)’
 >-- (rw[SS_def,inNs_def] >> rw[IN_BIGINTER] >> 
      rpt strip_tac >> first_x_assum irule >> arw[]) >>
 fs[inN's_def] >>
 drule inNf_monotone >>
 qby_tac ‘SS(App(inNf, inNs),ss)’
 >-- (irule SS_Trans >> qexists_tac ‘App(inNf, ss)’ >>
     arw[]) >>
 pop_assum (assume_tac o (rewr_rule [SS_def])) >>
 first_x_assum irule >> arw[])
(form_goal “SS(App(inNf,inNs),inNs)”));

val inNs_SS = prove_store("inNs_SS",
e0
(rw[inNs_def] >> rpt strip_tac >>
rw[SS_def] >> strip_tac >> 
rw[IN_BIGINTER] >> rw[inN's_def] >>
rpt strip_tac >> first_x_assum irule >> arw[])
(form_goal 
“∀X.SS(App(inNf, X), X) ⇒ SS(inNs, X)”));


“SS(inNs, X)”
|> basic_fconv (rewr_conv inNs_def) no_fconv
|> C iff_trans $
   (“SS(BIGINTER(inN's), X)”
   |> basic_fconv no_conv (rewr_fconv (spec_all SS_def)))
|> rewr_rule[IN_BIGINTER,inN's_def]
|> iffRL |> undisch 
|> prove_hyp $
(assume
     “∀ss. SS(App(inNf,ss),ss) ⇒ IN(a,ss)”
     |> qspecl [‘X:mem(Pow(N0))’]
     |> C mp (assume “SS(App(inNf, X), X)”)
     |> disch “∀ss. SS(App(inNf,ss),ss) ⇒ IN(a,ss)”
     |> allI ("a",mem_sort (rastt "N0")))
|> disch “SS(App(inNf, X), X)”
|> allI ("X",mem_sort (rastt "Pow(N0)"))



val inNs_cond = prove_store("inNs_cond",
e0
(rpt strip_tac >> rw[inNs_def] >> rw[IN_BIGINTER] >>
 rw[inN's_def])
(form_goal 
“∀a.(!X. SS(App(inNf, X), X) ==> IN(a, X)) ⇔ IN(a,inNs)”));

(*
“IN(a,inNs)”
 |> basic_fconv (rewr_conv inNs_def) no_fconv
 |> conv_rule $ basic_fconv no_conv (rewr_fconv (spec_all IN_BIGINTER))
 |> rewr_rule[inN's_def] |> GSYM

cond

*)



assume “SS(App(inNf,inNs),X)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘N0’,‘App(inNf,inNs)’,
                                ‘App(inNf,X)’]
                    |> undisch
                    |> qspecl [‘X:mem(Pow(N0))’]
                    |> undisch)
       |> prove_hyp
          (inNf_monotone 
               |> qspecl [‘inNs’,‘X:mem(Pow(N0))’]
               |> undisch)
       |> prove_hyp
          (inNs_SS |> qspecl [‘X:mem(Pow(N0))’]
                   |> undisch)
       |> disch “SS(App(inNf, X), X)”
       |> allI ("X",mem_sort (rastt "Pow(N0)"))
       |> rewr_rule[inNs_cond]
       |> disch “IN(a, App(inNf, inNs))”
       |> allI ("a",mem_sort (rastt "N0"))
       |> rewr_rule[GSYM SS_def]

assume “SS(App(inNf,A),A) ⇒ IN(a,A:mem(Pow(N0)))”
|> C mp (assume “SS(App(inNf,A),A)”)
|> prove_hyp
   (assume “∀X. SS(App(inNf,X),X) ⇒ IN(a,X)”
           |> qspecl [‘A:mem(Pow(N0))’])
|> disch
   “∀X. SS(App(inNf,X),X) ⇒ IN(a,X)”
|> allI ("a",mem_sort (rastt "N0"))
|> rewr_rule[inNs_cond]
|> rewr_rule[GSYM SS_def]
|> disch “SS(App(inNf, A), A)”
|> allI ("A",mem_sort (rastt "Pow(N0)"))

assume “SS(App(inNf,App(inNf,inNs)),App(inNf,inNs)) ⇒ 
        IN(a,App(inNf,inNs))”
|> C mp (assume “SS(App(inNf,App(inNf,inNs)),App(inNf,inNs))”)
|> prove_hyp 
   (inNf_monotone |> qspecl [‘App(inNf,inNs)’,‘inNs’]
                  |> undisch)
|> prove_hyp inN_rules0
|> prove_hyp (assume “∀X. SS(App(inNf,X),X) ⇒ IN(a,X)”
                     |> qspecl [‘App(inNf,inNs)’])
|> prove_hyp ( (iffRL inNs_cond) |> allE (rastt "a:mem(N0)")
                                 |> undisch)
|> disch “IN(a,inNs)”
|> allI ("a",mem_sort (rastt "N0"))
|> rewr_rule [GSYM SS_def]
|> conjI inN_rules0
|> mp (SS_SS_eq |> qspecl [‘N0’,‘App(inNf, inNs)’,‘inNs’])

(*
assume “SS(App(inNf,inNs),inNs)”
|> prove_hyp 
   (undisch $ iffRL $ basic_fconv no_conv (rewr_fconv (spec_all SS_def)) 
   “SS(App(inNf,inNs),inNs)”)
|> prove_hyp 

*)
   


val inN_rules1 = inN_rules0 |> rewr_rule [SS_def]
                            |> rewr_rule [inNf_def]

val inN_ind0 = prove_store("inN_ind0",
e0
(rpt strip_tac >>
 rw[inNs_def] >> rw[SS_def] >> rw[IN_BIGINTER] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘p’] assume_tac) >>
 rfs[inN's_def])
(form_goal
 “!p:mem(Pow(N0)). SS(App(inNf,p),p) ==> SS(inNs,p)”));




val inN_ind1 = inN_ind0 |> rewr_rule[SS_def]
                        |> rewr_rule[inNf_def]




val SS_SS_eq = prove_store("SS_SS_eq",
e0
(rpt strip_tac >> irule IN_EXT >> fs[SS_def] >> 
 strip_tac >> dimp_tac >> strip_tac >> 
 first_x_assum irule >> arw[])
(form_goal “∀A p1:mem(Pow(A)) p2. SS(p1,p2) ∧ SS(p2,p1) ⇒
 p1 = p2”));

val inN_cases0 = prove_store("inN_cases0",
e0
(irule SS_SS_eq >> rw[inN_rule0] >> 
 rw[SS_def] >> strip_tac >> rw[inNs_def] >>
 rw[IN_BIGINTER] >> strip_tac >>
 first_x_assum 
 (qspecl_then [‘App(inNf, BIGINTER(inN's))’] assume_tac) >>
 first_x_assum irule >> 
 assume_tac inN_rule0 >> rw[inN's_def] >>
 rw[GSYM inNs_def] >>
 irule inNf_monotone >> first_x_assum accept_tac)
(form_goal
 “App(inNf,inNs) = inNs”));

val IN_EXT_iff = prove_store("IN_EXT_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac 
 >-- (irule IN_EXT >> arw[]) >> arw[])
(form_goal “∀A s1 s2. (∀x:mem(A). IN(x,s1) ⇔ IN(x,s2)) ⇔ s1 = s2”));

val inN_cases1 = 
inN_cases0
    |> mp $ iffRL 
    (IN_EXT_iff 
         |> qspecl [‘N0’,‘App(inNf, inNs)’,‘inNs’])
    |> rewr_rule[inNf_def]
    |> GSYM




(*
assume “SS(App(isLf(X),isLs(X)),xs)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘Pow(N * X)’,‘App(isLf(X),isLs(X))’,
                                ‘App(isLf(X),xs)’]
                    |> undisch
                    |> qspecl [‘xs:mem(Pow(Pow(N * X)))’]
                    |> undisch)
       |> prove_hyp
          (isLf_monotone 
               |> qspecl [‘isLs(X)’,‘xs:mem(Pow(Pow(N * X)))’]
               |> undisch)
       |> prove_hyp
          (isLs_SS |> qspecl [‘xs:mem(Pow(Pow(N * X)))’]
                   |> undisch)
       |> disch “SS(App(isLf(X), xs), xs)”
       |> allI ("xs",mem_sort (rastt "Pow(Pow(N * X))"))
       |> rewr_rule[isLs_cond]
       |> disch “IN(a, App(isLf(X), isLs(X)))”
       |> allI ("a",mem_sort (rastt "Pow(N * X)"))
       |> rewr_rule[GSYM SS_def]



assume “SS(App(Cdf(X),Cds(X)),xs)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘Pow(X) * N’,‘App(Cdf(X),Cds(X))’,
                                ‘App(Cdf(X),xs)’]
                    |> undisch
                    |> qspecl [‘xs:mem(Pow(Pow(X) * N))’]
                    |> undisch)
       |> prove_hyp
          (Cdf_monotone 
               |> qspecl [‘Cds(X)’,‘xs:mem(Pow(Pow(X) * N))’]
               |> undisch)
       |> prove_hyp
          (Cds_SS |> qspecl [‘xs:mem(Pow(Pow(X) * N))’]
                   |> undisch)
       |> disch “SS(App(Cdf(X), xs), xs)”
       |> allI ("xs",mem_sort (rastt "Pow(Pow(X) * N)"))
       |> rewr_rule[Cds_cond]
       |> disch “IN(a, App(Cdf(X), Cds(X)))”
       |> allI ("a",mem_sort (rastt "Pow(X) * N"))
       |> rewr_rule[GSYM SS_def]

assume “SS(App(FIf(X),FIs(X)),xs)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘Pow(X)’,‘App(FIf(X),FIs(X))’,
                                ‘App(FIf(X),xs)’]
                    |> undisch
                    |> qspecl [‘xs:mem(Pow(Pow(X)))’]
                    |> undisch)
       |> prove_hyp
          (FIf_monotone 
               |> qspecl [‘FIs(X)’,‘xs:mem(Pow(Pow(X)))’]
               |> undisch)
       |> prove_hyp
          (FIs_SS |> qspecl [‘xs:mem(Pow(Pow(X)))’]
                   |> undisch)
       |> disch “SS(App(FIf(X), xs), xs)”
       |> allI ("xs",mem_sort (rastt "Pow(Pow(X))"))
       |> rewr_rule[FIs_cond]
       |> disch “IN(a, App(FIf(X), FIs(X)))”
       |> allI ("a",mem_sort (rastt "Pow(X)"))
       |> rewr_rule[GSYM SS_def]


assume “SS(App(inNf,inNs),X)”
       |> rewr_rule[SS_def]
       |> strip_all_and_imp
       |> prove_hyp
          (SS_Trans |> qspecl [‘N0’,‘App(inNf,inNs)’,
                                ‘App(inNf,X)’]
                    |> undisch
                    |> qspecl [‘X:mem(Pow(N0))’]
                    |> undisch)
       |> prove_hyp
          (inNf_monotone 
               |> qspecl [‘inNs’,‘X:mem(Pow(N0))’]
               |> undisch)
       |> prove_hyp
          (inNs_SS |> qspecl [‘X:mem(Pow(N0))’]
                   |> undisch)
       |> disch “SS(App(inNf, X), X)”
       |> allI ("X",mem_sort (rastt "Pow(N0)"))
       |> rewr_rule[inNs_cond]
       |> disch “IN(a, App(inNf, inNs))”
       |> allI ("a",mem_sort (rastt "N0"))
       |> rewr_rule[GSYM SS_def]


rules
*)

(*


assume “SS(App(isLf(X),A),A) ⇒ IN(a,A:mem(Pow(Pow(N * X))))”
|> C mp (assume “SS(App(isLf(X),A),A)”)
|> prove_hyp
   (assume “∀xs. SS(App(isLf(X),xs),xs) ⇒ IN(a,xs)”
           |> qspecl [‘A:mem(Pow(Pow(N * X)))’])
|> disch
   “∀xs. SS(App(isLf(X),xs),xs) ⇒ IN(a,xs)”
|> allI ("a",mem_sort (rastt "Pow(N * X)"))
|> rewr_rule[isLs_cond]
|> rewr_rule[GSYM SS_def]
|> disch “SS(App(isLf(X), A), A)”
|> allI ("A",mem_sort (rastt "Pow(Pow(N * X))"))


assume “SS(App(Cdf(X),A),A) ⇒ IN(a,A:mem(Pow(Pow(X) * N)))”
|> C mp (assume “SS(App(Cdf(X),A),A)”)
|> prove_hyp
   (assume “∀xs. SS(App(Cdf(X),xs),xs) ⇒ IN(a,xs)”
           |> qspecl [‘A:mem(Pow(Pow(X) * N))’])
|> disch
   “∀xs. SS(App(Cdf(X),xs),xs) ⇒ IN(a,xs)”
|> allI ("a",mem_sort (rastt "Pow(X) * N"))
|> rewr_rule[Cds_cond]
|> rewr_rule[GSYM SS_def]
|> disch “SS(App(Cdf(X), A), A)”
|> allI ("A",mem_sort (rastt "Pow(Pow(X) * N)"))


assume “SS(App(FIf(X),A),A) ⇒ IN(a,A:mem(Pow(Pow(X))))”
|> C mp (assume “SS(App(FIf(X),A),A)”)
|> prove_hyp
   (assume “∀xs. SS(App(FIf(X),xs),xs) ⇒ IN(a,xs)”
           |> qspecl [‘A:mem(Pow(Pow(X)))’])
|> disch
   “∀xs. SS(App(FIf(X),xs),xs) ⇒ IN(a,xs)”
(*TODO: BUGBUGBUG!!!!!! if for the quantifier wrongly write X, then BUG!*)
|> allI ("a",mem_sort (rastt "Pow(X)"))
|> rewr_rule[FIs_cond]
|> rewr_rule[GSYM SS_def]
|> disch “SS(App(FIf(X), A), A)”
|> allI ("A",mem_sort (rastt "Pow(Pow(X))"))


assume “SS(App(inNf,A),A) ⇒ IN(a,A:mem(Pow(N0)))”
|> C mp (assume “SS(App(inNf,A),A)”)
|> prove_hyp
   (assume “∀X. SS(App(inNf,X),X) ⇒ IN(a,X)”
           |> qspecl [‘A:mem(Pow(N0))’])
|> disch
   “∀X. SS(App(inNf,X),X) ⇒ IN(a,X)”
|> allI ("a",mem_sort (rastt "N0"))
|> rewr_rule[inNs_cond]
|> rewr_rule[GSYM SS_def]
|> disch “SS(App(inNf, A), A)”
|> allI ("A",mem_sort (rastt "Pow(N0)"))


ind
*)

(*



val isL_rules0 = mk_rules isLf_monotone isLs_SS isLs_cond

assume “SS(App(isLf(X),App(isLf(X),isLs(X))),App(isLf(X),isLs(X))) ⇒ 
        IN(a,App(isLf(X),isLs(X)))”
|> C mp (assume “SS(App(isLf(X),App(isLf(X),isLs(X))),App(isLf(X),isLs(X)))”)
|> prove_hyp 
   (isLf_monotone |> qspecl [‘App(isLf(X),isLs(X))’,‘isLs(X)’]
                  |> undisch)
|> prove_hyp isL_rules0
|> prove_hyp (assume “∀xs. SS(App(isLf(X),xs),xs) ⇒ IN(a,xs)”
                     |> qspecl [‘App(isLf(X),isLs(X))’])
|> prove_hyp ( (iffRL isLs_cond) |> allE (rastt "a:mem(Pow(N * X))")
                                 |> undisch)
|> disch “IN(a,isLs(X))”
|> allI ("a",mem_sort (rastt "Pow(N * X)")) 
|> rewr_rule [GSYM SS_def] 
|> conjI isL_rules0 
|> mp (SS_SS_eq |> qspecl [‘Pow(N * X)’,‘App(isLf(X), isLs(X))’,‘isLs(X)’])


val Cd_rules0 = mk_rules Cdf_monotone Cds_SS Cds_cond

assume “SS(App(Cdf(X),App(Cdf(X),Cds(X))),App(Cdf(X),Cds(X))) ⇒ 
        IN(a,App(Cdf(X),Cds(X)))”
|> C mp (assume “SS(App(Cdf(X),App(Cdf(X),Cds(X))),App(Cdf(X),Cds(X)))”)
|> prove_hyp 
   (Cdf_monotone |> qspecl [‘App(Cdf(X),Cds(X))’,‘Cds(X)’]
                  |> undisch)
|> prove_hyp Cd_rules0
|> prove_hyp (assume “∀xs. SS(App(Cdf(X),xs),xs) ⇒ IN(a,xs)”
                     |> qspecl [‘App(Cdf(X),Cds(X))’])
|> prove_hyp ( (iffRL Cds_cond) |> allE (rastt "a:mem(Pow(X) * N)")
                                 |> undisch)
|> disch “IN(a,Cds(X))”
|> allI ("a",mem_sort (rastt "Pow(X) * N"))
|> rewr_rule [GSYM SS_def]
|> conjI Cd_rules0
|> mp (SS_SS_eq |> qspecl [‘Pow(X) * N’,‘App(Cdf(X), Cds(X))’,‘Cds(X)’])


val FI_rules0 = mk_rules FIf_monotone FIs_SS FIs_cond

assume “SS(App(FIf(X),App(FIf(X),FIs(X))),App(FIf(X),FIs(X))) ⇒ 
        IN(a,App(FIf(X),FIs(X)))”
|> C mp (assume “SS(App(FIf(X),App(FIf(X),FIs(X))),App(FIf(X),FIs(X)))”)
|> prove_hyp 
   (FIf_monotone |> qspecl [‘App(FIf(X),FIs(X))’,‘FIs(X)’]
                  |> undisch)
|> prove_hyp FI_rules0
|> prove_hyp (assume “∀xs. SS(App(FIf(X),xs),xs) ⇒ IN(a,xs)”
                     |> qspecl [‘App(FIf(X),FIs(X))’])
|> prove_hyp ( (iffRL FIs_cond) |> allE (rastt "a:mem(Pow(X))")
                                 |> undisch)
|> disch “IN(a,FIs(X))”
|> allI ("a",mem_sort (rastt "Pow(X)"))
|> rewr_rule [GSYM SS_def]
|> conjI FI_rules0
|> mp (SS_SS_eq |> qspecl [‘Pow(X)’,‘App(FIf(X), FIs(X))’,‘FIs(X)’])


assume “SS(App(inNf,App(inNf,inNs)),App(inNf,inNs)) ⇒ 
        IN(a,App(inNf,inNs))”
|> C mp (assume “SS(App(inNf,App(inNf,inNs)),App(inNf,inNs))”)
|> prove_hyp 
   (inNf_monotone |> qspecl [‘App(inNf,inNs)’,‘inNs’]
                  |> undisch)
|> prove_hyp inN_rules0
|> prove_hyp (assume “∀X. SS(App(inNf,X),X) ⇒ IN(a,X)”
                     |> qspecl [‘App(inNf,inNs)’])
|> prove_hyp ( (iffRL inNs_cond) |> allE (rastt "a:mem(N0)")
                                 |> undisch)
|> disch “IN(a,inNs)”
|> allI ("a",mem_sort (rastt "N0"))
|> rewr_rule [GSYM SS_def]
|> conjI inN_rules0
|> mp (SS_SS_eq |> qspecl [‘N0’,‘App(inNf, inNs)’,‘inNs’])

cases
*)
