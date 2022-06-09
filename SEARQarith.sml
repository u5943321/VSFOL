
val Z1_def = Thm_2_4 |> qspecl [‘Z’]
                     |> fVar_sInst_th “P(a:mem(Z))”
                        “~(a = Oz)” 
                     |> qSKOLEM "Z1" []
                     |> qSKOLEM "ToZ" []

val ToZ_Inj = Z1_def |> conjE1 

val ToZ_ex_uex = Inj_ex_uex |> qsspecl [‘ToZ’] |> C mp ToZ_Inj 



fun rflip_fconv f = 
    let val eqths = List.map eq_sym (!EqSorts)
        val fc = first_fconv (List.map rewr_fconv eqths)
    in (rand_fconv no_conv $ once_depth_fconv no_conv fc) f
    end

val from_Z1_uex = Z1_def |> conjE2 |> spec_all |> conv_rule rflip_fconv 
                         |> rewr_rule[GSYM ToZ_ex_uex]
                         |> gen_all 




val int1'_def = qsspecl [‘int1’] from_Z1_uex |> rewr_rule[int1_NONZERO] 
                      |> uex2ex_rule
                      |> qSKOLEM "int1'" [] 


val toZ_def = qdefine_fsym("toZ",[‘z1:mem(Z1)’]) ‘App(ToZ,z1)’ |> gen_all
(*already want some theorem here for each application of Thm 2.4*)

val QR_def = AX1 |> qspecl [‘Z * Z1’,‘Z * Z1’]
                 |> fVar_sInst_th “P(ab:mem(Z * Z1),cd:mem(Z * Z1))”
                    “Mulz(Fst(ab),toZ(Snd(cd))) = Mulz(toZ(Snd(ab)),Fst(cd))”
                 |> uex2ex_rule |> qSKOLEM "QR" []

val QR_ER = prove_store("QR_ER",
e0
cheat
(form_goal “ER(QR)”));

val Q_def = Thm_2_4 |> GSYM
                    |>  qspecl [‘Pow(Z * Z1)’]
                    |> fVar_sInst_th “P(s:mem(Pow(Z * Z1)))”
                    “?ab. s = rsi(QR,ab)”
                    |> qSKOLEM "Q" []
                    |> qSKOLEM "iQ" []
                    |> store_as "Q_def";

val QR_iQ_Quot = Q_def |> rewr_rule[GSYM Quot_def]

val QR_iQ_has_umem = ER_Quot_has_umem |> qsspecl [‘QR’,‘iQ’]
                                      |> rewr_rule[QR_ER,QR_iQ_Quot]

val Oq_def = QR_iQ_has_umem |> qsspecl [‘Pair(Oz,int1')’] 
                            |> uex2ex_rule 
                            |> qSKOLEM "Oq" [] 

val absq_def = qdefine_fsym("absq",[]) ‘LINV(iQ,Oq)’ 

val Absq_def = qdefine_fsym("Absq",[‘pair:mem(Z * Z1)’])
‘App(absq o Rsi(QR),pair)’ |> gen_all

val Asq_def = qdefine_psym("Asq",[‘z:mem(Z)’,‘z1:mem(Z1)’]) ‘Absq(Pair(z,z1))’
|> gen_all

(**)
val addq0_def = 

IMAGE()






(*

worry if there is bug for matching function
|> gen_all

cont it
 
val tl = [rastt "QR",rastt "iQ"]
val th =  ER_Quot_has_umem 


match_tl essps 
[mk_var ("i",mk_sort "fun" [mk_var ("Q",set_sort),rastt "Pow(A)"])] 
[rastt "iQ"] emptyvd 

val ve = it 
pmenv (mk_menv ve emptyfvd) 

val (t1,t2,t3,t4) = (el 1 tl',el 2 tl',el 3 tl',el 4 tl')

sort_of t2

th |> spec t1 |> spec t2 |> spec t3

sspecl [‘QR’,‘iQ’]

 qspecl [‘Z * Z1’,‘QR’]
                                      |> qspecl [‘Q’,‘iQ’] 
                                      
                                      |> 
*)

(*need only nonempty, but a concrete term of quotient, to define*)
val Q_ = 
