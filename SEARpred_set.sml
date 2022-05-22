
val tof_Tpm_inv = prove_store("tof_Tpm_inv",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT] >>
 rw[GSYM tof_def,Tpm_def])
(form_goal
 “!A B f:A->B. tof(Tpm(f))  = f”));


val Tpm_tof_inv = prove_store("Tpm_tof_inv",
e0
(flip_tac >> rpt strip_tac >> irule is_Tpm >>
 rw[tof_def])
(form_goal
 “!A B f:mem(Exp(A,B)). Tpm(tof(f))  = f”));


val Tpm_eq_eq = prove_store("Tpm_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >> 
 irule $ iffLR FUN_EXT >>
 once_rw[GSYM Tpm_def] >> arw[])
(form_goal “!A B f1:A->B f2. Tpm(f1) = Tpm(f2) <=> f1 = f2”));


val tof_eq_eq = prove_store("tof_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘Tpm(tof(f)) = Tpm(tof(g))’ >-- arw[]>> fs[Tpm_tof_inv] )
(form_goal
 “!A B f:mem(Exp(A,B)) g. tof(f)  = tof(g) <=> f = g”));



val IN_Sing = prove_store("IN_Sing",
e0
(rw[Sing_def,Sg_def])
(form_goal “!A a0 a:mem(A). IN(a,Sing(a0)) <=> a = a0”));
