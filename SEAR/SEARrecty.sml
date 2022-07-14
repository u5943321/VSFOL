



(*

B1 ---i_1-----> A
|               \\
|
B2----i_2 ----> A


*)

use "SEARUF.sml";


val Vof_def = qdefine_fsym("Vof",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘tof(Snd(M))’ |> gen_all


val Rof_def = qdefine_fsym("Rof",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘Fst(M)’ |> gen_all


val Rm_def = qdefine_psym("Rm",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w1:mem(W)’,‘w2:mem(W)’]) ‘IN(Pair(w1,w2),Rof(M))’;

(*Holds at*)
val HAT_def = proved_th $
e0
(strip_tac >> irule 
 (P2fun_uex |> qspecl [‘A’,‘Pow(W)’] 
 |> fVar_sInst_th “P(a:mem(A),s:mem(Pow(W)))”
    “!w.IN(w,s) <=> IN(a,App(Vof(M:mem(Pow(W * W) * Exp(W,Pow(A)))),w))”) >>
 strip_tac >>
 accept_tac
 (IN_def_P |> qspecl [‘W’] 
 |> fVar_sInst_th “P(w:mem(W))”
    “IN(x,App(Vof(M:mem(Pow(W * W) * Exp(W,Pow(A)))),w))”))
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
 ?!f:A->Pow(W). !a w. IN(w,App(f,a)) <=> IN(a,App(Vof(M),w))”)
|> spec_all |> qsimple_uex_spec "HAT" [‘M’]


val satis_dmf = proved_th $
e0
(strip_tac >> irule 
 (P2fun_uex |> qspecl [‘Pow(W)’,‘Pow(W)’] 
 |> fVar_sInst_th “P(s0:mem(Pow(W)),s:mem(Pow(W)))”
    “!w.IN(w,s) <=> 
     ?w0. IN(w0,s0) & Rm(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,w0)”) >>
 strip_tac >>
 accept_tac
 (IN_def_P |> qspecl [‘W’] 
 |> fVar_sInst_th “P(w:mem(W))”
    “?w0. IN(w0,x) & Rm(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,w0)”))
(form_goal
 “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
  ?!f:Pow(W) -> Pow(W). 
  (!s0 w.IN(w,App(f,s0)) <=> ?w0.IN(w0,s0) & Rm(M,w,w0))”)
|> spec_all |> qsimple_uex_spec "sdmf" [‘M’]


val satisf_def = qdefine_fsym("satisf",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘fmrec(Empty(W), HAT(M), COMPL(W), UNION(W), sdmf(M))’
 
val satisf_clause = 
fmrec_clauses |> qspecl [‘Pow(W)’]
              |> qspecl [‘Empty(W)’]
              |> qspecl [‘A’]
              |> qspecl [‘HAT(M:mem(Pow(W * W) * Exp(W,Pow(A))))’]
              |> qspecl [‘COMPL(W)’]
              |> qspecl [‘UNION(W)’]
              |> qspecl [‘sdmf(M)’]
              |> rewr_rule[GSYM satisf_def]

val satis_def0 = qdefine_psym("satis",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w:mem(W)’,‘f:mem(form(A))’]) ‘IN(w,App(satisf(M),f))’;

val satis_def = prove_store("satis_def",
e0
(rw[satis_def0] >> rw[satisf_clause,COMPL_def,UNION_def,Empty_def] >>
 rw[HAT_def] >> rw[satis_dmf] >> 
 strip_tac >> dimp_tac >> strip_tac 
 >-- (qexists_tac ‘w0’ >> arw[]) >>
 qexists_tac ‘v’ >> arw[])
(form_goal 
“(~(satis(M,w,Bot(A)))) & 
 (!a.satis(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,Var(a:mem(A))) <=> 
 IN(a,App(Vof(M),w))) &
 (!f.satis(M,w,Neg(f)) <=> ~ (satis(M,w,f))) & 
 (!f1 f2.satis(M,w,Disj(f1,f2)) <=> (satis(M,w,f1) | satis(M,w,f2))) &
 (!f.satis(M,w,Diam(f)) <=> ?v. Rm(M,w,v) & satis(M,v,f))”));


val SATIS_def = qdefine_psym("SATIS",
[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,‘w:mem(W)’,‘fs:mem(Pow(form(A)))’])
‘!f. IN(f,fs) ==> satis(M,w,f)’

val Top_def = qdefine_fsym("Top",[‘A’]) ‘Neg(Bot(A))’;

val Conj_def = qdefine_fsym("Conj",[‘f1:mem(form(A))’,‘f2:mem(form(A))’]) 
                           ‘Neg(Disj(Neg(f1),Neg(f2)))’ 


val satis_Conj = prove_store("satis_Conj",
e0
(rpt strip_tac >> rw[Conj_def,satis_def] >> once_rw[neg_or_distr] >>
 rw[])
(form_goal “!M w:mem(W) f1:mem(form(A)) f2.
 satis(M,w,Conj(f1,f2)) <=> satis(M,w,f1) & satis(M,w,f2)
 ”));


local
val PE_cl = 
 “(f = Top(A) ==> IN(f,PEs)) &
  (f = Bot(A) ==> IN(f,PEs)) & 
  (!p.f = Var(p) ==> IN(f,PEs)) &
  (!f1 f2. IN(f1,PEs) & IN(f2,PEs) & f = Conj(f1,f2) ==> IN(f,PEs)) & 
  (!f1 f2. IN(f1,PEs) & IN(f2,PEs) & f = Disj(f1,f2) ==> IN(f,PEs)) & 
  (!f0. IN(f0,PEs) & f = Diam(f0) ==> IN(f,PEs))”
in
val (PE_incond,x1) = mk_incond PE_cl;
val PEf_ex = mk_fex PE_incond x1;
val PEf_def = mk_fdef "PEf" PEf_ex;
val PEf_monotone = mk_monotone PEf_def;
val PE's_def = mk_prim PEf_def;
val PEs_def = mk_LFP (rastt "PE's(A)");
val PEs_cond = mk_cond PEs_def PE's_def;
val PEs_SS = mk_SS PEs_def PE's_def;
val PE_rules0 = mk_rules PEf_monotone PEs_SS PEs_cond;
val PE_cases0 = mk_cases PEf_monotone PE_rules0 PEs_cond;
val PE_ind0 = mk_ind PEs_cond;
val PE_ind1 = mk_ind1 PEf_def PE_ind0;
val PE_ind2 = mk_ind2 PE_ind1; 
val PE_cases1 = mk_case1 PEf_def PE_cases0; 
val PE_rules1 = mk_rules1 PEf_def PE_rules0; 
val PE_rules2 = mk_rules2 PE_rules1; 
val PE_rules3 = mk_rules3 PE_rules2;
end

val PE_ind0 = PE_ind2 |> store_as "PE_ind";
val PE_cases0 = PE_cases1 |> store_as "PE_cases";
val PE_rules0 = PE_rules3 |> store_as "PE_rules";

val PE_def0 = qdefine_psym("PE",[‘f:mem(form(A))’]) ‘IN(f,PEs(A))’

val PE_ind = PE_ind0 |> rewr_rule[GSYM PE_def0];
val PE_cases = PE_cases0 |> rewr_rule[GSYM PE_def0];
val PE_rules = PE_rules0 |> rewr_rule[GSYM PE_def0];



val PE_induct = prove_store("PE_induct",
e0
(strip_tac >>
 x_choose_then "s" (assume_tac o conjE1) 
 (IN_def_P_expand |> qspecl [‘form(A)’]) >> arw[] >>
 disch_tac >> 
 match_mp_tac PE_ind >> arw[])
(form_goal
 “!A. P(Top(A)) & P(Bot(A)) & (!p:mem(A). P(Var(p))) &
      (!f1:mem(form(A)) f2. P(f1) & P(f2) ==> P(Conj(f1,f2))) & 
      (!f1:mem(form(A)) f2. P(f1) & P(f2) ==> P(Disj(f1,f2))) & 
      (!f:mem(form(A)).P(f) ==> P(Diam(f))) ==> 
      (!f:mem(form(A)). PE(f) ==> P(f)) ”));


val satis_Bot = satis_def |> conjE1 |> gen_all

val satis_Top = prove_store("satis_Top",
e0
(rw[Top_def,satis_def,satis_Bot])
(form_goal “!A M w:mem(W). satis(M,w,Top(A))”));


val Sim_def = qdefine_psym("Sim",[‘R:W1~>W2’,‘M1:mem(Pow(W1 * W1) * Exp(W1,Pow(A)))’,‘M2:mem(Pow(W2 * W2) * Exp(W2,Pow(A)))’]) 
‘!w1 w2.Holds(R,w1,w2) ==>
 (!p.IN(p,App(Vof(M1),w1)) ==> IN(p,App(Vof(M2),w2))) & 
 (!v. Rm(M1,w1,v) ==> ?v'. Holds(R,v,v') & Rm(M2,w2,v'))’

val PUS_def = qdefine_psym("PUS",[‘f:mem(form(A))’])
‘!W1 W2 R:W1~>W2 M1:mem(Pow(W1 * W1) * Exp(W1,Pow(A))) M2. Sim(R,M1,M2) ==>
 !w1 w2. Holds(R,w1,w2) ==> satis(M1,w1,f) ==> satis(M2,w2,f)’

val PUS_Var = prove_store("PUS_Var",
e0
(rpt strip_tac >> rw[PUS_def,satis_def] >>
 rpt strip_tac >> fs[Sim_def] >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 first_x_assum irule >> arw[])
(form_goal “!A p:mem(A). PUS(Var(p))”));

val PUS_Top = prove_store("PUS_Top",
e0
(rpt strip_tac >> rw[PUS_def,satis_Top])
(form_goal “!A. PUS(Top(A))”));

val PUS_Bot = prove_store("PUS_Bot",
e0
(rpt strip_tac >> fs[PUS_def,satis_Bot])
(form_goal “!A. PUS(Bot(A))”));

val Thm_6_25_r2l0 = prove_store("Thm_6_25_r2l0",
e0
(strip_tac >> ind_with (PE_induct |> spec_all) >>
 rw[PUS_Top,PUS_Bot,PUS_Var] >> 
 once_rw[PUS_def] >> rpt strip_tac (* 3 *)
 >-- (fs[satis_Conj] >> first_x_assum drule >>
      first_x_assum drule >> first_x_assum drule >> arw[] >>
      first_x_assum drule >> first_x_assum drule >> 
      first_x_assum drule >> arw[])
 >-- (fs[satis_def] (* 2 *)
     >-- (disj1_tac >> first_x_assum irule >>
         qexistsl_tac [‘W1’,‘M1’,‘R’,‘w1’] >> arw[]) >>
     disj2_tac >> first_x_assum irule >>
     qexistsl_tac [‘W1’,‘M1’,‘R’,‘w1’] >> arw[]) >>
 fs[satis_def] >>
 drule $ iffLR Sim_def >> 
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexists_tac ‘v'’ >> arw[] >> 
 first_x_assum irule >>
 qexistsl_tac [‘W1’,‘M1’,‘R’,‘v’] >> arw[]
 )
(form_goal “!A f:mem(form(A)). PE(f) ==> PUS(f)”));


val EQV_def = qdefine_psym("EQV",[‘f1:mem(form(A))’,‘f2:mem(form(A))’])
 ‘!W M w:mem(W). satis(M,w,f1) <=> satis(M,w,f2)’


val Thm_6_25_r2l = prove_store("Thm_6_25_r2l",
e0
(rpt strip_tac >> drule Thm_6_25_r2l0 >>
 fs[PUS_def] >> fs[EQV_def])
(form_goal “!A f f0:mem(form(A)). PE(f0) & EQV(f,f0) ==> PUS(f)”));


val Sab_def = qdefine_psym
                  ("Sab",[‘fs:mem(Pow(form(A)))’,‘X:mem(Pow(W))’,‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
                  ‘?x.IN(x,X) & SATIS(M,x,fs)’


val Fsab_def = qdefine_psym
                  ("Fsab",[‘fs:mem(Pow(form(A)))’,‘X:mem(Pow(W))’,‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
                  ‘!ss. Fin(ss) & SS(ss,fs) ==> Sab(ss,X,M)’

(*successor in M*)
val Sucm_def = proved_th $
e0
(rpt strip_tac >>
 accept_tac
 (IN_def_P |> qspecl [‘W’] 
 |> fVar_sInst_th “P(v:mem(W))”
    “Rm(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,v)”))
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
?!sucm. !v. IN(v,sucm) <=> Rm(M,w,v)”) 
|> spec_all |> qsimple_uex_spec "Sucm" [‘M’,‘w’]

val Msat_def = qdefine_psym("Msat",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’]) 
‘!w fs. Fsab(fs,Sucm(M,w),M) ==>  Sab(fs,Sucm(M,w),M) ’

(*True at, takes a letter, gives the set of worlds it holds*)
val Tat_def = proved_th $
e0
(rpt strip_tac >>
  accept_tac
 (IN_def_P |> qspecl [‘W’] 
 |> fVar_sInst_th “P(w:mem(W))”
    “IN(a,App(f0:W->Pow(A),w))”)
 )
(form_goal “!f0:W ->Pow(A). !a.?!ws:mem(Pow(W)).
 !w. IN(w,ws) <=> IN(a,App(f0,w))”)
|> spec_all |> qsimple_uex_spec "Tat" [‘f0’,‘a’]


val fun_mem_ex_iff = prove_store("fun_mem_ex_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
>-- (qexists_tac ‘Tpm(f)’ >> arw[tof_Tpm_inv]) >>
qexists_tac ‘tof(m)’ >> arw[Tpm_tof_inv])
(form_goal “!A B.(?f:A->B. P(f)) <=> ?m:mem(Exp(A,B)). P(tof(m))”));


val mem_fun_ex_iff = prove_store("mem_fun_ex_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
>-- (qexists_tac ‘tof(m)’ >> arw[Tpm_tof_inv]) >>
qexists_tac ‘Tpm(f)’ >> arw[tof_Tpm_inv])
(form_goal “!A B.(?m:mem(Exp(A,B)). P(m)) <=>
 (?f:A->B. P(Tpm(f)))”));




val fun_mem_uex_iff = prove_store("fun_mem_uex_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
>-- (uex_tac >> 
    pop_assum (assume_tac o uex_expand) >> 
    assume_tac (fun_mem_ex_iff 
    |> qspecl [‘A’,‘B’]
    |> fVar_sInst_th “P(g:A->B)”
       “P(g:A ->B) & !g'. P(g') ==> g' = g”) >>
    first_x_assum (drule o iffLR) >>
    pop_assum strip_assume_tac >>
    qexists_tac ‘m’ >> arw[] >>
    rpt strip_tac >>
    irule $ iffLR tof_eq_eq >> first_x_assum irule >>
    arw[]) >>
 uex_tac >>
 pop_assum (assume_tac o uex_expand) >>
 assume_tac (fun_mem_ex_iff 
    |> qspecl [‘A’,‘B’]
    |> fVar_sInst_th “P(g:A->B)”
       “P(g:A ->B) & !g'. P(g') ==> g' = g”) >>
 arw[] >> pop_assum (K all_tac) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘m’ >> arw[] >>
 rpt strip_tac >> 
 first_x_assum (qspecl_then [‘Tpm(g')’] assume_tac) >>
 fs[tof_Tpm_inv] >> first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >> arw[tof_Tpm_inv])
(form_goal “!A B.(?!f:A->B. P(f)) <=> ?!m:mem(Exp(A,B)). P(tof(m))”));


(*
val mem_fun_uex_iff = prove_store("mem_fun_uex_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
>-- (uex_tac >> 
    pop_assum (assume_tac o uex_expand) >> 
    assume_tac (fun_mem_ex_iff 
    |> qspecl [‘A’,‘B’]
    |> fVar_sInst_th “P(g:A->B)”
       “P(g:A ->B) & !g'. P(g') ==> g' = g”) >>
    first_x_assum (drule o iffLR) >>
    pop_assum strip_assume_tac >>
    qexists_tac ‘m’ >> arw[] >>
    rpt strip_tac >>
    irule $ iffLR tof_eq_eq >> first_x_assum irule >>
    arw[]) >>
 uex_tac >>
 pop_assum (assume_tac o uex_expand) >>
 assume_tac (fun_mem_ex_iff 
    |> qspecl [‘A’,‘B’]
    |> fVar_sInst_th “P(g:A->B)”
       “P(g:A ->B) & !g'. P(g') ==> g' = g”) >>
 arw[] >> pop_assum (K all_tac) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘m’ >> arw[] >>
 rpt strip_tac >> 
 first_x_assum (qspecl_then [‘Tpm(g')’] assume_tac) >>
 fs[tof_Tpm_inv] >> first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >> arw[tof_Tpm_inv])
(form_goal “!A B. (?!m:mem(Exp(A,B)). P(m)) <=>
 (?!f:A->B. P(Tpm(f)))”));

*)

val ueV_def = proved_th $
e0
(strip_tac >> assume_tac
 (fun_mem_uex_iff 
 |> qspecl [‘UFs(W)’,‘Pow(A)’]
 |> fVar_sInst_th “P(f:UFs(W)->Pow(A))”
 “!u a. IN(a,App(f:UFs(W)->Pow(A),u)) <=>
  IN(Tat(Vof(M),a),Repu(u))”) >>
 first_x_assum (irule o iffLR) >>
 irule 
 (P2fun_uex|> qspecl [‘UFs(W)’,‘Pow(A)’] 
 |> fVar_sInst_th “P(x:mem(UFs(W)),s:mem(Pow(A)))”
    “!a.IN(a,s) <=> IN(Tat(Vof(M:mem(Pow(W * W) * Exp(W,Pow(A)))),a),Repu(x))”) >>
 strip_tac >> 
 accept_tac
 (IN_def_P |> qspecl [‘A’] 
 |> fVar_sInst_th “P(a:mem(A))”
    “IN(Tat(Vof(M:mem(Pow(W * W) * Exp(W,Pow(A)))),a),Repu(x))”))
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
 ?!f0:mem(Exp(UFs(W),Pow(A))).
  !u a. IN(a,App(tof(f0),u)) <=>  IN(Tat(Vof(M),a),Repu(u))”)
|> spec_all |> qsimple_uex_spec "ueV" [‘M’]

val csee_def = proved_th $
e0
(rpt strip_tac >>
 accept_tac
 (IN_def_P |> qspecl [‘W’] 
 |> fVar_sInst_th “P(w:mem(W))”
    “?v.Rm(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,v) & IN(v,X)”))
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) X. 
 ?!cs:mem(Pow(W)).
 !w. IN(w,cs) <=> ?v.Rm(M,w,v) &  IN(v,X) ”)
|> spec_all |> qsimple_uex_spec "csee" [‘M’,‘X’]


val osee_def = proved_th $
e0
(rpt strip_tac >>
 accept_tac
 (IN_def_P |> qspecl [‘W’] 
 |> fVar_sInst_th “P(w:mem(W))”
    “!v.Rm(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,v) ==> IN(v,X)”))
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) X. 
 ?!cs:mem(Pow(W)).
 !w. IN(w,cs) <=> !v. Rm(M,w,v) ==> IN(v,X)”)
|> spec_all |> qsimple_uex_spec "osee" [‘M’,‘X’]

val ueR_def = proved_th $
e0
(
strip_tac >> accept_tac
(IN_def_P |> qspecl [‘UFs(W) * UFs(W)’] 
     |> fVar_sInst_th “P(u12:mem(UFs(W) * UFs(W)))”
        “!X.IN(X,Repu(Snd(u12))) ==> 
        IN(csee(M:mem(Pow(W * W) * Exp(W,Pow(A))),X),Repu(Fst(u12)))”
     |> conv_rule (depth_fconv no_conv forall_cross_fconv)
     |> rewr_rule[Pair_def']))
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
 ?!R:mem(Pow(UFs(W) * UFs(W))).
   !u1 u2. IN(Pair(u1,u2),R) <=> 
   (!X.IN(X,Repu(u2)) ==> IN(csee(M,X),Repu(u1)))”)
|> spec_all |> qsimple_uex_spec "ueR" [‘M’]

val UE_def = qdefine_fsym("UE",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’])
‘Pair(ueR(M),ueV(M))’


val ufilter_Compl = 
 ufilter_def |> iffLR 
             |> undisch |> conjE2
             |> disch_all |> gen_all
             |> store_as "ufilter_Compl";

val exists_forall_dual = prove_store("exists_forall_dual",
e0
(strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[]) >>
 ccontra_tac >>
 qby_tac ‘!a:mem(A).~P(a)’ 
 >-- (strip_tac >> ccontra_tac >>
     qsuff_tac ‘?a:mem(A). P(a)’ >-- arw[] >> 
     qexists_tac ‘a’ >> arw[]) >>
 fs[])
(form_goal “!A. (?a:mem(A).P(a)) <=>
 ~(!a:mem(A).~P(a))”));

val Prop_5_4_1 = prove_store("Prop_5_4_1",
e0
(rw[GSYM IN_EXT_iff,csee_def,IN_Compl,osee_def] >>
 rpt strip_tac >>
 assume_tac
 (exists_forall_dual |> qspecl [‘W’]
 |> fVar_sInst_th “P(v:mem(W))”
    “Rm(M:mem(Pow(W * W) * Exp(W,Pow(A))),x,v) & IN(v,X)”) >>
 arw[] >> rw[neg_conj_imp])
(form_goal
 “!M:mem(Pow(W * W) * Exp(W,Pow(A))) X. 
  csee(M,X) = Compl(osee(M,Compl(X)))”));

val Prop_5_4_2 = prove_store("Prop_5_4_2",
e0
(rw[GSYM IN_EXT_iff,csee_def,IN_Compl,osee_def] >>
 rpt strip_tac >>
 assume_tac
 (forall_exists_dual |> qspecl [‘W’]
 |> fVar_sInst_th “P(v:mem(W))”
    “Rm(M:mem(Pow(W * W) * Exp(W,Pow(A))),x,v) ==> IN(v,X)”) >>
 arw[] >> rw[neg_imp_conj])
(form_goal
 “!M:mem(Pow(W * W) * Exp(W,Pow(A))) X. 
  osee(M,X) = Compl(csee(M,Compl(X)))”));


val Prop_5_6 = prove_store("Prop_5_6",
e0
(rw[UE_def,ueR_def,Rm_def,Rof_def,Pair_def'] >> 
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule $ iffLR ufilter_Compl >>
     rw[Repu_ufilter] >>
     first_x_assum (qspecl_then [‘Compl(Y)’] assume_tac) >>
     qsuff_tac 
     ‘~IN(csee(M, Compl(Y)), Repu(u))’
     >-- (strip_tac >> ccontra_tac >> 
         first_x_assum drule >> fs[]) >>
     pop_assum (K all_tac) >>
     qsspecl_then [‘u’] assume_tac Repu_ufilter >> 
     drule $ GSYM ufilter_Compl >>
     once_arw[] >> rw[] >>
     pop_assum (K all_tac) >>
     arw[GSYM Prop_5_4_2]) >>
 qsspecl_then [‘v’] assume_tac Repu_ufilter >> 
 drule ufilter_Compl >>
 first_x_assum (drule o iffRL) >>
 first_x_assum (qspecl_then [‘Compl(X)’] assume_tac) >>
 qby_tac ‘~IN(osee(M, Compl(X)), Repu(u))’
 >-- (ccontra_tac >> first_x_assum drule >> fs[]) >>
 qsspecl_then [‘u’] assume_tac Repu_ufilter >>
 drule ufilter_Compl >> 
 first_x_assum 
 (qspecl_then [‘osee(M, Compl(X))’] (assume_tac o GSYM)) >>
 fs[Prop_5_4_1])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) u v. Rm(UE(M),u,v) <=> 
 (!Y. IN(osee(M,Y),Repu(u)) ==> IN(Y,Repu(v)))”));

val ueR_alt = Prop_5_6

val MEQ_def = 
    qdefine_psym("MEQ",[‘M1:mem(Pow(W1 * W1) * Exp(W1,Pow(A)))’,
                        ‘w1:mem(W1)’,
                        ‘M2:mem(Pow(W2 * W2) * Exp(W2,Pow(A)))’,
                        ‘w2:mem(W2)’])
    ‘!f. satis(M1,w1,f) <=> satis(M2,w2,f)’

(*
val plfilter_def = prove_store(""
*)

val pufilter_def = proved_th $
e0
(rpt strip_tac >>
 assume_tac
 (IN_def_P |> qspecl [‘Pow(A)’] 
 |> fVar_sInst_th “P(s:mem(Pow(A)))”
    “IN(a:mem(A),s)”) >>
 arw[])
(form_goal “!A a:mem(A).
 ?!ss. !s. IN(s,ss) <=> IN(a,s)”)
|> spec_all |> qsimple_uex_spec "pufilter" [‘a’]

val pufilter_filter = prove_store("pufilter_filter",
e0
(rw[filter_def,pufilter_def,IN_Inter,EMPTY_def,Whole_def] >>
 rpt strip_tac (* 2 *)
 >-- (ccontra_tac >> 
     first_x_assum (qspecl_then [‘a’] assume_tac) >> 
     arw[]) >>
 fs[SS_def] >> first_x_assum irule >> arw[]
 )
(form_goal “!A a:mem(A). filter(pufilter(a))”));


val pufilter_ufilter = prove_store("pufilter_ufilter",
e0
(rw[ufilter_def,pufilter_filter,pufilter_def,IN_Compl])
(form_goal “!A a:mem(A). ufilter(pufilter(a))”));

val Repu_eq_eq = prove_store("Repu_eq_eq",
e0
(rw[Repu_def] >> 
assume_tac (UFs_def|> conjE1 |> gen_all) >>
rpt strip_tac >>
first_x_assum (qspecl_then [‘W’] assume_tac) >>
fs[Inj_def] >> first_x_assum irule >> arw[])
(form_goal “!W u1:mem(UFs(W)) u2. Repu(u1) = Repu(u2) ==>
 u1 = u2”));

val Pft_def = proved_th $
e0
(rpt strip_tac >> 
 qsuff_tac ‘?uw:mem(UFs(W)).
 !ws.IN(ws,Repu(uw)) <=> IN(w0,ws)’
 >-- (rpt strip_tac >>
     uex_tac >> qexists_tac ‘uw’ >> arw[] >>
     rpt strip_tac >>
     irule Repu_eq_eq >> 
     arw[GSYM IN_EXT_iff]) >>
 assume_tac
 (from_UFs |> gen_all |> qsspecl [‘pufilter(w0:mem(W))’]) >>
 fs[pufilter_ufilter] >>
 qexists_tac ‘b’ >> pop_assum (assume_tac o GSYM)  >>
 arw[pufilter_def]
 )
(form_goal “!W w0:mem(W). ?!uw:mem(UFs(W)).
 !ws.IN(ws,Repu(uw)) <=> IN(w0,ws)”)
|> spec_all |> qsimple_uex_spec "Pft" [‘w0’]

(*satis worlds*)
val SW_def = proved_th $
e0
(strip_tac >> irule
 (P2fun_uex |> qspecl [‘form(A)’,‘Pow(W)’] 
 |> fVar_sInst_th “P(f:mem(form(A)),s:mem(Pow(W)))”
    “!w. IN(w,s) <=> satis(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,f)”) >>
 strip_tac >> accept_tac
 (IN_def_P |> qspecl [‘W’] 
 |> fVar_sInst_th “P(w:mem(W))”
    “satis(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,x)”))
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).
 ?!sws:form(A) -> Pow(W). !f w. IN(w,App(sws,f)) <=> satis(M,w,f)”)
|> spec_all |> qsimple_uex_spec "SW" [‘M’]

val Sw_def = qdefine_fsym("Sw",[‘M:mem(Pow(W * W) * Exp(W,Pow(A)))’,
                                        ‘f:mem(form(A))’]) 
                          ‘App(SW(M),f)’


val Prop_5_5_2 = prove_store("Prop_5_5_2",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff] >> strip_tac >>
 rw[osee_def,Inter_def,INTER_def] >> 
 dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum drule >> arw[])
 >--  (first_x_assum drule >> arw[]) 
 >> first_x_assum irule >> arw[])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) X Y:mem(Pow(W)). osee(M,Inter(X,Y)) = Inter(osee(M,X),osee(M,Y))”));
 
val Sw_Bot = prove_store("Sw_Bot",
e0
(rw[GSYM IN_EXT_iff,Sw_def,SW_def,Empty_def,satis_Bot])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). Sw(M,Bot(A)) = Empty(W)”));

val Sw_Var = prove_store("Sw_Var",
e0
(rw[GSYM IN_EXT_iff,Sw_def,SW_def,HAT_def,satis_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) p. 
                  Sw(M,Var(p)) = App(HAT(M),p)”));

val Vof_UE = prove_store("Vof_UE",
e0
(rw[UE_def,Vof_def,Pair_def'])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). Vof(UE(M)) = tof(ueV(M))”));


val HAT_Tat =prove_store("HAT_Tat",
e0
(rw[GSYM IN_EXT_iff,HAT_def,Tat_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) p. App(HAT(M), p) = Tat(Vof(M), p)”));


val Sw_Neg = prove_store("Sw_Neg",
e0
(rw[GSYM IN_EXT_iff,Sw_def,SW_def,satis_def,Compl_def,COMPL_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) f. 
                  Sw(M,Neg(f)) = Compl(Sw(M,f))”));




val Sw_Disj = prove_store("Sw_Disj",
e0
(rw[GSYM IN_EXT_iff,Sw_def,SW_def,satis_def,Union_def,UNION_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). 
                  Sw(M,Disj(f1,f2)) = Union(Sw(M,f1),Sw(M,f2))”));



val Rm_UE = prove_store("Rm_UE",
e0
(rw[Rm_def,Rof_def,UE_def,Pair_def',ueR_def] >> rpt strip_tac >> rw[])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) u u'.Rm(UE(M),u,u') <=>
 !X. IN(X,Repu(u')) ==> IN(csee(M,X),Repu(u))”));

val csee_Sw_DIAM = prove_store("csee_Sw_DIAM",
e0
(rw[GSYM IN_EXT_iff,csee_def,Sw_def,SW_def,satis_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) f.csee(M,Sw(M,f)) = 
 Sw(M,Diam(f))”));


val Prop_5_8 = prove_store("Prop_5_8",
e0
(strip_tac >> strip_tac >> 
 ind_with (form_induct |> qspecl [‘A’]) >>
 rpt strip_tac 
 >-- rw[satis_Bot,Sw_Bot,Empty_NOTIN_UFs]
 >-- rw[Sw_Var,satis_def,Vof_UE,ueV_def,HAT_Tat]
 >-- arw[satis_def,Sw_Neg,Compl_Repu]
 >-- arw[Sw_Disj,satis_def,Union_Repu] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (rw[satis_def] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 rw[Prop_5_6] >>
 qby_tac ‘?u0'. !Y. IN(Y,u0') <=> IN(osee(M,Y),Repu(u))’
 >-- accept_tac (IN_def_P_ex |> GSYM |> qspecl [‘Pow(W)’]
 |> fVar_sInst_th “P(Y:mem(Pow(W)))”
    “ IN(osee(M:mem(Pow(W * W) * Exp(W,Pow(A))),Y),Repu(u))”)
 >> pop_assum strip_assume_tac >>
 qby_tac ‘FIP(Ins(Sw(M,f0), u0'))’ >-- 
 (rw[GSYM Union_Sing] >>
 qby_tac ‘~(Sing(Sw(M, f0)) = Empty(Pow(W)))’
 >-- rw[Sing_NONEMPTY] >> 
 qcases ‘u0' = Empty(Pow(W))’ >--
 (arw[Union_Empty2] >> 
 qby_tac ‘~(Sw(M, f0) = Empty(W))’ 
 >-- (ccontra_tac >>
     qsuff_tac ‘Sw(M, Diam(f0)) = Empty(W)’ 
     >-- (strip_tac >> fs[Empty_NOTIN_UFs])  >>
     fs[GSYM IN_EXT_iff,SW_def,Sw_def,satis_def,Empty_def] >>
     strip_tac >> ccontra_tac >> fs[]) >>
 irule FIP_Sing >> arw[]
  ) >>
 irule FIP_closed_under_Inter >>
 arw[] >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     rw[Prop_5_5_2] >>
     irule Inter_IN_ufilter >>
     arw[Repu_ufilter]) >> strip_tac (* 2 *)
 >-- (rw[IN_Sing] >> rpt strip_tac >> arw[Inter_same]) >>
 rpt strip_tac >>
 qby_tac ‘IN(Inter(Sw(M, Diam(f0)),osee(M,b)),Repu(u))’ 
 >-- (irule Inter_IN_ufilter >> arw[Repu_ufilter]) >>
 qsspecl_then [‘u’] assume_tac Repu_ufilter >>
 drule IN_UF_NONEMPTY >>
 first_x_assum drule >>
 fs[GSYM IN_NONEMPTY] >>
 rw[GSYM IN_NONEMPTY,IN_Inter] >>
 fs[IN_Sing] >> rw[Sw_def,SW_def] >>
 fs[IN_Inter] >> fs[Sw_def,SW_def,osee_def,satis_def] >>
 first_x_assum drule >>  
 qexists_tac ‘v’ >> arw[]) >>
 qby_tac ‘?u'. SS(Ins(Sw(M,f0), u0'),Repu(u'))’
 >-- (irule Prop_5_3 >> arw[] >>
     qsspecl_then [‘u’] assume_tac Repu_ufilter >>
     fs[ufilter_def,filter_def]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘u'’ >> last_x_assum (assume_tac o GSYM) >> arw[] >>
 qby_tac ‘IN(Sw(M, f0), Repu(u'))’
 >-- (fs[SS_def,Ins_def] >>
     first_x_assum (qspecl_then [‘Sw(M, f0)’] assume_tac) >> fs[]) >>
 arw[] >> rpt strip_tac >>
 last_assum (drule o iffRL) >> fs[SS_def] >>
 first_x_assum irule >> arw[Ins_def])>>
fs[satis_def] >> rw[GSYM csee_Sw_DIAM] >> 
first_x_assum (drule o iffRL) >> fs[Rm_UE] >>
first_x_assum irule >> arw[])
(form_goal “!W M:mem(Pow(W * W) * Exp(W,Pow(A))) phi u.
 IN(Sw(M,phi),Repu(u)) <=> satis(UE(M),u,phi) ”));

val Prop_5_7 = prove_store("Prop_5_7",
e0
(rpt strip_tac >> rw[MEQ_def] >> rw[GSYM Prop_5_8] >>
 rw[Pft_def,Sw_def,SW_def])
(form_goal “!W M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
 MEQ(M,w,UE(M),Pft(w))”));

(*⊢ FIP A J ∧ J ̸= ∅ ⇒ ∃ U . ultrafilter U J ∧ A ⊆ U*)
(*
(rw[FIP_def] >> rpt strip_tac >> ccontra_tac >>
 fs[GSYM IN_EXT_iff,Empty_def,BIGINTER_def] >> 
 qby_tac ‘ss = Sing(Empty(A)) | ss = Empty(Pow(A))’ >-- cheat >>
 pop_assum strip_assume_tac (* 2 *)
 >-- fs[] >> fs[IN_BIGINTER,Sing_def,Sg_def]
     first_x_assum (qspecl_then [‘Sing(Empty(A))’] assume_tac) >>
     fs[Sing_def,Sg_def,SS_def] >> fs[GSYM Sing_def] >>
     qby_tac ‘Fin(Sing(Empty(A)))’ >-- cheat >> fs[] >>
     qby_tac ‘~(!x. ~(x = Empty(A)))’ >-- cheat >> fs[] >>
     cheat (*exists x:mem(A)*) 
 fs[] )
“!A. EMPTY(A) ==> !ss:mem(Pow(Pow(A))). ~FIP(ss)”
*)

val SATIS_Sing = prove_store("SATIS_Sing",
e0
(rw[SATIS_def,IN_Sing] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac >> arw[] >>
 first_x_assum irule >> rw[])
(form_goal “!M w:mem(W) f:mem(form(A)). SATIS(M,w,Sing(f)) <=> satis(M,w,f)”));



val Fin_Inter = prove_store("Fin_Inter",
e0
(rpt strip_tac (* 2 *)
 >-- (irule Fin_SS >> qexists_tac ‘s1’ >> arw[Inter_SS]) >>
 irule Fin_SS >> qexists_tac ‘s2’ >> arw[Inter_SS])
(form_goal “!A s1:mem(Pow(A)) s2. Fin(s1) | Fin(s2) ==> Fin(Inter(s1,s2))”));


val SATIS_Union = prove_store("SATIS_Union",
e0
(rw[SATIS_def,IN_Union] >> rpt strip_tac >> 
 dimp_tac >> rpt strip_tac (* 3 *)
 >-- (first_x_assum irule >> arw[]) 
 >-- (first_x_assum irule >> arw[]) 
 >-- (first_x_assum drule >> arw[]) >>
 first_x_assum drule >> arw[])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) w s1 s2.
 SATIS(M,w,Union(s1,s2)) <=> SATIS(M,w,s1) & SATIS(M,w,s2)”))



val only_see_whole_world = prove_store("only_see_whole_world",e0
(rw[GSYM IN_EXT_iff,Whole_def,osee_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))).osee(M, Whole(W)) = Whole(W)”));

val SATIS_Empty = prove_store("SATIS_Empty",
e0
(rw[SATIS_def,Empty_def])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
 SATIS(M,w,Empty(form(A)))”));


val BIGCONJ_EXISTS = prove_store("BIGCONJ_EXISTS",
e0
(ind_with (Fin_induct |> qspecl [‘form(A)’]) >>
 rw[SATIS_Empty] >> rpt strip_tac 
 >-- (qexists_tac ‘Top(A)’ >> rw[satis_Top]) >>
 qexists_tac ‘Conj(x,ff)’>>
 arw[satis_Conj,SATIS_def,Ins_def] >>
 rw[imp_or_distr] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac >> arw[] (* 2 *)
 >-- (first_x_assum irule >> arw[])
 >-- (first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
     fs[]) >>
 first_x_assum (qspecl_then [‘f’] strip_assume_tac) >>
 first_x_assum irule >> arw[])
(form_goal 
 “!s.Fin(s) ==> ?ff. 
  !W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
   satis(M,w,ff) <=> SATIS(M,w,s)”));




val SS_Union_of = prove_store("SS_Union_of",
e0
(rw[SS_def,IN_Union] >> rpt strip_tac >>
 first_x_assum drule >> arw[] )
(form_goal “!A s1:mem(Pow(A)) s2 s. SS(s1,s) & SS(s2,s) ==> SS(Union(s1,s2),s)”));

val Prop_5_9 = prove_store("Prop_5_9",
e0
(strip_tac >> rw[Msat_def] >> rpt strip_tac >>
 qcases ‘EMPTY(W)’ >-- 
 (fs[Fsab_def] >>
 first_x_assum (qspecl_then [‘Empty(form(A))’] assume_tac) >>
 fs[Fin_Empty,Empty_SS,Sab_def] >>
 qsspecl_then [‘x’] assume_tac Repu_ufilter >>
 fs[ufilter_def,filter_def]) >>
 qby_tac
 ‘?D0. !ws. IN(ws,D0) <=>
  ?ss. Fin(ss) & SS(ss,fs) & 
       (!w. IN(w,ws) <=> SATIS(M,w,ss))’
 >-- accept_tac (IN_def_P_ex |> GSYM |> qspecl [‘Pow(W)’]
 |> fVar_sInst_th “P(ws:mem(Pow(W)))”
    “?ss. Fin(ss) & SS(ss,fs) & 
       (!w. IN(w,ws) <=> SATIS(M:mem(Pow(W * W) * Exp(W,Pow(A))),w,ss))”) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘?Ys. !Y. IN(Y,Ys) <=> IN(osee(M,Y),Repu(w))’
 >-- accept_tac (IN_def_P_ex |> GSYM |> qspecl [‘Pow(W)’]
 |> fVar_sInst_th “P(Y:mem(Pow(W)))”
    “IN(osee(M:mem(Pow(W * W) * Exp(W,Pow(A))),Y),Repu(w))”)
 >> pop_assum strip_assume_tac >>
 qby_tac ‘FIP(Union(D0,Ys))’ >-- 
 (irule FIP_closed_under_Inter >> rpt strip_tac (* 5 *)
  >-- (rfs[Prop_5_5_2] >>
      irule Inter_IN_ufilter >> fs[Repu_ufilter]) 
  >-- (rfs[] >>
      qexists_tac ‘Union(ss,ss')’ >> rpt strip_tac 
      >-- (irule $ iffRL Fin_Union >> arw[]) 
      >-- (irule SS_Union_of >> arw[]) >>
      rw[IN_Inter] >> arw[] >>rw[SATIS_Union]) 
  >-- (arw[GSYM IN_NONEMPTY] >>
      qexists_tac ‘Whole(W)’ >>
      rw[only_see_whole_world] >>
      qsspecl_then [‘w’] assume_tac Repu_ufilter >>
      drule Whole_IN_ufilter >> arw[]) 
  >-- (arw[GSYM IN_NONEMPTY] >>
      qexistsl_tac [‘Whole(W)’,‘Empty(form(A))’] >>
      rw[Fin_Empty,Empty_SS,SATIS_def,Whole_def,Empty_def])
  >-- (rfs[Fsab_def] >>
      drule BIGCONJ_EXISTS >> fs[] >>
      arw[GSYM IN_NONEMPTY,IN_Inter] >>
      first_x_assum (qspecl_then [‘ss’] assume_tac) >>
      rfs[] >> fs[Sab_def] >>
      first_assum (drule o iffRL) >>
      qby_tac ‘SS(Ys,Repu(x))’
      >-- fs[Sucm_def,Prop_5_6,SS_def] >>
      fs[SS_def] >> 
      qby_tac ‘IN(b,Repu(x))’ 
      >-- (first_assum irule >> arw[]) >>
      qby_tac ‘a = Sw(M,ff)’
      >-- arw[GSYM IN_EXT_iff,Sw_def,SW_def] >> 
      qby_tac ‘IN(Inter(a,b),Repu(x))’
      >-- (irule Inter_IN_ufilter >> arw[Repu_ufilter] >>
          irule $ iffRL Prop_5_8 >> 
          arw[]) >>
      qsspecl_then [‘x’] assume_tac Repu_ufilter >>
      drule IN_UF_NONEMPTY >>
      first_x_assum drule >>
      fs[GSYM IN_NONEMPTY] >>
      qexists_tac ‘a'’ >> fs[IN_Inter] >>
      rfs[]))>>
 qby_tac ‘?w'. SS(Union(D0,Ys),Repu(w'))’
 >-- (irule Prop_5_3 >> arw[]) >> 
 pop_assum strip_assume_tac >>     
 rw[Sab_def] >> qexists_tac ‘w'’ >>
 strip_tac (* 2 *)
 >-- (rw[Sucm_def,Prop_5_6] >> rpt strip_tac >>
     first_x_assum (drule o iffRL) >>
     qsuff_tac ‘SS(Ys,Repu(w'))’ 
     >-- (arw[SS_def] >> rpt strip_tac >> first_x_assum drule >> arw[]) >>
     irule SS_Trans >>
     qexists_tac ‘Union(D0,Ys)’ >> arw[] >>
     rw[SS_Union]) >>
 rw[SATIS_def,GSYM Prop_5_8] >> 
 rpt strip_tac >>
 qsuff_tac ‘IN(Sw(M, f), D0)’ 
 >-- (strip_tac >> fs[SS_def,IN_Union] >> 
     first_x_assum irule >> arw[]) >>
 arw[] >>
 qexists_tac ‘Sing(f)’ >> rw[Fin_Sing] >>
 arw[SS_def,Sing_def,Sg_def] >>
 rpt strip_tac >-- arw[] >>
 rw[Sw_def,SW_def,GSYM Sing_def,SATIS_Sing])
(form_goal “!M:mem(Pow(W * W) * Exp(W,Pow(A))). Msat(UE(M))”));

val PE_Conj = PE_rules |> conjE2 |> conjE2 |> conjE2 |> conjE1

val PE_BIGCONJ = prove_store("PE_BIGCONJ",
e0
(ind_with (Fin_induct |> qspecl [‘form(A)’]) >>
 rw[SATIS_Empty] >> rpt strip_tac 
 >-- (qexists_tac ‘Top(A)’ >> rw[satis_Top,PE_rules]) >>
 qby_tac
 ‘!f. IN(f,xs0) ==> PE(f)’
 >-- (rpt strip_tac >>
     first_x_assum (qspecl_then [‘f’] assume_tac) >>
     rfs[Ins_def]) >>
 first_x_assum drule >> fs[] >> 
 qby_tac ‘PE(x)’ 
 >-- (last_x_assum irule >> rw[Ins_def]) >>
 qexists_tac ‘Conj(x,ff)’ >> rpt strip_tac (* 2 *)
 >-- (irule PE_Conj >> arw[]) >> 
 arw[satis_Conj,SATIS_def,Ins_def] >>
 rw[imp_or_distr] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac >> arw[] (* 2 *)
 >-- (first_x_assum irule >> arw[])
 >-- (first_x_assum (qspecl_then [‘x’] strip_assume_tac) >>
     fs[]) >>
 first_x_assum (qspecl_then [‘f’] strip_assume_tac) >>
 first_x_assum irule >> arw[])
(form_goal 
 “!s.Fin(s) ==> 
     (!f. IN(f,s) ==> PE(f)) ==>
?ff. PE(ff) & 
  !W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
   satis(M,w,ff) <=> SATIS(M,w,s)”));

val PE_Disj = PE_rules |> conjE2 |> conjE2 
                       |> conjE2 |> conjE2
                       |> conjE1

val PE_BIGDISJ = prove_store("PE_BIGDISJ",
e0
(ind_with (Fin_induct |> qspecl [‘form(A)’]) >>
 rw[SATIS_Empty,Empty_def] >> rpt strip_tac 
 >-- (qexists_tac ‘Bot(A)’ >> rw[satis_Bot,PE_rules] >>
      rpt strip_tac >> ccontra_tac >>
      pop_assum (x_choose_then "a" assume_tac) >>
      (*tactic BUG!!!!!!! if fs[], then 
         ERR
     ("sort of the variable to be abstract has extra variable(s)", [], [W],
      []) raised*)
      arw[]) >>
 qby_tac
 ‘!f. IN(f,xs0) ==> PE(f)’
 >-- (rpt strip_tac >>
     first_x_assum (qspecl_then [‘f’] assume_tac) >>
     rfs[Ins_def]) >>
 first_x_assum drule >> fs[] >> 
 qby_tac ‘PE(x)’ 
 >-- (last_x_assum irule >> rw[Ins_def]) >>
 qexists_tac ‘Disj(x,ff)’ >> rpt strip_tac (* 2 *)
 >-- (irule PE_Disj >> arw[]) >> 
 arw[satis_def,SATIS_def,Ins_def] >>
 rw[imp_or_distr] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac >> arw[] (* 4 *)
 >-- (qexists_tac ‘x’ >> arw[])
 >-- (qexists_tac ‘f’ >> arw[])
 >-- rfs[] >>
 disj2_tac >> qexists_tac ‘f’ >> arw[])
(form_goal 
 “!s.Fin(s) ==> 
     (!f. IN(f,s) ==> PE(f)) ==>
?ff. PE(ff) & 
  !W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
   satis(M,w,ff) <=> ?f.IN(f,s) & satis(M,w,f)”));


(* Z v1 v2 iff ∀ φ. PE φ ∧ M1, v1 􏲖 φ ⇒ M2, v2 􏲖 φ is a simulation. *)

val PE_Diam = PE_rules |> conjE2 |> conjE2
                       |> conjE2 |> conjE2 |> conjE2

val Thm_6_22 = prove_store("Thm_6_22",
e0
(rpt strip_tac >>
 strip_assume_tac (AX1 |> qspecl [‘W1’,‘W2’] 
 |> fVar_sInst_th “P(v1:mem(W1),v2:mem(W2))”
 “!phi:mem(form(A)). PE(phi) ==> 
          satis(M1,v1:mem(W1),phi) ==> satis(M2,v2:mem(W2),phi)”
 |> uex2ex_rule) >>
 qexists_tac ‘R’ >> arw[] >> rw[Sim_def] >>
 rpt gen_tac >> disch_tac >>
 qby_tac ‘!p. IN(p,App(Vof(M1),w1')) ==> IN(p,App(Vof(M2),w2'))’ 
 >-- (rw[GSYM satis_def] >> strip_tac >>
     first_x_assum (drule o iffLR) >>
     first_x_assum (qspecl_then [‘Var(p)’] assume_tac) >>
     fs[PE_rules]) >> arw[] >> rpt strip_tac >>
 qby_tac ‘?d. !phi. IN(phi,d) <=> 
              PE(phi) & satis(M1,v,phi)’ >-- 
 (accept_tac (IN_def_P_ex |> GSYM |> qspecl [‘form(A)’] 
 |> fVar_sInst_th “P(phi:mem(form(A)))”
    “PE(phi:mem(form(A))) & satis(M1,v:mem(W1),phi)”)) >>
 pop_assum strip_assume_tac >> fs[Msat_def] >> 
 rfs[] >> 
 qsuff_tac ‘Sab(d,Sucm(M2,w2'),M2)’ 
 >-- (rw[Sab_def] >> strip_tac >> qexists_tac ‘x’ >>
     fs[Sucm_def] >> fs[SATIS_def] >> rpt strip_tac >>
     first_x_assum irule >> arw[]) >> 
 fs[Msat_def] >> first_x_assum irule >>
 rw[Fsab_def,Sab_def] >> rpt strip_tac >>
 drule PE_BIGCONJ >>
 qby_tac ‘!f. IN(f,ss) ==> PE(f)’ 
 >-- (rpt strip_tac >> fs[SS_def] >>
     first_x_assum drule >> rfs[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 pop_assum (assume_tac o GSYM) >> 
 arw[] >> 
 rw[Sucm_def,GSYM satis_def] >> first_x_assum irule >>
 strip_tac >-- (irule PE_Diam >> arw[]) >>
 rw[satis_def] >> qexists_tac ‘v’ >> arw[] >> 
 pop_assum (assume_tac o GSYM) >> arw[SATIS_def] >>
 rpt strip_tac >> fs[SS_def] >>
 qby_tac ‘IN(f,d)’ >-- (first_x_assum irule >> arw[]) >>
 rfs[])
(form_goal “!M1 M2.Msat(M1) & Msat(M2) ==> 
 !w1:mem(W1) w2:mem(W2). (!f:mem(form(A)).PE(f) ==> satis(M1,w1,f) ==> satis(M2,w2,f)) ==>
 ?R. Sim(R,M1,M2) & Holds(R,w1,w2)”));

 
val MCOMPACT_def = 
qdefine_psym("MCOMPACT",[])
‘!A fs:mem(Pow(form(A))).
  (!ffs. SS(ffs,fs) & Fin(ffs) ==> 
  ?W M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
   SATIS(M,w,ffs)) ==>
  ?W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
   SATIS(M,w,fs) ’

val Thm_6_23 = prove_store("Thm_6_23",
e0
cheat
(form_goal
 “!fs:mem(Pow(form(A))).
  (!ffs. SS(ffs,fs) & Fin(ffs) ==> 
  ?W M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
   SATIS(M,w,ffs)) ==>
  ?W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
   SATIS(M,w,fs) ”));



val ENT_def = qdefine_psym("ENT",[‘phis:mem(Pow(form(A)))’,‘psi:mem(form(A))’])
‘!W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. 
 SATIS(M,w,phis) ==> satis(M,w,psi)’



val satis_Neg = prove_store("satis_Neg",
e0
(rw[satis_def])
(form_goal
 “!M:mem(Pow(W * W) * Exp(W,Pow(A))) w.satis(M, w, Neg(f)) <=> ~satis(M, w, f)”));


val Ent_def = qdefine_psym("Ent",[‘phi:mem(form(A))’,‘psi:mem(form(A))’])
‘!W M:mem(Pow(W * W) * Exp(W,Pow(A))) w. satis(M,w,phi) ==> satis(M,w,psi)’


val SATIS_SS = prove_store("SATIS_SS",
e0
(rpt strip_tac >> fs[SS_def,SATIS_def] >> 
 rpt strip_tac >> first_x_assum irule >> first_x_assum irule >> arw[])
(form_goal “!s1 s2. SS(s1,s2) ==>
 !M:mem(Pow(W * W) * Exp(W,Pow(A))) w.SATIS(M,w,s2) ==> SATIS(M,w,s1) ”))


val Thm_6_24 = prove_store("Thm_6_24",
e0
(rpt strip_tac >> ccontra_tac >>
 assume_tac
 (exists_forall_dual |> qspecl [‘Pow(form(A))’]
 |> fVar_sInst_th “P(ffs:mem(Pow(form(A))))”
    “SS(ffs:mem(Pow(form(A))), fs) & Fin(ffs) & ENT(ffs, phi)”) >>
 fs[] >>
 pop_assum (K all_tac) >>
 qsuff_tac 
 ‘?W M w:mem(W). SATIS(M,w,Ins(Neg(phi),fs))’ 
 >-- (strip_tac >> fs[ENT_def] >>
     qby_tac ‘SS(fs,Ins(Neg(phi),fs))’ 
     >-- rw[SS_Ins] >>
     drule SATIS_SS >> first_x_assum drule >> 
     first_x_assum drule >>
     qby_tac ‘IN(Neg(phi),Ins(Neg(phi),fs))’ 
     >-- rw[Ins_def] >>
     fs[SATIS_def] >> first_x_assum drule >> fs[satis_Neg]) >>
 irule Thm_6_23 >> 
 rpt strip_tac >>
 first_x_assum (qsspecl_then [‘Del(ffs,Neg(phi))’] assume_tac) >>
 qby_tac
 ‘SS(Del(ffs, Neg(phi)), fs)’ 
 >-- (drule SS_Ins_Del >> fs[]) >>
 qby_tac ‘Fin(Del(ffs, Neg(phi)))’ 
 >-- (irule Fin_Del >> arw[]) >>
 fs[] >> fs[ENT_def] >>
 (*repeatly apply the dual of ? and !*)
 qby_tac
 ‘?W M w:mem(W). SATIS(M, w, Del(ffs, Neg(phi))) & ~satis(M, w, phi)’ 
 >-- (ccontra_tac >>
     qsuff_tac ‘!W M w:mem(W). SATIS(M, w, Del(ffs, Neg(phi))) ==> satis(M, w, phi)’ >-- arw[] >>
     rpt strip_tac >> ccontra_tac >>
     qsuff_tac
     ‘?W M w:mem(W). SATIS(M, w, Del(ffs, Neg(phi))) & ~satis(M, w, phi)’
     >-- arw[] >>
     qexistsl_tac [‘W’,‘M’,‘w’] >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘W’,‘M’,‘w’] >> rw[SATIS_def] >>
 rpt strip_tac >> qcases ‘f = Neg(phi)’ (* 2 *)
 >-- arw[satis_Neg] >>
 qby_tac ‘IN(f,Del(ffs,Neg(phi)))’ 
 >-- arw[Del_def] >>
 fs[SATIS_def] >> first_x_assum irule >> arw[] )
(form_goal
 “!fs:mem(Pow(form(A))) phi.ENT(fs,phi) ==>
  ?ffs. SS(ffs,fs) & Fin(ffs) & ENT(ffs,phi)”));



val PEC_def = proved_th $
e0
(rpt strip_tac >>
 accept_tac
 (IN_def_P |> qspecl [‘form(A)’] 
 |> fVar_sInst_th “P(phi:mem(form(A)))”
    “PE(phi) & Ent(f,phi:mem(form(A)))”))
(form_goal “!A f:mem(form(A)). ?!pec.
 !phi. IN(phi,pec) <=> PE(phi) & Ent(f,phi)”)
|> spec_all |> qsimple_uex_spec "PEC" [‘f’]

val Fin_ENT_PE = prove_store("Fin_ENT_PE",
e0
(qsuff_tac
 ‘!fs. Fin(fs) ==> (!f. IN(f,fs) ==> PE(f))==> 
 ?phi:mem(form(A)).PE(phi) &
       !W M w:mem(W).SATIS(M,w,fs) <=> satis(M,w,phi)’
 >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
 ind_with (Fin_induct |> qspecl [‘form(A)’]) >>
 rw[Empty_def] >> strip_tac (* 2 *)
 >-- (rw[SATIS_Empty] >> qexists_tac ‘Top(A)’ >>
     rw[PE_rules,satis_Top]) >>
 rw[Ins_def] >> rpt strip_tac >>
 qby_tac 
 ‘!f. IN(f,xs0) ==> PE(f)’ 
 >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 rw[SATIS_def,Ins_def] >> 
 qexists_tac ‘Conj(x,phi)’ >>
 rw[satis_Conj] >>
 rpt strip_tac (* 2 *)
 >-- (irule PE_Conj >> arw[] >> 
     last_x_assum irule >> arw[]) >>
 dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum irule >> rw[]) 
 >-- (first_x_assum (irule o iffLR) >>
     rw[SATIS_def] >> rpt strip_tac >>
     first_x_assum irule >> arw[])
 >-- fs[] >>
 qsuff_tac ‘SATIS(M,w,xs0)’ 
 >-- (rw[SATIS_def] >> rpt strip_tac >>
     first_x_assum irule >> arw[]) >>
 arw[])
(form_goal
 “!fs. Fin(fs) & (!f. IN(f,fs) ==> PE(f))==> 
 ?phi:mem(form(A)).PE(phi) &
       !W M w:mem(W).SATIS(M,w,fs) <=> satis(M,w,phi)”));

val SATIS_PEC = prove_store("SATIS_PEC",
e0
(rw[SATIS_def] >> rpt strip_tac >>
 fs[PEC_def,Ent_def] >> first_x_assum irule >> arw[])
(form_goal “!f M:mem(Pow(W * W) * Exp(W,Pow(A))) w.
 satis(M,w,f) ==> SATIS(M,w,PEC(f)) ”));


(*
val Fin_Bij = prove_store("Fin_Bij",
e0
()
(form_goal “”));


val Fin_Inj_Whole = prove_store("Fin_Inj_Whole",
e0
(strip_tac >>
 ind_with (Fin_induct |> qspecl [‘B’]) >>
 )
(form_goal “!B s. Fin(s) ==> s = Whole(B) ==>
 !A f:A->B. Inj(f) ==> Fin(Whole(A))”));
*)

val Del_Fin = prove_store("Del_Fin",
e0
(rpt strip_tac >>
 qcases ‘IN(a,s)’ 
 >-- (drule Fin_Ins >>
     first_x_assum (qspecl_then [‘a’] assume_tac) >>
     drule Ins_Del >> fs[]) >> 
 drule NOTIN_Del >> fs[])
(form_goal “!A s a:mem(A). Fin(Del(s,a)) ==>Fin(s)”));


val Fin_Inj0 = prove_store("Fin_Inj0",
e0
(strip_tac >> ind_with (Fin_induct |> qspecl [‘B’]) >>
 flip_tac >> rw[IMAGE_eq_Empty] >>
 rpt strip_tac (* 2 *)
 >-- arw[Fin_Empty] >> 
 qcases ‘IN(x,xs0)’ 
 >-- (drule Ins_absorb >> fs[] >>
     first_x_assum drule >> first_x_assum irule >> arw[]) >>
 qby_tac ‘?!a. IN(a,ss) & App(f,a) = x’ 
 >-- (fs[GSYM IN_EXT_iff,IMAGE_def,Ins_def] >>
     first_x_assum (qspecl_then [‘x’] assume_tac) >>
     fs[] >>
     uex_tac >> qexists_tac ‘a’ >> arw[] >>
     rpt strip_tac >> 
     fs[Inj_def] >> first_x_assum irule >> arw[]) >>
 pop_assum (strip_assume_tac o uex_expand) >> 
 first_x_assum (qsspecl_then [‘f’,‘Del(ss,a)’] assume_tac) >>
 rfs[] >>
 qsuff_tac ‘IMAGE(f, Del(ss, a)) = xs0’ 
 >-- (strip_tac >> first_x_assum drule >>
     drule Del_Fin >> arw[]) >>
 drule Inj_IMAGE_Del >> arw[] >>
 drule Del_Ins >> arw[])
(form_goal “!B s. Fin(s) ==> !A f:A->B ss. s = IMAGE(f,ss) ==>
 Inj(f) ==> Fin(ss)”));

val Fin_Inj = prove_store("Fin_Inj",
e0
(rpt strip_tac >>
 drule Fin_Inj0 >> 
 first_x_assum irule >>
 qexists_tac ‘f’ >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !ss:mem(Pow(A)) . Fin(IMAGE(f,ss)) ==>
 Fin(ss)”));


(*
val Fin_IMAGE = prove_store("Fin_IMAGE",
e0
cheat
(form_goal “!A ss:mem(Pow(A)). Fin(ss) ==>
 !B f:A->B. Fin(IMAGE(f,ss))”));
*)




val Thm_6_25_l2r = prove_store("Thm_6_25_l2r",
e0
(rpt strip_tac >> 
 qsuff_tac
 ‘ENT(PEC(f),f)’
 >-- (strip_tac >>
     drule Thm_6_24 >> pop_assum strip_assume_tac >>
     qby_tac ‘!f.IN(f,ffs) ==> PE(f)’ 
     >-- (fs[SS_def,PEC_def] >> rpt strip_tac >> first_x_assum drule >>
         arw[]) >>
     qsspecl_then [‘ffs’] assume_tac Fin_ENT_PE >>
     rfs[] >> qexists_tac ‘phi’ >> arw[] >>
     rw[EQV_def] >> pop_assum (assume_tac o GSYM) >> arw[] >>
     rpt strip_tac >> dimp_tac (* 2 *)
     >-- (strip_tac >> qsuff_tac ‘SATIS(M,w,PEC(f))’
          >-- (match_mp_tac SATIS_SS  >> arw[]) >>
          irule SATIS_PEC >> arw[]) >>
     qpick_x_assum ‘ENT(ffs, f)’ assume_tac >>
     fs[ENT_def]) >>
 rw[ENT_def] >> rpt strip_tac >>
 qby_tac
 ‘?G. !psi. IN(psi,G) <=>?psi0. psi = Neg(psi0) & PE(psi0) & ~(satis(M,w,psi0))’
 >-- accept_tac (IN_def_P |> qspecl [‘form(A)’]
              |> fVar_sInst_th “P(psi:mem(form(A)))”
                 “?psi0:mem(form(A)). psi = Neg(psi0) & PE(psi0) & 
                                      ~(satis(M,w:mem(W),psi0))”
              |> uex2ex_rule) >>
 pop_assum strip_assume_tac >>
 qby_tac 
 ‘!ss.SS(ss,Ins(f,G)) &  Fin(ss) ==>
  ?V M1:mem(Pow(V * V) * Exp(V,Pow(A))) v.SATIS(M1,v,ss)’
 >-- (rpt strip_tac >> ccontra_tac >>
     qby_tac
     ‘?ss0. !f0. IN(f0,ss0) <=> 
      IN(Neg(f0),Del(ss,f))’ 
     >-- accept_tac (IN_def_P |> qspecl [‘form(A)’]
              |> fVar_sInst_th “P(f0:mem(form(A)))”
                 “IN(Neg(f0),Del(ss,f:mem(form(A))))”
              |> uex2ex_rule) >> 
     pop_assum strip_assume_tac >>
     qby_tac ‘Fin(ss0)’ >-- 
     (irule Fin_Inj >>
     qexistsl_tac [‘form(A)’,‘NEG(A)’] >>
     rw[NEG_Inj] >> irule Fin_SS >>
     qexists_tac ‘Del(ss,f)’ >>
     rw[SS_def,GSYM Neg_def,IMAGE_def] >> 
     rpt strip_tac (* 2 *)
     >-- rfs[] >>
     irule Fin_Del >> arw[]) >>
     qby_tac
     ‘!psi0.IN(Neg(psi0),G) ==> PE(psi0) & ~satis(M,w,psi0)’
     >-- (arw[] >> rw[Neg_eq_eq] >> rpt strip_tac >> rfs[] >> arw[]) >>
     qby_tac ‘SS(Del(ss,f),G)’ >--
     (irule SS_Ins_Del >> arw[])  >> 
     qby_tac ‘!f0. IN(f0,ss0) ==> PE(f0)’ 
     >-- (rpt strip_tac >> drule $ iffLR SS_def >> 
          first_x_assum (drule o iffLR) >> 
          qsuff_tac ‘PE(f0) & ~satis(M,w,f0)’ 
          >-- (strip_tac >> arw[]) >>
          first_x_assum irule >> 
          drule $ iffLR SS_def >> first_x_assum irule >> arw[]) >>
     qby_tac ‘?ff. PE(ff) & !V M1:mem(Pow(V * V) * Exp(V,Pow(A))) v.
              satis(M1,v,ff) <=> ?f0. IN(f0,ss0) & satis(M1,v,f0)’
     >-- (irule PE_BIGDISJ >> arw[]) >>
     pop_assum strip_assume_tac >>
     qby_tac ‘IN(ff,PEC(f))’ 
     >-- (rw[PEC_def] >> arw[] >> rw[Ent_def] >>
          arw[] >> rpt strip_tac >> ccontra_tac >>
          qsuff_tac ‘?V M1 v:mem(V). SATIS(M1,v,ss)’
          >-- arw[] >>
          qexistsl_tac [‘W'’,‘M'’,‘w'’] >>
          qby_tac ‘!f1. IN(f1,Del(ss,f)) ==> satis(M',w',f1)’ 
          >-- (rpt strip_tac >>
              qby_tac ‘?f0. f1 = Neg(f0)’ >-- 
              (fs[SS_def] >>
              first_x_assum drule >>
              rfs[]>> qexists_tac ‘psi0’ >> rw[]) >> fs[] >>
              fs[] >> ccontra_tac  >>
              qby_tac ‘?f0. IN(Neg(f0),Del(ss,f)) & satis(M',w',f0)’ 
              >-- (qexists_tac ‘f0’ >> arw[] >> fs[satis_Neg]) >>
              first_x_assum opposite_tac) >>
          rw[SATIS_def] >> rpt strip_tac >>
          qcases ‘f' = f’ 
          >-- arw[] >>
          qby_tac ‘IN(f',Del(ss,f))’ >-- arw[Del_def] >>
          first_x_assum drule >> arw[]) >>
     qby_tac ‘satis(M,w,ff)’ 
     >-- (rev_drule $ iffLR SATIS_def >>
         first_x_assum drule >> arw[]) >>
     qby_tac ‘?f0. IN(f0,ss0) & satis(M,w,f0)’ 
     >-- (first_x_assum (irule o iffLR) >> arw[]) >>
     pop_assum strip_assume_tac >> 
     qby_tac ‘!f0.IN(f0,ss0) ==> ~satis(M,w,f0)’ 
     >-- (rpt strip_tac >> 
         last_x_assum $ drule o iffLR >> 
         qby_tac ‘IN(Neg(f0'),G)’
         >-- (qsuff_tac ‘SS(Del(ss,f),G)’
             >-- (rw[SS_def] >> rpt strip_tac >>
                 first_x_assum irule >> arw[]) >>
             arw[]) >>
         pop_assum mp_tac >> arw[] >> strip_tac >>
         fs[Neg_eq_eq]) >>
     first_x_assum drule >> fs[])>>
 drule Thm_6_23 >> pop_assum strip_assume_tac >>
 qby_tac ‘!psi. PE(psi) ==> satis(M',w',psi) ==> satis(M,w,psi)’ 
 >-- (qsuff_tac ‘!psi.PE(psi) ==> ~satis(M,w,psi) ==> ~satis(M',w',psi)’
     >-- (rpt strip_tac >> ccontra_tac >> 
         first_x_assum drule >> first_x_assum drule >> fs[]) >>
     rpt strip_tac >>
     qby_tac ‘IN(Neg(psi),G)’ 
     >-- (first_x_assum (irule o iffRL) >>
         qexists_tac ‘psi’ >> arw[]) >> 
     drule $ iffLR SATIS_def >>
     first_x_assum (qsspecl_then [‘Neg(psi)’] assume_tac) >>
     rfs[Ins_def,satis_Neg]) >>
 qby_tac
 ‘?R. Sim(R,UE(M'),UE(M)) & Holds(R,Pft(w'),Pft(w))’
 >-- (irule Thm_6_22 >> rw[Prop_5_9] >> rpt strip_tac >>
     qby_tac ‘satis(M',w',f')’ 
     >-- (qsspecl_then [‘M'’,‘w'’] assume_tac Prop_5_7 >>
         fs[MEQ_def]) >>
     qby_tac ‘satis(M,w,f')’
     >-- (first_x_assum irule >> arw[]) >>
     qsspecl_then [‘M’,‘w’] assume_tac Prop_5_7 >>
     fs[MEQ_def]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘satis(M',w',f)’
 >-- (drule $ iffLR SATIS_def >> 
     first_x_assum (qsspecl_then [‘f’] assume_tac) >>
     fs[Ins_def]) >>
 qby_tac ‘satis(UE(M'),Pft(w'),f)’ 
 >-- (qsspecl_then [‘M'’,‘w'’] assume_tac Prop_5_7 >> fs[MEQ_def]) >>
 qby_tac ‘satis(UE(M),Pft(w),f)’ 
 >-- (drule $ iffLR PUS_def >> first_x_assum drule >>
     first_x_assum drule >> first_x_assum drule >> arw[]) >>
 qsspecl_then [‘M’,‘w’] assume_tac Prop_5_7 >> fs[MEQ_def])
(form_goal “!A f:mem(form(A)). PUS(f) ==> ?f0. PE(f0) & EQV(f,f0)”))

val Thm_6_25_iff = prove_store("Thm_6_25_iff",
e0
(rpt strip_tac >> dimp_tac >> disch_tac 
 >-- (drule Thm_6_25_l2r >> arw[]) >>
 irule Thm_6_25_r2l >> pop_assum strip_assume_tac >>
 qexists_tac ‘f0’ >> arw[])
(form_goal “!A f:mem(form(A)). PUS(f) <=> ?f0. PE(f0) & EQV(f,f0)”))

(*
the set of A-surreal should be subset of 

{functions from a subset of B to surreal} * 
{functions from a subset of B to surreal} 

B -> B opt?

construct set of surreals? 

a set of surreal is an element in

Pow(Exp(B,Pow(B) + 1) * Exp(B,Pow(B) + 1))

{0} := Sing(\b.NONE,\b.NONE)

if s is a set of surreals, then for all s'.

if !a b. IN((a,b),s') ==>
 a encodes a set of surreals in s,
 b encodes a set of surreals in s.
 under extra condition,
 then s' is a set of surreals.


So how to say: a encodes a set of surreals in s?

a surreal is a pair of functions B -> Pow(B) + 1, decode a function
B -> Pow(B) + 1 as a set of surreals.

For each b, decode the corresponding Pow(B) as a surreal.

B to be regarded as a universe of sets, closed under taking power set. 
so a subset of B is a set of such universe. 

a: B -> Pow(B) + 1, is a set indexed by a subset of B, for every b which is not sent to *, b is sent to some Pow(B), which is a set of elements in B, we require such a set to be a subset of 


if some
1:= ()

 A surreal = Exp(B,A surreal + 1) * Exp(B,A surreal + 1)

0 := (\b,NONE),(\b,NONE)
1 := (\CHOICE B. 0), 

B is the set contain all P^n A

{({},{})} empty maps is a set of surreal,

given {(L,R) | ..}is a set surreal, 

{}





*)
