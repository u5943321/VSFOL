val NPAIR_def = proved_th $
e0
(cheat)
(form_goal “?f:N * N -> N.Inj(f)”)
|> qSKOLEM "NPAIR" []

val npair_def = qdefine_fsym("npair",[‘n1:mem(N)’,‘n2:mem(N)’])
‘App(NPAIR,Pair(n1,n2))’

val f = 
 “(nx = Pair(O,x0:mem(X)) ==> IN(nx,Nind)) &
  (!)
  (!nx0. IN(nx0,Nind) & nx = Pair(Suc(Fst(nx0)),App(f0:X->X,Snd(nx0)))
    ==> IN(nx,Nind))”
local

val num1_def = qdefine_fsym("num1",[]) ‘Suc(O)’
val num2_def = qdefine_fsym("num2",[]) ‘Suc(num1)’
val num3_def = qdefine_fsym("num3",[]) ‘Suc(num2)’
val num4_def = qdefine_fsym("num4",[]) ‘Suc(num3)’


basic_fconv no_conv disj_imp_undistr_fconv 

“(A ==>D) & (B ==> D) & (C ==> D)”

 val f = 
 “(f = O ==> IN(f,isfms)) &
  (!p. f = Add(Mul(p,num4),num1) ==> IN(f,isfms)) &
  (!f0. IN(f0,isfms) & f = Add(Mul(f0,num4),num2) ==> IN(f,fms)) ”

val isfm_cl = 
 “(f = O ==> IN(f,isfms)) &
  (!p. f = Add(Mul(p,num4),num1) ==> IN(f,isfms)) &
  (!f0. IN(f0,isfms) & f = Add(Mul(f0,num4),num2) ==> IN(f,isfms)) &
  (!f1 f2. IN(f1,isfms) & IN(f2,isfms) & 
           f = Add(Mul(npair(f1,f2),num4),num3) ==> IN(f,isfms)) &
  (!f0. IN(f0,isfms) & f = Add(Mul(f0,num4),num4) ==> IN(f,isfms))”
in
val (isfm_incond,x1) = mk_incond isfm_cl;
val isfmf_ex = mk_fex isfm_incond x1;
val isfmf_def = mk_fdef "isff" isfmf_ex;
val isfmf_monotone = mk_monotone isfmf_def;
val isfm's_def = mk_prim isfmf_def;
val isfms_def = mk_LFP (rastt "isf's");
val isfms_cond = mk_cond isfms_def isfm's_def;
val isfms_SS = mk_SS isfms_def isfm's_def;
val isfm_rules0 = mk_rules isfmf_monotone isfms_SS isfms_cond;
val isfm_cases0 = mk_cases isfmf_monotone isfm_rules0 isfms_cond;
val isfm_ind0 = mk_ind isfms_cond;
val isfm_ind1 = mk_ind1 isfmf_def isfm_ind0;
val isfm_ind2 = mk_ind2 isfm_ind1;
val isfm_cases1 = mk_case1 isfmf_def isfm_cases0;
val isfm_rules1 = mk_rules1 isfmf_def isfm_rules0;
val isfm_rules2 = mk_rules2 isfm_rules1;
val isfm_rules3 = mk_rules3 isfm_rules2;
end


val isfm_ind = isfm_ind2 |> store_as "isfm_ind";
val isfm_cases = isfm_cases1 |> store_as "isfm_cases";
val isfm_rules = isfm_rules3 |> store_as "isfm_rules";
