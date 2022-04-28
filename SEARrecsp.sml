val Lf0_def = qdefine_fsym("Lf0",[‘A’]) ‘injN(A,O)’

(*
val injN2U_def = proved_th $
e0
cheat
(form_goal “∀A.∃!f:Pow(N * N * A) -> Pow(N * A).
f = f”)
|> spec_all |> uex2ex_rule |> qSKOLEM "injN2U" [‘A’]
*)


val injN2U_def = proved_th $
e0
cheat
(form_goal “∀A f:N -> Pow(N * A).∃!f1: mem(Pow(N * A)).
f1 = f1”)
|> spec_all |> uex2ex_rule |> qSKOLEM "injN2U" [‘f’]

(*
val injN2U_def = 
    qdefine_fsym("injN2U",[‘f:mem(Pow(N * N * A))’]) 
                ‘App(InjN2U(A),f)’ 
*)

val Nd0_def = qdefine_fsym("Nd0",[‘n:mem(N)’,‘a:mem(A)’,
 ‘f:N -> Pow(N * A)’]) ‘injUU(injN(A,Suc(n)),injUU(injA(a),injN2U(f)))’ 


val f = 
 “(nas = Lf0(A) ==> IN(nas,trees)) &
  (!m f. IN(App(f,m),trees) ==>
   !n a. IN(Nd0(n,a,f),trees))”




val isfm_cl = 
  “(nas = F0(A) ==> IN(nas,isfms)) &
  (!p:mem(A). nas = Var0(p) ⇒ IN(nas,isfms)) &
  (∀f0.IN(f0,isfms) & nas = Neg0(f0) ⇒ IN(nas,isfms)) & 
  (∀f1 f2.IN(f1,isfms) & IN(f2,isfms) & nas = Disj0(f1,f2) ⇒ IN(nas,isfms)) &
  (∀f0.IN(f0,isfms) & nas = Diam0(f0) ⇒ IN(nas,isfms))”


val istree_cl = 
 “(nas = Lf0(A) ==> IN(nas,istrees)) &
  (!f m n a. IN(App(f,m),istrees) & nas = Nd0(n,a,f) ==>
   IN(nas,istrees))”


val (istree_incond,x1) = mk_incond istree_cl;
val istreef_ex = mk_fex istree_incond x1;
val istreef_def = mk_fdef "istreef" istreef_ex;
val istreef_monotone = proved_th $
e0
cheat
(form_goal
 “!s1 s2. SS(s1,s2) ==>
 SS(App(istreef(A),s1),App(istreef(A),s2))”);
val istree's_def = mk_prim istreef_def;
val istrees_def = mk_LFP (rastt "istree's(A)");
val istrees_cond = mk_cond istrees_def istree's_def;
val istrees_SS = mk_SS istrees_def istree's_def;
val istree_rules0 = mk_rules istreef_monotone istrees_SS istrees_cond;
val istree_cases0 = mk_cases istreef_monotone istree_rules0 istrees_cond;
val istree_ind0 = mk_ind istrees_cond;
val istree_ind1 = mk_ind1 istreef_def istree_ind0;
val istree_ind2 = mk_ind2 istree_ind1;
val istree_cases1 = mk_case1 istreef_def istree_cases0;
val istree_rules1 = mk_rules1 istreef_def istree_rules0;
val istree_rules2 = mk_rules2 istree_rules1;
val istree_rules3 = mk_rules3 istree_rules2;
