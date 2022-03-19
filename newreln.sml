




fun simple_genl vsl th = 
    case  vsl of 
        [] => th
      | h :: t => allI h (simple_genl t th) 



fun spec_fVar pdef th = 
    let val (l,r) = dest_dimp pdef 
        val (P,vars0) = dest_fvar l
        val vars = List.map dest_var vars0
    in fVar_Inst_th (P,(vars,r)) th
    end

(* 3. ind_with function and soe examples: redefined match_mp_tac sine the old one used genl, messed up the order of variables. more examples in relnbyhand*)




fun efn (n,s) (f,th) = 
    let 
        val ef = mk_exists n s f
    in
        (ef,existsE (n,s) (assume ef) th)
    end
fun match_mp_tac th (ct:cont,asl:form list,w) = 
    let
        val (impl,gvs) = strip_forall (concl th)
        val (hyp,conseq) = dest_imp impl
        val (con,cvs) = strip_forall (conseq)
        val th1 = (C specl) (undisch ((C specl) th (List.map mk_var gvs))) (List.map mk_var cvs) 
        val (vs,evs) = partition (fn v => HOLset.member(fvf con,v)) gvs
        val th2 = uncurry disch (itlist efn evs (hyp, th1)) 
        val (gl,vs) = strip_forall w
        val env = match_form (fvfl (ant th)) (fVarsl (ant th)) con gl mempty
        val ith = inst_thm env th2
        val gth = simple_genl vs (undisch ith)
        val hyp = fst (dest_imp (concl ith))
    in
        ([(ct,asl,hyp)], sing (mp (disch hyp gth)))
    end


fun ind_with th (ct,asl,w) = 
    let 
        val th1 = undisch th
        val (conc,bvs) = strip_forall (concl th1)
        val (ante,con) = dest_imp conc
                         handle _ => (TRUE,conc)
        val (P,args) = dest_fvar con
        val (b,qvs) = strip_forall w
        val (gante,gcon) = dest_imp b
                           handle _ => (TRUE,b)
        val th2 = fVar_Inst_th (P,(qvs,gcon)) th
    in match_mp_tac th2 (ct,asl,w)
    end


val Sub_mono_eq = prove_store("Sub_mono_eq",
e0
(strip_tac >> ind_with N_ind_P >> rw[Sub_O,Sub_Suc,Suc_def] >> 
 rpt strip_tac (* 2 *) >-- rw[Pre_Suc] >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!m n. Sub(Suc(m),Suc(n)) = Sub(m,n)”));


(*4. reln by hand basically uniform but not absolutely uniform. Any suggested approach of normalising them?*)

val AX4 = new_ax
“?N0 O0:mem(N0) S0:N0~>N0. isFun(S0) & (!n:mem(N0). ~(Eval(S0,n) = O0)) & 
 !n m. Eval(S0,n) = Eval(S0,m) <=> n = m”


val inN_def = define_pred
“!n:mem(N0). inN(n) <=>
(!P.IN(O0,P) &
 (!n0. IN(n0,P) ==> IN(Eval(S0,n0),P)) ==> 
 IN(n,P))”


fun mk_ind0 def = 
    let val ipred = fst (strip_forall $ concl def) |> dest_dimp |> #1
    in
        def |> spec_all |> dimpl2r |> strip_all_and_imp
            |> disch ipred
            |> gen_all
            |> disch_all 
    end

val inN_ind0 = 
    inN_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “inN(n)”
            |> gen_all
            |> disch_all 
            |> gen_all

(*
fun subst_form (f0,f1) f = 
    case view_form f of 
        vPred _ => if eq_form(f,f0) then f1 else f0
      | vConn(co,fl) => mk_conn co (List.map (subst_form (f0,f1)) fl)
      | vQ(q,n,s,b) =>  mk_quant q n s b

*)


val fconjuncts =
   let
      fun aux acc f =
         aux (aux acc ((#2 o dest_conj) f)) ((#1 o dest_conj) f)
         handle _ => f :: acc
   in
      aux []
   end


val IN_def_P_ex = prove_store("IN_def_P_ex",
e0
(strip_tac >>
 qspecl_then [‘A’] strip_assume_tac IN_def_P_expand >>
 qexists_tac ‘s’ >> first_x_assum accept_tac)
(form_goal “!A. ?s:mem(Pow(A)). (!a. P(a) <=> IN(a,s))”));


fun IN2P P0 fm = 
    case view_form fm of
        vPred("IN",true,[t,P]) => if P = P0 then mk_fvar "P" [t] else fm
      | vPred _ => fm
      | vConn(co,fl) => mk_conn co (List.map (IN2P P0) fl)
      | vQ(q,n,s,b) => mk_quant q n s (IN2P P0 b)

fun is_Pow_term t = 
    case view_term t of 
    vFun("Pow",_,_) => true 
     | _ => false 


fun is_mem_Pow s = 
    case view_sort s of
        vSrt("mem",[t]) => is_Pow_term t 
      | _ => false



fun is_mem s = 
    case view_sort s of
        vSrt("mem",[t]) => true
      | _ => false


fun spec_until th = 
    let val ((n,s),b) = dest_forall (concl th)
    in if is_mem s then th else
       spec_until (allE (mk_var (n,s)) th)
    end




fun mk_ind0 def = 
    let val ipred = fst (strip_forall $ concl def) |> dest_dimp |> #1
        val def1 = spec_until (def |> spec_all |> dimpl2r |>
                                   undisch)
        val ((Pn,Ps),b) = dest_forall (concl def1)
    in def1 |> strip_all_and_imp
            |> disch ipred
            |> gen_all
            |> disch_all 
            |> allI (Pn,Ps)
    end

fun mk_ind def0 = 
    let val def = spec_until def0
        val (n,s) = #1 $ dest_forall (concl def)
        val (sname,dset0) = dest_sort s
        val dset = hd dset0
        val ind0 = mk_ind0 def 
(*
        val (P0,body) = dest_forall (concl ind0)
        val goal = IN2P (mk_var P0) body
        val PPow = mk_var("s1",mk_sort "mem" [Pow dset])
*)
        val exl = GSYM IN_def_P_ex |> allE dset
        val ((estr,esort),eb) = dest_exists (concl exl)
        val ind1 = allE (mk_var (estr,esort)) ind0 
        val ind2 = rewr_rule[assume eb] ind1
        val ind3 = existsE (estr,esort) exl ind2
    in ind3 |> gen_all
    end



                      


local 
val l = allE (rastt "N0") IN_def_P_expand
in
val inN_ind = prove_store("inN_ind",
e0
(strip_tac >> rw[inN_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !n:mem(N0). IN(n,P0) <=> P(n)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “(P(O0) &
   (!n0. P(n0) ==> P(Eval(S0,n0))) ==>
  !n.inN(n) ==> P(n))”))
end


fun IN2ipred ipred P0 fm = 
    case view_form fm of
        vPred("IN",true,[t,P]) => if P = P0 then mk_pred ipred [t] else fm
      | vPred _ => fm
      | vConn(co,fl) => mk_conn co (List.map (IN2ipred ipred P0) fl)
      | vQ(q,n,s,b) => mk_quant q n s (IN2ipred ipred P0 b)

fun conj_ths thl = 
    case thl of 
        [a,b] => conjI a b
      | h :: t => conjI h (conj_ths t)
      | _ => raise simple_fail "conj_ths. less than two items";

fun mk_rules def = 
    let val (l,r) = def |> spec_all |> concl |> dest_dimp
        val (ipred,argl) = dest_pred l
        val (P0,body) = dest_forall r
        val cjs = body |> dest_imp |> #1
        val goal = IN2ipred ipred (mk_var P0) cjs
        val goals = fconjuncts goal
        val defc = basic_fconv no_conv (rewr_fconv (spec_all def))
        val iffs = List.map defc goals
        val goals' = List.map (#2 o dest_dimp o concl) iffs 
        val lg = List.map form_goal goals'
        val lg' = List.map (e0 (rpt strip_tac >> 
        first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])) lg
(*need to edit, there may be more than one base case, and more than one step cases*)
        val ths = List.map proved_th lg'
        val l = zip iffs ths
        val ths' = List.map (fn (th1,th2) => dimp_mp_r2l th1 th2) l
    in conj_ths ths'
    end

val inN_rules = prove_store("inN_rules",
e0
(strip_tac >-- (rw[inN_def] >> rpt strip_tac) >>
 rw[inN_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “inN(O0) & 
  (!n. inN(n) ==> inN(Eval(S0,n)))”));

val inN_rules_step = inN_rules |> conjE2


(*inN_cases there is a case that rw does not work and do not know why*)
val inN_cases = prove_store("inN_cases",
e0
(strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!n0. inN(n0) ==> (n0 = O0 |
  (?a. n0 = Eval(S0,a) & inN(a)))’
 >-- (strip_tac >> arw[]) >>
 ind_with inN_ind >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexists_tac ‘O0’ >> rw[inN_rules]) >>
 disj2_tac >> qexists_tac ‘n0'’ >> rw[] >>
 arw[] >> match_mp_tac inN_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[inN_rules] >>
 arw[] >> match_mp_tac inN_rules_step >> arw[])
(form_goal
 “!n0. inN(n0) <=> (n0 = O0 |
  (?a. n0 = Eval(S0,a) & inN(a)))”));



val FI_def = define_pred 
“!X xs:mem(Pow(X)). FI(xs) <=> 
 !P. (IN(Empty(X),P) &
      (!xs. IN(xs,P)==> !x.IN(Ins(x,xs),P))) ==>
     IN(xs,P)”



val FI_ind0 = 
    FI_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “FI(xs:mem(Pow(X)))”
            |> gen_all
            |> disch_all 
            |> gen_all

local 
val l = allE (rastt "Pow(X)") IN_def_P_expand
in
val FI_ind = prove_store("FI_ind",
e0
(strip_tac >> strip_tac >> rw[FI_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !xs:mem(Pow(X)). IN(xs,P0) <=> P(xs)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “!X.(P(Empty(X)) &
   (!xs. P(xs) ==> !x:mem(X).P(Ins(x,xs)))) ==>
  !xs:mem(Pow(X)).FI(xs) ==> P(xs)”))
end

val FI_rules = prove_store("FI_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[FI_def] >> rpt strip_tac) >>
 rw[FI_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “!X. FI(Empty(X))& 
     (!xs:mem(Pow(X)). FI(xs) ==> !x. FI(Ins(x,xs)))”));

val FI_rules_step = FI_rules |> spec_all |> conjE2


val FI_cases = prove_store("FI_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!xs. FI(xs) ==> (xs = Empty(X) |
  (?xs0 x0. xs = Ins(x0,xs0) & FI(xs0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (FI_ind |> allE (rastt "X")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘Empty(X)’,‘x’] >> 
     rw[FI_rules]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘xs'’,‘x’] >> rw[] >> arw[] >>
 match_mp_tac FI_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[FI_rules] >>
 arw[] >> match_mp_tac FI_rules_step >> arw[])
(form_goal
 “!X xs. FI(xs) <=> (xs = Empty(X) |
  (?xs0 x0. xs = Ins(x0,xs0) & FI(xs0)))”));


val Cd_def = define_pred
“!X xs:mem(Pow(X)) n. Cd(xs,n) <=>
(!P.IN(Pair(Empty(X),O),P) &
   (!xs0 n0 x. IN(Pair(xs0,n0),P) & ~IN(x,xs0) ==>
   IN(Pair(Ins(x,xs0),Suc(n0)),P)) ==> 
 IN(Pair(xs,n),P))”


val Cd_ind0 = 
    Cd_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “Cd(xs:mem(Pow(X)),n)”
            |> qgen ‘n’ |> qgen ‘xs’
            |> disch_all 
            |> gen_all 

val Fst_of_Pair = prove_store("Fst_of_Pair",
e0
(rw[GSYM Fst_def,Eval_p1_Pair])
(form_goal
 “!A B a:mem(A) b:mem(B). Fst(Pair(a,b)) = a”));


val Snd_of_Pair = prove_store("Snd_of_Pair",
e0
(rw[GSYM Snd_def,Eval_p2_Pair])
(form_goal
 “!A B a:mem(A) b:mem(B). Snd(Pair(a,b)) = b”));


(* try to always apply Fst_of_Pair/Snd_of_pair.
   figure out a drule of doing this, instead of a tactic.
*)
local 
val l = allE (rastt "Pow(X) * N") IN_def_P_expand |>
spec_fVar “P(xsn:mem(Pow(X) * N)) <=> P(Fst(xsn),Snd(xsn))”
in
val Cd_ind = prove_store("Cd_ind",
e0
(strip_tac >> rw[Cd_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !xs:mem(Pow(X)) n. IN(Pair(xs,n),P0) <=> P(xs,n)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> (* simply arw[] works for previous cases but not for this, since the pattern is different *)
 qby_tac ‘!xs n. P(xs,n) <=> IN(Pair(xs,n),s)’ 
 >-- (rpt strip_tac >> 
      first_x_assum (qspecl_then [‘Pair(xs',n')’] assume_tac) >>
      fs[Fst_of_Pair,Snd_of_Pair]) >>
 arw[])
(form_goal 
 “!X.(P(Empty(X),O) &
     (!xs n x:mem(X). 
      P(xs,n) & (~IN(x,xs)) ==> 
      P(Ins(x,xs),Suc(n)))) ==>
  !xs:mem(Pow(X)) n.Cd(xs,n) ==> P(xs,n)”))
end

val Cd_rules = prove_store("Cd_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[Cd_def] >> rpt strip_tac) >>
 rw[Cd_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> arw[] (*to eliminate the ~IN(x,xs) in the goal, previously did not have it*) >> 
 first_x_assum match_mp_tac >> arw[])
(form_goal
 “!X. Cd(Empty(X),O)& 
     (!xs:mem(Pow(X)) n x. Cd(xs,n) & ~(IN(x,xs)) ==> 
     Cd(Ins(x,xs),Suc(n)))”));

val Cd_rules_step = Cd_rules |> spec_all |> conjE2


val Cd_cases = prove_store("Cd_cases",
e0
(strip_tac >> strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!xs n. Cd(xs,n) ==> ((xs = Empty(X) & n = O) |
  (?xs0 n0 x0. ~(IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) &
  Cd(xs0,n0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (Cd_ind |> allE (rastt "X")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] >> qexistsl_tac [‘Empty(X)’,‘O’,‘x’] >> 
     rw[Cd_rules] >> (*previously the rw [..._rules] solve the goal, but here require the condition not in empty*) 
     rw[Empty_property]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘xs'’,‘n'’,‘x’] >> rw[] >> arw[] >>
 match_mp_tac Cd_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[Cd_rules] >>
 arw[] >> match_mp_tac Cd_rules_step >> arw[])
(form_goal
 “!X xs:mem(Pow(X)) n. Cd(xs,n) <=> ((xs = Empty(X) & n = O) |
  (?xs0 n0 x0. ~(IN(x0,xs0)) & xs = Ins(x0,xs0) & n = Suc(n0) &
   Cd(xs0,n0)))”));




val isL_def = define_pred 
“!A nas:mem(Pow(N * A)). isL(nas) <=>
(!P.IN(Empty(N * A),P) &
   (!nas0. IN(nas0,P) ==>
    !a.IN(Ins(Pair(CARD(nas0),a),nas0),P)) ==> 
 IN(nas,P))”

val isL_ind0 = 
    isL_def |> spec_all |> dimpl2r |> undisch
            |> strip_all_and_imp 
            |> disch “isL(nas:mem(Pow(N * A)))”
            |> gen_all  
            |> disch_all 
            |> gen_all 


local 
val l = allE (rastt "Pow(N * A)") IN_def_P_expand
in
val isL_ind = prove_store("isL_ind",
e0
(strip_tac >> rw[isL_def] >> rpt strip_tac >>
 qsuff_tac
 ‘?P0. !nas:mem(Pow(N * A)). IN(nas,P0) <=> P(nas)’
 >-- (strip_tac >> 
     first_x_assum (qspecl_then [‘P0’] assume_tac) >>
     rfs[]) >>
 strip_assume_tac l >> 
 qexists_tac ‘s’ >> arw[])
(form_goal 
 “!A.(P(Empty(N * A)) &
   (!nas. P(nas) ==> !a:mem(A).P(Ins(Pair(CARD(nas),a),nas)))) ==>
  !nas:mem(Pow(N * A)).isL(nas) ==> P(nas)”))
end


val isL_rules = prove_store("isL_rules",
e0
(strip_tac >> strip_tac 
 >-- (rw[isL_def] >> rpt strip_tac) >>
 rw[isL_def] >> rpt strip_tac >>
 first_assum match_mp_tac >> first_x_assum match_mp_tac >> arw[])
(form_goal
 “!A. isL(Empty(N * A))& 
     (!nas:mem(Pow(N * A)). isL(nas) ==> 
              !a. isL(Ins(Pair(CARD(nas),a),nas)))”));

val isL_rules_step = isL_rules |> spec_all |> conjE2



val isL_cases = prove_store("isL_cases",
e0
(strip_tac >> strip_tac >> dimp_tac >-- 
 (qsuff_tac
 ‘!nas. isL(nas) ==> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))’
 >-- (strip_tac >> arw[]) >>
 ind_with (isL_ind |> allE (rastt "A")) >> strip_tac (* 2 *)
 >-- rw[] >>
 rpt strip_tac (* 2 *) 
 >-- (disj2_tac >> arw[] (*figure out why the arw work here*)>> 
      qexistsl_tac [‘Empty(N * A)’,‘a’] >> 
      rw[isL_rules]) >>
 disj2_tac >> (*if arw[] >> here, then does not work*) 
 qexistsl_tac [‘nas'’,‘a’] >> rw[] >> arw[] >>
 match_mp_tac isL_rules_step >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[isL_rules] >>
 arw[] >> match_mp_tac isL_rules_step >> arw[])
(form_goal
 “!A nas. isL(nas) <=> (nas = Empty(N * A) |
  (?nas0 a0. nas = Ins(Pair(CARD(nas0),a0),nas0) & isL(nas0)))”));




∃f: Pow(X) -> Pow(X). 
  (∀P x. IN(x,App(f,P)) ⇔ (x = O0 | ∃n0. IN(n0,P) ∧ x = SUC n0) )

monotonicity
  (∀P1:mem(Pow(X)) P2. 
   (∀x. IN(x,P1) ⇒ IN(x,P2))  ⇒
   (∀x. IN(x,App(f,P1)) ⇒ IN(x,App(f,P2))) )


Once prove f LFP ⊆ LFP

expand the def of subset:

∃ps:Pow(Pow(X)). (∀p. IN(p,ps) ⇔ 
       (∀x. x = O0 | ∃n0. IN(n0,P) ∧ x = SUC n0 ⇒ IN(x,p)))


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

val BI_Fun = BI_def |> spec_all |> conjE1 

val B1_def = rel2fun_ex |> qspecl 
                        [‘Pow(Pow(A))’,‘Pow(A)’,‘BI(A)’]
                        |> C mp BI_Fun
                        |> ex2fsym0 "B1" ["A"]
                        |> gen_all



val norm_lemma = prove_store("norm_lemma",
e0
(rpt strip_tac >>
 dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum irule >> rw[]) 
 >-- (first_x_assum irule >> disj2_tac >>
      qexists_tac ‘n0’ >> arw[])
 >-- arw[] >>
 arw[] >> first_x_assum irule >> arw[])
(form_goal
 “∀a. (∀x. (x = O0 | 
           ∃n0:mem(N0). IN(n0,a) ∧ x = App(S1,n0))
       ⇒ IN(x,a)) ⇔ 
    (IN(O0,a) ∧ 
     (∀n0. IN(n0,a) ⇒ IN(App(S1,n0),a)) )”));

val inN's_def = 
    IN_def_P_ex |> allE (rastt "Pow(N0)") |> GSYM
                |> fVar_sInst_th “P(a:mem(Pow(N0)))” 
                “∀x. x = O0 | 
                 ∃n0:mem(N0). IN(n0,a) ∧ x = App(S1,n0) ⇒ 
                                                IN(x,a)”
                |> ex2fsym0 "inN's" []
                |> store_as "inN's_def";




LFP = ∩ { X | f X ⊆ X } (* inNs_def *)

assume:
∀X Y. X ⊆ Y ⇒ f X ⊆ f Y

then derive:

f LFP ⊆ LFP   (i.e., a ∈ f LFP ⇒ a ∈ LFP  (* rule *))

a ∈ f LFP ?- a ∈ LFP

a ∈ f LFP ?- a ∈ ∩ { X | f X ⊆ X}

a ∈ f LFP ?- ∀X. f X ⊆ X ⇒ a ∈ X

a ∈ f LFP, f X ⊆ X ?- a ∈ X

a ∈ f LFP, f X ⊆ X, ∩ { X | f X ⊆ X} ⊆ X ?- a ∈ X 

a ∈ f LFP, f X ⊆ X, LEP ⊆ X ?- a ∈ X 

a ∈ f LFP, f X ⊆ X, f LEP ⊆ f X ?- a ∈ X 

a ∈ f LFP, f LEP ⊆ X ?- a ∈ X 


|> fVar_Inst_th ("P",)
∀x. IN(x, App(f,BIGINTER ps)) ⇒ IN(x,BIGINTER ps)


by def of In App

∀x. x = O0 | ∃n0. IN(n0,BIGINTER ps) ∧ x = SUC n0 ⇒
 IN(x,BIGINTER ps)

by def of biginter

∀x. x = O0 | ∃n0. (∀p. IN(p,ps) ⇒ IN(n0,p)) ∧ x = SUC n0 ⇒
 (∀p. IN(p,ps) ⇒ IN(x,p))

∀x. x = O0 | ∃n0. (∀p. (∀x. x = O0 | ∃n0. IN(n0,P) ∧ x = SUC n0 ⇒ IN(x,p)) ⇒ IN(n0,p)) ∧ x = SUC n0 ⇒



inN(n) ⇔ ∀p. IN(p,ps) ⇒ IN(x,p)

rules : IN(O0,LPF) ∧ 
∀n0. IN(n0,LPF) ⇒ IN(n0^+, LPF)


inN's_def

f LFP ⊆ LFP turned into rule:




LFP = ∩ { X | f X ⊆ X }

assume:
∀X Y. X ⊆ Y ⇒ f X ⊆ f Y

then derive:

f LFP ⊆ LFP   (i.e., a ∈ f LFP ⇒ a ∈ LFP  (* rule *))

a ∈ f LFP ?- a ∈ LFP

a ∈ f LFP ?- a ∈ ∩ { X | f X ⊆ X}

a ∈ f LFP ?- ∀X. f X ⊆ X ⇒ a ∈ X

a ∈ f LFP, f X ⊆ X ?- a ∈ X

a ∈ f LFP, f X ⊆ X, ∩ { X | f X ⊆ X} ⊆ X ?- a ∈ X 

a ∈ f LFP, f X ⊆ X, LEP ⊆ X ?- a ∈ X 

a ∈ f LFP, f X ⊆ X, f LEP ⊆ f X ?- a ∈ X 

a ∈ f LFP, f LEP ⊆ X ?- a ∈ X 

QED

!A. f A ⊆ A ⇒ LFP ⊆ A   (* induction *)

f A ⊆ A ?- LFP ⊆ A

f A ⊆ A ?- ∩ { X | f X ⊆ X} ⊆ A

f A ⊆ A ?- ∀a. (∀X. f X ⊆ X ⇒ a ∈ X) ⇒ a ∈ A

f A ⊆ A, ∀X. f X ⊆ X ⇒ a ∈ X |- a ∈ A

f A ⊆ A, f A ⊆ A ⇒ a ∈ A |- a ∈ A

QED


f LFP = LFP    (* cases *)

sufficient to prove LFP ⊆ f LFP, other direction given by above.

a ∈ LFP ?- a ∈ f LFP  

a ∈ ∩ { X | f X ⊆ X} ?- a ∈ f LFP

∀X. f X ⊆ X ⇒ a ∈ X ?- a ∈ f LFP

f (f LFP) ⊆ f LFP ⇒ a ∈ f LFP ?- a ∈ f LFP

f (f LFP) ⊆ f LFP ⇒ a ∈ f LFP, f LFP ⊆ LFP ?- a ∈ f LFP (*by the case above*)

f (f LFP) ⊆ f LFP ⇒ a ∈ f LFP, f (f LFP) ⊆ f LFP ?- a ∈ f LFP

QED




