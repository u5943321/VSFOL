(*
If !a. P(a) ==> ?!x1 ... xn:mem(A_1 * ... * A_n). a = constr(x1,...,xn)

then for every b0:mem(B), ?!f:A->B.
 !a. P(a) ==> !x1 ... xn. a = constr(x1,...,xn) ==> App(f,a) = 

need notion of sequence uex
*)


val th0 = proved_th $
e0
cheat
(form_goal “!k:mem(K). P(k) ==> ?a:mem(A) b:mem(B). k = App(mk,Pair(a,b)) &
 !a1 b1. k = App(mk,Pair(a1,b1)) ==> a1 = a & b1 = b”) 


(* want output to be 
 !X x0 g0:A * B ->X. ?!g:K ->X. 
 !k. P(k) ==> !a b. k = App(f,Pair(a,b)) ==> App(g,k) = App(g0,Pair(a,b))
     ELSE ==> App(g,k) = x0

“”
“k = App(f, Pair(a,b))”

 !. ?!


if exist unique a b, then exists a function K -> K * A * B?

declare the function constant locally?
*)


(*need a function takes 
 !k. P(k) ==> ?!x. Q(x) 
 and a x0.
produce a function 
 !k. P(k) ==> Q(App(f,k)) &
     ~P(k) ==> App(f,k) = x0

but not applied here, since then we need choose base point and the defined whole function will have extra parameters.

*)


val th0 = proved_th $
e0
cheat
(form_goal “!k:mem(K). P(k) ==> ?!ab:mem(A*B). k = App(mk,ab)”) 

K * X * A * B -> X

K -> K * X * A * B

Pow(X) -> X. 
if singleton then content, else x0


P(k,

k defined a subset of K * X * A * B such that 
k = App(mk,ab) & x = App(g0,ab)

\k. content(IMAGE(f,ambset(k)))


K -> A * B

“!k ab.  k = App(mk,ab) ==> App(f,k) = App(f0,ab)
    
           ”

let the image of

“!k. P(k) ==> ?!x. ?ab. k = App(mk,ab) & x = App(g0,ab)”
     ~P(k) ==> App(f,k) = x0.


“!k. ?!kab. Fst(kab) = k & k = App()”


!k. P(k) ==> ?!s:mem(Pow(A * B)). !ab. IN(ab,s) <=> k = App(mk,ab)


s can be declared as constant since it is unique on nose and Pow(A * B) is alwasys inhabited.

?!xs s. xs = context(IMAGE(f,s)) & 
      !ab. IN(ab,s) <=> k = App(mk,ab)

content (IMAGE(f,s))

val f0 =
“!kab:mem(K * A * B). 
  (Fst(kab) = App(mk,Snd(kab)) ==>
  App(f, kab) = App(g0,Snd(kab))) & 
  (ELSE ==> App(f,kab) = x0:mem(X))”

val f1 = normalise_lambda_input f0

“\k. context(IMAGE(f,PREIM(mk,k)))”



(*content*)
val content_def = proved_th $
e0
cheat
(form_goal 
 “!X x0.?!f:Pow(X) ->X. 
  !s x. s = Sing(x) ==> App(f,s) = x &
        (!x. ~(s = Sing(x)) ==> App(f,s) = x0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "content" [‘x0’] 
|> gen_all 

val content_Sing = content_def 
|> qsspecl [‘x0:mem(X)’,‘Sing(x:mem(X))’,‘x:mem(X)’]
|> rewr_rule[] |> qgenl [‘X’,‘x0’,‘x’] 


val ctt_def = qdefine_fsym("ctt",[‘s:mem(Pow(X))’,‘x0:mem(X)’])
‘App(content(x0),s)’ |> gen_all


val From_def = qdefine_psym("From",[‘f:A->B’,‘b:mem(B)’])
‘~(FIB(f,b) = Empty(A))’


define_lambda
“!k:mem(K). 
     (From(mk1,k) ==> 
     App(f,k) = ctt(IMAGE(g1:A * B->X,FIB(mk1,k)),x0)) &
     (From(mk2,k) ==>
     App(f,k) = ctt(IMAGE(g2:A * B->X,FIB(mk2,k)),x0)) &
     (ELSE ==> App(f,k) = x0)”

(*
val cstr1_def = 
 fun_tm_compr_uex ("ax0",mem_sort (rastt "A * X")) 
 (rastt "tuple4(num1,SOME(Fst(ax0)),Tpm(TNull(A+1)),Tpm(Conat(Snd(ax0:mem(A * X)))))") |> uex2ex_rule |> qSKOLEM "cstr1" [‘A’,‘X’] 
*)
(*
val cstr1_def = 
 fun_tm_compr_uex ("a",mem_sort (rastt "A")) 
 (rastt "tuple4(num1,SOME(a:mem(A)),Tpm(TNull(A+1)),Tpm(Conat(x0:mem(X))))") 
 |> uex2ex_rule |> qSKOLEM "cstr1" [‘A’,‘x0’] 
*)

(*
val mkf1_def = 
 fun_tm_compr_uex ("ax0f",mem_sort (rastt "(A * X) * Exp(A,X)")) 
 (rastt "App(tof(Snd(ax0f:mem((A * X) * Exp(A,X)))),Fst(Fst(ax0f)))") |> 
 uex2ex_rule |> qSKOLEM "mkf1" [‘A’,‘X’] 


qfun_compr ‘a:mem(A)’
‘tuple4(num1,SOME(a:mem(A)),Tpm(TNull(A+1)),Tpm(Conat(x0:mem(X))))’
*)

fun qfun_compr qv qt = 
    let val vt = qparse_term_with_cont essps qv
        val v = dest_var vt
        val t = qparse_term_with_cont (fvt vt) qt
    in fun_tm_compr_uex v t
    end


val cstr0_def = 
 qfun_compr ‘d:mem(1)’
 ‘tuple4(O, NONE(A), Tpm(TNull(A + 1)), Tpm(Conat(x0:mem(X))))’ 
|> uex2ex_rule |> qSKOLEM "cstr0" [‘A’,‘x0’]

val cstr1_def = 
 qfun_compr ‘a:mem(A)’
 ‘tuple4(num1,SOME(a:mem(A)),Tpm(TNull(A+1)),Tpm(Conat(x0:mem(X))))’
 |> uex2ex_rule |> qSKOLEM "cstr1" [‘A’,‘x0’] 

val cstr2_def = 
 qfun_compr ‘f0x:mem(Tree(A + 1) * X)’
 ‘tuple4(num2,NONE(A),Tpm(T1arg(Fst(f0x))),
                      Tpm(X1arg(Snd(f0x),x0:mem(X))))’
|> uex2ex_rule |> qSKOLEM "cstr2" [‘A’,‘x0’] 

val cstr3_def = 
 qfun_compr ‘f12x12:mem(Tree(A +1) * Tree(A+1) * X * X)’
 ‘tuple4(num3,NONE(A),Tpm(T2arg(c41(f12x12),c42(f12x12))),
                      Tpm(X2arg(c43(f12x12),c44(f12x12),x0:mem(X))))’
|> uex2ex_rule |> qSKOLEM "cstr3" [‘A’,‘x0’] 

val cstr4_def = 
 qfun_compr ‘f0x:mem(Tree(A + 1) * X)’
 ‘tuple4(num4,NONE(A),Tpm(T1arg(Fst(f0x))),
                      Tpm(X1arg(Snd(f0x),x0:mem(X))))’
|> uex2ex_rule |> qSKOLEM "cstr4" [‘A’,‘x0’]


(*cannot write cstr(num,A,x0) since the domains of cstrs are not consistent, maybe a hope is to use coproduct*)


val cf0 = 
define_lambda
“!tuple:mem(N * (A+1) * Exp(N,Tree(A+1)) * Exp(N,X)).
  (From(cstr0(A,x0),tuple) ==>
  App(f,tuple) = x0) & 
  (From(cstr1(A,x0), tuple) ==>
  App(f,tuple) = 
  ctt(IMAGE(vf, FIB(cstr1(A,x0),tuple)),x0)
  ) &
  (From(cstr2(A,x0), tuple) ==>
  App(f,tuple) = 
  ctt(IMAGE(nf o p2(Tree(A + 1),X),FIB(cstr2(A,x0),tuple)),x0)
  ) &
  (From(cstr3(A,x0), tuple) ==>
  App(f,tuple) = 
  ctt(IMAGE(djf o p2(Tree(A + 1),X * X) o p2(Tree(A + 1),Tree(A+1) * X * X),FIB(cstr3(A,x0),tuple)),x0)
  ) &
  (From(cstr4(A,x0), tuple) ==>
  App(f,tuple) = 
  ctt(IMAGE(dmf o p2(Tree(A + 1),X),FIB(cstr4(A,x0),tuple)),x0)
  ) & 
  (ELSE ==> App(f,tuple) = x0)”

val niff_cstr1 = proved_th $
e0
cheat
(form_goal 
 “(~From(cstr0(A, x0), tuple) & From(cstr1(A, x0:mem(X)), tuple)) <=>
  From(cstr1(A, x0), tuple)”)


val niff_cstr2 = proved_th $
e0
cheat
(form_goal 
 “(~From(cstr0(A, x0), tuple) & ~From(cstr1(A, x0:mem(X)), tuple) &
  From(cstr2(A, x0:mem(X)), tuple)) <=>
  From(cstr2(A, x0), tuple)”)


val niff_cstr3 = proved_th $
e0
cheat
(form_goal 
 “(~From(cstr0(A, x0), tuple) & ~From(cstr1(A, x0:mem(X)), tuple) &
   ~From(cstr2(A, x0:mem(X)), tuple) & From(cstr3(A, x0:mem(X)), tuple)) <=>
  From(cstr3(A, x0), tuple)”)


val niff_cstr4 = proved_th $
e0
cheat
(form_goal 
 “(~From(cstr0(A, x0), tuple) & ~From(cstr1(A, x0:mem(X)), tuple) &
   ~From(cstr2(A, x0:mem(X)), tuple) & ~From(cstr3(A, x0:mem(X)), tuple) & 
   From(cstr4(A, x0:mem(X)), tuple)) <=>
  From(cstr4(A, x0), tuple)”)


val encafm_def = qdefine_psym("encafm",[‘x0:mem(X)’,‘tuple:mem(N * (A + 1) * Exp(N,Tree(A+1)) * Exp(N,X))’]) 
‘From(cstr0(A, x0), tuple) | From(cstr1(A, x0), tuple) |
 From(cstr2(A, x0), tuple) | From(cstr3(A, x0), tuple) |
 From(cstr4(A, x0), tuple)’


(*need a drule, turn a conjunctive def into a disjunctive neg*)

val NOT_encafm = proved_th $
e0
cheat
(form_goal
 “(~From(cstr0(A, x0), tuple) & ~From(cstr1(A, x0:mem(X)), tuple) &
   ~From(cstr2(A, x0:mem(X)), tuple) & ~From(cstr3(A, x0:mem(X)), tuple) & 
   ~From(cstr4(A, x0:mem(X)), tuple)) <=>
  ~encafm(x0,tuple)”)

val fmFn_char = 
cf0 |> rewr_rule[niff_cstr1,niff_cstr2,niff_cstr3,niff_cstr4,NOT_encafm] 





val fmFn_def = proved_th $
e0
(chea
)
(form_goal
 “!X x0:mem(X) A vf:A->X nf:X->X djf:X*X->X dmf:X->X.
  ?!Fn:N * (A + 1) * Exp(N,Tree(A+1)) * Exp(N,X) -> X.
    Fnap(Fn,O,NONE(A),TNull(A+1),Conat(x0)) = x0 &
    (!a. 
       Fnap(Fn,num1,SOME(a),TNull(A+1),Conat(x0)) = App(vf,a)) &
    (!f0 x. 
       Fnap(Fn,num2,NONE(A),T1arg(f0),X1arg(x,x0)) = App(nf,x)) & 
    (!f1 f2 x1 x2. 
       Fnap(Fn,num3,NONE(A),T2arg(f1,f2),X2arg(x1,x2,x0)) = App(djf,Pair(x1,x2)))     &
    (!f0 x. 
       Fnap(Fn,num4,NONE(A),T1arg(f0),X1arg(x,x0)) = 
       App(dmf,x))  & 
    (!tuple. 
       ~encafm(x0,tuple) ==>
       App(Fn,tuple) = x0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "fmFn" [‘x0’,‘vf’,‘nf’,‘djf’,‘dmf’]



rw[From_def,cstr1_def,cstr4_def,GSYM IN_NONEMPTY] >>
rw[GSYM IN_EXT_iff,Empty_def,FIB_def,PREIM_def,cstr1_def,cstr4_def,IN_Sing] >>
rpt strip_tac >> ccontra_tac >> 
fs[]
“From(cstr4(A, x0:mem(X)), tuple) ==> ~From(cstr1(A, x0), tuple)”

“(A ==> ~B) & (C ==> A) ==>
 (~B & C <=> A)”
(*

define_lambda
“!tuple.
  (From(constf(1,tuple4(O,NONE(A),Tpm(TNull(A+1)),Tpm(Conat(x0)))),
       tuple) ==>
  App(f,tuple) = x0) & 
  (From(cstr1(A,X), tuple) ==>
  App(f,tuple) = 
  ctt(IMAGE(Ap1(mkf1(A,X),Tpm(vf)),
            FIB(cstr1(A,X),tuple)),x0)
  ) &
  (From(cstr2(A,X), tuple) ==>
  App(f,tuple) = 
  ctt(IMAGE(Ap1(mkf2(),Tpm(nf)),
            FIB(mk2(),tuple)),x0)
  )
  (ELSE ==> App(f,tuple) = x0)”
*)

(form_goal
 “!X x0:mem(X) A vf:A->X nf:X->X djf:X*X->X dmf:X->X.
  ?!Fn:N * (A + 1) * Exp(N,Tree(A+1)) * Exp(N,X) -> X.
    Fnap(Fn,O,NONE(A),TNull(A+1),Conat(x0)) = x0 &
    (!a. 
       Fnap(Fn,num1,SOME(a),TNull(A+1),Conat(x0)) = App(vf,a)) &
    (!f0 x. 
       Fnap(Fn,num2,NONE(A),T1arg(f0),X1arg(x,x0)) = App(nf,x)) & 
    (!f1 f2 x1 x2. 
       Fnap(Fn,num3,NONE(A),T2arg(f1,f2),X2arg(x1,x2,x0)) = App(djf,Pair(x1,x2)))     &
    (!f0 x. 
       Fnap(Fn,num4,NONE(A),T1arg(f0),X1arg(x,x0)) = 
       App(dmf,x))  & 
    (!n aopt targ xarg. 
       ~encafm(x0,n,aopt,targ,xarg) ==>
       Fnap(Fn,n,aopt,targ,xarg) = x0)”)
|> spec_all |> uex2ex_rule |> qSKOLEM "fmFn" [‘x0’,‘vf’,‘nf’,‘djf’,‘dmf’]
