
local
fun delete'(set,mem) = HOLset.delete(set,mem) handle _ => set
in
fun filter_cont ct = 
    HOLset.foldr 
        (fn (ns,set) => 
            case HOLset.find 
                     (fn (vn,vs) => HOLset.member(fvs vs,ns)) set of 
                SOME _ => delete'(set,ns)
              | NONE => set) ct ct
end

fun ex2fsym fsym strl th = 
    let val th' = spec_all th
        val (ct,asl) = (cont th',ant th')
        val (hyp,conc) = dest_imp (concl th')
        val inputvars0 = filter_cont (cont th') 
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) essps 
                                   (List.map (dest_var o (parse_term_with_cont ct)) strl)
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val inputvl = List.map (parse_term_with_cont ct) strl
        val ((n,s),b) = dest_exists conc
        val _ = new_fun fsym (s,List.map dest_var inputvl)
        val fterm = mk_fun fsym inputvl
        val b' = substf ((n,s),fterm) b
    in mk_thm (ct,asl,mk_imp hyp b')
    end

fun uex_ex f = 
    let val th0 = iffLR $ uex_def f |> undisch
        val c0 = concl th0
        val ((n,s),b) = dest_exists c0
        val th1 = assume b |> conjE1 
        val th2 = existsI (n,s) (mk_var(n,s)) (concl th1) th1
        val th3 = existsE (n,s) th0 th2
    in disch f th3
    end

fun uex2ex_rule th = mp (uex_ex $concl th) th
fun uex_expand th = rewr_rule [uex_def $ concl th] th



val _ = new_sort "ob" [] 
val _ = new_sort "ar" [("A",mk_sort "ob" []),("B",mk_sort "ob" [])]
val _ = EqSorts := "ar" :: (!EqSorts)
val ob_sort = mk_sort "ob" [];
fun ar_sort A B = mk_sort "ar" [A,B];

val _ = new_fun "1" (mk_sort "ob" [],[]);
val ONE = mk_fun "1" [];
val _ = new_fun "To1" (mk_sort "ar" [mk_var ("A",ob_sort),ONE],[("A",ob_sort)]);
val _ = new_fun "0" (mk_sort "ob" [],[]);
val ZERO = mk_fun "0" [];
val _ = new_fun "From0" (mk_sort "ar" [ZERO,mk_var ("A",ob_sort)],[("A",ob_sort)]);


val _ = new_fun "*" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun Po A B = mk_fun "*" [A,B];
val _ = new_fun "+" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun coPo A B = mk_fun "+" [A,B];
val _ = new_fun "Exp" (ob_sort,[("A",ob_sort),("B",ob_sort)]);
fun Exp A B = mk_fun "Exp" [A,B];

fun mk_ob name = mk_var (name,ob_sort);
fun mk_ar name dom cod = mk_var (name,ar_sort dom cod);
val _ = new_fun "Pa" (ar_sort (mk_ob "X") (Po (mk_ob "A") (mk_ob "B")),
 [("f",ar_sort (mk_ob "X") (mk_ob "A")),("g",ar_sort (mk_ob "X") (mk_ob "B"))]);

val _ = new_fun "o" (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])],[("f",mk_sort "ar" [mk_var("B",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])]),("g",mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("B",mk_sort "ob" [])])])


val _ = new_fun "id" 
       (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("A",mk_sort "ob" [])],
        [("A",mk_sort "ob" [])])

val _ = new_sort_infix "ar" "->"

fun new_ax f = 
    let
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end


val idL = new_ax “!B A f:B->A. id(A) o f = f”

val idR = new_ax “!A B f:A->B. f o id(A) = f”

val o_assoc = new_ax “!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f”

val _ = new_pred "is1" [("ONE",ob_sort)]

val is1_def = new_ax “!ONE. is1(ONE) <=> !X.?!f:X->ONE.T”

val ONE_ex = new_ax “?ONE.is1(ONE)”

fun ex2fsym0 name args th = th |> eqT_intro |> iffRL |> ex2fsym name args
                               |> C mp (trueI [])
                    
val ONE_def = ex2fsym0 "1" [] ONE_ex

val ONE_prop = ONE_def |> rewr_rule [is1_def]
(*why rewr_rule with is1_def loops? it thought is1 is fVar notpred  TODO*)

val To1_def = ONE_prop |> spec_all |> uex_expand |> ex2fsym0 "To1" ["X"] |> gen_all

val _ = new_pred "is0" [("ZERO",ob_sort)]

val is0_def = new_ax “!ZERO.is0(ZERO) <=> !X.?!f:ZERO ->X. T”

val ZERO_ex = new_ax “?ZERO.is0(ZERO)”

val ZERO_def = ex2fsym0 "0" [] ZERO_ex

val ZERO_prop = ZERO_def |> conv_rule (once_depth_fconv no_conv (rewr_fconv (spec_all is0_def)))

val From0_def = ZERO_prop |> spec_all |> uex_expand |> ex2fsym0 "From0" ["X"] |> gen_all

val _ = new_pred "isPr" [("p1",ar_sort (mk_ob "AB") (mk_ob "A")),
                         ("p2",ar_sort (mk_ob "AB") (mk_ob "B"))]

val isPr_def = new_ax “!A B AB p1:AB->A p2:AB->B. isPr(p1,p2) <=>
   !X f:X->A g:X->B.?!fg:X->AB. p1 o fg = f & p2 o fg = g”

val isPr_ex = new_ax “!A B.?AB p1:AB->A p2:AB->B.isPr(p1,p2)”;

val Po_def = isPr_ex |> spec_all |> ex2fsym0 "*" ["A","B"] |> gen_all

val p1_def = Po_def |> spec_all |> ex2fsym0 "p1" ["A","B"] |> gen_all

val p2_def = p1_def |> spec_all |> ex2fsym0 "p2" ["A","B"] |> gen_all

val Pa_def = p2_def |> rewr_rule[isPr_def] |> spec_all
                    |> uex_expand 
                    |> ex2fsym0 "Pa" ["f","g"]


val _ = new_pred "iscoPr" [("i1",ar_sort (mk_ob "A") (mk_ob "AB")),
                           ("i2",ar_sort (mk_ob "B") (mk_ob "AB"))]

val iscoPr_def = new_ax “!A B AB i1:A->AB i2:B->AB. iscoPr(i1,i2) <=>
   !X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g”

val iscoPr_ex = new_ax “!A B.?AB i1:A->AB i2:B->AB.iscoPr(i1,i2)”;

val coPo_def = iscoPr_ex |> spec_all |> ex2fsym0 "+" ["A","B"] |> gen_all

val i1_def = coPo_def |> spec_all |> ex2fsym0 "i1" ["A","B"] |> gen_all

val i2_def = i1_def |> spec_all |> ex2fsym0 "i2" ["A","B"] |> gen_all

val coPa_def = i2_def |> rewr_rule[iscoPr_def] |> spec_all
                      |> uex_expand 
                      |> ex2fsym0 "coPa" ["f","g"]


(*TODO: if ispr i.e. formula variable, then will loop*)

val _ = new_pred "isEq" 
                 [("f",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("g",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("e",ar_sort (mk_ob "E") (mk_ob "A"))]

val isEq_def = new_ax 
“!A B f:A->B g E e:E->A. 
      isEq(f,g,e) <=> 
      f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0”

val isEq_ex = new_ax “!A B f:A->B g:A->B.?E e:E->A.isEq(f,g,e)”

val Eqa_def = 
    isEq_def |> iffLR 
             |> spec_all |> undisch |> conjE2 
             |> spec_all |> undisch |> uex_expand
             |> conj_all_assum |> disch_all
             |> ex2fsym "Eqa" ["f","g","e","a"]


val _ = new_pred "iscoEq" 
                 [("f",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("g",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("ce",ar_sort (mk_ob "B") (mk_ob "cE"))]

val iscoEq_def = new_ax 
“!A B f:A->B g cE ce:B -> cE. 
      iscoEq(f,g,ce) <=> 
      ce o f = ce o g & 
      !X x:B->X. x o f = x o g ==>
      ?!x0:cE->X. x = x0 o ce”

val iscoEq_ex = new_ax “!A B f:A->B g:A->B.?cE ce:B->cE.iscoEq(f,g,ce)”;

val coEqa_def = 
    iscoEq_def |> iffLR 
               |> spec_all |> undisch |> conjE2 
               |> spec_all |> undisch |> uex_expand
               |> conj_all_assum |> disch_all
               |> ex2fsym "coEqa" ["f","g","ce","x"]
(*TodO tidy the conjs to imp here*)


(*
e that given any pair of objects A, B there exists an
object BA and a mapping A × BA→
e
B with the property that for any object X and any
mapping A × X →
f
B there is a unique mapping X →
h
BA such that (A × h)e = f. This
universal mapping property is partly expressed by the following diagram.
*)
val _ = new_pred "isExp" 
 [("ev",ar_sort (Po (mk_ob "A") (mk_ob "A2B")) (mk_ob "B"))]

val isExp_def =
 new_ax “!A B A2B ev:A * A2B -> B.
         isExp(ev) <=> !X f:A * X->B. ?!h:X->A2B. ev o Pa(p1(A,X), h o p2(A,X)) = f”


(*example here : we cannot get function for eqlz, because the inputs are a pair of ars, and we need to produce an object first. But here the input are objects, we can produce an object from the objects first, the exp, and then have ev(A,B)*)

val isExp_ex = new_ax “!A B. ?A2B ev:A * A2B->B. isExp(ev)”

val Exp_def = isExp_ex |> spec_all 
                       |> ex2fsym0 "Exp" ["A","B"] |> gen_all

val Ev_def = Exp_def |> spec_all |> rewr_rule[isExp_def]
                     |> ex2fsym0 "Ev" ["A","B"]

val Tp_def = Ev_def |> spec_all |> uex_expand 
                    |> ex2fsym0 "Tp" ["f"]


val N_ex = new_ax “?N O:1->N SUC:N->N.
 !X x0:1->X t:X->X.?!x:N->X. x o O = x0 & x o SUC = t o x”

val N_def = N_ex |> ex2fsym0 "N" []

val O_def = N_def |> ex2fsym0 "O" []

val SUC_def = O_def |> ex2fsym0 "SUC" []

val WP = new_ax “!A B f:A->B g.~(f = g) ==> ?a:1->A. ~(f o a = g o a)”


(*mono does not need "is" version becuase it does not induce any function*)
val _ = new_pred "Mono" [("f",ar_sort (mk_ob "A") (mk_ob "B"))]

val Mono_def = new_ax “!A B f:A->B. Mono(f) <=> !X g:X->A h. f o g = f o h ==> g = h”

val NONZERO_EL = new_ax “!X.~(is0(X)) ==>?x:1->X.T”

val AC = new_ax “!A B f:A->B. ?g:B->A. f o g o f = f”;


val ismem_def = read_axiom "!A x:1-> A A0 a:A0 -> A. ismem(x,a) <=> ismono(a) & ?x0:1 -> A0. a o x0 = x";

val INC_FAC = new_ax “!A B f:1->A + B. (?f0:1->A.i1(A,B) o f0 = f) |(?f0:1->B.i2(A,B) o f0 = f)”

val DISTI_EL = new_ax “?X x1:1->X x2. ~(x1 = x2)”

