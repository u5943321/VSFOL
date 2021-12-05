fun store_as name th = 
let val _ = store_thm(name, th)
in th
end

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
 
fun store_ax (name,f) = store_as name (new_ax f)

val idL = store_ax("idL", “!B A f:B->A. id(A) o f = f”);

val idR = store_ax("idR",“!A B f:A->B. f o id(A) = f”);

val o_assoc = store_ax("o_assoc",“!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f”);

val _ = new_pred "is1" [("ONE",ob_sort)]

val is1_def = store_ax("is1_def",“!ONE. is1(ONE) <=> !X.?!f:X->ONE.T”)

val ONE_ex = store_ax("ONE_ex",“?ONE.is1(ONE)”)

fun ex2fsym0 name args th = th |> eqT_intro |> iffRL |> ex2fsym name args
                               |> C mp (trueI [])
                    
val ONE_def = ex2fsym0 "1" [] ONE_ex |> store_as "ONE_def"

val ONE_prop = ONE_def |> rewr_rule [is1_def]
                       |> store_as "ONE_prop"

(*why rewr_rule with is1_def loops? it thought is1 is fVar notpred  TODO*)

val To1_def = ONE_prop |> spec_all |> uex_expand |> ex2fsym0 "To1" ["X"] |> gen_all |> store_as "To1_def"

val _ = new_pred "is0" [("ZERO",ob_sort)]

val is0_def = store_ax("is0_def",“!ZERO.is0(ZERO) <=> !X.?!f:ZERO ->X. T”)

val ZERO_ex = store_ax("ZERO_ex",“?ZERO.is0(ZERO)”)

val ZERO_def = ex2fsym0 "0" [] ZERO_ex |> store_as "ZERO_def"

val ZERO_prop = ZERO_def |> conv_rule (once_depth_fconv no_conv (rewr_fconv (spec_all is0_def))) |> store_as "ZERO_prop"

val From0_def = ZERO_prop |> spec_all |> uex_expand |> ex2fsym0 "From0" ["X"] |> gen_all |> store_as "From0_def"

val _ = new_pred "isPr" [("p1",ar_sort (mk_ob "AB") (mk_ob "A")),
                         ("p2",ar_sort (mk_ob "AB") (mk_ob "B"))]

val isPr_def = store_ax("isPr_def",“!A B AB p1:AB->A p2:AB->B. isPr(p1,p2) <=>
   !X f:X->A g:X->B.?!fg:X->AB. p1 o fg = f & p2 o fg = g”)

val isPr_ex = store_ax("isPr_ex",“!A B.?AB p1:AB->A p2:AB->B.isPr(p1,p2)”);

val Po_def = isPr_ex |> spec_all |> ex2fsym0 "*" ["A","B"] |> gen_all |> store_as "Po_def"

val p1_def = Po_def |> spec_all |> ex2fsym0 "p1" ["A","B"] |> gen_all |> store_as "p1_def"

val p2_def = p1_def |> spec_all |> ex2fsym0 "p2" ["A","B"] |> gen_all |> store_as "p2_def"

val Pa_def = p2_def |> rewr_rule[isPr_def] |> spec_all
                    |> uex_expand 
                    |> ex2fsym0 "Pa" ["f","g"] |> gen_all
                    |> store_as "Pa_def"

val _ = new_pred "iscoPr" [("i1",ar_sort (mk_ob "A") (mk_ob "AB")),
                           ("i2",ar_sort (mk_ob "B") (mk_ob "AB"))]

val iscoPr_def = store_ax("iscoPr_def",“!A B AB i1:A->AB i2:B->AB. iscoPr(i1,i2) <=>
   !X f:A->X g:B->X.?!fg:AB->X.fg o i1 = f & fg o i2 = g”);

val iscoPr_ex = store_ax("iscoPr_ex",“!A B.?AB i1:A->AB i2:B->AB.iscoPr(i1,i2)”);

val coPo_def = iscoPr_ex |> spec_all |> ex2fsym0 "+" ["A","B"] |> gen_all |> store_as "coPo_def";

val i1_def = coPo_def |> spec_all |> ex2fsym0 "i1" ["A","B"] |> gen_all |> store_as "i1_def";

val i2_def = i1_def |> spec_all |> ex2fsym0 "i2" ["A","B"] |> gen_all |> store_as "i2_def";

val coPa_def = i2_def |> rewr_rule[iscoPr_def] |> spec_all
                      |> uex_expand 
                      |> ex2fsym0 "coPa" ["f","g"]
                      |> gen_all
                      |> store_as "coPa_def";


(*TODO: if ispr i.e. formula variable, then will loop*)

val _ = new_pred "isEq" 
                 [("f",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("g",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("e",ar_sort (mk_ob "E") (mk_ob "A"))];

val isEq_def = store_ax("isEq_def",
“!A B f:A->B g E e:E->A. 
      isEq(f,g,e) <=> 
      f o e = g o e & 
      !X a:X->A. f o a = g o a ==>
      ?!a0:X->E. a = e o a0”)

val isEq_ex = store_ax("isEq_ex",“!A B f:A->B g:A->B.?E e:E->A.isEq(f,g,e)”)

val Eqa_def = 
    isEq_def |> iffLR 
             |> spec_all |> undisch |> conjE2 
             |> spec_all |> undisch |> uex_expand
             |> conj_all_assum |> disch_all
             |> ex2fsym "Eqa" ["f","g","e","a"]
             |> gen_all
             |> store_as "Eqa_def"

val _ = new_pred "iscoEq" 
                 [("f",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("g",ar_sort (mk_ob "A") (mk_ob "B")),
                  ("ce",ar_sort (mk_ob "B") (mk_ob "cE"))]

val iscoEq_def = store_ax("iscoEq_def",
“!A B f:A->B g cE ce:B -> cE. 
      iscoEq(f,g,ce) <=> 
      ce o f = ce o g & 
      !X x:B->X. x o f = x o g ==>
      ?!x0:cE->X. x = x0 o ce”)

val iscoEq_ex = store_ax("iscoEq_ex",“!A B f:A->B g:A->B.?cE ce:B->cE.iscoEq(f,g,ce)”);

val coEqa_def = 
    iscoEq_def |> iffLR 
               |> spec_all |> undisch |> conjE2 
               |> spec_all |> undisch |> uex_expand
               |> conj_all_assum |> disch_all
               |> ex2fsym "coEqa" ["f","g","ce","x"]
               |> store_as "coEqa_def"
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
 store_ax("isExp_def",“!A B A2B ev:A * A2B -> B.
         isExp(ev) <=> !X f:A * X->B. ?!h:X->A2B. ev o Pa(p1(A,X), h o p2(A,X)) = f”)


(*example here : we cannot get function for eqlz, because the inputs are a pair of ars, and we need to produce an object first. But here the input are objects, we can produce an object from the objects first, the exp, and then have ev(A,B)*)

val isExp_ex = store_ax("isExp_ex",“!A B. ?A2B ev:A * A2B->B. isExp(ev)”);

val Exp_def = isExp_ex |> spec_all 
                       |> ex2fsym0 "Exp" ["A","B"] |> gen_all
                       |> store_as "Exp_def"

val Ev_def = Exp_def |> spec_all |> rewr_rule[isExp_def]
                     |> ex2fsym0 "Ev" ["A","B"]
                     |> gen_all
                     |> store_as "Ev_def"

val Tp_def = Ev_def |> spec_all |> uex_expand 
                    |> ex2fsym0 "Tp" ["f"] |> gen_all
                    |> store_as "Tp_def"


val N_ex = store_ax("N_ex",“?N O:1->N SUC:N->N.
 !X x0:1->X t:X->X.?!x:N->X. x o O = x0 & x o SUC = t o x”)

val N_def = N_ex |> ex2fsym0 "N" [] |> store_as "N_def";

val O_def = N_def |> ex2fsym0 "O" [] |> store_as "O_def";

val SUC_def = O_def |> ex2fsym0 "SUC" [] |> store_as "SUC_def";

val Nind_def = SUC_def |> spec_all |> uex_expand
                       |> ex2fsym0 "Nind" ["x0","t"]
                       |> gen_all
                       |> store_as "Nind_def"

val WP = store_ax("WP",“!A B f:A->B g.~(f = g) ==> ?a:1->A. ~(f o a = g o a)”);


(*mono does not need "is" version becuase it does not induce any function*)
val _ = new_pred "Mono" [("f",ar_sort (mk_ob "A") (mk_ob "B"))]

val Mono_def = store_ax("Mono_def",“!A B f:A->B. Mono(f) <=> !X g:X->A h. f o g = f o h ==> g = h”);

val _ = new_pred "Epi" [("f",ar_sort (mk_ob "A") (mk_ob "B"))]

val Epi_def = store_ax("Epi_def",“!A B f:A->B. Epi(f) <=> !X g:B->X h. g o f = h o f ==> g = h”);

val NONZERO_EL = store_ax("NONZERO_EL",“!X.~(is0(X)) ==>?x:1->X.T”);

val AC = store_ax("AC",“!A B a:1->A f:A->B. ?g:B->A. f o g o f = f”);

val INC_FAC = store_ax("INC_FAC",“!A B f:1->A + B. (?f0:1->A.i1(A,B) o f0 = f) |(?f0:1->B.i2(A,B) o f0 = f)”);

val DISTI_EL = store_ax("DISTI_EL",“?X x1:1->X x2. ~(x1 = x2)”);

val AX8 = DISTI_EL;

val FALSE_ex = prove_store ("FALSE_ex",
e0
(qexists_tac ‘i1(1,1)’ >> rw[])
(form_goal
 “?f. i1(1,1) = f”)
);

val FALSE_def = ex2fsym0 "FALSE" [] FALSE_ex 
                         |> store_as "FALSE_def"

val TRUE_ex = prove_store ("TRUE_ex",
e0
(qexists_tac ‘i2(1,1)’ >> rw[])
(form_goal
 “?f. i2(1,1) = f”)
);

val TRUE_def = ex2fsym0 "TRUE" [] TRUE_ex 
                        |> store_as "TRUE_def";


val Tp1_ex = prove_store("Tp1_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(f o p1(A,1))’ >> rw[])
(form_goal
“!A B f:A->B.?tpf:1->Exp(A,B).Tp(f o p1(A,1)) = tpf”));

val Ev_of_Tp = prove_store("Ev_of_Tp",
e0
(rpt strip_tac >> rw[Tp_def])
(form_goal
 “!A B X f:A * X ->B. 
  Ev(A,B) o Pa(p1(A,X),Tp(f) o p2(A,X)) = f”));

val Tp_eq = prove_store("Tp_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (once_rw[GSYM Ev_of_Tp] >> arw[]) >> arw[])
(form_goal
 “!A B X f:A * X ->B g:A * X ->B.Tp(f) = Tp(g) <=> f = g”));

val is_Tp = prove_store("is_Tp",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘B’,‘X’,‘f’] (assume_tac o conjE2) Tp_def>>
 first_x_assum irule >> arw[])
(form_goal
 “!A B X f:A * X ->B h:X-> Exp(A,B). 
  Ev(A,B) o Pa(p1(A,X),h o p2(A,X)) = f ==> h = Tp(f)”));

val Ev_eq_eq = prove_store("Ev_eq_eq",
e0
(rpt strip_tac >> 
 qsuff_tac ‘f = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X))) & 
  g = Tp(Ev(A,B) o Pa(p1(A,X),g o p2(A,X)))’
 >-- (rpt strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Tp >> first_x_assum accept_tac) >>
 irule is_Tp >> rw[])
(form_goal
 “!A B X f g. Ev(A,B) o Pa(p1(A,X),f o p2(A,X)) = 
              Ev(A,B) o Pa(p1(A,X),g o p2(A,X)) ==> f = g”));

val is_Pa = Pa_def |> spec_all |> conjE2 |> gen_all
                   |> store_as "is_Pa";

val to_P_component = prove_store("to_Pr_component",
e0
(rpt strip_tac >> irule is_Pa >> rw[])
(form_goal
 “!A B X f:X->A * B.  f = Pa(p1(A,B) o f,p2(A,B) o f)”));

val to_P_eq = prove_store("to_P_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f = Pa(p1(A,B) o g,p2(A,B) o g) &
            g = Pa(p1(A,B) o g,p2(A,B) o g)’ >--
 (strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Pa >> arw[]) >> once_rw[to_P_component])
(form_goal
 “!A B X f:X->A * B g:X->A * B. p1(A,B) o f = p1(A,B) o g &
 p2(A,B) o f = p2(A,B) o g ==> f = g”));

val is_coPa = coPa_def |> spec_all |> conjE2
                       |> gen_all
                       |> store_as "is_coPa";

val from_coP_component = prove_store("from_coP_component",
 e0
(rpt strip_tac >> irule is_coPa >> rw[])
(form_goal
 “!A B X f:A + B ->X g:A + B->X. f = coPa(f o i1(A,B),f o i2(A,B))”));


val from_coP_eq = prove_store("from_coP_eq",
e0
(rpt strip_tac >>
 qsuff_tac ‘f = coPa(g o i1(A,B),g o i2(A,B)) &
            g = coPa(g o i1(A,B),g o i2(A,B))’ >--
 (strip_tac >> once_arw[] >> rw[]) >>
 strip_tac (* 2 *) >--
 (irule is_coPa >> arw[]) >> once_rw[from_coP_component])
(form_goal
 “!A B X f:A + B-> X g:A + B->X. f o i1(A,B) = g o i1(A,B) & f o i2(A,B) = g o i2(A,B) ==> f = g”));


val i12_of_coPa = coPa_def |> spec_all |> conjE1
                           |> gen_all 
                           |> store_as "i12_of_coPa";

val i1_of_coPa = i12_of_coPa |> spec_all |> conjE1
                             |> gen_all 
                             |> store_as "i1_of_coPa";


val i2_of_coPa = i12_of_coPa |> spec_all |> conjE2
                             |> gen_all 
                             |> store_as "i2_of_coPa";
 
val p12_of_Pa = Pa_def |> spec_all |> conjE1
                       |> gen_all
                       |> store_as "p12_of_Pa";

                       
val p1_of_Pa = p12_of_Pa |> spec_all |> conjE1
                         |> gen_all 
                         |> store_as "p1_of_Pa";

val p2_of_Pa = p12_of_Pa |> spec_all |> conjE2
                         |> gen_all 
                         |> store_as "p2_of_Pa";

 

val i1_ne_i2_1 = prove_store ("i1_ne_i2",
e0
(ccontra_tac >> 
 x_choosel_then ["X","x1","x2"] assume_tac DISTI_EL >>
 qsuff_tac ‘x1 = x2’ >-- arw[] >>
 qby_tac ‘coPa(x1,x2) o i1(1,1) = x1 &
          coPa(x1,x2) o i2(1,1) = x2’ >--
 rw[i12_of_coPa] >>
 pop_assum (assume_tac o GSYM) >> 
 qpick_x_assum ‘~(x1 = x2)’ (K all_tac) >> 
 once_arw[] >> pop_assum (K all_tac) >> arw[])
(form_goal
 “~(i1(1,1) = i2(1,1))”)
)

val to1_unique = prove_store("to1_unique",
e0
(rpt strip_tac >>
 qspecl_then [‘X’,‘f’] assume_tac To1_def >>
 qspecl_then [‘X’,‘g’] assume_tac To1_def >> 
 arw[])
(form_goal
 “!X f:X->1 g:X->1. f = g”));

val one_to_one_id = prove_store("one_to_one_id",
e0
(strip_tac >>
 qspecl_then [‘1’,‘f’,‘id(1)’] assume_tac to1_unique >>
 first_x_assum accept_tac)
(form_goal
 “!f:1->1. f = id(1)”))

val prop_5_lemma = prove_store("prop_5_lemma",
e0
(rpt strip_tac >> 
 ccontra_tac >> 
 qsuff_tac ‘i1(1,1) = i2(1,1)’ >-- rw[i1_ne_i2_1] >>
 qby_tac
 ‘coPa(i1(1,1) o To1(A),i2(1,1) o To1(B)) o i1(A, B) o x0 =   coPa(i1(1,1) o To1(A), i2(1,1) o To1(B)) o i2(A, B) o x0'’
 >-- arw[] >> 
 fs[GSYM o_assoc,i12_of_coPa] >>
 fs[o_assoc] >> pop_assum mp_tac >>
 once_rw[one_to_one_id] >> rw[idR])
(form_goal
 “!A B x0:1->A x0':1->B. ~(i1(A,B) o x0 = i2(A,B) o x0')”));

val i1_i2_disjoint = prove_store("i1_i2_disjoint",
e0
(rw[prop_5_lemma])
(form_goal
 “!X t:1->X. ~(i1(X,X) o t = i2(X,X) o t)”));

(*
val i1_ne_i2 = prove_store("i1_ne_i2",
e0
(strip_tac >> ccontra_tac >> 
 qbirule WP)
(form_goal
 “!X. ~(is0(X)) ==> ~(i1(X,X) = i2(X,X))”)); 

maybe todo
*)

val is0_expand = 
  iff_trans (is0_def |> spec_all) (uex_def “?!f:ZERO->X.T” |> rewr_rule [] |> forall_iff ("X",ob_sort)) |> gen_all

val from_zero_unique = prove_store("from_zero_unique",
e0
(rpt strip_tac >> fs[is0_expand] >>
 first_x_assum $ qspecl_then [‘X’] strip_assume_tac >>
 first_assum $ qspecl_then [‘f’] strip_assume_tac >>
 first_assum $ qspecl_then [‘g’] strip_assume_tac >>
 arw[])
(form_goal
 “!ZERO. is0(ZERO) ==> !X f:ZERO->X g. f = g”));

val no_Epi_from_zero = prove_store("no_Epi_from_zero",
e0
(rpt strip_tac >>
 ccontra_tac >> 
 qsuff_tac ‘i1(1,1) = i2(1,1)’ >-- rw[i1_ne_i2_1] >>
 qsuff_tac ‘i1(1,1) o To1(B) = i2(1,1) o To1(B)’ >--
 (strip_tac >> 
  qby_tac ‘?b:1->B.T’ >-- 
  (irule NONZERO_EL >> arw[]) >> 
  pop_assum strip_assume_tac >>
  qby_tac ‘i1(1, 1) o To1(B) o b = i2(1, 1) o To1(B) o b’ 
  >-- arw[GSYM o_assoc] >>
  pop_assum mp_tac >> once_rw[one_to_one_id] >> 
  rw[idR]) >>
 fs[Epi_def] >> first_x_assum irule >>
 irule from_zero_unique >> arw[])
(form_goal
“!A B f:A->B. Epi(f) ==>
 ~is0(B) ==> ~is0(A)”));

val ZERO_no_MEM = prove_store("ZERO_no_MEM",
 e0
(ccontra_tac >> pop_assum strip_assume_tac >>
 strip_assume_tac DISTI_EL >>
 qsuff_tac ‘x1 = x2’ >-- arw[] >>
 qby_tac ‘x1 = x1 o To1(0) o f & 
          x2 = x2 o To1(0) o f’
 >-- (once_rw[one_to_one_id] >> rw[idR]) >>
 qpick_x_assum ‘~(x1 = x2)’ (K all_tac) >>
 once_arw[] >> 
 rw[GSYM o_assoc] >>
 qsuff_tac ‘x1 o To1(0) = x2 o To1(0)’
 >-- (pop_assum (K all_tac) >> strip_tac >> arw[]) >>
 irule from_zero_unique >> rw[ZERO_def]
 )
(form_goal
 “~(?f:1->0.T)”));

val not_to_zero = prove_store("not_to_ZERO",
e0
(rpt strip_tac >> ccontra_tac >> drule NONZERO_EL >>
 pop_assum strip_assume_tac >> 
 suffices_tac ``?f:1->0.T``
 >-- (disch_tac >> fs[ZERO_no_MEM]) >>
 qexists_tac ‘f o x’ >> rw[])
(form_goal
 “!A f:A->0.is0(A)”));


val to_zero_zero = prove_store("to_ZERO_ZERO",
e0
(rpt strip_tac >> 
 qsuff_tac ‘?g:A->0.T’ >-- 
 (strip_tac >> 
  qspecl_then [‘A’,‘g’] accept_tac not_to_zero) >>
  fs[is0_expand] >> 
 first_x_assum (qspecl_then [‘0’] strip_assume_tac) >>
 qexists_tac ‘f' o f’ >> rw[]
 )
(form_goal
 “!A B f:A->B.is0(B) ==>is0(A)”));

fun try_done tac (G,fl,l) = 
    case tac (G,fl,l) of 
        ([],pf) => ([],pf)
       | _ => ([(G,fl,l):goal],sing I)

val non_zero_pinv = prove_store("non_zero_pinv",
e0
(rpt strip_tac >> 
 drule NONZERO_EL >> pop_assum strip_assume_tac >>
 qspecl_then [‘A’,‘B’,‘x’,‘f’] accept_tac AC)
(form_goal
 “!A.~is0(A) ==>!B f:A->B.?g:B->A. f o g o f = f”));

val Mono_pinv_post_inv = prove_store("Mono_pinv_post_inv",
e0
(rpt strip_tac >> fs[Mono_def] >> first_x_assum irule >>
 arw[idR])
(form_goal
 “!A B f:A->B. Mono(f) ==> !g:B->A. 
 f o g o f = f ==> g o f = id(A)”));

 
val Epi_pinv_pre_inv = prove_store("Epi_pinv_pre_inv",
e0
(rpt strip_tac >> fs[Epi_def] >> first_x_assum irule >>
 arw[idL,o_assoc])
(form_goal
 “!A B f:A->B. Epi(f) ==> !g:B->A. 
 f o g o f = f ==> f o g = id(B)”));

val Mono_no_zero_post_inv = prove_store("Mono_no_zero_post_inv",
e0
(rpt strip_tac >> drule non_zero_pinv >>
 drule Mono_pinv_post_inv >>
 first_x_assum (qspecl_then [‘B’,‘f’] strip_assume_tac) >>
 first_x_assum drule >>
 qexists_tac ‘g’ >> arw[]
 )
(form_goal
 “!A B f:A->B. Mono(f) ==> ~is0(A) ==>
  ?g:B->A. g o f = id(A)”));


val Epi_no_zero_pre_inv = prove_store("Epi_no_zero_pre_inv",
e0
(rpt strip_tac >> drule non_zero_pinv >>
 drule Epi_pinv_pre_inv >>
 first_x_assum (qspecl_then [‘B’,‘f’] strip_assume_tac) >>
 first_x_assum drule >>
 qexists_tac ‘g’ >> arw[]
 )
(form_goal
 “!A B f:A->B. Epi(f) ==> ~is0(A) ==>
  ?g:B->A. f o g = id(B)”));

val inc_inc_iso = prove_store("inc_inc_iso",
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 cases_on “is0(X)” >> cases_on “is0(Y)” >>
 strip_tac >>
 try_done (irule from_zero_unique >> arw[]) (* 4 *)
 >-- (qspecl_then [‘Y’,‘X’,‘h2’] assume_tac to_zero_zero >>
      first_x_assum drule >> fs[])
 >-- (qspecl_then [‘X’,‘Y’,‘h1’] assume_tac to_zero_zero >>
      first_x_assum drule >> fs[])
 >-- (qby_tac ‘?b'. b' o b = id(Y)’ >--
      (irule Mono_no_zero_post_inv >> arw[]) >>
      pop_assum strip_assume_tac >> 
      qsuff_tac ‘b' o (b o h1) o h2 = id(Y)’ >--
      arw[GSYM o_assoc,idL] >>
      arw[]) >>
 qby_tac ‘?a'. a' o a = id(X)’ >--
 (irule Mono_no_zero_post_inv >> arw[]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac ‘a' o (a o h2) o h1 = id(X)’ >--
 arw[GSYM o_assoc,idL] >>
 arw[]
 )
(form_goal
 “!X A a:X->A Y b:Y->A h1:X->Y h2:Y->X. 
  Mono(a)& Mono(b) & b o h1 = a & a o h2 = b ==> 
  h1 o h2 = id(Y) & h2 o h1 = id(X)”));

(*
val parallel_P_o = prove_store("parallel_P_o",
e0
()
(form_goal
 “!”));
*)

val zero_no_MEM = prove_store("zero_no_MEM",
e0
(rpt strip_tac >> ccontra_tac >>
 pop_assum strip_assume_tac >>
 fs[is0_expand] >> assume_tac ZERO_no_MEM >>
 qsuff_tac ‘?f0:1->0.T’ >-- fs[] >>
 first_x_assum (qspecl_then [‘0’] strip_assume_tac) >>
 qexists_tac ‘f' o f’ >> rw[])
(form_goal
 “!zero. is0(zero) ==> ~(?f:1->zero.T)”));



val FUN_EXT = prove_store("FUN_EXT",
e0
(repeat strip_tac >> ccontra_tac >> drule WP >> 
 pop_assum strip_assume_tac >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >> 
 fs[])
(form_goal
 “!A B f:A->B g. (!a:1->A. f o a = g o a) ==> f = g”));


val prop_2_half2 = prove_store("prop_2_half2",
e0
(rpt strip_tac >> cases_on “is0(Y)” (* 2 *) >--
 (qby_tac ‘is0(X)’ >--
  (ccontra_tac >> 
   qsuff_tac ‘?y:1->Y.T’ >-- 
   (rw[] >> irule zero_no_MEM >> arw[]) >>
   drule NONZERO_EL >>
   pop_assum strip_assume_tac >>
   first_x_assum (qspecl_then [‘a o x’,‘x’] assume_tac) >>
   fs[] >> qexists_tac ‘xb'’ >> rw[]) >>
  fs[is0_expand] >>
  first_assum (qspecl_then [‘Y’] strip_assume_tac) >>
  qexists_tac ‘f’ >> 
  first_assum (qspecl_then [‘A’] strip_assume_tac) >>
  first_assum (qspecl_then [‘b o f’] strip_assume_tac) >>
  first_assum (qspecl_then [‘a’] strip_assume_tac) >>
  fs[]) >>
 drule Mono_no_zero_post_inv >> first_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘g o a’ >> irule FUN_EXT >>
 strip_tac >> 
 first_assum (qspecl_then [‘a o a'’,‘a'’] assume_tac) >>
 fs[] >> pop_assum (assume_tac o GSYM) >> arw[o_assoc] >>
 qby_tac ‘b o g o b o xb' = b o (g o b) o xb'’
 >-- rw[o_assoc] >>
 arw[idL])
(form_goal
 “!X A a:X->A. Mono(a) ==> !Y b:Y->A. Mono(b) ==>
  (!x:1->A xb:1->X. a o xb = x ==> ?xb':1->Y. b o xb' = x)
  ==> ?h:X->Y. b o h = a”));

val prop_2_coro_subo = prove_store("prop_2_coro_subo",
e0
(rpt strip_tac >>
 qby_tac ‘?h1. b o h1 = a’ 
 >-- (irule prop_2_half2 >> arw[] >> rpt strip_tac >>
      first_assum (qspecl_then [‘xb’] strip_assume_tac) >>
      qexists_tac ‘y’ >> fs[]) >>
 qby_tac ‘?h2. a o h2 = b’ 
 >-- (irule prop_2_half2 >> arw[] >> rpt strip_tac >>
      first_assum (qspecl_then [‘xb’] strip_assume_tac) >>
      qexists_tac ‘x'’ >> fs[]) >>
 pop_assum_list (map_every strip_assume_tac) >>
 qexistsl_tac [‘h1’,‘h2’] >> arw[] >>
 irule inc_inc_iso >> qexistsl_tac [‘A’,‘a’,‘b’] >> arw[])
(form_goal
 “!X A a:X->A.Mono(a) ==> 
  !Y b:Y->A. Mono(b) & 
             (!y:1->Y. ?x:1->X.a o x = b o y) & 
             (!x:1->X. ?y:1->Y.a o x = b o y) ==> 
  ?h1:X->Y h2:Y->X. 
    b o h1 = a & a o h2 = b & 
    h1 o h2 = id(Y) & h2 o h1 = id(X)”));

val _ = new_pred "areiso" [("A",ob_sort),("B",ob_sort)]

val areiso_def = store_ax("areiso_def",
“!A B. areiso(A,B) <=> ?f:A->B g:B->A. f o g = id(B) & g o f = id(A)”)

val prop_2_coro = prove_store("prop_2_coro",
e0
(repeat strip_tac >> rw[areiso_def] >>
 rev_drule prop_2_coro_subo >>
 first_x_assum (qspecl_then [‘Y’,‘b’] assume_tac) >>
 rev_full_simp_tac[] >>
 qexistsl_tac [‘h1’,‘h2’] >> arw[])
(form_goal
 “!X A a:X->A. Mono(a) ==>
  !Y b:Y->A. Mono(b) & 
  (!y:1->Y. ?x:1->X.a o x = b o y) & 
  (!x:1->X.?y:1->Y.a o x = b o y) ==> areiso(X,Y)”));

val Epi_has_section = prove_store("Epi_has_section",
e0
(rpt strip_tac >> cases_on “is0(B)” 
 >-- (fs[is0_expand] >> 
      first_assum (qspecl_then [‘B’] strip_assume_tac) >>
      first_assum (qspecl_then [‘A’] strip_assume_tac) >>
      qexists_tac ‘f'’ >>
      arw[]) >>
 drule no_Epi_from_zero >> first_assum drule >>
 drule NONZERO_EL >> pop_assum strip_assume_tac >>
 qspecl_then [‘A’,‘B’,‘x’,‘e’] strip_assume_tac AC >>
 drule Epi_pinv_pre_inv >> first_assum drule >>
 qexists_tac ‘g’ >> arw[])
(form_goal
 “!A B e:A->B. Epi(e) ==>?s0:B->A. e o s0 = id(B)”));

val Eq_equality = isEq_def |> iffLR |> strip_all_and_imp
                           |> conjE1 |> disch_all
                           |> gen_all
                           |> store_as "Eq_equality";


val coEq_equality = iscoEq_def |> iffLR |> strip_all_and_imp
                               |> conjE1 |> disch_all
                               |> gen_all
                               |> store_as "coEq_equality";

val isEq_expand = 
    isEq_def 
        |> rewr_rule[uex_def “?!a0:X->E.a = (e:E->A) o a0”]
        |> store_as "isEq_expand";


val iscoEq_expand = 
    iscoEq_def 
        |> rewr_rule[uex_def “?!x0:cE->X.x = x0 o (ce:B->cE)”]
        |> store_as "iscoEq_expand";

val coEq_of_equal = prove_store("coEq_of_equal",
e0
(rpt strip_tac >> rw[iscoEq_expand,idR] >> rpt strip_tac >>
 qexists_tac ‘x’ >> rw[] >> rpt strip_tac >> arw[])
(form_goal
 “!A B f:A->B.iscoEq(f,f,id(B))”));

val is_Eqa = Eqa_def|> strip_all_and_imp |> conjE2
                    |> disch_all |> gen_all
                    |> store_as "is_Eqa"

val is_coEqa = coEqa_def|> strip_all_and_imp |> conjE2
                        |> disch_all |> gen_all
                        |> store_as "is_coEqa" 


val Eqa_Mono = prove_store("Eqa_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qsuff_tac
 ‘h = Eqa(f,g,e,e o h) & g' = Eqa(f,g,e,e o h)’
 >-- (strip_tac >> once_arw[] >> rw[]) >> 
 strip_tac (* 2 *)
 >>(irule is_Eqa >> drule Eq_equality >>
     arw[GSYM o_assoc]))
(form_goal
 “!A B f:A->B g:A->B E e:E->A.isEq(f,g,e) ==> Mono(e)”));


val coEqa_Epi = prove_store("coEqa_Epi",
e0
(rpt strip_tac >> rw[Epi_def] >> rpt strip_tac >>
 qsuff_tac
 ‘h = coEqa(f,g,ce,h o ce) & g' = coEqa(f,g,ce,h o ce)’
 >-- (strip_tac >> once_arw[] >> rw[]) >> 
 strip_tac (* 2 *)
 >>(irule is_coEqa >> drule coEq_equality >> arw[o_assoc]))
(form_goal
 “!A B f:A->B g:A->B cE ce:B->cE.
   iscoEq(f,g,ce) ==> Epi(ce)”));

val via_Eq = prove_store("via_Eq",
e0
(rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
 drule Eq_equality >> arw[GSYM o_assoc])
(form_goal
 “!A B f:A->B g:A->B E e:E->A. isEq(f,g,e) ==>!X h:X->A h0. e o h0 = h ==>
  f o h = g o h”));


val via_coEq = prove_store("via_coEq",
e0
(rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
 drule coEq_equality >> arw[o_assoc])
(form_goal
 “!A B f:A->B g:A->B cE ce:B->cE. iscoEq(f,g,ce) ==>
  !X h:B->X h0. h0 o ce = h ==>
  h o f = h o g”));

val Eq_def_imp = Eqa_def |> strip_all_and_imp |> split_assum
                      |> disch “f:A->B o a:X->A = g o a”
                      |>gen_all
                      |> disch_all |> gen_all

val coEq_def_imp = coEqa_def |> strip_all_and_imp |> split_assum
                      |> disch “x:B->X o f:A->B = x o g”
                      |>gen_all
                      |> disch_all |> gen_all

val via_Eq_iff = prove_store("via_Eq_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule via_Eq >> qexistsl_tac [‘E’,‘e’,‘h0’] >> arw[])>>
 drule Eq_def_imp >> first_x_assum drule >> 
 qexists_tac ‘Eqa(f,g,e,h)’ >> 
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B g:A->B E e:E->A. isEq(f,g,e) ==>
  !X h:X->A.(?h0. e o h0 = h) <=>
  f o h = g o h”));


val via_coEq_iff = prove_store("via_coEq_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule via_coEq >> 
      qexistsl_tac [‘cE’,‘ce’,‘h0’] >> arw[])>>
 drule coEq_def_imp >> first_x_assum drule >> 
 qexists_tac ‘coEqa(f,g,ce,h)’ >> 
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B g:A->B cE ce:B->cE. iscoEq(f,g,ce) ==>
  !X h.(?h0:cE->X. h0 o ce = h) <=>
  h o f = h o g”));


val Pa_distr = proved_th $
e0
(rpt strip_tac >> irule is_Pa >>
 rw[GSYM o_assoc,p12_of_Pa])
(form_goal
“!A B X a1:X ->A a2:X->B X0 x:X0->X. Pa(a1,a2) o x = 
Pa(a1 o x,a2 o x) ”)

val Pa_eq_eq = prove_store("Pa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘p1(A,B) o Pa(f1, g1) = p1(A,B) o Pa(f2, g2) &
          p2(A,B) o Pa(f1, g1) = p2(A,B) o Pa(f2, g2)’
 >-- arw[] >>
 fs[p12_of_Pa])
(form_goal
 “!A X f1:X->A f2:X->A B g1:X->B g2:X->B. 
  Pa(f1,g1) = Pa(f2,g2) <=> f1 = f2 & g1 = g2”));


val coPa_eq_eq = prove_store("coPa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘coPa(f1, g1) o i1(A,B) = coPa(f2, g2) o i1(A,B) &
          coPa(f1, g1) o i2(A,B) = coPa(f2, g2) o i2(A,B)’
 >-- arw[] >>
 fs[i12_of_coPa])
(form_goal
 “!A X f1:A ->X f2:A ->X B g1:B ->X  g2:B->X. 
  coPa(f1,g1) = coPa(f2,g2) <=> f1 = f2 & g1 = g2”));

val Thm1_case1_comm_condition_left = prove_store(
"Thm1_case1_comm_condition_left",
e0
(rpt strip_tac >> rw[Pa_distr,idL] >> dimp_tac >> strip_tac
 >-- arw[] >>
 fs[Pa_eq_eq])
(form_goal
 “!B f:N->B g:1->B. Pa(id(N),f) o O = Pa(O,g) <=> f o O = g”));
 
val Thm1_case1_comm_condition_right = prove_store(
"Thm1_case1_comm_condition_right",
e0
(rpt strip_tac >> 
 rw[Pa_distr,o_assoc,p1_of_Pa,idL,idR,Pa_eq_eq])
(form_goal
 “!B f:N->B h:N * B ->B.
 Pa(SUC o p1(N,B),h) o Pa(id(N),f) = Pa(id(N),f) o SUC <=>
 h o Pa(id(N),f) = f o SUC”));

val Thm1_case1_comm_condition = prove_store(
"Thm1_case1_comm_condition",
e0
(rpt strip_tac >> 
 rw[Thm1_case1_comm_condition_left,
 Thm1_case1_comm_condition_right] >> dimp_tac >> strip_tac >> arw[])
(form_goal
 “!B f0:N->B g:1->B h:N * B -> B. f0 o O = g & f0 o SUC = h o Pa(id(N),f0) <=>
 Pa(id(N),f0) o O = Pa(O,g) &
 Pa(SUC o p1(N,B),h) o Pa(id(N),f0) = Pa(id(N),f0) o SUC”));

val uex_tac:tactic = fn (ct,asl,w) =>
    let val th = uex_def w
        val w' = snd $ dest_dimp $ concl th
    in ([(ct,asl,w')],(sing (dimp_mp_r2l th)))
    end

val comm_with_SUC_id = prove_store("comm_with_SUC_id",
e0
(qspecl_then [‘N’,‘SUC’,‘O’] strip_assume_tac Nind_def >>
 rpt strip_tac >>
 qsuff_tac ‘f = Nind(O,SUC) & id(N) = Nind(O,SUC)’
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[idL,idR])
(form_goal
 “!f:N->N. f o O = O & f o SUC = SUC o f ==> f = id(N)”));

val is_Nind = Nind_def |> spec_all |> conjE2
                       |> gen_all
                       |> store_as "is_Nind"

val Thm1_case_1 = prove_store("Thm1_case_1",
e0
(rpt strip_tac >> uex_tac >> 
 abbrev_tac “Nind(Pa(O,g:1->B),Pa(SUC o p1(N,B),h:N * B->B)) = f'” >>
 abbrev_tac “p2(N,B) o f':N->N * B = f” >>
 qby_tac ‘p1(N,B) o f' = id(N)’ >--
 (irule comm_with_SUC_id >> 
  qpick_x_assum ‘Nind(Pa(O, g), Pa(SUC o p1(N, B), h)) = f'’
  (assume_tac o GSYM) >> arw[] >>
  rw[o_assoc,Nind_def,p1_of_Pa] >> 
  rw[GSYM o_assoc,p1_of_Pa]) >>
 qby_tac ‘f' = Pa(id(N),f)’ >--
 (once_rw[to_P_component] >> rw[p12_of_Pa] >> arw[]) >>
 qexists_tac ‘f’ >>
 qby_tac ‘f' o O = Pa(O,g) & 
  f' o SUC = Pa(SUC o p1(N, B), h) o f'’ 
 >-- (qpick_x_assum 
     ‘Nind(Pa(O, g), Pa(SUC o p1(N, B), h)) = f'’
     (assume_tac o GSYM) >> once_arw[] >>
     rw[Nind_def]) >>
 qby_tac ‘f o O = g & f o SUC = h o Pa(id(N), f)’
 >-- (qpick_x_assum ‘p2(N, B) o f' = f’ (assume_tac o GSYM)>>
      once_arw[] >> rw[o_assoc] >> once_arw[] >>
      rw[GSYM o_assoc,p2_of_Pa] >>
      pop_assum (K all_tac) >>
      pop_assum (K all_tac) >> arw[]) >>
 once_arw[] >> rw[] >>
 rpt strip_tac >> 
 qsuff_tac ‘Pa(id(N), f'') = Pa(id(N), f)’ 
 >-- rw[Pa_eq_eq] >>
 qsuff_tac ‘Pa(id(N), f'') = f'’ >-- arw[] >>
 qsuff_tac ‘Pa(id(N), f'') = 
  Nind(Pa(O, g), Pa(SUC o p1(N, B), h))’ >-- arw[] >>
 irule is_Nind >> 
 rw[Pa_distr,p1_of_Pa,o_assoc,idL,idR] >> once_arw[] >>
 rw[])
(form_goal
 “!B g:1->B h:N * B -> B. ?!f:N->B. f o O = g & f o SUC = h o Pa(id(N),f)”));

val Tp1_ex = prove_store("Tp1_ex",
e0
(rpt strip_tac >> qexists_tac ‘Tp(f o p1(A,1))’ >> rw[])
(form_goal
 “!A B f:A->B. ?tpf:1->Exp(A,B).Tp(f o p1(A,1)) = tpf”)
);

val Tp1_def = Tp1_ex |> spec_all |> ex2fsym0 "Tp1" ["f"] 
                     |> gen_all |> store_as "Tp1_def"; 

fun Tp1 f = mk_fun "Tp1" [f] 


val Tp0_ex = prove_store("Tp0_ex",
e0
(rpt strip_tac >> qexists_tac ‘Ev(X,Y) o Pa(id(X),f o To1(X))’ >>
 rw[])
(form_goal
 “!X Y f:1->Exp(X,Y).?tp0:X->Y. Ev(X,Y) o Pa(id(X),f o To1(X)) = tp0”));

val Tp0_def = 
    Tp0_ex |> spec_all |> ex2fsym0 "Tp0" ["f"] |> gen_all
           |> store_as "Tp0_def"


fun eq_sym a = 
    if mem a (!EqSorts) then 
        let val ns0 = srt2ns a
            val v1 = mk_var ns0
            val v2 = pvariantt (HOLset.add(essps,ns0)) v1
            val v1v2 = mk_eq v1 v2
            val v2v1 = mk_eq v2 v1
            val l2r = assume v1v2 |> sym|> disch_all
            val r2l = assume v2v1 |> sym|> disch_all
        in dimpI l2r r2l
        end
    else raise ERR ("eq_sym.input sort: " ^ a ^ " does not have equality",
                    [],[],[])


val Tp1_Tp0_inv = prove_store("Tp1_Tp0_inv",
e0
(rpt strip_tac >> rw[GSYM Tp1_def,GSYM Tp0_def] >>
 fconv_tac (rewr_fconv (eq_sym "ar")) >> irule is_Tp >>
 rw[o_assoc,Pa_distr,idL] >>
 once_rw[To1_def] >> rw[])
(form_goal
 “!X Y f:1-> Exp(X,Y). Tp1(Tp0(f)) = f”));



val Ev_of_Tp_el = prove_store("Ev_of_Tp_el",
e0
(rpt strip_tac >>
 assume_tac Ev_of_Tp >> 
 first_x_assum (qspecl_then [‘A’,‘B’,‘X’,‘f’] assume_tac) >>
 qby_tac 
 ‘Pa(a, Tp(f) o x) = Pa(p1(A, X), Tp(f) o p2(A, X)) o Pa(a,x)’ >--
 (irule to_P_eq >> rw[p12_of_Pa] >> 
  rw[p12_of_Pa,GSYM o_assoc] >> rw[o_assoc,p12_of_Pa]) >>
 arw[GSYM o_assoc])
(form_goal
 “!A B X f:A * X ->B P a:P->A x: P ->X. 
  Ev(A,B) o Pa(a, Tp(f) o x) = f o Pa(a,x)”));

val Tp0_Tp1_inv = prove_store("Tp0_Tp1_inv",
e0
(rpt strip_tac >> rw[GSYM Tp1_def,GSYM Tp0_def] >>
 rw[Ev_of_Tp_el,o_assoc,p1_of_Pa,idR])
(form_goal
 “!X Y f:X->Y. Tp0(Tp1(f)) = f”));

val Thm1_comm_eq_left = prove_store(
"Thm1_comm_eq_left",
e0
(rpt strip_tac >> 
 qby_tac ‘Pa(p1(A,1), Tp(f) o O o p2(A,1)) = 
 Pa(p1(A,N),Tp(f) o p2(A,N)) o Pa(p1(A,1),O o p2(A,1))’
 >-- rw[Pa_distr,o_assoc,p12_of_Pa] >>
 dimp_tac >> strip_tac (* 2 *) >--
 (qsuff_tac ‘f o Pa(p1(A, 1), O o p2(A, 1)) = 
                 Ev(A,B) o Pa(p1(A,1),(Tp(f) o O) o p2(A,1)) &
             g o p1(A, 1) = 
                 Ev(A,B) o Pa(p1(A,1),Tp1(g) o p2(A,1))’
 >-- (strip_tac >> fs[]) >>
 strip_tac (* 2 *)
 >-- (rw[o_assoc] >> arw[] >>
      rw[GSYM o_assoc,Ev_of_Tp]) >>
 rw[GSYM Tp1_def,Ev_of_Tp]) >>
 rw[GSYM Tp1_def] >> irule is_Tp >> 
 rw[o_assoc] >> arw[GSYM o_assoc,Ev_of_Tp])
(form_goal
 “!A B f: A * N ->B g:A->B. 
  Tp(f) o O = Tp1(g) <=> f o Pa(p1(A,1),O o p2(A,1)) = g o p1(A,1)”));

val Pa_p1_p2 = prove_store("Pa_p1_p2",
e0
(rpt strip_tac >>
 fconv_tac (rewr_fconv (eq_sym "ar")) >>
 irule is_Pa >> rw[idR])
(form_goal
 “!A B. Pa(p1(A,B),p2(A,B)) = id(A * B)”));

val flip_tac = 
fconv_tac (rewr_fconv (eq_sym "ar"));

val Thm1_comm_eq_right = prove_store("Thm1_comm_eq_right",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘Tp(h o l) o Pa(id(N),Tp(f)) = Tp(h o Pa(id(A * N),f)) & 
  Tp(f o Pa(p1(A,N), SUC o p2(A,N))) = Tp(f) o SUC’
 >-- (strip_tac >> dimp_tac >> strip_tac (* 2 *)
      >-- arw[] >>
      irule $ iffLR Tp_eq >> arw[] >>
      qpick_x_assum
      ‘Tp((h o l)) o Pa(id(N), Tp(f)) =
       Tp(h o Pa(id(A * N), f))’
      (assume_tac o GSYM) >> arw[]) >>
 strip_tac (* 2 *) >--
 (irule is_Tp >> 
  qby_tac
  ‘Pa(p1(A, N), (Tp((h o l)) o Pa(id(N), Tp(f))) o p2(A, N))=
   Pa(p1(A,N * Exp(A,B)), Tp(h o l) o p2(A,N * Exp(A,B))) o 
   Pa(p1(A,N),Pa(id(N),Tp(f)) o p2(A,N))’ >-- 
  (irule to_P_eq >> 
   rw[p12_of_Pa,o_assoc] >> rw[GSYM o_assoc,p12_of_Pa] >>
   rw[p12_of_Pa,o_assoc]) >>
  once_arw[] >> rw[GSYM o_assoc,Ev_of_Tp] >>
  rw[o_assoc] >>
  qsuff_tac
  ‘l o Pa(p1(A, N), Pa(id(N), Tp(f)) o p2(A, N)) = 
   Pa(id(A * N), f)’ >--
  (strip_tac >> arw[]) >>
  irule to_P_eq >> rw[p12_of_Pa] >>
  pop_assum (K all_tac) >>
  pop_assum (assume_tac o GSYM) >> arw[] >>
  rw[p12_of_Pa,GSYM o_assoc] >>
  rw[o_assoc,p12_of_Pa,Pa_distr,Ev_of_Tp,idL,idR] >>
  rw[Pa_p1_p2]) >>
 flip_tac >> irule is_Tp >>
 qby_tac
 ‘Pa(p1(A, N), (Tp(f) o SUC) o p2(A, N)) = 
  Pa(p1(A, N), Tp(f) o p2(A,N)) o Pa(p1(A,N),SUC o p2(A,N))’
 >-- (irule to_P_eq >> rw[GSYM o_assoc,p12_of_Pa] >>
      rw[o_assoc,p12_of_Pa]) >>
 arw[GSYM o_assoc,Ev_of_Tp]
 )
(form_goal
 “!A B f:A * N ->B h: (A * N) * B ->B l . 
Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l
 ==>
 (h o Pa(id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N)) <=>
 Tp(h o l) o Pa(id(N),Tp(f)) = Tp(f) o SUC)”));

val Thm1_comm_eq_condition = prove_store(
"Thm1_comm_eq_condition",
e0
(rpt strip_tac >> drule Thm1_comm_eq_right >>
 once_arw[] >> rw[GSYM Thm1_comm_eq_left])
(form_goal
 “!A B f: A * N ->B g:A->B h: (A * N) * B -> B l.
 Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l ==>
 (f o Pa(p1(A,1),O o p2(A,1)) = g o p1(A,1) & 
  h o Pa(id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N)) <=>
  Tp(f) o O = Tp1(g) & Tp(h o l) o Pa(id(N),Tp(f)) = Tp(f) o SUC)
  ”));


val Thm1 = prove_store("Thm1",
e0
(rpt strip_tac >>
 uex_tac >>
 abbrev_tac “Tp(g:A->B o p1(A,1)) = g'” >>
 abbrev_tac “Pa(
 Pa(p1(A,N * Exp(A,B)), p1(N,Exp(A,B)) o p2(A,N * Exp(A,B))),
 Ev(A,B) o 
 Pa(p1(A,N * Exp(A,B)), p2(N,Exp(A,B)) o p2(A,N * Exp(A,B)))) = l” >>
 abbrev_tac “Tp(h:(A * N) * B->B o l:A * N * Exp(A,B) -> (A * N) * B) = h'” >>
 qspecl_then [‘Exp(A,B)’,‘g'’,‘h'’] (assume_tac o uex_expand) Thm1_case_1 >>
 pop_assum (x_choose_then "fb" strip_assume_tac) >>
 qabbrev_tac ‘Ev(A,B) o Pa(p1(A,N),fb o p2(A,N)) = f’ >>
 qby_tac ‘Tp(f) = fb’ >--
 (flip_tac >> irule is_Tp >> arw[]) >>
 qexists_tac ‘f’ >>
 qspecl_then [‘A’,‘B’,‘f’,‘g’] assume_tac
 Thm1_comm_eq_condition >>
 first_x_assum drule >> once_arw[] >>
 qby_tac
 ‘Tp(f) o O = Tp1(g) & 
  Tp((h o l)) o Pa(id(N), Tp(f)) = Tp(f) o SUC’
 >-- arw[GSYM Tp1_def] >>
 arw[] >> strip_tac >>
 qspecl_then [‘A’,‘B’,‘f'’,‘g’] assume_tac
 Thm1_comm_eq_condition >>
 first_x_assum drule >> once_arw[] >>
 rpt strip_tac >>
 irule $ iffLR Tp_eq >> arw[] >> first_x_assum irule >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 qpick_x_assum ‘Tp(f') o O = Tp1(g)’ 
 (assume_tac o GSYM) >> arw[] >> fs[GSYM Tp1_def])
(form_goal
 “!A B g:A->B h:(A * N) * B ->B. 
 ?!f:A * N ->B.
   f o Pa(p1(A,1),O o p2(A,1)) = g o p1(A,1) & 
  h o Pa(id(A * N),f) = f o Pa(p1(A,N), SUC o p2(A,N))”));

val PRE_ex = 
 Thm1_case_1 |> specl (List.map rastt ["N","O","p1(N,N)"])
             |> uex_expand |> rewr_rule[p1_of_Pa]
             |> store_as "PRE_ex";

val PRE_def = PRE_ex |> ex2fsym0 "PRE" []
                     |> store_as "PRE_def";


val rfs = rev_full_simp_tac

val post_inv_Mono = prove_store("post_inv_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qby_tac
 ‘i o m o g = i o m o h’ >-- arw[] >>
 rfs[GSYM o_assoc] >> fs[idL])
(form_goal
 “!A B m:A->B i:B->A. i o m = id(A) ==> Mono(m)”));


val pre_inv_Epi = prove_store("pre_inv_Epi",
e0
(rpt strip_tac >> rw[Epi_def] >> rpt strip_tac >>
 qby_tac
 ‘g o e o i = h o e o i’ >-- arw[GSYM o_assoc] >>
 rfs[idR])
(form_goal
 “!A B e:A->B i:B->A. e o i = id(B) ==> Epi(e)”));

val _ = new_pred "Iso" [("f",ar_sort (mk_ob "A") (mk_ob "B"))]

val Iso_def = store_ax("Iso_def",
“!A B f:A->B. Iso(f) <=> ?f':B->A. f' o f = id(A) & f o f' = id(B)”);

val to_zero_Iso = prove_store("to_zero_Iso",
e0
(rpt strip_tac >> rw[Iso_def] >>
 drule to_zero_zero >> fs[is0_def] >> 
 first_assum 
  (qspecl_then [‘X’] $ strip_assume_tac o uex_expand)>>
 first_assum 
  (qspecl_then [‘A’] $ strip_assume_tac o uex_expand) >>
 last_assum 
  (qspecl_then [‘X’] $ strip_assume_tac o uex_expand) >>
 last_assum 
  (qspecl_then [‘A’] $ strip_assume_tac o uex_expand) >>
 qexists_tac ‘f''''’ >>
 once_arw[] >> rw[])
(form_goal
 “!X. is0(X) ==> !A f:A->X. Iso(f)”));

val Mono_Epi_Iso = prove_store("Mono_Epi_Iso",
e0
(rpt strip_tac >> 
 cases_on “is0(B)” >--
 (drule to_zero_Iso >> arw[]) >>
 drule no_Epi_from_zero >> first_x_assum drule >>
 drule NONZERO_EL >> pop_assum strip_assume_tac >>
 qspecl_then [‘A’,‘B’,‘x’,‘a’] strip_assume_tac AC >>
 rw[Iso_def] >> drule Mono_pinv_post_inv >>
 first_x_assum drule >>
 drule Epi_pinv_pre_inv >> first_x_assum drule >>
 qexists_tac ‘g’ >> arw[])
(form_goal
 “!A B a:A->B. Mono(a) & Epi(a) ==> Iso(a)”));

val DISTI_endo_2 = prove_store("DISTI_endo_2",
e0
(ccontra_tac >> fs[coPa_eq_eq] >>
 fs[i1_ne_i2_1])
(form_goal
 “~(coPa(i1(1,1),i2(1,1)) = coPa(i2(1,1),i1(1,1)))”))

val Thm2_1 = prove_store("Thm2_1",
e0
(strip_tac >> ccontra_tac >>
 qsuff_tac ‘!X t:X->X. t = id(X)’
 >-- (strip_tac >> 
      first_assum 
      (qspecl_then [‘1+1’,‘coPa(i1(1,1),i2(1,1))’] 
      assume_tac) >>
      first_x_assum 
      (qspecl_then [‘1+1’,‘coPa(i2(1,1),i1(1,1))’] 
      assume_tac) >> 
      qby_tac
      ‘coPa(i1(1,1),i2(1,1)) = coPa(i2(1,1),i1(1,1))’
      >-- arw[] >>
      fs[DISTI_endo_2]) >>
 rpt strip_tac >> irule FUN_EXT >> strip_tac >> 
 qby_tac ‘SUC o O = O’ >--
 (qby_tac ‘PRE o SUC o n = PRE o O’ >-- arw[] >>
  assume_tac $ conjE1 PRE_def >> 
  fs[GSYM o_assoc] >> fs[idL]) >>
 qspecl_then [‘X’,‘t’,‘a’] (strip_assume_tac o conjE1) 
 Nind_def >>
 rw[idL] >>
 qby_tac ‘t o a = t o Nind(a, t) o O’ 
 >-- arw[] >>
 fs[GSYM o_assoc] >> 
 qpick_x_assum ‘Nind(a, t) o SUC = t o Nind(a, t)’
 (assume_tac o GSYM) >> arw[] >>
 rw[o_assoc] >> arw[])
(form_goal
 “!n:1->N. ~(SUC o n = O)”));


val Thm2_2 = prove_store("Thm2_2",
e0
(irule post_inv_Mono >>
 qexists_tac ‘PRE’ >> rw[PRE_def])
(form_goal
 “Mono(SUC)”));

val Thm2_3_alt' = prove_store("Thm2_3_alt'",
e0
(rpt strip_tac >> irule Mono_Epi_Iso >>
 arw[] >> irule pre_inv_Epi >>
 qexists_tac ‘Nind(z,s)’ >> irule comm_with_SUC_id >>
 rw[o_assoc,Nind_def] >> arw[GSYM o_assoc])
(form_goal
 “!A a:A->N. Mono(a) ==>
  !s:A->A z:1->A.a o s = SUC o a & a o z = O ==>
  Iso(a)”));

val _ = new_pred "isPb"
  [("f",ar_sort (mk_ob "X") (mk_ob "Z")),
   ("g",ar_sort (mk_ob "Y") (mk_ob "Z")),
   ("p",ar_sort (mk_ob "P") (mk_ob "X")),
   ("q",ar_sort (mk_ob "P") (mk_ob "Y"))];

val isPb_def = store_ax("isPb_def",
“!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y.
 isPb(f, g, p, q) <=> f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v”);

val isPb_expand = isPb_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : A -> P. p:P->X o a = u & q:P->Y o a = v”) |> store_as "isPb_expand";

val Eqa_eqn = Eqa_def |> spec_all |> undisch |> conjE1
                      |> disch_all |> gen_all
                      |> store_as "Eqa_eqn";


val coEqa_eqn = coEqa_def |> spec_all |> undisch |> conjE1
                      |> disch_all |> gen_all
                      |> store_as "coEqa_eqn";

val isPb_ex = prove_store("isPb_ex",
e0
(rpt strip_tac >> rw[isPb_expand] >>
 qspecl_then [‘X * Y’,‘Z’,‘f o p1(X,Y)’,‘g o p2(X,Y)’] (x_choosel_then ["E","e"] assume_tac) isEq_ex >>
 qexistsl_tac [‘E’,‘p1(X,Y) o e’,‘p2(X,Y) o e’] >>
 qby_tac
 ‘f o p1(X, Y) o e = g o p2(X, Y) o e’
 >-- (rw[GSYM o_assoc] >> irule Eq_equality >> arw[]) >>
 arw[] >> rpt strip_tac >>
 qexists_tac ‘Eqa(f o p1(X,Y), g o p2(X,Y),e,Pa(u,v))’ >>
 rw[o_assoc] >>
 qby_tac
 ‘e o Eqa(f o p1(X, Y), g o p2(X, Y), e, Pa(u, v)) = 
  Pa(u,v)’ >--
 (flip_tac >> irule Eqa_eqn >> arw[o_assoc,p12_of_Pa]) >>
 arw[p12_of_Pa] >> rpt strip_tac >>
 drule Eqa_Mono >> fs[Mono_def] >>
 first_x_assum irule >>
 irule to_P_eq >> arw[p12_of_Pa])
(form_goal
 “!X Z f:X->Z Y g:Y->Z. ?P p:P->X q. isPb(f,g,p,q)”));

val Pb_Mono_Mono = prove_store("Pb_Mono_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 drule $ iffLR isPb_expand >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘f o p o h = g o q o h’ >--
 (strip_tac >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘g' = a & h = a’ >-- 
 (strip_tac >> arw[]) >> strip_tac >> 
 first_x_assum irule >> arw[] >>
 fs[Mono_def] >> first_x_assum irule >> 
 qpick_x_assum ‘f o p = g o q’ (assume_tac o GSYM) >>
 arw[GSYM o_assoc] >> arw[o_assoc]) >>
 arw[GSYM o_assoc])
(form_goal
 “!X Z f:X->Z Y g:Y->Z P p:P->X q:P->Y. 
  isPb(f,g,p,q) ==> Mono(g) ==> Mono(p)”));

val surj_Epi = prove_store("surj_Epi",
e0
(rpt strip_tac >> rw[Epi_def] >> rpt strip_tac >>
 irule FUN_EXT >> strip_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[GSYM o_assoc])
(form_goal
 “!A B f:A->B. (!b:1->B.?b0:1->A. f o b0 = b) ==> Epi(f)”));

fun qgenl l th = 
    case l of [] => th
             |h :: t => qgen h (qgenl t th)

val isPb_equality = 
    isPb_expand |> spec_all |> iffLR
                |> undisch |> conjE1
                |> disch_all 
                |> qgenl [‘X’,‘Z’,‘f’,‘Y’,‘g’,‘P’,‘p’,‘q’]
                |> store_as "isPb_equality"

val ind_fac = prove_store("ind_fac",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘N’,‘SUC o a’,‘A’,‘a’] strip_assume_tac 
 isPb_ex>> 
 drule isPb_equality >> 
 qsuff_tac ‘Iso(p)’ 
 >-- (rw[Iso_def] >> strip_tac >> qexists_tac ‘q o f'’ >>
      qpick_x_assum ‘(SUC o a) o p = a o q’ 
       (assume_tac o GSYM) >>
      arw[GSYM o_assoc] >> arw[o_assoc,idR]) >>
 irule Mono_Epi_Iso >> strip_tac (* 2 *)
 >-- (irule surj_Epi >> strip_tac >>
      qby_tac ‘?sn0. SUC o a o b = a o sn0’
      >-- (first_x_assum irule >> qexists_tac ‘b’ >> rw[]) >>
      drule $ iffLR isPb_expand >> 
      pop_assum strip_assume_tac >>
      fs[GSYM o_assoc] >> first_x_assum drule >>
      pop_assum strip_assume_tac >>
      qexists_tac ‘a'’ >> arw[]) >>
 irule Pb_Mono_Mono >>
 qexistsl_tac [‘A’,‘q’,‘N’,‘SUC o a’,‘a’] >> arw[])
(form_goal
 “!A a:A->N. Mono(a) & 
  (!n:1->N. (?n0:1->A. n = a o n0) ==> (?sn0. SUC o n = a o sn0)) ==> ?t:A->A. a o t = SUC o a”));

val Thm2_3' = prove_store("Thm2_3'",
e0
(rpt strip_tac >> irule Thm2_3_alt' >>
 arw[] >> strip_tac (* 2 *)
 >-- (qexists_tac ‘O0’ >> rw[]) >>
 irule ind_fac >> arw[])
(form_goal
 “!A a:A->N. (Mono(a) & (!n:1->N. (?n0:1->A. n = a o n0) ==>
 ?sn0. SUC o n = a o sn0) & ?O0:1->A. O = a o O0) ==> Iso(a)”));

val coEq_of_equal_post_inv = prove_store(
"coEq_of_equal_post_inv",
e0
(rpt strip_tac >> 
 qby_tac ‘iscoEq(f, f, e) & id(B) o f = id(B) o f’
 >-- arw[] >>
 drule coEqa_def >> 
 qexists_tac ‘coEqa(f,f,e,id(B))’ >> 
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal
 “!A B f:A->B cE e:B->cE. iscoEq(f,f,e) ==>
  ?e':cE->B. e' o e = id(B)”));

val Thm3_A_zero_I_zero = prove_store(
"Thm3_A_zero_I_zero",
e0
(rpt strip_tac >> 
 qsuff_tac ‘~(?t:1->I0.T)’ >--
 (strip_tac >> ccontra_tac >> drule NONZERO_EL >> rfs[]) >>
 ccontra_tac >> 
 pop_assum strip_assume_tac >>
 qsuff_tac ‘i1(B,B) o q' o t = i2(B,B) o q' o t’ >--
 rw[i1_i2_disjoint] >>
 drule Eq_equality >>
 qby_tac ‘i1(B, B) o f = i2(B, B) o f’ >--
 (fs[is0_expand] >>
 first_x_assum (qspecl_then [‘B +B’] strip_assume_tac) >>
 fs[]) >> fs[] >>
 drule coEq_of_equal_post_inv >> 
 pop_assum strip_assume_tac >>
 qby_tac ‘e' o (k' o i1(B, B)) o q' =
          e' o (k' o i2(B, B)) o q'’ >-- arw[] >>
 rfs[GSYM o_assoc,idL])
(form_goal
 “!A. is0(A) ==>
  !B f:A->B R' k':B + B -> R'.
  iscoEq(i1(B,B) o f,i2(B,B) o f,k') ==>
  !I0 q':I0->B. isEq(k' o i1(B,B),k' o i2(B,B),q') ==>
  is0(I0)”));

val Thm3_case_zero = prove_store("Thm3_case_zero",
e0
(rpt strip_tac >>
 irule to_zero_Iso >> irule Thm3_A_zero_I_zero >>
 qexistsl_tac [‘A’,‘B’,‘f’,‘q'’,‘R'’,‘k'’] >> arw[])
(form_goal
 “!A B f:A->B. is0(A) ==>
 !R' k':B + B ->R'. iscoEq(i1(B,B) o f, i2(B,B) o f,k') ==>
 !I0 q':I0->B. isEq(k' o i1(B,B), k' o i2(B,B),q') ==> 
 !R k:R->A * A. isEq(f o p1(A,A),f o p2(A,A),k) ==>
 !I' q:A->I'.iscoEq(p1(A,A) o k, p2(A,A) o k,q) ==>
 !h:I'->I0. q' o h o q = f ==> Iso(h)”));


val o_Mono_imp_Mono = prove_store("o_Mono_imp_Mono",
e0
(rpt strip_tac >> fs[Mono_def] >> rpt strip_tac >> 
 first_x_assum irule >> arw[o_assoc])
(form_goal “!A B f:A->B C m:B->C. Mono(m o f) ==> Mono(f)”)
);


val o_Epi_imp_Epi = prove_store("o_Epi_imp_Epi",
e0
(rpt strip_tac >> fs[Epi_def] >> rpt strip_tac >> 
 first_x_assum irule >> arw[GSYM o_assoc])
(form_goal “!A B f:A->B C e:C->A. Epi(f o e) ==> Epi(f)”)
);

val Thm3_case_non_zero = prove_store("Thm3_case_non_zero",
e0
(rpt strip_tac >> irule Mono_Epi_Iso >> 
 drule Eqa_Mono >> rev_drule Eqa_Mono >>
 drule coEqa_Epi >> rev_drule coEqa_Epi >>
 qby_tac ‘~(is0(I0))’ >--
 (ccontra_tac >> 
  qsuff_tac ‘is0(A)’ >-- fs[] >>
  match_mp_tac to_zero_zero (* TODO: find out why match mp can do but irule cannot *) >>
  qexistsl_tac [‘I0’,‘h o q’] >> arw[]) >>
 strip_tac (* 2 *) >--
 (qsuff_tac ‘Epi(h o q)’ >-- 
  (strip_tac >> drule o_Epi_imp_Epi >> arw[]) >>
  rw[Epi_def] >> rpt strip_tac >>
 drule Mono_no_zero_post_inv >> first_x_assum drule >>
 pop_assum (x_choose_then "qi" assume_tac) >>
 qby_tac ‘?w.w o k' = coPa(h' o qi,g o qi)’ >--
 (irule $ iffRL via_coEq_iff >>
  qexistsl_tac [‘A’,‘i1(B, B) o f’,‘i2(B, B) o f’] >>
  arw[i12_of_coPa,GSYM o_assoc] >> 
  qsuff_tac
  ‘(h' o qi) o q' o h o q = h' o (qi o q') o h o q &
   (g o qi) o q' o h o q = g o (qi o q') o h o q’
  >--(strip_tac >> rfs[idL]) >>
  rw[o_assoc]) >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘coPa(h' o qi,g o qi) o i1(B,B) o q' = h' &
 coPa(h' o qi,g o qi) o i2(B,B) o q' = g &
 coPa(h' o qi,g o qi) o i1(B,B) o q' = 
 coPa(h' o qi,g o qi) o i2(B,B) o q'’ >--
 (strip_tac >> rfs[]) >> rpt strip_tac (* 3 *) >--
 (arw[i1_of_coPa,GSYM o_assoc] >> arw[o_assoc,idR]) >--
 (arw[i2_of_coPa,GSYM o_assoc] >> arw[o_assoc,idR]) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 rw[o_assoc] >> rev_drule Eq_equality >>
 fs[o_assoc]) >>
 qsuff_tac ‘Mono(q' o h)’
 >-- (strip_tac >> match_mp_tac o_Mono_imp_Mono >>
      qexistsl_tac [‘B’,‘q'’] >> arw[]) >>
 qby_tac ‘?t.q o t = id(I')’ >--
 (irule Epi_no_zero_pre_inv >> arw[]) >>
 pop_assum strip_assume_tac >> 
 rw[Mono_def] >> rpt strip_tac >>
 qby_tac ‘?w.k o w = Pa(t o h',t o g)’ >--
 (irule $ iffRL via_Eq_iff >> 
  qexistsl_tac [‘B’,‘f o p1(A, A)’,‘f o p2(A, A)’] >>
  arw[o_assoc,p12_of_Pa] >> 
  qby_tac
  ‘(q' o h o q) o t o h' = q' o h o (q o t) o h' & 
   (q' o h o q) o t o g = q' o h o (q o t) o g’ >--
  rw[o_assoc] >>
  qpick_x_assum ‘q' o h o q = f’ (assume_tac o GSYM) >>
  arw[] >> fs[idR,idL,o_assoc]) >>
 pop_assum strip_assume_tac >> 
 qsuff_tac ‘q o p1(A,A) o Pa(t o h', t o g) = h' &
            q o p2(A,A) o Pa(t o h', t o g) = g &
            q o p1(A,A) o Pa(t o h', t o g) = 
            q o p2(A,A) o Pa(t o h', t o g)’ >--
 (rpt strip_tac >> rfs[]) >> rpt strip_tac (* 3 *)
 >-- (arw[p1_of_Pa] >> arw[GSYM o_assoc,idL])
 >-- (arw[p2_of_Pa] >> arw[GSYM o_assoc,idL]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 drule coEq_equality >> fs[GSYM o_assoc])
(form_goal
 “!A B f:A->B. ~(is0(A)) ==>
 !R' k':B + B ->R'. iscoEq(i1(B,B) o f, i2(B,B) o f,k') ==>
 !I0 q':I0->B. isEq(k' o i1(B,B), k' o i2(B,B),q') ==> 
 !R k:R->A * A. isEq(f o p1(A,A),f o p2(A,A),k) ==>
 !I' q:A->I'.iscoEq(p1(A,A) o k, p2(A,A) o k,q) ==>
 !h:I'->I0. q' o h o q = f ==> Iso(h)”));


val unique_h_lemma = prove_store("unique_h_lemma",
e0
(rpt strip_tac >> qexists_tac ‘h’ >> strip_tac >>
 dimp_tac >> strip_tac >> rfs[])
(form_goal 
“!A B f:A->B C q:A->C D g:D->B k:A->D h:C->D.
 (!k'. g o k' = f <=> k' = k) &
 (!h'. h' o q = k <=> h' = h) ==>
 (?h:C->D. !h0. g o h0 o q = f <=> h0 = h)”));


val Eqa_def_alt = prove_store("Eqa_def_alt",
e0
(rpt strip_tac >> drule Eq_def_imp >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 dimp_tac >> strip_tac (* 2 *) >--
 (first_x_assum irule >> flip_tac >> 
 first_x_assum accept_tac) >>
 once_arw[] >> rw[] )
(form_goal
 “!A B f:A->B g:A->B E e:E->A.
 isEq(f,g,e) ==>
 !X a:X->A. f o a = g o a ==> 
 !a0:X->E. e o a0 = a <=> a0 = Eqa(f,g,e,a) ”));


val coEqa_def_alt = prove_store("coEqa_def_alt",
e0
(rpt strip_tac >> drule coEq_def_imp >> 
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 dimp_tac >> strip_tac (* 2 *) >--
 (first_x_assum irule >> flip_tac >> 
 first_x_assum accept_tac) >>
 once_arw[] >> rw[] )
(form_goal
 “!A B f:A->B g:A->B cE ce:B->cE.
 iscoEq(f,g,ce) ==>
 !X x:B->X. x o f = x o g ==> 
 !x0:cE->X. x0 o ce = x <=> x0 = coEqa(f,g,ce,x) ”));

val Thm3_h_exists = prove_store("Thm3_h_exists",
e0
(rpt strip_tac >> match_mp_tac unique_h_lemma >>
 qexistsl_tac
 [‘Eqa(k' o i1(B,B),k' o i2(B,B),q',f)’,
  ‘coEqa(p1(A,A) o k,p2(A,A) o k,q,
        Eqa(k' o i1(B,B),k' o i2(B,B),q',f))’] >>
 rpt strip_tac 
 >-- (rev_drule Eqa_def_alt >>
      first_x_assum irule >>
      rev_drule coEq_equality >> fs[o_assoc]) >>
 drule coEqa_def_alt >> first_x_assum irule >>
 drule Eq_equality >>
 rev_drule Eqa_Mono >> fs[Mono_def] >>
 first_x_assum irule >>
 qsuff_tac
 ‘q' o Eqa((k' o i1(B, B)), (k' o i2(B, B)), q', f) = f’ 
 >-- (strip_tac >> arw[GSYM o_assoc]) >>
 rev_drule Eqa_def_alt >> 
 first_x_assum (qspecl_then [‘A’,‘f’] assume_tac) >> 
 rev_drule coEq_equality >> fs[o_assoc])
(form_goal 
“!A B f:A->B.
 !R' k':B + B->R'. iscoEq(i1(B,B) o f,i2(B,B) o f,k') ==>
 !I0 q':I0->B. isEq(k' o i1(B,B), k' o i2(B,B),q') ==>
 !R k:R->A * A. isEq(f o p1(A,A),f o p2(A,A),k) ==>
 !I' q:A->I'.iscoEq(p1(A,A) o k, p2(A,A) o k,q) ==>
 ?h:I' ->I0.!h0. q' o h0 o q = f <=> h0 = h”));

val Thm3_without_assume_exists = prove_store(
"Thm3_without_assume_exists",
e0
(rpt strip_tac >>
 drule Thm3_h_exists >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘h’ >>
 qby_tac ‘q' o h o q = f’ >-- arw[] >>
 cases_on “is0(A)” (* 3 *) >-- 
 (qspecl_then [‘A’,‘B’,‘f’] assume_tac Thm3_case_zero >>
  first_x_assum drule >> strip_tac >> 
  first_x_assum drule >> first_x_assum drule >>
  first_x_assum drule >> first_x_assum drule >>
  dimp_tac >> strip_tac >> rfs[] >> 
  first_x_assum irule >> 
  first_x_assum (qspecl_then [‘h’] assume_tac) >>
  fs[]) >>
 qspecl_then [‘A’,‘B’,‘f’] assume_tac Thm3_case_non_zero >>
  first_x_assum drule >> strip_tac >> 
  first_x_assum drule >> first_x_assum drule >>
  first_x_assum drule >> first_x_assum drule >>
  dimp_tac >> strip_tac >> rfs[] >> 
  first_x_assum irule >> 
  first_x_assum (qspecl_then [‘h’] assume_tac) >>
  fs[])
(form_goal
 “!A B f:A->B.
 !R' k':B + B->R'. iscoEq(i1(B,B) o f,i2(B,B) o f,k') ==>
 !I0 q':I0->B. isEq(k' o i1(B,B), k' o i2(B,B),q') ==>
 !R k:R->A * A. isEq(f o p1(A,A),f o p2(A,A),k) ==>
 !I' q:A->I'.iscoEq(p1(A,A) o k, p2(A,A) o k,q) ==>
 ?h:I' ->I0.!h0. q' o h0 o q = f & Iso(h) <=> h0 = h”));

val Iso_Mono = prove_store("Iso_Mono",
e0
(rw[Iso_def,Mono_def] >> rpt strip_tac >> 
 qsuff_tac ‘f' o f o g = f' o f o h’ 
 >-- (arw[GSYM o_assoc,idL]) >> arw[])
(form_goal “!A B f:A->B.Iso(f) ==> Mono(f)”));


val o_Mono_Mono = prove_store("o_Mono_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 fs[o_assoc,Mono_def] >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal 
“!A B f:A->B. Mono(f) ==> !C g:B->C. Mono(g) ==>
 Mono(g o f)”));

val Mono_o_Iso_Mono = prove_store("Mono_o_Iso_Mono",
e0
(rpt strip_tac >> irule o_Mono_Mono >> 
 drule Iso_Mono >> arw_tac[])
(form_goal “!X A i:X->A.Iso(i) ==> !B f:A->B. Mono(f) ==> Mono(f o i)”));

val Mono_Epi_fac = prove_store("Mono_Epi_fac",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘B + B’,‘i1(B,B) o f’,‘i2(B,B) o f’]
 (x_choosel_then ["R'","k'"] assume_tac) iscoEq_ex >>
 qspecl_then [‘B’,‘R'’,‘k' o i1(B,B)’,‘k' o i2(B,B)’]
 (x_choosel_then ["I0","q'"] assume_tac) isEq_ex >> 
 qspecl_then [‘A * A’,‘B’,‘f o p1(A,A)’,‘f o p2(A,A)’]
 (x_choosel_then ["R","k"] assume_tac) isEq_ex >>
 qspecl_then [‘R’,‘A’,‘p1(A,A) o k’,‘p2(A,A) o k’]
 (x_choosel_then ["I'","q"] assume_tac) iscoEq_ex >> 
 drule Thm3_without_assume_exists >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qby_tac ‘q' o h o q = f & Iso(h)’ >-- arw[] >>
 rev_drule Eqa_Mono >> drule coEqa_Epi >>
 qexistsl_tac [‘I'’,‘q' o h’,‘q’] >> arw[o_assoc] >>
 irule Mono_o_Iso_Mono >> arw[])
(form_goal
 “!A B f:A->B. ?X m:X->B e:A->X. Epi(e) & Mono(m) & f = m o e”)); 

val Epi_surj = prove_store("Epi_surj",
e0
(rpt strip_tac >>
 drule Epi_has_section >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘s0 o b’ >> fs[GSYM o_assoc,idL])
(form_goal “!A B f:A->B. Epi(f) ==> (!b:1->B. ?b0:1->A. f o b0 = b)”));

val Thm4 = prove_store("Thm4",
e0
(rpt strip_tac >> 
 abbrev_tac 
 “Ev(X,1+1) o Pa(p1(X,J),ss:J->Exp(X,1+1) o p2(X,J)) = s0” >>
 abbrev_tac “i2(1,1) o To1(X * J) = i2t” >>
 qspecl_then [‘X * J’,‘1 + 1’,‘s0’,‘i2t’]
 (x_choosel_then ["E","k"] assume_tac) isEq_ex >>
 qspecl_then [‘E’,‘X’,‘p1(X,J) o k’]
 (x_choosel_then ["U","a","q"] strip_assume_tac)
 Mono_Epi_fac >> qexistsl_tac [‘U’,‘a’] >> arw[] >> 
 strip_tac >> 
 qby_tac ‘!j:1->J. Ev(X,1+1) o Pa(x,ss o j) = i2(1,1) <=>
 s0 o Pa(x,j) = i2(1,1)’ >--
 (strip_tac >>
  qsuff_tac ‘Ev(X,1+1) o Pa(x,ss o j) = s0 o Pa(x,j)’
  >-- (strip_tac >> arw[]) >>
  last_x_assum (assume_tac o GSYM) >> arw[o_assoc] >>
  qsuff_tac 
  ‘Pa(x, ss o j) = Pa(p1(X, J), (ss o p2(X, J))) o Pa(x, j)’
  >-- (strip_tac >> arw[]) >>
  irule to_P_eq >> rw[p12_of_Pa] >>
  rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc, p12_of_Pa]) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *) >--
 (drule Epi_surj >> 
 first_x_assum 
 (qspecl_then [‘x0’] $ x_choose_then "xb" assume_tac) >>
 qexists_tac ‘p2(X,J) o k o xb’ >>
 qby_tac ‘Pa(x,p2(X,J) o k o xb) = k o xb’ >--
 (irule to_P_eq >> rw[p12_of_Pa] >> arw[GSYM o_assoc] >>
  arw[o_assoc]) >>
 drule Eq_equality >>
 qby_tac ‘i2t o k o xb = i2(1,1)’ >--
 (qpick_x_assum ‘i2(1, 1) o To1(X * J) = i2t’
  (assume_tac o GSYM) >> once_arw[] >>
  rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) >>
 arw[]>> arw[GSYM o_assoc] >> arw[o_assoc]) >>
 qexists_tac ‘q o Eqa(s0,i2t,k,Pa(x,j))’ >>
 qpick_x_assum ‘p1(X, J) o k = a o q’ (assume_tac o GSYM) >>
 arw[GSYM o_assoc] >> 
 qby_tac ‘k o Eqa(s0, i2t, k, Pa(x, j)) = Pa(x,j)’
 >-- (flip_tac >> irule Eqa_eqn >> arw[] >>
      qpick_x_assum ‘i2(1, 1) o To1(X * J) = i2t’
      (assume_tac o GSYM) >> arw[o_assoc] >> 
      once_rw[one_to_one_id] >> rw[idR]) >>
 arw[o_assoc,p1_of_Pa]
 )
(form_goal
 “!J X ss:J-> Exp(X,1+1).
  ?U a:U->X. Mono(a) & 
   !x:1->X.
   (?x0. x = a o x0) <=>
   ?j:1->J. Ev(X,1+1) o Pa(x,ss o j) = i2(1,1)”));


val from_one_Mono = prove_store("from_one_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 qspecl_then [‘X'’] strip_assume_tac To1_def >> arw[])
(form_goal
 “!X f:1->X.Mono(f)”));

val Mono_disjoint_coPa_Mono = prove_store
("Mono_disjoint_coPa_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 irule FUN_EXT >> strip_tac >>
 qspecl_then [‘A’,‘B’,‘g o a'’] assume_tac INC_FAC >>
 qspecl_then [‘A’,‘B’,‘h o a'’] assume_tac INC_FAC >>
 pop_assum_list (map_every strip_assume_tac) (* 4 *)
 >-- (*case 1, use a is mono, both via a*)
 (qsuff_tac ‘f0 = f0'’ >-- (strip_tac >> fs[]) >>
  fs[Mono_def] >> first_x_assum irule >>
  qsuff_tac ‘coPa(a,b) o i1(A,B) o f0 = 
             coPa(a,b) o i1(A,B) o f0'’
  >-- rw[GSYM o_assoc,i1_of_coPa] >>
  arw[] >> arw[GSYM o_assoc])
 >-- (*case 2, h via a, g via b, contradiction*)
 (qsuff_tac ‘a o f0 = b o f0'’ >-- arw[] >>
  qsuff_tac ‘coPa(a,b) o i1(A,B) o f0 = 
             coPa(a,b) o i2(A,B) o f0'’
  >-- rw[GSYM o_assoc,i12_of_coPa] >>
  arw[] >> rw[GSYM o_assoc] >> arw[])
 >-- (*case 3, h via b, g via a, contradiction*)
 (qsuff_tac ‘a o f0' = b o f0’ >-- arw[] >>
  qsuff_tac ‘coPa(a,b) o i1(A,B) o f0' = 
             coPa(a,b) o i2(A,B) o f0’
  >-- rw[GSYM o_assoc,i12_of_coPa] >>
  arw[] >> rw[GSYM o_assoc] >> arw[]) >>
 (*case 4, both via b, use b mono*)
 qsuff_tac ‘f0 = f0'’ >-- (strip_tac >> fs[]) >>
 fs[Mono_def] >> last_x_assum irule >>
 qsuff_tac ‘coPa(a,b) o i2(A,B) o f0 = 
            coPa(a,b) o i2(A,B) o f0'’
 >-- rw[GSYM o_assoc,i2_of_coPa] >>
 arw[] >> arw[GSYM o_assoc])
(form_goal
 “!A X a:A->X.Mono(a) ==>
  !B b:B->X. Mono(b) ==>
  (!a0:1->A b0:1->B. ~(a o a0 = b o b0)) ==>
  Mono(coPa(a,b))”));

val Thm5_lemma_1 = prove_store("Thm5_lemma_1",
e0
(rpt strip_tac >> 
 qby_tac ‘~(is0(A + 1))’ 
 >-- (ccontra_tac >> drule zero_no_MEM >>
      qby_tac ‘?f:1->A +1 . T’ 
      >-- (qexists_tac ‘i2(A,1)’ >> rw[]) >> fs[]) >>
 qby_tac ‘Mono(coPa(a,x))’
 >-- (irule Mono_disjoint_coPa_Mono >>
      arw[from_one_Mono] >> rpt strip_tac >>
      once_rw[one_to_one_id] >> arw[idR]) >>
 drule Mono_no_zero_post_inv >> first_x_assum drule >>
 pop_assum (x_choose_then "u" assume_tac) >>
 qexists_tac ‘coPa(i1(1,1) o To1(A),i2(1,1)) o u’ >>
 rw[o_assoc] >>
 qby_tac ‘u o coPa(a, x) o i2(A,1) = id(A + 1) o i2(A,1)’
 >-- arw[GSYM o_assoc] >>
 qby_tac ‘u o coPa(a, x) o i1(A,1) = id(A + 1) o i1(A,1)’
 >-- arw[GSYM o_assoc] >>
 fs[i12_of_coPa,idL,idR])
(form_goal
 “!A X a:A->X.Mono(a) ==>
  !x:1->X. (!x0:1->A. ~(a o x0 = x)) ==>
  ?phi:X->1+1. phi o x = i2(1,1) & phi o a = i1(1,1) o To1(A)”));


val Thm5_constructions = prove_store("Thm5_constructions",
e0
(rpt strip_tac >>
 qexists_tac ‘Tp(i1(1,1) o To1(A * 1))’ >> rw[] >> 
 qexists_tac 
 ‘Tp(Ev(X, 1 + 1) o
  Pa(a o p1(A, Exp(X, 1 + 1)), p2(A, Exp(X, 1 + 1))))’ >>
 rw[] >> rpt strip_tac >>
 qexists_tac 
 ‘Ev(X, 1 + 1) o Pa(p1(X, L), u o p2(X, L))’ >>
 rw[] >> rpt strip_tac >>
 qspecl_then [‘E’,‘X’,‘p1(X,L) o k’] 
 assume_tac Mono_Epi_fac >>
 first_x_assum accept_tac)
(form_goal 
“!A X a:A->X.Mono(a) ==> 
 ?j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 &
 ?a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 &
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 ?ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub & 
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 ?A' a':A'->X q:E->A'.Epi(q) & Mono(a') & p1(X,L) o k = a' o q”));

val Thm5_Mono = prove_store("Thm5_Mono",
e0
(rpt strip_tac >> 
 qby_tac
 ‘(j0 o To1 (Exp(X,1+1))) o u = a2 o u’
 >-- (rev_drule Eq_equality >> arw[]) >>
 qby_tac
 ‘Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1))) =
  Ev(A,1+1) o Pa(p1(A,Exp(X,1+1)), a2 o p2(A,Exp(X,1+1)))’
 >-- (qpick_x_assum
      ‘Tp(Ev(X, 1 + 1) o Pa(a o p1(A, Exp(X, 1 + 1)), p2(A, Exp(X, 1 + 1)))) = a2’ (assume_tac o GSYM) >>
     arw[] >> rw[Ev_of_Tp]) >>
 qby_tac
 ‘Pa(p1(A, Exp(X, 1 + 1)),a2 o p2(A, Exp(X, 1 + 1))) o 
  Pa(p1(A,L),u o p2(A,L)) =
  Pa(p1(A,L), a2 o u o p2(A,L))’
 >-- (irule to_P_eq >> rw[p12_of_Pa] >>
      rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc,p12_of_Pa]) >>
 qby_tac
 ‘!x:1->X.(?x0: 1-> A.a o x0 = x) ==>
  !t: 1 -> Exp(X,1+1).
   (?t0:1 -> L. u o t0 = t) ==>
   Ev(X,1+1) o Pa(x,t) = i1(1,1)’
 >-- (rpt strip_tac >>
      qby_tac 
      ‘Pa(a o x0,u o t0) = 
       Pa(a o p1(A, Exp(X, 1 + 1)), p2(A, Exp(X, 1 + 1))) o
       Pa(p1(A,L), u o p2(A,L)) o Pa(x0,t0)’ >--
      (irule to_P_eq >> rw[p12_of_Pa] >>
       rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc,p12_of_Pa] >>
       qby_tac
       ‘a o p1(A, Exp(X, 1 + 1)) o Pa(p1(A, L), (u o p2(A, L))) o Pa(x0, t0) =  a o (p1(A, Exp(X, 1 + 1)) o Pa(p1(A, L), (u o p2(A, L)))) o Pa(x0, t0)’ >-- rw[o_assoc] >>
       arw[p12_of_Pa]) >>
      qpick_x_assum ‘a o x0 = x’
      (assume_tac o GSYM) >> 
      qpick_x_assum ‘u o t0 = t’
      (assume_tac o GSYM) >> once_arw[] >> 
      once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >>
      qby_tac
      ‘(Ev(A, 1 + 1) o Pa(p1(A, Exp(X, 1 + 1)), a2 o p2(A, Exp(X, 1 + 1)))) o Pa(p1(A, L), u o p2(A, L)) =
       Ev(A, 1 + 1) o Pa(p1(A, Exp(X, 1 + 1)), a2 o p2(A, Exp(X, 1 + 1))) o Pa(p1(A, L), u o p2(A, L))’ >-- rw[o_assoc]>>
      arw[] >>
      qpick_x_assum ‘(j0 o To1(Exp(X, 1 + 1))) o u = a2 o u’
      (assume_tac o GSYM)  >>
      arw[GSYM o_assoc] >> 
      qby_tac
      ‘Pa(p1(A, L), ((j0 o To1(Exp(X, 1 + 1))) o u) o p2(A, L)) = Pa(p1(A,1),j0 o p2(A,1)) o Pa(p1(A,L),(To1(Exp(X,1+1)) o u) o p2(A,L))’ 
      >-- (irule to_P_eq >> rw[p12_of_Pa] >>
           rw[GSYM o_assoc,p12_of_Pa] >>
           rw[o_assoc,p12_of_Pa]) >>
      fs[o_assoc] >>
      qpick_x_assum ‘Tp(i1(1, 1) o To1(A * 1)) = j0’
      (assume_tac o GSYM) >> arw[GSYM o_assoc,Ev_of_Tp] >>
      rw[o_assoc]>> once_rw[one_to_one_id] >> rw[idR]) >>
qby_tac 
 ‘!x:1 -> X. 
  (?xb: 1 -> A'. a' o xb = x) ==>
  ?t: 1-> Exp(X,1+1). (?t0:1-> L.u o t0 = t) &
  Ev(X,1+1) o Pa(x,t) = i2(1,1)’
>-- (rpt strip_tac >> 
     qby_tac ‘?x0:1 -> E. q o x0 = xb’
     >-- (drule Epi_surj >> 
          first_x_assum $ qspecl_then [‘xb’] accept_tac) >>
     pop_assum strip_assume_tac >>
     qexists_tac ‘u o p2(X,L) o k o x0’ >>
     strip_tac (* 2 *) >--
     (qexists_tac ‘p2(X,L) o k o x0’ >> rw[]) >>
     qby_tac 
     ‘Pa(x, u o p2(X,L) o k o x0) = 
      Pa(p1(X,L), u o p2(X,L)) o
      Pa(x:1->X,p2(X,L) o k o x0)’
     >-- (irule to_P_eq >> rw[p12_of_Pa] >>
          rw[GSYM o_assoc,p12_of_Pa] >> 
          rw[o_assoc,p12_of_Pa]) >>
     once_arw[] >> drule Eq_equality >> 
     rw[GSYM o_assoc] >> once_arw[] >>
     qby_tac ‘x = p1(X,L) o k o x0’ 
     >-- (rw[GSYM o_assoc] >> arw[] >> arw[o_assoc]) >>
     once_arw[] >> rw[o_assoc,GSYM to_P_component] >>
     arw[GSYM o_assoc] >>
     rw[o_assoc] >> once_rw[one_to_one_id] >>
     rw[idR]) >>
qby_tac 
 ‘!x:1->X. (~((?x0:1->A. a o x0 = x) &
             ?x0:1->A'. a' o x0 = x))’ 
>-- (rpt strip_tac >> ccontra_tac >>
     pop_assum strip_assume_tac >>
     qsuff_tac ‘i1(1,1) = i2(1,1)’ >-- rw[i1_ne_i2_1] >>
     qby_tac ‘?xb : 1 -> A'. a' o xb = x’ 
     >-- (qexists_tac ‘x0'’ >> arw[]) >>
     first_x_assum drule >> 
     pop_assum strip_assume_tac >> 
     qby_tac ‘?x0 : 1 -> A. a o x0 = x’ 
     >-- (qexists_tac ‘x0’ >> arw[]) >>
     first_x_assum drule >> 
     pop_assum strip_assume_tac >> 
     first_x_assum $ qspecl_then [‘t’] assume_tac >>
     qby_tac ‘?(t0 : 1 -> L). u o t0 = t’ 
     >-- (qexists_tac ‘t0’ >> arw[]) >>
     first_x_assum drule >> fs[]) >> 
irule Mono_disjoint_coPa_Mono >> arw[] >>
rpt strip_tac >> ccontra_tac >>
qsuff_tac
‘((?x0 :1->A. a o x0 = a' o b0) &
   ?(x0 :1->A'). a' o x0 = a' o b0)’ >-- arw[] >>
strip_tac (* 2 *)
>-- (qexists_tac ‘a0’ >> arw[]) >>
qexists_tac ‘b0’ >> arw[] )
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) & Mono(a') & p1(X,L) o k = a' o q ==> Mono(coPa(a,a'))”));


val Thm5_Epi_ex_xp_a2phi0 = prove_store(
"Thm5_Epi_ex_xp_a2phi0",
e0
(rpt strip_tac >> irule Ev_eq_eq >>
 rw[o_assoc] >> 
 qby_tac
 ‘j0 o To1(Exp(X, 1 + 1)) o phi0 o p2(A, 1) = 
  j0 o (To1(Exp(X, 1 + 1)) o phi0) o p2(A, 1)’ >-- 
 rw[o_assoc] >>
 once_arw[] >> once_rw[one_to_one_id] >> rw[idL] >>
 qby_tac
 ‘Pa(p1(A, 1), a2 o phi0 o p2(A, 1)) = 
  Pa(p1(A,Exp(X,1+1)), a2 o p2(A,Exp(X,1+1))) o 
  Pa(p1(A,1),phi0 o p2(A,1))’
 >-- (irule to_P_eq >> rw[p12_of_Pa] >>
      rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc,p12_of_Pa]) >>
 once_arw[] >> rw[GSYM o_assoc] >> 
 qpick_x_assum ‘Tp(Ev(X, 1 + 1) o Pa(a o p1(A, Exp(X, 1 + 1)), p2(A, Exp(X, 1 + 1)))) = a2’ (assume_tac o GSYM) >>
 once_arw[] >> rw[Ev_of_Tp] >> 
 qpick_x_assum ‘Tp(i1(1, 1) o To1(A * 1)) = j0’
 (assume_tac o GSYM) >> once_arw[] >> rw[Ev_of_Tp] >>
 qpick_x_assum ‘Tp(phi o p1(X, 1)) = phi0’
 (assume_tac o GSYM) >> once_arw[] >>
 rw[Pa_distr,o_assoc,p12_of_Pa] >>
 qby_tac 
 ‘Pa(a o p1(A, 1), Tp((phi o p1(X, 1))) o p2(A, 1)) = 
  Pa(p1(X,1), phi0 o p2(X,1)) o Pa(a o p1(A,1), p2(A,1))’
 >-- (irule to_P_eq >> rw[p12_of_Pa] >>
      rw[GSYM o_assoc,p12_of_Pa] >> 
      rw[o_assoc,p12_of_Pa] >> arw[]) >>
 arw[] >> rw[GSYM o_assoc,Ev_of_Tp] >>
 rw[o_assoc,p12_of_Pa] >> arw[GSYM o_assoc] >>
 rw[o_assoc] >> once_rw[To1_def]>> rw[]
 )
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) ==> Mono(a') ==>
  p1(X,L) o k = a' o q ==> 
 !b:1->X.(~(?b0:1 -> A. a o b0 = b)) ==> 
 !phi. phi o a = i1(1,1) o To1(A) ==> phi o b = i2(1,1) ==>
 !phi0.Tp(phi o p1(X,1)) = phi0 ==>
   a2 o phi0 = (j0 o To1 (Exp(X,1+1))) o phi0”));


val Thm5_Epi_ex_xp = prove_store(
"Thm5_Epi_ex_xp",
e0
(rpt strip_tac >> 
 assume_tac (Thm5_Epi_ex_xp_a2phi0 |> strip_all_and_imp) >>
 qby_tac
 ‘?phi0':1->L. u o phi0' = Tp(phi o p1(X,1))’
 >-- (qexists_tac ‘Eqa(a2,j0 o To1(Exp(X,1+1)),u,phi0)’ >>
      arw[] >> flip_tac >> irule Eqa_eqn >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘ub o Pa(b, phi0') = 
  (i2(1,1) o To1 (X * L)) o Pa(b, phi0')’
 >-- (qby_tac ‘Pa(p1(X,L),u o p2(X,L)) o Pa(b, phi0') = 
               Pa(b, u o phi0')’
      >-- (irule to_P_eq >> rw[p12_of_Pa] >>
           rw[GSYM o_assoc,p12_of_Pa] >> 
           rw[o_assoc,p12_of_Pa]) >>
      qsuff_tac ‘Ev(X,1+1) o Pa(b,phi0) = phi o b’
      >-- (strip_tac >> rw[o_assoc] >>
           once_rw[one_to_one_id] >> rw[idR] >>
           qpick_x_assum 
           ‘Ev(X, 1 + 1) o Pa(p1(X, L), u o p2(X, L)) = ub’
           (assume_tac o GSYM) >>
           arw[o_assoc]) >> 
      qpick_x_assum 
      ‘Tp(phi o p1(X, 1)) = phi0’ (assume_tac o GSYM) >>
      arw[] >> 
      qby_tac ‘Tp(phi o p1(X, 1)) = 
      Tp(phi o p1(X, 1)) o id(1)’ >-- rw[idR] >>
      once_arw[] >> rw[Ev_of_Tp_el,o_assoc,p1_of_Pa]>>
      first_x_assum accept_tac) >>
 qby_tac
 ‘?bp0:1->E.k o bp0 = Pa(b,phi0')’ 
 >-- (qexists_tac 
      ‘Eqa(ub,i2(1,1) o To1(X * L),k,Pa(b, phi0'))’ >>
      flip_tac >> irule Eqa_eqn >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘bp0’ >> irule to_P_eq >>
 rw[p12_of_Pa] >> rw[GSYM o_assoc,p12_of_Pa] >>
 arw[o_assoc,p12_of_Pa])
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) ==> Mono(a') ==>
  p1(X,L) o k = a' o q ==> 
 !b:1->X.(~(?b0:1 -> A. a o b0 = b)) ==> 
 !phi. phi o a = i1(1,1) o To1(A) ==> phi o b = i2(1,1) ==>
 !phi0.Tp(phi o p1(X,1)) = phi0 ==>
   ?xp:1->E. Pa(p1(X,L),u o p2(X,L)) o k o xp = 
  Pa(b,phi0)”));


val Thm5_Epi = prove_store("Thm5_Epi",
e0
(rpt strip_tac >> irule surj_Epi >> strip_tac >>
 cases_on “?b0:1->A. a:A->X o b0 = b” >--
 (pop_assum strip_assume_tac >> 
  qexists_tac ‘i1(A,A') o b0’ >> 
  arw[GSYM o_assoc,i1_of_coPa]) >>
 qsuff_tac ‘?b0':1->A'. a' o b0' = b’ >--
 (strip_tac >> qexists_tac ‘i2(A,A') o b0'’ >>
  arw[GSYM o_assoc,i2_of_coPa]) >>
 rev_drule Thm5_lemma_1 >> 
 qby_tac ‘!x0:1->A. ~(a o x0 = b)’
 >-- (strip_tac >> ccontra_tac >>
      qby_tac ‘?b0.a o b0 = b’ 
      >-- (qexists_tac ‘x0’ >> arw[]) >>
      fs[]) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 abbrev_tac “Tp(phi:X->1+1 o p1(X,1)) = phi0” >>
 assume_tac (strip_all_and_imp Thm5_Epi_ex_xp) >>
 pop_assum strip_assume_tac >> 
 qexists_tac ‘q o xp’ >> 
 qby_tac ‘p1(X,Exp(X,1+1)) o Pa(b,phi0) = b’
 >-- rw[p1_of_Pa] >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 rw[GSYM o_assoc,p1_of_Pa] >> once_arw[] >> rw[])
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) & Mono(a') & p1(X,L) o k = a' o q ==> Epi(coPa(a,a'))”));

val Thm5_Iso = prove_store("Thm5_Iso",
e0
(rpt strip_tac >> irule Mono_Epi_Iso >>
 rev_drule Thm5_Mono >> 
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> 
 qby_tac ‘Mono(coPa(a, a'))’ >--
 (first_x_assum irule >> arw[] >>
  qexists_tac ‘q’ >> arw[]) >> arw[] >>
 rev_drule Thm5_Epi >> 
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> 
 first_x_assum irule >> arw[] >>
 qexists_tac ‘q’ >> arw[])
(form_goal
“!A X a:A->X.Mono(a) ==> 
 !j0:1->Exp(A,1 + 1). Tp(i1(1,1) o To1(A * 1)) = j0 ==>
 !a2:Exp(X,1+1)->Exp(A,1+1).
 Tp(Ev(X,1+1) o Pa(a o p1(A,Exp(X,1+1)),p2(A,Exp(X,1+1)))) = a2 ==> 
 !L u:L-> Exp(X,1+1). isEq(a2,j0 o To1(Exp(X,1+1)),u) ==>
 !ub:X * L-> 1 + 1. 
 Ev(X,1+1) o Pa(p1(X,L),u o p2(X,L)) = ub ==>
 !E k:E->X * L.isEq(ub,i2(1,1) o To1(X * L),k) ==>
 !A' a':A'->X q:E->A'.Epi(q) & Mono(a') & p1(X,L) o k = a' o q ==> Iso(coPa(a,a'))”));


val Thm5 = prove_store("Thm5",
e0
(rpt strip_tac >> drule Thm5_constructions >>
 pop_assum strip_assume_tac >>
 qspecl_then 
 [‘Exp(X,1+1)’,‘Exp(A,1+1)’,‘a2’,‘j0 o To1(Exp(X,1+1))’] 
 (x_choosel_then ["L","u"] assume_tac) isEq_ex >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qspecl_then [‘X * L’,‘1+1’,‘ub’,‘i2(1,1) o To1(X * L)’]
 (x_choosel_then ["E","k"] assume_tac) isEq_ex >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["A'","a'","q"] assume_tac) >>
 qexistsl_tac [‘A'’,‘a'’] >> 
 drule Thm5_Iso >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 arw[])
(form_goal
 “!A X a:A->X.Mono(a) ==> 
  ?A' a':A'->X. Mono(a') & Iso(coPa(a,a'))”));


val _ = new_pred "Trans" [("f0",ar_sort (mk_ob "R") (mk_ob "A")),
                          ("f1",ar_sort (mk_ob "R") (mk_ob "A"))];


val Trans_def = store_ax("Trans_def",
“!R A f0:R->A f1:R->A.Trans(f0,f1) <=> !X h0:X->R h1:X->R. f1 o h0 = f0 o h1 ==> ?u:X->R. f0 o u = f0 o h0 & f1 o u = f1 o h1”);


val _ = new_pred "Refl" [("f0",ar_sort (mk_ob "R") (mk_ob "A")),
                         ("f1",ar_sort (mk_ob "R") (mk_ob "A"))]

val Refl_def = store_ax("Refl_def",
“!R A f0:R->A f1. Refl(f0,f1) <=> ?d:A->R. f0 o d = id(A) & f1 o d = id(A)”);



val _ = new_pred "Sym" [("f0",ar_sort (mk_ob "R") (mk_ob "A")),
                        ("f1",ar_sort (mk_ob "R") (mk_ob "A"))];

val Sym_def = store_ax("Sym_def",
“!R A f0:R->A f1. Sym(f0,f1) <=> ?t:R->R. f0 o t = f1 & f1 o t = f0”);


val Thm6_first_sentence = prove_store(
"Thm6_first_sentence",
 e0
(rpt strip_tac >> irule prop_2_coro >>
 qexistsl_tac [‘A * A’,‘Pa(f0,f1)’,‘e’] >>
 drule Eqa_Mono >> arw[] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac 
      ‘Eqa(ce o p1(A,A),ce o p2(A,A),e,Pa(f0, f1) o x)’ >>
      irule Eqa_eqn >> 
      qby_tac
      ‘(ce o p1(A, A)) o Pa(f0, f1) o x = 
       ce o (p1(A, A) o Pa(f0, f1)) o x &
       (ce o p2(A, A)) o Pa(f0, f1) o x =
       ce o (p2(A, A) o Pa(f0, f1)) o x’
      >-- rw[o_assoc] >> arw[p12_of_Pa] >> 
      drule coEq_equality >> arw[GSYM o_assoc]) >>
 first_x_assum 
 (qspecl_then [‘p1(A,A) o e o y’,‘p2(A,A) o e o y’]
  assume_tac) >>
 drule Eq_equality >>
 fs[GSYM o_assoc] >> qexists_tac ‘r’ >> 
 irule to_P_eq >> arw[GSYM o_assoc,p12_of_Pa])
(form_goal
“!R A f0:R->A f1. Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> Mono(Pa(f0,f1)) ==> 
!cE ce:A->cE.iscoEq(f0,f1,ce) ==>
(!a0:1->A a1:1->A. ce o a0 = ce o a1 ==> ?r:1->R. f0 o r = a0 & f1 o r = a1) ==> !E e:E->A * A. isEq(ce o p1(A,A),ce o p2(A,A),e) ==> areiso(R,E)”));


val Mem_of_name_Eqa = prove_store("Mem_of_name_Eqa",
e0
(rpt strip_tac >> drule via_Eq_iff >> arw[] >>
rw[o_assoc] >> once_arw[one_to_one_id] >> rw[idR] >>
qby_tac ‘Tp(psi o p1(R, 1)) = Tp(psi o p1(R, 1)) o id(1)’
>-- rw[idR] >>
once_arw[] >> rw[Ev_of_Tp_el] >> rw[o_assoc,p12_of_Pa])
(form_goal 
“!R psi:R-> 1+1 r:1 -> R. 
  !E e. isEq(Ev(R,1+1),i2(1,1) o To1(R * Exp(R,1+1)),e)==>
 (psi o r = i2(1,1) <=> 
  ?r':1->E. e o r' = Pa(r,Tp(psi o p1(R,1))))”));



val Char_ex = prove_store("Char_ex",
e0
(rpt strip_tac >> drule Thm5 >> pop_assum strip_assume_tac >>
 fs[Iso_def] >>
 qexists_tac ‘coPa(i2(1,1) o To1(A),i1(1,1) o To1(A')) o f'’
 >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac 
      ‘(coPa(i2(1,1) o To1(A), i1(1,1) o To1(A')) o f') o a o x0 =  coPa(i2(1,1) o To1(A), i1(1,1) o To1(A')) o (f' o a) o x0’ 
     >-- rw[o_assoc] >>
     qpick_x_assum ‘a o x0 = x’ 
     (assume_tac o GSYM) >> arw[] >>
     qby_tac ‘f' o a = i1(A,A')’
     >-- (qby_tac 
         ‘f' o coPa(a, a') o i1(A,A') = id(A+A') o i1(A,A')’
         >-- (rw[GSYM o_assoc] >> arw[]) >>
         pop_assum mp_tac >> rw[i12_of_coPa,idL]) >>
     once_arw[] >> rw[GSYM o_assoc,i1_of_coPa] >>
     rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) >>
qspecl_then [‘A’,‘A'’,‘f' o x’] strip_assume_tac INC_FAC
>-- (qexists_tac ‘f0’ >>
     qby_tac ‘coPa(a,a') o i1(A, A') o f0 = 
              coPa(a,a') o f' o x’ >-- arw[] >>
     rfs[GSYM o_assoc,i1_of_coPa,idL]) >>
fs[o_assoc] >> pop_assum (assume_tac o GSYM) >> 
fs[] >> fs[GSYM o_assoc,i12_of_coPa] >>
fs[o_assoc] >> 
qpick_x_assum ‘i1(1, 1) o To1(A') o f0 = i2(1, 1)’ mp_tac >>
once_rw[one_to_one_id] >> rw[idR,i1_ne_i2_1])
(form_goal 
“!A X a:A->X. Mono(a) ==> 
 ?phi:X->1 + 1. (!x:1->X.(?x0:1->A.a o x0 = x) <=> phi o x = i2(1,1))”));


val Refl_equiv_to_itself  = prove_store("Refl_equiv_to_itself",
 e0
(rpt strip_tac >> fs[Refl_def] >> 
 qexists_tac ‘d o a’ >> rw[GSYM o_assoc] >> arw[idL])
(form_goal “!R A f0:R->A f1:R->A.Refl(f0:R->A,f1) ==> !a:1->A. ?r:1->R. f0 o r = a & f1 o r = a”));


val equiv_to_same_element = prove_store("equiv_to_same_element",
e0
(rpt strip_tac >> drule Refl_equiv_to_itself >> 
 first_x_assum (qspecl_then [‘a1’] assume_tac) >>
 first_x_assum (qspecl_then [‘a1’] assume_tac) >> rfs[] >>
 qexistsl_tac [‘r'’] >> arw[])
(form_goal 
“!R A f0:R->A f1.Refl(f0,f1) ==> 
 !a0 a1.
(!a':1->A.(?r:1->R.f0 o r = a1 & f1 o r = a') <=> (?r.f0 o r = a0 & f1 o r = a')) ==>
?r:1->R. f0 o r = a0 & f1 o r = a1”));

val Sym_Trans_rel_lemma = prove_store(
"Sym_Trans_rel_lemma",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >-- 
 (fs[Sym_def,Trans_def] >> 
  first_x_assum 
   (qspecl_then [‘1’,‘t o r'’,‘r’] assume_tac) >>
  qby_tac ‘f1 o t o r' = f0 o r’
  >-- (rw[GSYM o_assoc] >> arw[]) >>
  first_x_assum drule >> pop_assum strip_assume_tac >>
  qexists_tac ‘t o u’ >> rw[GSYM o_assoc] >> once_arw[] >>
  once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >> 
  once_arw[] >> rw[]) >> 
 fs[Trans_def] >>
 qpick_x_assum ‘f0 o r'' = f1 o r’
 (assume_tac o GSYM) >>
 first_x_assum drule >> pop_assum strip_assume_tac >> 
 qexists_tac ‘u’ >> arw[])
(form_goal 
“!R A f0:R->A f1.Sym(f0:R->A,f1) & Trans(f0,f1) ==> 
!a:1->A r:1->R. 
((?r':1->R. f0 o r' = f0 o r & f1 o r' = a) <=> 
 (?r'':1->R. f0 o r'' = f1 o r & f1 o r'' = a))”));


val Char_def = Char_ex |> spec_all |> ex2fsym "Char" ["a"]
                       |> gen_all
                       |> store_as "Char_def";



val fac_Char = prove_store("fac_Char",
e0
(rpt strip_tac >> drule Char_def >>
irule FUN_EXT >> strip_tac >> rw[o_assoc] >>
once_rw[one_to_one_id] >> rw[idR] >> 
pop_assum (assume_tac o iffLR) >> first_x_assum irule >>
qexists_tac ‘f o a’ >> rw[GSYM o_assoc] >> once_arw[] >> rw[])
(form_goal 
“!A X m:A->X.Mono(m)==>!P p:P->X f:P->A. m o f = p ==>
Char(m) o p = i2(1,1) o To1(P)”));


val fac_Char_via_any_map = prove_store(
"fac_Char_via_any_map",
e0
(rpt strip_tac >> drule Epi_has_section >> 
 drule Char_def >> 
 first_x_assum (qspecl_then [‘b’] assume_tac) >>
 rfs[] >> qexists_tac ‘s0 o x0’ >>
 qby_tac ‘(m o e) o s0 o x0 = m o (e o s0) o x0’
 >-- rw[o_assoc] >> arw[idL])
(form_goal 
“!A M e:A->M. Epi(e) ==> !B m:M->B.Mono(m) ==>
 !f:A->B. f = m o e ==> 
 !b:1->B.Char(m) o b = i2(1,1) ==>
 ?a:1->A. f o a = b”));

val Pa_o_split = prove_store("Pa_o_split",
e0
(rpt strip_tac >> irule to_P_eq >>
 rw[p12_of_Pa] >> rw[GSYM o_assoc,p12_of_Pa] >>
 rw[o_assoc,p12_of_Pa])
(form_goal
 “!B X f:B->X Y g:X->Y A.Pa(p1(A,B),g:X->Y o f o p2(A,B)) = 
  Pa(p1(A,X), g o p2(A,X)) o Pa(p1(A,B),f o p2(A,B))”));

val o_partial_Ev = prove_store("o_partial_Ev",
e0
(rpt strip_tac >> 
 qby_tac 
 ‘Pa(id(A),To1(A)) o x = Pa(x,id(1))’ 
 >-- (irule to_P_eq >> rw[GSYM o_assoc,p12_of_Pa,idL] >>
      once_rw[one_to_one_id]) >>
 rw[Pa_o_split,GSYM o_assoc,Ev_of_Tp] >>
 rw[o_assoc,Pa_distr,p12_of_Pa,idL] >> 
 once_rw[one_to_one_id] >> rw[idR])
(form_goal 
“!A x:1->A X Y psi:X->Y phi. 
 phi o Pa(x,Tp1(psi)) = 
 Ev(A,1+1) o Pa(p1(A,1),Tp(phi) o Tp1(psi) o p2(A,1)) o 
 Pa(id(A),To1(A)) o x”));


val Thm6_lemma_3 = prove_store("Thm6_lemma_3",
 e0
(rpt strip_tac >> 
abbrev_tac “i2(1,1) o To1(R * Exp(R,1+1)) = t” >>
qspecl_then [‘R * Exp(R,1+1)’,‘1+1’,‘Ev(R,1+1)’,‘t’] assume_tac isEq_ex >>
pop_assum (x_choosel_then ["R'","Psi"] assume_tac) >>
abbrev_tac 
“Pa(h:R->A o p1(R,Exp(R,1+1)),p2(R,Exp(R,1+1))) = h2R” >>
qspecl_then [‘R'’,‘A * Exp(R,1+1)’,‘h2R o Psi’] (x_choosel_then ["M","m","e"] strip_assume_tac) Mono_Epi_fac >>
abbrev_tac “Char(m:M -> A * Exp(R,1+1)) = phi” >> 
qby_tac ‘!x:1->A * Exp(R,1+1). 
         (?x0:1->M. m o x0 = x) <=> phi o x = i2(1,1)’
>-- (drule Char_def >> arw[]) >>
qexists_tac ‘Tp(phi)’ >> strip_tac >> 
qby_tac
‘!r:1->R.
 psi o r = i2(1,1) <=> 
 ?r':1->R'. Psi o r' = Pa(r,Tp1(psi))’
>-- (strip_tac >> rw[GSYM Tp1_def] >> 
     irule Mem_of_name_Eqa >> fs[]) >>
strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
(qby_tac 
 ‘phi o Pa(x,Tp1(psi)) = 
  Ev(A,1+1) o Pa(p1(A,1),Tp(phi) o Tp1(psi) o p2(A,1)) o 
  Pa(id(A),To1(A)) o x’ 
 >-- rw[o_partial_Ev] >>
 rfs[] >>
 drule fac_Char_via_any_map >> first_x_assum drule >>
 first_x_assum drule >> rfs[] >> first_x_assum drule >>
 first_x_assum (qspecl_then [‘Pa(x,Tp1(psi))’] assume_tac)>>
 rfs[] >> qexists_tac ‘p1(R,Exp(R,1+1)) o Psi o a’ >>
 strip_tac (* 2 *)
 >-- (qexists_tac ‘a’ >> irule to_P_eq >>
      rw[p12_of_Pa] >> 
      qby_tac 
      ‘p2(R, Exp(R, 1 + 1)) = p2(A, Exp(R, 1 + 1)) o h2R’
      >-- (qpick_x_assum 
           ‘Pa(h o p1(R, Exp(R, 1 + 1)), p2(R, Exp(R, 1 + 1))) = h2R’ 
           (assume_tac o GSYM) >> arw[p2_of_Pa]) >>
      once_arw[] >>
      qby_tac ‘(p2(A, Exp(R, 1 + 1)) o h2R) o Psi o a = 
      p2(A, Exp(R, 1 + 1)) o (h2R o Psi) o a’
      >-- rw[o_assoc] >> arw[p2_of_Pa]) >>
 qby_tac
 ‘h o p1(R, Exp(R, 1 + 1)) = p1(A, Exp(R, 1 + 1)) o h2R’
 >-- (qpick_x_assum 
      ‘Pa(h o p1(R, Exp(R, 1 + 1)), p2(R, Exp(R, 1 + 1))) = h2R’
      (assume_tac o GSYM) >> once_arw[] >> 
      rw[p1_of_Pa]) >>
 rw[GSYM o_assoc] >> once_arw[] >> 
 qby_tac ‘((p1(A, Exp(R, 1 + 1)) o h2R) o Psi) o a =
 p1(A, Exp(R, 1 + 1)) o (h2R o Psi) o a’ >-- rw[o_assoc] >>
 arw[p1_of_Pa]) >>
rfs[] >> 
qby_tac ‘m o e o r' = h2R o Pa(r, Tp1(psi))’
>-- (rw[GSYM o_assoc] >> 
     qpick_x_assum ‘h2R o Psi = m o e’ (assume_tac o GSYM) >>
     arw[] >> arw[o_assoc]) >>
qby_tac ‘h2R o Pa(r, Tp1(psi)) = Pa(x, Tp1(psi))’
>-- (irule to_P_eq >> rw[GSYM o_assoc,p12_of_Pa] >>
     qpick_x_assum 
     ‘Pa(h o p1(R, Exp(R, 1 + 1)), p2(R, Exp(R, 1 + 1))) = h2R’ (assume_tac o GSYM) >> arw[p12_of_Pa] >>
     arw[o_assoc,p12_of_Pa]) >>
qby_tac ‘phi o h2R o Pa(r, Tp1(psi)) = i2(1,1)’
>-- (qpick_x_assum ‘Char(m) = phi’ (assume_tac o GSYM) >>
     once_arw[] >> drule fac_Char >>
     first_x_assum 
     (qspecl_then [‘1’,‘Pa(x, Tp1(psi))’] assume_tac) >>
     qby_tac ‘To1(1) = id(1)’ 
     >-- (once_rw[one_to_one_id] >> rw[]) >> 
     qsuff_tac ‘Char(m) o Pa(x, Tp1(psi)) = i2(1,1) o To1(1)’
     >-- (once_arw[] >> rw[idR]) >>
     first_x_assum irule >>
     qexists_tac ‘e o r'’>> arw[]) >>
rw[Pa_distr,p12_of_Pa,idL,o_assoc] >> 
once_rw[one_to_one_id] >> rw[idR] >> 
qby_tac 
‘phi o Pa(x,Tp1(psi)) = 
 Ev(A,1+1) o Pa(p1(A,1),Tp(phi) o Tp1(psi) o p2(A,1)) o 
 Pa(id(A),To1(A)) o x’ 
>-- (rw[o_partial_Ev]) >> 
qby_tac ‘(h2R o Psi) o r' =
 h2R o Pa(r, Tp1(psi))’ >-- (arw[o_assoc]) >>
qby_tac 
‘Pa(x, Tp(phi) o Tp1(psi)) = 
 Pa(p1(A, 1), (Tp(phi) o Tp1(psi) o p2(A, 1))) o
               Pa(id(A), To1(A)) o x’
>-- (irule to_P_eq >> rw[p12_of_Pa] >>
     rw[GSYM o_assoc,p12_of_Pa] >> rw[o_assoc,p12_of_Pa] >>
     once_rw[one_to_one_id] >> rw[idL,idR]) >>
arw[] >> 
qpick_x_assum ‘phi o Pa(x, Tp1(psi)) = Ev(A, 1 + 1) o
               Pa(p1(A, 1), (Tp(phi) o Tp1(psi) o p2(A, 1))) o
               Pa(id(A), To1(A)) o x’
(assume_tac o GSYM) >> arw[] >>
qpick_x_assum ‘h2R o Pa(r, Tp1(psi)) = Pa(x, Tp1(psi))’
(assume_tac o GSYM) >> arw[]
)
(form_goal 
“!R A h:R->A.?hb:Exp(R,1+1)-> Exp(A,1+1). 
!psi:R-> 1+1 x:1->A.
 (Ev(A,1+1) o Pa(p1(A,1),hb o Tp1(psi) o p2(A,1)) o
  Pa(id(A),To1(A)) o x = i2(1,1) <=> 
  ?r:1->R. psi o r = i2(1,1) & h o r = x)”));

val Diag_ex = prove_store("Diag_ex",
e0
(strip_tac >> qexists_tac ‘Pa(id(X),id(X))’ >> rw[])
(form_goal
“!X.?dX:X->X * X. Pa(id(X),id(X)) = dX”));

val Diag_def = Diag_ex |> spec_all |> eqT_intro
                       |> iffRL |> ex2fsym "Diag" ["X"]
                       |> C mp (trueI []) |> gen_all

val Diag_Mono = prove_store("Diag_Mono",
e0
(strip_tac >> rw[Mono_def,GSYM Diag_def] >> 
 rpt strip_tac >> 
 qby_tac ‘p1(A,A) o Pa(id(A), id(A)) o g = 
          p1(A,A) o Pa(id(A), id(A)) o h’ 
 >-- arw[] >> 
 fs[p1_of_Pa,GSYM o_assoc,idL])
(form_goal
 “!A.Mono(Diag(A))”));

val Eq_ex = prove_store("Eq_ex",
e0
(strip_tac >> qexists_tac ‘Char(Diag(X))’ >> rw[])
(form_goal “!X.?eqX:X * X -> 1+1. Char(Diag(X)) = eqX”))

val Eq_def = Eq_ex |> spec_all |> eqT_intro
                   |> iffRL |> ex2fsym "Eq" ["X"]
                   |> C mp (trueI []) |> gen_all
                   |> store_as "Eq_def";


val True_ex = prove_store("True_ex",
e0
(strip_tac >> qexists_tac ‘TRUE o To1(X)’ >> rw[])
(form_goal
“!X. ?tX:X->1+1.TRUE o To1(X) = tX”));

val True_def = True_ex |> spec_all |> eqT_intro 
                       |> iffRL |> ex2fsym "True" ["X"] |> C mp (trueI []) |> gen_all |> store_as "True_def";

val False_ex = prove_store("False_ex",
e0
(strip_tac >> qexists_tac ‘FALSE o To1(X)’ >> rw[])
(form_goal
“!X. ?fX:X->1+1.FALSE o To1(X) = fX”));

val False_def = False_ex |> spec_all |> eqT_intro 
                         |> iffRL |> ex2fsym "False" ["X"] |> C mp (trueI []) |> gen_all |> store_as "False_def";



val fac_Diag_eq = prove_store("fac_Diag_eq",
e0
(rpt strip_tac >> 
 fs[Pa_distr,Pa_eq_eq,idL] >>
 pop_assum_list (map_every (assume_tac o GSYM)) >> fs[])
(form_goal 
“!A x:1->A y:1->A x0:1->A.Pa(id(A),id(A)) o x0 = Pa(y,x) ==> 
 y = x”)); 

val fac_Diag_eq_iff = prove_store("fac_Diag_eq_iff",
e0
(rpt strip_tac >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (irule fac_Diag_eq >> qexists_tac ‘a0’  >>
      arw[Pa_distr,p12_of_Pa]) >>
 qexists_tac ‘p1(A,A) o aa’ >> 
 irule to_P_eq >> arw[Pa_distr,p12_of_Pa,GSYM o_assoc,idL])
(form_goal
 “!A aa:1->A * A.
  (?a0:1->A. aa = Pa(id(A),id(A)) o a0) <=>
  p1(A,A) o aa = p2(A,A) o aa”));

val Char_Diag = prove_store("Char_Diag",
e0
(rpt strip_tac >> 
 qspecl_then [‘A’,‘Pa(a1,a2)’] assume_tac fac_Diag_eq_iff>>
 fs[p12_of_Pa] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 qspecl_then [‘A’] assume_tac Diag_Mono >>
 drule Char_def >> pop_assum (assume_tac o GSYM) >>
 arw[Diag_def] >> 
 fconv_tac 
 (rand_fconv no_conv 
 $ basic_once_fconv no_conv (rewr_fconv (eq_sym "ar")))  >>
 rw[])
(form_goal
“!A a1:1->A a2:1->A. Char(Diag(A)) o Pa(a1,a2) = i2(1,1) <=> a1 = a2”));

(*Eq_property same as char_diag_gen*)
val Eq_property = prove_store("Eq_property",
e0
(rpt strip_tac >> rw[GSYM Eq_def] >>
 assume_tac TRUE_def >> 
 qspecl_then [‘X’] assume_tac Diag_Mono >>
 drule Char_def >> dimp_tac >> strip_tac (* 2 *)
 >-- (irule FUN_EXT >> strip_tac >> 
     fs[GSYM True_def,o_assoc,GSYM TRUE_def] >>
     once_rw[one_to_one_id] >> rw[idR,Pa_distr,Char_Diag])>>
 irule FUN_EXT >> strip_tac >> once_rw[GSYM Char_Diag] >>
 qby_tac ‘Char(Diag(X)) o Pa(f, g) o a = True(A) o a’
 >-- arw[GSYM o_assoc] >>
 fs[GSYM TRUE_def,GSYM True_def,Pa_distr] >>
 rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!X A f:A->X g:A->X. 
f = g <=> Eq(X) o Pa(f,g) = True(A)”));

val Thm6_lemma_2 = prove_store("Thm6_lemma_2",
e0
(rpt strip_tac >> 
 rw[Pa_o_split,GSYM o_assoc,Ev_of_Tp] >>
 rw[o_assoc,Pa_distr,idL] >> once_rw[one_to_one_id] >>
 rw[idR,p1_of_Pa] >> rw[Char_Diag])
(form_goal
“!A x:1->A y:1->A. Ev(A,1+1) o 
Pa(p1(A,1),Tp(Char(Diag(A))) o x o p2(A,1))  o Pa(id(A),To1(A)) o y = i2(1,1) <=> y = x”));

val Pa_o_split' = Pa_o_split |> spec_all |> gen_all
                             |> store_as "Pa_o_split'";


val Thm6_g_ev_lemma = prove_store("Thm6_g_ev_lemma",
e0
(rpt strip_tac >> irule Ev_eq_eq >>
 pop_assum (assume_tac o GSYM) >> rw[o_assoc] >>
 qspecl_then [‘R’,‘1’,‘A’,‘a’,‘Exp(R, 1+1)’,
‘Tp((Ev(A, 1 + 1) o
                 Pa(f0 o p1(R, Exp(A, 1 + 1)), p2(R, Exp(A, 1 + 1))))) o
                Tp(Char(Diag(A)))’] assume_tac Pa_o_split' >>
fs[o_assoc] >> rw[Pa_o_split'] >>
rw[GSYM o_assoc,Ev_of_Tp] >> 
rw[o_assoc,Pa_distr,p12_of_Pa] >>
last_x_assum (assume_tac o GSYM) >>
once_arw[] >> rw[GSYM Tp1_def,Ev_of_Tp] >>
rw[o_assoc,Pa_distr,p12_of_Pa]  >>
rw[idL] >>
qsuff_tac ‘p2(R, 1) = To1(A) o f0 o p1(R, 1)’
>-- (strip_tac >> arw[]) >>
once_rw[To1_def] >> rw[])
(form_goal 
“!A a:1->A a':1->A R f0:R->A f1:R->A.
!psi:R->1+1.psi = 
Ev(A,1+1) o Pa(p1(A,1),Tp(Char(Diag(A))) o a o p2(A,1)) o 
Pa(id(A),To1(A)) o f0 ==>
Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o Tp(Char(Diag(A))) o a = 
Tp1(psi)”));



val Bar_def = Thm6_lemma_3 |> spec_all 
                           |> ex2fsym0 "Bar" ["h"]
                           |> gen_all
                           |> store_as "Bar_def"

val Sing_ex = prove_store("Sing_ex",
e0
(strip_tac >> qexists_tac ‘Tp(Char(Diag(A)))’ >> rw[])
(form_goal “!A.?sg. Tp(Char(Diag(A))) = sg”));

val Sing_def = Sing_ex |> spec_all |> ex2fsym0 "Sing" ["A"]
                       |> gen_all
                       |> store_as "Sing_def";


(*Thm6_lemma_2 is sg_def*)
val Thm6_g_ev = prove_store("Thm6_g_ev",
e0
(rpt strip_tac >> 
 abbrev_tac 
 “Ev(A,1+1) o Pa(p1(A,1),Sing(A) o a o p2(A,1)) o Pa(id(A),To1(A)) o f0:R->A = psi” >>
 pop_assum (assume_tac o GSYM) >>
 assume_tac Thm6_g_ev_lemma >> fs[Sing_def] >>
 first_x_assum drule >> 
 qby_tac
 ‘Tp((Ev(A, 1 + 1) o
                 Pa(f0 o p1(R, Exp(A, 1 + 1)), p2(R, Exp(A, 1 + 1))))) o
                Sing(A) o a o p2(A, 1) = 
 (Tp((Ev(A, 1 + 1) o
                 Pa(f0 o p1(R, Exp(A, 1 + 1)), p2(R, Exp(A, 1 + 1))))) o
                Sing(A) o a) o p2(A, 1)’ 
 >-- rw[o_assoc] >>
 last_x_assum (assume_tac o GSYM) >>
 arw[] >>
 qspecl_then [‘A’,‘R’,‘f1’] assume_tac Bar_def >>
 arw[] >>
qsuff_tac ‘!r:1->R. f0 o r = a <=> psi o r = i2(1,1)’
>-- (strip_tac >> arw[]) >>
qpick_x_assum
 ‘Ev(A, 1 + 1) o Pa(p1(A, 1), (Sing(A) o a o p2(A, 1))) o
  Pa(id(A), To1(A)) o f0 = psi’
(assume_tac o GSYM) >>
once_arw[] >> assume_tac Thm6_lemma_2 >>
fs[Sing_def,o_assoc])
(form_goal 
“!R A f0:R->A f1:R->A a:1->A a':1->A. Ev(A,1+1) o 
Pa(p1(A,1),Bar(f1) o 
Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o 
Sing(A) o a o p2(A,1)) o Pa(id(A),To1(A)) o a' = i2(1,1) <=> ?r:1->R. f0 o r = a & f1 o r = a'”));


val Thm6_g_ev' = prove_store("Thm6_g_ev'",
e0
(rpt strip_tac >> 
 assume_tac Thm6_g_ev >> 
 qby_tac
 ‘Pa(a', id(1)) = Pa(id(A), To1(A)) o a'’
 >-- (rw[Pa_distr] >> once_rw[one_to_one_id] >>
     rw[idL]) >>
 arw[])
(form_goal 
“!R A f0:R->A f1:R->A a':1->A a:1->A. Ev(A,1+1) o 
Pa(p1(A,1),
   Bar(f1) o 
   Tp(Ev(A,1+1) o
      Pa(f0 o p1(R,Exp(A,1+1)), p2(R,Exp(A,1+1)))) o 
   Sing(A) o a o p2(A,1)) o Pa(a',id(1)) = 
i2(1,1) <=>
?r:1->R.f0 o r = a & f1 o r = a'”));


val one_to_two_cases = prove_store("one_to_two_cases",
 e0
(rpt strip_tac >> 
 qspecl_then [‘1’,‘1’,‘f’] strip_assume_tac INC_FAC >>(* 2 *)
 pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR] >>
 strip_tac >> arw[])
(form_goal 
“!f:1->1+1. f = i1(1,1) | f = i2(1,1)”));

val one_to_two_eq = prove_store("one_to_two_eq",
e0
(rpt strip_tac >> cases_on “f = i2(1,1)”
 >-- fs[] >>
 fs[] >> 
 qspecl_then [‘f’] strip_assume_tac one_to_two_cases >>
 qspecl_then [‘g’] strip_assume_tac one_to_two_cases >>
 arw[])
(form_goal 
“!f:1->1+1 g:1->1+1. (f = i2(1,1) <=> g = i2(1,1)) ==> f = g”))



val f0g_eq_f1g = prove_store("f0g_eq_f1g",
 e0
(rpt strip_tac >> irule FUN_EXT >> strip_tac >> 
 irule Ev_eq_eq >> irule FUN_EXT >> strip_tac >> 
 irule one_to_two_eq >>
 assume_tac Thm6_g_ev' >>
 qby_tac ‘a' = Pa(p1(A,1) o a',p2(A,1) o a')’ 
 >-- rw[GSYM to_P_component] >>
 pop_assum mp_tac >> once_rw[one_to_one_id] >> strip_tac >>
 once_arw[] >> pop_assum (K all_tac) >>
 fs[o_assoc] >>
 first_assum (qspecl_then [‘R’,‘A’,‘f0’,‘f1’,‘p1(A, 1) o a'’,‘f0 o a’] assume_tac) >> fs[o_assoc]>>
 first_assum (qspecl_then [‘R’,‘A’,‘f0’,‘f1’,‘p1(A, 1) o a'’,‘f1 o a’] assume_tac) >> fs[o_assoc] >> 
 irule Sym_Trans_rel_lemma >> arw[])
(form_goal
“!R A f0:R->A f1:R->A. Sym(f0,f1) & Trans(f0,f1) ==> 
 Bar(f1) o Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)), p2(R,Exp(A,1+1)))) o Sing(A) o f0 = 
  Bar(f1) o Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)), p2(R,Exp(A,1+1)))) o Sing(A) o f1”));


val Thm6_page29_means_just_that = prove_store
("Thm6_page29_means_just_that",
e0
(rpt strip_tac >> 
 qspecl_then [‘R’,‘A’,‘f0’,‘f1’,‘a'’,‘a0’] 
 (assume_tac o GSYM) Thm6_g_ev' >>
 qspecl_then [‘R’,‘A’,‘f0’,‘f1’,‘a'’,‘a1’] 
 (assume_tac o GSYM) Thm6_g_ev' >>
 once_arw[] >>  pop_assum (K all_tac) >>
 pop_assum (K all_tac) >> 
 fs[GSYM o_assoc])
(form_goal
“!A a0:1->A a1:1->A R f0:R->A f1:R->A.
 Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a0 = 
 Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a1 ==>
 !a':1->A.(?r:1->R. f0 o r = a0 & f1 o r = a') <=>
          (?r:1->R. f0 o r = a1 & f1 o r = a')”));


(*TO-DO: let rw be able to solve f <=>f*)
val compose_with_g_eq_equiv = prove_store
("compose_with_g_eq_equiv",
e0
(rpt strip_tac >>
 drule Thm6_page29_means_just_that >>
 irule equiv_to_same_element >> arw[])
(form_goal
“!A a0:1->A a1:1->A R f0:R->A f1:R->A.
 Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a0 = 
  Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a1 ==>
 Refl(f0,f1) ==>
 ?r:1->R. f0 o r = a0 & f1 o r = a1”));



val Thm6_page29_picture = prove_store(
"Thm6_page29_picture",
e0
(rpt strip_tac >>
 qby_tac ‘Sym(f0, f1) & Trans(f0, f1)’ >-- arw[] >> 
 drule f0g_eq_f1g >> 
 abbrev_tac
 “Bar(f1:R->A) o Tp((Ev(A, 1 + 1) o
                Pa(f0 o p1(R, Exp(A, 1 + 1)), p2(R, Exp(A, 1 + 1))))) o
               Sing(A) = l” >>
 fs[GSYM o_assoc] >>  
 qsuff_tac ‘?u. u o ce = l’
 >-- (strip_tac >> pop_assum (assume_tac o GSYM) >> fs[] >>
      arw[o_assoc]) >>
 qexists_tac ‘coEqa(f0,f1,ce,l)’ >> 
 flip_tac >> irule coEqa_eqn >> arw[])
(form_goal
“!R A f0:R->A f1:R->A. Sym(f0,f1) ==> Trans(f0,f1) ==> 
 !cE ce:A->cE. iscoEq(f0,f1,ce) ==>
 !a0:1->A a1:1->A.
 ce o a0 = ce o a1 ==>
  Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a0 = 
  Bar(f1) o 
 Tp(Ev(A,1+1) o Pa(f0 o p1(R,Exp(A,1+1)),p2(R,Exp(A,1+1)))) o
 Sing(A) o a1”));


val Thm6 = prove_store("Thm6",
e0
(rpt strip_tac >> irule Thm6_first_sentence >> 
 qexistsl_tac [‘A’,‘e’,‘f0’,‘f1’,‘cE’,‘ce’] >>
 arw[] >> rpt strip_tac >> irule equiv_to_same_element >>
 arw[] >> irule Thm6_page29_means_just_that >>
 irule Thm6_page29_picture >> arw[] >>
 qexistsl_tac [‘cE’,‘ce’] >> arw[])
(form_goal
“!R A f0:R->A f1:R->A. Mono(Pa(f0,f1)) ==>
 Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> 
 !cE ce:A->cE. iscoEq(f0,f1,ce) ==>
 !E e:E->A * A. isEq(ce o p1(A,A),ce o p2(A,A),e) ==>
 areiso(R,E)”));








val Thm6_first_sentence' = prove_store(
"Thm6_first_sentence",
 e0
(rpt strip_tac >> irule prop_2_coro_subo>>
(* qexistsl_tac [‘A * A’,‘Pa(f0,f1)’,‘e’] >> *)
 drule Eqa_Mono >> arw[] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac 
      ‘Eqa(ce o p1(A,A),ce o p2(A,A),e,Pa(f0, f1) o x)’ >>
      irule Eqa_eqn >> 
      qby_tac
      ‘(ce o p1(A, A)) o Pa(f0, f1) o x = 
       ce o (p1(A, A) o Pa(f0, f1)) o x &
       (ce o p2(A, A)) o Pa(f0, f1) o x =
       ce o (p2(A, A) o Pa(f0, f1)) o x’
      >-- rw[o_assoc] >> arw[p12_of_Pa] >> 
      drule coEq_equality >> arw[GSYM o_assoc]) >>
 first_x_assum 
 (qspecl_then [‘p1(A,A) o e o y’,‘p2(A,A) o e o y’]
  assume_tac) >>
 drule Eq_equality >>
 fs[GSYM o_assoc] >> qexists_tac ‘r’ >> 
 irule to_P_eq >> arw[GSYM o_assoc,p12_of_Pa])
(form_goal
“!R A f0:R->A f1. Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> Mono(Pa(f0,f1)) ==> 
!cE ce:A->cE.iscoEq(f0,f1,ce) ==>
(!a0:1->A a1:1->A. ce o a0 = ce o a1 ==> ?r:1->R. f0 o r = a0 & f1 o r = a1) ==> !E e:E->A * A. isEq(ce o p1(A,A),ce o p2(A,A),e) ==> 
 ?h1 h2. e o h1 = Pa(f0,f1) & Pa(f0,f1) o h2 = e & h1 o h2 = id(E) & h2 o h1 = id(R)”));



val Thm6' = prove_store("Thm6",
e0
(rpt strip_tac >> irule Thm6_first_sentence' >> arw[] >>
 qexistsl_tac [‘cE’,‘ce’] >>
 arw[] >> rpt strip_tac >> irule equiv_to_same_element >>
 arw[] >> irule Thm6_page29_means_just_that >>
 irule Thm6_page29_picture >> arw[] >>
 qexistsl_tac [‘cE’,‘ce’] >> arw[])
(form_goal
“!R A f0:R->A f1:R->A. Mono(Pa(f0,f1)) ==>
 Refl(f0,f1) & Sym(f0,f1) & Trans(f0,f1) ==> 
 !cE ce:A->cE. iscoEq(f0,f1,ce) ==>
 !E e:E->A * A. isEq(ce o p1(A,A),ce o p2(A,A),e) ==>
 ?h1 h2. e o h1 = Pa(f0,f1) & Pa(f0,f1) o h2 = e & h1 o h2 = id(E) & h2 o h1 = id(R)”));

