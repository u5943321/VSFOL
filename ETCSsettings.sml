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

val TRUE_def = ex2fsym0 "TRUE" [] FALSE_ex 
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

val Eq_eqn = Eqa_def |> strip_all_and_imp |> split_assum
                      |> disch “f:A->B o a:X->A = g o a”
                      |>gen_all
                      |> disch_all |> gen_all

val coEq_eqn = coEqa_def |> strip_all_and_imp |> split_assum
                      |> disch “x:B->X o f:A->B = x o g”
                      |>gen_all
                      |> disch_all |> gen_all

val via_Eq_iff = prove_store("via_Eq_iff",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule via_Eq >> qexistsl_tac [‘E’,‘e’,‘h0’] >> arw[])>>
 drule Eq_eqn >> first_x_assum drule >> 
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
 drule coEq_eqn >> first_x_assum drule >> 
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
