
fun mk_foralls vl f = 
    case vl of [] => f 
             | h :: t => uncurry mk_forall h (mk_foralls t f)



fun mk_tinst l = mk_inst l [] 

fun addprims l = 
            case l of [] => l
                    | (n,s) :: t =>
                      let val new = (n^"'",s)
                      in
                          new :: 
                          (List.map 
                               (dest_var o 
                                (substt ((n,s),mk_var new)) o mk_var) (addprims t))
                      end

fun mk_existss nsl f = 
    case nsl of 
        [] => f
      | (h as (n,s)) :: t =>
        mk_exists n s (mk_existss t f)

fun dest_n_exists n f = 
    if n = 0 then ([],f) else 
    let val (l,b) = dest_n_exists (n-1) f
        val (ns,b1) = dest_exists b
    in (l @ [ns],b1)
    end

fun mk_REFL_condf (arg1:(string * sort) list,
                  arg2:(string * sort) list,eqr) = 
    let
        val argtrefl = List.map mk_var arg1
        val reflbody = 
            inst_form (mk_tinst (zip arg2 argtrefl)) eqr
        val reflcl = mk_foralls arg1 reflbody
    in reflcl
    end


fun mk_SYM_condf (arg1:(string * sort) list,
                  arg2:(string * sort) list,eqr) = 
    let
        val (symt1,symt2) = (List.map mk_var arg1,
                             List.map mk_var arg2)
       val symconc = 
            inst_form
            (mk_tinst((zip arg1 symt2) @ (zip arg2 symt1)))
            eqr
        val symbody = 
            mk_imp eqr symconc
        val symcl = mk_foralls (arg1 @ arg2) symbody    
    in symcl
    end
 
fun mk_TRANS_condf (arg1:(string * sort) list,
                    arg2:(string * sort) list,eqr) = 
    let
        val arg3 = addprims arg2
        val (transt1,transt2,transt3) =
            (List.map mk_var arg1,
             List.map mk_var arg2,
             List.map mk_var arg3)
        val transant2 = 
            inst_form
            (mk_tinst((zip arg1 transt2) @ (zip arg2 transt3)))
            eqr
        val transconc = 
            inst_form
            (mk_tinst((zip arg1 transt1) @ (zip arg2 transt3)))
            eqr
        val transbody = mk_imp (mk_conj eqr transant2)
                               transconc
        val transcl = mk_foralls (arg1 @ arg2 @ arg3)
                                 transbody
    in transcl
    end 
 
fun mk_ER_condf argseqr = 
    let val reflcl = mk_REFL_condf argseqr
        val symcl = mk_SYM_condf argseqr
        val transcl = mk_TRANS_condf argseqr
        val eqvcls = mk_conj reflcl (mk_conj symcl transcl)
    in eqvcls
    end 

(*val argseqr = arg12eqr 
  val reflth = coPr_REFL
  val symth = coPr_SYM
  val transth = coPr_TRANS
*)
fun check_REFL argseqr reflth =
    let val reflcl = mk_REFL_condf argseqr 
        val _ = eq_form (reflcl,concl reflth)
    in ()
    end


fun check_SYM argseqr symth =
    let val symcl = mk_SYM_condf argseqr 
        val _ = eq_form (symcl,concl symth)
    in ()
    end


fun check_TRANS argseqr transth =
    let val transcl = mk_TRANS_condf argseqr 
        val _ = eq_form (transcl,concl transth)
    in ()
    end


fun check_ER argseqr eqvth uexth = 
    let val eqvcls = mk_ER_condf argseqr
        val _ = eq_form (eqvcls,concl eqvth) orelse
                raise simple_fail "newspec.eqvth concl"
        val _ = HOLset.isSubset(cont eqvth,cont uexth) orelse
                raise simple_fail "newspec.eqvth cont"
        val _ = List.all 
                    (fn asm => 
                        List.exists
                            (fn a => eq_form(a,asm)) (ant uexth))
                    (ant eqvth) orelse
                raise simple_fail "newspec.eqvth ant"
(*all the condition that requires to prove the equivalence relation is contained in the existential-up-to-unique theorem*)  
    in ()
    end        

(*take: 1.the body of formula we want to create function symbols for
        2.the equivalence relation and its two arguments.
  produce: the existence of the terms in the body of the formula up to the 
  relation*)

fun mk_uexf (arg:(string * sort) list,Q) 
            (arg1:(string * sort) list,
             arg2:(string * sort) list,eqr) = 
    let
        val maint = List.map mk_var arg
        val mainprimv = addprims arg
        val mainprimt = List.map mk_var mainprimv
        val mainprim = inst_form
            (mk_tinst (zip arg mainprimt)) Q
        val relf = 
            inst_form
            (mk_tinst((zip arg1 maint) @ (zip arg2 mainprimt)))
            eqr
        val cj2ofit = mk_foralls mainprimv 
                      (mk_imp mainprim relf)
        val whole = mk_existss arg (mk_conj Q cj2ofit)
    in
        whole
    end

fun check_uexth argQ arg12eqr uexth = 
    let 
        val whole = mk_uexf argQ arg12eqr
        val _ = eq_form(whole,concl uexth) orelse
                raise simple_fail "newspec.uexth concl"
    in ()
    end

(*check the soundness theorem. to pass the check, require the term to exist once the variables in uexth exist, under no assumption and of correct form.*)

fun check_eth arg eth uexth = 
    let val _ = HOLset.isSubset(cont eth,cont uexth) orelse
                raise simple_fail "newspec.eth has extra variables"
        val _ = eq_forml (ant eth) [] orelse
                raise simple_fail "newspec.eth has assumptions"
        val _ = eq_form(concl eth, mk_existss arg TRUE)
                orelse 
                raise simple_fail "newspec.ill-formed eth"
    in ()
    end

(*check the information contained in inputs is enough*)
fun check_inputs vl vs0 = 
    let 
        val inputvars0 = filter_cont vs0
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) 
                           essps vl
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
    in ()
    end

fun mk_newfsym fnames vl uexth = 
    let val (newspvs,b) = dest_n_exists (length fnames) (concl uexth)
        val (main,impf) = dest_conj b 
        val recoverex = mk_existss newspvs main
        val sts = List.map snd newspvs
        val (ct,asm) = (cont uexth,ant uexth)
        fun itmk fnl sts vl f = 
            case fnl of 
                [] => (fnl,f)
              | h :: t =>
                let val _ = new_fun (hd fnl) (hd sts,vl)
                    val ft = mk_fun (hd fnl) (List.map mk_var vl)
                    val (ns,b) = dest_exists f
                    val f0 = substf (ns,ft) b
                    val sts' = List.map (substs (ns,ft)) sts
                in itmk (tl fnl) (tl sts') vl f0
                end 
(*
        fun itmk fnl sts vl f = (*List.foldl  *)
            case fnl of 
                [] => (fnl,f)
              | h :: t =>
                let val _ = new_fun (hd fnl) (hd sts,vl)
                    val ft = mk_fun (hd fnl) (List.map mk_var vl)
                    val (ns,b) = dest_exists f
                    val f0 = substf (ns,ft) b
                in itmk (tl fnl) (tl sts) vl f0
                end *)
        val (_,conc) = itmk fnames sts vl recoverex
    in
        mk_thm(ct,asm,conc)
    end

fun new_spec argQ arg12eqr
             fnames vl eth eqvth uexth = 
    let val _ = check_ER arg12eqr eqvth uexth 
        val _ = check_uexth argQ arg12eqr uexth
        val arg = #1 argQ
        val _ = check_eth arg eth uexth
        val vs0 = cont uexth
        val _ = check_inputs vl vs0
    in mk_newfsym fnames vl uexth
    end


fun impr_fconv fc f = 
    case view_form f of
        vConn("==>",[p,q]) => imp_iff (frefl p) (fc q)       
      | _ => raise ERR ("imp_fconv.not an implication",[],[],[f])

fun uex_def' f = 
    let val th0 = uex_def f 
        val (l,r) = dest_dimp (concl th0) 
        val r2r' = (once_depth_fconv no_conv (impr_fconv sym_fconv)) r
        val th1 = iff_trans th0 r2r' 
    in th1 
    end

fun uex_expand' th = dimp_mp_l2r th (uex_def' $ concl th)



(*
(*simple case of uex_spec, applies only when the assumption list of uex is empty and hence the derivation of soundness existential theorem is automated*)


(*simple_uex_spec "Id" [("A",set_sort)] Id_uex0 *)

val Thm_2_4_unique = proved_th $
e0
(cheat)
(form_goal “
 ∀A B i:B->A B' i'.
 (Inj(i) &
      (∀a. P(a) <=> ∃b:mem(B). a = App(i,b))) & 
 (Inj(i') & 
      (∀a. P(a) ⇔ ∃b:mem(B'). a = App(i',b))) ⇒
  ∃f:B -> B' g:B' -> B. 
     f o g = Id(B') &
     g o f = Id(B) &
     i' o f = i & i o g = i'”)

val Thm_2_4' = proved_th $
e0
(strip_tac >>
 qspecl_then [‘A’] strip_assume_tac Thm_2_4 >> 
  qexistsl_tac [‘B’,‘i’] >> arw[] >>
 rpt strip_tac >>
 irule Thm_2_4_unique >> arw[])
(form_goal 
 “∀A. 
    ∃B i:B->A. 
     (Inj(i) &
      (∀a. P(a) <=> ∃b:mem(B). a = App(i,b))) &
     (∀B' i':B'->A.
      Inj(i') & 
      (∀a. P(a) ⇔ ∃b:mem(B'). a = App(i',b)) ⇒
     ∃f:B -> B' g:B' -> B. 
     f o g = Id(B') &
     g o f = Id(B) &
     i' o f = i & i o g = i')”)



val T24_ts_ex = proved_th $
e0
(strip_tac >> qexistsl_tac [‘A’,‘Id(A)’] >> rw[])
(form_goal “!A. ?B i:B->A. T”)

val Rrefl = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘Id(B)’,‘Id(B)’] >> rw[IdR,IdL])
(form_goal 
 “∀B i:B->A. 
  ∃f:B ->B g:B->B. f o g = Id(B) & g o f = Id(B) &
    i o f = i & i o g = i”)

val Rsym = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘g’,‘f’] >> arw[])
(form_goal 
“∀B i:B ->A B' i':B' -> A. 
 (∃f:B->B' g:B'->B.
  f o g = Id(B') & g o f = Id(B) &
  i' o f = i & i o g = i') ⇒ 
 (∃f:B'->B g:B->B'.
  f o g = Id(B) & g o f = Id(B') &
  i o f = i' & i' o g = i)”)


val Rtrans = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘f' o f’,‘g o g'’] >> arw[] >>
 arw[GSYM o_assoc] >> 
 qsuff_tac
 ‘f' o (f o g) o g' = Id(B'') & g o (g' o f') o f = Id(B)’ 
 >-- rw[o_assoc] >>
 arw[IdL,IdR])
(form_goal 
“∀B i:B ->A B' i':B' -> A B'' i'':B''->A. 
 (∃f:B->B' g:B'->B.
  f o g = Id(B') & g o f = Id(B) &
  i' o f = i & i o g = i') & 
 (∃f:B'->B'' g:B''->B'.
  f o g = Id(B'') & g o f = Id(B') &
  i'' o f = i' & i' o g = i'') ⇒
 (∃f:B->B'' g:B''->B.
  f o g = Id(B'') & g o f = Id(B) &
  i'' o f = i & i o g = i'')”)

val T24_eqv = conjI Rrefl (conjI Rsym Rtrans)


val set_spec_eqv = T24_eqv |> gen_all

val set_spec_arg12eqr0 = 
([("B",set_sort),("i",fun_sort (rastt "B") (rastt "A"))],
 [("B'",set_sort),("i'",fun_sort (rastt "B'") (rastt "A"))],
 “(∃f:B->B' g:B'->B.
           f o g = Id(B') & g o f = Id(B) &
           i' o f = i & i o g = i':B'->A)”)


fun set_spec oriset sname iname fvs uexth = 
    let val cuexth = concl uexth 
        val (buexth,arg) = strip_exists cuexth 
        val (Q,_) = dest_conj buexth
        val argQ = (arg,Q) 
        val tenv = mk_tinst [(("A",set_sort),oriset)]
        val arg12eqr = 
            (List.map (dest_var o (inst_term (vd_of tenv)) o mk_var) 
                      (#1 set_spec_arg12eqr0),
            List.map (dest_var o (inst_term (vd_of tenv)) o mk_var) 
                      (#2 set_spec_arg12eqr0),
            inst_form tenv (#3 set_spec_arg12eqr0))
        val eth = T24_ts_ex |> allE oriset
        val eqvth = set_spec_eqv |> allE oriset
    in new_spec argQ arg12eqr [sname,iname] fvs eth eqvth uexth
    end


(*
val Reqv = conjI Rrefl (conjI Rsym Rtrans)

val arg = [("B",set_sort),("i",fun_sort (rastt "B") (rastt "A"))]

val Q = “(Inj(i:B->A) &
         (∀a. P(a) <=> ∃b:mem(B). a = App(i,b)))”

val argQ = (arg,Q)

val arg1 = [("B",set_sort),("i",fun_sort (rastt "B") (rastt "A"))]

val arg2 = [("B'",set_sort),("i'",fun_sort (rastt "B'") (rastt "A"))]

val eqr = “(∃f:B->B' g:B'->B.
           f o g = Id(B') & g o f = Id(B) &
           i' o f = i & i o g = i':B'->A)”

val arg12eqr = (arg1,arg2,eqr) 

val fnames = ["sset","inc"]

val vl = [("A",set_sort)] (*will have more things in practice*)

val eth = spec_all T24_ts_ex

val uexth = spec_all Thm_2_4'

val eqvth = Reqv

new_spec argQ arg12eqr fnames vl eth eqvth uexth


val N_def = Thm_2_4 |> qspecl [‘N0’] 
                    |> fVar_sInst_th 
                       “P(a:mem(N0))” “IN(a,inNs)”
                    |> qSKOLEM "N" [] |> qSKOLEM "iN" []

val uexth = 
 Thm_2_4' |> qspecl [‘N0’] 
                    |> fVar_sInst_th 
                       “P(a:mem(N0))” “IN(a,inNs)”

val fvs:(string * sort) list = []

val sname = "N"

val iname = "iN"


val oriset = rastt "N0"


set_spec (rastt "Pow(N * X)") "List" "iL" [("X",set_sort)] 

 (Thm_2_4' |> qspecl [‘Pow(N * X)’] 
                    |> fVar_sInst_th 
                       “P(a:mem(Pow(N * X)))” 
                       “IN(a:mem(Pow(N * X)),isLs(X))”)



argQ = uexth |> concl



new_spec
“(!AB p1:AB->A p2:AB->B.
 ?!i:AB->AB j. i o j = Id(AB) & j o i = Id(AB) &
  p1 o i = p1 & p2 o i = p2 &
  p1 o j = p1 & p2 o j = p2) &
 (!AB p1:AB->A p2:AB->B AB' p1':AB'->A p2':AB'->B. 
  (?!i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   p1' o i = p1 & p2' o i = p2 &
   p1 o j = p1' & p2 o j = p2')==>
  (?!i:AB'->AB j. i o j = Id(AB) & j o i = Id(AB') &
   p1 o i = p1' & p2 o i = p2' &
   p1' o j = p1 & p2' o j = p2)) & 
 (!AB p1:AB->A p2:AB->B AB' p1':AB'->A p2':AB'->B
      AB'' p1'':AB''->A p2'':AB''->B. 
  (?!i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   p1' o i = p1 & p2' o i = p2 &
   p1 o j = p1' & p2 o j = p2') &
  (?!i:AB'->AB'' j. i o j = Id(AB'') & j o i = Id(AB') &
   p1'' o i = p1' & p2'' o i = p2' &
   p1' o j = p1'' & p2' o j = p2'') ==>
  (?!i:AB->AB'' j. i o j = Id(AB'') & j o i = Id(AB) &
   p1'' o i = p1 & p2'' o i = p2 &
   p1 o j = p1'' & p2 o j = p2''))
 ”)





val coPr_unique = prove_store("coPr_unique",
e0
(rpt strip_tac >>
 drule $ iffLR iscoPr_def >>
 rev_drule $ iffLR iscoPr_def >> 
 last_x_assum (qsspecl_then [‘i1’,‘i2’] (strip_assume_tac o uex_expand)) >>
 last_x_assum (qsspecl_then [‘i1'’,‘i2'’] (strip_assume_tac o uex_expand)) >> 
 qexistsl_tac [‘fg'’,‘fg’] >> arw[] >>
 drule $ iffLR iscoPr_def >>
 rev_drule $ iffLR iscoPr_def >> 
 last_x_assum (qsspecl_then [‘i1'’,‘i2'’] (strip_assume_tac o uex_expand)) >>
 last_x_assum (qsspecl_then [‘i1’,‘i2’] (strip_assume_tac o uex_expand)) >> 
 rpt strip_tac (* 2 *)
 >-- (qsuff_tac
 ‘fg' o fg = fg'' & Id(AB') = fg''’
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[IdL,IdR] >>
 arw[o_assoc]) >>
 qsuff_tac
 ‘fg o fg' = fg''' & Id(AB) = fg'''’
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[IdL,IdR] >>
 arw[o_assoc])
(form_goal
 “∀AB i1:A->AB i2:B->AB AB' i1':A->AB' i2':B->AB'.
  iscoPr(i1,i2) & iscoPr(i1',i2') ⇒ 
  ∃i:AB -> AB' j:AB' -> AB.
   i o j = Id(AB') &  j o i = Id(AB) &
   j o i1' = i1 & j o i2' = i2 & 
   i o i1 = i1' & i o i2 = i2'”));


uexth

uex_expand uexth0

val argQ = (arg,Q);
val arg12eqr = (arg1,arg2,eqr)
*)
*)
