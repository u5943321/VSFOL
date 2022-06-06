


val Pr_uex = prove_store("Pr_uex",
e0
cheat
(form_goal “!A B. ?AB p1:AB->A p2:AB ->B. 
 isPr(p1,p2) &
 (!AB' p1':AB'->A p2'. isPr(p1',p2') ==>
  ?!i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
  p1' o i = p1 & p2' o i = p2 &
  p1 o j = p1' & p2 o j = p2')”));

val Pr_ts_ex = proved_th $
e0
cheat
(form_goal “!A B. ?AB p1:AB->A p2:AB ->B. T”)

val Reqv = proved_th $
e0
cheat
(form_goal 
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

val uexth = Pr_uex |> spec_all

val eth = Pr_ts_ex |> spec_all

val eqvth = Reqv

val fnames = ["*","p1","p2"]

(*val iseqr = “P()”*)


val arg1 = List.map (dest_var o rastt) 
                    ["AB","p1:AB->A","p2:AB->B"]

val arg2 = List.map (dest_var o rastt) 
                     ["AB'","p1':AB'->A","p2':AB'->B"]

val eqr = 
“?!i:AB->AB' j. i o j = Id(AB') & j o i = Id(AB) &
   (p1':AB'->A) o i = p1 & (p2':AB'->B) o i = p2 &
   p1 o j = p1' & p2 o j = p2'”


val arg = arg1
val Q = “isPr(p1:AB->A,p2:AB->B)”

val vl = List.map dest_var [rastt "A",rastt "B"]


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
        fun itmk fnl vl f = (*List.foldl  *)
            case fnl of 
                [] => (fnl,f)
              | h :: t =>
                let val _ = new_fun (hd fnl) (hd sts,vl)
                    val ft = mk_fun (hd fnl) (List.map mk_var vl)
                    val (ns,b) = dest_exists f
                    val f0 = substf (ns,ft) b
                in itmk (tl fnl) vl f0
                end 
        val (_,conc) = itmk fnames vl recoverex
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

val argQ = (arg,Q);
val arg12eqr = (arg1,arg2,eqr)
